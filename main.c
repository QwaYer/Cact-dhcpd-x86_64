/*
 * dhcpd — DHCP client for CactOS (analog of dhclient/dhcpcd on Linux).
 *
 * Keeps an address on the network card via DHCP: DISCOVER/OFFER/REQUEST/ACK,
 * renews the lease at T1/T2, applies the received config (ip/mask/gw/dns)
 * to the kernel via /dev/net CACT_NETCTL_NETCFG. The kernel does not perform
 * DHCP — it only applies what this daemon (or the ip tool) tells it.
 *
 * Usage:
 *   dhcpd [-i IFACE] [-f]
 *   dhcpd -6 [-i IFACE]        (SLAAC: IPv6 stateless autoconfiguration)
 *   dhcpd -6 -D [-i IFACE]     (stateful DHCPv6 + default route from RA)
 *
 *   -i IFACE   interface name to configure (default: the primary NIC)
 *   -6         IPv6 SLAAC instead of DHCPv4: send a Router Solicitation over a
 *              raw ICMPv6 socket and apply the advertised prefix (EUI-64 IID)
 *   -D         stateful DHCPv6 (implies -6): SOLICIT/REQUEST to ff02::1:2 for an
 *              address + DNS; the default route still comes from an RA
 *   -f         do not go into the background (foreground is the default anyway)
 *
 * The daemon is meant to be run as root (CACT_NETCTL_IFACE_SETCFG is required).
 * With several NICs, run one dhcpd per interface (each with its own `-i IFACE`).
 */

#include <stdint.h>
#include <stddef.h>
#include <string.h>
#include <stdio.h>
#include <time.h>

#include <socket.h>
#include <unistd.h>
#include <fcntl.h>
#include <poll.h>
#include <ioctl_abi.h>

#define DHCP_MAGIC      0x63825363u
#define DHCP_OPT_MSG_TYPE  53
#define DHCP_OPT_SERVER_ID 54
#define DHCP_OPT_REQ_IP    50
#define DHCP_OPT_SUBNET    1
#define DHCP_OPT_ROUTER    3
#define DHCP_OPT_DNS       6
#define DHCP_OPT_LEASE     51
#define DHCP_OPT_T1        58
#define DHCP_OPT_T2        59
#define DHCP_OPT_PARAM_REQ 55
#define DHCP_OPT_HOSTNAME  12
#define DHCP_OPT_END       255

#define DHCP_TYPE_DISCOVER 1
#define DHCP_TYPE_OFFER    2
#define DHCP_TYPE_REQUEST  3
#define DHCP_TYPE_ACK      5
#define DHCP_TYPE_NAK      6

#define DHCP_CLIENT_PORT   68
#define DHCP_SERVER_PORT   67

#define IFACE_DEFAULT "eth0"

#define LEASE_DEFAULT_S   3600u

struct dhcp_hdr {
    uint8_t  op, htype, hlen, hops;
    uint32_t xid;
    uint16_t secs, flags;
    uint32_t ciaddr, yiaddr, siaddr, giaddr;
    uint8_t  chaddr[16];
    uint8_t  sname[64];
    uint8_t  file[128];
    uint32_t magic;
    uint8_t  opts[312];
} __attribute__((packed));

typedef struct {
    uint32_t ip_host;      /* yiaddr from the server, host order */
    uint32_t netmask_host;
    uint32_t gateway_host;
    uint32_t dns_host;
    uint32_t server_host;  /* option 54 */
    uint32_t lease_s;
    uint32_t t1_s;
    uint32_t t2_s;
    uint8_t  mac[6];
} lease_t;

static const char *g_iface = IFACE_DEFAULT;
static int         g_ifindex = 0;   /* resolved from -i IFACE, else the primary (0) */
static uint32_t    g_xid   = 0;

/* ────────────────────────────────────────────────────────────────────────── */

static int opt_get_u32(const uint8_t *opts, int opts_len, uint8_t key, uint32_t *out) {
    int i = 0;
    while (i < opts_len) {
        uint8_t t = opts[i++];
        if (t == DHCP_OPT_END) break;
        if (t == 0) continue;
        if (i >= opts_len) break;
        uint8_t l = opts[i++];
        if (i + l > opts_len) break;
        if (t == key && l >= 4) {
            /* Wire bytes are already the address in reading order, so the
             * big-endian assembly *is* the host-order value (a.b.c.d ->
             * 0xAABBCCDD) that ip_print()/net_apply() expect.  Swapping here
             * too would double-convert every option. */
            uint32_t netv = ((uint32_t)opts[i] << 24) |
                            ((uint32_t)opts[i + 1] << 16) |
                            ((uint32_t)opts[i + 2] << 8) |
                            (uint32_t)opts[i + 3];
            *out = netv;
            return 0;
        }
        i += l;
    }
    return -1;
}

static int opt_get_u8(const uint8_t *opts, int opts_len, uint8_t key, uint8_t *out) {
    int i = 0;
    while (i < opts_len) {
        uint8_t t = opts[i++];
        if (t == DHCP_OPT_END) break;
        if (t == 0) continue;
        if (i >= opts_len) break;
        uint8_t l = opts[i++];
        if (i + l > opts_len) break;
        if (t == key && l >= 1) {
            *out = opts[i];
            return 0;
        }
        i += l;
    }
    return -1;
}

static void opt_append_u8(uint8_t *opts, int *off, int cap, uint8_t key, uint8_t val) {
    if (*off + 3 > cap) return;
    opts[(*off)++] = key;
    opts[(*off)++] = 1;
    opts[(*off)++] = val;
}

static void opt_append_u32(uint8_t *opts, int *off, int cap, uint8_t key, uint32_t host_val) {
    if (*off + 6 > cap) return;
    /* Emit the host-order value big-endian: no htonl() first, or the two
     * conversions cancel and the address goes out byte-reversed. */
    opts[(*off)++] = key;
    opts[(*off)++] = 4;
    opts[(*off)++] = (uint8_t)((host_val >> 24) & 0xFF);
    opts[(*off)++] = (uint8_t)((host_val >> 16) & 0xFF);
    opts[(*off)++] = (uint8_t)((host_val >> 8) & 0xFF);
    opts[(*off)++] = (uint8_t)(host_val & 0xFF);
}

static void opt_end(uint8_t *opts, int *off, int cap) {
    if (*off < cap) opts[(*off)++] = DHCP_OPT_END;
}

/* ── /dev/net: read/apply kernel config ─────────────────────────────────── */

/* Index (CACT_NETCTL_IFACE_GET) of the interface named `name`, or -1. */
static int iface_index_by_name(const char *name) {
    int fd = open("/dev/net", O_RDWR);
    if (fd < 0) return -1;
    int count = ioctl(fd, CACT_NETCTL_IFACE_COUNT, 0);
    int found = -1;
    for (int i = 0; i < count; i++) {
        cact_iface_get_arg_t a;
        memset(&a, 0, sizeof(a));
        a.index = (uint32_t)i;
        if (ioctl(fd, CACT_NETCTL_IFACE_GET, &a) < 0) continue;
        if (strcmp(a.info.name, name) == 0) { found = i; break; }
    }
    close(fd);
    return found;
}

static int net_get(cact_iface_info_t *g) {
    int fd = open("/dev/net", O_RDWR);
    if (fd < 0) return -1;
    cact_iface_get_arg_t a;
    memset(&a, 0, sizeof(a));
    a.index = (uint32_t)g_ifindex;
    int r = ioctl(fd, CACT_NETCTL_IFACE_GET, &a);
    close(fd);
    if (r == 0 && g) *g = a.info;
    return r;
}

static int net_apply(const lease_t *ls) {
    cact_iface_setcfg_arg_t cfg;
    memset(&cfg, 0, sizeof(cfg));
    cfg.index        = (uint32_t)g_ifindex;
    cfg.ip_host      = ls->ip_host;
    cfg.netmask_host = ls->netmask_host;
    cfg.gateway_host = ls->gateway_host;
    cfg.dns_host     = ls->dns_host;

    int fd = open("/dev/net", O_RDWR);
    if (fd < 0) return -1;
    int r = ioctl(fd, CACT_NETCTL_IFACE_SETCFG, &cfg);
    close(fd);
    return r;
}

/* ── socket ──────────────────────────────────────────────────────────────── */

static int dhcp_socket(void) {
    int fd = socket(AF_INET, SOCK_DGRAM, IPPROTO_UDP);
    if (fd < 0) return -1;

    int one = 1;
    (void)setsockopt(fd, SOL_SOCKET, SO_REUSEADDR, &one, sizeof(one));

    struct sockaddr_in local;
    memset(&local, 0, sizeof(local));
    local.sin_family = AF_INET;
    local.sin_port   = htons(DHCP_CLIENT_PORT);
    if (bind(fd, (struct sockaddr *)&local, sizeof(local)) < 0) {
        close(fd);
        return -1;
    }
    return fd;
}

/* ── message building ───────────────────────────────────────────────────── */

static void dhcp_fill_hdr(struct dhcp_hdr *h, int op, const uint8_t mac[6]) {
    memset(h, 0, sizeof(*h));
    h->op    = (uint8_t)op;      /* 1 = BOOTREQUEST */
    h->htype = 1;                /* Ethernet */
    h->hlen  = 6;
    h->xid   = htonl(g_xid);
    h->flags = htons(0x8000);    /* broadcast reply */
    h->magic = htonl(DHCP_MAGIC);
    if (mac)
        memcpy(h->chaddr, mac, 6);
}

static void dhcp_build_discover(struct dhcp_hdr *h, const uint8_t mac[6]) {
    dhcp_fill_hdr(h, 1, mac);
    int oi = 0;
    opt_append_u8(h->opts, &oi, (int)sizeof(h->opts), DHCP_OPT_MSG_TYPE, DHCP_TYPE_DISCOVER);
    /* parameter-request list: subnet/router/dns/lease */
    h->opts[oi++] = DHCP_OPT_PARAM_REQ;
    h->opts[oi++] = 4;
    h->opts[oi++] = DHCP_OPT_SUBNET;
    h->opts[oi++] = DHCP_OPT_ROUTER;
    h->opts[oi++] = DHCP_OPT_DNS;
    h->opts[oi++] = DHCP_OPT_LEASE;
    opt_end(h->opts, &oi, (int)sizeof(h->opts));
}

/* type=3 (REQUEST): if we already have an address and server — RENEWING/REBINDING.
 * server_host != 0  -> unicast renew to server (REQ with ciaddr)
 * server_host == 0  -> broadcast REQUEST (SELECTING, with requested-ip) */
static void dhcp_build_request(struct dhcp_hdr *h, const uint8_t mac[6],
                               uint32_t requested_ip_h, uint32_t server_h,
                               uint32_t ciaddr_h, int include_reqip) {
    dhcp_fill_hdr(h, 1, mac);
    h->ciaddr = htonl(ciaddr_h);
    int oi = 0;
    opt_append_u8(h->opts, &oi, (int)sizeof(h->opts), DHCP_OPT_MSG_TYPE, DHCP_TYPE_REQUEST);
    if (include_reqip && requested_ip_h)
        opt_append_u32(h->opts, &oi, (int)sizeof(h->opts), DHCP_OPT_REQ_IP, requested_ip_h);
    if (server_h)
        opt_append_u32(h->opts, &oi, (int)sizeof(h->opts), DHCP_OPT_SERVER_ID, server_h);
    h->opts[oi++] = DHCP_OPT_PARAM_REQ;
    h->opts[oi++] = 4;
    h->opts[oi++] = DHCP_OPT_SUBNET;
    h->opts[oi++] = DHCP_OPT_ROUTER;
    h->opts[oi++] = DHCP_OPT_DNS;
    h->opts[oi++] = DHCP_OPT_LEASE;
    opt_end(h->opts, &oi, (int)sizeof(h->opts));
}

static int dhcp_sendto(int fd, const struct dhcp_hdr *h, uint32_t dst_ip_h, uint16_t dst_port_h) {
    struct sockaddr_in dst;
    memset(&dst, 0, sizeof(dst));
    dst.sin_family = AF_INET;
    dst.sin_port   = htons(dst_port_h);
    dst.sin_addr   = htonl(dst_ip_h);
    return sendto(fd, h, sizeof(*h), 0, (struct sockaddr *)&dst, sizeof(dst));
}

/* Wait for a reply of the required type until deadline (time()). */
static int dhcp_wait_reply(int fd, uint32_t want_type, time_t deadline,
                           struct dhcp_hdr *rep, lease_t *out) {
    while (time(0) < deadline) {
        struct sockaddr_in from;
        uint32_t fromlen = sizeof(from);
        int n = recvfrom(fd, rep, sizeof(*rep), 0,
                         (struct sockaddr *)&from, &fromlen);
        if (n <= 0) {
            sleep(1);
            continue;
        }
        if ((size_t)n < offsetof(struct dhcp_hdr, opts) + 4) continue;
        if (rep->op != 2) continue;                       /* BOOTREPLY */
        if (rep->xid != htonl(g_xid)) continue;           /* another transaction */
        if (ntohl(rep->magic) != DHCP_MAGIC) continue;

        int opts_len = n - (int)offsetof(struct dhcp_hdr, opts);
        uint8_t mt = 0;
        if (opt_get_u8(rep->opts, opts_len, DHCP_OPT_MSG_TYPE, &mt) < 0) continue;
        if (mt == DHCP_TYPE_NAK) return -2;               /* server refused */
        if (mt != want_type) continue;

        out->ip_host = ntohl(rep->yiaddr);
        (void)opt_get_u32(rep->opts, opts_len, DHCP_OPT_SUBNET, &out->netmask_host);
        if (out->netmask_host == 0) out->netmask_host = 0xFFFFFF00u;
        (void)opt_get_u32(rep->opts, opts_len, DHCP_OPT_ROUTER, &out->gateway_host);
        (void)opt_get_u32(rep->opts, opts_len, DHCP_OPT_DNS, &out->dns_host);
        (void)opt_get_u32(rep->opts, opts_len, DHCP_OPT_SERVER_ID, &out->server_host);
        uint32_t lease = 0, t1 = 0, t2 = 0;
        (void)opt_get_u32(rep->opts, opts_len, DHCP_OPT_LEASE, &lease);
        (void)opt_get_u32(rep->opts, opts_len, DHCP_OPT_T1, &t1);
        (void)opt_get_u32(rep->opts, opts_len, DHCP_OPT_T2, &t2);
        out->lease_s = lease ? lease : LEASE_DEFAULT_S;
        out->t1_s    = t1 ? t1 : out->lease_s / 2;
        out->t2_s    = t2 ? t2 : (out->lease_s * 7) / 8;
        if (out->t1_s == 0 || out->t1_s > out->lease_s) out->t1_s = out->lease_s / 2;
        if (out->t2_s < out->t1_s || out->t2_s > out->lease_s) out->t2_s = out->lease_s;
        return 0;
    }
    return -1;   /* timeout */
}

static void lease_copy_mac(lease_t *ls, const uint8_t mac[6]) {
    if (mac) memcpy(ls->mac, mac, 6);
}

static void ip_print(uint32_t ip_h) {
    printf("%u.%u.%u.%u",
           (unsigned)((ip_h >> 24) & 0xFF), (unsigned)((ip_h >> 16) & 0xFF),
           (unsigned)((ip_h >> 8) & 0xFF), (unsigned)(ip_h & 0xFF));
}

/* Full INIT/SELECTING/REQUESTING cycle: DISCOVER->OFFER->REQUEST->ACK.
 * Returns 0 and a filled lease on success. */
static int dhcp_acquire(int fd, const uint8_t mac[6], lease_t *out) {
    struct dhcp_hdr req, rep;

    int got_offer = 0;
    for (int attempt = 0; attempt < 5; attempt++) {
        g_xid = (uint32_t)((uint32_t)getpid() << 16) ^
                (uint32_t)time(0) ^ (uint32_t)(attempt + 1) ^ 0xCA7CD00Du;
        dhcp_build_discover(&req, mac);
        printf("dhcpd: discover #%d (xid=%08x)\n", attempt + 1, (unsigned)g_xid);
        if (dhcp_sendto(fd, &req, 0xFFFFFFFFu, DHCP_SERVER_PORT) < 0) {
            printf("dhcpd: discover send failed\n");
            sleep(2);
            continue;
        }
        time_t deadline = time(0) + (2 << attempt);   /* 2,4,8,16,32 c */
        int r = dhcp_wait_reply(fd, DHCP_TYPE_OFFER, deadline, &rep, out);
        if (r == 0) {
            got_offer = 1;
            break;
        }
        if (r == -2) { printf("dhcpd: NAK on discover\n"); return -1; }
    }
    if (!got_offer) {
        printf("dhcpd: no offer received\n");
        return -1;
    }

    printf("dhcpd: offer ip="); ip_print(out->ip_host);
    if (out->server_host) { printf(" server="); ip_print(out->server_host); }
    printf("\n");

    lease_copy_mac(out, mac);
    for (int attempt = 0; attempt < 5; attempt++) {
        /* SELECTING: REQUEST for the chosen address, broadcast, include server id */
        dhcp_build_request(&req, mac, out->ip_host, out->server_host, 0, 1);
        printf("dhcpd: request #%d\n", attempt + 1);
        if (dhcp_sendto(fd, &req, 0xFFFFFFFFu, DHCP_SERVER_PORT) < 0) {
            sleep(2);
            continue;
        }
        time_t deadline = time(0) + (2 << attempt);
        int r = dhcp_wait_reply(fd, DHCP_TYPE_ACK, deadline, &rep, out);
        if (r == 0) return 0;       /* bound */
        if (r == -2) { printf("dhcpd: NAK on request\n"); return -1; }
    }
    printf("dhcpd: no ack received\n");
    return -1;
}

/* Lease renewal: RENEWING (unicast to the server) then REBINDING (broadcast).
 * Returns 0 on renewal, -1 on failure (lease expired). */
static int dhcp_renew(int fd, const uint8_t mac[6], lease_t *ls) {
    struct dhcp_hdr req, rep;
    time_t now = time(0);

    lease_copy_mac(ls, mac);
    for (int attempt = 0; attempt < 4; attempt++) {
        g_xid = (uint32_t)((uint32_t)getpid() << 16) ^
                (uint32_t)(time(0) + attempt) ^ 0xD00DFEEDu;
        if (attempt < 2 && ls->server_host) {
            /* RENEWING: directly to the server */
            dhcp_build_request(&req, mac, ls->ip_host, ls->server_host,
                               ls->ip_host, 0);
            printf("dhcpd: renew to server (unicast)\n");
            if (dhcp_sendto(fd, &req, ls->server_host, DHCP_SERVER_PORT) < 0) {
                sleep(2);
                continue;
            }
        } else {
            /* REBINDING: broadcast */
            dhcp_build_request(&req, mac, ls->ip_host, 0, ls->ip_host, 0);
            printf("dhcpd: rebind (broadcast)\n");
            if (dhcp_sendto(fd, &req, 0xFFFFFFFFu, DHCP_SERVER_PORT) < 0) {
                sleep(2);
                continue;
            }
        }
        time_t deadline = time(0) + (2 << attempt);
        int r = dhcp_wait_reply(fd, DHCP_TYPE_ACK, deadline, &rep, ls);
        if (r == 0) return 0;
        if (r == -2) return -1;
    }
    (void)now;
    return -1;
}

static void lease_print(const lease_t *ls) {
    printf("dhcpd: lease ip="); ip_print(ls->ip_host);
    printf(" mask="); ip_print(ls->netmask_host);
    if (ls->gateway_host) { printf(" gw="); ip_print(ls->gateway_host); }
    if (ls->dns_host)     { printf(" dns="); ip_print(ls->dns_host); }
    if (ls->server_host)  { printf(" server="); ip_print(ls->server_host); }
    printf(" lease=%us t1=%us t2=%us\n",
           (unsigned)ls->lease_s, (unsigned)ls->t1_s, (unsigned)ls->t2_s);
}

/* ── SLAAC (IPv6 stateless autoconfiguration, `dhcpd -6`) ─────────────────
 * The kernel exposes a raw ICMPv6 socket (SOCK_RAW/AF_INET6/IPPROTO_ICMPV6);
 * we send a Router Solicitation and apply the address a Router Advertisement
 * advertises.  DHCPv6 (stateful) is not implemented. */

#define ICMPV6_RS 133
#define ICMPV6_RA 134
#define ND_OPT_SRC_LLADDR 1
#define ND_OPT_PREFIX_INFO 3
#define ND_PREFIX_FLAG_A 0x40

static void ip6_print(const uint8_t a[16]) {
    char b[46];
    if (inet_ntop(AF_INET6, a, b, sizeof(b)))
        printf("%s", b);
}

/* EUI-64 interface identifier from a 48-bit MAC (RFC 4291 App. A). */
static void iid_from_mac(const uint8_t mac[6], uint8_t iid[8]) {
    iid[0] = (uint8_t)(mac[0] ^ 0x02);
    iid[1] = mac[1];
    iid[2] = mac[2];
    iid[3] = 0xff;
    iid[4] = 0xfe;
    iid[5] = mac[3];
    iid[6] = mac[4];
    iid[7] = mac[5];
}

/* Zero every bit of `addr` below `prefix_len`. */
static void mask_prefix(uint8_t addr[16], int prefix_len) {
    for (int i = 0; i < 16; i++) {
        int bits = prefix_len - i * 8;
        if (bits >= 8) continue;
        if (bits <= 0) { addr[i] = 0; continue; }
        addr[i] &= (uint8_t)(0xFF << (8 - bits));
    }
}

static int net_apply6(const uint8_t addr[16], uint32_t prefix,
                      const uint8_t gw[16], const uint8_t dns[16]) {
    cact_iface_setcfg6_arg_t cfg;
    memset(&cfg, 0, sizeof(cfg));
    cfg.index  = (uint32_t)g_ifindex;
    cfg.prefix = prefix;
    memcpy(cfg.addr, addr, 16);
    if (gw) memcpy(cfg.gateway, gw, 16);
    if (dns) memcpy(cfg.dns, dns, 16);
    int fd = open("/dev/net", O_RDWR);
    if (fd < 0) return -1;
    int r = ioctl(fd, CACT_NETCTL_IFACE_SETCFG6, &cfg);
    close(fd);
    return r;
}

static int slaac_run(int want_name) {
    cact_iface_info_t link;
    for (;;) {
        int idx = want_name ? iface_index_by_name(g_iface) : 0;
        if (idx >= 0) {
            g_ifindex = idx;
            if (net_get(&link) == 0 && link.link_up && link.mac[0] != 0) {
                int ll_nonzero = 0;
                for (int k = 0; k < 16; k++)
                    if (link.ip6_link_local[k]) ll_nonzero = 1;
                if (ll_nonzero) break;
            }
        }
        sleep(1);
    }
    printf("dhcpd: SLAAC on %s, link-local ", link.name);
    ip6_print(link.ip6_link_local);
    printf("\n");

    int fd = socket(AF_INET6, SOCK_RAW, IPPROTO_ICMPV6);
    if (fd < 0) {
        printf("dhcpd: cannot open raw ICMPv6 socket\n");
        return 1;
    }
    /* Bind to the interface's link-local, so the raw socket is placed on that NIC. */
    struct sockaddr_in6 la;
    memset(&la, 0, sizeof(la));
    la.sin6_family = AF_INET6;
    memcpy(la.sin6_addr.s6_addr, link.ip6_link_local, 16);
    (void)bind(fd, (struct sockaddr *)&la, sizeof(la));

    struct sockaddr_in6 dst;
    memset(&dst, 0, sizeof(dst));
    dst.sin6_family = AF_INET6;
    (void)inet_pton(AF_INET6, "ff02::2", dst.sin6_addr.s6_addr);

    for (;;) {
        /* Router Solicitation: type, code, checksum(kernel), reserved(4),
         * Source Link-Layer Address option. */
        uint8_t rs[16];
        int n = 0;
        rs[n++] = ICMPV6_RS;
        rs[n++] = 0;
        rs[n++] = 0; rs[n++] = 0;   /* checksum — the kernel fills it */
        rs[n++] = 0; rs[n++] = 0; rs[n++] = 0; rs[n++] = 0;
        rs[n++] = ND_OPT_SRC_LLADDR;
        rs[n++] = 1;                /* length in 8-octet units */
        memcpy(rs + n, link.mac, 6);
        n += 6;

        printf("dhcpd: SLAAC: sending Router Solicitation\n");
        (void)sendto(fd, rs, n, 0, (struct sockaddr *)&dst, sizeof(dst));

        for (int tries = 0; tries < 8; tries++) {
            struct pollfd pfd;
            pfd.fd = fd;
            pfd.events = POLLIN;
            pfd.revents = 0;
            if (poll(&pfd, 1, 500) <= 0)
                continue;
            uint8_t buf[256];
            struct sockaddr_in6 src;
            uint32_t sl = sizeof(src);
            int r = recvfrom(fd, buf, sizeof(buf), 0, (struct sockaddr *)&src, &sl);
            if (r < 16 || buf[0] != ICMPV6_RA)
                continue;

            /* ICMPv6 RA header is 16 bytes; then options. */
            uint16_t router_lifetime = (uint16_t)((buf[4] << 8) | buf[5]);
            int oi = 16;
            while (oi + 2 <= r) {
                uint8_t t = buf[oi];
                uint8_t l = buf[oi + 1];
                int olen = (int)l * 8;
                if (l == 0 || oi + olen > r)
                    break;
                if (t == ND_OPT_PREFIX_INFO && olen >= 32) {
                    uint8_t plen  = buf[oi + 2];
                    uint8_t flags = buf[oi + 3];
                    const uint8_t *prefix = buf + oi + 16;
                    if ((flags & ND_PREFIX_FLAG_A) && plen <= 64) {
                        uint8_t addr[16];
                        memcpy(addr, prefix, 16);
                        mask_prefix(addr, plen);
                        iid_from_mac(link.mac, addr + 8);
                        printf("dhcpd: SLAAC prefix ");
                        ip6_print(prefix);
                        printf("/%u -> addr ", (unsigned)plen);
                        ip6_print(addr);
                        printf(", gw ");
                        ip6_print(src.sin6_addr.s6_addr);
                        printf("\n");
                        if (router_lifetime != 0) {
                            if (net_apply6(addr, plen, src.sin6_addr.s6_addr, 0) != 0)
                                printf("dhcpd: SLAAC: IFACE_SETCFG6 failed (root needed?)\n");
                            else
                                printf("dhcpd: SLAAC address applied\n");
                        }
                        close(fd);
                        return 0;   /* the kernel holds the address; one cycle suffices */
                    }
                }
                oi += olen;
            }
        }
        printf("dhcpd: SLAAC: no Router Advertisement yet, retrying\n");
        sleep(2);
    }
}

/* ── DHCPv6 (RFC 8415) — `dhcpd -6 -D` ────────────────────────────────────
 * Stateful DHCPv6: SOLICIT → ADVERTISE → REQUEST → REPLY over UDPv6 to
 * ff02::1:2:547.  We take the address from IA_NA (an IAADDR is /128) and the
 * resolver from the DNS-servers option; the default route is not carried by
 * DHCPv6, so a short Router Advertisement listen supplies it. */

#define DH6_CLIENT_PORT 546
#define DH6_SERVER_PORT 547
#define DH6_SOLICIT     1
#define DH6_ADVERTISE   2
#define DH6_REQUEST     3
#define DH6_REPLY       7

#define DH6_OPT_CLIENTID    1
#define DH6_OPT_SERVERID    2
#define DH6_OPT_IA_NA       3
#define DH6_OPT_IAADDR      5
#define DH6_OPT_ORO         6
#define DH6_OPT_ELAPSED     8
#define DH6_OPT_DNS_SERVERS 23

static uint32_t g_dh6_iaid = 0x0cac0001u;

/* Find option `code` in a DHCPv6 message body starting at `off`; returns its
 * value pointer, writing the value length to `*olen`, or NULL. */
static const uint8_t *dh6_find(const uint8_t *msg, int len, int off,
                               uint16_t code, int *olen) {
    while (off + 4 <= len) {
        uint16_t c = (uint16_t)((msg[off] << 8) | msg[off + 1]);
        uint16_t l = (uint16_t)((msg[off + 2] << 8) | msg[off + 3]);
        off += 4;
        if (off + l > len) return 0;
        if (c == code) { if (olen) *olen = l; return msg + off; }
        off += l;
    }
    return 0;
}

static int dh6_put(uint8_t *buf, int off, int cap,
                   uint16_t code, const uint8_t *val, int vlen) {
    if (off + 4 + vlen > cap) return off;
    buf[off++] = (uint8_t)(code >> 8);
    buf[off++] = (uint8_t)code;
    buf[off++] = (uint8_t)(vlen >> 8);
    buf[off++] = (uint8_t)vlen;
    if (vlen) { memcpy(buf + off, val, vlen); off += vlen; }
    return off;
}

static int dh6_send(int fd, const struct sockaddr_in6 *srv, uint8_t code,
                    const uint8_t mac[6], const uint8_t *server_id, int server_id_len) {
    uint8_t m[256];
    int o = 0;
    m[o++] = code;
    m[o++] = (uint8_t)(g_xid >> 16);
    m[o++] = (uint8_t)(g_xid >> 8);
    m[o++] = (uint8_t)g_xid;
    /* Client ID: DUID-LL (type 3, hwtype 1 Ethernet, MAC). */
    uint8_t duid[10];
    duid[0] = 0; duid[1] = 3; duid[2] = 0; duid[3] = 1;
    memcpy(duid + 4, mac, 6);
    o = dh6_put(m, o, (int)sizeof(m), DH6_OPT_CLIENTID, duid, 10);
    if (server_id && server_id_len > 0)
        o = dh6_put(m, o, (int)sizeof(m), DH6_OPT_SERVERID, server_id, server_id_len);
    /* IA_NA: IAID + T1(0) + T2(0), no IAADDR in a SOLICIT. */
    uint8_t ia[12];
    ia[0] = (uint8_t)(g_dh6_iaid >> 24); ia[1] = (uint8_t)(g_dh6_iaid >> 16);
    ia[2] = (uint8_t)(g_dh6_iaid >> 8);  ia[3] = (uint8_t)g_dh6_iaid;
    ia[4] = ia[5] = ia[6] = ia[7] = 0;
    ia[8] = ia[9] = ia[10] = ia[11] = 0;
    o = dh6_put(m, o, (int)sizeof(m), DH6_OPT_IA_NA, ia, 12);
    /* ORO: DNS servers; Elapsed Time 0. */
    uint8_t oro[2]; oro[0] = 0; oro[1] = DH6_OPT_DNS_SERVERS;
    o = dh6_put(m, o, (int)sizeof(m), DH6_OPT_ORO, oro, 2);
    uint8_t el[2]; el[0] = 0; el[1] = 0;
    o = dh6_put(m, o, (int)sizeof(m), DH6_OPT_ELAPSED, el, 2);
    return sendto(fd, m, o, 0, (const struct sockaddr *)srv, sizeof(*srv)) < 0 ? -1 : 0;
}

/* Poll for a message of `want_type`; copies it into `buf`, returns its length. */
static int dh6_recv(int fd, uint8_t *buf, int cap, uint8_t want_type, int timeout_ms) {
    for (int waited = 0; waited < timeout_ms; waited += 200) {
        struct pollfd pfd; pfd.fd = fd; pfd.events = POLLIN; pfd.revents = 0;
        if (poll(&pfd, 1, 200) <= 0) continue;
        int r = (int)recv(fd, buf, (uint32_t)cap, 0);
        if (r >= 4 && buf[0] == want_type) return r;
    }
    return -1;
}

/* Short Router Solicitation/Advertisement exchange for the default router's
 * link-local address (DHCPv6 carries no default route). */
static int ra_router_listen(int rawfd, const uint8_t mac[6], uint8_t out_router[16]) {
    struct sockaddr_in6 dst;
    memset(&dst, 0, sizeof(dst));
    dst.sin6_family = AF_INET6;
    (void)inet_pton(AF_INET6, "ff02::2", dst.sin6_addr.s6_addr);
    uint8_t rs[16];
    int n = 0;
    rs[n++] = ICMPV6_RS; rs[n++] = 0;
    rs[n++] = 0; rs[n++] = 0; rs[n++] = 0; rs[n++] = 0; rs[n++] = 0; rs[n++] = 0;
    rs[n++] = ND_OPT_SRC_LLADDR; rs[n++] = 1;
    memcpy(rs + n, mac, 6); n += 6;
    (void)sendto(rawfd, rs, n, 0, (struct sockaddr *)&dst, sizeof(dst));
    for (int i = 0; i < 6; i++) {
        struct pollfd pfd; pfd.fd = rawfd; pfd.events = POLLIN; pfd.revents = 0;
        if (poll(&pfd, 1, 500) <= 0) continue;
        uint8_t buf[256];
        struct sockaddr_in6 src;
        uint32_t sl = sizeof(src);
        int r = recvfrom(rawfd, buf, sizeof(buf), 0, (struct sockaddr *)&src, &sl);
        if (r >= 16 && buf[0] == ICMPV6_RA) {
            if (out_router) memcpy(out_router, src.sin6_addr.s6_addr, 16);
            return 0;
        }
    }
    return -1;
}

static int dhcpv6_run(int want_name) {
    cact_iface_info_t link;
    for (;;) {
        int idx = want_name ? iface_index_by_name(g_iface) : 0;
        if (idx >= 0) {
            g_ifindex = idx;
            if (net_get(&link) == 0 && link.link_up && link.mac[0] != 0) {
                int ll = 0;
                for (int k = 0; k < 16; k++)
                    if (link.ip6_link_local[k]) ll = 1;
                if (ll) break;
            }
        }
        sleep(1);
    }
    printf("dhcpd: DHCPv6 on %s\n", link.name);
    g_xid = (uint32_t)time(0) ^ ((uint32_t)getpid() << 8);

    int fd = socket(AF_INET6, SOCK_DGRAM, IPPROTO_UDP);
    if (fd < 0) { printf("dhcpd: cannot open DHCPv6 UDP socket\n"); return 1; }
    struct sockaddr_in6 local;
    memset(&local, 0, sizeof(local));
    local.sin6_family = AF_INET6;
    local.sin6_port   = htons(DH6_CLIENT_PORT);
    memcpy(local.sin6_addr.s6_addr, link.ip6_link_local, 16);  /* pin to this NIC */
    if (bind(fd, (struct sockaddr *)&local, sizeof(local)) < 0)
        printf("dhcpd: DHCPv6 bind :546 failed\n");

    struct sockaddr_in6 srv;
    memset(&srv, 0, sizeof(srv));
    srv.sin6_family = AF_INET6;
    srv.sin6_port   = htons(DH6_SERVER_PORT);
    (void)inet_pton(AF_INET6, "ff02::1:2", srv.sin6_addr.s6_addr);

    for (;;) {
        printf("dhcpd: DHCPv6: sending SOLICIT\n");
        if (dh6_send(fd, &srv, DH6_SOLICIT, link.mac, 0, 0) < 0) { sleep(2); continue; }
        uint8_t buf[512];
        int r = dh6_recv(fd, buf, sizeof(buf), DH6_ADVERTISE, 3000);
        if (r < 0) { printf("dhcpd: DHCPv6: no ADVERTISE, retrying\n"); sleep(2); continue; }
        int sid_len = 0;
        const uint8_t *sid = dh6_find(buf, r, 4, DH6_OPT_SERVERID, &sid_len);
        uint8_t server_id[130];
        int have_sid = 0;
        if (sid && sid_len > 0 && sid_len <= (int)sizeof(server_id)) {
            memcpy(server_id, sid, sid_len);
            have_sid = 1;
        }
        printf("dhcpd: DHCPv6: ADVERTISE, sending REQUEST\n");
        if (dh6_send(fd, &srv, DH6_REQUEST, link.mac, have_sid ? server_id : 0, sid_len) < 0) {
            sleep(2);
            continue;
        }
        r = dh6_recv(fd, buf, sizeof(buf), DH6_REPLY, 3000);
        if (r < 0) { printf("dhcpd: DHCPv6: no REPLY, retrying\n"); sleep(2); continue; }

        /* IA_NA → IAADDR → address. */
        uint8_t addr[16];
        int have_addr = 0;
        int ia_len = 0;
        const uint8_t *ia = dh6_find(buf, r, 4, DH6_OPT_IA_NA, &ia_len);
        if (ia && ia_len >= 12) {
            int alen = 0;
            const uint8_t *iaaddr = dh6_find(ia, ia_len, 12, DH6_OPT_IAADDR, &alen);
            if (iaaddr && alen >= 16) { memcpy(addr, iaaddr, 16); have_addr = 1; }
        }
        uint8_t dns[16];
        int have_dns = 0;
        int dlen = 0;
        const uint8_t *d = dh6_find(buf, r, 4, DH6_OPT_DNS_SERVERS, &dlen);
        if (d && dlen >= 16) { memcpy(dns, d, 16); have_dns = 1; }

        if (!have_addr) {
            printf("dhcpd: DHCPv6 REPLY without an address\n");
            close(fd);
            return 1;
        }
        printf("dhcpd: DHCPv6 addr "); ip6_print(addr);
        if (have_dns) { printf(" dns "); ip6_print(dns); }
        printf("\n");

        uint8_t router[16];
        memset(router, 0, sizeof(router));
        int rawfd = socket(AF_INET6, SOCK_RAW, IPPROTO_ICMPV6);
        if (rawfd >= 0) {
            struct sockaddr_in6 la;
            memset(&la, 0, sizeof(la));
            la.sin6_family = AF_INET6;
            memcpy(la.sin6_addr.s6_addr, link.ip6_link_local, 16);
            (void)bind(rawfd, (struct sockaddr *)&la, sizeof(la));
            if (ra_router_listen(rawfd, link.mac, router) == 0) {
                printf("dhcpd: DHCPv6 router from RA "); ip6_print(router); printf("\n");
            }
            close(rawfd);
        }

        if (net_apply6(addr, 128, router[0] ? router : 0, have_dns ? dns : 0) != 0)
            printf("dhcpd: DHCPv6: IFACE_SETCFG6 failed (root needed?)\n");
        else
            printf("dhcpd: DHCPv6 address applied\n");
        close(fd);
        return 0;
    }
}

int main(int argc, char *argv[]) {
    int foreground = 1;
    int want_name = 0;
    int slaac = 0;
    int dhcpv6 = 0;
    for (int i = 1; i < argc; i++) {
        if (argv[i][0] != '-') continue;
        if (argv[i][1] == 'i' && i + 1 < argc) {
            g_iface = argv[++i];
            want_name = 1;
        } else if (argv[i][1] == '6') {
            slaac = 1;
        } else if (argv[i][1] == 'D') {
            dhcpv6 = 1;   /* stateful DHCPv6 (implies -6) */
        } else if (argv[i][1] == 'f') {
            foreground = 1;
        } else if (argv[i][1] == 'd') {
            foreground = 0;   /* «daemon»: hint only, we detach manually below */
        }
    }
    (void)foreground;

    if (slaac)
        return dhcpv6 ? dhcpv6_run(want_name) : slaac_run(want_name);
    if (dhcpv6)
        return dhcpv6_run(want_name);
    for (;;) {
        /* wait for the target card to appear (and resolve -i IFACE to an index) */
        cact_iface_info_t link;
        memset(&link, 0, sizeof(link));
        for (;;) {
            int idx = want_name ? iface_index_by_name(g_iface) : 0;
            if (idx < 0) { sleep(1); continue; }
            g_ifindex = idx;
            if (net_get(&link) == 0 && link.link_up && link.mac[0] != 0)
                break;
            sleep(1);
        }
        printf("dhcpd: link up, mac=%02x:%02x:%02x:%02x:%02x:%02x\n",
               link.mac[0], link.mac[1], link.mac[2],
               link.mac[3], link.mac[4], link.mac[5]);

        int fd = dhcp_socket();
        if (fd < 0) {
            printf("dhcpd: cannot open DHCP socket (bind :68)\n");
            sleep(3);
            continue;
        }

        lease_t ls;
        memset(&ls, 0, sizeof(ls));
        if (dhcp_acquire(fd, link.mac, &ls) != 0) {
            close(fd);
            sleep(5);
            continue;   /* no server / network not ready — retry */
        }

        if (net_apply(&ls) != 0) {
            printf("dhcpd: failed to apply config (root needed?)\n");
            close(fd);
            sleep(3);
            continue;
        }
        lease_print(&ls);

        /* BOUND: sleep until T1, then renew; on failure — until T2 and full restart */
        int renewed = 0;
        time_t bound_at = time(0);
        while (1) {
            time_t renew_at = bound_at + (time_t)ls.t1_s;
            time_t dead_at  = bound_at + (time_t)ls.lease_s;
            while (time(0) < renew_at)
                sleep(5);

            printf("dhcpd: attempting renewal at T1\n");
            if (dhcp_renew(fd, link.mac, &ls) == 0) {
                if (net_apply(&ls) == 0)
                    lease_print(&ls);
                bound_at = time(0);
                renewed = 1;
                continue;
            }
            printf("dhcpd: renewal failed, will rebind until lease end\n");
            while (time(0) < dead_at)
                sleep(5);
            renewed = 0;
            break;
        }
        (void)renewed;
        close(fd);
        printf("dhcpd: lease cycle finished, restarting\n");
    }
    return 0;
}
