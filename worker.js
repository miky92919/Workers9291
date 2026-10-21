/**
 * Config panel for Cloudflare Workers
 *
 * What it does
 *   - relays VLESS and Trojan over WebSocket (TLS is terminated by Cloudflare)
 *   - serves a settings panel at /panel (password protected, bilingual fa/en)
 *   - serves subscriptions at /sub/<token>:  raw links (base64), Xray JSON,
 *     sing-box JSON and Clash/Mihomo YAML  (?app=raw|xray|singbox|clash)
 *
 * Setup
 *   1. Workers & Pages -> Create -> Worker, paste this file, deploy.
 *   2. Storage & Databases -> KV -> create a namespace, then in the Worker:
 *      Settings -> Bindings -> Add -> KV namespace, variable name:  kv
 *   3. Open https://<your-worker>/panel and set the admin password right away.
 */
import { connect } from 'cloudflare:sockets';

const WS_PATH = '/ws?ed=2560';
const TLS_PORTS = [443, 8443, 2053, 2083, 2087, 2096];
const FINGERPRINTS = ['chrome', 'firefox', 'safari', 'ios', 'android', 'edge', 'randomized', 'random'];
const DOH_FOR_UDP = 'https://1.1.1.1/dns-query';
const SESSION_DAYS = 7;

const ECH_DEFAULT_OUTBOUND = {
  tag: 'tls-repack-dns',
  protocol: 'direct',
  settings: { redirect: '1.1.1.1:443' },
  streamSettings: {
    security: 'tls',
    tlsSettings: {
      serverName: 'www.microsoft.com',
      verifyPeerCertByName: 'fromMitM,www.microsoft.com',
      alpn: ['fromMitM'],
      fingerprint: 'chrome'
    }
  }
};

/* ------------------------------------------------------------------ */
/* small helpers                                                       */
/* ------------------------------------------------------------------ */

const enc = new TextEncoder();
const dec = new TextDecoder();

function randomHex(n) {
  const b = crypto.getRandomValues(new Uint8Array(n));
  return [...b].map((x) => x.toString(16).padStart(2, '0')).join('');
}
function randomPass(n) {
  const chars = 'ABCDEFGHJKLMNPQRSTUVWXYZabcdefghijkmnopqrstuvwxyz23456789';
  const b = crypto.getRandomValues(new Uint8Array(n));
  let s = '';
  for (const x of b) s += chars[x % chars.length];
  return s;
}
function hexToBytes(h) {
  const o = new Uint8Array(h.length / 2);
  for (let i = 0; i < o.length; i++) o[i] = parseInt(h.substr(i * 2, 2), 16);
  return o;
}
function bytesToHex(b) {
  return [...b].map((x) => x.toString(16).padStart(2, '0')).join('');
}
function b64urlDecode(s) {
  s = s.replace(/-/g, '+').replace(/_/g, '/');
  while (s.length % 4) s += '=';
  const bin = atob(s);
  const o = new Uint8Array(bin.length);
  for (let i = 0; i < bin.length; i++) o[i] = bin.charCodeAt(i);
  return o;
}
function concat(a, b) {
  const o = new Uint8Array(a.length + b.length);
  o.set(a, 0);
  o.set(b, a.length);
  return o;
}
function toBytes(d) {
  if (d instanceof ArrayBuffer) return new Uint8Array(d);
  if (ArrayBuffer.isView(d)) return new Uint8Array(d.buffer, d.byteOffset, d.byteLength);
  return enc.encode(String(d));
}
function safeEq(a, b) {
  if (a.length !== b.length) return false;
  let r = 0;
  for (let i = 0; i < a.length; i++) r |= a.charCodeAt(i) ^ b.charCodeAt(i);
  return r === 0;
}
function json(data, status = 200, extra = {}) {
  return new Response(JSON.stringify(data), {
    status,
    headers: { 'content-type': 'application/json; charset=utf-8', 'cache-control': 'no-store', ...extra }
  });
}
function brackets(a) {
  return a.includes(':') && !a.startsWith('[') ? '[' + a + ']' : a;
}
function isIPv4(s) {
  return /^(\d{1,3})\.(\d{1,3})\.(\d{1,3})\.(\d{1,3})$/.test(s) && s.split('.').every((n) => +n <= 255);
}

/* ------------------------------------------------------------------ */
/* SHA-224 (needed for the Trojan password hash; WebCrypto has none)   */
/* ------------------------------------------------------------------ */

const SHA_K = (() => {
  const k = [];
  let n = 2;
  while (k.length < 64) {
    let p = true;
    for (let i = 2; i * i <= n; i++) if (n % i === 0) { p = false; break; }
    if (p) k.push(Math.floor((Math.cbrt(n) % 1) * 4294967296));
    n++;
  }
  return k;
})();

function sha224(str) {
  const bytes = enc.encode(str);
  const l = bytes.length;
  const n = ((l + 9 + 63) >> 6) << 6;
  const buf = new Uint8Array(n);
  buf.set(bytes);
  buf[l] = 0x80;
  const dv = new DataView(buf.buffer);
  dv.setUint32(n - 8, Math.floor(l / 0x20000000));
  dv.setUint32(n - 4, (l << 3) >>> 0);
  let h = [0xc1059ed8, 0x367cd507, 0x3070dd17, 0xf70e5939, 0xffc00b31, 0x68581511, 0x64f98fa7, 0xbefa4fa4];
  const w = new Uint32Array(64);
  for (let o = 0; o < n; o += 64) {
    for (let i = 0; i < 16; i++) w[i] = dv.getUint32(o + i * 4);
    for (let i = 16; i < 64; i++) {
      const a = w[i - 15], b = w[i - 2];
      const s0 = ((a >>> 7) | (a << 25)) ^ ((a >>> 18) | (a << 14)) ^ (a >>> 3);
      const s1 = ((b >>> 17) | (b << 15)) ^ ((b >>> 19) | (b << 13)) ^ (b >>> 10);
      w[i] = (w[i - 16] + s0 + w[i - 7] + s1) | 0;
    }
    let [a, b, c, d, e, f, g, hh] = h;
    for (let i = 0; i < 64; i++) {
      const S1 = ((e >>> 6) | (e << 26)) ^ ((e >>> 11) | (e << 21)) ^ ((e >>> 25) | (e << 7));
      const ch = (e & f) ^ (~e & g);
      const t1 = (hh + S1 + ch + SHA_K[i] + w[i]) | 0;
      const S0 = ((a >>> 2) | (a << 30)) ^ ((a >>> 13) | (a << 19)) ^ ((a >>> 22) | (a << 10));
      const maj = (a & b) ^ (a & c) ^ (b & c);
      const t2 = (S0 + maj) | 0;
      hh = g; g = f; f = e; e = (d + t1) | 0; d = c; c = b; b = a; a = (t1 + t2) | 0;
    }
    h = [(h[0] + a) | 0, (h[1] + b) | 0, (h[2] + c) | 0, (h[3] + d) | 0, (h[4] + e) | 0, (h[5] + f) | 0, (h[6] + g) | 0, (h[7] + hh) | 0];
  }
  return h.slice(0, 7).map((x) => (x >>> 0).toString(16).padStart(8, '0')).join('');
}

let trCache = { p: '', h: '' };
function trojanHash(pass) {
  if (trCache.p !== pass) trCache = { p: pass, h: sha224(pass) };
  return trCache.h;
}

/* ------------------------------------------------------------------ */
/* settings                                                            */
/* ------------------------------------------------------------------ */

function defaults() {
  return {
    remark: 'Panel',
    uuid: crypto.randomUUID(),
    trPass: randomPass(16),
    subToken: randomHex(16),
    protocols: ['vless', 'trojan'],
    ports: [443],
    cleanIPs: [],
    proxyIPs: [],
    fp: 'chrome',
    remoteDNS: 'https://8.8.8.8/dns-query',
    localDNS: '8.8.8.8',
    bypassIran: true,
    bypassLAN: true,
    blockAds: false,
    blockQUIC: true,
    fragment: { enabled: false, packets: 'tlshello', length: '100-200', interval: '1-1' },
    ech: { enabled: false, config: 'h2c://1.1.1.1/dns-query', outbound: JSON.stringify(ECH_DEFAULT_OUTBOUND, null, 2) }
  };
}

let settingsCache = { t: 0, v: null };
async function getSettings(env, fresh) {
  if (!fresh && settingsCache.v && Date.now() - settingsCache.t < 30000) return settingsCache.v;
  const stored = await env.kv.get('settings', 'json');
  const v = stored ? { ...defaults(), ...stored, fragment: { ...defaults().fragment, ...(stored.fragment || {}) }, ech: { ...defaults().ech, ...(stored.ech || {}) } } : null;
  settingsCache = { t: Date.now(), v };
  return v;
}
async function putSettings(env, s) {
  await env.kv.put('settings', JSON.stringify(s));
  settingsCache = { t: Date.now(), v: s };
}

function toList(v) {
  if (Array.isArray(v)) v = v.join('\n');
  return [...new Set(String(v || '').split(/[\s,]+/).map((x) => x.trim()).filter(Boolean))];
}

// returns { ok: settings } or { error: code }
function sanitize(inp, cur) {
  const s = { ...cur };
  s.remark = String(inp.remark || '').trim().slice(0, 30) || 'Panel';

  const protocols = (Array.isArray(inp.protocols) ? inp.protocols : []).filter((p) => p === 'vless' || p === 'trojan');
  if (!protocols.length) return { error: 'no_protocol' };
  s.protocols = protocols;

  const ports = (Array.isArray(inp.ports) ? inp.ports : []).map(Number).filter((p) => TLS_PORTS.includes(p));
  if (!ports.length) return { error: 'no_port' };
  s.ports = [...new Set(ports)];

  const clean = toList(inp.cleanIPs);
  const hostRe = /^(\[[0-9a-fA-F:]+\]|[A-Za-z0-9.-]+|[0-9a-fA-F:]+)$/;
  if (clean.some((x) => !hostRe.test(x))) return { error: 'bad_clean_ip' };
  s.cleanIPs = clean.map((x) => x.replace(/^\[|\]$/g, ''));

  const px = toList(inp.proxyIPs);
  if (px.some((x) => !/^[A-Za-z0-9.-]+(:\d{1,5})?$/.test(x) && !/^\[[0-9a-fA-F:]+\](:\d{1,5})?$/.test(x))) return { error: 'bad_proxy_ip' };
  s.proxyIPs = px;

  s.fp = FINGERPRINTS.includes(inp.fp) ? inp.fp : 'chrome';

  const rd = String(inp.remoteDNS || '').trim();
  if (!/^https:\/\/[^\s/]+(\/\S*)?$/.test(rd)) return { error: 'bad_remote_dns' };
  s.remoteDNS = rd;
  const ld = String(inp.localDNS || '').trim();
  if (!isIPv4(ld)) return { error: 'bad_local_dns' };
  s.localDNS = ld;

  s.bypassIran = !!inp.bypassIran;
  s.bypassLAN = !!inp.bypassLAN;
  s.blockAds = !!inp.blockAds;
  s.blockQUIC = !!inp.blockQUIC;

  const f = inp.fragment || {};
  const range = /^\d{1,4}-\d{1,4}$/;
  if (!range.test(String(f.length || '')) || !range.test(String(f.interval || ''))) return { error: 'bad_fragment' };
  s.fragment = {
    enabled: !!f.enabled,
    packets: ['tlshello', '1-3'].includes(f.packets) ? f.packets : 'tlshello',
    length: String(f.length),
    interval: String(f.interval)
  };

  const e = inp.ech || {};
  const config = String(e.config || '').trim();
  const outText = String(e.outbound || '').trim() || JSON.stringify(ECH_DEFAULT_OUTBOUND, null, 2);
  if (e.enabled && !config) return { error: 'bad_ech' };
  if (e.enabled && /h2c:\/\//i.test(config) && !parseEchOutbound(outText)) return { error: 'bad_ech_outbound' };
  s.ech = { enabled: !!e.enabled, config: config || 'h2c://1.1.1.1/dns-query', outbound: outText };

  return { ok: s };
}

function parseEchOutbound(text) {
  try {
    const o = JSON.parse(text);
    if (o && typeof o === 'object' && !Array.isArray(o) && typeof o.tag === 'string' && o.tag) return o;
  } catch (e) {}
  return null;
}

/* ------------------------------------------------------------------ */
/* admin auth (PBKDF2 password + HMAC session cookie)                  */
/* ------------------------------------------------------------------ */

async function hashPassword(pw, saltHex) {
  const key = await crypto.subtle.importKey('raw', enc.encode(pw), 'PBKDF2', false, ['deriveBits']);
  const bits = await crypto.subtle.deriveBits({ name: 'PBKDF2', hash: 'SHA-256', salt: hexToBytes(saltHex), iterations: 100000 }, key, 256);
  return bytesToHex(new Uint8Array(bits));
}
async function hmac(secretHex, msg) {
  const key = await crypto.subtle.importKey('raw', hexToBytes(secretHex), { name: 'HMAC', hash: 'SHA-256' }, false, ['sign']);
  return bytesToHex(new Uint8Array(await crypto.subtle.sign('HMAC', key, enc.encode(msg))));
}
async function makeSession(auth) {
  const exp = String(Date.now() + SESSION_DAYS * 86400000);
  return exp + '.' + (await hmac(auth.secret, exp));
}
async function checkSession(request, auth) {
  if (!auth) return false;
  const m = /(?:^|;\s*)__p=([^;]+)/.exec(request.headers.get('cookie') || '');
  if (!m) return false;
  const [exp, sig] = m[1].split('.');
  if (!exp || !sig || +exp < Date.now()) return false;
  return safeEq(sig, await hmac(auth.secret, exp));
}
function cookie(value, maxAge) {
  return '__p=' + value + '; Path=/; HttpOnly; Secure; SameSite=Strict; Max-Age=' + maxAge;
}
async function getAuth(env) {
  return env.kv.get('auth', 'json');
}
async function setPassword(env, pw) {
  const salt = randomHex(16);
  const prev = await getAuth(env);
  const auth = { salt, hash: await hashPassword(pw, salt), secret: prev ? prev.secret : randomHex(32) };
  await env.kv.put('auth', JSON.stringify(auth));
  return auth;
}
async function rateLimited(env, request, hit) {
  const ip = request.headers.get('cf-connecting-ip') || 'x';
  const key = 'rl:' + ip;
  const n = +((await env.kv.get(key)) || 0);
  if (!hit) return n >= 6;
  await env.kv.put(key, String(n + 1), { expirationTtl: 900 });
  return n + 1 >= 6;
}

/* ------------------------------------------------------------------ */
/* proxy: VLESS + Trojan over WebSocket                                */
/* ------------------------------------------------------------------ */

function uuidBytes(u) {
  return hexToBytes(u.replace(/-/g, ''));
}
function readAddr(b, o, type, kinds) {
  // kinds: [ipv4, domain, ipv6] address-type codes
  let host;
  if (type === kinds[0]) {
    host = b.subarray(o, o + 4).join('.');
    o += 4;
  } else if (type === kinds[1]) {
    const l = b[o++];
    host = dec.decode(b.subarray(o, o + l));
    o += l;
  } else if (type === kinds[2]) {
    const parts = [];
    for (let i = 0; i < 8; i++) parts.push(((b[o + i * 2] << 8) | b[o + i * 2 + 1]).toString(16));
    host = parts.join(':');
    o += 16;
  } else return null;
  return { host, o };
}
function parseVless(b, cfg) {
  if (b.length < 24) return null;
  const id = uuidBytes(cfg.uuid);
  for (let i = 0; i < 16; i++) if (b[1 + i] !== id[i]) return null;
  let o = 18 + b[17];
  const cmd = b[o++];
  if (cmd !== 1 && cmd !== 2) return null;
  const port = (b[o] << 8) | b[o + 1];
  o += 2;
  const a = readAddr(b, o + 1, b[o], [1, 2, 3]);
  if (!a) return null;
  return { proto: 'vless', udp: cmd === 2, host: a.host, port, offset: a.o, resp: new Uint8Array([b[0], 0]) };
}
function parseTrojan(b, cfg) {
  if (dec.decode(b.subarray(0, 56)) !== trojanHash(cfg.trPass)) return null;
  let o = 58;
  const cmd = b[o++];
  if (cmd !== 1) return null;
  const a = readAddr(b, o + 1, b[o], [1, 3, 4]);
  if (!a) return null;
  o = a.o;
  const port = (b[o] << 8) | b[o + 1];
  o += 4; // port + CRLF
  return { proto: 'trojan', udp: false, host: a.host, port, offset: o, resp: null };
}
function parseRequest(b, cfg) {
  if (b.length > 58 && b[56] === 13 && b[57] === 10) return cfg.protocols.includes('trojan') ? parseTrojan(b, cfg) : null;
  return cfg.protocols.includes('vless') ? parseVless(b, cfg) : null;
}

function pickProxy(list) {
  if (!list || !list.length) return null;
  const v = list[Math.floor(Math.random() * list.length)];
  const m = /^(\[[^\]]+\]|[^:]+)(?::(\d+))?$/.exec(v);
  return m ? { host: m[1].replace(/^\[|\]$/g, ''), port: m[2] ? +m[2] : 0 } : null;
}

async function pump(sock, ws, resp, retry, close) {
  let got = false;
  let sentResp = !resp;
  try {
    const reader = sock.readable.getReader();
    for (;;) {
      const { done, value } = await reader.read();
      if (done) break;
      if (!value || !value.length) continue;
      got = true;
      if (ws.readyState !== 1) break;
      if (!sentResp) { ws.send(concat(resp, value)); sentResp = true; } else ws.send(value);
    }
  } catch (e) {}
  if (!got && retry) { retry(); return; }
  close();
}

function dnsRelay(ws, resp) {
  let sent = false;
  return async (chunk) => {
    let i = 0;
    while (i + 2 <= chunk.length) {
      const len = (chunk[i] << 8) | chunk[i + 1];
      const q = chunk.subarray(i + 2, i + 2 + len);
      i += 2 + len;
      const r = await fetch(DOH_FOR_UDP, { method: 'POST', headers: { 'content-type': 'application/dns-message' }, body: q });
      const a = new Uint8Array(await r.arrayBuffer());
      const f = new Uint8Array(2 + a.length);
      f[0] = a.length >> 8;
      f[1] = a.length & 255;
      f.set(a, 2);
      if (ws.readyState === 1) ws.send(sent ? f : concat(resp, f));
      sent = true;
    }
  };
}

function session(ws, earlyHeader, cfg) {
  let remote = null, writer = null, dns = null, closed = false;
  const close = () => {
    if (closed) return;
    closed = true;
    try { ws.close(); } catch (e) {}
    try { remote && remote.s.close(); } catch (e) {}
  };

  async function open(h, payload) {
    const dial = async (host, port) => {
      const s = connect({ hostname: host, port });
      await s.opened;
      const w = s.writable.getWriter();
      await w.write(payload);
      return { s, w };
    };
    const attach = (r, canRetry) => {
      remote = r;
      writer = r.w;
      pump(r.s, ws, h.resp, canRetry ? retry : null, close);
    };
    const retry = async () => {
      const px = pickProxy(cfg.proxyIPs);
      if (!px || closed) return close();
      try {
        const r = await dial(px.host, px.port || h.port);
        try { remote.s.close(); } catch (e) {}
        attach(r, false);
      } catch (e) { close(); }
    };
    try { attach(await dial(h.host, h.port), true); } catch (e) { await retry(); }
  }

  async function handle(chunk) {
    if (closed) return;
    if (dns) return dns(chunk);
    if (writer) { await writer.write(chunk); return; }
    const h = parseRequest(chunk, cfg);
    if (!h) throw new Error('bad header');
    const payload = chunk.subarray(h.offset);
    if (h.udp) {
      if (h.port !== 53) throw new Error('udp only for dns');
      dns = dnsRelay(ws, h.resp);
      if (payload.length) await dns(payload);
      return;
    }
    await open(h, payload);
  }

  let chain = Promise.resolve();
  const push = (bytes) => { chain = chain.then(() => handle(bytes)).catch(close); };
  if (earlyHeader) { try { const e = b64urlDecode(earlyHeader); if (e.length) push(e); } catch (e) {} }
  ws.addEventListener('message', (ev) => push(toBytes(ev.data)));
  ws.addEventListener('close', close);
  ws.addEventListener('error', close);
}

async function handleWS(request, env) {
  const cfg = env.kv ? await getSettings(env) : null;
  if (!cfg) return new Response('Not configured', { status: 503 });
  const [client, server] = Object.values(new WebSocketPair());
  server.accept();
  session(server, request.headers.get('sec-websocket-protocol'), cfg);
  return new Response(null, { status: 101, webSocket: client });
}

/* ------------------------------------------------------------------ */
/* subscriptions                                                       */
/* ------------------------------------------------------------------ */

function endpoints(cfg, host) {
  const addrs = [host, ...cfg.cleanIPs.filter((a) => a !== host)];
  const out = [];
  for (const proto of cfg.protocols) {
    for (const addr of addrs) {
      for (const port of cfg.ports) {
        out.push({ proto, addr, port, name: cfg.remark + ' ' + (proto === 'vless' ? 'VLESS' : 'Trojan') + ' ' + addr + ':' + port });
      }
    }
  }
  return out;
}

function echActive(cfg) {
  return cfg.ech.enabled && /h2c:\/\//i.test(cfg.ech.config) ? parseEchOutbound(cfg.ech.outbound) : null;
}

function makeLink(e, cfg, host) {
  const q = new URLSearchParams();
  if (e.proto === 'vless') q.set('encryption', 'none');
  q.set('security', 'tls');
  q.set('sni', host);
  q.set('fp', cfg.fp);
  q.set('alpn', 'http/1.1');
  q.set('type', 'ws');
  q.set('host', host);
  q.set('path', WS_PATH);
  if (cfg.ech.enabled) {
    q.set('ech', cfg.ech.config);
    const ob = echActive(cfg);
    if (ob) q.set('echOutbound', JSON.stringify(ob));
  }
  const user = e.proto === 'vless' ? cfg.uuid : encodeURIComponent(cfg.trPass);
  return e.proto + '://' + user + '@' + brackets(e.addr) + ':' + e.port + '?' + q.toString() + '#' + encodeURIComponent(e.name);
}

function rawSub(cfg, host) {
  return btoa(endpoints(cfg, host).map((e) => makeLink(e, cfg, host)).join('\n'));
}

/* ---- Xray ---- */
function xrayConfig(e, cfg, host) {
  const tls = { serverName: host, fingerprint: cfg.fp, alpn: ['http/1.1'], allowInsecure: false };
  const extra = [];
  if (cfg.ech.enabled) {
    tls.echConfigList = cfg.ech.config;
    const ob = echActive(cfg);
    if (ob) { tls.echSockopt = { dialerProxy: ob.tag }; extra.push(ob); }
  }
  const stream = {
    network: 'ws',
    security: 'tls',
    tlsSettings: tls,
    wsSettings: { path: WS_PATH, host, headers: { Host: host } }
  };
  if (cfg.fragment.enabled) stream.sockopt = { dialerProxy: 'fragment', tcpNoDelay: true };

  const proxy = e.proto === 'vless'
    ? { tag: 'proxy', protocol: 'vless', settings: { vnext: [{ address: e.addr, port: e.port, users: [{ id: cfg.uuid, encryption: 'none', level: 8 }] }] }, streamSettings: stream }
    : { tag: 'proxy', protocol: 'trojan', settings: { servers: [{ address: e.addr, port: e.port, password: cfg.trPass, level: 8 }] }, streamSettings: stream };

  const outbounds = [
    proxy,
    { tag: 'direct', protocol: 'freedom', settings: {} },
    { tag: 'block', protocol: 'blackhole', settings: { response: { type: 'http' } } },
    { tag: 'dns-out', protocol: 'dns' }
  ];
  if (cfg.fragment.enabled) {
    outbounds.push({
      tag: 'fragment',
      protocol: 'freedom',
      settings: { fragment: { packets: cfg.fragment.packets, length: cfg.fragment.length, interval: cfg.fragment.interval } },
      streamSettings: { sockopt: { tcpNoDelay: true } }
    });
  }
  outbounds.push(...extra);

  const servers = [cfg.remoteDNS];
  const rules = [{ type: 'field', inboundTag: ['socks', 'http', 'tun'], port: '53', outboundTag: 'dns-out' }];
  if (cfg.bypassIran) {
    servers.push({ address: cfg.localDNS, domains: ['geosite:category-ir', 'domain:.ir'], tag: 'local-dns' });
    rules.push({ type: 'field', inboundTag: ['local-dns'], outboundTag: 'direct' });
  }
  rules.push({ type: 'field', inboundTag: ['dns'], outboundTag: 'proxy' });
  if (cfg.blockQUIC) rules.push({ type: 'field', network: 'udp', port: '443', outboundTag: 'block' });
  if (cfg.blockAds) rules.push({ type: 'field', domain: ['geosite:category-ads-all', 'geosite:category-ads-ir'], outboundTag: 'block' });
  if (cfg.bypassLAN) rules.push({ type: 'field', ip: ['geoip:private'], outboundTag: 'direct' });
  if (cfg.bypassIran) {
    rules.push({ type: 'field', domain: ['geosite:category-ir', 'domain:.ir'], outboundTag: 'direct' });
    rules.push({ type: 'field', ip: ['geoip:ir'], outboundTag: 'direct' });
  }
  rules.push({ type: 'field', network: 'tcp,udp', outboundTag: 'proxy' });

  return {
    remarks: e.name,
    log: { loglevel: 'warning' },
    dns: { servers, tag: 'dns' },
    inbounds: [
      { tag: 'socks', listen: '127.0.0.1', port: 10808, protocol: 'socks', settings: { auth: 'noauth', udp: true }, sniffing: { enabled: true, destOverride: ['http', 'tls', 'quic'], routeOnly: false } },
      { tag: 'http', listen: '127.0.0.1', port: 10809, protocol: 'http', sniffing: { enabled: true, destOverride: ['http', 'tls', 'quic'], routeOnly: false } }
    ],
    outbounds,
    routing: { domainStrategy: 'IPIfNonMatch', rules }
  };
}
function xraySub(cfg, host) {
  return JSON.stringify(endpoints(cfg, host).map((e) => xrayConfig(e, cfg, host)), null, 2);
}

/* ---- sing-box (1.12+) ---- */
function singNode(e, cfg, host) {
  const base = {
    tag: e.name,
    server: e.addr,
    server_port: e.port,
    tls: { enabled: true, server_name: host, insecure: false, alpn: ['http/1.1'], utls: { enabled: true, fingerprint: cfg.fp } },
    transport: { type: 'ws', path: '/ws', headers: { Host: host }, max_early_data: 2560, early_data_header_name: 'Sec-WebSocket-Protocol' }
  };
  return e.proto === 'vless'
    ? { type: 'vless', ...base, uuid: cfg.uuid }
    : { type: 'trojan', ...base, password: cfg.trPass };
}
function singboxSub(cfg, host) {
  const eps = endpoints(cfg, host);
  const tags = eps.map((e) => e.name);
  const doh = new URL(cfg.remoteDNS);
  const dohServer = { type: 'https', tag: 'dns-remote', server: doh.hostname.replace(/^\[|\]$/g, ''), server_port: +doh.port || 443, path: doh.pathname || '/dns-query', detour: 'proxy' };
  const dnsRules = cfg.bypassIran ? [{ domain_suffix: ['ir'], server: 'dns-local' }] : [];
  const routeRules = [{ action: 'sniff' }, { protocol: 'dns', action: 'hijack-dns' }];
  if (cfg.blockQUIC) routeRules.push({ protocol: 'quic', action: 'reject' });
  if (cfg.bypassLAN) routeRules.push({ ip_is_private: true, outbound: 'direct' });
  if (cfg.bypassIran) routeRules.push({ domain_suffix: ['ir'], outbound: 'direct' });
  return JSON.stringify({
    log: { level: 'warn', timestamp: true },
    dns: {
      servers: [dohServer, { type: 'udp', tag: 'dns-local', server: cfg.localDNS }],
      rules: dnsRules,
      final: 'dns-remote',
      strategy: 'prefer_ipv4'
    },
    inbounds: [
      { type: 'tun', tag: 'tun-in', address: ['172.19.0.1/28'], auto_route: true, strict_route: true, stack: 'mixed' },
      { type: 'mixed', tag: 'mixed-in', listen: '127.0.0.1', listen_port: 2080 }
    ],
    outbounds: [
      { type: 'selector', tag: 'proxy', outbounds: ['auto', ...tags], default: 'auto' },
      { type: 'urltest', tag: 'auto', outbounds: tags, url: 'https://www.gstatic.com/generate_204', interval: '10m', tolerance: 50 },
      ...eps.map((e) => singNode(e, cfg, host)),
      { type: 'direct', tag: 'direct' }
    ],
    route: { rules: routeRules, final: 'proxy', auto_detect_interface: true, default_domain_resolver: 'dns-local' },
    experimental: { cache_file: { enabled: true } }
  }, null, 2);
}

/* ---- Clash / Mihomo ---- */
function clashSub(cfg, host) {
  const eps = endpoints(cfg, host);
  const fp = cfg.fp === 'randomized' ? 'random' : cfg.fp;
  const j = JSON.stringify;
  const proxies = eps.map((e) => {
    const p = { name: e.name, type: e.proto, server: e.addr, port: e.port };
    if (e.proto === 'vless') { p.uuid = cfg.uuid; p.tls = true; p.servername = host; } else { p.password = cfg.trPass; p.sni = host; }
    Object.assign(p, {
      udp: true,
      network: 'ws',
      'skip-cert-verify': false,
      'client-fingerprint': fp,
      alpn: ['http/1.1'],
      'ws-opts': { path: '/ws', headers: { Host: host }, 'max-early-data': 2560, 'early-data-header-name': 'Sec-WebSocket-Protocol' }
    });
    return p;
  });
  const names = eps.map((e) => e.name);
  const rules = [];
  if (cfg.bypassLAN) {
    for (const c of ['10.0.0.0/8', '172.16.0.0/12', '192.168.0.0/16', '127.0.0.0/8', '100.64.0.0/10', '169.254.0.0/16']) rules.push('IP-CIDR,' + c + ',DIRECT,no-resolve');
  }
  if (cfg.bypassIran) rules.push('DOMAIN-SUFFIX,ir,DIRECT');
  rules.push('MATCH,Proxy');
  const lines = [
    'mixed-port: 7890',
    'allow-lan: false',
    'mode: rule',
    'log-level: warning',
    'ipv6: false',
    'dns:',
    '  enable: true',
    '  ipv6: false',
    '  enhanced-mode: fake-ip',
    '  fake-ip-range: 198.18.0.1/16',
    '  default-nameserver: [' + j(cfg.localDNS) + ']',
    '  nameserver: [' + j(cfg.remoteDNS) + ']'
  ];
  if (cfg.bypassIran) lines.push('  nameserver-policy: {"+.ir": [' + j(cfg.localDNS) + ']}');
  lines.push('proxies:');
  for (const p of proxies) lines.push('  - ' + j(p));
  lines.push('proxy-groups:');
  lines.push('  - ' + j({ name: 'Proxy', type: 'select', proxies: ['Auto', ...names] }));
  lines.push('  - ' + j({ name: 'Auto', type: 'url-test', proxies: names, url: 'https://www.gstatic.com/generate_204', interval: 300, tolerance: 50 }));
  lines.push('rules:');
  for (const r of rules) lines.push('  - ' + j(r));
  return lines.join('\n') + '\n';
}

function detectApp(ua) {
  if (/sing-box|singbox|sfa|sfi|hiddify/i.test(ua)) return 'singbox';
  if (/clash|mihomo|stash|flclash|verge/i.test(ua)) return 'clash';
  return 'raw';
}

function handleSub(request, url, cfg) {
  const host = url.hostname;
  const app = (url.searchParams.get('app') || detectApp(request.headers.get('user-agent') || '')).toLowerCase();
  const common = { 'cache-control': 'no-store', 'profile-update-interval': '6', 'profile-title': cfg.remark };
  if (app === 'xray') return new Response(xraySub(cfg, host), { headers: { ...common, 'content-type': 'application/json; charset=utf-8' } });
  if (app === 'singbox') return new Response(singboxSub(cfg, host), { headers: { ...common, 'content-type': 'application/json; charset=utf-8' } });
  if (app === 'clash') return new Response(clashSub(cfg, host), { headers: { ...common, 'content-type': 'text/yaml; charset=utf-8' } });
  return new Response(rawSub(cfg, host), { headers: { ...common, 'content-type': 'text/plain; charset=utf-8' } });
}

/* ------------------------------------------------------------------ */
/* routing                                                             */
/* ------------------------------------------------------------------ */

function sameOrigin(request) {
  const o = request.headers.get('origin');
  return !o || new URL(o).host === new URL(request.url).host;
}

async function route(request, env) {
  const url = new URL(request.url);
  const path = url.pathname;

  if ((request.headers.get('upgrade') || '').toLowerCase() === 'websocket') return handleWS(request, env);

  if (path === '/') return Response.redirect(url.origin + '/panel', 302);

  if (!env.kv) {
    if (path === '/panel') return new Response(noKvPage(), { status: 500, headers: { 'content-type': 'text/html; charset=utf-8' } });
    return new Response('KV namespace "kv" is not bound', { status: 500 });
  }

  if (path.startsWith('/sub/')) {
    const cfg = await getSettings(env);
    if (!cfg || !safeEq(path.slice(5), cfg.subToken)) return new Response('Not found', { status: 404 });
    return handleSub(request, url, cfg);
  }

  if (path === '/panel') {
    const auth = await getAuth(env);
    const state = !auth ? 'setup' : (await checkSession(request, auth)) ? 'app' : 'login';
    return new Response(PAGE.replace('__STATE__', state), {
      headers: { 'content-type': 'text/html; charset=utf-8', 'cache-control': 'no-store', 'x-frame-options': 'DENY', 'referrer-policy': 'no-referrer' }
    });
  }

  if (path.startsWith('/api/')) {
    if (request.method !== 'POST' && !(request.method === 'GET' && path === '/api/settings')) return json({ error: 'method' }, 405);
    if (request.method === 'POST' && !sameOrigin(request)) return json({ error: 'origin' }, 403);
    return api(request, env, path);
  }

  return new Response('Not found', { status: 404 });
}

async function api(request, env, path) {
  const auth = await getAuth(env);
  let body = {};
  if (request.method === 'POST') {
    try { body = await request.json(); } catch (e) { return json({ error: 'json' }, 400); }
  }

  if (path === '/api/setup') {
    if (auth) return json({ error: 'exists' }, 409);
    const pw = String(body.password || '');
    if (pw.length < 8) return json({ error: 'weak_password' }, 400);
    const a = await setPassword(env, pw);
    if (!(await getSettings(env, true))) await putSettings(env, defaults());
    return json({ ok: true }, 200, { 'set-cookie': cookie(await makeSession(a), SESSION_DAYS * 86400) });
  }

  if (path === '/api/login') {
    if (!auth) return json({ error: 'no_setup' }, 400);
    if (await rateLimited(env, request, false)) return json({ error: 'rate' }, 429);
    const ok = safeEq(await hashPassword(String(body.password || ''), auth.salt), auth.hash);
    if (!ok) {
      await rateLimited(env, request, true);
      return json({ error: 'bad_password' }, 401);
    }
    return json({ ok: true }, 200, { 'set-cookie': cookie(await makeSession(auth), SESSION_DAYS * 86400) });
  }

  if (!(await checkSession(request, auth))) return json({ error: 'auth' }, 401);

  if (path === '/api/logout') return json({ ok: true }, 200, { 'set-cookie': cookie('', 0) });

  if (path === '/api/settings') {
    const cur = (await getSettings(env, true)) || defaults();
    if (request.method === 'GET') return json({ settings: cur, ports: TLS_PORTS, fingerprints: FINGERPRINTS });
    const r = sanitize(body, cur);
    if (r.error) return json({ error: r.error }, 400);
    await putSettings(env, r.ok);
    return json({ ok: true, settings: r.ok });
  }

  if (path === '/api/regen') {
    const cur = (await getSettings(env, true)) || defaults();
    if (body.what === 'uuid') cur.uuid = crypto.randomUUID();
    else if (body.what === 'trojan') cur.trPass = randomPass(16);
    else if (body.what === 'sub') cur.subToken = randomHex(16);
    else return json({ error: 'what' }, 400);
    await putSettings(env, cur);
    return json({ ok: true, settings: cur });
  }

  if (path === '/api/password') {
    const pw = String(body.password || '');
    if (pw.length < 8) return json({ error: 'weak_password' }, 400);
    const a = await setPassword(env, pw);
    return json({ ok: true }, 200, { 'set-cookie': cookie(await makeSession(a), SESSION_DAYS * 86400) });
  }

  return json({ error: 'not_found' }, 404);
}

export default {
  async fetch(request, env) {
    try {
      return await route(request, env);
    } catch (e) {
      return new Response('Error: ' + (e && e.message ? e.message : e), { status: 500 });
    }
  }
};

/* ------------------------------------------------------------------ */
/* panel page                                                          */
/* ------------------------------------------------------------------ */

function noKvPage() {
  return '<!doctype html><meta charset="utf-8"><meta name="viewport" content="width=device-width,initial-scale=1">' +
    '<body style="font-family:system-ui,Tahoma,sans-serif;max-width:34rem;margin:3rem auto;padding:0 1rem;line-height:1.7">' +
    '<h2>KV is not connected</h2><p>Worker settings, Bindings, Add, KV namespace. Set the variable name to <b>kv</b>, then reload this page.</p>' +
    '<p dir="rtl">در تنظیمات Worker بخش Bindings یک KV namespace با نام متغیر <b>kv</b> وصل کنید و صفحه را دوباره باز کنید.</p></body>';
}

const PAGE = String.raw`<!doctype html>
<html lang="fa" dir="rtl">
<head>
<meta charset="utf-8">
<meta name="viewport" content="width=device-width, initial-scale=1">
<meta name="robots" content="noindex">
<meta name="theme-color" content="#0e2a35">
<title>Panel</title>
<style>
:root{
  --bg:#e9f0f2; --surface:#ffffff; --ink:#0e2a35; --muted:#587079; --line:#cddbe0;
  --accent:#0b7f86; --accent-ink:#ffffff; --warn:#b4531a; --field:#f5f9fa; --good:#1b7a4b;
  --mono:ui-monospace,"SF Mono",Menlo,Consolas,monospace;
  --sans:system-ui,-apple-system,"Segoe UI",Tahoma,"Noto Sans Arabic",sans-serif;
}
@media (prefers-color-scheme:dark){
  :root{--bg:#0a1a21;--surface:#112832;--ink:#e3eff2;--muted:#8ba5ae;--line:#1f3c48;--accent:#3cc4c9;--accent-ink:#06242a;--warn:#f0a06a;--field:#0d212a;--good:#59c890}
}
*{box-sizing:border-box}
html{-webkit-text-size-adjust:100%}
body{margin:0;background:var(--bg);color:var(--ink);font:16px/1.65 var(--sans)}
button,input,select,textarea{font:inherit;color:inherit}
header{position:sticky;top:0;z-index:5;background:var(--ink);color:var(--bg);display:flex;align-items:center;gap:.75rem;padding:.7rem 1rem}
header h1{margin:0;font-size:1.05rem;font-weight:700;flex:1}
header button{background:transparent;border:1px solid currentColor;color:inherit;border-radius:.5rem;padding:.2rem .7rem;cursor:pointer}
main{max-width:42rem;margin:0 auto;padding:1rem 1rem 6rem}
.hero{background:var(--ink);color:var(--bg);border-radius:1rem;padding:1.1rem 1rem 1rem;margin-bottom:1rem}
.hero h2{margin:0 0 .15rem;font-size:1.25rem}
.hero p{margin:0 0 .8rem;font-size:.9rem;opacity:.8}
.sub{display:grid;grid-template-columns:5.2rem 1fr auto;gap:.5rem;align-items:center;padding:.5rem 0;border-top:1px solid rgba(255,255,255,.14)}
.sub b{font-weight:600}
.sub code{direction:ltr;text-align:left;font:.78rem/1.3 var(--mono);overflow:hidden;text-overflow:ellipsis;white-space:nowrap;opacity:.85}
.btn{border:0;border-radius:.6rem;padding:.5rem .9rem;background:var(--accent);color:var(--accent-ink);font-weight:600;cursor:pointer}
.btn.ghost{background:transparent;color:inherit;border:1px solid var(--line)}
.hero .btn{background:var(--bg);color:var(--ink);padding:.3rem .8rem}
details{background:var(--surface);border:1px solid var(--line);border-radius:.9rem;margin:0 0 .7rem}
summary{cursor:pointer;list-style:none;padding:.85rem 1rem;font-weight:700;display:flex;justify-content:space-between;align-items:center}
summary::-webkit-details-marker{display:none}
summary::after{content:"+";font-weight:400;font-size:1.3rem;color:var(--muted)}
details[open] summary::after{content:"\2212"}
.body{padding:0 1rem 1rem;display:grid;gap:.85rem}
label.f{display:grid;gap:.3rem;font-size:.92rem}
label.f span,.cap{color:var(--muted);font-size:.85rem}
input[type=text],input[type=password],select,textarea{width:100%;background:var(--field);border:1px solid var(--line);border-radius:.6rem;padding:.55rem .7rem;direction:ltr;text-align:left}
textarea{min-height:5.5rem;font:.85rem/1.5 var(--mono);resize:vertical}
.ltr{direction:ltr;text-align:left}
.checks{display:flex;flex-wrap:wrap;gap:.5rem}
.chip{display:inline-flex;align-items:center;gap:.4rem;background:var(--field);border:1px solid var(--line);border-radius:2rem;padding:.3rem .8rem;cursor:pointer;user-select:none}
.chip input{accent-color:var(--accent)}
.row{display:flex;align-items:center;justify-content:space-between;gap:.6rem}
.row input[type=checkbox]{width:1.3rem;height:1.3rem;accent-color:var(--accent)}
.val{display:flex;gap:.5rem;align-items:center}
.val code{flex:1;direction:ltr;text-align:left;font:.82rem var(--mono);background:var(--field);border:1px solid var(--line);border-radius:.6rem;padding:.5rem .7rem;overflow:hidden;text-overflow:ellipsis;white-space:nowrap}
.hint{margin:0;color:var(--muted);font-size:.84rem}
.bar{position:fixed;inset:auto 0 0 0;background:var(--surface);border-top:1px solid var(--line);padding:.7rem 1rem;display:flex;justify-content:center;gap:.7rem;z-index:6}
.bar .btn{min-width:10rem}
.toast{position:fixed;left:50%;bottom:4.6rem;transform:translateX(-50%);background:var(--ink);color:var(--bg);padding:.5rem 1rem;border-radius:.6rem;opacity:0;pointer-events:none;transition:opacity .2s;z-index:9;max-width:90vw}
.toast.on{opacity:1}
.toast.err{background:var(--warn);color:#fff}
.gate{max-width:24rem;margin:12vh auto 0;background:var(--surface);border:1px solid var(--line);border-radius:1rem;padding:1.3rem;display:grid;gap:.8rem}
.gate h2{margin:0}
.hide{display:none!important}
button:focus-visible,input:focus-visible,select:focus-visible,textarea:focus-visible,summary:focus-visible{outline:2px solid var(--accent);outline-offset:2px}
@media (prefers-reduced-motion:reduce){*{transition:none!important}}
</style>
</head>
<body>
<header>
  <h1 id="ttl">Panel</h1>
  <button id="lang" type="button">EN</button>
  <button id="out" type="button" class="hide" data-i="logout"></button>
</header>

<main id="gate" class="hide">
  <form class="gate" id="gateForm" autocomplete="on">
    <h2 id="gateT"></h2>
    <p class="hint" id="gateH"></p>
    <input type="password" id="gpw" autocomplete="current-password" aria-label="password">
    <button class="btn" type="submit" id="gateB"></button>
  </form>
</main>

<main id="app" class="hide">
  <section class="hero">
    <h2 data-i="subs"></h2>
    <p data-i="subsHint"></p>
    <div id="subs"></div>
  </section>

  <details open>
    <summary data-i="conn"></summary>
    <div class="body">
      <label class="f"><span data-i="remark"></span><input type="text" id="remark" maxlength="30"></label>
      <div><div class="cap" data-i="protocols"></div>
        <div class="checks">
          <label class="chip"><input type="checkbox" id="p_vless"> VLESS</label>
          <label class="chip"><input type="checkbox" id="p_trojan"> Trojan</label>
        </div></div>
      <div><div class="cap" data-i="ports"></div><div class="checks" id="ports"></div></div>
      <label class="f"><span data-i="cleanIPs"></span><textarea id="cleanIPs" spellcheck="false" placeholder="104.16.1.1&#10;example.com"></textarea>
        <p class="hint" data-i="cleanHint"></p></label>
      <label class="f"><span data-i="proxyIPs"></span><textarea id="proxyIPs" spellcheck="false" placeholder="proxy.example.com&#10;203.0.113.5:443"></textarea>
        <p class="hint" data-i="proxyHint"></p></label>
      <label class="f"><span data-i="fp"></span><select id="fp"></select></label>
    </div>
  </details>

  <details>
    <summary data-i="dns"></summary>
    <div class="body">
      <label class="f"><span data-i="remoteDNS"></span><input type="text" id="remoteDNS" placeholder="https://8.8.8.8/dns-query"></label>
      <label class="f"><span data-i="localDNS"></span><input type="text" id="localDNS" placeholder="8.8.8.8"></label>
      <label class="row"><span data-i="bypassIran"></span><input type="checkbox" id="bypassIran"></label>
      <label class="row"><span data-i="bypassLAN"></span><input type="checkbox" id="bypassLAN"></label>
      <label class="row"><span data-i="blockQUIC"></span><input type="checkbox" id="blockQUIC"></label>
      <label class="row"><span data-i="blockAds"></span><input type="checkbox" id="blockAds"></label>
      <p class="hint" data-i="dnsHint"></p>
    </div>
  </details>

  <details>
    <summary data-i="frag"></summary>
    <div class="body">
      <label class="row"><span data-i="fragOn"></span><input type="checkbox" id="fragOn"></label>
      <label class="f"><span data-i="fragPackets"></span><select id="fragPackets"><option value="tlshello">tlshello</option><option value="1-3">1-3</option></select></label>
      <label class="f"><span data-i="fragLen"></span><input type="text" id="fragLen" placeholder="100-200"></label>
      <label class="f"><span data-i="fragInt"></span><input type="text" id="fragInt" placeholder="1-1"></label>
      <p class="hint" data-i="fragHint"></p>
    </div>
  </details>

  <details>
    <summary data-i="ech"></summary>
    <div class="body">
      <label class="row"><span data-i="echOn"></span><input type="checkbox" id="echOn"></label>
      <label class="f"><span data-i="echValue"></span>
        <select id="echPreset">
          <option value="h2c://1.1.1.1/dns-query">h2c://1.1.1.1/dns-query</option>
          <option value="https://1.1.1.1/dns-query">https://1.1.1.1/dns-query</option>
          <option value="https://8.8.8.8/dns-query">https://8.8.8.8/dns-query</option>
          <option value="https://8.8.4.4/dns-query">https://8.8.4.4/dns-query</option>
          <option value="udp://1.1.1.1">udp://1.1.1.1</option>
          <option value="">custom</option>
        </select></label>
      <input type="text" id="echValue" aria-label="echConfigList">
      <label class="f"><span data-i="echOut"></span><textarea id="echOut" spellcheck="false" style="min-height:14rem"></textarea></label>
      <p class="hint" data-i="echHint"></p>
    </div>
  </details>

  <details>
    <summary data-i="acct"></summary>
    <div class="body">
      <div><div class="cap">UUID (VLESS)</div><div class="val"><code id="uuid"></code><button class="btn ghost" type="button" data-regen="uuid" data-i="regen"></button></div></div>
      <div><div class="cap" data-i="trPass"></div><div class="val"><code id="trPass"></code><button class="btn ghost" type="button" data-regen="trojan" data-i="regen"></button></div></div>
      <div><div class="cap" data-i="subToken"></div><div class="val"><code id="subToken"></code><button class="btn ghost" type="button" data-regen="sub" data-i="regen"></button></div></div>
      <p class="hint" data-i="regenHint"></p>
      <label class="f"><span data-i="newPass"></span><input type="password" id="npw" autocomplete="new-password"></label>
      <button class="btn ghost" type="button" id="chPw" data-i="changePass"></button>
    </div>
  </details>

  <div class="bar"><button class="btn" type="button" id="save" data-i="save"></button></div>
</main>
<div class="toast" id="toast" role="status" aria-live="polite"></div>

<script>
var STATE="__STATE__";
var $=function(i){return document.getElementById(i)};
var T={
fa:{title:"پنل کانفیگ",logout:"خروج",subs:"لینک‌های اشتراک",subsHint:"هر لینک را در برنامه‌ات به‌عنوان اشتراک اضافه کن.",copy:"کپی",copied:"کپی شد",
 conn:"اتصال",remark:"نام کانفیگ‌ها",protocols:"پروتکل",ports:"پورت TLS",cleanIPs:"آی‌پی یا دامنه‌ی تمیز",cleanHint:"هر خط یک مورد. به ازای هر مورد یک کانفیگ ساخته می‌شود. دامنه‌ی خود Worker همیشه هست.",
 proxyIPs:"ProxyIP (پشتیبان)",proxyHint:"برای سایت‌هایی که پشت کلادفلر هستند لازم است. هر خط یک مورد، با پورت اختیاری.",fp:"اثرانگشت TLS",
 dns:"DNS و مسیریابی",remoteDNS:"DNS از راه دور (DoH)",localDNS:"DNS داخلی",bypassIran:"سایت‌های ایرانی مستقیم",bypassLAN:"شبکه محلی مستقیم",blockQUIC:"بستن QUIC",blockAds:"بستن تبلیغات (فقط Xray)",
 dnsHint:"برای DoH از آدرس آی‌پی استفاده کن. قوانین ایران برای sing-box و Clash فقط بر پایه‌ی پسوند ir. است.",
 frag:"Fragment (فقط Xray)",fragOn:"فعال",fragPackets:"بسته‌ها",fragLen:"طول",fragInt:"فاصله (میلی‌ثانیه)",fragHint:"TLS hello را تکه‌تکه می‌فرستد.",
 ech:"ECH",echOn:"ECH در لینک و Xray",echValue:"echConfigList",echOut:"echOutbound (JSON خام)",echHint:"وقتی مقدار با h2c:// شروع شود، پارامتر echOutbound به لینک‌ها و خروجی Xray اضافه می‌شود. sing-box و Clash از این روش پشتیبانی نمی‌کنند.",
 acct:"حساب",trPass:"رمز Trojan",subToken:"توکن اشتراک",regen:"ساخت دوباره",regenHint:"با ساخت دوباره‌ی UUID یا رمز، کانفیگ‌های قبلی از کار می‌افتند. با تغییر توکن، لینک‌های اشتراک قبلی باطل می‌شوند.",
 newPass:"رمز جدید پنل",changePass:"تغییر رمز",save:"ذخیره",saved:"ذخیره شد",
 gateLogin:"ورود",gateSetup:"ساخت رمز مدیر",gateSetupH:"اولین بار است. یک رمز حداقل ۸ کاراکتری بساز.",gateLoginH:"رمز پنل را وارد کن.",enter:"ورود",create:"ساخت رمز",
 e_bad_password:"رمز اشتباه است.",e_weak_password:"رمز باید حداقل ۸ کاراکتر باشد.",e_rate:"تلاش زیاد. کمی بعد دوباره امتحان کن.",e_auth:"نشست تمام شده. دوباره وارد شو.",
 e_no_protocol:"حداقل یک پروتکل انتخاب کن.",e_no_port:"حداقل یک پورت انتخاب کن.",e_bad_clean_ip:"آی‌پی یا دامنه‌ی تمیز معتبر نیست.",e_bad_proxy_ip:"ProxyIP معتبر نیست.",
 e_bad_remote_dns:"DNS از راه دور باید با https:// شروع شود.",e_bad_local_dns:"DNS داخلی باید آی‌پی IPv4 باشد.",e_bad_fragment:"طول و فاصله را به شکل 100-200 بنویس.",
 e_bad_ech:"مقدار echConfigList خالی است.",e_bad_ech_outbound:"echOutbound باید آبجکت JSON معتبر با فیلد tag باشد.",e_network:"ارتباط با Worker برقرار نشد."},
en:{title:"Config panel",logout:"Log out",subs:"Subscriptions",subsHint:"Add each link as a subscription in your client.",copy:"Copy",copied:"Copied",
 conn:"Connection",remark:"Config name",protocols:"Protocols",ports:"TLS ports",cleanIPs:"Clean IPs or domains",cleanHint:"One per line. Each one gets its own configs. The Worker domain is always included.",
 proxyIPs:"ProxyIP (fallback)",proxyHint:"Needed for sites behind Cloudflare. One per line, port optional.",fp:"TLS fingerprint",
 dns:"DNS and routing",remoteDNS:"Remote DNS (DoH)",localDNS:"Local DNS",bypassIran:"Iranian sites direct",bypassLAN:"Local network direct",blockQUIC:"Block QUIC",blockAds:"Block ads (Xray only)",
 dnsHint:"Use an IP-based DoH address. The Iran rules for sing-box and Clash only match the .ir suffix.",
 frag:"Fragment (Xray only)",fragOn:"Enabled",fragPackets:"Packets",fragLen:"Length",fragInt:"Interval (ms)",fragHint:"Splits the TLS hello into pieces.",
 ech:"ECH",echOn:"ECH in links and Xray",echValue:"echConfigList",echOut:"echOutbound (raw JSON)",echHint:"When the value starts with h2c://, the echOutbound param is added to links and to the Xray output. sing-box and Clash do not support this method.",
 acct:"Account",trPass:"Trojan password",subToken:"Subscription token",regen:"Regenerate",regenHint:"Regenerating the UUID or password breaks existing configs. Changing the token invalidates old subscription links.",
 newPass:"New panel password",changePass:"Change password",save:"Save changes",saved:"Saved",
 gateLogin:"Log in",gateSetup:"Create the admin password",gateSetupH:"First run. Choose a password of at least 8 characters.",gateLoginH:"Enter the panel password.",enter:"Log in",create:"Create password",
 e_bad_password:"Wrong password.",e_weak_password:"The password needs at least 8 characters.",e_rate:"Too many attempts. Try again later.",e_auth:"Session expired. Log in again.",
 e_no_protocol:"Pick at least one protocol.",e_no_port:"Pick at least one port.",e_bad_clean_ip:"A clean IP or domain is not valid.",e_bad_proxy_ip:"A ProxyIP is not valid.",
 e_bad_remote_dns:"Remote DNS must start with https://.",e_bad_local_dns:"Local DNS must be an IPv4 address.",e_bad_fragment:"Write length and interval like 100-200.",
 e_bad_ech:"echConfigList is empty.",e_bad_ech_outbound:"echOutbound must be a valid JSON object with a tag field.",e_network:"Could not reach the Worker."}
};
var lang=localStorage.getItem("lang")||"fa";
var cur=null;
function tr(k){return (T[lang][k]!==undefined?T[lang][k]:k)}
function applyLang(){
  document.documentElement.lang=lang;document.documentElement.dir=lang==="fa"?"rtl":"ltr";
  $("lang").textContent=lang==="fa"?"EN":"FA";$("ttl").textContent=tr("title");document.title=tr("title");
  var n=document.querySelectorAll("[data-i]");for(var i=0;i<n.length;i++){n[i].textContent=tr(n[i].getAttribute("data-i"))}
  $("gateT").textContent=STATE==="setup"?tr("gateSetup"):tr("gateLogin");
  $("gateH").textContent=STATE==="setup"?tr("gateSetupH"):tr("gateLoginH");
  $("gateB").textContent=STATE==="setup"?tr("create"):tr("enter");
}
var tt;
function toast(msg,err){var t=$("toast");t.textContent=msg;t.className="toast on"+(err?" err":"");clearTimeout(tt);tt=setTimeout(function(){t.className="toast"},2600)}
function api(path,body){
  return fetch(path,{method:body===undefined?"GET":"POST",headers:{"content-type":"application/json"},body:body===undefined?undefined:JSON.stringify(body),credentials:"same-origin"})
   .then(function(r){return r.json().then(function(j){j._status=r.status;return j})})
   .catch(function(){return {error:"network"}});
}
function errText(j){return T[lang]["e_"+j.error]||j.error}
function copy(text){
  if(navigator.clipboard&&navigator.clipboard.writeText){return navigator.clipboard.writeText(text)}
  var a=document.createElement("textarea");a.value=text;document.body.appendChild(a);a.select();document.execCommand("copy");document.body.removeChild(a);return Promise.resolve();
}
function show(){
  $("gate").className=STATE==="app"?"hide":"";$("app").className=STATE==="app"?"":"hide";
  $("out").className=STATE==="app"?"":"hide";applyLang();
}
function renderSubs(){
  var base=location.origin+"/sub/"+cur.subToken;
  var rows=[["raw",""],["Xray","?app=xray"],["sing-box","?app=singbox"],["Clash","?app=clash"]];
  var h="";
  for(var i=0;i<rows.length;i++){
    h+='<div class="sub"><b>'+rows[i][0]+'</b><code>'+base+rows[i][1]+'</code><button class="btn" type="button" data-copy="'+base+rows[i][1]+'">'+tr("copy")+'</button></div>';
  }
  $("subs").innerHTML=h;
}
function fill(d){
  cur=d.settings;var s=cur;
  $("remark").value=s.remark;
  $("p_vless").checked=s.protocols.indexOf("vless")>=0;$("p_trojan").checked=s.protocols.indexOf("trojan")>=0;
  var p="";for(var i=0;i<d.ports.length;i++){var v=d.ports[i];p+='<label class="chip"><input type="checkbox" name="port" value="'+v+'"'+(s.ports.indexOf(v)>=0?" checked":"")+'> '+v+'</label>'}
  $("ports").innerHTML=p;
  var f="";for(var j=0;j<d.fingerprints.length;j++){f+='<option value="'+d.fingerprints[j]+'">'+d.fingerprints[j]+'</option>'}
  $("fp").innerHTML=f;$("fp").value=s.fp;
  $("cleanIPs").value=s.cleanIPs.join("\n");$("proxyIPs").value=s.proxyIPs.join("\n");
  $("remoteDNS").value=s.remoteDNS;$("localDNS").value=s.localDNS;
  $("bypassIran").checked=s.bypassIran;$("bypassLAN").checked=s.bypassLAN;$("blockQUIC").checked=s.blockQUIC;$("blockAds").checked=s.blockAds;
  $("fragOn").checked=s.fragment.enabled;$("fragPackets").value=s.fragment.packets;$("fragLen").value=s.fragment.length;$("fragInt").value=s.fragment.interval;
  $("echOn").checked=s.ech.enabled;$("echValue").value=s.ech.config;$("echOut").value=s.ech.outbound;syncPreset();
  $("uuid").textContent=s.uuid;$("trPass").textContent=s.trPass;$("subToken").textContent=s.subToken;
  renderSubs();
}
function syncPreset(){
  var sel=$("echPreset"),v=$("echValue").value,hit=false;
  for(var i=0;i<sel.options.length;i++){if(sel.options[i].value===v&&v!==""){hit=true}}
  sel.value=hit?v:"";
}
function collect(){
  var pr=[];if($("p_vless").checked)pr.push("vless");if($("p_trojan").checked)pr.push("trojan");
  var ports=[],c=document.querySelectorAll("input[name=port]:checked");for(var i=0;i<c.length;i++){ports.push(+c[i].value)}
  return {remark:$("remark").value,protocols:pr,ports:ports,cleanIPs:$("cleanIPs").value,proxyIPs:$("proxyIPs").value,fp:$("fp").value,
    remoteDNS:$("remoteDNS").value,localDNS:$("localDNS").value,bypassIran:$("bypassIran").checked,bypassLAN:$("bypassLAN").checked,blockQUIC:$("blockQUIC").checked,blockAds:$("blockAds").checked,
    fragment:{enabled:$("fragOn").checked,packets:$("fragPackets").value,length:$("fragLen").value,interval:$("fragInt").value},
    ech:{enabled:$("echOn").checked,config:$("echValue").value,outbound:$("echOut").value}};
}
function load(){api("/api/settings").then(function(j){if(j.error){if(j.error==="auth"){STATE="login";show()}else{toast(errText(j),true)}return}fill(j)})}

$("lang").onclick=function(){lang=lang==="fa"?"en":"fa";localStorage.setItem("lang",lang);applyLang();if(cur)renderSubs()};
$("echPreset").onchange=function(){if(this.value!==""){$("echValue").value=this.value}else{$("echValue").focus()}};
$("echValue").oninput=syncPreset;
$("gateForm").onsubmit=function(e){
  e.preventDefault();
  api(STATE==="setup"?"/api/setup":"/api/login",{password:$("gpw").value}).then(function(j){
    if(j.error){toast(errText(j),true);return}
    STATE="app";$("gpw").value="";show();load();
  });
};
$("out").onclick=function(){api("/api/logout",{}).then(function(){STATE="login";cur=null;show()})};
$("save").onclick=function(){
  api("/api/settings",collect()).then(function(j){if(j.error){toast(errText(j),true);return}fill({settings:j.settings,ports:[443,8443,2053,2083,2087,2096],fingerprints:[].map.call($("fp").options,function(o){return o.value})});toast(tr("saved"))});
};
document.addEventListener("click",function(e){
  var t=e.target;
  if(t.getAttribute&&t.getAttribute("data-copy")){copy(t.getAttribute("data-copy")).then(function(){toast(tr("copied"))});return}
  if(t.getAttribute&&t.getAttribute("data-regen")){
    api("/api/regen",{what:t.getAttribute("data-regen")}).then(function(j){if(j.error){toast(errText(j),true);return}cur=j.settings;$("uuid").textContent=cur.uuid;$("trPass").textContent=cur.trPass;$("subToken").textContent=cur.subToken;renderSubs();toast(tr("saved"))});
  }
});
$("chPw").onclick=function(){
  api("/api/password",{password:$("npw").value}).then(function(j){if(j.error){toast(errText(j),true);return}$("npw").value="";toast(tr("saved"))});
};
show();
if(STATE==="app")load();
</script>
</body>
</html>`;
