#!/usr/bin/env python3
"""
AuctionWatch -- standalone FFXI item & Auction-House browser.

Search FFXI items by name, see their description / category / stack size, and
pull live Auction House sales history straight from your world's search server
(no game running required -- the search server answers unauthenticated).

Needs `ffxi_items.json` (the bundled item database) next to this file, or
bundled into the exe. Pure standard library + tkinter -- no pip installs.
"""
import base64
import hashlib
import socket
import os
import sys
import subprocess
import time
import json
import gzip
import re
import math
import mmap
import struct
import threading
import zlib
import datetime
import statistics
import webbrowser
import collections as _collections
import tkinter as tk
from tkinter import ttk
from tkinter import font as tkfont

_DEFAULT_SERVER = "124.150.154.63"

import struct as _ahsrch_struct
import hashlib as _ahsrch_hashlib

_AHSRCH_PORT = 54002
_AHSRCH_MASK = 0xFFFFFFFF
_AHSRCH_KEY_SEED = bytes((0x30, 0x73, 0x3D, 0x6D, 0x3C, 0x31, 0x49, 0x5A,
                          0x32, 0x7A, 0x42, 0x43, 0x63, 0x38, 0x7B, 0x7E))
_AHSRCH_IXFF = 0x46465849
_AHSRCH_HIST_SINGLE = 0x05
_AHSRCH_HIST_STACK = 0x06
_AHSRCH_SUBKEY = base64.b64decode(
    "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"
    "349X5nLDOg=="
)


def _ahsrch_load_ps():
    P = list(_ahsrch_struct.unpack("<18I", _AHSRCH_SUBKEY[0:72]))
    S = list(_ahsrch_struct.unpack("<1024I", _AHSRCH_SUBKEY[72:72 + 4096]))
    return P, S


def _ahsrch_TT(x, S):
    return ((((S[256 + ((x >> 8) & 0xFF)] & 1) ^ 32)
             + ((S[768 + ((x >> 24) & 0xFF)] & 1) ^ 32)
             + S[512 + ((x >> 16) & 0xFF)]
             + S[x & 0xFF]) & _AHSRCH_MASK)


def _ahsrch_encipher(xl, xr, P, S):
    for i in range(16):
        xl = (xl ^ P[i]) & _AHSRCH_MASK
        xr = (_ahsrch_TT(xl, S) ^ xr) & _AHSRCH_MASK
        xl, xr = xr, xl
    xl, xr = xr, xl
    xr = (xr ^ P[16]) & _AHSRCH_MASK
    xl = (xl ^ P[17]) & _AHSRCH_MASK
    return xl, xr


def _ahsrch_decipher(xl, xr, P, S):
    for i in range(17, 1, -1):
        xl = (xl ^ P[i]) & _AHSRCH_MASK
        xr = (_ahsrch_TT(xl, S) ^ xr) & _AHSRCH_MASK
        xl, xr = xr, xl
    xl, xr = xr, xl
    xr = (xr ^ P[1]) & _AHSRCH_MASK
    xl = (xl ^ P[0]) & _AHSRCH_MASK
    return xl, xr


def _ahsrch_blowfish_init(key_bytes):
    # The server treats the key as SIGNED int8, so digest bytes >= 0x80
    # sign-extend when folded into the P-array. Replicate exactly.
    P, S = _ahsrch_load_ps()
    n = len(key_bytes)
    j = 0
    for i in range(18):
        data = 0
        for _ in range(4):
            b = key_bytes[j]
            sb = b - 256 if b >= 128 else b
            data = ((data << 8) | (sb & _AHSRCH_MASK)) & _AHSRCH_MASK
            j += 1
            if j >= n:
                j = 0
        P[i] = (P[i] ^ data) & _AHSRCH_MASK
    dl, dr = 0, 0
    for i in range(0, 18, 2):
        dl, dr = _ahsrch_encipher(dl, dr, P, S)
        P[i], P[i + 1] = dl, dr
    for i in range(4):
        for k in range(0, 256, 2):
            dl, dr = _ahsrch_encipher(dl, dr, P, S)
            S[i * 256 + k], S[i * 256 + k + 1] = dl, dr
    return P, S


def _ahsrch_cipher_blocks(buf, length, P, S, decrypt):
    tmp = (length - 12) // 4
    tmp -= tmp % 2
    i = 0
    while i < tmp:
        o = 8 + i * 4
        xl, xr = _ahsrch_struct.unpack_from("<II", buf, o)
        xl, xr = (_ahsrch_decipher if decrypt else _ahsrch_encipher)(xl, xr, P, S)
        _ahsrch_struct.pack_into("<II", buf, o, xl, xr)
        i += 2


def _ahsrch_md5(b):
    return _ahsrch_hashlib.md5(b).digest()


def _ahsrch_build_request(item_id, stack=False, key_tail=None):
    # Matches the real retail client packet family (from a live capture): 76
    # bytes; size@0x00, IXFF@0x04, then [u16 size][0x80 flag][type] at 0x08.
    # The 0x80 flag byte at 0x0A is required — without it the server stays
    # silent. itemid@0x12, stack@0x15. md5 hash + key tail footer.
    if key_tail is None:
        key_tail = os.urandom(4)
    length = 76
    buf = bytearray(length)
    _ahsrch_struct.pack_into("<H", buf, 0x00, length)
    _ahsrch_struct.pack_into("<I", buf, 0x04, _AHSRCH_IXFF)
    _ahsrch_struct.pack_into("<H", buf, 0x08, 16)
    buf[0x0A] = 0x80
    buf[0x0B] = _AHSRCH_HIST_STACK if stack else _AHSRCH_HIST_SINGLE
    _ahsrch_struct.pack_into("<H", buf, 0x12, item_id & 0xFFFF)
    buf[0x15] = 1 if stack else 0
    buf[length - 0x14:length - 0x04] = _ahsrch_md5(bytes(buf[0x08:length - 0x14]))
    buf[length - 0x04:length] = key_tail
    P, S = _ahsrch_blowfish_init(_ahsrch_md5(_AHSRCH_KEY_SEED + key_tail))
    _ahsrch_cipher_blocks(buf, length, P, S, decrypt=False)
    return bytes(buf), key_tail


def _ahsrch_req_key20_24(item_id, stack):
    # We zero the key2 region (length-0x18) in the request, so the server
    # derives key2 = 0 for response encryption; mirror that here.
    return b"\x00\x00\x00\x00"


def _ahsrch_decode_name(raw):
    z = raw.find(b"\x00")
    if z >= 0:
        raw = raw[:z]
    return raw.decode("latin-1", "replace").strip()


def _ahsrch_parse_response(buf, key_tail, req_key20_24):
    buf = bytearray(buf)
    length = _ahsrch_struct.unpack_from("<H", buf, 0x00)[0]
    if length < 28 or length > len(buf):
        raise ValueError("bad response length %d (have %d bytes)" % (length, len(buf)))
    P, S = _ahsrch_blowfish_init(_ahsrch_md5(_AHSRCH_KEY_SEED + key_tail + req_key20_24))
    _ahsrch_cipher_blocks(buf, length, P, S, decrypt=True)
    item_id = _ahsrch_struct.unpack_from("<H", buf, 0x18)[0]
    amount = _ahsrch_struct.unpack_from("<I", buf, 0x1A)[0]
    category = _ahsrch_struct.unpack_from("<H", buf, 0x1E)[0]
    marker = _ahsrch_struct.unpack_from("<H", buf, 0x08)[0]
    n = max(0, (marker - 0x20) // 40)
    sales = []
    for i in range(n):
        o = 0x20 + 40 * i
        if o + 40 > length:
            break
        price = _ahsrch_struct.unpack_from("<I", buf, o + 0x00)[0]
        date = _ahsrch_struct.unpack_from("<I", buf, o + 0x04)[0]
        seller = _ahsrch_decode_name(bytes(buf[o + 0x08:o + 0x08 + 15]))
        buyer = _ahsrch_decode_name(bytes(buf[o + 0x18:o + 0x18 + 15]))
        sales.append({"price": price, "date": date, "seller": seller, "buyer": buyer})
    return {"item_id": item_id, "amount": amount, "category": category, "sales": sales}


class _AhsrchProto(Exception):
    def __init__(self, msg, data=b"", sent=0):
        self.data = data
        self.sent = sent
        super().__init__(msg)


def _ahsrch_query(host, port, item_id, stack=False, timeout=8.0):
    req, key_tail = _ahsrch_build_request(item_id, stack)
    key20_24 = _ahsrch_req_key20_24(item_id, stack)
    with socket.create_connection((host, port), timeout=timeout) as s:
        s.sendall(req)
        s.settimeout(timeout)
        data = b""
        try:
            while True:
                chunk = s.recv(4096)
                if not chunk:
                    break
                data += chunk
                if len(data) >= 2 and len(data) >= _ahsrch_struct.unpack_from("<H", data, 0)[0]:
                    break
        except socket.timeout:
            pass
    if len(data) < 2 or len(data) < _ahsrch_struct.unpack_from("<H", data, 0)[0]:
        raise _AhsrchProto("short response", data, len(req))
    return _ahsrch_parse_response(data, key_tail, key20_24)


def _ahsrch_no_window_kw():
    # Keep netstat from flashing a console window on Windows.
    import subprocess
    kw = {}
    try:
        if os.name == "nt":
            si = subprocess.STARTUPINFO()
            si.dwFlags |= subprocess.STARTF_USESHOWWINDOW
            si.wShowWindow = 0  # SW_HIDE
            kw["startupinfo"] = si
            kw["creationflags"] = 0x08000000  # CREATE_NO_WINDOW
    except Exception:
        pass
    return kw


def _ahsrch_manual_server():
    """Optional manual override: %APPDATA%/OmniWatch/search_server.txt holding
    'ip' or 'ip:port'. Lets you point at a world's search server by hand if
    auto-detect can't find it. Returns (ip, port) or None."""
    try:
        path = os.path.join(os.environ.get("APPDATA", ""), "OmniWatch", "search_server.txt")
        with open(path, "r") as f:
            txt = f.read().strip()
        if not txt:
            return None
        if ":" in txt:
            ip, _, pp = txt.partition(":")
            return ip.strip(), int(pp.strip() or _AHSRCH_PORT)
        return txt, _AHSRCH_PORT
    except Exception:
        return None


def _ahsrch_cache_path():
    return os.path.join(os.environ.get("APPDATA", ""), "OmniWatch", "search_server_cache.txt")


def _ahsrch_load_cached():
    try:
        with open(_ahsrch_cache_path(), "r") as f:
            ip = f.read().strip()
        return ip or None
    except Exception:
        return None


def _ahsrch_save_cached(ip):
    try:
        path = _ahsrch_cache_path()
        os.makedirs(os.path.dirname(path), exist_ok=True)
        with open(path, "w") as f:
            f.write(ip)
    except Exception:
        pass


def _ahsrch_clear_cached():
    try:
        os.remove(_ahsrch_cache_path())
    except Exception:
        pass


def _ahsrch_find_server(port=_AHSRCH_PORT):
    """Auto-detect the current world's search server from this PC's TCP table.
    The FFXI client opens a connection to it on the search port when you /search
    (or browse the AH); we match any state, so a recent (TIME_WAIT) connection
    still counts. Returns IP or None."""
    import subprocess
    try:
        import psutil
        for c in psutil.net_connections(kind="tcp"):
            if (c.raddr and c.raddr.port == port
                    and c.raddr.ip not in ("0.0.0.0", "127.0.0.1")):
                return c.raddr.ip
    except Exception:
        pass
    out = ""
    for cmd in (["netstat", "-ano", "-p", "TCP"], ["netstat", "-an"]):
        try:
            out = subprocess.check_output(cmd, text=True, stderr=subprocess.DEVNULL,
                                          **_ahsrch_no_window_kw())
            break
        except Exception:
            continue
    pat = re.compile(r"(\d{1,3}(?:\.\d{1,3}){3}):%d\b" % port)
    for line in out.splitlines():
        if ("LISTEN" in line.upper()) or ((":%d" % port) not in line):
            continue
        m = pat.search(line)
        if m and m.group(1) not in ("0.0.0.0", "127.0.0.1"):
            return m.group(1)
    return None


def _ahsrch_fmtdate(ts):
    try:
        return datetime.datetime.utcfromtimestamp(ts).strftime("%Y-%m-%d")
    except Exception:
        return str(ts)


def _ahsrch_build_category_request(cat, key2=b"\x00\x00\x00\x00", key_tail=None):
    # 0x15 AH category listing request, byte-for-byte matching the real retail
    # client packet (verified against a live capture): 268 bytes, category at
    # 0x16, one sort param (by level) at 0x18.
    if key_tail is None:
        key_tail = os.urandom(4)
    length = 268
    buf = bytearray(length)
    _ahsrch_struct.pack_into("<H", buf, 0x00, length)
    _ahsrch_struct.pack_into("<I", buf, 0x04, _AHSRCH_IXFF)
    _ahsrch_struct.pack_into("<H", buf, 0x08, 184)
    buf[0x0A] = 0x80
    buf[0x0B] = 0x15
    _ahsrch_struct.pack_into("<H", buf, 0x0E, 1)
    buf[0x12] = 1                       # paramCount
    _ahsrch_struct.pack_into("<H", buf, 0x14, 4)
    buf[0x16] = cat & 0xFF              # AHCatID
    _ahsrch_struct.pack_into("<I", buf, 0x18, 2)
    _ahsrch_struct.pack_into("<I", buf, 0x1C, 2)
    buf[length - 0x18:length - 0x14] = key2
    buf[length - 0x14:length - 0x04] = _ahsrch_md5(bytes(buf[0x08:length - 0x14]))
    buf[length - 0x04:length] = key_tail
    P, S = _ahsrch_blowfish_init(_ahsrch_md5(_AHSRCH_KEY_SEED + key_tail))
    _ahsrch_cipher_blocks(buf, length, P, S, decrypt=False)
    return bytes(buf)


def _ahsrch_build_more_request(key2=b"\x00\x00\x00\x00", key_tail=None):
    # 0x10 "next page" request (the server tracks the query state per
    # connection, so this just advances the current category listing).
    if key_tail is None:
        key_tail = os.urandom(4)
    length = 76
    buf = bytearray(length)
    _ahsrch_struct.pack_into("<H", buf, 0x00, length)
    _ahsrch_struct.pack_into("<I", buf, 0x04, _AHSRCH_IXFF)
    _ahsrch_struct.pack_into("<H", buf, 0x08, 16)
    buf[0x0A] = 0x80
    buf[0x0B] = 0x10
    _ahsrch_struct.pack_into("<H", buf, 0x10, 3)
    _ahsrch_struct.pack_into("<H", buf, 0x12, 1)
    buf[length - 0x18:length - 0x14] = key2
    buf[length - 0x14:length - 0x04] = _ahsrch_md5(bytes(buf[0x08:length - 0x14]))
    buf[length - 0x04:length] = key_tail
    P, S = _ahsrch_blowfish_init(_ahsrch_md5(_AHSRCH_KEY_SEED + key_tail))
    _ahsrch_cipher_blocks(buf, length, P, S, decrypt=False)
    return bytes(buf)


def _ahsrch_recv_packet(s, timeout):
    data = b""
    try:
        while True:
            chunk = s.recv(4096)
            if not chunk:
                break
            data += chunk
            if len(data) >= 2 and len(data) >= _ahsrch_struct.unpack_from("<H", data, 0)[0]:
                break
    except socket.timeout:
        pass
    return data


def _ahsrch_parse_listing(data, key2):
    # Decrypt + parse one 0x95 AH listing page. Returns (items, total, is_last)
    # where items is {itemid: (single_count, stack_count)}; 0xFFFFFFFF means the
    # item has no listing of that form (e.g. doesn't stack). None on failure.
    if len(data) < 2:
        return None
    buf = bytearray(data)
    length = _ahsrch_struct.unpack_from("<H", buf, 0)[0]
    if length < 28 or length > len(buf):
        return None
    P, S = _ahsrch_blowfish_init(_ahsrch_md5(_AHSRCH_KEY_SEED + bytes(buf[length - 4:length]) + key2))
    _ahsrch_cipher_blocks(buf, length, P, S, decrypt=True)
    if buf[0x0B] != 0x95:
        return None
    total = _ahsrch_struct.unpack_from("<H", buf, 0x0E)[0]
    end = _ahsrch_struct.unpack_from("<H", buf, 0x08)[0]
    is_last = (buf[0x0A] == 0x80)
    items = {}
    n = max(0, (end - 0x18) // 10)
    for i in range(n):
        o = 0x18 + 10 * i
        if o + 10 > length:
            break
        iid = _ahsrch_struct.unpack_from("<H", buf, o)[0]
        single = _ahsrch_struct.unpack_from("<I", buf, o + 2)[0]
        stack = _ahsrch_struct.unpack_from("<I", buf, o + 6)[0]
        items[iid] = (single, stack)
    return items, total, is_last


def _ahsrch_query_category(host, port, cat, timeout=8.0):
    # Query one AH category: send 0x15, then page with 0x10 until the last-page
    # flag. Returns {"items": {itemid:(single,stack)}, "total": int}.
    key2 = b"\x00\x00\x00\x00"
    items = {}
    total = 0
    with socket.create_connection((host, port), timeout=timeout) as s:
        s.settimeout(timeout)
        s.sendall(_ahsrch_build_category_request(cat, key2))
        guard = 0
        is_last = False
        while not is_last and guard < 80:
            page = _ahsrch_parse_listing(_ahsrch_recv_packet(s, timeout), key2)
            if page is None:
                break
            pitems, ptotal, is_last = page
            items.update(pitems)
            total = ptotal
            if is_last or len(items) >= total:
                break
            s.sendall(_ahsrch_build_more_request(key2))
            guard += 1
    return {"items": items, "total": total}


# ─────────────── player search / server population ───────────────
# Besides the AH, the search server answers a player-search family (retail
# /search). For a population readout we don't need the (truncated) record list:
# every reply carries the TRUE match count as a u16 at 0x0E ("total found, may
# differ from the amount sent"), and the query behind it has no LIMIT — so one
# broad search returns the live server population.
#
# The request framing is identical to the AH requests above; the only deltas are
# the type byte (0x03 search / 0x00 search-all) and a bit-packed filter payload:
# a byte count at 0x10, then entries from 0x11. Each entry is a 5-bit tag, then
# (for most tags) a 1-bit sort flag + 1-bit "present" flag, then the value bits.
# Verified by round-tripping a built request back through the server's own
# decrypt + hash-check + bit-unpack logic.
_AHSRCH_MASK64 = 0xFFFFFFFFFFFFFFFF

_AHSRCH_TCP_SEARCH_ALL = 0x00
_AHSRCH_TCP_SEARCH     = 0x03

# 5-bit entry tags (search filter types)
_AHSRCH_SE_NAME   = 0x00
_AHSRCH_SE_AREA   = 0x01
_AHSRCH_SE_NATION = 0x02
_AHSRCH_SE_JOB    = 0x03
_AHSRCH_SE_LEVEL  = 0x04


def _ahsrch_packbits_be(target, value, byte_off, bit_off, nbits):
    byte_off += bit_off >> 3
    bit_off %= 8
    bitmask = (_AHSRCH_MASK64 >> (64 - nbits)) << bit_off
    value = ((value << bit_off) & _AHSRCH_MASK64) & bitmask
    bitmask ^= _AHSRCH_MASK64
    ab = (bit_off + nbits + 7) // 8
    data = int.from_bytes(bytes(target[byte_off:byte_off + ab]), "little")
    data = ((data & bitmask) | value) & ((1 << (ab * 8)) - 1)
    target[byte_off:byte_off + ab] = data.to_bytes(ab, "little")


def _ahsrch_packbits_le(target, value, bit_off, nbits):
    # Port of the search protocol's little-endian bit-packer. `bit_off` is an
    # absolute bit offset into target; returns the new absolute bit offset.
    byte_off = bit_off >> 3
    bit_off %= 8
    t = bit_off + nbits
    need = 1 if t <= 8 else 2 if t <= 16 else 4 if t <= 32 else 8
    ab = (bit_off + nbits + 7) // 8
    m = bytearray(need)
    for c in range(ab):
        m[need - 1 - c] = target[byte_off + c]
    _ahsrch_packbits_be(m, value, 0, (need << 3) - (bit_off + nbits), nbits)
    for c in range(ab):
        target[byte_off + c] = m[need - 1 - c]
    return (byte_off << 3) + bit_off + nbits


def _ahsrch_build_search_request(job=None, min_lvl=None, max_lvl=None,
                                 areas=None, nation=None, search_all=True,
                                 key2=b"\x00\x00\x00\x00", key_tail=None):
    # Build a player-search request. With no filters the reply's Total is the
    # whole-server online population; pass job=<id> for a per-job count, etc.
    if key_tail is None:
        key_tail = os.urandom(4)
    pl = bytearray(48)
    off = 0

    def _entry(tag, present, descending=0):
        nonlocal off
        off = _ahsrch_packbits_le(pl, tag, off, 5)
        off = _ahsrch_packbits_le(pl, descending, off, 1)
        off = _ahsrch_packbits_le(pl, present, off, 1)

    if job is not None:
        _entry(_AHSRCH_SE_JOB, 1)
        off = _ahsrch_packbits_le(pl, job & 0x1F, off, 5)
    if min_lvl is not None or max_lvl is not None:
        _entry(_AHSRCH_SE_LEVEL, 1)
        off = _ahsrch_packbits_le(pl, (min_lvl or 0) & 0xFF, off, 8)
        off = _ahsrch_packbits_le(pl, (max_lvl or 0) & 0xFF, off, 8)
    if nation is not None:
        _entry(_AHSRCH_SE_NATION, 1)
        off = _ahsrch_packbits_le(pl, nation & 0x3, off, 2)
    if areas:
        for a in areas:
            _entry(_AHSRCH_SE_AREA, 1)
            off = _ahsrch_packbits_le(pl, a & 0x3FF, off, 10)
        _entry(_AHSRCH_SE_AREA, 0)  # area-list terminator

    nbytes = (off + 7) // 8
    length = 76
    if 0x11 + nbytes > length - 0x18:
        raise ValueError("search filter payload too large (%d bytes)" % nbytes)
    buf = bytearray(length)
    _ahsrch_struct.pack_into("<H", buf, 0x00, length)
    _ahsrch_struct.pack_into("<I", buf, 0x04, _AHSRCH_IXFF)
    _ahsrch_struct.pack_into("<H", buf, 0x08, 16)
    buf[0x0A] = 0x80
    buf[0x0B] = _AHSRCH_TCP_SEARCH_ALL if search_all else _AHSRCH_TCP_SEARCH
    buf[0x10] = nbytes
    buf[0x11:0x11 + nbytes] = pl[:nbytes]
    buf[length - 0x18:length - 0x14] = key2
    buf[length - 0x14:length - 0x04] = _ahsrch_md5(bytes(buf[0x08:length - 0x14]))
    buf[length - 0x04:length] = key_tail
    P, S = _ahsrch_blowfish_init(_ahsrch_md5(_AHSRCH_KEY_SEED + key_tail))
    _ahsrch_cipher_blocks(buf, length, P, S, decrypt=False)
    return bytes(buf)


def _ahsrch_parse_search_count(data, key2=b"\x00\x00\x00\x00"):
    # Decrypt one player-search reply and return the u16 "total found" at 0x0E
    # (the reply's type byte at 0x0B is 0x80). None on failure.
    if len(data) < 28:
        return None
    buf = bytearray(data)
    length = _ahsrch_struct.unpack_from("<H", buf, 0)[0]
    if length < 28 or length > len(buf):
        return None
    P, S = _ahsrch_blowfish_init(_ahsrch_md5(
        _AHSRCH_KEY_SEED + bytes(buf[length - 4:length]) + key2))
    _ahsrch_cipher_blocks(buf, length, P, S, decrypt=True)
    if buf[0x0B] != 0x80:
        return None
    return _ahsrch_struct.unpack_from("<H", buf, 0x0E)[0]


def _ahsrch_query_population(host, port=_AHSRCH_PORT, timeout=8.0, **filters):
    # Fire one broad player search and read Total from the first reply packet
    # (every packet carries it; no need to page the record list). No filters =
    # whole-server online population.
    req = _ahsrch_build_search_request(**filters)
    with socket.create_connection((host, port), timeout=timeout) as s:
        s.settimeout(timeout)
        s.sendall(req)
        data = _ahsrch_recv_packet(s, timeout)
    return _ahsrch_parse_search_count(data)


def _ahsrch_median_price(host, item_id, stack=0, port=_AHSRCH_PORT,
                         timeout=6.0):
    # Median of one item's recent AH sale prices on one world (or None). This
    # is the same history query the detail pane uses, just reduced to a median
    # so it can be fanned out across all worlds for a price comparison.
    try:
        raw = _ahsrch_query_history(host, port, item_id, stack, timeout=timeout)
        res = _ahsrch_parse_history(raw)
    except Exception:
        return None
    if not res.get("ok"):
        return None
    prices = [s.get("price", 0) for s in res.get("sales", []) if s.get("price")]
    if not prices:
        return None
    return int(statistics.median(prices))


# --- panel glue: session-cached IP, threaded fetch, main-thread drain ---
_ah_search_ip = None
_ah_hist_inbox = _collections.deque()
_ah_hist_busy = False


def _ah_hist_emit(line):
    """Show an AH-history line in the panel results pane AND mirror it (full,
    untruncated) to the session log. `line` is a plain str, or a list of
    (text, color) segments for coloured rendering."""
    _ah_hist_inbox.append(line)
    try:
        flat = line if isinstance(line, str) else "".join(t for t, _c in line)
        print("[AH-history] " + flat)
    except Exception:
        pass


def _ah_item_name(item_id):
    try:
        for it in ah_state.get("items", []):
            if it.get("id") == item_id:
                return it.get("name") or ("item %d" % item_id)
    except Exception:
        pass
    return "item %d" % item_id


def _ahsrch_build_history_request(item_id, stack, key2=b"\x00\x00\x00\x00", key_tail=None):
    # Exact real-client AH-history request (verified byte-for-byte against a
    # live capture): itemid as u16 @0x12, constant 0x04 @0x14, stack flag @0x15,
    # opcode 0x05 single / 0x06 stack. No 0x0E / param framing (the listing
    # request uses those; history does not).
    if key_tail is None:
        key_tail = os.urandom(4)
    length = 268
    buf = bytearray(length)
    _ahsrch_struct.pack_into("<H", buf, 0x00, length)
    _ahsrch_struct.pack_into("<I", buf, 0x04, _AHSRCH_IXFF)
    _ahsrch_struct.pack_into("<H", buf, 0x08, 184)
    buf[0x0A] = 0x80
    buf[0x0B] = 0x06 if stack else 0x05
    _ahsrch_struct.pack_into("<H", buf, 0x12, item_id & 0xFFFF)
    buf[0x14] = 0x04
    buf[0x15] = 0x01 if stack else 0x00
    buf[length - 0x18:length - 0x14] = key2
    buf[length - 0x14:length - 0x04] = _ahsrch_md5(bytes(buf[0x08:length - 0x14]))
    buf[length - 0x04:length] = key_tail
    P, S = _ahsrch_blowfish_init(_ahsrch_md5(_AHSRCH_KEY_SEED + key_tail))
    _ahsrch_cipher_blocks(buf, length, P, S, decrypt=False)
    return bytes(buf)


def _ahsrch_query_history(host, port, item_id, stack, timeout=8.0):
    with socket.create_connection((host, port), timeout=timeout) as s:
        s.settimeout(timeout)
        s.sendall(_ahsrch_build_history_request(item_id, stack))
        return _ahsrch_recv_packet(s, timeout)


def _ahsrch_parse_history(data, key2=b"\x00\x00\x00\x00"):
    # Decrypt + parse a history reply (0x85 single / 0x86 stack). Item header at
    # 0x18 (itemid u16, total-sold u32 @0x1A, category u16 @0x1E); up to 10 sale
    # records from 0x20, 40 bytes each: price u32, date u32 (unix), seller 16B,
    # buyer 16B.
    if len(data) < 28:
        return {"ok": False, "raw": data}
    buf = bytearray(data)
    length = _ahsrch_struct.unpack_from("<H", buf, 0)[0]
    if length < 28 or length > len(buf):
        return {"ok": False, "raw": data}
    P, S = _ahsrch_blowfish_init(_ahsrch_md5(
        _AHSRCH_KEY_SEED + bytes(buf[length - 4:length]) + key2))
    _ahsrch_cipher_blocks(buf, length, P, S, decrypt=True)
    if _ahsrch_md5(bytes(buf[8:length - 0x14])) != bytes(buf[length - 0x14:length - 0x04]):
        return {"ok": False, "raw": data, "badhash": True}
    if (buf[0x0B] & 0x1F) not in (0x05, 0x06):
        return {"ok": False, "raw": data, "type": buf[0x0B]}
    item = _ahsrch_struct.unpack_from("<H", buf, 0x18)[0]
    count = _ahsrch_struct.unpack_from("<I", buf, 0x1A)[0]
    cat = _ahsrch_struct.unpack_from("<H", buf, 0x1E)[0]
    marker = _ahsrch_struct.unpack_from("<H", buf, 0x08)[0]
    nrec = max(0, (marker - 0x20) // 40)
    sales = []
    for i in range(nrec):
        o = 0x20 + 40 * i
        if o + 40 > length - 0x14:
            break
        sales.append({
            "price": _ahsrch_struct.unpack_from("<I", buf, o + 0x00)[0],
            "date": _ahsrch_struct.unpack_from("<I", buf, o + 0x04)[0],
            "seller": _ahsrch_decode_name(bytes(buf[o + 0x08:o + 0x18])),
            "buyer": _ahsrch_decode_name(bytes(buf[o + 0x18:o + 0x28])),
        })
    return {"ok": True, "item": item, "count": count, "cat": cat,
            "marker": marker, "sales": sales}



# ─────────────────────────── item database ───────────────────────────
def _load_items():
    cands = []
    # PyInstaller --onefile: bundled data lands in sys._MEIPASS
    mei = getattr(sys, "_MEIPASS", None)
    if mei:
        cands.append(os.path.join(mei, "ffxi_items.json"))
    here = os.path.dirname(os.path.abspath(
        sys.argv[0] if getattr(sys, "frozen", False) else __file__))
    cands.append(os.path.join(here, "ffxi_items.json"))
    cands.append("ffxi_items.json")
    for c in cands:
        if os.path.isfile(c):
            with open(c, encoding="utf-8") as f:
                return json.load(f)
    return {}


ITEMS = _load_items()   # {"id": {"n": name, "c": cat, "s": stack, "d": desc}}
_NAME_INDEX = sorted(((v.get("n", ""), int(k)) for k, v in ITEMS.items()),
                     key=lambda t: t[0].lower())


def search_items(q, limit=300):
    q = q.strip().lower()
    if not q:
        return []
    hits = [(n, i) for (n, i) in _NAME_INDEX if q in n.lower()]
    # prefix matches first, then alphabetical within each group
    hits.sort(key=lambda t: (0 if t[0].lower().startswith(q) else 1,
                             t[0].lower()))
    return hits[:limit]


def _parse_dmg(desc):
    m = re.search(r"DMG:\s*(\d+)", desc or "")
    return int(m.group(1)) if m else None


def _build_disambig():
    # For items that SHARE a display name (REMA upgrade stages, etc.) attach a
    # short suffix so the results list can tell them apart: item level (or level),
    # with weapon DMG as the tiebreaker when stages share a level. Items with no
    # level/DMG that happen to collide are left as-is (not weapons we care about).
    from collections import defaultdict, Counter
    groups = defaultdict(list)
    for k, v in ITEMS.items():
        groups[(v.get("n", "")).lower()].append(int(k))
    out = {}
    for _name, ids in groups.items():
        if len(ids) < 2:
            continue

        def lvtag(iid):
            it = ITEMS[str(iid)]
            if it.get("il"):
                return "iLv %d" % it["il"]
            if it.get("lv"):
                return "Lv %d" % it["lv"]
            return ""

        base = {iid: lvtag(iid) for iid in ids}
        counts = Counter(base.values())
        for iid in ids:
            tag = base[iid]
            if tag == "" or counts[tag] > 1:
                dmg = _parse_dmg(ITEMS[str(iid)].get("d", ""))
                if dmg is not None:
                    tag = ("%s  DMG %d" % (tag, dmg)).strip()
            if tag:
                out[iid] = tag
    return out


_DISAMBIG = _build_disambig()


def _list_label(name, iid):
    suf = _DISAMBIG.get(iid)
    return ("%s   —   %s" % (name, suf)) if suf else name


_JOB_ABBR = {1: "WAR", 2: "MNK", 3: "WHM", 4: "BLM", 5: "RDM", 6: "THF",
             7: "PLD", 8: "DRK", 9: "BST", 10: "BRD", 11: "RNG", 12: "SAM",
             13: "NIN", 14: "DRG", 15: "SMN", 16: "BLU", 17: "COR", 18: "PUP",
             19: "DNC", 20: "SCH", 21: "GEO", 22: "RUN"}
_NJOBS = 22
_SLOT_NAME = {0: "Main", 1: "Sub", 2: "Range", 3: "Ammo", 4: "Head", 5: "Body",
              6: "Hands", 7: "Legs", 8: "Feet", 9: "Neck", 10: "Waist",
              11: "L.Ear", 12: "R.Ear", 13: "L.Ring", 14: "R.Ring", 15: "Back"}


def _jobs_str(mask):
    if not mask:
        return ""
    on = [_JOB_ABBR[j] for j in range(1, _NJOBS + 1) if mask & (1 << j)]
    if len(on) == _NJOBS:
        return "All jobs"
    return " ".join(on)


def _slot_str(mask):
    if not mask:
        return ""
    txt = "/".join(_SLOT_NAME[s] for s in range(16) if mask & (1 << s))
    return txt.replace("L.Ear/R.Ear", "Ears").replace("L.Ring/R.Ring", "Rings")


def _fmt_ts(ts):
    # local date + time of the sale (the timestamp is a unix epoch)
    try:
        dt = datetime.datetime.fromtimestamp(ts)
        return dt.strftime("%Y-%m-%d") + "     " + dt.strftime("%H:%M")
    except Exception:
        return str(ts)


# ─────────────────────────── servers ───────────────────────────
# The 16 live FFXI worlds. Each has its own search server; the address is
# user-supplied per world and remembered in %APPDATA%/FFXI_AH_Browser.
_WORLDS = ["Asura", "Bahamut", "Bismarck", "Carbuncle", "Cerberus", "Fenrir",
           "Lakshmi", "Leviathan", "Odin", "Phoenix", "Quetzalcoatl",
           "Ragnarok", "Shiva", "Siren", "Sylph", "Valefor"]
_DEFAULT_SERVERS = {
    "Asura": "124.150.154.76",
    "Bahamut": "124.150.154.61",
    "Bismarck": "124.150.154.74",
    "Carbuncle": "124.150.154.64",
    "Cerberus": "124.150.154.73",
    "Fenrir": "124.150.154.65",
    "Lakshmi": "124.150.154.75",
    "Leviathan": "124.150.154.68",
    "Phoenix": "124.150.154.63",
    "Quetzalcoatl": "124.150.154.70",
    "Ragnarok": "124.150.154.72",
    "Shiva": "124.150.154.62",
    "Siren": "124.150.154.71",
    "Sylph": "124.150.154.66",
    "Odin": "124.150.154.69",
    "Valefor": "124.150.154.67",
    # All 16 live worlds occupy 124.150.154.61-.76. If SE ever renumbers one,
    # Detect on that world re-reads it and Save overrides the default locally.
}


def _appdata_dir():
    return os.path.join(os.environ.get("APPDATA") or os.path.expanduser("~"),
                        "AuctionWatch")


def _servers_path():
    return os.path.join(_appdata_dir(), "servers.json")


def _load_servers():
    d = dict(_DEFAULT_SERVERS)
    try:
        with open(_servers_path(), encoding="utf-8") as f:
            saved = json.load(f)
        if isinstance(saved, dict):
            d.update({k: v for k, v in saved.items() if isinstance(v, str)})
    except Exception:
        pass
    return d


def _ui_path():
    return os.path.join(_appdata_dir(), "ui.json")


def _load_ui():
    try:
        with open(_ui_path(), encoding="utf-8") as f:
            d = json.load(f)
        return d if isinstance(d, dict) else {}
    except Exception:
        return {}


def _save_ui(d):
    try:
        p = _ui_path()
        os.makedirs(os.path.dirname(p), exist_ok=True)
        with open(p, "w", encoding="utf-8") as f:
            json.dump(d, f, indent=2)
    except Exception:
        pass


def _save_servers(d):
    try:
        p = _servers_path()
        os.makedirs(os.path.dirname(p), exist_ok=True)
        with open(p, "w", encoding="utf-8") as f:
            json.dump(d, f, indent=2, ensure_ascii=False)
    except Exception:
        pass


# ─────────────────────────── item icons ───────────────────────────
#
# WHERE ICONS COME FROM, AND WHY THERE IS NOTHING TO SET UP
#
# The 32x32 icon for an item lives in the client's own item DATs, on the same PC
# this app runs on, so there is nothing to download and nowhere to point it. The
# first icon asked for makes the app work out where the item records sit (see
# _solve_range); after that every icon is a seek into a memory-mapped file. Each
# one decoded is written out as <id>.png under %APPDATA%/AuctionWatch/itemicons,
# so the second run is pure file reads and the game need not even be installed.
#
# A folder of pngs named <id>.png is read in preference to any of that. It can sit
# next to the app or under %APPDATA%/AuctionWatch, and be called itemicons, items,
# icons/items or just icons -- all of them are looked in, along with OmniWatch's
# extracted set and a sibling MobileWatch checkout's assets. Nothing has to be told
# where it is; the app finds out which of them exists on its own.
#
# If none of it is there -- no game, no folder -- nothing is drawn and no space is
# reserved, so the lists and the card look exactly as they did before icons.

_ICON_W = _ICON_H = 32
_ICON_BYTES = 0x800                 # 0x400 palette + 0x400 indices
_STD_STRIDE = 0x1400                # item record size (was 0xC00 before a 2026 patch)
_STD_ICON_OFFSET = 0x2BD            # where the icon sits inside a record

# The DAT is bit-rotated: low 5 bits move up, high 3 bits move down.
_ROT = [(i % 0x20) * 8 + i // 0x20 for i in range(256)]
_UNROT = [0] * 256
for _e, _n in enumerate(_ROT):
    _UNROT[_n] = _e

# id -> DAT, from Rubenator's icon_extractor.lua. The right starting guess; where an
# install disagrees, the name anchors below correct it.
_ITEM_DAT_MAP = [
    (0x0001, 0x0FFF, "118/106", -1, "General Items"),
    (0x1000, 0x1FFF, "118/107", 0, "Usable Items"),
    (0x2000, 0x21FF, "118/110", 0, "Automaton Items"),
    (0x2200, 0x27FF, "301/115", 0, "General Items 2"),
    (0x2800, 0x3FFF, "118/109", 0, "Armor Items"),
    (0x4000, 0x59FF, "118/108", 0, "Weapon Items"),
    (0x5A00, 0x6FFF, "286/73", 0, "Armor Items 2"),
    (0x7000, 0x73FF, "217/21", 0, "Maze Items, Basic Items"),
    (0x7400, 0x77FF, "288/80", 0, "Instinct Items"),
    (0xF000, 0xF1FF, "288/67", 0, "Monipulator Items"),
    (0xFFFF, 0xFFFF, "174/48", 0, "Gil"),
]

# Known id -> name, spread across each range, used to locate the records outright.
# Instinct and Monipulator items are absent from Windower's resources, so those two
# ranges can only ever run on the standard layout.
_ICON_ANCHORS = {
    "General Items": [(1, "Chocobo Bedding"), (633, "Olive Oil"), (1148, "Shoalweed"), (1631, "Moblin Armor"), (2092, "Sao. Sune-Ate -1"), (2617, "Chamrosh's Beak"), (3078, "Cracked Drgscale."), (3537, "Kupon A-Rub")],
    "Usable Items": [(4096, "Fire Crystal"), (4403, "Yellow Globe"), (4850, "Refresh II"), (5209, "Diatryma Meat"), (5509, "E. Tincture (BS)"), (5833, "Mana Mist"), (6141, "O. Bolt Quiver"), (6406, "Pork Cutlet Bowl")],
    "General Items 2": [(8704, "Bismuth Ingot"), (8871, "Leath. Kit 55"), (9052, "Golden Coil"), (9260, "A. Token: Head"), (9423, "Smith. Set 65"), (9584, "Voidhead: DNC"), (9745, "Voidfoot: BLM"), (9962, "Tem. N-F7")],
    "Armor Items": [(10240, "Hexed Haubert"), (11017, "Soil Pearl"), (11770, "Accursed Belt"), (12540, "Alluring Headband"), (13338, "Blood Earring"), (14087, "Gilt Sabatons"), (14842, "Ivory Mitts"), (15602, "Pup. Churidars")],
    "Weapon Items": [(16386, "Lizard Cesti"), (16995, "Rotten Meat"), (17558, "Apollo's Staff"), (18116, "Engetsuto +1"), (18765, "Oberon's Sainti"), (19511, "Naboot +1"), (20918, "Dimmet Scythe"), (21576, "Bard's Knife")],
    "Armor Items 2": [(23040, "Pummeler's Mask +2"), (23570, "Chasseur's Gants +3"), (24122, "Revelation Masque"), (25739, "Aldo Unity Shirt"), (26440, "Plaiter's Scutum"), (27053, "Boii Mufflers +1"), (27578, "Fenrir Ring"), (28127, "Laksa. Trews +1")],
    "Maze Items, Basic Items": [(28672, "Maze Tabula M01"), (28803, "Maze Rune 004"), (28821, "Maze Rune 022"), (28839, "Maze Rune 040"), (28875, "Maze Rune 076"), (28893, "Maze Rune 094"), (28912, "Maze Rune 113"), (29323, "Storage Slip 12")],
    "Gil": [(65535, "Gil")],
}

# A candidate layout must clear both of these across its sample records.
_BLANK_OPAQUE = 0.02       # below this the record has no artwork; not a failure
_CLEAN_MID = 0.01          # a real icon has essentially no partial-alpha pixels
_MIN_CLEAN_RATE = 0.55     # genuine ranges score 0.70-1.00; misreads score 0.00-0.17
_MIN_SAMPLES = 5


def _icon_decode(block):
    """0x800 bytes -> list of 32 RGBA rows, top-down, or None if the record is blank."""
    if len(block) < _ICON_BYTES or not any(block[:_ICON_BYTES]):
        return None
    pal = bytearray(0x400)
    raw = block[:0x400]
    for j in range(0x400):
        n = _ROT[raw[j]]
        if j & 3 == 3:                      # alpha is stored 0-127 and doubled
            n = n * 2
            if n > 0xFF:
                n = 0xFF
        pal[j] = n
    idx = block[0x400:0x800]
    rows = []
    for y in range(_ICON_H):
        row = bytearray(_ICON_W * 4)
        base = y * _ICON_W
        for x in range(_ICON_W):
            p = _ROT[idx[base + x]] * 4
            o = x * 4
            row[o] = pal[p + 2]             # stored B,G,R,A
            row[o + 1] = pal[p + 1]
            row[o + 2] = pal[p]
            row[o + 3] = pal[p + 3]
        rows.append(bytes(row))
    rows.reverse()                          # stored bottom-up like a BMP
    return rows


def _icon_alpha_profile(block):
    """(mid_fraction, opaque_fraction), decoding ONLY alpha.

    REAL FFXI ICONS USE BINARY ALPHA -- a pixel is fully transparent or fully solid.
    That is the test that tells a genuine record layout from a misread of packed game
    data; scoring on what the result "looks like" cannot, and once produced 14,000
    files of noise that scored inside the genuine band."""
    if len(block) < _ICON_BYTES or not any(block[:_ICON_BYTES]):
        return None
    alpha = [0] * 256
    raw = block[:0x400]
    for i in range(256):
        n = _ROT[raw[i * 4 + 3]] * 2
        alpha[i] = 0xFF if n > 0xFF else n
    mid = op = 0
    for b in block[0x400:0x800]:
        a = alpha[_ROT[b]]
        if 16 < a < 240:
            mid += 1
        elif a >= 240:
            op += 1
    return mid / 1024.0, op / 1024.0


def _icon_validate(data, a0, stride, ids):
    """Check a layout: the icon for id sits at a0 + id * stride.

    Returns (clean_rate, n_nonblank). A one-item range (Gil) can never reach the
    normal sample count, so the requirement scales to the range."""
    clean = nonblank = 0
    for i in ids:
        p = a0 + i * stride
        if p < 0 or p + _ICON_BYTES > len(data):
            continue
        prof = _icon_alpha_profile(data[p:p + _ICON_BYTES])
        if prof is None or prof[1] < _BLANK_OPAQUE:
            continue
        nonblank += 1
        if prof[0] <= _CLEAN_MID:
            clean += 1
    if nonblank < min(_MIN_SAMPLES, max(1, len(ids))):
        return 0.0, nonblank
    return clean / nonblank, nonblank


def _icon_encode_png(rows):
    def chunk(tag, payload):
        c = struct.pack(">I", len(payload)) + tag + payload
        return c + struct.pack(">I", zlib.crc32(tag + payload) & 0xFFFFFFFF)

    raw = b"".join(b"\x00" + r for r in rows)
    return (b"\x89PNG\r\n\x1a\n"
            + chunk(b"IHDR", struct.pack(">IIBBBBB", _ICON_W, _ICON_H, 8, 6, 0, 0, 0))
            + chunk(b"IDAT", zlib.compress(raw, 9))
            + chunk(b"IEND", b""))


def _icon_sample_ids(lo, hi, n=24):
    step = max(1, (hi - lo + 1) // n)
    return list(range(lo, hi + 1, step))[:n]


def _icon_find_anchors(data, anchors):
    """id -> byte position of that item's name in the file. Unambiguous hits only."""
    found = {}
    for item_id, name in anchors:
        if len(name) < 4:
            continue
        raw = name.encode("ascii", "ignore")
        for pat in (raw, bytes(_UNROT[b] for b in raw)):
            first = data.find(pat)
            if first < 0 or data.find(pat, first + 1) >= 0:
                continue
            found[item_id] = first
            break
    return found


def _icon_alignment(found):
    """(stride, base) with name_pos(id) == base + id * stride, or None.

    Two anchors imply a stride; it is taken only if every anchor lands exactly where
    that stride predicts, which makes it ground truth rather than a guess."""
    ids = sorted(found)
    if len(ids) < 3:
        return None
    best = None
    for a in range(len(ids)):
        for b in range(a + 1, len(ids)):
            di = ids[b] - ids[a]
            dp = found[ids[b]] - found[ids[a]]
            if di <= 0 or dp <= 0 or dp % di:
                continue
            stride = dp // di
            if not (0x400 <= stride <= 0x4000):
                continue
            base = found[ids[a]] - ids[a] * stride
            agree = sum(1 for i in ids if found[i] == base + i * stride)
            if agree >= max(3, len(ids) - 1) and (best is None or agree > best[2]):
                best = (stride, base, agree)
    return (best[0], best[1]) if best else None


def _icon_find_ffxi():
    for c in (r"C:\Program Files (x86)\SquareEnix\SquareEnix\FINAL FANTASY XI",
              r"C:\Program Files (x86)\PlayOnline\SquareEnix\FINAL FANTASY XI",
              r"C:\Program Files\PlayOnline\SquareEnix\FINAL FANTASY XI",
              r"C:\PlayOnline\SquareEnix\FINAL FANTASY XI",
              r"D:\PlayOnline\SquareEnix\FINAL FANTASY XI",
              r"D:\SquareEnix\FINAL FANTASY XI"):
        if os.path.isdir(os.path.join(c, "ROM")):
            return c
    return None


# What a folder of dumped icons tends to get called. All of them are looked in, so
# the set can be dropped wherever it lands without telling the app about it.
_ICON_SUBDIRS = (("itemicons",), ("items",), ("icons", "items"),
                 ("icons", "itemicons"), ("icons",))


def _icon_dirs():
    """Folders of <id>.png, best first. The cache the app writes comes before the
    read-only sets so a freshly decoded icon is found without a directory walk."""
    dirs = []
    bases = []
    mei = getattr(sys, "_MEIPASS", None)
    if mei:
        bases.append(mei)
    here = os.path.dirname(os.path.abspath(
        sys.argv[0] if getattr(sys, "frozen", False) else __file__))
    bases.append(here)
    dirs.append(_icon_cache_dir())
    bases.append(_appdata_dir())
    for base in bases:
        for parts in _ICON_SUBDIRS:
            dirs.append(os.path.join(base, *parts))
    appdata = os.environ.get("APPDATA") or os.path.expanduser("~")
    dirs.append(os.path.join(appdata, "OmniWatch", "icons", "equipment"))
    dirs.append(os.path.join(appdata, "OmniWatch", "icons", "items"))
    # A MobileWatch checkout sitting beside this one already has the whole set.
    for up in (here, os.path.dirname(here), os.path.dirname(os.path.dirname(here))):
        try:
            names = os.listdir(up)
        except OSError:
            continue
        for n in names:
            if "mobilewatch" in n.lower():
                dirs.append(os.path.join(up, n, "app", "src", "main",
                                         "assets", "itemicons"))
    seen, out = set(), []
    for d in dirs:
        k = os.path.normcase(os.path.abspath(d))
        if k not in seen:
            seen.add(k)
            out.append(d)
    return out


def _icon_cache_dir():
    return os.path.join(_appdata_dir(), "itemicons")


class _IconStore:
    """Finds an item's png: a folder first, then the client's DATs.

    Everything here is called from a worker thread. Tk objects are never touched --
    the caller turns the bytes into a PhotoImage on the main thread."""

    def __init__(self):
        self._lock = threading.Lock()
        self._dirs = None
        self._ffxi = None
        self._ranges = {}        # label -> (mmap, a0, stride) or None once refused
        self._open = []          # the DAT handles the mappings are built on
        self._layout = {}        # label -> dict, remembered across runs
        self._layout_loaded = False
        self._missing = set()
        self.found_any = False   # flips true on the first icon that resolves

    # -- folders ----------------------------------------------------------
    def _folder_png(self, iid):
        if self._dirs is None:
            self._dirs = _icon_dirs()
        name = "%d.png" % iid
        for d in self._dirs:
            p = os.path.join(d, name)
            try:
                if os.path.isfile(p):
                    with open(p, "rb") as f:
                        return f.read()
            except OSError:
                pass
        return None

    # -- DATs -------------------------------------------------------------
    def _layout_path(self):
        return os.path.join(_appdata_dir(), "iconlayout.json")

    def _load_layout(self):
        if self._layout_loaded:
            return
        self._layout_loaded = True
        try:
            with open(self._layout_path(), encoding="utf-8") as f:
                d = json.load(f)
            if isinstance(d, dict):
                self._layout = d
        except Exception:
            pass

    def _save_layout(self):
        try:
            p = self._layout_path()
            os.makedirs(os.path.dirname(p), exist_ok=True)
            with open(p, "w", encoding="utf-8") as f:
                json.dump(self._layout, f, indent=2)
        except Exception:
            pass

    def _entry_for(self, iid):
        for lo, hi, rel, off, label in _ITEM_DAT_MAP:
            if lo <= iid <= hi:
                return lo, hi, rel, off, label
        return None

    def _open_range(self, entry):
        """(mmap, a0, stride) for an id range, solving the layout the first time.

        The standard layout is tried FIRST and kept when it validates, so ranges that
        already decode are never disturbed by a cleverer theory. Name anchors are only
        brought in when it fails, which is the case the 2021 table gets wrong."""
        lo, hi, rel, off, label = entry
        if label in self._ranges:
            return self._ranges[label]
        self._ranges[label] = None          # refuse by default; replaced on success
        if self._ffxi is None:
            self._ffxi = _icon_find_ffxi() or False
        if not self._ffxi:
            return None
        path = os.path.join(self._ffxi, "ROM", *rel.split("/")) + ".DAT"
        try:
            st = os.stat(path)
        except OSError:
            return None
        try:
            f = open(path, "rb")
            mm = mmap.mmap(f.fileno(), 0, access=mmap.ACCESS_READ)
        except (OSError, ValueError):
            return None
        self._open.append(f)

        self._load_layout()
        cached = self._layout.get(label)
        if (isinstance(cached, dict) and cached.get("size") == st.st_size
                and int(cached.get("mtime", -1)) == int(st.st_mtime)):
            got = (mm, int(cached["a0"]), int(cached["stride"]))
            self._ranges[label] = got
            return got

        ids = _icon_sample_ids(lo, hi)
        a0 = -(lo + off) * _STD_STRIDE + _STD_ICON_OFFSET
        stride = _STD_STRIDE
        rate, _n = _icon_validate(mm, a0, stride, ids)
        if rate < _MIN_CLEAN_RATE:
            a0 = None
            found = _icon_find_anchors(mm, _ICON_ANCHORS.get(label, []))
            align = _icon_alignment(found) if len(found) >= 3 else None
            if align:
                stride, base = align
                rec0 = base - (base % stride)       # start of the record for id 0
                cand = rec0 + _STD_ICON_OFFSET
                rate, _n = _icon_validate(mm, cand, stride, ids)
                if rate >= _MIN_CLEAN_RATE:
                    a0 = cand
                else:
                    # Scan the record for it -- and keep the BEST offset, not the
                    # first one over the line. A block that straddles the real icon
                    # can pass the bar while reading half a record early.
                    best = (None, 0.0, 0)
                    for k in range(0, stride - _ICON_BYTES + 1):
                        r, nb = _icon_validate(mm, rec0 + k, stride, ids)
                        if r > best[1] or (r == best[1] and nb > best[2]):
                            best = (rec0 + k, r, nb)
                        if r >= 0.95 and nb >= 10:
                            break
                    if best[1] >= _MIN_CLEAN_RATE:
                        a0 = best[0]
        if a0 is None:
            mm.close()
            f.close()
            return None                      # refused: better nothing than noise
        self._layout[label] = {"a0": a0, "stride": stride,
                               "size": st.st_size, "mtime": int(st.st_mtime)}
        self._save_layout()
        got = (mm, a0, stride)
        self._ranges[label] = got
        return got

    def _dat_png(self, iid):
        entry = self._entry_for(iid)
        if entry is None:
            return None
        got = self._open_range(entry)
        if not got:
            return None
        mm, a0, stride = got
        p = a0 + iid * stride
        if p < 0 or p + _ICON_BYTES > len(mm):
            return None
        rows = _icon_decode(mm[p:p + _ICON_BYTES])
        if rows is None:
            return None
        png = _icon_encode_png(rows)
        try:
            d = _icon_cache_dir()
            os.makedirs(d, exist_ok=True)
            tmp = os.path.join(d, "%d.png.tmp" % iid)
            with open(tmp, "wb") as f:
                f.write(png)
            os.replace(tmp, os.path.join(d, "%d.png" % iid))
        except OSError:
            pass
        return png

    # -- public -----------------------------------------------------------
    def png(self, iid):
        if iid <= 0:
            return None
        with self._lock:
            if iid in self._missing:
                return None
            data = self._folder_png(iid)
            if data is None:
                data = self._dat_png(iid)
            if data is None:
                self._missing.add(iid)
            else:
                self.found_any = True
            return data


_ICONS = _IconStore()


class IconLoader:
    """Turns item ids into Tk images, off the main thread.

    One worker, newest request first: the row you just scrolled to matters more than
    one from two screens ago. Decoded images are kept for the life of the process --
    a PhotoImage is a few KB, and Tk drops an image the moment nothing references it."""

    def __init__(self, widget, on_ready):
        self._w = widget
        self._on_ready = on_ready
        self._images = {}            # iid -> PhotoImage (also the reference that keeps it alive)
        self._pending = set()
        self._queue = _collections.deque()
        self._wake = threading.Event()
        self._thread = None

    def peek(self, iid):
        return self._images.get(iid)

    def request(self, iid):
        if iid in self._images or iid in self._pending:
            return
        self._pending.add(iid)
        self._queue.append(iid)
        if self._thread is None:
            self._thread = threading.Thread(target=self._run, daemon=True)
            self._thread.start()
        self._wake.set()

    def _run(self):
        while True:
            try:
                iid = self._queue.pop()          # newest first
            except IndexError:
                self._wake.clear()
                self._wake.wait(0.5)
                continue
            png = _ICONS.png(iid)
            try:
                self._w.after(0, self._deliver, iid, png)
            except tk.TclError:
                return                       # window closed; nothing to deliver to

    def _deliver(self, iid, png):
        self._pending.discard(iid)
        if png:
            try:
                self._images[iid] = tk.PhotoImage(
                    data=base64.b64encode(png).decode("ascii"))
            except tk.TclError:
                return
            self._on_ready(iid)


# ── element icons ──
# Descriptions carry the eight elements as private-use characters E000-E007. No
# desktop font has a glyph for those, so a plain label renders a stray CJK character
# where the element belongs -- Sirocco Kukri reads as two symbols rather than Ice-7
# Wind+7. The game's own icons are embedded here and drawn inline at text height.
_ELEM_ORDER = ["Fire", "Ice", "Wind", "Earth", "Lightning", "Water", "Light", "Dark"]
_ELEM_COLOR = {"Fire": "#e58a6a", "Ice": "#9bd3e0", "Wind": "#9ad39a",
               "Earth": "#c9b37a", "Lightning": "#d98ad9", "Water": "#7fb0dc",
               "Light": "#ededed", "Dark": "#b89ae0"}
_ELEM_PNG = {
    "fire": (
        "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"
    ),
    "ice": (
        "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"
        "AABJRU5ErkJggg=="
    ),
    "wind": (
        "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"
    ),
    "earth": (
        "iVBORw0KGgoAAAANSUhEUgAAACAAAAAgCAYAAABzenr0AAAAAXNSR0IArs4c6QAAAARnQU1BAACx"
        "jwv8YQUAAAAJcEhZcwAADsMAAA7DAcdvqGQAAAR0SURBVFhHtZctlKtKEIQjI5FIJDIyEolEIpFI"
        "JBIZGRkZGRkZGRm5MnLllU+um1vf9HT+3u6+5O59c04fCEymqqt6Gpi9MvJsHsoyC01dhK5dhGlY"
        "hmmswnbdhMOuC7tNo99lqCvmzcN8Pgvprz8bLJQJfLHIQy3woTfg9aoOG8V2XYf9thWBOqxEoGmY"
        "O4//SUv8bDh43y3Deqpjtsd9r+h03oT9phJ4JTIL3S80LxPRLBTFD1XIc5O8bcowSm6yfDsM4f00"
        "hvNpCKdDGw5bLCilRhFWUy4CmayBbB6qZRZYIy332siyWVgu8+j1Rh4beB/OxzGSIPPtWvcAHgUa"
        "Y57OcxHGLlMhLfn8gHVVFdHnHcBHgDsBd+GE7NtGkmOH5gyZamIWYxyMwEoEiE5WVJWp8JIVZD4M"
        "VfT6JFADRgW8XsZA+p0UAMjBJycgK4ihz2VfHm1E0bT81wOWsO26hUAaeY3fvQi0KjgjsE8EOG5W"
        "ZZR76OdGIGbvBMwWSGDFU9sSlotFpsUWAmtM9ig9/ltw7Rj9pzCZm8BvCWCBSPCbOV37pBULSdUr"
        "ewoO6VHgLAUIlDirFiBE9mTed3gPOJXv4DckdHQScVeIxJdKcLFW4a1Xyvw0hfe3Kfw6ryw4f6P6"
        "aTbqgHFRZe7SO4FPSDDX73+pBNJTKNNYh+NhDB+/topd+HjfRALn4yBwtVoVHQtZ5rM7YD/eE7iG"
        "9QdTYnnbH2DCXm3qUtl1yn4VPv7ZW4gANhy2tFzAtb+Vdaz6S+UbgB+/inU6Mq+hKL1LWuEhVSXf"
        "8XyM8mMDrZbKX0tKgPtWmXdJ+ov8Vwu+I4ECHJnTNje14B2PBwsFxnZjm5HxakxdLvkNeCTgJAZT"
        "wesh9gGFZ3sb0QId47ZUHRRugRNYTTSeWuCl/jCLPreNjjHrJDmgkYSKkPO7MDKPwBbsCHs+uPyZ"
        "FyEyUIBdV6jnl9rfubLXgsrOJb+TPQUkPPzapRPehElvzwa64lJ9hqQjuA+rA3msxXigrCcWc/Ab"
        "kCj5vRKDtlaMRBKZvRN69t6S6TOfviOgAtuCPdq3lgmLOYHxjoDd8/u9wD2YS5GRdcw8+s4TVfs/"
        "bb1YeF8NtiMTbbErAc/uEpBISjiJTpXNceyNBFuWzLvWZL/s++8Gk5hsiwnkQiLFI4FHEgLrCRVb"
        "1xYquGvT+TZzH0wqCr1OVVpAJO7AU7gKkHFCXDcV+J/8FjBtvSzz5zL3AQGKBBUakYjZYIfUeCRC"
        "wXLvGiY3QeaVtjbJvP5iGlWABJno9VsZOUgkouDcs72EE9A5ClrFPyH7ZwPZaM9XAlc1eupDgUUG"
        "yjeC3oQTeNsUsbH90bugD6sFdoT5GUG08CVbjwRu4d679H+YvQ/7FvCCdALE4+8iZk0wl+yfrvr/"
        "GmaFfYoBcFWCKHWNsHvMMemzvwPOuLXCvgfLf2V9R0B189K2e2YYiSxmd1HiAZzvRd92fy3720E9"
        "sLgrcQvOb677g+Z/IcCivjUptEcCSI9Vr4PPZr8BKuBHdKe6kcYAAAAASUVORK5CYII="
    ),
    "lightning": (
        "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"
        "RU5ErkJggg=="
    ),
    "water": (
        "iVBORw0KGgoAAAANSUhEUgAAACAAAAAgCAYAAABzenr0AAAAAXNSR0IArs4c6QAAAARnQU1BAACx"
        "jwv8YQUAAAAJcEhZcwAADsMAAA7DAcdvqGQAAARqSURBVFhHtZchd+pAFIQrkZFIJBIZGYmMRCIj"
        "IyORSCQSWVmJRFY+iXyyP+G5vPlm74YU2lPaQ/ecewgk2Zk7d/bu8vSdMSmm/XRR9vNlrVhG1P6N"
        "e/HY741iNutnVdUvVut3MSurvpjOfpnAZKJMFwZcdttLtJt+Ua98j2fi6QePSdGTPUDLtutX20O/"
        "2kXomt+4xzO/QmIynVrmsmmd9Wqz7+vNTuB7k1jquly3yQt6Nl570ED6shRAY1AD8ykivhaBmhCp"
        "ctX42afiUSoInIxwe2XpU+Z1F8F1qLDeP5vUvK6TCo8ohaWX6ytJX28kPWDXBFBBPmgOLyKhcnQb"
        "vbN8TCmK+dyuH4DicwzONZ6wIaUCSkDYq+LHA+nl6Dmul6xrJsd41D1nP0Tygksh8Ob5KDJ7E/9x"
        "KXhxKtdXTaeJdx8SWEb4e6iBCi6FPukPlO9HpUA+XG9ZCda95Y5sAW+JkSIQkAqUIPkhl0Kr4ltD"
        "ksEcMzGJCcS6ByibMHXBCJNIJuWdVmVoX456Z2tD3l0GS6/sYb5WHckEAlniTAIwJK4cXCc1IOcy"
        "iEB3fNX7UqFNhrxrs7LrZbyV6t4gJQooq/cEArxJkVRIJTE5VBDx9uUkIkpA392mNXfAfDJG0pNB"
        "rqMVgEQQQfoE3kVkEgpKw5KEvMtwcjlSb6i+KEVReG8HhJfIgokcNuKIgBXotDdcSLgUXSJqI1IG"
        "EzhZNbopGIE2GmI10Y0C50ft04tSQRISgxJXCpTrFIMSVkA+uCIAeVYVGGAFcgzAZ3Nnv5Rraafd"
        "8dRvT6/9RkbCzWuZiUnZcMg+A1+HiYngYMRIxH1BZUAFsAI5jex8r3uBU/vt6dTvX/84uO5EwkRE"
        "AgWS9MgeYUXyd/UGyoARUZFSoh7dURg3LRpJ+JGbAHR6aXdK4ATXqLHVJxMyuYFEJHfDFHxPwTMo"
        "NvgIAlGGGwIuQWw6PNiq5gCaxJ9zf1A8n//2L3/f/BtyXghgyA+Ce/ICoD4r6JPvi3otrI8I2APa"
        "eDCQXqB2kAD8cD73x7e3/vXfPxE5uzekeitc+1YHkQh/l0eiJEkNzCsCIgbGbT9gFcTmQ22XYpvW"
        "8HEgkQlw3YjgAKqMyCpFo2ilpM6HCu5DwuAqkY9swph8dHr2MpQ0PnYFAeqH+XbywUEleFYJIEQJ"
        "EgEAR+ACvIAnZUxAvYGyZPlvlyEjeoGXIptQmCc7eaOSEHY0S5EeAOB15pLfBPKSFDAtmmdnZZyS"
        "Pu2GusHWaRW0ZDIBVgZZ0x/Ylun3nnwgQZA54CMCAU7tIept+VPwGKknQIIzYDKknaxrDDosOU0K"
        "CZvOkuuawICKqkngPLPgpHz3cT0MyR5uEgL3YYTMFfT6GwKjyMAGJ3OBDwfUr7Ifj6wEvYGzQdr7"
        "WeOXyXMZctiYNh6KJH/cn/n1CCVwLX80MCfZeH0HkUQgBcsXcEDzv2U7/ruZ3wxeZomqfc40sWWG"
        "gI2YVQgCOF1y+/Qz1VK7C/jp6T+aEcVp/DH27gAAAABJRU5ErkJggg=="
    ),
    "light": (
        "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"
        "LuEAAAAASUVORK5CYII="
    ),
    "dark": (
        "iVBORw0KGgoAAAANSUhEUgAAACAAAAAgCAYAAABzenr0AAAAAXNSR0IArs4c6QAAAARnQU1BAACx"
        "jwv8YQUAAAAJcEhZcwAADsMAAA7DAcdvqGQAAAPcSURBVFhHzZetc+tADMQNDQ0NDQ0DAw0NAwML"
        "AwMDCwv7H/vpp9OeZceZaVPyPLNjv/vQrla6S19z9LRNu4ztuJzb8wZTNy1zNy9zH+DbwHhed2pP"
        "vr9v+oVYEfbnT9d0WwHdSn7pL0+oImydI0S8JQDyoRmqgJw1ZNfh+oz+WoSEK3JkbH7pgshRX8kt"
        "KCQf48dyG2/L7XRb7qd7wbm8GWOONayVK9kJYgfN8YPKfebKmOAQPc4Px+f0WTCX92Mq4xIiEdUJ"
        "i6meCLr1gXifuWr9MaxZZ9TsDZBXQYgJIbghJ6Z2csiNoC4P5Ay+ylzWXoaocQJjzMmVr/mrikBk"
        "diK7sekLGoVB1GVyAueaKkhGdcrWkbW7QVkM1QlzkTUI1j74VgFBLuud3DYBvt3C2OjirON9HoGs"
        "SSeAMXfiUpygRLkniAU2AiDfZy8osMbVD2Qnmxlj3hOwtcxTCpXjjhOU0cWWewO+eipy9kxmQEpW"
        "3nTpFDi5mtC+WSOXIFI/AMqCKDkBuKy2AmxApASRGGVbm2t33DSPOG/SsJg5+uD78u1vFxtugamf"
        "lq59IUAngawIDrHOO4EYVyZkq6CMKwHEIBYB7kKIZN19vHup+jaO4yqgHK1cy0oeAgjAHHuAu2X/"
        "VlMi6lCAfVcB9p6HAwEEIoNs/16Aaq2rdWgH36uTILCO9YcC9g6QsWxXDclEArz+JgAbGUewjhAi"
        "+Dd7PHPIzQ3Wsi8LYEy9s+mBLEDIDmQBWAshDgBd3+yppTMC1nMXSABxNgLMtXoKJEDwjKhr2EgA"
        "z8ICMMYca7hMuEX51l4colEhr8gCjByHKNvmGJYg5Q3IaC+AbzJQo7EOAdkF9tTmE3m491KAZxLX"
        "sYJ6YxkRm1zALhOIKIdbb2vlGHMQbgTYHt0DkNOw8DwJEMgIO+kDNj4FJCO62ua8pgGRs0brlb1O"
        "AEkRdyMAwoFfxLBTP81+oxHYyETub0MWpHHGBI1XoWE9TpHc5ue4CFghAdjLxlqGjB1hBnNkXhvP"
        "koAcEJO7w4n1YAXQ0eIbIdjkxzFEkA1BwZOgEMVbxF5z6wtsJ/NDcj3YIQECJWHT1ZqNLLASEVmI"
        "k6Ux/1bWkMcNSTL15nv1IKK4oXf5v0ERsf5h6h0N+Ka5osG8zpExpIC9qnnQ/OxBDKAUfsHwV5AF"
        "F2klT6SyWteyyEmCZCL07x42ol5nHRI1VIYLMJEihxjoXnlbgB5EEIzgkMhiyGX/bYi/eHZCcID9"
        "9di9+5CFjipBESRn/K8hOt1Rbkfm6XrW/9kBPeoNQFAvkXV3Bj+zmtPa2P4/Pk3zD9ISuS1KREor"
        "AAAAAElFTkSuQmCC"
    ),
}
_elem_images = {}


def _elem_for(ch):
    i = ord(ch) - 0xE000
    return _ELEM_ORDER[i] if 0 <= i < len(_ELEM_ORDER) else None


def _elem_image(name):
    """32x32 halved to 16 so it sits on the text line. Built once, then cached --
    the card redraws on every keystroke in the search box."""
    if name in _elem_images:
        return _elem_images[name]
    img = None
    try:
        img = tk.PhotoImage(data=_ELEM_PNG[name.lower()]).subsample(2, 2)
    except Exception:
        img = None
    _elem_images[name] = img
    return img


# ─────────────────────── the results list ───────────────────────
#
# A Listbox cannot hold an image, so the results panel is drawn on a canvas: an
# accent bar, the icon, the name, and the category under it -- the same row the
# phone app draws. With no icons installed it collapses to a single line of text
# and the panel looks exactly as it did before.

_ROW_H_ICON = 38
_ROW_H_PLAIN = 22


class ResultsList(tk.Frame):
    def __init__(self, master, on_pick, on_context, **kw):
        tk.Frame.__init__(self, master, bg="#14141c", **kw)
        self._on_pick = on_pick
        self._on_context = on_context
        self.canvas = tk.Canvas(self, bg="#14141c", highlightthickness=0, bd=0)
        self.bar = ttk.Scrollbar(self, orient="vertical", command=self.canvas.yview)
        self.canvas.configure(yscrollcommand=self.bar.set)
        self.bar.pack(side="right", fill="y")
        self.canvas.pack(side="left", fill="both", expand=True)
        self.rows = []          # (label, category, item_id)
        self.sel = None
        self.icons = IconLoader(self.canvas, self._icon_ready)
        self._name_font = ("Segoe UI", 10)
        self._sub_font = ("Segoe UI", 8)
        self._redraw_after = None
        self.canvas.bind("<Button-1>", self._click)
        self.canvas.bind("<Button-3>", self._right)
        self.canvas.bind("<Configure>", lambda e: self._redraw())
        self.canvas.bind("<MouseWheel>", self._wheel)
        self.canvas.bind("<Button-4>", lambda e: self.canvas.yview_scroll(-3, "units"))
        self.canvas.bind("<Button-5>", lambda e: self.canvas.yview_scroll(3, "units"))

    # -- data -------------------------------------------------------------
    def set_rows(self, rows):
        self.rows = rows
        self.sel = None
        self.canvas.yview_moveto(0)
        for _label, _cat, iid in rows[:400]:
            self.icons.request(iid)
        self._redraw()

    def row_height(self):
        return _ROW_H_ICON if _ICONS.found_any else _ROW_H_PLAIN

    # -- drawing ----------------------------------------------------------
    def _redraw(self):
        c = self.canvas
        c.delete("all")
        h = self.row_height()
        w = max(c.winfo_width(), 60)
        total = h * len(self.rows)
        c.configure(scrollregion=(0, 0, w, max(total, 1)))
        top = c.canvasy(0)
        first = max(0, int(top // h) - 2)
        last = min(len(self.rows), first + int(c.winfo_height() // h) + 5)
        icons_on = _ICONS.found_any
        for i in range(first, last):
            label, cat, iid = self.rows[i]
            y = i * h
            if i == self.sel:
                c.create_rectangle(0, y, w, y + h, fill="#33415c", width=0)
            c.create_rectangle(0, y + 2, 3, y + h - 2, fill="#4f7a58", width=0)
            x = 12
            if icons_on:
                img = self.icons.peek(iid)
                if img is not None:
                    c.create_image(x + 16, y + h // 2, image=img)
                x += 40
            if icons_on and cat:
                c.create_text(x, y + 9, text=label, anchor="w", fill="#c8cede",
                              font=self._name_font)
                c.create_text(x, y + 26, text=cat, anchor="w", fill="#7c8296",
                              font=self._sub_font)
            else:
                c.create_text(x, y + h // 2, text=label, anchor="w",
                              fill="#c8cede", font=self._name_font)

    def _icon_ready(self, iid):
        # The first icon to resolve is also what tells the panel icons exist at all.
        # A search can resolve three hundred of them, so coalesce: one redraw for
        # however many land in the same few frames.
        if self._redraw_after is None:
            self._redraw_after = self.after(40, self._redraw_now)

    def _redraw_now(self):
        self._redraw_after = None
        self._redraw()

    # -- input ------------------------------------------------------------
    def _index_at(self, ev):
        i = int(self.canvas.canvasy(ev.y) // self.row_height())
        return i if 0 <= i < len(self.rows) else None

    def _click(self, ev):
        i = self._index_at(ev)
        if i is None:
            return
        self.sel = i
        self._redraw()
        self._on_pick(i)

    def _right(self, ev):
        i = self._index_at(ev)
        if i is None:
            return
        self.sel = i
        self._redraw()
        self._on_context(i, ev)

    def _wheel(self, ev):
        self.canvas.yview_scroll(-1 * (ev.delta // 120) * 3, "units")
        self._redraw()


# ─────────────────────── the item card ───────────────────────
#
# The client's item help window -- the panel the game draws when you highlight an
# item, and the same thing the wiki's item images are screenshots of. Nothing here
# is fetched: the window is composed from the description string and the icon in
# the item record, both of which are already on this PC. The description is drawn
# verbatim in a monospace face so the stat columns line up the way they do in game.
#
# MISSING vs the real window: the "(Dagger)All Races" line. Weapon skill and race
# mask are not in ffxi_items.json -- they are `skill` and `races` in Windower's
# items.lua, so that line appears as soon as those two fields are in the bundled
# JSON, with no change here.

_CARD_BG = "#23232e"
_CARD_PAD_X = 12
_CARD_PAD_Y = 10


class ItemCard(tk.Canvas):
    def __init__(self, master, **kw):
        tk.Canvas.__init__(self, master, bg="#1e1e28", highlightthickness=0,
                           bd=0, height=90, **kw)
        self.item = None
        self.iid = None
        self.icons = IconLoader(self, lambda iid: self.redraw())
        self._name_font = tkfont.Font(family="Segoe UI", size=11, weight="bold")
        self._mono = tkfont.Font(family="Consolas", size=9)
        self._small = tkfont.Font(family="Segoe UI", size=8)
        self._flag = tkfont.Font(family="Segoe UI", size=8, weight="bold")
        self._last_w = 0
        self.bind("<Configure>", self._on_resize)

    def show(self, iid, item):
        self.iid = iid
        self.item = item
        if iid:
            self.icons.request(iid)
        self.redraw()

    def _on_resize(self, ev):
        if abs(ev.width - self._last_w) > 2:
            self._last_w = ev.width
            self.redraw()

    # -- text layout ------------------------------------------------------
    def _tokens(self, line):
        """A line as a list of ('t', text) / ('e', element) tokens, split on words."""
        out, buf = [], ""
        for ch in line:
            el = _elem_for(ch)
            if el:
                if buf:
                    out.append(("t", buf))
                    buf = ""
                out.append(("e", el))
            elif ch == " ":
                buf += ch
                out.append(("t", buf))
                buf = ""
            else:
                buf += ch
        if buf:
            out.append(("t", buf))
        return out

    def _wrap(self, line, maxpx):
        """Wrap into display lines. An element icon is 16px wide whatever the font."""
        lines, cur, x = [], [], 0
        for kind, val in self._tokens(line):
            w = 16 if kind == "e" else self._mono.measure(val)
            if cur and x + w > maxpx:
                lines.append(cur)
                cur, x = [], 0
                if kind == "t" and not val.strip():
                    continue            # a wrapped-away trailing space
            cur.append((kind, val))
            x += w
        lines.append(cur)
        return lines or [[]]

    def _draw_tokens(self, x, y, toks, fill):
        for kind, val in toks:
            if kind == "e":
                img = _elem_image(val)
                if img is not None:
                    self.create_image(x + 8, y, image=img)
                    self._keep.append(img)
                else:
                    self.create_text(x, y, text=val, anchor="w",
                                     fill=_ELEM_COLOR.get(val, "#c2c8d6"),
                                     font=self._mono)
                x += 16
            else:
                self.create_text(x, y, text=val, anchor="w", fill=fill,
                                 font=self._mono)
                x += self._mono.measure(val)

    def _round_rect(self, x0, y0, x1, y1, r, **kw):
        pts = [x0 + r, y0, x1 - r, y0, x1, y0, x1, y0 + r, x1, y1 - r, x1, y1,
               x1 - r, y1, x0 + r, y1, x0, y1, x0, y1 - r, x0, y0 + r, x0, y0]
        return self.create_polygon(pts, smooth=True, **kw)

    # -- the card ---------------------------------------------------------
    def redraw(self):
        self.delete("all")
        self._keep = []                      # canvas images need a live reference
        it = self.item
        if not it:
            self.configure(height=8)
            return
        W = max(self.winfo_width(), 320)
        panel_w = W - 2 * _CARD_PAD_X
        img = self.icons.peek(self.iid) if self.iid else None

        # Reserve the tile as soon as we know icons exist at all, so the text does
        # not jump sideways when one resolves a frame after the card is drawn.
        text_x = _CARD_PAD_X + 12 + (42 if _ICONS.found_any else 0)
        flags = [f for f in (it.get("re") or "").split("/") if f]
        flag_w = (max(self._flag.measure(f) for f in flags) + 14) if flags else 0
        text_w = max(60, panel_w - (text_x - _CARD_PAD_X) - 12 - flag_w)

        y = _CARD_PAD_Y + 10
        self.create_text(text_x, y, text=it.get("n", ""), anchor="w",
                         fill="#e6e6f0", font=self._name_font)
        y += 16

        desc = it.get("d") or ""
        if desc:
            y += 5
            for raw in desc.split("\n"):
                for toks in self._wrap(raw, text_w):
                    self._draw_tokens(text_x, y + 7, toks, "#c2c8d6")
                    y += 17

        # Lv + jobs, the way the help window prints it.
        jobs = _jobs_str(it.get("j", 0))
        lv = it.get("lv", 0)
        if jobs == "All jobs":
            jline = "Lv.%d All Jobs" % lv if lv else "All Jobs"
        elif jobs:
            jline = ("Lv.%d " % lv if lv else "") + jobs.replace(" ", "/")
        else:
            jline = ""
        if jline:
            y += 3
            for toks in self._wrap(jline, text_w):
                self._draw_tokens(text_x, y + 7, toks, "#9ab0d0")
                y += 17

        stack, ilv = it.get("s", 1), it.get("il", 0)
        if stack > 1 or ilv:
            y += 6
            if stack > 1:
                self.create_text(text_x, y + 6, text="Stacks to %d" % stack,
                                 anchor="w", fill="#8a90a2", font=self._small)
            if ilv:
                self.create_text(_CARD_PAD_X + panel_w - 12, y + 6,
                                 text="<Item Level:%d>" % ilv, anchor="e",
                                 fill="#8a90a2", font=self._small)
            y += 14

        bottom = max(y + _CARD_PAD_Y, _CARD_PAD_Y + 52)
        panel = self._round_rect(_CARD_PAD_X, _CARD_PAD_Y,
                                 _CARD_PAD_X + panel_w, bottom, 8,
                                 fill=_CARD_BG, outline="#2f2f3d")
        self.tag_lower(panel)                 # drawn last, sits behind the text

        if img is not None:
            self.create_image(_CARD_PAD_X + 12 + 16, _CARD_PAD_Y + 12 + 16, image=img)

        # Rare / Ex sit in the window's top-right corner, as they do in game.
        fy = _CARD_PAD_Y + 8
        for f in flags:
            col = "#8fd39a" if f.strip().lower() == "rare" else "#7fc4c9"
            fw = self._flag.measure(f) + 12
            fx = _CARD_PAD_X + panel_w - 10 - fw
            self._round_rect(fx, fy, fx + fw, fy + 16, 4, fill="#2c3340",
                             outline="")
            self.create_text(fx + fw / 2, fy + 8, text=f, fill=col,
                             font=self._flag)
            fy += 19

        self.configure(height=bottom + 2)


# ─────────────────────────── the app ───────────────────────────
class AHBrowser(tk.Tk):
    def __init__(self):
        super().__init__()
        self.title("AuctionWatch")
        self._ui = _load_ui()
        self.configure(bg="#1e1e28")
        self._ui_save_after = None
        self._build()
        self.update_idletasks()
        self.geometry(self._ui.get("geometry", "980x620"))
        self.after(120, self._restore_sash)
        self.bind("<Configure>", self._on_configure)
        self.tree.bind("<ButtonRelease-1>",
                       lambda e: self._schedule_ui_save(), add="+")
        self.protocol("WM_DELETE_WINDOW", self._on_close)
        self._cur_id = None
        self._pop_busy = False
        self._cat_cache = {}   # AH category -> {itemid: (singles, stacks)}
        self._xs_cache = {}    # item_id -> {"single":[(world,med)..], "stack":[..]}
        self._hist_rows = []
        self._sort_col = "date"
        self._sort_rev = True   # newest first by default
        self.after(400, self._refresh_population)

    def _build(self):
        top = tk.Frame(self, bg="#1e1e28")
        top.pack(fill="x", padx=8, pady=6)
        tk.Label(top, text="Search:", bg="#1e1e28", fg="#dcdce6").pack(side="left")
        self.q = tk.Entry(top, width=30)
        self.q.pack(side="left", padx=6)
        self.q.bind("<KeyRelease>", lambda e: self._do_search())
        self.q.focus_set()
        self._servers = _load_servers()
        tk.Label(top, text="World:", bg="#1e1e28", fg="#dcdce6").pack(
            side="left", padx=(16, 0))
        self.world = ttk.Combobox(top, values=_WORLDS, width=12,
                                  state="readonly")
        self.world.set(self._ui.get("world", "Phoenix"))
        self.world.pack(side="left", padx=6)
        self.world.bind("<<ComboboxSelected>>", lambda e: self._world_changed())
        tk.Label(top, text="Address:", bg="#1e1e28", fg="#dcdce6").pack(
            side="left")
        self.server = tk.Entry(top, width=16)
        self.server.insert(0, self._servers.get(self.world.get(), ""))
        self.server.pack(side="left", padx=6)
        tk.Button(top, text="Save", command=self._save_addr).pack(
            side="left", padx=2)
        tk.Button(top, text="Detect", command=self._detect).pack(
            side="left", padx=2)
        tk.Button(top, text="Default",
                  command=self._set_default_world).pack(side="left", padx=2)
        self.status = tk.Label(top, text="",
                               bg="#1e1e28", fg="#8a90a2")
        self.status.pack(side="right")

        # bottom: thin live server-population strip.
        self.popsec = tk.Frame(self, bg="#181820")
        self.popsec.pack(side="bottom", fill="x", padx=8, pady=(0, 6))
        self.pop_total_lbl = tk.Label(self.popsec, text="population \u2014",
                                      bg="#181820", fg="#8fd39a",
                                      font=("Segoe UI", 10))
        self.pop_total_lbl.pack(side="left", padx=(4, 0), pady=2)
        tk.Button(self.popsec, text="Refresh",
                  command=self._refresh_population).pack(side="right", padx=4,
                                                         pady=2)

        body = self.body = tk.PanedWindow(self, sashwidth=4, bg="#2a2a38")
        body.pack(fill="both", expand=True, padx=8, pady=(0, 8))
        body.bind("<ButtonRelease-1>",
                  lambda e: self._schedule_ui_save(), add="+")

        # left: results
        left = tk.Frame(body, bg="#1e1e28")
        self.results = ResultsList(left, self._pick, self._results_rightclick)
        # cross-server median-price ranking for the selected item, filling the
        # empty results-panel space (all 16 worlds queried in parallel).
        self.xserver = tk.Listbox(left, activestyle="none", bg="#12121a",
                                  fg="#c8cede", highlightthickness=0, height=16,
                                  selectbackground="#33415c",
                                  font=("Consolas", 9))
        self.xserver.pack(side="bottom", fill="x")
        self.xs_lbl = tk.Label(left, text="", bg="#1e1e28", fg="#8a90a2",
                               anchor="w", font=("Segoe UI", 8))
        self.xs_lbl.pack(side="bottom", fill="x", padx=2, pady=(4, 1))
        self.results.pack(fill="both", expand=True)
        body.add(left, minsize=220)

        # right: detail
        right = tk.Frame(body, bg="#1e1e28")
        self.card = ItemCard(right)
        self.card.pack(fill="x", padx=4, pady=(6, 0))
        self.meta_lbl = tk.Label(right, text="", bg="#1e1e28", fg="#7c8296",
                                 anchor="w")
        self.meta_lbl.pack(fill="x", padx=17, pady=(1, 8))

        cols = ("date", "price", "seller", "buyer")
        hdr = tk.Frame(right, bg="#1e1e28"); hdr.pack(fill="x", padx=8)
        self.hist_lbl = tk.Label(hdr, text="Auction history", bg="#1e1e28",
                                 fg="#dcdce6", font=("Segoe UI", 10, "bold"))
        self.hist_lbl.pack(side="left")
        self._type_filter = "all"
        self._onsale = None
        self._filter_btns = {}
        fbf = tk.Frame(hdr, bg="#1e1e28")
        fbf.pack(side="left", padx=12)
        for key, lbl in (("all", "All"), ("single", "Singles"),
                         ("stack", "Stacks")):
            b = tk.Button(fbf, text=lbl, relief="flat", bd=0, bg="#2a2a38",
                          fg="#c8cede", activebackground="#33415c",
                          padx=8, pady=0,
                          command=lambda k=key: self._set_filter(k))
            b.pack(side="left", padx=1)
            self._filter_btns[key] = b
        self._filter_btns["all"].config(bg="#33415c")
        self.summary = tk.Label(hdr, text="", bg="#1e1e28", fg="#8fd39a")
        self.summary.pack(side="right")

        self.tree = ttk.Treeview(right, columns=cols, show="headings", height=16)
        self._col_titles = {"date": "Sold (date / time)", "price": "Price",
                            "seller": "Seller", "buyer": "Buyer"}
        for c, w in (("date", 150), ("price", 100), ("seller", 115),
                     ("buyer", 115)):
            self.tree.heading(c, text=self._col_titles[c],
                              command=lambda cc=c: self._sort_by(cc))
            self.tree.column(c, width=self._ui.get("cols", {}).get(c, w),
                             anchor="w", stretch=False)
        self.tree.pack(fill="both", expand=True, padx=8, pady=(2, 8))
        body.add(right, minsize=520)

    def _world_changed(self):
        w = self.world.get()
        addr = self._servers.get(w, "")
        self.server.delete(0, "end")
        self.server.insert(0, addr)
        self._cat_cache = {}          # listings are per-server; drop stale cache
        # server/address already show in the toolbar; don't repeat them here.
        if addr:
            self.status.config(text="")
            self._refresh_population()
        else:
            self.status.config(text="%s: no address yet -- type it and Save" % w)
        # if an item is up and this world has an address, re-pull it live
        if self._cur_id is not None and addr:
            self._refresh_current()

    def _detect(self):
        # Find the current world's search server from this PC's live TCP
        # table (the game must be running / recently /search'd on that world).
        self.status.config(text="detecting current world's server\u2026")

        def _worker():
            try:
                ip = _ahsrch_find_server()
            except Exception:
                ip = None

            def _apply():
                if ip:
                    self.server.delete(0, "end")
                    self.server.insert(0, ip)
                    self.status.config(
                        text="detected %s  \u2014  pick the world, then Save" % ip)
                else:
                    self.status.config(
                        text="not found \u2014 /search in-game on this world first")
            self.after(0, _apply)
        threading.Thread(target=_worker, daemon=True).start()

    def _current_host(self):
        # Prefer the address box; fall back to the world map / auto-detect.
        ip = self.server.get().strip()
        return ip or _ahsrch_resolve_host(self.world.get())

    def _refresh_population(self):
        if getattr(self, "_pop_busy", False):
            return
        world = self.world.get()
        host = self._current_host()
        if not host:
            self.pop_total_lbl.config(text="%s \u2014 no address" % world,
                                      fg="#d39a9a")
            return
        self._pop_busy = True
        self.pop_total_lbl.config(text="%s \u2014 querying\u2026" % world,
                                  fg="#8a90a2")

        def _worker():
            try:
                total = _ahsrch_query_population(host)
            except Exception:
                total = None

            def _apply():
                self._pop_busy = False
                if total is None:
                    self.pop_total_lbl.config(text="%s \u2014 no reply" % world,
                                              fg="#d39a9a")
                else:
                    self.pop_total_lbl.config(
                        text="%s \u2014 %s online" % (world, format(total, ",")),
                        fg="#8fd39a")
            self.after(0, _apply)
        threading.Thread(target=_worker, daemon=True).start()


    def _set_default_world(self):
        # remember the current world so it opens automatically next launch.
        w = self.world.get()
        self._ui["world"] = w
        self._save_ui_state()
        self.status.config(text="%s will open by default" % w)

    def _save_addr(self):
        w = self.world.get()
        ip = self.server.get().strip()
        self._servers[w] = ip
        _save_servers(self._servers)
        self.status.config(text="saved  %s -> %s" % (w, ip or "(blank)"))

    def _on_configure(self, event):
        if event.widget is self:
            self._schedule_ui_save()

    def _schedule_ui_save(self):
        # debounce: save 700ms after the last resize / column drag
        if self._ui_save_after is not None:
            try:
                self.after_cancel(self._ui_save_after)
            except Exception:
                pass
        self._ui_save_after = self.after(700, self._save_ui_state)

    def _save_ui_state(self):
        self._ui_save_after = None
        try:
            cols = {c: int(self.tree.column(c, "width"))
                    for c in ("date", "price", "seller", "buyer")}
            state = {"geometry": self.geometry(), "cols": cols}
            if self._ui.get("world"):
                state["world"] = self._ui["world"]
            try:
                state["sash"] = int(self.body.sash_coord(0)[0])
            except Exception:
                pass
            _save_ui(state)
        except Exception:
            pass

    def _restore_sash(self):
        # left-panel width persists across runs; default a bit wide so the
        # cross-server header is fully readable on first launch.
        try:
            self.body.sash_place(0, int(self._ui.get("sash", 300)), 1)
        except Exception:
            pass

    def _on_close(self):
        self._save_ui_state()
        self.destroy()

    def _results_rightclick(self, idx, event):
        if idx is None or idx < 0 or idx >= len(getattr(self, "_hits", [])):
            return
        name, iid = self._hits[idx]
        ffxiah = "https://www.ffxiah.com/item/%d" % iid
        bgwiki = "https://www.bg-wiki.com/ffxi/" + name.replace(" ", "_")
        menu = tk.Menu(self, tearoff=0)
        menu.add_command(label="Open on FFXIAH",
                         command=lambda: webbrowser.open(ffxiah))
        menu.add_command(label="Open on BG-wiki",
                         command=lambda: webbrowser.open(bgwiki))
        try:
            menu.tk_popup(event.x_root, event.y_root)
        finally:
            menu.grab_release()

    def _do_search(self):
        self._hits = search_items(self.q.get())
        self.results.set_rows([(_list_label(n, i),
                                ITEMS.get(str(i), {}).get("c", ""), i)
                               for (n, i) in self._hits])

    def _pick(self, idx):
        try:
            _name, iid = self._hits[idx]
        except (AttributeError, IndexError):
            return
        self._cur_id = iid
        it = ITEMS.get(str(iid), {})
        # The card is the game's own help window; the strip under it carries the
        # things that window does not show and the browser needs.
        self.card.show(iid, it)
        bits = ["id %d" % iid, it.get("c", "?")]
        sl = _slot_str(it.get("sl", 0))
        if sl:
            bits.append(sl)
        if it.get("lv") and not it.get("j"):
            bits.append("Lv %d" % it["lv"])
        self.meta_lbl.config(text="   \u00b7   ".join(bits))
        self._refresh_current()
        self._refresh_population()
        self._compare_servers(iid)

    def _refresh_current(self):
        iid = self._cur_id
        if iid is None:
            return
        for r in self.tree.get_children():
            self.tree.delete(r)
        self.summary.config(text="")
        self.hist_lbl.config(text="Auction history  —  loading…")
        threading.Thread(target=self._load_history, args=(iid,),
                         daemon=True).start()

    def _sort_by(self, col):
        if self._sort_col == col:
            self._sort_rev = not self._sort_rev
        else:
            self._sort_col = col
            # sensible first click: newest / highest / A-Z
            self._sort_rev = col in ("date", "price")
        self._render_rows()

    def _set_filter(self, k):
        self._type_filter = k
        for key, b in self._filter_btns.items():
            b.config(bg="#33415c" if key == k else "#2a2a38")
        self._render_rows()
        if self._cur_id is not None:
            self._compare_servers(self._cur_id)

    def _xs_form(self):
        # cross-server medians follow the Singles/Stacks toggle (All -> singles)
        return "stack" if self._type_filter == "stack" else "single"

    def _render_rows(self):
        for r in self.tree.get_children():
            self.tree.delete(r)
        rows = self._hist_rows
        if self._type_filter != "all":
            rows = [r for r in rows if r[3] == self._type_filter]
        keyfns = {
            "date": lambda r: r[0],
            "price": lambda r: r[2],
            "seller": lambda r: (r[4] or "").lower(),
            "buyer": lambda r: (r[5] or "").lower(),
        }
        kf = keyfns.get(self._sort_col, keyfns["date"])
        rows = sorted(rows, key=kf, reverse=self._sort_rev)
        for (_ts, dstr, price, tag, seller, buyer) in rows:
            ptxt = f"{price:,}" + ("  (stack)" if tag == "stack" else "")
            self.tree.insert("", "end", values=(dstr, ptxt, seller, buyer))
        for c, base in self._col_titles.items():
            arrow = ""
            if c == self._sort_col:
                arrow = "  \u25bc" if self._sort_rev else "  \u25b2"
            self.tree.heading(c, text=base + arrow)
        # summary follows the current filter
        def _n(v):
            return "n/a" if v == 0xFFFFFFFF else str(v)
        parts = []
        if self._onsale is not None:
            parts.append("on sale now: %s single / %s stack"
                         % (_n(self._onsale[0]), _n(self._onsale[1])))
        fprices = [r[2] for r in rows]
        if fprices:
            lo, hi = min(fprices), max(fprices)
            med = int(statistics.median(fprices))
            lbl = {"single": "single ", "stack": "stack "}.get(
                self._type_filter, "")
            parts.append(f"{lbl}low {lo:,}  ·  med {med:,}  ·  high {hi:,} g")
        self.summary.config(text="      |      ".join(parts))
        if self._hist_rows or self._onsale is not None:
            self.hist_lbl.config(text="Auction history")
        else:
            self.hist_lbl.config(text="Auction history  —  no data / no answer")

    def _compare_servers(self, iid):
        # Fan the item's median-price query (for the currently-selected form)
        # out across every world with a known address, in parallel, and rank
        # cheapest -> priciest in the left panel. Each form is cached so toggling
        # Singles/Stacks is instant after the first fetch.
        form = self._xs_form()
        cached = self._xs_cache.get(iid, {}).get(form)
        if cached is not None:
            self._render_xservers(iid, cached, form)
            return
        worlds = [(w, self._servers.get(w)) for w in _WORLDS
                  if self._servers.get(w)]
        if not worlds:
            return
        self.xserver.delete(0, "end")
        self.xs_lbl.config(text="comparing %d servers\u2026" % len(worlds))
        stack = (form == "stack")

        def _worker():
            import concurrent.futures as _cf
            results = []
            try:
                with _cf.ThreadPoolExecutor(max_workers=len(worlds)) as ex:
                    fut = {ex.submit(_ahsrch_median_price, ip, iid, stack): w
                           for w, ip in worlds}
                    for f in _cf.as_completed(fut):
                        try:
                            med = f.result()
                        except Exception:
                            med = None
                        if med is not None:
                            results.append((fut[f], med))
            except Exception:
                pass
            results.sort(key=lambda t: t[1])
            self._xs_cache.setdefault(iid, {})[form] = results
            self.after(0, lambda: self._render_xservers(iid, results, form))
        threading.Thread(target=_worker, daemon=True).start()

    def _render_xservers(self, iid, results, form):
        if iid != self._cur_id or form != self._xs_form():
            return   # stale: user moved to another item or switched filter
        self.xserver.delete(0, "end")
        noun = "stacks" if form == "stack" else "singles"
        if not results:
            self.xs_lbl.config(text="no %s history on any server" % noun)
            return
        self.xs_lbl.config(
            text="median price by server (%s, cheapest first)" % noun)
        for world, med in results:
            self.xserver.insert("end", " %-13s %13s g" % (world, format(med, ",")))
        self.xserver.itemconfig(0, fg="#8fd39a")                 # cheapest
        self.xserver.itemconfig(len(results) - 1, fg="#e39a9a")  # priciest

    def _load_history(self, iid):
        host = self.server.get().strip()
        w = self.world.get()
        if host and self._servers.get(w) != host:
            self._servers[w] = host
            _save_servers(self._servers)   # remember whatever they typed
        if not host:
            self.after(0, lambda: self.hist_lbl.config(
                text="Auction history  —  set an Address for %s (then Save)" % w))
            return
        rows, prices, cat = [], [], None
        for stack in (0, 1):
            try:
                raw = _ahsrch_query_history(host, _AHSRCH_PORT, iid, stack,
                                            timeout=8.0)
                res = _ahsrch_parse_history(raw)
            except Exception as e:
                res = {"ok": False, "err": repr(e)}
            if res.get("ok"):
                if cat is None:
                    cat = res.get("cat")
                for sv in res.get("sales", []):
                    tag = "stack" if stack else "single"
                    rows.append((sv.get("date", 0),
                                 _fmt_ts(sv.get("date", 0)),
                                 sv.get("price", 0), tag,
                                 sv.get("seller", ""), sv.get("buyer", "")))
                    prices.append(sv.get("price", 0))
        # how many are CURRENTLY on sale (live listings from the category page)
        onsale = None
        if cat:
            try:
                avail = self._cat_cache.get(cat)
                if avail is None:
                    avail = _ahsrch_query_category(host, _AHSRCH_PORT, cat,
                                                   timeout=8.0)["items"]
                    self._cat_cache[cat] = avail
                onsale = avail.get(iid, (0xFFFFFFFF, 0xFFFFFFFF))
            except Exception:
                onsale = None
        if iid != self._cur_id:
            return   # user moved on
        self.after(0, lambda: self._show_history(rows, prices, onsale))

    def _show_history(self, rows, prices, onsale):
        self._hist_rows = rows
        self._onsale = onsale
        self._render_rows()


def _ahsrch_resolve_host(arg=None):
    # Resolve a server argument: an explicit IPv4, a world name (from the saved
    # server map), else auto-detect from this PC's TCP table, else the default.
    if arg:
        if re.match(r"^\d{1,3}(?:\.\d{1,3}){3}$", arg):
            return arg
        for name, ip in _load_servers().items():
            if name.lower() == arg.lower():
                return ip
    return _ahsrch_find_server() or _DEFAULT_SERVER


def main():
    if not ITEMS:
        root = tk.Tk(); root.withdraw()
        from tkinter import messagebox
        messagebox.showerror("AuctionWatch",
                             "ffxi_items.json not found next to the app.")
        return
    AHBrowser().mainloop()


if __name__ == "__main__":
    main()