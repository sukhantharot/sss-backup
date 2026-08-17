#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
sss_backup.py — แตกไฟล์เป็น n ชิ้นด้วย Shamir's Secret Sharing
                ใช้เพียง k ชิ้นก็กู้ไฟล์เดิมกลับมาได้ 100%

ใช้ไลบรารีมาตรฐานของ Python ล้วน ไม่ต้อง pip install อะไรเลย

    python sss_backup.py split  <ไฟล์>  [-k 3] [-n 5] [-o โฟลเดอร์]
    python sss_backup.py restore <โฟลเดอร์> [-o โฟลเดอร์ปลายทาง]
    python sss_backup.py            <- เมนูโต้ตอบ
"""

import os
import sys
import glob
import json
import hmac
import struct
import hashlib
import getpass
import argparse

# =====================================================================
#  ส่วนที่ 1 : เลขคณิตใน GF(256)
# ---------------------------------------------------------------------
#  GF(256) คือ "สนามจำกัด" ที่มีสมาชิก 256 ตัว พอดีกับ 1 ไบต์
#    บวก / ลบ  = XOR
#    คูณ / หาร = ใช้ตาราง log-exp บนตัวสร้าง 0x03 และ polynomial 0x11B
#  ข้อดีคือทุกการคำนวณปิดอยู่ใน 1 ไบต์ ไม่มีเศษ ไม่มีการบวมของตัวเลข
# =====================================================================

GF_EXP = [0] * 512
GF_LOG = [0] * 256


def _xtime(a):
    """คูณด้วย 2 ใน GF(256) — เลื่อนบิตซ้าย ถ้าล้นก็ลดด้วย polynomial 0x11B"""
    a <<= 1
    if a & 0x100:
        a ^= 0x11B
    return a


def _build_tables():
    x = 1
    for i in range(255):
        GF_EXP[i] = x
        GF_LOG[x] = i
        # ต้องคูณด้วย 3 ไม่ใช่ 2 !
        # เลข 2 มี multiplicative order แค่ 51 ในสนามนี้ ไม่ใช่ตัวสร้าง
        # แต่ 3 วนครบทั้ง 255 ตัว   (3·x = 2·x XOR x)
        x = _xtime(x) ^ x
    for i in range(255, 512):  # ต่อตารางให้ยาวขึ้น จะได้ไม่ต้อง mod ตอนใช้
        GF_EXP[i] = GF_EXP[i - 255]


_build_tables()


def gf_mul(a, b):
    if a == 0 or b == 0:
        return 0
    return GF_EXP[GF_LOG[a] + GF_LOG[b]]


def gf_inv(a):
    if a == 0:
        raise ZeroDivisionError("GF(256): หารด้วยศูนย์ไม่ได้")
    return GF_EXP[255 - GF_LOG[a]]


def gf_div(a, b):
    return gf_mul(a, gf_inv(b))


# ตารางคูณสำเร็จรูป 256 ชุด ชุดละ 256 ไบต์
# MUL_TABLE[c] ใช้กับ bytes.translate() เพื่อคูณทั้งสายด้วยค่าคงที่ c ในครั้งเดียว
# (เร็วกว่าวนลูปทีละไบต์ใน Python หลายสิบเท่า)
MUL_TABLE = [bytes(gf_mul(v, c) for v in range(256)) for c in range(256)]


def xor(a, b):
    """XOR สองสายไบต์ที่ยาวเท่ากัน — แปลงเป็น int ก้อนเดียวเพื่อความเร็ว"""
    if not a:
        return b''
    n = len(a)
    return (int.from_bytes(a, 'big') ^ int.from_bytes(b, 'big')).to_bytes(n, 'big')


# =====================================================================
#  ส่วนที่ 2 : Shamir's Secret Sharing บนสายไบต์
# ---------------------------------------------------------------------
#  แตก : สร้างพหุนามดีกรี k-1 ต่อหนึ่งไบต์  f(x) = a0 + a1·x + a2·x² + ...
#        โดย a0 = ไบต์ความลับ ส่วน a1..a(k-1) สุ่มใหม่ทุกไบต์
#        share ตัวที่ x คือค่า f(x)
#  ประกอบ : Lagrange interpolation ย้อนกลับไปหา f(0)
# =====================================================================

def sss_split(data: bytes, k: int, n: int) -> dict:
    """คืน dict {x: share_bytes} โดย x = 1..n"""
    if not 2 <= k <= n <= 255:
        raise ValueError("ต้องมี 2 <= k <= n <= 255")

    size = len(data)
    # สัมประสิทธิ์สุ่ม a1..a(k-1) — สุ่มแยกอิสระทุกไบต์ของไฟล์
    coeffs = [os.urandom(size) for _ in range(k - 1)]

    shares = {}
    for x in range(1, n + 1):
        acc = data          # เทอม a0
        x_pow = 1
        for c in coeffs:
            x_pow = gf_mul(x_pow, x)                  # x, x², x³, ...
            acc = xor(acc, c.translate(MUL_TABLE[x_pow]))
        shares[x] = acc
    return shares


def sss_combine(shares: dict) -> bytes:
    """รับ dict {x: share_bytes} อย่างน้อย k ชิ้น แล้วคืนข้อมูลต้นฉบับ"""
    xs = list(shares.keys())
    size = len(next(iter(shares.values())))
    result = bytes(size)

    for j in xs:
        # สัมประสิทธิ์ Lagrange ที่จุด x = 0 :  Π (x_m / (x_m - x_j))
        num = den = 1
        for m in xs:
            if m == j:
                continue
            num = gf_mul(num, m)
            den = gf_mul(den, m ^ j)      # ลบ = XOR ใน GF(256)
        lam = gf_div(num, den)
        result = xor(result, shares[j].translate(MUL_TABLE[lam]))
    return result


# =====================================================================
#  ส่วนที่ 3 : ชั้นเข้ารหัสด้วยรหัสผ่าน (encrypt-then-MAC)
# ---------------------------------------------------------------------
#  เข้ารหัสก่อน แล้วค่อยแตกเป็น shares  =>  ต่อให้เก็บ share ครบ k ชิ้น
#  แต่ไม่มีรหัสผ่าน ก็เปิดไม่ได้
#
#  หมายเหตุ: ที่นี่ใช้ HMAC-SHA256 แบบ counter mode เป็น keystream เพราะ
#  ต้องการให้พึ่งเฉพาะไลบรารีมาตรฐาน  ถ้าลง `cryptography` ได้ ควรเปลี่ยน
#  ไปใช้ AES-256-GCM ซึ่งเร็วกว่ามากและเป็นมาตรฐานที่ผ่านการตรวจสอบแล้ว
# =====================================================================

SCRYPT_N, SCRYPT_R, SCRYPT_P = 2 ** 15, 8, 1


def derive_keys(password: str, salt: bytes):
    """รหัสผ่าน -> คีย์ 2 ตัว (เข้ารหัส, ตรวจสอบความถูกต้อง)"""
    # maxmem ต้องระบุเอง ไม่งั้น OpenSSL จะจำกัดไว้แค่ 32MB แล้ว error
    dk = hashlib.scrypt(password.encode('utf-8'), salt=salt,
                        n=SCRYPT_N, r=SCRYPT_R, p=SCRYPT_P, dklen=64,
                        maxmem=SCRYPT_N * SCRYPT_R * 256)
    return dk[:32], dk[32:]


def keystream(key: bytes, nonce: bytes, length: int) -> bytes:
    out = bytearray()
    ctr = 0
    while len(out) < length:
        out += hmac.new(key, nonce + ctr.to_bytes(8, 'big'), hashlib.sha256).digest()
        ctr += 1
    return bytes(out[:length])


def encrypt(plain: bytes, k_enc: bytes, k_mac: bytes, nonce: bytes):
    cipher = xor(plain, keystream(k_enc, nonce, len(plain)))
    tag = hmac.new(k_mac, nonce + cipher, hashlib.sha256).digest()
    return cipher, tag


def decrypt(cipher: bytes, tag: bytes, k_enc: bytes, k_mac: bytes, nonce: bytes):
    expect = hmac.new(k_mac, nonce + cipher, hashlib.sha256).digest()
    if not hmac.compare_digest(tag, expect):   # เทียบแบบ constant-time
        raise ValueError("รหัสผ่านไม่ถูกต้อง หรือข้อมูลถูกแก้ไข")
    return xor(cipher, keystream(k_enc, nonce, len(cipher)))


# =====================================================================
#  ส่วนที่ 4 : รูปแบบไฟล์ share
# ---------------------------------------------------------------------
#  ทุกอย่างที่จำเป็นต่อการกู้คืนถูกฝังไว้ใน header ของ share ทุกชิ้น
#  => ไม่ต้องพึ่งไฟล์ JSON ภายนอกเลย มี share ครบ k ชิ้นก็จบ
#
#  ชื่อไฟล์เดิมกับ hash ถูกซ่อนอยู่ "ข้างใน" ส่วนที่เข้ารหัส
#  => share ที่หลุดออกไปไม่บอกใบ้ว่าข้างในคือไฟล์อะไร
# =====================================================================

MAGIC = b'SSS53\x00'
VERSION = 1
HDR_FMT = '!6sBBBB16s16s32sI'          # = 78 ไบต์
HDR_LEN = struct.calcsize(HDR_FMT)


def pack_share(x, k, n, salt, nonce, tag, payload):
    return struct.pack(HDR_FMT, MAGIC, VERSION, x, k, n,
                       salt, nonce, tag, len(payload)) + payload


def unpack_share(raw):
    if len(raw) < HDR_LEN:
        raise ValueError("ไฟล์สั้นเกินไป")
    magic, ver, x, k, n, salt, nonce, tag, plen = struct.unpack(HDR_FMT, raw[:HDR_LEN])
    if magic != MAGIC:
        raise ValueError("ไม่ใช่ไฟล์ share ของระบบนี้")
    if ver != VERSION:
        raise ValueError(f"เวอร์ชัน {ver} ไม่รองรับ")
    payload = raw[HDR_LEN:HDR_LEN + plen]
    if len(payload) != plen:
        raise ValueError("ข้อมูลไม่ครบ ไฟล์อาจเสียหาย")
    return dict(x=x, k=k, n=n, salt=salt, nonce=nonce, tag=tag, payload=payload)


# =====================================================================
#  ส่วนที่ 5 : คำสั่งหลัก
# =====================================================================

def do_split(path, password, k=3, n=5, outdir=None):
    outdir = outdir or os.path.dirname(os.path.abspath(path)) or '.'
    os.makedirs(outdir, exist_ok=True)

    with open(path, 'rb') as f:
        data = f.read()

    # เมทาดาทาถูกผูกไว้กับตัวข้อมูล แล้วเข้ารหัสไปพร้อมกัน
    meta = {
        'name': os.path.basename(path),
        'size': len(data),
        'sha256': hashlib.sha256(data).hexdigest(),
    }
    mj = json.dumps(meta, ensure_ascii=False).encode('utf-8')
    plain = struct.pack('!H', len(mj)) + mj + data

    salt, nonce = os.urandom(16), os.urandom(16)
    k_enc, k_mac = derive_keys(password, salt)
    cipher, tag = encrypt(plain, k_enc, k_mac, nonce)

    shares = sss_split(cipher, k, n)

    written = []
    for x, payload in shares.items():
        fp = os.path.join(outdir, f'part{x}.bin')
        with open(fp, 'wb') as f:
            f.write(pack_share(x, k, n, salt, nonce, tag, payload))
        written.append(fp)

    # manifest นี้ "ไม่จำเป็น" ต่อการกู้คืน มีไว้ให้คนอ่านเฉยๆ
    # และตั้งใจไม่ใส่ชื่อไฟล์เดิม/hash ลงไป เพื่อไม่ให้ข้อมูลรั่ว
    with open(os.path.join(outdir, 'manifest.json'), 'w', encoding='utf-8') as f:
        json.dump({'scheme': 'shamir-gf256', 'threshold': k, 'shares': n,
                   'kdf': f'scrypt(n={SCRYPT_N},r={SCRYPT_R},p={SCRYPT_P})',
                   'cipher': 'hmac-sha256-ctr + hmac-sha256 tag',
                   'files': [os.path.basename(p) for p in written]},
                  f, indent=2, ensure_ascii=False)

    return written, meta


def do_restore(indir, password, outdir=None):
    outdir = outdir or indir

    found = []
    for fp in sorted(glob.glob(os.path.join(indir, '*.bin'))):
        try:
            with open(fp, 'rb') as f:
                s = unpack_share(f.read())
            s['file'] = os.path.basename(fp)
            found.append(s)
        except Exception:
            continue        # ข้ามไฟล์ .bin ที่ไม่เกี่ยวข้อง

    if not found:
        raise SystemExit("ไม่พบไฟล์ share ที่ใช้ได้ในโฟลเดอร์นี้")

    # จัดกลุ่มตาม (salt, nonce, tag) — กันกรณีมี backup หลายชุดปนกัน
    groups = {}
    for s in found:
        groups.setdefault((s['salt'], s['nonce'], s['tag']), []).append(s)
    group = max(groups.values(), key=len)

    k = group[0]['k']
    # กันกรณี share ซ้ำ x เดียวกัน
    uniq = {s['x']: s for s in group}
    if len(uniq) < k:
        raise SystemExit(f"ต้องการอย่างน้อย {k} ชิ้น แต่พบเพียง {len(uniq)} ชิ้น")

    chosen = dict(sorted(uniq.items())[:k])
    print(f"[*] พบ share ใช้ได้ {len(uniq)} ชิ้น — เลือกใช้: "
          f"{[uniq[x]['file'] for x in chosen]}")

    cipher = sss_combine({x: s['payload'] for x, s in chosen.items()})

    g = group[0]
    k_enc, k_mac = derive_keys(password, g['salt'])
    plain = decrypt(cipher, g['tag'], k_enc, k_mac, g['nonce'])

    mlen = struct.unpack('!H', plain[:2])[0]
    meta = json.loads(plain[2:2 + mlen].decode('utf-8'))
    data = plain[2 + mlen:]

    if hashlib.sha256(data).hexdigest() != meta['sha256']:
        raise SystemExit("SHA-256 ไม่ตรง ข้อมูลเสียหาย")

    os.makedirs(outdir, exist_ok=True)
    dest = os.path.join(outdir, meta['name'])
    with open(dest, 'wb') as f:
        f.write(data)
    return dest, meta


# =====================================================================
#  ส่วนที่ 6 : หน้าจอ
# =====================================================================

def menu():
    print("=" * 62)
    print("  SSS BACKUP VAULT  —  Shamir's Secret Sharing")
    print("=" * 62)
    print("  [1] แตกไฟล์ (Split)")
    print("  [2] กู้คืนไฟล์ (Restore)")
    print("  [3] ออก")
    print("=" * 62)
    c = input("เลือก [1-3]: ").strip()

    if c == '1':
        path = input("ไฟล์ที่ต้องการแตก: ").strip().strip('"')
        k = int(input("ต้องใช้กี่ชิ้นถึงกู้ได้ (k) [3]: ") or 3)
        n = int(input("แตกทั้งหมดกี่ชิ้น (n) [5]: ") or 5)
        pw = getpass.getpass("ตั้งรหัสผ่าน: ")
        if pw != getpass.getpass("ยืนยันรหัสผ่าน: "):
            raise SystemExit("รหัสผ่านไม่ตรงกัน")
        files, meta = do_split(path, pw, k, n)
        print(f"\n[+] แตก '{meta['name']}' ({meta['size']:,} ไบต์) "
              f"เป็น {n} ชิ้น ใช้ {k} ชิ้นก็กู้ได้")
        for f in files:
            print("    ->", f)

    elif c == '2':
        d = input("โฟลเดอร์ที่เก็บ share [.]: ").strip().strip('"') or '.'
        pw = getpass.getpass("รหัสผ่าน: ")
        dest, meta = do_restore(d, pw)
        print(f"\n[+] กู้คืนสำเร็จ 100% -> {dest} ({meta['size']:,} ไบต์)")

    else:
        print("[*] ออกจากโปรแกรม")


def main():
    if len(sys.argv) == 1:
        menu()
        return

    ap = argparse.ArgumentParser(description="Shamir's Secret Sharing file backup")
    sub = ap.add_subparsers(dest='cmd', required=True)

    sp = sub.add_parser('split')
    sp.add_argument('file')
    sp.add_argument('-k', type=int, default=3, help='จำนวนชิ้นขั้นต่ำที่ใช้กู้')
    sp.add_argument('-n', type=int, default=5, help='จำนวนชิ้นทั้งหมด')
    sp.add_argument('-o', '--outdir')
    sp.add_argument('--password')

    rp = sub.add_parser('restore')
    rp.add_argument('dir', nargs='?', default='.')
    rp.add_argument('-o', '--outdir')
    rp.add_argument('--password')

    a = ap.parse_args()
    pw = a.password or getpass.getpass("รหัสผ่าน: ")

    if a.cmd == 'split':
        files, meta = do_split(a.file, pw, a.k, a.n, a.outdir)
        print(f"[+] แตก '{meta['name']}' ({meta['size']:,} ไบต์) เป็น {a.n} ชิ้น "
              f"(ใช้ {a.k} ชิ้นก็กู้ได้)")
        for f in files:
            print("    ->", f)
    else:
        dest, meta = do_restore(a.dir, pw, a.outdir)
        print(f"[+] กู้คืนสำเร็จ 100% -> {dest} ({meta['size']:,} ไบต์)")


if __name__ == '__main__':
    main()
