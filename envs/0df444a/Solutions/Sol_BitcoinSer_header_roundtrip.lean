-- Prove2me | solution 1 for BitcoinSer.header_roundtrip
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-26T14:08:51.403002+00:00
-- url     : https://prove2.me/submissions/6362bcda-203f-4a0a-8ef7-e04a87c726ff

import Definitions.Def_BitcoinSer

namespace BR_Hdr
open BitcoinSer

theorem BR_len (k n : Nat) : (leBytes k n).length = k := by
  induction k generalizing n with
  | zero => rfl
  | succ k ih => simp [leBytes, ih]

theorem BR_val (k n : Nat) (h : n < 2 ^ (8 * k)) : leVal (leBytes k n) = n := by
  induction k generalizing n with
  | zero => simp at h; subst h; rfl
  | succ k ih =>
    simp only [leBytes, leVal]
    have : n / 256 < 2 ^ (8 * k) := by
      rw [Nat.div_lt_iff_lt_mul (by decide)]
      have : 2 ^ (8 * (k+1)) = 2 ^ (8*k) * 256 := by rw [show 8*(k+1) = 8*k+8 by omega, Nat.pow_add]
      omega
    rw [ih _ this]
    simp [BitVec.toNat_ofNat]
    omega

theorem BR_read (k n : Nat) (rest : Bytes) (h : n < 2 ^ (8 * k)) :
    readLE k (leBytes k n ++ rest) = some (n, rest) := by
  simp [readLE, BR_len, BR_val k n h]

theorem BR_read32 (n : Nat) (rest : Bytes) (h : n < 2 ^ 32) :
    readLE 4 (ser32 n ++ rest) = some (n, rest) := BR_read 4 n rest h

theorem BR_hash (p rest : Bytes) (h : p.length = 32) :
    readHash (p ++ rest) = some (p, rest) := by
  simp [readHash, h]

theorem BR_int32 (v : Int) (rest : Bytes) (h1 : -(2 ^ 31) ≤ v) (h2 : v < 2 ^ 31) :
    readInt32 (serInt32 v ++ rest) = some (v, rest) := by
  have hnn : 0 ≤ v % 2 ^ 32 := Int.emod_nonneg _ (by decide)
  have hm : (((v % 2 ^ 32).toNat : Nat) : Int) = v % 2 ^ 32 := Int.toNat_of_nonneg hnn
  have hlt : (v % 2 ^ 32).toNat < 2 ^ (8 * 4) := by omega
  simp only [readInt32, serInt32, BR_read 4 _ rest hlt, Option.map_some]
  congr 2
  split <;> omega

end BR_Hdr

open BitcoinSer in
theorem solution (h : Header) (rest : Bytes) (hw : h.wf) :
    BitcoinSer.readHeader (BitcoinSer.serHeader h ++ rest) = some (h, rest) := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := hw
  simp only [readHeader, serHeader, List.append_assoc, BR_Hdr.BR_int32 _ _ h1 h2,
    BR_Hdr.BR_hash _ _ h3, BR_Hdr.BR_hash _ _ h4, BR_Hdr.BR_read32 _ _ h5,
    BR_Hdr.BR_read32 _ _ h6, BR_Hdr.BR_read32 _ _ h7]

