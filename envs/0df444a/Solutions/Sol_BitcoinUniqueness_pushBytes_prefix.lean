-- Prove2me | solution 1 for BitcoinUniqueness.pushBytes_prefix
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-29T14:01:00.453985+00:00
-- url     : https://prove2.me/submissions/aa417abf-0a42-4b13-a5fd-9a2ffb2e9493

import Definitions.Def_BitcoinUniqueness
import Definitions.Def_BitcoinSer
import Definitions.Def_BitcoinSig
open BitcoinUniqueness BitcoinSer BitcoinBlockV2

theorem s229_leVal_leBytes (k n : Nat) : leVal (leBytes k n) = n % 256 ^ k := by
  induction k generalizing n with
  | zero => simp [leBytes, leVal, Nat.mod_one]
  | succ k ih =>
    simp only [leBytes, leVal, ih, BitVec.toNat_ofNat]
    rw [show 256 ^ (k+1) = 256 * 256 ^ k from Nat.pow_succ', Nat.mod_mul (a := 256) (b := 256 ^ k)]
    have e : n % 256 % (2^7*2) = n % 256 := Nat.mod_mod n 256
    rw [e]

theorem s229_leBytes_length (k n : Nat) : (leBytes k n).length = k := by
  induction k generalizing n with
  | zero => rfl
  | succ k ih => simp [leBytes, ih]

theorem s229_ofNat8_inj {a b : Nat} (ha : a < 256) (hb : b < 256)
    (h : BitVec.ofNat 8 a = BitVec.ofNat 8 b) : a = b := by
  have := congrArg BitVec.toNat h
  simp only [BitVec.toNat_ofNat] at this
  omega

theorem s229_append_eq {d d' t : BitcoinSer.Bytes} (h : d ++ t = d') (hl : d.length = d'.length) :
    d = d' := by
  have : t.length = 0 := by
    have := congrArg List.length h
    simp at this; omega
  rw [List.length_eq_zero_iff] at this
  subst this; simpa using h

theorem solution (d d' : BitcoinSer.Bytes) (hd : d.length < 2 ^ 32) (hd' : d'.length < 2 ^ 32)
    (h : (BitcoinSig.pushBytes d).isPrefixOf (BitcoinSig.pushBytes d') = true) : d = d' := by
  rw [List.isPrefixOf_iff_prefix] at h
  obtain ⟨t, ht⟩ := h
  unfold BitcoinSig.pushBytes BitcoinSig.OP_PUSHDATA1 BitcoinSig.OP_PUSHDATA2 BitcoinSig.OP_PUSHDATA4 at ht
  by_cases h1 : d.length < 76 <;> by_cases h2 : d.length ≤ 255 <;> by_cases h3 : d.length ≤ 65535 <;>
  by_cases h1' : d'.length < 76 <;> by_cases h2' : d'.length ≤ 255 <;> by_cases h3' : d'.length ≤ 65535 <;>
  simp only [h1, h2, h3, h1', h2', h3', if_true, if_false, List.cons_append, List.nil_append,
    List.append_assoc, List.cons.injEq, true_and] at ht
  all_goals first | omega | skip
  all_goals first
    | (obtain ⟨hb, hr⟩ := ht
       have hb' := congrArg BitVec.toNat hb
       simp only [BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod] at hb'
       first | (exfalso; omega) | exact s229_append_eq hr (by omega))
    | (obtain ⟨hl, hr⟩ := List.append_inj ht (by simp [s229_leBytes_length])
       have hv := congrArg leVal hl
       rw [s229_leVal_leBytes, s229_leVal_leBytes] at hv
       simp only [Nat.reducePow] at hv
       exact s229_append_eq hr (by omega))
