-- Prove2me | solution 1 for BitcoinUniqueness.heightScript_prefix
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-29T14:01:48.466576+00:00
-- url     : https://prove2.me/submissions/edf1614e-cc15-460b-b29a-57b55805a9d5

import Definitions.Def_BitcoinUniqueness
open BitcoinUniqueness BitcoinSer BitcoinBlockV2

theorem s229_natBytes_len (k n : Nat) (h : n < 256 ^ k) : (BitcoinScript.natBytes n).length ≤ k := by
  induction k generalizing n with
  | zero =>
    have : n = 0 := by simp at h; omega
    subst this; rw [BitcoinScript.natBytes]; simp
  | succ k ih =>
    rw [BitcoinScript.natBytes]
    by_cases hn : n = 0
    · simp [hn]
    · simp only [hn, dite_false, List.length_cons]
      have : n / 256 < 256 ^ k := by
        rw [Nat.pow_succ'] at h
        exact Nat.div_lt_of_lt_mul h
      have := ih _ this
      omega

theorem s229_natBytes_ne (n : Nat) (h : n ≠ 0) : BitcoinScript.natBytes n ≠ [] := by
  rw [BitcoinScript.natBytes]; simp [h]

theorem s229_leNat_natBytes (n : Nat) : BitcoinScript.leNat (BitcoinScript.natBytes n) = n := by
  induction n using Nat.strongRecOn with
  | ind n ih =>
    rw [BitcoinScript.natBytes]
    by_cases hn : n = 0
    · simp [hn, BitcoinScript.leNat]
    · simp only [hn, dite_false, BitcoinScript.leNat, BitVec.toNat_ofNat]
      rw [ih (n / 256) (Nat.div_lt_self (Nat.pos_of_ne_zero hn) (by decide))]
      have e : n % 256 % (2^8) = n % 256 := Nat.mod_mod n 256
      rw [e]; omega

theorem s229_leNat_append0 (x : BitcoinSer.Bytes) : BitcoinScript.leNat (x ++ [0#8]) = BitcoinScript.leNat x := by
  induction x with
  | nil => simp [BitcoinScript.leNat]
  | cons b r ih => simp [BitcoinScript.leNat, ih]

theorem s229_serialize (n : Nat) (h0 : n ≠ 0) (h : n < 2 ^ 31) :
    BitcoinScript.leNat (BitcoinScript.serialize (n : Int)) = n ∧
    1 ≤ (BitcoinScript.serialize (n : Int)).length ∧ (BitcoinScript.serialize (n : Int)).length ≤ 5 := by
  have hl := s229_natBytes_len 4 n (by omega)
  have hne := s229_natBytes_ne n h0
  have hpos : 0 < (BitcoinScript.natBytes n).length := List.length_pos_iff.2 hne
  unfold BitcoinScript.serialize
  have hi : ((n : Int) = 0) = False := by simp; omega
  have hneg : ((n : Int) < 0) = False := by simp
  simp only [hi, hneg, if_false, Int.natAbs_natCast, decide_false]
  split
  · simp [s229_leNat_append0, s229_leNat_natBytes]; omega
  · simp [s229_leNat_natBytes]; omega

theorem s229_hs_cases (n : Nat) (h : n < 2 ^ 31) :
    (n = 0 ∧ heightScript n = [0#8]) ∨
    (1 ≤ n ∧ n ≤ 16 ∧ heightScript n = [BitVec.ofNat 8 (0x50 + n)]) ∨
    (16 < n ∧ heightScript n = BitVec.ofNat 8 (BitcoinScript.serialize (n : Int)).length ::
        BitcoinScript.serialize (n : Int) ∧
      1 ≤ (BitcoinScript.serialize (n : Int)).length ∧ (BitcoinScript.serialize (n : Int)).length ≤ 5 ∧
      BitcoinScript.leNat (BitcoinScript.serialize (n : Int)) = n) := by
  unfold heightScript
  by_cases h0 : n = 0
  · left; simp [h0]
  by_cases h16 : n ≤ 16
  · right; left; simp [h0, h16]; omega
  · right; right
    obtain ⟨e1, e2, e3⟩ := s229_serialize n h0 h
    refine ⟨by omega, ?_, e2, e3, e1⟩
    simp only [h0, h16, if_false]
    unfold BitcoinSig.pushBytes BitcoinSig.OP_PUSHDATA1
    rw [if_pos (by omega)]

theorem solution (a b : Nat) (ha : a < 2 ^ 31) (hb : b < 2 ^ 31)
    (h : (BitcoinBlockV2.heightScript a).isPrefixOf (BitcoinBlockV2.heightScript b) = true) : a = b := by
  rw [List.isPrefixOf_iff_prefix] at h
  obtain ⟨t, ht⟩ := h
  rcases s229_hs_cases a ha with ⟨a0, ea⟩ | ⟨a1, a2, ea⟩ | ⟨a1, ea, la1, la2, va⟩ <;>
  rcases s229_hs_cases b hb with ⟨b0, eb⟩ | ⟨b1, b2, eb⟩ | ⟨b1, eb, lb1, lb2, vb⟩ <;>
  rw [ea, eb] at ht <;> simp only [List.cons_append, List.nil_append, List.cons.injEq] at ht
  all_goals first
    | omega
    | (obtain ⟨hb', hr⟩ := ht
       have hv := congrArg BitVec.toNat hb'
       simp only [BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod] at hv
       first
       | omega
       | (have hlen : (BitcoinScript.serialize (a : Int)).length = (BitcoinScript.serialize (b : Int)).length := by omega
          have : t.length = 0 := by
            have := congrArg List.length hr
            simp at this; omega
          rw [List.length_eq_zero_iff] at this
          subst this
          simp only [List.append_nil] at hr
          rw [← va, ← vb, hr]))
