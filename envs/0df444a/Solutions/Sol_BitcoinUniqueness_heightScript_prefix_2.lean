-- Prove2me | solution 2 for BitcoinUniqueness.heightScript_prefix
-- status  : ACCEPTED   (prove)
-- author  : @pitimespi
-- created : 2026-10-29T15:13:03.004423+00:00
-- url     : https://prove2.me/submissions/f0db4f44-9931-481d-b09c-56fe81dc4a6b

import Definitions.Def_BitcoinUniqueness
import Theorems.Thm_BitcoinBlockV2_acceptance
import Theorems.Thm_BitcoinBlockV2_apply_spec
import Theorems.Thm_BitcoinBlockV2_reachable_wellFormed
import Theorems.Thm_BitcoinScript_serialize_roundtrip
import Theorems.Thm_BitcoinSer_leBytes_length
import Theorems.Thm_BitcoinSer_readLE_leBytes
import Theorems.Thm_BitcoinUniqueness_pushBytes_prefix

open BitcoinUniqueness BitcoinSer BitcoinBlockV2

private theorem leBytes_inj (k a b : Nat) (ha : a < 2 ^ (8 * k)) (hb : b < 2 ^ (8 * k))
    (h : BitcoinSer.leBytes k a = BitcoinSer.leBytes k b) : a = b := by
  have h1 := BitcoinSer.readLE_leBytes k a [] ha
  have h2 := BitcoinSer.readLE_leBytes k b [] hb
  rw [h] at h1; rw [h1] at h2
  simp only [Option.some.injEq, Prod.mk.injEq] at h2
  exact h2.1

private theorem ofNat8_inj (a b : Nat) (ha : a < 256) (hb : b < 256) (h : BitVec.ofNat 8 a = BitVec.ofNat 8 b) : a = b := by
  have := congrArg BitVec.toNat h
  simp only [BitVec.toNat_ofNat] at this
  rwa [Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb] at this

private theorem natBytes_length : ∀ (k n : Nat), n < 256 ^ k → (BitcoinScript.natBytes n).length ≤ k
  | 0, n, h => by
    have : n = 0 := by simp at h; omega
    subst this; simp [BitcoinScript.natBytes]
  | k + 1, n, h => by
    unfold BitcoinScript.natBytes
    split
    · simp
    · simp only [List.length_cons]
      have := natBytes_length k (n / 256) (by
        rw [Nat.pow_succ] at h
        exact Nat.div_lt_of_lt_mul (by rw [Nat.mul_comm]; exact h))
      omega

private theorem setTop_length : ∀ (l : BitcoinSer.Bytes), (BitcoinScript.setTop l).length = l.length
  | [] => rfl
  | [b] => rfl
  | b :: c :: s => by simp [BitcoinScript.setTop, setTop_length (c :: s)]

private theorem serialize_length (n : Nat) (hn : n < 2 ^ 32) : (BitcoinScript.serialize n).length ≤ 5 := by
  unfold BitcoinScript.serialize
  split
  · simp
  · simp only [Int.natAbs_natCast]
    have e4 : (256:Nat)^4 = 2^32 := by rfl
    have hl := natBytes_length 4 n (by omega)
    split
    · simp only [List.length_append, List.length_singleton]; omega
    · split
      · rw [setTop_length]; omega
      · omega

private theorem serialize_inj (a b : Nat) (h : BitcoinScript.serialize a = BitcoinScript.serialize b) : a = b := by
  have ha := BitcoinScript.serialize_roundtrip (a : Int)
  have hb := BitcoinScript.serialize_roundtrip (b : Int)
  rw [h] at ha; rw [ha] at hb
  exact Int.ofNat.inj hb

private theorem serialize_pos_nonempty (n : Nat) (hn : 0 < n) : BitcoinScript.serialize n ≠ [] := by
  intro h
  have := BitcoinScript.serialize_roundtrip (n : Int)
  rw [h] at this
  simp [BitcoinScript.setVch, BitcoinScript.leNat, BitcoinScript.topBit] at this
  omega

/-- The shape of a push of a non-empty element: a first byte in `1..0x4e` and at least as many
further bytes as the element. -/
private theorem pushBytes_shape (d : BitcoinSer.Bytes) (hne : d ≠ []) (hd : d.length < 2 ^ 32) :
    ∃ c rest, BitcoinSig.pushBytes d = c :: rest ∧ 1 ≤ c.toNat ∧ c.toNat ≤ 0x4e ∧ d.length ≤ rest.length := by
  have hpos : 0 < d.length := List.length_pos_iff.2 hne
  unfold BitcoinSig.pushBytes
  simp only [BitcoinSig.OP_PUSHDATA1, BitcoinSig.OP_PUSHDATA2, BitcoinSig.OP_PUSHDATA4]
  by_cases c1 : d.length < 76
  · simp only [c1, ite_true]
    refine ⟨_, d, rfl, ?_, ?_, Nat.le_refl _⟩ <;> simp only [BitVec.toNat_ofNat] <;> omega
  · simp only [c1, ite_false]
    by_cases c2 : d.length ≤ 255
    · simp only [c2, ite_true]
      refine ⟨_, _, rfl, ?_, ?_, by simp⟩ <;> simp only [BitVec.toNat_ofNat] <;> omega
    · simp only [c2, ite_false]
      by_cases c3 : d.length ≤ 65535
      · simp only [c3, ite_true]
        refine ⟨_, _, rfl, by decide, by decide, ?_⟩
        show d.length ≤ (BitcoinSer.leBytes 2 d.length ++ d).length
        rw [List.length_append, BitcoinSer.leBytes_length]; omega
      · simp only [c3, ite_false]
        refine ⟨_, _, rfl, by decide, by decide, ?_⟩
        show d.length ≤ (BitcoinSer.leBytes 4 d.length ++ d).length
        rw [List.length_append, BitcoinSer.leBytes_length]; omega

/-- A single byte `0` or `0x50 + n` (`n ≤ 16`) is never a prefix of a push, and a push is never a
prefix of a single byte. -/
private theorem single_push_no_prefix (x : BitcoinSer.Byte) (hx : x.toNat = 0 ∨ 0x51 ≤ x.toNat) (d : BitcoinSer.Bytes)
    (hne : d ≠ []) (hd : d.length < 2 ^ 32) :
    [x].isPrefixOf (BitcoinSig.pushBytes d) = false ∧ (BitcoinSig.pushBytes d).isPrefixOf [x] = false := by
  obtain ⟨c, rest, hp, h1, h2, h3⟩ := pushBytes_shape d hne hd
  rw [hp]
  constructor
  · apply Bool.eq_false_iff.2; intro h
    rw [List.isPrefixOf_iff_prefix, List.cons_prefix_cons] at h
    rw [h.1] at hx; omega
  · apply Bool.eq_false_iff.2; intro h
    rw [List.isPrefixOf_iff_prefix, List.cons_prefix_cons] at h
    have := List.IsPrefix.length_le h.2
    have hpos : 0 < d.length := List.length_pos_iff.2 hne
    simp only [List.length_nil] at this; omega

/-- The BIP34 height pushes are prefix-free: a height push that is a prefix of another is the same
push, of the same height. (Heights below `2^31`, the `int nHeight` range.) -/
theorem solution (a b : Nat) (ha : a < 2 ^ 31) (hb : b < 2 ^ 31)
    (h : (BitcoinBlockV2.heightScript a).isPrefixOf (BitcoinBlockV2.heightScript b) = true) : a = b := by
  have hsa : (BitcoinScript.serialize a).length < 2 ^ 32 := by have := serialize_length a (by omega); omega
  have hsb : (BitcoinScript.serialize b).length < 2 ^ 32 := by have := serialize_length b (by omega); omega
  unfold heightScript at h
  by_cases a0 : a = 0
  · subst a0
    simp only [ite_true] at h
    by_cases b0 : b = 0
    · exact b0.symm
    · simp only [b0, ite_false] at h
      by_cases b16 : b ≤ 16
      · simp only [b16, ite_true] at h
        rw [List.isPrefixOf_iff_prefix, List.cons_prefix_cons] at h
        have := congrArg BitVec.toNat h.1; simp at this; omega
      · simp only [b16, ite_false] at h
        have := (single_push_no_prefix 0 (Or.inl rfl) _ (serialize_pos_nonempty b (by omega)) hsb).1
        rw [this] at h; cases h
  · simp only [a0, ite_false] at h
    by_cases a16 : a ≤ 16
    · simp only [a16, ite_true] at h
      by_cases b0 : b = 0
      · subst b0; simp only [ite_true] at h
        rw [List.isPrefixOf_iff_prefix, List.cons_prefix_cons] at h
        have := congrArg BitVec.toNat h.1; simp at this; omega
      · simp only [b0, ite_false] at h
        by_cases b16 : b ≤ 16
        · simp only [b16, ite_true] at h
          rw [List.isPrefixOf_iff_prefix, List.cons_prefix_cons] at h
          exact ofNat8_inj _ _ (by omega) (by omega) h.1 |> fun e => by omega
        · simp only [b16, ite_false] at h
          have := (single_push_no_prefix (BitVec.ofNat 8 (0x50 + a)) (Or.inr (by simp only [BitVec.toNat_ofNat]; omega)) _
            (serialize_pos_nonempty b (by omega)) hsb).1
          rw [this] at h; cases h
    · simp only [a16, ite_false] at h
      by_cases b0 : b = 0
      · subst b0; simp only [ite_true] at h
        have := (single_push_no_prefix 0 (Or.inl rfl) _ (serialize_pos_nonempty a (by omega)) hsa).2
        rw [this] at h; cases h
      · simp only [b0, ite_false] at h
        by_cases b16 : b ≤ 16
        · simp only [b16, ite_true] at h
          have := (single_push_no_prefix (BitVec.ofNat 8 (0x50 + b)) (Or.inr (by simp only [BitVec.toNat_ofNat]; omega)) _
            (serialize_pos_nonempty a (by omega)) hsa).2
          rw [this] at h; cases h
        · simp only [b16, ite_false] at h
          exact serialize_inj a b (BitcoinUniqueness.pushBytes_prefix _ _ hsa hsb h)
