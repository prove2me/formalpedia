-- Prove2me | solution 2 for BitcoinUniqueness.coinbases_distinct
-- status  : ACCEPTED   (prove)
-- author  : @pitimespi
-- created : 2026-10-29T15:13:35.779423+00:00
-- url     : https://prove2.me/submissions/9f0eb8d1-b391-4d8f-8fc8-11afb311cd17

import Definitions.Def_BitcoinUniqueness
import Theorems.Thm_BitcoinBlockV2_acceptance
import Theorems.Thm_BitcoinBlockV2_apply_spec
import Theorems.Thm_BitcoinBlockV2_reachable_wellFormed
import Theorems.Thm_BitcoinScript_serialize_roundtrip
import Theorems.Thm_BitcoinSer_leBytes_length
import Theorems.Thm_BitcoinSer_readLE_leBytes
import Theorems.Thm_BitcoinUniqueness_coinbase_height_prefix
import Theorems.Thm_BitcoinUniqueness_heightScript_prefix

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

/-- Two blocks accepted at different heights where BIP34 is enforced (both below `2^31`) have
different coinbase `scriptSig`s: each starts with its own height push, and height pushes are
prefix-free. -/
theorem solution (S₁ S₂ : ChainState) (b₁ b₂ : BitcoinSer.Block) (now₁ now₂ : Int)
    (S₁' S₂' : ChainState) (undo₁ undo₂ : BlockUndo)
    (hR₁ : BitcoinBlockV2.Reachable S₁) (hR₂ : BitcoinBlockV2.Reachable S₂)
    (h₁ : BitcoinBlockV2.validate S₁ b₁ now₁ = .accept S₁' undo₁) (h₂ : BitcoinBlockV2.validate S₂ b₂ now₂ = .accept S₂' undo₂)
    (h34₁ : BitcoinHeader.BIP34Height ≤ S₁.nextHeight) (h34₂ : BitcoinHeader.BIP34Height ≤ S₂.nextHeight)
    (hlt₁ : S₁.nextHeight < 2 ^ 31) (hlt₂ : S₂.nextHeight < 2 ^ 31) (hne : S₁.nextHeight ≠ S₂.nextHeight) :
    BitcoinUniqueness.coinbaseScriptSig b₁ ≠ BitcoinUniqueness.coinbaseScriptSig b₂ := by
  intro heq
  have p₁ := BitcoinUniqueness.coinbase_height_prefix S₁ b₁ now₁ S₁' undo₁ hR₁ h₁ h34₁
  have p₂ := BitcoinUniqueness.coinbase_height_prefix S₂ b₂ now₂ S₂' undo₂ hR₂ h₂ h34₂
  rw [heq] at p₁
  rw [List.isPrefixOf_iff_prefix] at p₁ p₂
  -- both height pushes are prefixes of the same bytes: the shorter is a prefix of the longer
  rcases Nat.le_total (heightScript S₁.nextHeight).length (heightScript S₂.nextHeight).length with hl | hl
  · have := List.prefix_of_prefix_length_le p₁ p₂ hl
    exact hne (BitcoinUniqueness.heightScript_prefix _ _ hlt₁ hlt₂ (List.isPrefixOf_iff_prefix.2 this))
  · have := List.prefix_of_prefix_length_le p₂ p₁ hl
    exact hne (BitcoinUniqueness.heightScript_prefix _ _ hlt₂ hlt₁ (List.isPrefixOf_iff_prefix.2 this)).symm
