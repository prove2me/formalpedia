-- Prove2me | solution 2 for BitcoinUniqueness.pushBytes_prefix
-- status  : ACCEPTED   (prove)
-- author  : @pitimespi
-- created : 2026-10-29T15:12:27.617522+00:00
-- url     : https://prove2.me/submissions/a7a7767d-c4b4-446d-8f82-a25064b7ae0f

import Definitions.Def_BitcoinUniqueness
import Theorems.Thm_BitcoinBlockV2_acceptance
import Theorems.Thm_BitcoinBlockV2_apply_spec
import Theorems.Thm_BitcoinBlockV2_reachable_wellFormed
import Theorems.Thm_BitcoinScript_serialize_roundtrip
import Theorems.Thm_BitcoinSer_leBytes_length
import Theorems.Thm_BitcoinSer_readLE_leBytes

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

/-- A push is never a proper prefix of another push: `pushBytes d` prefix of `pushBytes d'` forces
`d = d'`. The first byte fixes the encoding class and (with the length field) the length. -/
theorem solution (d d' : BitcoinSer.Bytes) (hd : d.length < 2 ^ 32) (hd' : d'.length < 2 ^ 32)
    (h : (BitcoinSig.pushBytes d).isPrefixOf (BitcoinSig.pushBytes d') = true) : d = d' := by
  rw [List.isPrefixOf_iff_prefix] at h
  unfold BitcoinSig.pushBytes at h
  simp only [BitcoinSig.OP_PUSHDATA1, BitcoinSig.OP_PUSHDATA2, BitcoinSig.OP_PUSHDATA4] at h
  -- classes: direct (< 76), PUSHDATA1 (≤ 255), PUSHDATA2 (≤ 65535), PUSHDATA4
  by_cases c1 : d.length < 76 <;> by_cases c1' : d'.length < 76 <;>
    by_cases c2 : d.length ≤ 255 <;> by_cases c2' : d'.length ≤ 255 <;>
    by_cases c3 : d.length ≤ 65535 <;> by_cases c3' : d'.length ≤ 65535 <;>
    simp only [c1, c1', c2, c2', c3, c3', ite_true, ite_false, List.cons_append,
      List.cons_prefix_cons, List.nil_append] at h <;>
    (try omega) <;>
    (try (obtain ⟨hb, hp⟩ := h; exfalso;
          have := congrArg BitVec.toNat hb; simp only [BitVec.toNat_ofNat] at this; omega))
  · -- direct / direct
    obtain ⟨hb, hp⟩ := h
    have hl : d.length = d'.length := ofNat8_inj _ _ (by omega) (by omega) hb
    exact List.IsPrefix.eq_of_length hp hl
  · -- PUSHDATA1 / PUSHDATA1
    obtain ⟨-, hb, hp⟩ := h
    have hl : d.length = d'.length := ofNat8_inj _ _ (by omega) (by omega) hb
    exact List.IsPrefix.eq_of_length hp hl
  · -- PUSHDATA2 / PUSHDATA2
    obtain ⟨-, hp⟩ := h
    have hl2 := BitcoinSer.leBytes_length 2 d.length
    have hl2' := BitcoinSer.leBytes_length 2 d'.length
    have hA : BitcoinSer.leBytes 2 d.length <+: BitcoinSer.leBytes 2 d'.length ++ d' :=
      (List.prefix_append _ _).trans hp
    have hB : BitcoinSer.leBytes 2 d'.length <+: BitcoinSer.leBytes 2 d'.length ++ d' := List.prefix_append _ _
    have hpre' : BitcoinSer.leBytes 2 d.length <+: BitcoinSer.leBytes 2 d'.length :=
      List.prefix_of_prefix_length_le hA hB (by omega)
    have heq := List.IsPrefix.eq_of_length hpre' (by omega)
    have hl : d.length = d'.length := leBytes_inj 2 _ _ (by omega) (by omega) heq
    rw [heq] at hp
    exact List.IsPrefix.eq_of_length ((List.prefix_append_right_inj _).1 hp) hl
  · -- PUSHDATA4 / PUSHDATA4
    obtain ⟨-, hp⟩ := h
    have hl4 := BitcoinSer.leBytes_length 4 d.length
    have hl4' := BitcoinSer.leBytes_length 4 d'.length
    have hA : BitcoinSer.leBytes 4 d.length <+: BitcoinSer.leBytes 4 d'.length ++ d' :=
      (List.prefix_append _ _).trans hp
    have hB : BitcoinSer.leBytes 4 d'.length <+: BitcoinSer.leBytes 4 d'.length ++ d' := List.prefix_append _ _
    have hpre' : BitcoinSer.leBytes 4 d.length <+: BitcoinSer.leBytes 4 d'.length :=
      List.prefix_of_prefix_length_le hA hB (by omega)
    have heq := List.IsPrefix.eq_of_length hpre' (by omega)
    have hl : d.length = d'.length := leBytes_inj 4 _ _ (by omega) (by omega) heq
    rw [heq] at hp
    exact List.IsPrefix.eq_of_length ((List.prefix_append_right_inj _).1 hp) hl
