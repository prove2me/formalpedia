-- Prove2me | solution 1 for BitcoinTapSoundnessV2.branch_eq
-- status  : ACCEPTED   (prove)
-- author  : @pitimespi
-- created : 2026-10-29T18:06:01.602086+00:00
-- url     : https://prove2.me/submissions/c6638096-4356-46f5-8637-ef91edfcc6ba

import Definitions.Def_BitcoinTapSoundnessV2
import Theorems.Thm_BitcoinSer_sha256_length
import Theorems.Thm_BitcoinTapSoundnessV2_tagged_collision

open BitcoinTapSoundnessV2 BitcoinSer BitcoinTaproot

private theorem append_inj_len {α : Type} (a b c d : List α) (hl : a.length = c.length) (h : a ++ b = c ++ d) :
    a = c ∧ b = d :=
  List.append_inj h hl

private theorem tapleafHash_eq (v : Byte) (s : Bytes) : tapleafHash v s = tagged "TapLeaf" (leafMsg v s) := rfl

private theorem tapbranchHash_eq (a b : Bytes) : tapbranchHash a b = tagged "TapBranch" (branchMsg a b) := rfl

/-- Equal branch hashes of 32-byte children have the same two children (in some order), or the two
`TapBranch` preimages collide. -/
theorem solution (a b c d : BitcoinSer.Bytes) (ha : a.length = 32) (hb : b.length = 32)
    (hc : c.length = 32) (hd : d.length = 32) (h : BitcoinTaproot.tapbranchHash a b = BitcoinTaproot.tapbranchHash c d) :
    ((a = c ∧ b = d) ∨ (a = d ∧ b = c)) ∨
      BitcoinTapSoundnessV2.Collides (BitcoinTapSoundnessV2.taggedPre "TapBranch" (BitcoinTapSoundnessV2.branchMsg a b))
        (BitcoinTapSoundnessV2.taggedPre "TapBranch" (BitcoinTapSoundnessV2.branchMsg c d)) := by
  rw [tapbranchHash_eq, tapbranchHash_eq] at h
  rcases BitcoinTapSoundnessV2.tagged_collision _ _ _ _ h with ⟨-, hm⟩ | hcol
  · left
    unfold branchMsg at hm
    split at hm <;> split at hm
    · obtain ⟨h1, h2⟩ := append_inj_len _ _ _ _ (by rw [ha, hc]) hm; exact Or.inl ⟨h1, h2⟩
    · obtain ⟨h1, h2⟩ := append_inj_len _ _ _ _ (by rw [ha, hd]) hm; exact Or.inr ⟨h1, h2⟩
    · obtain ⟨h1, h2⟩ := append_inj_len _ _ _ _ (by rw [hb, hc]) hm; exact Or.inr ⟨h2, h1⟩
    · obtain ⟨h1, h2⟩ := append_inj_len _ _ _ _ (by rw [hb, hd]) hm; exact Or.inl ⟨h2, h1⟩
  · right; exact hcol
