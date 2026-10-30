-- Prove2me | solution 1 for BitcoinTapSoundnessV2.leaf_ne_branch
-- status  : ACCEPTED   (prove)
-- author  : @pitimespi
-- created : 2026-10-29T18:05:59.772931+00:00
-- url     : https://prove2.me/submissions/3add314c-8d54-4b59-b7b1-638f7c49891e

import Definitions.Def_BitcoinTapSoundnessV2
import Theorems.Thm_BitcoinSer_sha256_length
import Theorems.Thm_BitcoinTapSoundnessV2_tagged_collision
import Theorems.Thm_BitcoinTapSoundnessV2_tapleaf_ne_tapbranch

open BitcoinTapSoundnessV2 BitcoinSer BitcoinTaproot

private theorem append_inj_len {α : Type} (a b c d : List α) (hl : a.length = c.length) (h : a ++ b = c ++ d) :
    a = c ∧ b = d :=
  List.append_inj h hl

private theorem tapleafHash_eq (v : Byte) (s : Bytes) : tapleafHash v s = tagged "TapLeaf" (leafMsg v s) := rfl

private theorem tapbranchHash_eq (a b : Bytes) : tapbranchHash a b = tagged "TapBranch" (branchMsg a b) := rfl

/-- A leaf hash equal to a branch hash: the `TapLeaf` preimage and the `TapBranch` preimage collide. -/
theorem solution (v : BitcoinSer.Byte) (s a b : BitcoinSer.Bytes)
    (h : BitcoinTaproot.tapleafHash v s = BitcoinTaproot.tapbranchHash a b) :
    BitcoinTapSoundnessV2.Collides (BitcoinTapSoundnessV2.taggedPre "TapLeaf" (BitcoinTapSoundnessV2.leafMsg v s))
      (BitcoinTapSoundnessV2.taggedPre "TapBranch" (BitcoinTapSoundnessV2.branchMsg a b)) := by
  rw [tapleafHash_eq, tapbranchHash_eq] at h
  rcases BitcoinTapSoundnessV2.tagged_collision _ _ _ _ h with ⟨ht, -⟩ | hc
  · exact absurd ht BitcoinTapSoundnessV2.tapleaf_ne_tapbranch
  · exact hc
