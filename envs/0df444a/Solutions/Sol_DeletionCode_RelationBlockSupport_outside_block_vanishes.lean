-- Prove2me | solution 1 for DeletionCode.RelationBlockSupport.outside_block_vanishes
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T06:15:56.769946+00:00
-- url     : https://prove2.me/submissions/1b6f42e5-5ca5-4116-882f-19ffe9220e0f

import Definitions.Def_DeletionCode_RelationSupport
import Definitions.Def_DeletionCode_RelationBlockSupport
import Theorems.Thm_DeletionCode_GeneratingBlocks_common_gram_adjacent


set_option autoImplicit true
open DeletionCode DeletionCode.RelationBlockSupport
open SignedSupport RuleSetGraph GeneratingBlocks
open scoped BigOperators
namespace DeletionCode.RelationBlockSupport
theorem _root_.solution {I : Type*} {L : ℕ}
    (G : I → Gram L → ℤ) (T : Finset I)
    (hclosed : BlockClosed G (↑T : Set I)) (g : Gram L)
    (hsupport : ∃ i ∈ T, G i g ≠ 0) :
    ∀ j, j ∉ T → G j g = 0 := by
  obtain ⟨i, hi, hgi⟩ := hsupport
  intro j hj
  by_contra hgj
  exact hj (hclosed i hi j
    (Relation.EqvGen.rel i j (common_gram_adjacent G i j g hgi hgj)))
end DeletionCode.RelationBlockSupport
