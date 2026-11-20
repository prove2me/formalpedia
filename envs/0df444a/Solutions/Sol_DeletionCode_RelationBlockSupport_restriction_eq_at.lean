-- Prove2me | solution 1 for DeletionCode.RelationBlockSupport.restriction_eq_at
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T06:15:55.120941+00:00
-- url     : https://prove2.me/submissions/061b33c7-e29e-47db-b7b3-1dbe8ab75e0e

import Definitions.Def_DeletionCode_RelationSupport
import Definitions.Def_DeletionCode_RelationBlockSupport

set_option autoImplicit true
open DeletionCode DeletionCode.RelationBlockSupport
open SignedSupport RuleSetGraph GeneratingBlocks
open scoped BigOperators
namespace DeletionCode.RelationBlockSupport
theorem _root_.solution {I : Type*} [Fintype I] {L : ℕ}
    (G : I → Gram L → ℤ) (w : Gram L → ℤ) (a : I → ℚ)
    (hrel : RelationSupport.Relation G w a) (T : Finset I) (g : Gram L)
    (houtside : ∀ i, i ∉ T → G i g = 0) :
    (w g : ℚ) = ∑ i ∈ T, a i * (G i g : ℚ) := by
  classical
  rw [hrel g]
  symm
  apply Finset.sum_subset (Finset.subset_univ T)
  intro i _ hi
  simp [houtside i hi]
end DeletionCode.RelationBlockSupport
