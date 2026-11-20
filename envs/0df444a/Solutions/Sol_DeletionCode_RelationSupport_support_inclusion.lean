-- Prove2me | solution 1 for DeletionCode.RelationSupport.support_inclusion
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T06:15:52.496007+00:00
-- url     : https://prove2.me/submissions/91f2f9d2-66c5-4893-9654-04ba7995a82a

import Definitions.Def_DeletionCode_WitnessAlgebra
import Definitions.Def_DeletionCode_RelationSupport

set_option autoImplicit true
open DeletionCode DeletionCode.RelationSupport
open SignedSupport
open scoped BigOperators
namespace DeletionCode.RelationSupport
theorem _root_.solution {I : Type*} [Fintype I] {L : ℕ}
    (G : I → Gram L → ℤ) (w : Gram L → ℤ) (a : I → ℚ)
    (hrel : Relation G w a) (g : Gram L) (hw : w g ≠ 0) :
    ∃ i, G i g ≠ 0 := by
  classical
  by_contra hnone
  push Not at hnone
  have hz : (w g : ℚ) = 0 := by
    rw [hrel g]
    apply Finset.sum_eq_zero
    intro i _
    simp [hnone i]
  exact hw (by exact_mod_cast hz)
end DeletionCode.RelationSupport
