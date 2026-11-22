-- Prove2me | solution 1 for Formalism.BranchingDeterminantCap.elemDeriv_monomial_weighted
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T23:27:35.704204+00:00
-- url     : https://prove2.me/submissions/c8174284-6236-40bd-be98-5cd1760ad8c2

import Mathlib
import Definitions.Def_Formalism_GradedWeylDivisibility_FinalC
import Definitions.Def_Formalism_BranchSandwichDivisors_StatementW
import Definitions.Def_Formalism_BranchSandwichDivisors_BranchIsometryProofs_MemBranchRangeOfDefectEq
import Definitions.Def_Formalism_BranchSandwichDivisors_BranchIsometryProofs_BranchMap
import Theorems.Thm_Formalism_BranchingDeterminantCap_bm_deriv_monomial_WH
import Theorems.Thm_Formalism_GradedWeylDivisibility_rowDivL_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.GradedWeylDivisibility.rowDivL_apply



set_option autoImplicit false
open MvPolynomial Formalism.GradedWeylDivisibility
noncomputable section
open Formalism Formalism.BranchingDeterminantCap
namespace Formalism.BranchingDeterminantCap
theorem _root_.solution (R : Type*) [CommRing R] (n : ℕ) {B : Type*} [AddCommMonoid B]
    (w : Fin (n + 1) × Fin n → B) (hw : ∀ (a : Fin (n + 1)) (s t : Fin n), a ≠ Fin.last n → w (a, s) = w (a, t))
    (s t : Fin n) (m : Fin (n + 1) × Fin n →₀ ℕ) :
    IsWeightedHomogeneous w (bmEL R n s t (monomial m 1)) (Finsupp.weight w m) := by
  have hf : ∀ v : Fin (n + 1) × Fin n, IsWeightedHomogeneous w
      ((fun v : Fin (n + 1) × Fin n => if v.2 = t ∧ v.1 ≠ Fin.last n then (X (v.1, s) : BP R n) else 0) v)
      (w v + 0) := by
    intro v
    dsimp only
    split_ifs with hv
    · have e : w v + 0 = w (v.1, s) := by
        rw [add_zero, hw v.1 s t hv.2, ← hv.1]
      rw [e]
      apply isWeightedHomogeneous_X
    · apply isWeightedHomogeneous_zero
  have key := bm_deriv_monomial_WH (R := R) w 0 _ hf m
  rw [add_zero] at key
  exact key
end Formalism.BranchingDeterminantCap
