-- Prove2me | solution 1 for Formalism.BranchingDeterminantCap.rowAction_ext_elemDeriv_X
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:29:27.341916+00:00
-- url     : https://prove2.me/submissions/10ef2874-7e40-45b7-94ad-056f9742d0d4

import Mathlib
import Definitions.Def_Formalism_GradedWeylDivisibility_FinalC
import Definitions.Def_Formalism_BranchSandwichDivisors_StatementW
import Definitions.Def_Formalism_BranchSandwichDivisors_BranchIsometryProofs_MemBranchRangeOfDefectEq
import Definitions.Def_Formalism_BranchSandwichDivisors_BranchIsometryProofs_BranchMap
import Theorems.Thm_Formalism_BranchingDeterminantCap_elemDeriv_X
import Theorems.Thm_Formalism_BranchingDeterminantCap_extendMatrix_last_right_zero
import Theorems.Thm_Formalism_BranchingDeterminantCap_extendMatrix_last_left_zero
import Theorems.Thm_Formalism_BranchingDeterminantCap_rowAction_X_sum
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
theorem _root_.solution (R : Type*) [CommRing R] (n : ℕ) (g : Matrix (Fin n) (Fin n) R) (s t : Fin n)
    (v : Fin (n + 1) × Fin n) :
    rowAct R (extM R g) (bmE R n s t (X v)) = bmE R n s t (rowAct R (extM R g) (X v)) := by
  rw [elemDeriv_X, rowAction_X_sum, map_sum]
  obtain ⟨a, c⟩ := v
  by_cases hc : c = t
  · subst hc
    by_cases ha : a = Fin.last n
    · subst ha
      simp only [ne_eq, not_true_eq_false, and_false, if_false, map_zero]
      refine (Finset.sum_eq_zero fun b _ => ?_).symm
      by_cases hb : b = Fin.last n
      · subst hb
        rw [Derivation.leibniz, elemDeriv_X]
        simp [MvPolynomial.derivation_C]
      · rw [extendMatrix_last_left_zero R g b hb]
        simp
    · simp only [ha, ne_eq, not_false_eq_true, and_self, if_true, rowAction_X_sum]
      refine Finset.sum_congr rfl fun b _ => ?_
      rw [Derivation.leibniz, elemDeriv_X, MvPolynomial.derivation_C, smul_zero, add_zero, smul_eq_mul]
      by_cases hb : b = Fin.last n
      · subst hb
        rw [extendMatrix_last_right_zero R g a ha]
        simp
      · simp [hb]
  · simp only [hc, false_and, if_false, map_zero]
    refine (Finset.sum_eq_zero fun b _ => ?_).symm
    rw [Derivation.leibniz, elemDeriv_X, MvPolynomial.derivation_C]
    simp [hc]
end Formalism.BranchingDeterminantCap
