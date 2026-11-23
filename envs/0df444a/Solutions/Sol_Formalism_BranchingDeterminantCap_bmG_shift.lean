-- Prove2me | solution 1 for Formalism.BranchingDeterminantCap.bmG_shift
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:24:36.346869+00:00
-- url     : https://prove2.me/submissions/b0877cbb-8a6a-4046-8b13-34609390f40f

import Mathlib
import Definitions.Def_Formalism_GradedWeylDivisibility_FinalC
import Definitions.Def_Formalism_BranchSandwichDivisors_StatementW
import Definitions.Def_Formalism_BranchSandwichDivisors_BranchIsometryProofs_MemBranchRangeOfDefectEq
import Definitions.Def_Formalism_BranchSandwichDivisors_BranchIsometryProofs_BranchMap
import Theorems.Thm_Formalism_BranchingDeterminantCap_bmG_nuNext_of_succ
import Theorems.Thm_Formalism_BranchingDeterminantCap_bmG_nuNext_last
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
theorem _root_.solution {M : Type*} [CommMonoid M] (n : ℕ) (D : ℕ → M) (hD : D 0 = 1) (b : Fin n → ℕ) :
    ∏ i : Fin n, D i.val ^ b i = ∏ i : Fin n, D (i.val + 1) ^ nuNext b i := by
  cases n with
  | zero => simp
  | succ m =>
    rw [Fin.prod_univ_succ, Fin.prod_univ_castSucc (f := fun i : Fin (m + 1) => D (i.val + 1) ^ nuNext b i)]
    have h1 : nuNext b (Fin.last m) = 0 := bmG_nuNext_last b _ (by simp)
    rw [h1, pow_zero, mul_one]
    simp only [Fin.val_zero, hD, one_pow, one_mul]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [bmG_nuNext_of_succ b i.castSucc i.succ (by simp)]
    simp
end Formalism.BranchingDeterminantCap
