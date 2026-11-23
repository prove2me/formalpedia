-- Prove2me | solution 1 for Formalism.BranchingDeterminantCap.elemDeriv_lastMonomial_zero
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:29:06.737372+00:00
-- url     : https://prove2.me/submissions/28ead47d-6b7a-443f-b73d-5dd531166705

import Mathlib
import Definitions.Def_Formalism_GradedWeylDivisibility_FinalC
import Definitions.Def_Formalism_BranchSandwichDivisors_StatementW
import Definitions.Def_Formalism_BranchSandwichDivisors_BranchIsometryProofs_MemBranchRangeOfDefectEq
import Definitions.Def_Formalism_BranchSandwichDivisors_BranchIsometryProofs_BranchMap
import Theorems.Thm_Formalism_BranchingDeterminantCap_elemDeriv_X
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
theorem _root_.solution (R : Type*) [CommRing R] (n : ℕ) (s t : Fin n) (b : Fin n → ℕ) :
    bmE R n s t (zmon R n b) = 0 := by
  unfold zmon
  refine Finset.prod_induction _ (fun p => bmE R n s t p = 0) (fun a b ha hb => ?_) (by simp) (fun x _ => ?_)
  · beta_reduce at ha hb ⊢
    rw [Derivation.leibniz, ha, hb, smul_zero, smul_zero, add_zero]
  · beta_reduce
    rw [Derivation.leibniz_pow, elemDeriv_X]
    simp
end Formalism.BranchingDeterminantCap
