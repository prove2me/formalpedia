-- Prove2me | solution 1 for Formalism.BranchingDeterminantCap.bmA_comm_prod
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:22:30.7815+00:00
-- url     : https://prove2.me/submissions/41855d93-4d30-4fbd-a4d5-81ad7281d33c

import Mathlib
import Definitions.Def_Formalism_GradedWeylDivisibility_FinalC
import Definitions.Def_Formalism_BranchSandwichDivisors_StatementW
import Definitions.Def_Formalism_BranchSandwichDivisors_BranchIsometryProofs_MemBranchRangeOfDefectEq
import Definitions.Def_Formalism_BranchSandwichDivisors_BranchIsometryProofs_BranchMap
import Theorems.Thm_Formalism_BranchingDeterminantCap_bmA_prod_update_zero
import Theorems.Thm_Formalism_BranchingDeterminantCap_bmA_prod_update_succ
import Theorems.Thm_Formalism_GradedWeylDivisibility_CoeffHom_prod
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
variable {A : Type*} [Ring A]
namespace Formalism.BranchingDeterminantCap
theorem _root_.solution (x : A) : ∀ {n : ℕ} (g : Fin n → A),
    x * (List.ofFn g).prod - (List.ofFn g).prod * x =
      ∑ k, (List.ofFn (Function.update g k (x * g k - g k * x))).prod
  | 0, g => by simp
  | n + 1, g => by
    have ih := solution x (fun i : Fin n => g i.succ)
    rw [Fin.sum_univ_succ, bmA_prod_update_zero]
    simp only [bmA_prod_update_succ]
    rw [← Finset.mul_sum, ← ih, List.ofFn_succ, List.prod_cons]
    noncomm_ring
end Formalism.BranchingDeterminantCap
