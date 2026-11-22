-- Prove2me | solution 1 for Formalism.BranchingDeterminantCap.bmA_prod_update_sub
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T23:23:35.478784+00:00
-- url     : https://prove2.me/submissions/4dec82fc-55cd-47a8-9b3a-eb97f741cde7

import Mathlib
import Definitions.Def_Formalism_GradedWeylDivisibility_FinalC
import Definitions.Def_Formalism_BranchSandwichDivisors_StatementW
import Definitions.Def_Formalism_BranchSandwichDivisors_BranchIsometryProofs_MemBranchRangeOfDefectEq
import Definitions.Def_Formalism_BranchSandwichDivisors_BranchIsometryProofs_BranchMap
import Theorems.Thm_Formalism_BranchingDeterminantCap_bmA_prod_update_zero
import Theorems.Thm_Formalism_BranchingDeterminantCap_bmA_prod_update_succ
import Theorems.Thm_Formalism_GradedWeylDivisibility_CoeffHom_prod


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial Formalism.GradedWeylDivisibility
noncomputable section
open Formalism Formalism.BranchingDeterminantCap
variable {A : Type*} [Ring A]
namespace Formalism.BranchingDeterminantCap
theorem _root_.solution {n : ℕ} (g : Fin n → A) (k : Fin n) (a b : A) :
    (List.ofFn (Function.update g k (a - b))).prod =
      (List.ofFn (Function.update g k a)).prod - (List.ofFn (Function.update g k b)).prod := by
  induction n with
  | zero => exact k.elim0
  | succ n ih =>
    cases k using Fin.cases with
    | zero => rw [bmA_prod_update_zero, bmA_prod_update_zero, bmA_prod_update_zero, sub_mul]
    | succ k => rw [bmA_prod_update_succ, bmA_prod_update_succ, bmA_prod_update_succ, ih, mul_sub]
end Formalism.BranchingDeterminantCap
