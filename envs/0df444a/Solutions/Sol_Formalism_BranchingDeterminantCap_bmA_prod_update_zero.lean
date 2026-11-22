-- Prove2me | solution 1 for Formalism.BranchingDeterminantCap.bmA_prod_update_zero
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T21:02:11.137795+00:00
-- url     : https://prove2.me/submissions/9fb70eb6-4047-4cc7-a974-3f088876f63e

import Mathlib
import Definitions.Def_Formalism_GradedWeylDivisibility_FinalC
import Definitions.Def_Formalism_BranchSandwichDivisors_StatementW
import Definitions.Def_Formalism_BranchSandwichDivisors_BranchIsometryProofs_MemBranchRangeOfDefectEq
import Definitions.Def_Formalism_BranchSandwichDivisors_BranchIsometryProofs_BranchMap
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
theorem _root_.solution {n : ℕ} (g : Fin (n + 1) → A) (w : A) :
    (List.ofFn (Function.update g 0 w)).prod = w * (List.ofFn fun i : Fin n => g i.succ).prod := by
  simp [List.ofFn_succ, Function.update_of_ne, Fin.succ_ne_zero]
end Formalism.BranchingDeterminantCap
