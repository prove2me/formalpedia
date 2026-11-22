-- Prove2me | solution 1 for Formalism.BranchingDeterminantCap.bmA_prod_update_succ
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T21:02:07.725218+00:00
-- url     : https://prove2.me/submissions/07eb7b01-2a8e-4743-a511-2d4eea71bb67

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
theorem _root_.solution {n : ℕ} (g : Fin (n + 1) → A) (k : Fin n) (w : A) :
    (List.ofFn (Function.update g k.succ w)).prod =
      g 0 * (List.ofFn (Function.update (fun i : Fin n => g i.succ) k w)).prod := by
  rw [List.ofFn_succ, List.prod_cons, Function.update_of_ne (Fin.succ_ne_zero k).symm]
  congr 1
  congr 1
  congr 1
  funext i
  by_cases h : i = k
  · subst h
    simp
  · rw [Function.update_of_ne h, Function.update_of_ne (fun h' => h (Fin.succ_injective _ h'))]
end Formalism.BranchingDeterminantCap
