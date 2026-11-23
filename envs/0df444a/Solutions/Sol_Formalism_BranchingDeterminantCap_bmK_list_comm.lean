-- Prove2me | solution 1 for Formalism.BranchingDeterminantCap.bmK_list_comm
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:28:55.544837+00:00
-- url     : https://prove2.me/submissions/ac71bac1-1929-449b-9e94-f9916f82976c

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
namespace Formalism.BranchingDeterminantCap
theorem _root_.solution {A : Type*} [Ring A] (C : ℤ → A) (x : A) (hx : ∀ u, Commute x (C u)) (ℓ : List ℤ) :
    Commute x (ℓ.map C).prod := by
  induction ℓ with
  | nil => simp
  | cons a t ih =>
    rw [List.map_cons, List.prod_cons]
    exact (hx a).mul_right ih
end Formalism.BranchingDeterminantCap
