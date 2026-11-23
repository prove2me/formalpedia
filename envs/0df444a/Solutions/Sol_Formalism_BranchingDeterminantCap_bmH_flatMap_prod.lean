-- Prove2me | solution 1 for Formalism.BranchingDeterminantCap.bmH_flatMap_prod
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:31:18.022041+00:00
-- url     : https://prove2.me/submissions/d5df6ed1-e664-4de1-91e1-bc4f86b82d36

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
theorem _root_.solution {α : Type*} (l : List α) (f : α → List ℤ) (g : ℤ → ℤ) :
    ((l.flatMap f).map g).prod = (l.map fun i => ((f i).map g).prod).prod := by
  induction l with
  | nil => simp
  | cons a t ih => simp [List.flatMap_cons, List.prod_append, ih]
end Formalism.BranchingDeterminantCap
