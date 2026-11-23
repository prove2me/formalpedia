-- Prove2me | solution 1 for Formalism.BranchingDeterminantCap.bmK_list_mem
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:28:56.146048+00:00
-- url     : https://prove2.me/submissions/86950da7-c6f4-4f31-86ba-c46a183b9c3e

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
theorem _root_.solution {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M] (C : ℤ → Module.End R M)
    (W : Submodule R M) (hC : ∀ u, ∀ G ∈ W, C u G ∈ W) (ℓ : List ℤ) : ∀ G ∈ W, (ℓ.map C).prod G ∈ W := by
  induction ℓ with
  | nil => intro G hG; simpa using hG
  | cons a t ih =>
    intro G hG
    rw [List.map_cons, List.prod_cons]
    exact hC a _ (ih G hG)
end Formalism.BranchingDeterminantCap
