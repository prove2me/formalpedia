-- Prove2me | solution 1 for Formalism.BranchingDeterminantCap.bmEL_rel
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:42:23.228551+00:00
-- url     : https://prove2.me/submissions/904356cf-b31d-47fd-a2ea-886144085d85

import Mathlib
import Definitions.Def_Formalism_GradedWeylDivisibility_FinalC
import Definitions.Def_Formalism_BranchSandwichDivisors_StatementW
import Definitions.Def_Formalism_BranchSandwichDivisors_BranchIsometryProofs_MemBranchRangeOfDefectEq
import Definitions.Def_Formalism_BranchSandwichDivisors_BranchIsometryProofs_BranchMap
import Theorems.Thm_Formalism_BranchingDeterminantCap_elemDeriv_lie_bracket
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
theorem _root_.solution (R : Type*) [CommRing R] (n : ℕ) (i j k l : Fin n) :
    bmEL R n i j * bmEL R n k l - bmEL R n k l * bmEL R n i j =
      (if j = k then bmEL R n i l else 0) - (if i = l then bmEL R n k j else 0) := by
  refine LinearMap.ext fun F => ?_
  have h := congrArg (fun D : Derivation R (BP R n) (BP R n) => D F) (elemDeriv_lie_bracket R n i j k l)
  simp only [Derivation.commutator_apply] at h
  show bmE R n i j (bmE R n k l F) - bmE R n k l (bmE R n i j F) = _
  rw [h]
  split_ifs <;> simp [bmEL]
end Formalism.BranchingDeterminantCap
