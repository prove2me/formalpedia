-- Prove2me | solution 1 for Formalism.BranchingDeterminantCap.bmZL_comm_bmEL
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:35:31.578843+00:00
-- url     : https://prove2.me/submissions/4375498e-89b3-4cef-a030-96b95f7ede9b

import Mathlib
import Definitions.Def_Formalism_GradedWeylDivisibility_FinalC
import Definitions.Def_Formalism_BranchSandwichDivisors_StatementW
import Definitions.Def_Formalism_BranchSandwichDivisors_BranchIsometryProofs_MemBranchRangeOfDefectEq
import Definitions.Def_Formalism_BranchSandwichDivisors_BranchIsometryProofs_BranchMap
import Theorems.Thm_Formalism_BranchingDeterminantCap_lastRowDeriv_elemDeriv_commute
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
theorem _root_.solution (R : Type*) [CommRing R] (n : ℕ) (l j s t : Fin n) :
    Commute (bmZL R n l j) (bmEL R n s t) := by
  refine LinearMap.ext fun F => ?_
  have h := congrArg (fun D : Derivation R (BP R n) (BP R n) => D F) (lastRowDeriv_elemDeriv_commute R n l j s t)
  simp only [Derivation.commutator_apply, Derivation.zero_apply] at h
  exact sub_eq_zero.mp h
end Formalism.BranchingDeterminantCap
