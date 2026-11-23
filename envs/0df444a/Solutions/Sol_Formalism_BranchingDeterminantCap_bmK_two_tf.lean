-- Prove2me | solution 1 for Formalism.BranchingDeterminantCap.bmK_two_tf
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:28:56.44755+00:00
-- url     : https://prove2.me/submissions/4631939d-1cd0-47a7-a830-53d221d494fe

import Mathlib
import Definitions.Def_Formalism_GradedWeylDivisibility_FinalC
import Definitions.Def_Formalism_BranchSandwichDivisors_StatementW
import Definitions.Def_Formalism_BranchSandwichDivisors_BranchIsometryProofs_MemBranchRangeOfDefectEq
import Definitions.Def_Formalism_BranchSandwichDivisors_BranchIsometryProofs_BranchMap

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
namespace Formalism.BranchingDeterminantCap
theorem _root_.solution (R : Type*) [CommRing R] [IsDomain R] [CharZero R] (n : ℕ) (x : Module.End R (BP R n))
    (h : x + x = 0) : x = 0 := by
  refine LinearMap.ext fun F => ?_
  have h1 := LinearMap.congr_fun h F
  rw [LinearMap.add_apply, LinearMap.zero_apply] at h1
  rw [LinearMap.zero_apply]
  exact add_self_eq_zero.mp h1
end Formalism.BranchingDeterminantCap
