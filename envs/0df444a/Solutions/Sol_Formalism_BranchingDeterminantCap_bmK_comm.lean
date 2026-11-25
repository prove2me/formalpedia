-- Prove2me | solution 1 for Formalism.BranchingDeterminantCap.bmK_comm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T00:58:26.993877+00:00
-- url     : https://prove2.me/submissions/70d2d8f6-79ea-4839-aade-e6158b73ab77

import Mathlib
import Definitions.Def_Formalism_GradedWeylDivisibility_FinalC
import Definitions.Def_Formalism_BranchSandwichDivisors_StatementW
import Definitions.Def_Formalism_BranchSandwichDivisors_BranchIsometryProofs_MemBranchRangeOfDefectEq
import Definitions.Def_Formalism_BranchSandwichDivisors_BranchIsometryProofs_BranchMap
import Theorems.Thm_Formalism_BranchingDeterminantCap_capDet_commute_of
import Theorems.Thm_Formalism_BranchingDeterminantCap_bmK_central

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
theorem _root_.solution (R : Type*) [CommRing R] [IsDomain R] [CharZero R] (n : ℕ) (u v : ℤ) :
    Commute (bmCap R n u) (bmCap R n v) := by
  exact (capDet_commute_of (bmEL R n) u (bmCap R n v) (fun i j => (bmK_central R n i j v).symm)).symm
end Formalism.BranchingDeterminantCap
