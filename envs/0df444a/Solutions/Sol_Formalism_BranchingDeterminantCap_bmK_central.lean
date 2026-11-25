-- Prove2me | solution 1 for Formalism.BranchingDeterminantCap.bmK_central
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T00:48:07.065647+00:00
-- url     : https://prove2.me/submissions/d1a30de6-d388-4d52-8194-ce8a6ad68188

import Mathlib
import Definitions.Def_Formalism_GradedWeylDivisibility_FinalC
import Definitions.Def_Formalism_BranchSandwichDivisors_StatementW
import Definitions.Def_Formalism_BranchSandwichDivisors_BranchIsometryProofs_MemBranchRangeOfDefectEq
import Definitions.Def_Formalism_BranchSandwichDivisors_BranchIsometryProofs_BranchMap
import Theorems.Thm_Formalism_BranchingDeterminantCap_bmEL_rel
import Theorems.Thm_Formalism_BranchingDeterminantCap_capDet_central
import Theorems.Thm_Formalism_BranchingDeterminantCap_bmK_two_tf

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
theorem _root_.solution (R : Type*) [CommRing R] [IsDomain R] [CharZero R] (n : ℕ) (k l : Fin n) (u : ℤ) :
    Commute (bmEL R n k l) (bmCap R n u) := by
  exact capDet_central (bmEL R n) u (bmEL_rel R n) (bmK_two_tf R n) k l
end Formalism.BranchingDeterminantCap
