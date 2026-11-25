-- Prove2me | solution 1 for Formalism.BranchingDeterminantCap.bmK_bmE
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T00:58:26.043311+00:00
-- url     : https://prove2.me/submissions/43c2dfb2-9a73-47f2-b4f1-e2e5ddb91cf7

import Mathlib
import Definitions.Def_Formalism_GradedWeylDivisibility_FinalC
import Definitions.Def_Formalism_BranchSandwichDivisors_StatementW
import Definitions.Def_Formalism_BranchSandwichDivisors_BranchIsometryProofs_MemBranchRangeOfDefectEq
import Definitions.Def_Formalism_BranchSandwichDivisors_BranchIsometryProofs_BranchMap
import Theorems.Thm_Formalism_BranchingDeterminantCap_bmE_comm_apply
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
theorem _root_.solution (R : Type*) [CommRing R] [IsDomain R] [CharZero R] (n : ℕ) (k l : Fin n) (u : ℤ) (G : BP R n) :
    bmE R n k l (bmCap R n u G) = bmCap R n u (bmE R n k l G) := by
  exact bmE_comm_apply (bmK_central R n k l u) G
end Formalism.BranchingDeterminantCap
