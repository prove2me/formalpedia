-- Prove2me | solution 1 for Formalism.BranchingDeterminantCap.bmK_bmZ
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:42:23.509794+00:00
-- url     : https://prove2.me/submissions/753f6efe-f9f6-47c4-9979-0c99e66cbaea

import Mathlib
import Definitions.Def_Formalism_GradedWeylDivisibility_FinalC
import Definitions.Def_Formalism_BranchSandwichDivisors_StatementW
import Definitions.Def_Formalism_BranchSandwichDivisors_BranchIsometryProofs_MemBranchRangeOfDefectEq
import Definitions.Def_Formalism_BranchSandwichDivisors_BranchIsometryProofs_BranchMap
import Theorems.Thm_Formalism_BranchingDeterminantCap_bmZL_comm_bmEL
import Theorems.Thm_Formalism_BranchingDeterminantCap_capDet_commute_of
import Theorems.Thm_Formalism_BranchingDeterminantCap_bmE_comm_apply

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
theorem _root_.solution (R : Type*) [CommRing R] (n : ℕ) (k l : Fin n) (u : ℤ) (G : BP R n) :
    bmZ R n k l (bmCap R n u G) = bmCap R n u (bmZ R n k l G) := by
  exact bmE_comm_apply (capDet_commute_of (bmEL R n) u (bmZL R n k l) (fun i j => bmZL_comm_bmEL R n k l i j)) G
end Formalism.BranchingDeterminantCap
