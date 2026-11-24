-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.PW.diag_comm
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T08:49:33.388805+00:00
-- url     : https://prove2.me/submissions/28fe1d84-370a-4a0a-8bfe-dcb404f556a9

import Definitions.Def_Formalism_ThetaLogCoordinates_TraceIsometryWeights_StatementA
import Definitions.Def_Formalism_ThetaLogCoordinates_TraceIsometryWeights_SchurTraceProofs_InvInv
import Theorems.Thm_Formalism_InvariantFactorPaths_PW_GlRel_sw

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.InvariantFactorPaths Formalism.InvariantFactorPaths.PW
open Finset
variable {K W ι : Type} [Field K] [AddCommGroup W] [Module K W] [DecidableEq ι]
variable {E : ι → ι → Module.End K W}
namespace Formalism.InvariantFactorPaths.PW
theorem _root_.solution (h : GlRel E) {a b c : ι} (ha : a ≠ c) (hb : b ≠ c) : E c c * E a b = E a b * E c c := by
  rw [h.sw c c a b, if_neg (Ne.symm ha), if_neg hb, sub_zero, add_zero]
end Formalism.InvariantFactorPaths.PW
