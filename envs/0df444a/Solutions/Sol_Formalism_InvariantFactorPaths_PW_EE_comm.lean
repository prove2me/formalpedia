-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.PW.EE_comm
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T22:45:44.670811+00:00
-- url     : https://prove2.me/submissions/a3d94dfa-102f-4cad-8e57-e3ab56bcdde6

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
theorem _root_.solution (h : GlRel E) {z i k : ι} (hi : i ≠ z) (hk : k ≠ z) : E i z * E k z = E k z * E i z := by
  rw [h.sw i z k z, if_neg (Ne.symm hk), if_neg (Ne.symm hi), sub_zero, add_zero]
end Formalism.InvariantFactorPaths.PW
