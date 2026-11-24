-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.PW.schurTrace_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T09:26:00.181779+00:00
-- url     : https://prove2.me/submissions/c3020dcc-cb6c-497c-bc8c-077beff471be

import Definitions.Def_Formalism_ThetaLogCoordinates_TraceIsometryWeights_StatementB
import Definitions.Def_Formalism_ThetaLogCoordinates_TraceIsometryWeights_SchurTraceProofs_HomRelationHolds
import Definitions.Def_Formalism_ThetaLogCoordinates_TraceIsometryWeights_SchurTraceProofs_SchurTraceOfHomInv
import Theorems.Thm_Formalism_InvariantFactorPaths_PW_homInv_of
import Theorems.Thm_Formalism_InvariantFactorPaths_PW_schurTrace_of_homInv

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.InvariantFactorPaths Formalism.InvariantFactorPaths.PW
open Finset Formalism.GM.DimensionMonotonicity
namespace Formalism.InvariantFactorPaths.PW
theorem _root_.solution (h1 : InvInv) : SchurTrace := schurTrace_of_homInv (homInv_of h1)
end Formalism.InvariantFactorPaths.PW
