-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.PW.Top.dischargeE
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T04:06:56.988098+00:00
-- url     : https://prove2.me/submissions/bbb5511c-550c-46d5-aad1-2fd3598eae19

import Definitions.Def_Formalism_ThetaLogCoordinates_TraceIsometryWeights_FinalP
import Definitions.Def_Formalism_ThetaLogCoordinates_TraceIsometryWeights_SchurTraceProofs_WeylInt
import Definitions.Def_Formalism_ThetaLogCoordinates_TraceIsometryWeights_SchurTraceProofs_ZpClosedToAddSubgroup
import Definitions.Def_Formalism_ThetaLogCoordinates_TraceIsometryWeights_SchurTraceProofs_CompEqZeroOfNotDle
import Definitions.Def_Formalism_ThetaLogCoordinates_TraceIsometryWeights_DischargeHeightBound
import Theorems.Thm_Formalism_InvariantFactorPaths_PW_Top_extP
import Theorems.Thm_Formalism_InvariantFactorPaths_PW_dischargeE_of


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.InvariantFactorPaths Formalism.InvariantFactorPaths.PW Formalism.InvariantFactorPaths.PW.Top
namespace Formalism.InvariantFactorPaths.PW.Top
theorem _root_.solution : DischargeE := dischargeE_of extP
end Formalism.InvariantFactorPaths.PW.Top
