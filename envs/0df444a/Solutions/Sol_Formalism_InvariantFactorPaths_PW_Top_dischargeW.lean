-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.PW.Top.dischargeW
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T04:06:40.604879+00:00
-- url     : https://prove2.me/submissions/fb77712f-bae9-42d7-bf8d-9f1cc4ab7d9b

import Definitions.Def_Formalism_ThetaLogCoordinates_TraceIsometryWeights_FinalP
import Definitions.Def_Formalism_ThetaLogCoordinates_TraceIsometryWeights_SchurTraceProofs_WeylInt
import Definitions.Def_Formalism_ThetaLogCoordinates_TraceIsometryWeights_SchurTraceProofs_ZpClosedToAddSubgroup
import Definitions.Def_Formalism_ThetaLogCoordinates_TraceIsometryWeights_SchurTraceProofs_CompEqZeroOfNotDle
import Definitions.Def_Formalism_ThetaLogCoordinates_TraceIsometryWeights_DischargeHeightBound
import Theorems.Thm_Formalism_InvariantFactorPaths_PW_Top_weylP
import Theorems.Thm_Formalism_InvariantFactorPaths_PW_dischargeW_of


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
theorem _root_.solution : DischargeW := dischargeW_of weylP
end Formalism.InvariantFactorPaths.PW.Top
