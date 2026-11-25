-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.PW.Top.weylInt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T03:06:30.02975+00:00
-- url     : https://prove2.me/submissions/fb830865-53ac-4df3-a6bc-ad2c06bd4de6

import Definitions.Def_Formalism_ThetaLogCoordinates_TraceIsometryWeights_FinalP
import Definitions.Def_Formalism_ThetaLogCoordinates_TraceIsometryWeights_SchurTraceProofs_WeylInt
import Definitions.Def_Formalism_ThetaLogCoordinates_TraceIsometryWeights_SchurTraceProofs_ZpClosedToAddSubgroup
import Definitions.Def_Formalism_ThetaLogCoordinates_TraceIsometryWeights_SchurTraceProofs_CompEqZeroOfNotDle
import Definitions.Def_Formalism_ThetaLogCoordinates_TraceIsometryWeights_DischargeHeightBound
import Theorems.Thm_Formalism_InvariantFactorPaths_PW_weyl_integral_holds


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
theorem _root_.solution : WeylInt := weyl_integral_holds
end Formalism.InvariantFactorPaths.PW.Top
