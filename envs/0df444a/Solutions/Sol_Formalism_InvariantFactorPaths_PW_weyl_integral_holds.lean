-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.PW.weyl_integral_holds
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T10:51:20.746263+00:00
-- url     : https://prove2.me/submissions/502eeeb8-61d5-4c72-b466-f6f4f1738ba8

import Definitions.Def_Formalism_ThetaLogCoordinates_TraceIsometryWeights_SchurTraceProofs_SchurTraceOfHomInv
import Definitions.Def_Formalism_ThetaLogCoordinates_TraceIsometryWeights_SchurTraceProofs_InvInv
import Definitions.Def_Formalism_ThetaLogCoordinates_TraceIsometryWeights_SchurTraceProofs_InvInt
import Definitions.Def_Formalism_ThetaLogCoordinates_TraceIsometryWeights_SchurTraceProofs_WeylInt
import Theorems.Thm_Formalism_InvariantFactorPaths_PW_weylInt_of
import Theorems.Thm_Formalism_InvariantFactorPaths_PW_invariant_inverse_holds
import Theorems.Thm_Formalism_InvariantFactorPaths_PW_invariant_natural_holds
import Theorems.Thm_Formalism_InvariantFactorPaths_PW_schurTrace_of


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.InvariantFactorPaths Formalism.InvariantFactorPaths.PW
open Finset Formalism.GM.DimensionMonotonicity Formalism.CountingSumsFrames
namespace Formalism.InvariantFactorPaths.PW
theorem _root_.solution : WeylInt := weylInt_of invariant_natural_holds (schurTrace_of invariant_inverse_holds)
end Formalism.InvariantFactorPaths.PW
