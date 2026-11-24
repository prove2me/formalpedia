-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.levelInequalityOfSteps
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:01:34.865421+00:00
-- url     : https://prove2.me/submissions/3dc6c172-caae-401d-b64c-1ff2a6b3d4de

import Definitions.Def_Formalism_HermitianCurvature_StatementTB
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_OneLevelCoefficients
import Theorems.Thm_Formalism_FourierDecayAlt_P_OneLevelCoefficients_oneLevel_of_steps

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
namespace Formalism.FourierDecayAlt.P
theorem _root_.solution : Formalism.FourierDecayAlt.TB.OneLevelOfSteps := OneLevelCoefficients.oneLevel_of_steps
end Formalism.FourierDecayAlt.P
