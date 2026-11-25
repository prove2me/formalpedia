-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.frame_stabiliser_characterisation
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T16:42:04.239897+00:00
-- url     : https://prove2.me/submissions/4fae8e8b-c572-4d72-9992-e039964ae363

import Definitions.Def_Formalism_HermitianCurvature_MemParahoricTimesPrincipalCongruenceIff
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PointwiseStabiliserParametrisationBijective
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_OrderIndexAndStrata
import Theorems.Thm_Formalism_FourierDecayAlt_P_OrderIndexAndStrata_sFrame

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option linter.unusedVariables false
namespace Formalism.FourierDecayAlt.P
theorem _root_.solution : Formalism.FourierDecayAlt.S3.SIsFrameStabiliser :=
  Formalism.FourierDecayAlt.P.OrderIndexAndStrata.sFrame (fun A _ r k x => Formalism.FourierDecayAlt.P.S3x1.isS_iff x)
end Formalism.FourierDecayAlt.P
