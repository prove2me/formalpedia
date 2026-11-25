-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.pointwise_stabiliser_characterisation
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T16:47:42.035909+00:00
-- url     : https://prove2.me/submissions/0bd8bb1b-5bac-44c8-8e83-2d3f75fcddff

import Definitions.Def_Formalism_HermitianCurvature_MemParahoricTimesPrincipalCongruenceIff
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PointwiseStabiliserParametrisationBijective
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_OrderIndexAndStrata
import Theorems.Thm_Formalism_FourierDecayAlt_P_OrderIndexAndStrata_pointwise_stabiliser_of_explicit

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
theorem _root_.solution : Formalism.FourierDecayAlt.S3.FrameStabiliserPointwise :=
  Formalism.FourierDecayAlt.P.OrderIndexAndStrata.pointwise_stabiliser_of_explicit (fun A _ r k x => Formalism.FourierDecayAlt.P.S3x1.isS_iff x)
end Formalism.FourierDecayAlt.P
