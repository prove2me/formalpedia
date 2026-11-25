-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.frame_stabiliser_explicit
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T16:43:45.504851+00:00
-- url     : https://prove2.me/submissions/642e8981-987b-4834-a97f-7e6f127fa774

import Definitions.Def_Formalism_HermitianCurvature_MemParahoricTimesPrincipalCongruenceIff
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PointwiseStabiliserParametrisationBijective

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
open Formalism.FourierDecayAlt.P.S3x1
namespace Formalism.FourierDecayAlt.P
theorem _root_.solution : Formalism.FourierDecayAlt.S3.SExplicit := by
  intro A _ r k x
  exact isS_iff x
end Formalism.FourierDecayAlt.P
