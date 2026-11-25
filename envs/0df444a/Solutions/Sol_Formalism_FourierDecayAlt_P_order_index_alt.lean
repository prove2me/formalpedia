-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.order_index_alt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T16:54:07.997336+00:00
-- url     : https://prove2.me/submissions/ed94d2fe-ba52-4b0f-8096-3e4ed27598f9

import Definitions.Def_Formalism_HermitianCurvature_MemParahoricTimesPrincipalCongruenceIff
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PointwiseStabiliserParametrisationBijective
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_OrderIndexAndStrata
import Theorems.Thm_Formalism_FourierDecayAlt_P_OrderIndexAndStrata_rOrderIndex

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
theorem _root_.solution : Formalism.FourierDecayAlt.S3.ROrderIndex :=
  Formalism.FourierDecayAlt.P.OrderIndexAndStrata.rOrderIndex
end Formalism.FourierDecayAlt.P
