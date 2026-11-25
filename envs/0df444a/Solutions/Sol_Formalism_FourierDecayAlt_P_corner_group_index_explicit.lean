-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.corner_group_index_explicit
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T16:44:09.220161+00:00
-- url     : https://prove2.me/submissions/fea58b8c-c012-4677-af83-8042a86622df

import Definitions.Def_Formalism_HermitianCurvature_MemParahoricTimesPrincipalCongruenceIff
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PointwiseStabiliserParametrisationBijective
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_OrderIndexAndStrata
import Theorems.Thm_Formalism_FourierDecayAlt_P_OrderIndexAndStrata_kppCorner
import Theorems.Thm_Formalism_FourierDecayAlt_P_S3x1_isNU_iff


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
theorem _root_.solution : Formalism.FourierDecayAlt.S3.KppCorner :=
  Formalism.FourierDecayAlt.P.OrderIndexAndStrata.kppCorner (fun A _ r k x => Formalism.FourierDecayAlt.P.S3x1.isNU_iff x)
end Formalism.FourierDecayAlt.P
