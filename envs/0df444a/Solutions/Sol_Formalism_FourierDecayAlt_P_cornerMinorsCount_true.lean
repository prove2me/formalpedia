-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.cornerMinorsCount_true
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T16:44:04.056956+00:00
-- url     : https://prove2.me/submissions/78f9cef6-6689-4420-b7b2-85e046257228

import Definitions.Def_Formalism_HermitianCurvature_MemParahoricTimesPrincipalCongruenceIff
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_Minors
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_Block32EqZeroOfUnipotent
import Theorems.Thm_Formalism_FourierDecayAlt_P_S3x9_cornerCount

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

open Formalism.FourierDecayAlt.P.S3x9 Formalism.FourierDecayAlt.S3 Matrix
namespace Formalism.FourierDecayAlt.P
theorem _root_.solution : Formalism.FourierDecayAlt.S3.CornerMinorsCount :=
  fun K _ _ r => cornerCount K r
end Formalism.FourierDecayAlt.P
