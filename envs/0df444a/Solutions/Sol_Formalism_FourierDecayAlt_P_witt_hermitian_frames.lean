-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.witt_hermitian_frames
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T16:57:28.932425+00:00
-- url     : https://prove2.me/submissions/e72a917f-7af4-4e01-a439-f44a442723be

import Definitions.Def_Formalism_HermitianCurvature_MemParahoricTimesPrincipalCongruenceIff
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RestrictOrthogonalComplementNondeg
import Theorems.Thm_Formalism_FourierDecayAlt_P_S3x6_d_wittHerm

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
theorem _root_.solution : Formalism.FourierDecayAlt.S3.WittHerm := S3x6.d_wittHerm
end Formalism.FourierDecayAlt.P
