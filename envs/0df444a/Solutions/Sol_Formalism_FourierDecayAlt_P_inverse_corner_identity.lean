-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.inverse_corner_identity
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T16:47:27.297046+00:00
-- url     : https://prove2.me/submissions/3c4a960a-1ff8-4893-af7a-e4036efef670

import Definitions.Def_Formalism_HermitianCurvature_MemParahoricTimesPrincipalCongruenceIff
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LduDecompositionExists
import Theorems.Thm_Formalism_FourierDecayAlt_P_S3x7_inverse_corner

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
open Formalism.FourierDecayAlt.P.S3x7
namespace Formalism.FourierDecayAlt.P
theorem _root_.solution : Formalism.FourierDecayAlt.S3.InverseCorner := by
  intro o _ _ _ ϖ hϖ r k j X hj hX
  exact inverse_corner hϖ j X hj hX
end Formalism.FourierDecayAlt.P
