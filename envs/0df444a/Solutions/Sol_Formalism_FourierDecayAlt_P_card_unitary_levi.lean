-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.card_unitary_levi
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T16:40:23.871929+00:00
-- url     : https://prove2.me/submissions/cc1aa68b-6f04-4f3d-bf59-4d27b2ba1266

import Definitions.Def_Formalism_HermitianCurvature_MemParahoricTimesPrincipalCongruenceIff
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PointwiseStabiliserParametrisationBijective
import Theorems.Thm_Formalism_FourierDecayAlt_P_S3x1_card_uni

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
theorem _root_.solution : Formalism.FourierDecayAlt.S3.CardUk := by
  intro K _ _ k
  rw [Nat.card_congr (upUniGEquiv k), card_uni]
end Formalism.FourierDecayAlt.P
