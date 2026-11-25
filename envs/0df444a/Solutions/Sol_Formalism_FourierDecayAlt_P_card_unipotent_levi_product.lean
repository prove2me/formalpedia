-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.card_unipotent_levi_product
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T16:40:19.647346+00:00
-- url     : https://prove2.me/submissions/e2f66cc3-06bc-4f5f-9389-2843d538baef

import Definitions.Def_Formalism_HermitianCurvature_MemParahoricTimesPrincipalCongruenceIff
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PointwiseStabiliserParametrisationBijective
import Theorems.Thm_Formalism_FourierDecayAlt_P_S3x1_card_isN
import Theorems.Thm_Formalism_FourierDecayAlt_P_S3x1_card_isNU

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
theorem _root_.solution : Formalism.FourierDecayAlt.S3.CardNU := by
  intro K _ _ r k
  rw [card_isNU, card_isN, Nat.card_congr (upUniGEquiv k), mul_comm]
end Formalism.FourierDecayAlt.P
