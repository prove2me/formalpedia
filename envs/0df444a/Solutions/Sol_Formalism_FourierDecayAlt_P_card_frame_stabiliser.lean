-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.card_frame_stabiliser
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T21:59:13.185823+00:00
-- url     : https://prove2.me/submissions/0de96917-ce70-4de2-8c97-cee402027a48

import Definitions.Def_Formalism_HermitianCurvature_MemParahoricTimesPrincipalCongruenceIff
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PointwiseStabiliserParametrisationBijective
import Theorems.Thm_Formalism_FourierDecayAlt_P_S3x1_card_isN
import Theorems.Thm_Formalism_FourierDecayAlt_P_S3x1_card_isS

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
theorem _root_.solution : Formalism.FourierDecayAlt.S3.CardS := by
  intro K _ _ r k
  rw [card_isS, card_isN, Nat.card_congr (glEquiv k)]
end Formalism.FourierDecayAlt.P
