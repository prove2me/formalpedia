-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.c7_letter_product_degree_count
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T16:45:11.786155+00:00
-- url     : https://prove2.me/submissions/20085ece-db09-44a2-8d1f-d21785283c81

import Definitions.Def_Formalism_HermitianCurvature_LetterProductDoubleDegreeCount
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AdditiveCharacterPsi
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ThresholdExponentEstimate

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.FourierDecayAlt
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
namespace Formalism.FourierDecayAlt.P
theorem _root_.solution : C7.LetterProductDegreeCount := by
  intro k r N d D hk h1 h2; unfold C7.Dstar C7.Nprime C7.nOf at *
  constructor <;> nlinarith
end Formalism.FourierDecayAlt.P
