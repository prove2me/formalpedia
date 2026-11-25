-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.budget_sum_estimate
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T16:44:59.287616+00:00
-- url     : https://prove2.me/submissions/e996cea3-f957-4772-9a95-aaf96679746b

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
theorem _root_.solution : C7.BudgetSum := by
  intro r N' n d D h1 h2; unfold C7.B0; nlinarith
end Formalism.FourierDecayAlt.P
