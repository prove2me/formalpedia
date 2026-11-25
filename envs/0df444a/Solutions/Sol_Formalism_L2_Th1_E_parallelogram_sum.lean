-- Prove2me | solution 1 for Formalism.L2.Th1.E.parallelogram_sum
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T17:28:03.592139+00:00
-- url     : https://prove2.me/submissions/7ff3088c-1247-4ccb-97e9-356b8b5f86b6

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_TorsionTranslationPowers_StatementT
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_TorsionTranslationPowers_NonsingularJetNorms_ScaledXEqOffOrigin
import Theorems.Thm_Formalism_L2_Th1_E_Power_sum_zero

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PowerSeries
noncomputable section
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.E
namespace Formalism.L2.Th1.E
theorem _root_.solution : ParSum := by
  intro A _ _ M h Q hQ
  exact Power.sum_zero M Q (M Q) fun P => h P Q hQ
end Formalism.L2.Th1.E
