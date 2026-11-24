-- Prove2me | solution 1 for Formalism.L2.Th1.F.sigma_summable
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T10:53:03.169279+00:00
-- url     : https://prove2.me/submissions/31816738-746c-4471-a2ee-5f1a9fc2b759

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_Legendre
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_AnalyticIdentityTheorems_SigmaConv
import Theorems.Thm_Formalism_L2_Th1_F_SigmaConv_norm_wFactor_sub_one_le
import Theorems.Thm_Formalism_L2_Th1_F_SigmaConv_summable_majorant
import Theorems.Thm_Formalism_L2_Th1_F_SigmaConv_eventually_large

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators ComplexConjugate
open Filter
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.F
open SigmaConv
namespace Formalism.L2.Th1.F
theorem _root_.solution : SigmaSummable := by
  intro L z
  refine Summable.of_norm_bounded_eventually (summable_majorant L ‖z‖) ?_
  filter_upwards [eventually_large L (2 * ‖z‖)] with l hl
  rw [norm_norm]
  exact norm_wFactor_sub_one_le ‖z‖ l z le_rfl hl
end Formalism.L2.Th1.F
