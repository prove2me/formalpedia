-- Prove2me | solution 1 for Formalism.L2.Th1.F.Hk1.norm_hk_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T21:58:06.682564+00:00
-- url     : https://prove2.me/submissions/be84c49e-72bc-4b0b-b005-a23345109f2a

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_HkRowIntegral
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_AnalyticIdentityTheorems_HeckeKernelIntegralValue
import Theorems.Thm_Formalism_L2_Th1_F_Hk1_norm_hk

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
open MeasureTheory Filter Topology
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.F
open Formalism.L2.Th1.F.Hk1
namespace Formalism.L2.Th1.F.Hk1
theorem _root_.solution (s : ℝ) (w : ℂ) : ‖hk s w‖ ≤ ‖w‖ ^ (-(2 + 2 * s)) := by
  by_cases hw : w = 0
  · subst hw
    simp only [hk]
    simp
    exact Real.rpow_nonneg le_rfl _
  · exact (norm_hk s w hw).le
end Formalism.L2.Th1.F.Hk1
