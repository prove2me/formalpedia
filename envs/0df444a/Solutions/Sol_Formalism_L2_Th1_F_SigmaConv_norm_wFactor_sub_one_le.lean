-- Prove2me | solution 1 for Formalism.L2.Th1.F.SigmaConv.norm_wFactor_sub_one_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T10:37:52.742481+00:00
-- url     : https://prove2.me/submissions/664044ee-aad6-4a05-bc6d-c37c3a7949f8

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_Legendre
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_AnalyticIdentityTheorems_SigmaConv
import Theorems.Thm_Formalism_L2_Th1_F_SigmaConv_norm_factor_sub_one_le
import Theorems.Thm_Formalism_L2_Th1_F_SigmaConv_wFactor_eq

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
open Formalism.L2.Th1.F.SigmaConv
namespace Formalism.L2.Th1.F.SigmaConv
theorem _root_.solution (r : ℝ) (l z : ℂ) (hz : ‖z‖ ≤ r) (hl : 2 * r ≤ ‖l‖) :
    ‖wFactor l z - 1‖ ≤ 2 * r ^ 3 * ‖l‖ ^ (-3 : ℝ) := by
  have hr : 0 ≤ r := (norm_nonneg z).trans hz
  have hrp : ‖l‖ ^ (-3 : ℝ) = (‖l‖ ^ 3)⁻¹ := by
    rw [Real.rpow_neg (norm_nonneg _)]
    norm_cast
  rcases eq_or_ne l 0 with rfl | hl0
  · have h1 : wFactor 0 z = 1 := by simp [wFactor]
    rw [h1, sub_self, norm_zero]
    exact mul_nonneg (mul_nonneg (by norm_num) (pow_nonneg hr 3)) (Real.rpow_nonneg le_rfl _)
  have hlpos : 0 < ‖l‖ := norm_pos_iff.mpr hl0
  have hw : ‖z / l‖ ≤ 1 / 2 := by
    rw [norm_div, div_le_iff₀ hlpos]
    linarith
  calc ‖wFactor l z - 1‖ ≤ 2 * ‖z / l‖ ^ 3 := by
        rw [wFactor_eq]
        exact norm_factor_sub_one_le _ hw
    _ = 2 * ‖z‖ ^ 3 * (‖l‖ ^ 3)⁻¹ := by rw [norm_div, div_pow]; ring
    _ ≤ 2 * r ^ 3 * (‖l‖ ^ 3)⁻¹ := by gcongr
    _ = 2 * r ^ 3 * ‖l‖ ^ (-3 : ℝ) := by rw [hrp]
end Formalism.L2.Th1.F.SigmaConv
