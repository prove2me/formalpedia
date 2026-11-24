-- Prove2me | solution 1 for Formalism.L2.Th1.F.Hk2.hk_diff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T22:01:54.651798+00:00
-- url     : https://prove2.me/submissions/d9e21628-d42a-4b11-a18e-ec7816a57faf

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_HkRowIntegral
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_AnalyticIdentityTheorems_HeckeKernelCellContinuous
import Theorems.Thm_Formalism_L2_Th1_F_Hk2_rpow_bd
import Theorems.Thm_Formalism_L2_Th1_F_Hk2_rpow_diff
import Theorems.Thm_Formalism_L2_Th1_F_Hk2_inv_sq_diff

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
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.F
open Formalism.L2.Th1.F.Hk2
namespace Formalism.L2.Th1.F.Hk2
theorem _root_.solution {κ ρ s : ℝ} {w w' : ℂ} (hκ : 0 < κ) (hκ1 : κ ≤ 1) (hρ : κ ≤ ρ) (hw : ρ ≤ ‖w‖)
    (hw' : ρ ≤ ‖w'‖) (hd : ‖w - w'‖ ≤ 1) (hs0 : 0 ≤ s) (hs1 : s ≤ 1) :
    ‖hk s w - hk s w'‖ ≤ 4 * (κ ^ 2)⁻¹ * (ρ ^ 3)⁻¹ := by
  have hρ0 : 0 < ρ := lt_of_lt_of_le hκ hρ
  have e : hk s w - hk s w' = ((w ^ 2)⁻¹ - (w' ^ 2)⁻¹) * ((‖w‖ ^ (-(2 * s)) : ℝ) : ℂ)
      + (w' ^ 2)⁻¹ * ((‖w‖ ^ (-(2 * s)) - ‖w'‖ ^ (-(2 * s)) : ℝ) : ℂ) := by
    unfold hk
    push_cast
    ring
  have a1 : ‖(w ^ 2)⁻¹ - (w' ^ 2)⁻¹‖ ≤ 2 * (ρ ^ 3)⁻¹ := by
    refine (inv_sq_diff hρ0 hw hw').trans ?_
    have : 0 ≤ 2 * (ρ ^ 3)⁻¹ := by positivity
    nlinarith
  have a2 : ‖((‖w‖ ^ (-(2 * s)) : ℝ) : ℂ)‖ ≤ (κ ^ 2)⁻¹ := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (norm_nonneg _) _)]
    exact rpow_bd hκ hκ1 (hρ.trans hw) (by linarith) (by linarith)
  have a3 : ‖(w' ^ 2)⁻¹‖ ≤ (ρ ^ 2)⁻¹ := by
    rw [norm_inv, norm_pow]
    exact inv_anti₀ (by positivity) (by gcongr)
  have a4 : ‖((‖w‖ ^ (-(2 * s)) - ‖w'‖ ^ (-(2 * s)) : ℝ) : ℂ)‖ ≤ 2 * (κ ^ 2)⁻¹ * ρ⁻¹ := by
    rw [Complex.norm_real, Real.norm_eq_abs]
    refine (rpow_diff hκ hκ1 hρ hw hw' (by linarith) (by linarith)).trans ?_
    have h1 : |‖w‖ - ‖w'‖| ≤ 1 := (abs_norm_sub_norm_le w w').trans hd
    have : 0 ≤ 2 * (κ ^ 2)⁻¹ * ρ⁻¹ := by positivity
    nlinarith
  rw [e]
  calc _ ≤ ‖((w ^ 2)⁻¹ - (w' ^ 2)⁻¹) * ((‖w‖ ^ (-(2 * s)) : ℝ) : ℂ)‖
        + ‖(w' ^ 2)⁻¹ * ((‖w‖ ^ (-(2 * s)) - ‖w'‖ ^ (-(2 * s)) : ℝ) : ℂ)‖ := norm_add_le _ _
    _ ≤ 2 * (ρ ^ 3)⁻¹ * (κ ^ 2)⁻¹ + (ρ ^ 2)⁻¹ * (2 * (κ ^ 2)⁻¹ * ρ⁻¹) := by
        rw [norm_mul, norm_mul]
        gcongr
    _ = 4 * (κ ^ 2)⁻¹ * (ρ ^ 3)⁻¹ := by
        field_simp
        ring
end Formalism.L2.Th1.F.Hk2
