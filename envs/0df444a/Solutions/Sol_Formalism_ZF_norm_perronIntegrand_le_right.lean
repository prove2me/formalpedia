-- Prove2me | solution 1 for Formalism.ZF.norm_perronIntegrand_le_right
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T11:42:13.567064+00:00
-- url     : https://prove2.me/submissions/680e5402-17da-47ae-a485-cf3d9cd22e45

import Definitions.Def_Formalism_ZeroFreeRegion_SmallHeightLogDeriv
import Definitions.Def_Formalism_ZeroFreeRegion_ZetaLogDerivativeBounds_RiemannZetaNeZeroOfMemRectangle
import Theorems.Thm_Formalism_ZF_norm_perronIntegrand

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex MeasureTheory
noncomputable section
open Formalism Formalism.ZF
namespace Formalism.ZF
theorem _root_.solution (C₂ : ℝ)
    (hR : ∀ s : ℂ, 1 < s.re → ‖deriv riemannZeta s / riemannZeta s‖ ≤ 1 / (s.re - 1) + C₂)
    (y T t : ℝ) (hy : 1 < y) (hT : 0 < T) (ht : T ≤ |t|) :
    ‖Fy y (((1 + 1 / Real.log y : ℝ) : ℂ) + t * I)‖ ≤
      (Real.log y + C₂) * (Real.exp 1 * y) / t ^ 2 := by
  set w : ℂ := ((1 + 1 / Real.log y : ℝ) : ℂ) + t * I with hw
  have hl : 0 < Real.log y := Real.log_pos hy
  have hre : w.re = 1 + 1 / Real.log y := by simp [hw]
  have him : w.im = t := by simp [hw]
  have hy0 : 0 < y := by linarith
  rw [norm_perronIntegrand y hy0 w]
  have hζ : ‖deriv riemannZeta w / riemannZeta w‖ ≤ Real.log y + C₂ := by
    have := hR w (by rw [hre]; have := one_div_pos.mpr hl; linarith)
    rw [hre] at this
    simpa using this
  have hpow : y ^ w.re = Real.exp 1 * y := by
    rw [hre, Real.rpow_add hy0, Real.rpow_one, Real.rpow_def_of_pos hy0,
      mul_one_div_cancel hl.ne']
    ring
  have ht0 : 0 < |t| := lt_of_lt_of_le hT ht
  have hw1 : |t| ≤ ‖w‖ := by rw [← him]; exact Complex.abs_im_le_norm w
  have hw2 : |t| ≤ ‖w - 1‖ := by
    have : (w - 1).im = t := by simp [him]
    rw [← this]; exact Complex.abs_im_le_norm _
  have hden : t ^ 2 ≤ ‖w‖ * ‖w - 1‖ := by
    rw [← sq_abs]; nlinarith [abs_nonneg t]
  have hnum : 0 ≤ Real.log y + C₂ := le_trans (norm_nonneg _) hζ
  rw [hpow]
  have htp : 0 < t ^ 2 := by rw [← sq_abs]; exact pow_pos ht0 2
  calc ‖deriv riemannZeta w / riemannZeta w‖ * (Real.exp 1 * y) / (‖w‖ * ‖w - 1‖)
      ≤ (Real.log y + C₂) * (Real.exp 1 * y) / (‖w‖ * ‖w - 1‖) := by
        gcongr
    _ ≤ (Real.log y + C₂) * (Real.exp 1 * y) / t ^ 2 := by
        apply div_le_div_of_nonneg_left (mul_nonneg hnum (by positivity)) htp hden
end Formalism.ZF
