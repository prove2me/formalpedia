-- Prove2me | solution 1 for Formalism.ZeroFreeDirichlet.perron_right_line_bound
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T11:45:24.24562+00:00
-- url     : https://prove2.me/submissions/01c7c1d2-f069-41d3-93c9-9630335926ec

import Definitions.Def_Formalism_LandauZeroFreeBounds_LogDerivRegionChiOf
import Definitions.Def_Formalism_LandauZeroFreeBounds_ExceptionalZeroBounds_PerronHorizontalSegmentBound
import Theorems.Thm_Formalism_ZeroFreeDirichlet_norm_perron_integrand_eq

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
open Formalism Formalism.ZeroFreeDirichlet
namespace Formalism.ZeroFreeDirichlet
theorem _root_.solution {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (C₀ : ℝ)
    (hR : ∀ s : ℂ, 1 < s.re → ‖negLD χ s‖ ≤ 1 / (s.re - 1) + C₀)
    (y T t : ℝ) (hy : 1 < y) (hT : 0 < T) (ht : T ≤ |t|) :
    ‖Fchi χ y (((1 + 1 / Real.log y : ℝ) : ℂ) + t * I)‖ ≤
      (Real.log y + C₀) * (Real.exp 1 * y) / t ^ 2 := by
  have hL0 : 0 < Real.log y := Real.log_pos hy
  have hy0 : 0 < y := by linarith
  set L := Real.log y with hL
  set w : ℂ := ((1 + 1 / L : ℝ) : ℂ) + t * I with hw
  have hwre : w.re = 1 + 1 / L := by simp [hw]
  have hwim : w.im = t := by simp [hw]
  have ht0 : 0 < |t| := lt_of_lt_of_le hT ht
  rw [norm_perron_integrand_eq χ y hy0 w, hwre]
  have hN : ‖negLD χ w‖ ≤ L + C₀ := by
    have hpos : 0 < 1 / L := by positivity
    have h1 := hR w (by rw [hwre]; linarith)
    rw [hwre] at h1
    simpa [one_div, inv_inv] using h1
  have hpow : y ^ (1 + 1 / L) = Real.exp 1 * y := by
    rw [Real.rpow_def_of_pos hy0, ← hL, mul_add, mul_one, mul_one_div_cancel hL0.ne',
      Real.exp_add, Real.exp_log hy0]
    ring
  have hw1 : |t| ≤ ‖w‖ := by rw [← hwim]; exact Complex.abs_im_le_norm w
  have hw2 : |t| ≤ ‖w - 1‖ := by
    have h2 : (w - 1).im = t := by simp [hwim]
    rw [← h2]; exact Complex.abs_im_le_norm _
  rw [hpow]
  have htt : t ^ 2 ≤ ‖w‖ * ‖w - 1‖ := by
    rw [← sq_abs]; nlinarith [abs_nonneg t]
  have htt0 : 0 < t ^ 2 := by rw [← sq_abs]; positivity
  have hNn : 0 ≤ L + C₀ := le_trans (norm_nonneg _) hN
  have hey : 0 < Real.exp 1 * y := by positivity
  calc ‖negLD χ w‖ * (Real.exp 1 * y) / (‖w‖ * ‖w - 1‖)
      ≤ (L + C₀) * (Real.exp 1 * y) / (‖w‖ * ‖w - 1‖) :=
        div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hN hey.le) (by positivity)
    _ ≤ (L + C₀) * (Real.exp 1 * y) / t ^ 2 :=
        div_le_div_of_nonneg_left (mul_nonneg hNn hey.le) htt0 htt
end Formalism.ZeroFreeDirichlet
