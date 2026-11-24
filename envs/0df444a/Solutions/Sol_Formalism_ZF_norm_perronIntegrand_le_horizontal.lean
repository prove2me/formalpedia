-- Prove2me | solution 1 for Formalism.ZF.norm_perronIntegrand_le_horizontal
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T11:42:11.479295+00:00
-- url     : https://prove2.me/submissions/521b1567-3b0e-433d-9e8f-015dee526263

import Definitions.Def_Formalism_ZeroFreeRegion_SmallHeightLogDeriv
import Definitions.Def_Formalism_ZeroFreeRegion_ZetaLogDerivativeBounds_RiemannZetaNeZeroOfMemRectangle
import Theorems.Thm_Formalism_ZF_norm_perronIntegrand
import Theorems.Thm_Formalism_ZF_one_sub_div_log_le

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
theorem _root_.solution (c₁ C₁ : ℝ) (hC₁ : 0 ≤ C₁)
    (hD : ∀ s : ℂ, s ≠ 1 → 1 - c₁ / Real.log (|s.im| + 2) ≤ s.re →
      ‖deriv riemannZeta s / riemannZeta s + 1 / (s - 1)‖ ≤ C₁ * Real.log (|s.im| + 2) ^ 2)
    (c y T x v σ₀ : ℝ) (hc : 0 < c) (hcc : c ≤ c₁) (hy : 1 ≤ y) (hT : 1 ≤ T) (hv : |v| = T)
    (hx1 : 1 - c / Real.log (T + 2) ≤ x) (hx2 : x ≤ σ₀) :
    ‖Fy y ((x : ℂ) + (v : ℂ) * I)‖ ≤
      (C₁ * Real.log (T + 2) ^ 2 + 1) * y ^ σ₀ / T ^ 2 := by
  set w : ℂ := (x : ℂ) + (v : ℂ) * I with hw
  have hre : w.re = x := by simp [hw]
  have him : w.im = v := by simp [hw]
  have hy0 : 0 < y := by linarith
  rw [norm_perronIntegrand y hy0 w]
  have hw1 : T ≤ ‖w‖ := by rw [← hv, ← him]; exact Complex.abs_im_le_norm w
  have hw2 : T ≤ ‖w - 1‖ := by
    have : (w - 1).im = v := by simp [him]
    rw [← hv, ← this]; exact Complex.abs_im_le_norm _
  have hne : w ≠ 1 := by
    intro h
    have : (w - 1) = 0 := by rw [h]; ring
    rw [this, norm_zero] at hw2; linarith
  have hreg : 1 - c₁ / Real.log (|w.im| + 2) ≤ w.re := by
    rw [hre]
    exact (one_sub_div_log_le c c₁ T w.im hc hcc (by linarith) (by rw [him, hv])).trans hx1
  have hD' := hD w hne hreg
  rw [him, hv] at hD'
  have hinv : ‖1 / (w - 1)‖ ≤ 1 := by
    rw [norm_div, norm_one]
    exact (div_le_one (by linarith)).mpr (by linarith)
  have hζ : ‖deriv riemannZeta w / riemannZeta w‖ ≤ C₁ * Real.log (T + 2) ^ 2 + 1 := by
    calc ‖deriv riemannZeta w / riemannZeta w‖
        = ‖(deriv riemannZeta w / riemannZeta w + 1 / (w - 1)) - 1 / (w - 1)‖ := by ring_nf
      _ ≤ ‖deriv riemannZeta w / riemannZeta w + 1 / (w - 1)‖ + ‖1 / (w - 1)‖ := norm_sub_le _ _
      _ ≤ C₁ * Real.log (T + 2) ^ 2 + 1 := add_le_add hD' hinv
  have hpow : y ^ w.re ≤ y ^ σ₀ := by
    rw [hre]; exact Real.rpow_le_rpow_of_exponent_le hy hx2
  have hden : T ^ 2 ≤ ‖w‖ * ‖w - 1‖ := by nlinarith
  have htp : 0 < T ^ 2 := by positivity
  calc ‖deriv riemannZeta w / riemannZeta w‖ * y ^ w.re / (‖w‖ * ‖w - 1‖)
      ≤ (C₁ * Real.log (T + 2) ^ 2 + 1) * y ^ σ₀ / (‖w‖ * ‖w - 1‖) := by
        gcongr
    _ ≤ (C₁ * Real.log (T + 2) ^ 2 + 1) * y ^ σ₀ / T ^ 2 := by
        apply div_le_div_of_nonneg_left (by positivity) htp hden
end Formalism.ZF
