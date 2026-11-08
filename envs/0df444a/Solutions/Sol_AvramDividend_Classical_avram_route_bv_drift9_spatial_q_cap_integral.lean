-- Prove2me | solution 1 for AvramDividend.Classical.avram_route_bv_drift9_spatial_q_cap_integral
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-07T10:09:06.630869+00:00
-- url     : https://prove2.me/submissions/c53b7ea0-81aa-4277-9e24-26a0dea13782

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave3_03_bv_full_cap_gradient_secant
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section
theorem solution
    (C : ℝ≥0∞) (hC : 0 < C) (w : ℝ → ℝ)
    (hw_cont : ContinuousOn w (Ici 0))
    (hw_smooth : ContDiffOn ℝ 1 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hw_grad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C → 1 ≤ deriv w y)
    (ε : ℝ) (hε : 0 < ε) (hεC : ENNReal.ofReal ε < C)
    (q : ℝ) (hq : 0 ≤ q) :
    (∫ y in Ioc (0 : ℝ) ε, q * w y ∂(volume : Measure ℝ)) ≤ q * ε * w ε := by
  have hmon : MonotoneOn w (Icc (0 : ℝ) ε) := by
    intro a ha b hb hab
    have hbc : ENNReal.ofReal b ≤ C := (ENNReal.ofReal_mono hb.2).trans hεC.le
    have hsec := avram_wave3_03_bv_full_cap_gradient_secant C hC w hw_cont
      hw_smooth hw_grad a b ha.1 hab hbc
    linarith
  have hsubset : uIcc (0 : ℝ) ε ⊆ Ici 0 := by
    intro y hy
    exact (show y ∈ Icc (0 : ℝ) ε by simpa [uIcc_of_le hε.le] using hy).1
  have hcont : ContinuousOn (fun y : ℝ => q * w y) (uIcc 0 ε) :=
    continuousOn_const.mul (hw_cont.mono hsubset)
  have hint : IntervalIntegrable (fun y : ℝ => q * w y) volume 0 ε :=
    hcont.intervalIntegrable
  have hbound : ∀ y ∈ Icc (0 : ℝ) ε, q * w y ≤ q * w ε := by
    intro y hy
    exact mul_le_mul_of_nonneg_left
      (hmon hy ⟨hε.le, le_refl _⟩ hy.2) hq
  have hmono := intervalIntegral.integral_mono_on hε.le hint
    intervalIntegrable_const hbound
  rw [← intervalIntegral.integral_of_le hε.le]
  calc
    _ ≤ ∫ y in (0 : ℝ)..ε, (q * w ε) := hmono
    _ = q * ε * w ε := by simp [intervalIntegral.integral_const]; ring
