-- Prove2me | solution 1 for AvramDividend.Classical.avram_bvb_phys131_original_stopped_compensator_double_integral_nonpos
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-11T12:58:35.623363+00:00
-- url     : https://prove2.me/submissions/d5e6bb0e-3f67-4c84-b5cf-f0b3bf9eceae

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_bvb_phys128_original_stopped_compensator_negative_mark_kernel_nonpos
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem solution
    (C : ℝ≥0∞) (hC : 0 < C) (w : ℝ → ℝ)
    (hw_cont : ContinuousOn w (Ici 0)) (hw0 : 0 ≤ w 0)
    (hw_neg : ∀ y < 0, w y = 0)
    (hw_smooth : ContDiffOn ℝ 1 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hw_grad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C → 1 ≤ deriv w y)
    (q T : ℝ) (b : ℝ≥0 → ℝ) (τ : ℝ≥0 → ℝ≥0∞)
    (μ : Measure ℝ≥0) (ν : Measure ℝ) :
    (∫ t, ∫ z,
      (if 0 < t ∧ (t : ℝ) < T ∧ (t : ℝ≥0∞) ≤ τ t ∧
          0 ≤ b t ∧ ENNReal.ofReal (b t) ≤ C ∧ z < 0 then
        Real.exp (-(q * (t : ℝ))) * (w (b t + z) - w (b t))
       else 0) ∂ν ∂μ) ≤ 0 := by
  apply integral_nonpos
  intro t
  apply integral_nonpos
  intro z
  exact
    avram_bvb_phys128_original_stopped_compensator_negative_mark_kernel_nonpos
      C hC w hw_cont hw0 hw_neg hw_smooth hw_grad
      q T t (b t) z (τ t)
