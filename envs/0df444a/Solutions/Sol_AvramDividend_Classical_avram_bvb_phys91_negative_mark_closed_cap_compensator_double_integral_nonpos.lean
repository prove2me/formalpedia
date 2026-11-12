-- Prove2me | solution 1 for AvramDividend.Classical.avram_bvb_phys91_negative_mark_closed_cap_compensator_double_integral_nonpos
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-11T08:48:25.674444+00:00
-- url     : https://prove2.me/submissions/729f5dc8-68c4-4aec-a9d1-2f3874a3930f

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_bvb_phys88_original_closed_cap_negative_mark_value_increment_nonpos

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section
attribute [local instance] Classical.propDecidable

/-- Every nonnegative discounted weight of a negative-mark value increment
is nonpositive after both original mark and time integration. -/
theorem solution
    (C : ℝ≥0∞) (hC : 0 < C)
    (w : ℝ → ℝ) (hw_cont : ContinuousOn w (Ici 0))
    (hw0 : 0 ≤ w 0) (hw_neg : ∀ y < 0, w y = 0)
    (hw_smooth : ContDiffOn ℝ 1 w
      {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hw_grad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      1 ≤ deriv w y)
    (μ : Measure ℝ) (ν : Measure ℝ≥0)
    (U : ℝ≥0 → ℝ) (e : ℝ≥0 → ℝ) (A : Set ℝ≥0)
    (he : ∀ t, 0 ≤ e t)
    (hU : ∀ t ∈ A, 0 ≤ U t ∧ ENNReal.ofReal (U t) ≤ C) :
    (∫ t, ∫ z,
      (if t ∈ A ∧ z < 0 then
        e t * (w (U t + z) - w (U t)) else 0) ∂μ ∂ν) ≤ 0 := by
  classical
  apply integral_nonpos
  intro t
  apply integral_nonpos
  intro z
  by_cases h : t ∈ A ∧ z < 0
  · simp only [if_pos h]
    have hb := hU t h.1
    exact mul_nonpos_of_nonneg_of_nonpos (he t)
      (avram_bvb_phys88_original_closed_cap_negative_mark_value_increment_nonpos
        C hC w hw_cont hw0 hw_neg hw_smooth hw_grad
        (U t) z hb.1 hb.2 h.2)
  · simp [h]
