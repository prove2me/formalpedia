-- Prove2me | solution 1 for AvramDividend.Classical.avram_bvb_phys93_negative_mark_closed_cap_compensator_double_integral_nonpos
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-11T10:23:56.408031+00:00
-- url     : https://prove2.me/submissions/1a35fe12-48da-4a8f-9043-6fe50086ec2f

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_bvb_phys91_negative_mark_closed_cap_compensator_double_integral_nonpos

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal Topology
attribute [local instance] Classical.propDecidable

/-- Instantiates the Proved mark/time double-integral sign theorem
with the original target's ordering of the two measure arguments. -/
theorem solution
    (C : ℝ≥0∞) (hC : 0 < C)
    (w : ℝ → ℝ) (hw_cont : ContinuousOn w (Ici 0))
    (hw0 : 0 ≤ w 0) (hw_neg : ∀ y < 0, w y = 0)
    (hw_smooth : ContDiffOn ℝ 1 w
      {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hw_grad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      1 ≤ deriv w y)
    (μ : Measure ℝ≥0) (ν : Measure ℝ)
    (U : ℝ≥0 → ℝ) (e : ℝ≥0 → ℝ) (A : Set ℝ≥0)
    (he : ∀ t, 0 ≤ e t)
    (hU : ∀ t ∈ A, 0 ≤ U t ∧ ENNReal.ofReal (U t) ≤ C) :
    (∫ t, ∫ z,
      (if t ∈ A ∧ z < 0 then
        e t * (w (U t + z) - w (U t)) else 0) ∂ν ∂μ) ≤ 0 := by
  exact avram_bvb_phys91_negative_mark_closed_cap_compensator_double_integral_nonpos
    C hC w hw_cont hw0 hw_neg hw_smooth hw_grad ν μ U e A he hU
