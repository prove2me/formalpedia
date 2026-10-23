-- Prove2me | solution 1 for AvramDividend.Classical.gaussian_double_tail_real_kernel_zero_nonpositive
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-22T12:31:41.387985+00:00
-- url     : https://prove2.me/submissions/308d0d26-74b6-4e08-8e87-a9b640bab4be

import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Mathlib.Analysis.Complex.Exponential
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped ENNReal

theorem solution (μ : Measure ℝ) (φ t : ℝ) (ht : t ≤ 0) :
    (∫⁻ z : ℝ,
      (if 0 < t ∧ t < z then
        ENNReal.ofReal (z - t) *
          ENNReal.ofReal (Real.exp (-(φ * z))) else 0) ∂μ).toReal = 0 := by
  have hnot : ¬ (0 < t) := not_lt.mpr ht
  simp [hnot]
