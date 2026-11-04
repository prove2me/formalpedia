-- Prove2me | solution 1 for AvramDividend.Classical.avram_p2_f_weighted_indicator_lintegral_scalar_count
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T13:29:16.810181+00:00
-- url     : https://prove2.me/submissions/8e619ba4-69c6-49f1-a461-347813137462

import Mathlib

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped ENNReal

/-- The nonnegative indicator of a measurable marked cell integrates to its
exact mass times the weight, including zero and infinite values. -/
theorem solution
    {α : Type*} [MeasurableSpace α]
    (μ : Measure α) (S : Set α)
    (hS : MeasurableSet S) (c : ℝ≥0∞) :
    (∫⁻ x, S.indicator (fun _ => c) x ∂μ) = c * μ S := by
  simp [lintegral_indicator hS, mul_comm]
