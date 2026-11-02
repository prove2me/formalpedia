-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave6_02_bounded_measurable_scalar_preserves_real_MemLp_two
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-01T22:37:30.787739+00:00
-- url     : https://prove2.me/submissions/aa5d7aad-b7b9-43e8-bcf3-1c0a19988b3c

import Mathlib
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory
open scoped ENNReal

theorem solution
    {α : Type*} [MeasurableSpace α]
    (μ : Measure α) (f a : α → ℝ)
    (hf : MemLp f (2 : ℝ≥0∞) μ)
    (hfm : Measurable f) (ham : Measurable a)
    (haBound : ∀ p, |a p| ≤ (1 : ℝ)) :
    MemLp (fun p => a p * f p) (2 : ℝ≥0∞) μ := by
  apply MemLp.mono hf ((ham.mul hfm).aestronglyMeasurable)
  filter_upwards [] with p
  calc
    ‖a p * f p‖ = |a p| * |f p| := by simp [Real.norm_eq_abs, abs_mul]
    _ ≤ 1 * |f p| := mul_le_mul_of_nonneg_right (haBound p) (abs_nonneg _)
    _ = ‖f p‖ := by simp [Real.norm_eq_abs]
