-- Prove2me | solution 1 for AvramDividend.Classical.avram_p3_2_original_marked_count_nonlinear_lintegral_eq_tsum
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-05T08:51:32.801902+00:00
-- url     : https://prove2.me/submissions/f2a3cb85-f94d-4043-80b9-3d312a52b7b6

import Mathlib.MeasureTheory.Integral.Lebesgue.Map
import Mathlib.MeasureTheory.Integral.Lebesgue.Countable
import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.Count

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal BigOperators Classical

/-- Exact marked-count integral of a nonlinear nonnegative jump kernel,
with a genuinely measurable original time-mark map. -/
theorem solution
    (S : Set ℝ≥0) (hS : MeasurableSet S)
    (mark : ℝ≥0 → ℝ≥0 × ℝ) (hmark : Measurable mark)
    (F : ℝ≥0 × ℝ → ℝ≥0∞) (hF : Measurable F) :
    (∫⁻ p, F p ∂((Measure.count.restrict S).map mark)) =
      ∑' u : ℝ≥0, if u ∈ S then F (mark u) else 0 := by
  rw [lintegral_map hF hmark]
  rw [← lintegral_indicator hS]
  rw [lintegral_count]
  apply tsum_congr
  intro u
  by_cases hu : u ∈ S
  · simp [Set.indicator, hu]
  · simp [Set.indicator, hu]
