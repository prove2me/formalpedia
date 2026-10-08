-- Prove2me | solution 1 for AvramDividend.Classical.excursion_ordered_tail_inner_lintegral
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-08T08:05:19.062979+00:00
-- url     : https://prove2.me/submissions/49899643-245b-4533-9fff-e9048f4258f9

import Mathlib

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped ENNReal

theorem solution
    (μ : Measure ℝ) (t : ℝ) (ht : 0 < t)
    (g : ℝ → ℝ≥0∞) (hg : Measurable g) (w : ℝ≥0∞) :
    (∫⁻ z : ℝ, (if 0 < t ∧ t < z then w * g z else 0) ∂μ) =
      w * (∫⁻ z in Ioi t, g z ∂μ) := by
  have hfunc :
      (fun z : ℝ => if 0 < t ∧ t < z then w * g z else 0) =
        (Ioi t).indicator (fun z : ℝ => w * g z) := by
    funext z
    by_cases hz : t < z
    · simp [Set.indicator, hz, ht]
    · simp [Set.indicator, hz, ht]
  rw [hfunc, lintegral_indicator measurableSet_Ioi]
  exact lintegral_const_mul w hg
