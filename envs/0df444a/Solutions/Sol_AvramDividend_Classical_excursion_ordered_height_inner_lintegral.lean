-- Prove2me | solution 1 for AvramDividend.Classical.excursion_ordered_height_inner_lintegral
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-08T08:05:34.643893+00:00
-- url     : https://prove2.me/submissions/0d7bd985-e018-4c68-b172-9eb85987f8ce

import Mathlib

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped ENNReal

theorem solution
    (z : ℝ) (w : ℝ → ℝ≥0∞) (hw : Measurable w)
    (g : ℝ≥0∞) :
    (∫⁻ t : ℝ, (if 0 < t ∧ t < z then w t * g else 0) ∂volume) =
      g * (∫⁻ t in Ioo (0 : ℝ) z, w t ∂volume) := by
  have hfunc :
      (fun t : ℝ => if 0 < t ∧ t < z then w t * g else 0) =
        (Ioo (0 : ℝ) z).indicator (fun t : ℝ => w t * g) := by
    funext t
    by_cases ht : 0 < t ∧ t < z
    · simp [Set.indicator, ht]
    · simp [Set.indicator, ht]
  rw [hfunc, lintegral_indicator measurableSet_Ioo]
  rw [lintegral_mul_const g hw]
  exact mul_comm _ _
