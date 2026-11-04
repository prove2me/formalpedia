-- Prove2me | solution 1 for AvramDividend.Classical.avram_p2_34dbea70_increasing_borel_mark_rectangle_measure_iUnion
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T15:03:41.704558+00:00
-- url     : https://prove2.me/submissions/dc43c9c7-13e3-4697-bad5-d23d24f3742a

import Mathlib

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped ENNReal NNReal

/-- An increasing family of marked rectangles converges in measure. -/
theorem solution (μ : Measure (ℝ≥0 × ℝ)) (T : ℝ≥0)
    (B : ℕ → Set ℝ) (hB : Monotone B) :
    μ (Ioc 0 T ×ˢ (⋃ n, B n)) =
      ⨆ n, μ (Ioc 0 T ×ˢ B n) := by
  have hrect : Monotone (fun n : ℕ => Ioc (0 : ℝ≥0) T ×ˢ B n) := by
    intro m n hmn
    exact Set.prod_mono (Subset.rfl) (hB hmn)
  simpa only [Set.prod_iUnion] using (hrect.measure_iUnion (μ := μ))
