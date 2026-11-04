-- Prove2me | solution 1 for AvramDividend.Classical.avram_p2_34dbea70_marked_rectangle_disjoint_mark_add
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T14:46:05.798219+00:00
-- url     : https://prove2.me/submissions/04e82e2d-f7bd-41cb-9097-46558fca6590

import Mathlib

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped ENNReal NNReal

/-- The same marked rectangle splits its measure over disjoint Borel marks. -/
theorem solution (μ : Measure (ℝ≥0 × ℝ)) (T : ℝ≥0)
    (B C : Set ℝ) (hB : MeasurableSet B) (hC : MeasurableSet C)
    (hBC : Disjoint B C) :
    μ (Ioc 0 T ×ˢ (B ∪ C)) =
      μ (Ioc 0 T ×ˢ B) + μ (Ioc 0 T ×ˢ C) := by
  have hdisj : Disjoint (Ioc (0 : ℝ≥0) T ×ˢ B) (Ioc 0 T ×ˢ C) := by
    apply Set.disjoint_left.mpr
    intro p hpB hpC
    exact Set.disjoint_left.mp hBC hpB.2 hpC.2
  have hmeasC : MeasurableSet (Ioc (0 : ℝ≥0) T ×ˢ C) :=
    measurableSet_Ioc.prod hC
  simpa only [Set.prod_union] using (measure_union hdisj hmeasC)
