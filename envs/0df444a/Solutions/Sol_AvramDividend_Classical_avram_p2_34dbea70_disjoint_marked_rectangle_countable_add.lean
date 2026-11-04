-- Prove2me | solution 1 for AvramDividend.Classical.avram_p2_34dbea70_disjoint_marked_rectangle_countable_add
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T15:15:52.968902+00:00
-- url     : https://prove2.me/submissions/0979366a-a7d2-494d-82ce-5d2674244b4c

import Mathlib

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped ENNReal NNReal

/-- Countable disjoint Borel mark rectangles are additive for any source measure. -/
theorem solution (μ : Measure (ℝ≥0 × ℝ)) (T : ℝ≥0)
    (B : ℕ → Set ℝ) (hB : ∀ n, MeasurableSet (B n))
    (hDisj : Pairwise (Function.onFun Disjoint B)) :
    μ (Ioc 0 T ×ˢ (⋃ n, B n)) =
      ∑' n, μ (Ioc 0 T ×ˢ B n) := by
  have hrectDisj : Pairwise
      (Function.onFun Disjoint (fun n : ℕ => Ioc (0 : ℝ≥0) T ×ˢ B n)) := by
    intro m n hmn
    apply Set.disjoint_left.mpr
    intro p hp hp'
    exact Set.disjoint_left.mp (hDisj hmn) hp.2 hp'.2
  have hmeas (n : ℕ) : MeasurableSet (Ioc (0 : ℝ≥0) T ×ˢ B n) :=
    measurableSet_Ioc.prod (hB n)
  simpa only [Set.prod_iUnion] using
    (measure_iUnion hrectDisj hmeas)
