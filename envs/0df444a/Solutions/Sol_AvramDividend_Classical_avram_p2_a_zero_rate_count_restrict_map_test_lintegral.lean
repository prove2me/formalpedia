-- Prove2me | solution 1 for AvramDividend.Classical.avram_p2_a_zero_rate_count_restrict_map_test_lintegral
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-04T00:00:38.189133+00:00
-- url     : https://prove2.me/submissions/7f35af1c-26c0-4f45-84b8-2d8828737ebf

import Mathlib.MeasureTheory.Integral.Lebesgue.Map
import Mathlib.MeasureTheory.Integral.Lebesgue.Countable
import Mathlib.MeasureTheory.Integral.Lebesgue.Basic

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory
open scoped ENNReal

/-- The actual restricted counting-measure push-forward integrates any
measurable nonnegative mark test as the marked jump sum. -/
theorem solution
    {α : Type*} [MeasurableSpace α] [MeasurableSingletonClass α]
    {β : Type*} [MeasurableSpace β]
    (J : Set α) (hJ : MeasurableSet J)
    (j : α → β) (hj : Measurable j)
    (g : β → ℝ≥0∞) (hg : Measurable g) :
    (∫⁻ y, g y ∂((Measure.count.restrict J).map j)) =
      ∑' x : α, J.indicator (fun y => g (j y)) x := by
  classical
  calc
    _ = ∫⁻ x, g (j x) ∂(Measure.count.restrict J) :=
      lintegral_map hg hj
    _ = ∫⁻ x, J.indicator (fun y => g (j y)) x ∂(Measure.count : Measure α) :=
      (lintegral_indicator hJ (fun y => g (j y))).symm
    _ = ∑' x : α, J.indicator (fun y => g (j y)) x :=
      lintegral_count _
