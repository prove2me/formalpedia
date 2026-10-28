-- Prove2me | solution 1 for AvramDividend.Classical.chat08_levy_detection_at_time_or_infinity_stopping
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-24T09:16:57.300993+00:00
-- url     : https://prove2.me/submissions/0e1674c6-fea3-4246-85ee-0421eb3496f4

import Theorems.Thm_AvramDividend_Classical_chat08_measurable_detection_time_or_infinity_is_stopping
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Mathlib.MeasureTheory.MeasurableSpace.Defs

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory AvramDividend.Classical
open scoped NNReal ENNReal
attribute [local instance] Classical.propDecidable

/-! A single sampled Lévy threshold detection is a stopping time, with no-hit infinity. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {ℱ : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P ℱ) (s : ℝ≥0) (a : ℝ) :
    IsStoppingTime ℱ
      (fun ω => if a < X.X s ω then (s : WithTop ℝ≥0) else ⊤) := by
  have hA : MeasurableSet[ℱ s] {ω | a < X.X s ω} :=
    measurableSet_lt measurable_const (X.adapted s)
  simpa only [Set.mem_setOf_eq] using
    (chat08_measurable_detection_time_or_infinity_is_stopping
      ℱ s {ω | a < X.X s ω} hA)
