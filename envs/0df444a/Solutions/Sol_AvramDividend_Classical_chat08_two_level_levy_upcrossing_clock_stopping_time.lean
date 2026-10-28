-- Prove2me | solution 1 for AvramDividend.Classical.chat08_two_level_levy_upcrossing_clock_stopping_time
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-24T08:33:08.198302+00:00
-- url     : https://prove2.me/submissions/77de3523-1699-47a0-887f-e4d29106f5cc

import Theorems.Thm_AvramDividend_Classical_chat08_two_level_measurable_event_stopping_time
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Mathlib.MeasureTheory.MeasurableSpace.Defs

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory AvramDividend.Classical
open scoped NNReal ENNReal
attribute [local instance] Classical.propDecidable

/-! An adapted Lévy threshold decision is a finite-valued stopping clock. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {ℱ : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P ℱ)
    (s t : ℝ≥0) (hst : s ≤ t) (a : ℝ) :
    IsStoppingTime ℱ
      (fun ω => if a < X.X s ω then (s : WithTop ℝ≥0)
        else (t : WithTop ℝ≥0)) := by
  have hA : MeasurableSet[ℱ s] {ω | a < X.X s ω} :=
    measurableSet_lt measurable_const (X.adapted s)
  simpa only [Set.mem_setOf_eq] using
    (chat08_two_level_measurable_event_stopping_time
      ℱ s t hst {ω | a < X.X s ω} hA)
