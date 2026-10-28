-- Prove2me | solution 1 for AvramDividend.Classical.chat08_levy_upcrossing_event_measurable_at_time
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-24T07:28:15.080034+00:00
-- url     : https://prove2.me/submissions/95dff245-deae-45fc-881d-dd345abadc6c

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

open MeasureTheory AvramDividend.Classical
open scoped NNReal ENNReal
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {ℱ : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P ℱ) (s : ℝ≥0) (a : ℝ) :
    MeasurableSet[ℱ s] {ω | a < X.X s ω} :=
  (X.adapted s) measurableSet_Ioi
