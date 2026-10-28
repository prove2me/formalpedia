-- Prove2me | solution 1 for AvramDividend.Classical.barrierRuinTime_stopping_rightCont_filtration
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-25T21:48:35.298795+00:00
-- url     : https://prove2.me/submissions/3655c294-10a6-4651-b0dc-40fee7469763

import Mathlib.Probability.Process.Stopping
import Theorems.Thm_AvramDividend_Classical_barrierRuinTime_eq_ruinTime_runningSup
import Theorems.Thm_AvramDividend_Classical_runningSup_isDividendStrategy
import Theorems.Thm_AvramDividend_Classical_ruinTime_stopping_rightCont_filtration

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory
open scoped NNReal ENNReal

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (a : ℝ) :
    IsStoppingTime 𝓕.rightCont (barrierRuinTime X a) := by
  rw [barrierRuinTime_eq_ruinTime_runningSup X a]
  exact ruinTime_stopping_rightCont_filtration X a (runningSup X)
    (runningSup_isDividendStrategy X)
