-- Prove2me | solution 2 for AvramDividend.Classical.barrierRuinTime_stopping_rightCont_filtration
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-25T21:48:46.097121+00:00
-- url     : https://prove2.me/submissions/025c8a3e-931e-4357-851a-e507306515a6

import Mathlib.Probability.Process.Stopping
import Theorems.Thm_AvramDividend_Classical_barrierRuinTime_eq_ruinTime_runningSup
import Theorems.Thm_AvramDividend_Classical_runningSup_isDividendStrategy
import Theorems.Thm_AvramDividend_Classical_ruinTime_stopping_rightCont_filtration

open AvramDividend.Classical MeasureTheory
open scoped NNReal ENNReal

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (a : ℝ) :
    IsStoppingTime 𝓕.rightCont (barrierRuinTime X a) := by
  rw [barrierRuinTime_eq_ruinTime_runningSup]
  exact ruinTime_stopping_rightCont_filtration X a _ (runningSup_isDividendStrategy X)