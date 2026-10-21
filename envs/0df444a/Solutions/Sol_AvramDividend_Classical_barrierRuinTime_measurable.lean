-- Prove2me | solution 1 for AvramDividend.Classical.barrierRuinTime_measurable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-20T06:18:42.921989+00:00
-- url     : https://prove2.me/submissions/9fe60e5e-2a83-41d8-ad9a-be16ead8f5bf

import Theorems.Thm_AvramDividend_Classical_runningSup_isDividendStrategy
import Theorems.Thm_AvramDividend_Classical_barrierRuinTime_eq_ruinTime_runningSup
import Theorems.Thm_AvramDividend_Classical_ruinTime_measurable
import Mathlib.MeasureTheory.MeasurableSpace.Defs

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (a : ℝ) :
    Measurable (barrierRuinTime X a) := by
  rw [barrierRuinTime_eq_ruinTime_runningSup X a]
  exact ruinTime_measurable X a (runningSup X)
    (runningSup_isDividendStrategy X)
