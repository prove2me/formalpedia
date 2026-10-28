-- Prove2me | solution 1 for AvramDividend.Classical.runningSup_dividendMeasure_Ioc_eq_drift_of_linear_record
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-26T00:07:25.946132+00:00
-- url     : https://prove2.me/submissions/b85454cb-f195-41c6-8b4f-5b12e0a125ca

import Theorems.Thm_AvramDividend_Classical_runningSup_dividendMeasure_Ioc_eq_linear_drift
import Theorems.Thm_AvramDividend_Classical_runningSup_realTime_rightLim_eq
open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (ω : Ω) (s t : ℝ)
    (hs : runningSup X s.toNNReal ω = X.drift * s)
    (ht : runningSup X t.toNNReal ω = X.drift * t) :
    (dividendMeasure (runningSup X) ω) (Ioc s t) =
      ENNReal.ofReal (X.drift * (t - s)) := by 
  exact runningSup_dividendMeasure_Ioc_eq_linear_drift X ω s t
    (by rw [runningSup_realTime_rightLim_eq]; exact hs)
    (by rw [runningSup_realTime_rightLim_eq]; exact ht)
