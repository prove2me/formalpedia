-- Prove2me | solution 1 for AvramDividend.Classical.runningSup_dividendMeasure_Ioc_eq_drift_before_time
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-26T00:12:36.983996+00:00
-- url     : https://prove2.me/submissions/07700917-54a7-4a61-88bf-3803d94b8353

import Theorems.Thm_AvramDividend_Classical_runningSup_dividendMeasure_Ioc_eq_drift_of_linear_record
open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (ω : Ω) (T s t : ℝ)
    (hPath : ∀ u : ℝ, 0 ≤ u → u ≤ T →
      runningSup X u.toNNReal ω = X.drift * u)
    (hs : 0 ≤ s) (hst : s ≤ t) (ht : t ≤ T) :
    (dividendMeasure (runningSup X) ω) (Ioc s t) =
      ENNReal.ofReal (X.drift * (t - s)) := by 
  exact runningSup_dividendMeasure_Ioc_eq_drift_of_linear_record X ω s t
    (hPath s hs (hst.trans ht)) (hPath t (hs.trans hst) ht)
