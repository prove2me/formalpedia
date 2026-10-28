-- Prove2me | solution 2 for AvramDividend.Classical.runningSup_dividendMeasure_Ioc_eq_drift_before_time
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-26T00:15:23.299409+00:00
-- url     : https://prove2.me/submissions/89f422d6-f1bd-45c4-af70-d40ba37fa0d2

import Theorems.Thm_AvramDividend_Classical_runningSup_dividendMeasure_Ioc_eq_drift_of_linear_record
import Mathlib.Data.ENNReal.Basic
import Mathlib.MeasureTheory.MeasurableSpace.Defs
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

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
  apply runningSup_dividendMeasure_Ioc_eq_drift_of_linear_record X ω s t
  · exact hPath s hs (le_trans hst ht)
  · exact hPath t (le_trans hs hst) ht
