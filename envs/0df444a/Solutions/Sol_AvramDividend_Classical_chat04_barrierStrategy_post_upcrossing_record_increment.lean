-- Prove2me | solution 1 for AvramDividend.Classical.chat04_barrierStrategy_post_upcrossing_record_increment
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-23T12:07:54.620316+00:00
-- url     : https://prove2.me/submissions/dbeaa3e7-02ba-41df-beef-1968eb339d68

import Mathlib.Order.ConditionallyCompleteLattice.Indexed
import Theorems.Thm_AvramDividend_Classical_firstUpcrossing_attains_peak
import Theorems.Thm_AvramDividend_Classical_barrierStrategy_after_firstUpcrossing_shift
import Theorems.Thm_AvramDividend_Classical_runningSup_excess_after_peak
import Theorems.Thm_AvramDividend_Classical_runningSup_eq_rawSup_nonneg

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

/-- After a first attained barrier crossing, dividends equal new record increments. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x a : ℝ) (hxa : x ≤ a) (u t : ℝ≥0) (ω : Ω)
    (hu : (u : ℝ≥0∞) =
      (⨅ (s : ℝ≥0) (_ : a - x < X.X s ω), (s : ℝ≥0∞)))
    (hb : BddAbove ((fun r : ℝ≥0 => X.X r ω) '' Set.Icc 0 (u + t))) :
    barrierStrategy X x a (u + t) ω =
      runningSup X (u + t) ω - runningSup X u ω := by
  have hpeak :=
    (firstUpcrossing_attains_peak X (a - x) (sub_nonneg.mpr hxa) ω u hu).2
  have hrecord :=
    runningSup_excess_after_peak (fun r : ℝ≥0 => X.X r ω) u t hb hpeak
  have hpost :=
    barrierStrategy_after_firstUpcrossing_shift X x a hxa u t ω hu hb
  calc
    barrierStrategy X x a (u + t) ω =
        max 0
          (sSup ((fun r : ℝ≥0 => X.X (u + r) ω) '' Set.Icc 0 t) -
            X.X u ω) := hpost
    _ = sSup ((fun r : ℝ≥0 => X.X r ω) '' Set.Icc 0 (u + t)) -
        X.X u ω := hrecord.symm
    _ = runningSup X (u + t) ω - runningSup X u ω := by
      rw [(runningSup_eq_rawSup_nonneg X (u + t) ω).1]
      rw [(runningSup_eq_rawSup_nonneg X u ω).1]
      have hpeakIndex : (⨆ r : Set.Icc (0 : ℝ≥0) u, X.X r.1 ω) = X.X u ω := by
        simpa only [sSup_image'] using hpeak
      rw [hpeakIndex]
      simp only [sSup_image']
