-- Prove2me | solution 1 for AvramDividend.Classical.runningSup_dividendMeasure_zero_through_first_positive_record
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-25T18:02:34.895399+00:00
-- url     : https://prove2.me/submissions/23b52ee1-6710-4109-89d8-e027387a5577

import Mathlib.MeasureTheory.Measure.Restrict
import Theorems.Thm_AvramDividend_Classical_barrierStrategy_dividendMeasure_zero_until_firstUpcrossing
import Theorems.Thm_AvramDividend_Classical_barrierStrategy_self_eq_runningSup

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (a : ℝ) (ha : 0 ≤ a)
    (ω : Ω) (u : ℝ≥0)
    (hu : (u : ℝ≥0∞) =
      (⨅ (s : ℝ≥0) (_ : (0 : ℝ) < X.X s ω), (s : ℝ≥0∞))) :
    (dividendMeasure (runningSup X) ω)
      (Set.Ioc (0 : ℝ) (u : ℝ)) = 0 := by
  have hraw :=
    barrierStrategy_dividendMeasure_zero_until_firstUpcrossing
      X a a ha (le_refl a) ω u (by simpa only [sub_self] using hu)
  have heq : barrierStrategy X a a = runningSup X := by
    funext t ω'
    exact barrierStrategy_self_eq_runningSup X a ω' t
  simpa only [heq] using hraw
