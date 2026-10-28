-- Prove2me | solution 1 for AvramDividend.Classical.barrierStrategy_dividendMeasure_map_shift_of_levy
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-26T22:57:07.971457+00:00
-- url     : https://prove2.me/submissions/ddd41991-0aea-45db-848e-a0f55c59d420

import Mathlib.MeasureTheory.Measure.Map
import Theorems.Thm_AvramDividend_Classical_dividendMeasure_locallyFinite
import Theorems.Thm_AvramDividend_Classical_barrierStrategy_dividendMeasure_zero_nonpositive
import Theorems.Thm_AvramDividend_Classical_shiftedSup_dividendMeasure_zero_nonpositive_of_levy
import Theorems.Thm_AvramDividend_Classical_barrierStrategy_dividendMeasure_map_shift_of_support
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x a : ℝ) (hx0 : 0 ≤ x) (hxa : x ≤ a)
    (ω : Ω) (u : ℝ≥0)
    (hu : (u : ℝ≥0∞) =
      (⨅ (s : ℝ≥0) (_ : a - x < X.X s ω), (s : ℝ≥0∞))) :
    dividendMeasure (barrierStrategy X x a) ω =
      Measure.map (fun t : ℝ => (u : ℝ) + t)
        (dividendMeasure
      (fun r (_ : Ω) =>
        sSup ((fun v : ℝ≥0 => X.X (u + v) ω - X.X u ω) '' Set.Icc 0 r))
      ω) := by
  classical
  letI : IsLocallyFiniteMeasure
      (dividendMeasure (barrierStrategy X x a) ω) :=
    dividendMeasure_locallyFinite (barrierStrategy X x a) ω
  apply barrierStrategy_dividendMeasure_map_shift_of_support
    X x a hx0 hxa ω u hu
  · exact barrierStrategy_dividendMeasure_zero_nonpositive
      X x a hx0 hxa ω
  · exact shiftedSup_dividendMeasure_zero_nonpositive_of_levy X ω u