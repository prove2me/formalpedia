-- Prove2me | solution 1 for AvramDividend.Classical.barrierStrategy_dividendMeasure_map_shift_of_support
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-25T18:53:41.018319+00:00
-- url     : https://prove2.me/submissions/cd429cb4-1ac9-4663-bc85-24af4ea77066

import Mathlib.MeasureTheory.Measure.Map
import Theorems.Thm_AvramDividend_Classical_barrierStrategy_shifted_runningSup_dividendMeasure_Ioc_unconditional
import Theorems.Thm_AvramDividend_Classical_barrierStrategy_dividendMeasure_zero_through_firstUpcrossing
import Theorems.Thm_AvramDividend_Classical_measure_Iic_zero_of_zero_nonpositive_and_initial_window
import Theorems.Thm_AvramDividend_Classical_measure_eq_translated_of_zero_prepayment_and_cumulative

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x a : ℝ) (hx0 : 0 ≤ x) (hxa : x ≤ a)
    (ω : Ω) (u : ℝ≥0)
    (hu : (u : ℝ≥0∞) =
      (⨅ (s : ℝ≥0) (_ : a - x < X.X s ω), (s : ℝ≥0∞)))
    [IsLocallyFiniteMeasure (dividendMeasure (barrierStrategy X x a) ω)]
    (hμneg : (dividendMeasure (barrierStrategy X x a) ω)
      (Set.Iic (0 : ℝ)) = 0)
    (hνneg : (dividendMeasure
      (fun r _ =>
        sSup ((fun v : ℝ≥0 => X.X (u + v) ω - X.X u ω) '' Set.Icc 0 r))
      ω) (Set.Iic (0 : ℝ)) = 0) :
    dividendMeasure (barrierStrategy X x a) ω =
      Measure.map (fun t : ℝ => (u : ℝ) + t)
        (dividendMeasure
          (fun r _ =>
            sSup ((fun v : ℝ≥0 => X.X (u + v) ω - X.X u ω) '' Set.Icc 0 r))
          ω) := by
  refine AvramDividend.Classical.measure_eq_translated_of_zero_prepayment_and_cumulative _ _ _
    (AvramDividend.Classical.measure_Iic_zero_of_zero_nonpositive_and_initial_window _ _ hμneg
      (AvramDividend.Classical.barrierStrategy_dividendMeasure_zero_through_firstUpcrossing
        X x a hx0 hxa ω u hu)) hνneg ?_
  intro t ht
  have h := AvramDividend.Classical.barrierStrategy_shifted_runningSup_dividendMeasure_Ioc_unconditional
    X x a hxa ω u hu ⟨t, ht⟩
  exact h
