-- Prove2me | solution 1 for AvramDividend.Classical.barrierStrategy_preUpcrossing_stieltjesReward_zero
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-25T17:34:17.290514+00:00
-- url     : https://prove2.me/submissions/79a6c9be-3b19-403f-9e38-76ef516c9b74

import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Theorems.Thm_AvramDividend_Classical_barrierStrategy_dividendMeasure_zero_through_firstUpcrossing

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

/-- Every nonnegative Stieltjes reward vanishes up to first upper exit. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x a : ℝ) (hx0 : 0 ≤ x) (hxa : x ≤ a)
    (ω : Ω) (u : ℝ≥0)
    (hu : (u : ℝ≥0∞) =
      (⨅ (s : ℝ≥0) (_ : a - x < X.X s ω), (s : ℝ≥0∞)))
    (f : ℝ → ℝ≥0∞) :
    (∫⁻ t in Set.Icc (0 : ℝ) (u : ℝ), f t
      ∂(dividendMeasure (barrierStrategy X x a) ω)) = 0 := by
  exact setLIntegral_measure_zero _ f
    (barrierStrategy_dividendMeasure_zero_through_firstUpcrossing
      X x a hx0 hxa ω u hu)
