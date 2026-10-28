-- Prove2me | solution 1 for AvramDividend.Classical.barrierStrategy_stoppedReward_postUpcrossing_shifted_window_of_levy
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-26T23:06:14.918547+00:00
-- url     : https://prove2.me/submissions/f5682ecf-1cb4-442a-9d76-54215cbae54b

import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Theorems.Thm_AvramDividend_Classical_barrierStrategy_stoppedReward_postUpcrossing_shifted_window
import Theorems.Thm_AvramDividend_Classical_shiftedSup_dividendMeasure_zero_nonpositive_of_levy
import Mathlib.Analysis.Complex.Exponential
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
    (q : ℝ) (ω : Ω) (u : ℝ≥0)
    (hu : (u : ℝ≥0∞) =
      (⨅ (s : ℝ≥0) (_ : a - x < X.X s ω), (s : ℝ≥0∞))) :
    (∫⁻ t in paymentTimes (ruinTime X x (barrierStrategy X x a) ω),
      ENNReal.ofReal (Real.exp (-(q * t)))
      ∂dividendMeasure (barrierStrategy X x a) ω) =
    ENNReal.ofReal (Real.exp (-(q * (u : ℝ)))) *
      (∫⁻ t in (Set.Ioi (0 : ℝ)) ∩
        ((fun t : ℝ => (u : ℝ) + t) ⁻¹'
          paymentTimes (ruinTime X x (barrierStrategy X x a) ω)),
        ENNReal.ofReal (Real.exp (-(q * t)))
        ∂(dividendMeasure
          (fun r (_ : Ω) =>
            sSup ((fun v : ℝ≥0 => X.X (u + v) ω - X.X u ω) '' Set.Icc 0 r))
          ω)) := by
  exact barrierStrategy_stoppedReward_postUpcrossing_shifted_window
    X x a hx0 hxa q ω u hu
    (shiftedSup_dividendMeasure_zero_nonpositive_of_levy X ω u)
