-- Prove2me | solution 1 for AvramDividend.Classical.barrierStrategy_zeroPayoff_if_rawLowerExitBeforeUpper
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-25T18:38:19.922018+00:00
-- url     : https://prove2.me/submissions/8d2f8323-31af-4a11-af11-933cb5b0e70e

import Theorems.Thm_AvramDividend_Classical_barrierStrategy_ruinClock_lt_upClock_iff_rawLowerClock_lt
import Theorems.Thm_AvramDividend_Classical_barrierStrategy_discountedDividend_zero_if_ruin_before_upcrossing

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q x a : ℝ) (hx0 : 0 ≤ x) (hxa : x ≤ a)
    (ω : Ω) (u : ℝ≥0)
    (hu : (u : ℝ≥0∞) =
      (⨅ (s : ℝ≥0) (_ : a - x < X.X s ω), (s : ℝ≥0∞)))
    (hraw : (⨅ (s : ℝ≥0) (_ : X.X s ω < -x),
      (s : ℝ≥0∞)) < (u : ℝ≥0∞)) :
    (∫⁻ t in paymentTimes
        (ruinTime X x (barrierStrategy X x a) ω),
      ENNReal.ofReal (Real.exp (-(q * t)))
      ∂(dividendMeasure (barrierStrategy X x a) ω)) = 0 := by
  exact AvramDividend.Classical.barrierStrategy_discountedDividend_zero_if_ruin_before_upcrossing
    X q x a hx0 hxa ω u hu
    (((AvramDividend.Classical.barrierStrategy_ruinClock_lt_upClock_iff_rawLowerClock_lt
      X x a ω u hu).2 hraw).le)
