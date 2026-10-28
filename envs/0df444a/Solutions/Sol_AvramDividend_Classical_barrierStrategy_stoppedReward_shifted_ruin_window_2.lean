-- Prove2me | solution 2 for AvramDividend.Classical.barrierStrategy_stoppedReward_shifted_ruin_window
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-26T23:34:47.956839+00:00
-- url     : https://prove2.me/submissions/5b8aadef-f8c9-4995-b1f7-ffadbc986b24

import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Theorems.Thm_AvramDividend_Classical_barrierStrategy_stoppedReward_postUpcrossing_shifted_window_of_levy
import Theorems.Thm_AvramDividend_Classical_barrierStrategy_ruinTime_post_firstUpcrossing_add_shifted_badClock
import Theorems.Thm_AvramDividend_Classical_translated_payment_window_eq_shifted_ruin_window
open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x a : ℝ) (hx0 : 0 ≤ x) (hxa : x ≤ a)
    (q : ℝ) (ω : Ω) (u : ℝ≥0)
    (hu : (u : ℝ≥0∞) =
      (⨅ (s : ℝ≥0) (_ : a - x < X.X s ω), (s : ℝ≥0∞)))
    (hsuccess : (u : ℝ≥0∞) <
      ruinTime X x (barrierStrategy X x a) ω) :
    (∫⁻ t in paymentTimes (ruinTime X x (barrierStrategy X x a) ω),
      ENNReal.ofReal (Real.exp (-(q * t)))
      ∂dividendMeasure (barrierStrategy X x a) ω) =
    ENNReal.ofReal (Real.exp (-(q * (u : ℝ)))) *
      (∫⁻ t in (Set.Ioi (0 : ℝ)) ∩
        paymentTimes (⨅ (r : ℝ≥0)
          (_ : a + (X.X (u + r) ω - X.X u ω) <
            max 0
              (sSup ((fun z : ℝ≥0 => X.X (u + z) ω) '' Set.Icc 0 r) -
                X.X u ω)), (r : ℝ≥0∞)),
        ENNReal.ofReal (Real.exp (-(q * t)))
        ∂(dividendMeasure
          (fun r (_ : Ω) =>
            sSup ((fun v : ℝ≥0 => X.X (u + v) ω - X.X u ω) '' Set.Icc 0 r))
          ω)) := by
  rw [barrierStrategy_stoppedReward_postUpcrossing_shifted_window_of_levy X x a hx0 hxa q ω u hu]
  congr 2
  rw [barrierStrategy_ruinTime_post_firstUpcrossing_add_shifted_badClock X x a hxa ω u hu hsuccess,
    translated_payment_window_eq_shifted_ruin_window]
