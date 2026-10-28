-- Prove2me | solution 1 for AvramDividend.Classical.barrierStrategy_stoppedReward_shifted_ruin_window
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-26T23:33:47.24476+00:00
-- url     : https://prove2.me/submissions/3fd126d6-2d2a-4660-9997-57504a1adb07

import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Theorems.Thm_AvramDividend_Classical_barrierStrategy_stoppedReward_postUpcrossing_shifted_window_of_levy
import Theorems.Thm_AvramDividend_Classical_barrierStrategy_ruinTime_post_firstUpcrossing_add_shifted_badClock
import Theorems.Thm_AvramDividend_Classical_translated_payment_window_eq_shifted_ruin_window
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
  classical
  let ρ : ℝ≥0∞ := (⨅ (r : ℝ≥0)
      (_ : a + (X.X (u + r) ω - X.X u ω) <
        max 0
          (sSup ((fun z : ℝ≥0 => X.X (u + z) ω) '' Set.Icc 0 r) -
            X.X u ω)), (r : ℝ≥0∞))
  have hclock :
      ruinTime X x (barrierStrategy X x a) ω =
        (u : ℝ≥0∞) + ρ := by
    exact barrierStrategy_ruinTime_post_firstUpcrossing_add_shifted_badClock
      X x a hxa ω u hu hsuccess
  calc
    (∫⁻ t in paymentTimes (ruinTime X x (barrierStrategy X x a) ω),
      ENNReal.ofReal (Real.exp (-(q * t)))
      ∂dividendMeasure (barrierStrategy X x a) ω) =
      ENNReal.ofReal (Real.exp (-(q * (u : ℝ)))) *
        (∫⁻ t in Set.Ioi (0 : ℝ) ∩
          ((fun t : ℝ => (u : ℝ) + t) ⁻¹'
            paymentTimes (ruinTime X x (barrierStrategy X x a) ω)),
          ENNReal.ofReal (Real.exp (-(q * t)))
          ∂(dividendMeasure
            (fun r (_ : Ω) =>
              sSup ((fun v : ℝ≥0 => X.X (u + v) ω - X.X u ω) '' Set.Icc 0 r))
            ω)) :=
      barrierStrategy_stoppedReward_postUpcrossing_shifted_window_of_levy
        X x a hx0 hxa q ω u hu
    _ = ENNReal.ofReal (Real.exp (-(q * (u : ℝ)))) *
        (∫⁻ t in Set.Ioi (0 : ℝ) ∩ paymentTimes ρ,
          ENNReal.ofReal (Real.exp (-(q * t)))
          ∂(dividendMeasure
            (fun r (_ : Ω) =>
              sSup ((fun v : ℝ≥0 => X.X (u + v) ω - X.X u ω) '' Set.Icc 0 r))
            ω)) := by
      rw [hclock, translated_payment_window_eq_shifted_ruin_window]

