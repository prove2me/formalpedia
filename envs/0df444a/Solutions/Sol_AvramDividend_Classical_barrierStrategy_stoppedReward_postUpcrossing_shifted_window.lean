-- Prove2me | solution 1 for AvramDividend.Classical.barrierStrategy_stoppedReward_postUpcrossing_shifted_window
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-26T22:57:54.67345+00:00
-- url     : https://prove2.me/submissions/138e4aa9-4165-4ea6-a372-c1596a177f7a

import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Theorems.Thm_AvramDividend_Classical_dividendMeasure_locallyFinite
import Theorems.Thm_AvramDividend_Classical_barrierStrategy_dividendMeasure_zero_nonpositive
import Theorems.Thm_AvramDividend_Classical_barrierStrategy_dividendMeasure_zero_preUpcrossing_Iic
import Theorems.Thm_AvramDividend_Classical_barrierStrategy_dividendMeasure_map_shift_of_support
import Theorems.Thm_AvramDividend_Classical_stopped_payment_lintegral_eq_post_u_of_zero_Iic
import Theorems.Thm_AvramDividend_Classical_discounted_paymentTimes_shift_of_measure_map
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
    (hνneg : (dividendMeasure
      (fun r (_ : Ω) =>
        sSup ((fun v : ℝ≥0 => X.X (u + v) ω - X.X u ω) '' Set.Icc 0 r))
      ω) (Set.Iic (0 : ℝ)) = 0) :
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
  classical
  let μ : Measure ℝ :=
    dividendMeasure (barrierStrategy X x a) ω
  let ν : Measure ℝ :=
    dividendMeasure
      (fun r (_ : Ω) =>
        sSup ((fun v : ℝ≥0 => X.X (u + v) ω - X.X u ω) '' Set.Icc 0 r))
      ω
  let σ : ℝ≥0∞ := ruinTime X x (barrierStrategy X x a) ω
  let f : ℝ → ℝ≥0∞ := fun t => ENNReal.ofReal (Real.exp (-(q * t)))
  have hzero : μ (Set.Iic (u : ℝ)) = 0 := by
    exact barrierStrategy_dividendMeasure_zero_preUpcrossing_Iic
      X x a hx0 hxa ω u hu
  letI : IsLocallyFiniteMeasure μ :=
    dividendMeasure_locallyFinite (barrierStrategy X x a) ω
  have hmap : μ = Measure.map (fun t : ℝ => (u : ℝ) + t) ν := by
    exact barrierStrategy_dividendMeasure_map_shift_of_support
      X x a hx0 hxa ω u hu
      (barrierStrategy_dividendMeasure_zero_nonpositive
        X x a hx0 hxa ω) hνneg
  have hremove :
      (∫⁻ t in paymentTimes σ, f t ∂μ) =
        (∫⁻ t in Set.Ioi (u : ℝ) ∩ paymentTimes σ, f t ∂μ) :=
    stopped_payment_lintegral_eq_post_u_of_zero_Iic
      μ f σ (u : ℝ) hzero
  have hshift :
      (∫⁻ t in Set.Ioi (u : ℝ) ∩ paymentTimes σ, f t ∂μ) =
      ENNReal.ofReal (Real.exp (-(q * (u : ℝ)))) *
        (∫⁻ t in Set.Ioi (0 : ℝ) ∩
          ((fun t : ℝ => (u : ℝ) + t) ⁻¹' paymentTimes σ),
          f t ∂ν) := by
    exact discounted_paymentTimes_shift_of_measure_map
      μ ν (u : ℝ) q σ hmap
  exact hremove.trans hshift
