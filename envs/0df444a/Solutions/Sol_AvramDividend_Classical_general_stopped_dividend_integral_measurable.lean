-- Prove2me | solution 1 for AvramDividend.Classical.general_stopped_dividend_integral_measurable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-23T07:01:46.821221+00:00
-- url     : https://prove2.me/submissions/aa7d018a-27d1-4fe7-b51d-f248bf370c32

import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Theorems.Thm_AvramDividend_Classical_general_stopped_dividend_indicator_reward_measurable
import Theorems.Thm_AvramDividend_Classical_paymentTimes_measurable
import Definitions.Def_AvramDividend_Classical_DividendStrategy
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set ProbabilityTheory
open scoped NNReal ENNReal Classical
open AvramDividend.Classical

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsDividendStrategy 𝓕 D) :
    Measurable (fun ω : Ω =>
      ∫⁻ t in paymentTimes (ruinTime X x D ω),
        ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)) := by
  have hm :=
    AvramDividend.Classical.general_stopped_dividend_indicator_reward_measurable
      X q x D hD
  convert hm using 1
  funext ω
  have hs : MeasurableSet (paymentTimes (ruinTime X x D ω)) :=
    AvramDividend.Classical.paymentTimes_measurable (ruinTime X x D ω)
  calc
    (∫⁻ t in paymentTimes (ruinTime X x D ω),
      ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)) =
      (∫⁻ t, (paymentTimes (ruinTime X x D ω)).indicator
        (fun s : ℝ => ENNReal.ofReal (Real.exp (-(q * s)))) t
        ∂(dividendMeasure D ω)) := by
        exact (lintegral_indicator (μ := dividendMeasure D ω) hs
          (fun t : ℝ => ENNReal.ofReal (Real.exp (-(q * t))))).symm
    _ = (∫⁻ t, if t ∈ paymentTimes (ruinTime X x D ω)
      then ENNReal.ofReal (Real.exp (-(q * t))) else 0
      ∂(dividendMeasure D ω)) := by
        congr 1

