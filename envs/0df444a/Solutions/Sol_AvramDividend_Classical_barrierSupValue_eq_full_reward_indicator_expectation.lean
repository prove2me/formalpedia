-- Prove2me | solution 1 for AvramDividend.Classical.barrierSupValue_eq_full_reward_indicator_expectation
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-20T15:28:07.610687+00:00
-- url     : https://prove2.me/submissions/c00206c6-b9e5-469f-9aec-9e922f2c0661

import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Theorems.Thm_AvramDividend_Classical_paymentTimes_measurable
import Definitions.Def_AvramDividend_Classical_ReflectionBarrier
import Mathlib.Analysis.Complex.Exponential

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal Classical
open AvramDividend.Classical

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (a q : ℝ) :
    barrierSupValue X a q =
      ∫⁻ ω, ∫⁻ t,
        if t ∈ paymentTimes (barrierRuinTime X a ω)
        then ENNReal.ofReal (Real.exp (-(q * t))) else 0
        ∂(dividendMeasure (runningSup X) ω) ∂P := by
  classical
  unfold barrierSupValue
  apply lintegral_congr
  intro ω
  change
    (∫⁻ t in paymentTimes (barrierRuinTime X a ω),
      ENNReal.ofReal (Real.exp (-(q * t)))
      ∂(dividendMeasure (runningSup X) ω)) =
    (∫⁻ t,
      (paymentTimes (barrierRuinTime X a ω)).indicator
        (fun t : ℝ => ENNReal.ofReal (Real.exp (-(q * t)))) t
      ∂(dividendMeasure (runningSup X) ω))
  exact (lintegral_indicator
    (μ := dividendMeasure (runningSup X) ω)
    (paymentTimes_measurable (barrierRuinTime X a ω))
    (fun t : ℝ => ENNReal.ofReal (Real.exp (-(q * t))))).symm
