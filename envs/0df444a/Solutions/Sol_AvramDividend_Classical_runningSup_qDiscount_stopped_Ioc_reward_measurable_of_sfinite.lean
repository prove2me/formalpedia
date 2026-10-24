-- Prove2me | solution 1 for AvramDividend.Classical.runningSup_qDiscount_stopped_Ioc_reward_measurable_of_sfinite
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-23T11:34:42.935982+00:00
-- url     : https://prove2.me/submissions/3c335ec0-77c0-4f1c-8fae-bf9270e984cb

import Mathlib.Probability.Kernel.MeasurableLIntegral
import Mathlib.MeasureTheory.Function.SpecialFunctions.Basic
import Mathlib.MeasureTheory.Constructions.BorelSpace.Real
import Theorems.Thm_AvramDividend_Classical_runningSup_dividendMeasure_restrict_Ioc_measurable
import Theorems.Thm_AvramDividend_Classical_barrierPaymentRegion_measurable
import Theorems.Thm_AvramDividend_Classical_measurable_random_indicator_lintegral

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set ProbabilityTheory
open scoped NNReal ENNReal Classical
open AvramDividend.Classical

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (a q l u : ℝ)
    [ProbabilityTheory.IsSFiniteKernel (ProbabilityTheory.Kernel.mk
      (fun ω : Ω =>
        (dividendMeasure (runningSup X) ω).restrict (Set.Ioc l u))
      (runningSup_dividendMeasure_restrict_Ioc_measurable X l u))] :
    Measurable (fun ω : Ω =>
      ∫⁻ t,
        if t ∈ paymentTimes (barrierRuinTime X a ω)
        then ENNReal.ofReal (Real.exp (-(q * t))) else 0
        ∂(dividendMeasure (runningSup X) ω).restrict (Set.Ioc l u)) := by
  have hw : Measurable (fun t : ℝ =>
      ENNReal.ofReal (Real.exp (-(q * t)))) := by
    fun_prop
  exact measurable_random_indicator_lintegral
    (ProbabilityTheory.Kernel.mk
      (fun ω : Ω =>
        (dividendMeasure (runningSup X) ω).restrict (Set.Ioc l u))
      (runningSup_dividendMeasure_restrict_Ioc_measurable X l u))
    {p : ℝ × Ω | p.1 ∈ paymentTimes (barrierRuinTime X a p.2)}
    (barrierPaymentRegion_measurable X a)
    (fun t : ℝ => ENNReal.ofReal (Real.exp (-(q * t))))
    hw
