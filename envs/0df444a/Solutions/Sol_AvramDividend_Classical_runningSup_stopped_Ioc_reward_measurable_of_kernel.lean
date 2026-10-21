-- Prove2me | solution 1 for AvramDividend.Classical.runningSup_stopped_Ioc_reward_measurable_of_kernel
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-20T08:26:11.741868+00:00
-- url     : https://prove2.me/submissions/fef9c255-8390-4ac1-8196-2ede3c888faa

import Mathlib.Probability.Kernel.MeasurableLIntegral
import Mathlib.MeasureTheory.Function.SpecialFunctions.Basic
import Mathlib.MeasureTheory.Constructions.BorelSpace.Real
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
    (κ : ProbabilityTheory.Kernel Ω ℝ)
    [ProbabilityTheory.IsSFiniteKernel κ]
    (hκ : ∀ ω : Ω, κ ω =
      (dividendMeasure (runningSup X) ω).restrict (Set.Ioc l u)) :
    Measurable (fun ω : Ω =>
      ∫⁻ t,
        if t ∈ paymentTimes (barrierRuinTime X a ω)
        then ENNReal.ofReal (Real.exp (-(q * t))) else 0
        ∂(dividendMeasure (runningSup X) ω).restrict (Set.Ioc l u)) := by
  have hw : Measurable (fun t : ℝ =>
      ENNReal.ofReal (Real.exp (-(q * t)))) := by
    exact ENNReal.measurable_ofReal.comp
      (Real.measurable_exp.comp ((measurable_const.mul measurable_id).neg))
  have hS : MeasurableSet
      {p : ℝ × Ω | p.1 ∈ paymentTimes (barrierRuinTime X a p.2)} :=
    barrierPaymentRegion_measurable X a
  have hm := measurable_random_indicator_lintegral κ
    {p : ℝ × Ω | p.1 ∈ paymentTimes (barrierRuinTime X a p.2)}
    hS (fun t : ℝ => ENNReal.ofReal (Real.exp (-(q * t)))) hw
  simpa only [Set.mem_setOf_eq, hκ] using hm
