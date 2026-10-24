-- Prove2me | solution 1 for AvramDividend.Classical.general_stopped_dividend_indicator_reward_measurable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-23T06:53:20.49605+00:00
-- url     : https://prove2.me/submissions/d151aa56-3695-412f-8a67-bfa6dad72bb4

import Mathlib.Probability.Kernel.MeasurableLIntegral
import Mathlib.MeasureTheory.Function.SpecialFunctions.Basic
import Mathlib.MeasureTheory.Constructions.BorelSpace.Real
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_dividendMeasure_global_sfinite_kernel_exists
import Theorems.Thm_AvramDividend_Classical_ruinTime_measurable
import Theorems.Thm_AvramDividend_Classical_paymentTimes_joint_measurable
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
    (X : SpectrallyNegativeLevy P 𝓕)
    (q x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsDividendStrategy 𝓕 D) :
    Measurable (fun ω : Ω =>
      ∫⁻ t, if t ∈ paymentTimes (ruinTime X x D ω)
        then ENNReal.ofReal (Real.exp (-(q * t))) else 0
        ∂(dividendMeasure D ω)) := by
  obtain ⟨κ, hsf, hκ⟩ :=
    AvramDividend.Classical.dividendMeasure_global_sfinite_kernel_exists D hD
  letI : ProbabilityTheory.IsSFiniteKernel κ := hsf
  have hS :
      MeasurableSet {p : ℝ × Ω |
        p.1 ∈ paymentTimes (ruinTime X x D p.2)} :=
    AvramDividend.Classical.paymentTimes_joint_measurable
      (ruinTime X x D)
      (AvramDividend.Classical.ruinTime_measurable X x D hD)
  have hw : Measurable (fun t : ℝ =>
      ENNReal.ofReal (Real.exp (-(q * t)))) := by
    exact ENNReal.measurable_ofReal.comp
      (Real.measurable_exp.comp ((measurable_const.mul measurable_id).neg))
  have hm := AvramDividend.Classical.measurable_random_indicator_lintegral
    κ {p : ℝ × Ω | p.1 ∈ paymentTimes (ruinTime X x D p.2)}
    hS (fun t : ℝ => ENNReal.ofReal (Real.exp (-(q * t)))) hw
  simpa only [Set.mem_setOf_eq, hκ] using hm

