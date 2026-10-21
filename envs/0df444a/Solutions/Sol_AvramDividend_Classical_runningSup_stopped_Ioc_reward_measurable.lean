-- Prove2me | solution 1 for AvramDividend.Classical.runningSup_stopped_Ioc_reward_measurable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-20T15:03:03.389991+00:00
-- url     : https://prove2.me/submissions/0c096932-ca3e-4fbc-8f29-07b7b2ae3429

import Theorems.Thm_AvramDividend_Classical_runningSup_intervalKernel_isSFinite_of_eq
import Theorems.Thm_AvramDividend_Classical_runningSup_stopped_Ioc_reward_measurable_of_kernel
import Theorems.Thm_AvramDividend_Classical_runningSup_dividendMeasure_restrict_Ioc_measurable
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Probability.Kernel.Defs

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set ProbabilityTheory
open scoped NNReal ENNReal Classical
open AvramDividend.Classical

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (a q l u : ℝ) :
    Measurable (fun ω : Ω =>
      ∫⁻ t,
        if t ∈ paymentTimes (barrierRuinTime X a ω)
        then ENNReal.ofReal (Real.exp (-(q * t))) else 0
        ∂(dividendMeasure (runningSup X) ω).restrict (Set.Ioc l u)) := by
  let κ : ProbabilityTheory.Kernel Ω ℝ :=
    ProbabilityTheory.Kernel.mk
      (fun ω : Ω => (dividendMeasure (runningSup X) ω).restrict (Set.Ioc l u))
      (runningSup_dividendMeasure_restrict_Ioc_measurable X l u)
  have hκ : ∀ ω : Ω,
      κ ω = (dividendMeasure (runningSup X) ω).restrict (Set.Ioc l u) := by
    intro ω
    rfl
  letI : ProbabilityTheory.IsSFiniteKernel κ :=
    runningSup_intervalKernel_isSFinite_of_eq X l u κ hκ
  exact runningSup_stopped_Ioc_reward_measurable_of_kernel X a q l u κ hκ
