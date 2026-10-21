-- Prove2me | solution 1 for AvramDividend.Classical.runningSup_stopped_full_reward_measurable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-20T15:03:10.191274+00:00
-- url     : https://prove2.me/submissions/912e3b44-0477-45f3-b865-bde21caabbb3

import Theorems.Thm_AvramDividend_Classical_runningSup_dividendMeasure_global_sfinite_kernel_exists
import Theorems.Thm_AvramDividend_Classical_runningSup_stopped_full_reward_measurable_of_kernel
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
    (X : SpectrallyNegativeLevy P 𝓕) (a q : ℝ) :
    Measurable (fun ω : Ω =>
      ∫⁻ t,
        if t ∈ paymentTimes (barrierRuinTime X a ω)
        then ENNReal.ofReal (Real.exp (-(q * t))) else 0
        ∂dividendMeasure (runningSup X) ω) := by
  obtain ⟨κ, hsf, hκ⟩ :=
    runningSup_dividendMeasure_global_sfinite_kernel_exists X
  letI : ProbabilityTheory.IsSFiniteKernel κ := hsf
  exact runningSup_stopped_full_reward_measurable_of_kernel X a q κ hκ
