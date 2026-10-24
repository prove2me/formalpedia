-- Prove2me | solution 1 for AvramDividend.Classical.runningSup_Ioc_kernel_isFinite_of_uniform_bound
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-23T11:34:15.297131+00:00
-- url     : https://prove2.me/submissions/a9f1a094-a0b6-4cf6-b441-a8f3e6d11a48

import Mathlib.Probability.Kernel.Defs
import Theorems.Thm_AvramDividend_Classical_runningSup_dividendMeasure_restrict_Ioc_measurable

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set ProbabilityTheory
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (s t : ℝ)
    (C : ℝ≥0∞) (hC : C < ⊤)
    (hBound : ∀ ω : Ω,
       (dividendMeasure (runningSup X) ω) (Set.Ioc s t) ≤ C) :
    ProbabilityTheory.IsFiniteKernel
      (ProbabilityTheory.Kernel.mk
        (fun ω : Ω =>
          (dividendMeasure (runningSup X) ω).restrict (Set.Ioc s t))
        (runningSup_dividendMeasure_restrict_Ioc_measurable X s t)) := by
  constructor
  refine ⟨C, hC, ?_⟩
  intro ω
  change ((dividendMeasure (runningSup X) ω).restrict (Set.Ioc s t)) Set.univ ≤ C
  simpa only [Measure.restrict_apply_univ] using hBound ω
