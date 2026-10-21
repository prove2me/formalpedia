-- Prove2me | solution 1 for AvramDividend.Classical.runningSup_intervalKernel_isSFinite_of_eq
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-20T10:51:28.116495+00:00
-- url     : https://prove2.me/submissions/bc213bee-0289-402b-861d-99eda1cdf262

import Theorems.Thm_AvramDividend_Classical_kernel_isSFinite_of_pointwise_finite
import Theorems.Thm_AvramDividend_Classical_runningSup_dividendMeasure_Ioc_lt_top
import Mathlib.Probability.Kernel.Defs

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set ProbabilityTheory
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (l u : ℝ)
    (κ : ProbabilityTheory.Kernel Ω ℝ)
    (hκ : ∀ ω : Ω,
      κ ω = (dividendMeasure (runningSup X) ω).restrict (Set.Ioc l u)) :
    ProbabilityTheory.IsSFiniteKernel κ := by
  apply kernel_isSFinite_of_pointwise_finite κ
  intro ω
  rw [hκ ω]
  simpa using (runningSup_dividendMeasure_Ioc_lt_top X ω l u)
