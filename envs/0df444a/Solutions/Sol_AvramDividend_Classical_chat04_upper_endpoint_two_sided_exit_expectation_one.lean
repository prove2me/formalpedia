-- Prove2me | solution 1 for AvramDividend.Classical.chat04_upper_endpoint_two_sided_exit_expectation_one
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-25T09:38:15.540026+00:00
-- url     : https://prove2.me/submissions/26dab511-8aaf-469a-b2b2-e81fb1459fd2

import Mathlib.MeasureTheory.Integral.Lebesgue.Add
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.Analysis.Complex.Exponential
import Definitions.Def_AvramDividend_Classical_TwoSidedExit

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q a : ℝ)
    (hup0 : ∀ᵐ ω ∂P, twoSidedExitUpTime X 0 ω = 0)
    (hdownpos : ∀ᵐ ω ∂P,
      0 < twoSidedExitDownTime X (-a) ω) :
    twoSidedExitExpectation X q a a = 1 := by
  haveI := X.isProbability
  unfold twoSidedExitExpectation
  refine (lintegral_congr_ae (g := fun _ => (1 : ℝ≥0∞)) ?_).trans (by simp)
  filter_upwards [hup0, hdownpos] with ω h1 h2
  rw [sub_self, h1, if_pos h2]
  simp
