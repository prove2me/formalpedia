-- Prove2me | solution 1 for AvramDividend.Classical.avram_ws01e_b_capped_firstRecord_residual_clock_freshPath_indepFun
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-28T00:15:52.251757+00:00
-- url     : https://prove2.me/submissions/1213a1c1-d7e6-48a2-9332-59d75bb170e0

import Mathlib.Probability.ConditionalProbability
import Definitions.Def_AvramDividend_Classical_TwoSidedExit
import Theorems.Thm_AvramDividend_Classical_firstRecord_capped_rightCont_stopping_and_clock_measurable
import Theorems.Thm_AvramDividend_Classical_levy_rightCont_process
import Theorems.Thm_AvramDividend_Classical_avram_ws01e_b_levy_conditional_residual_clock_shiftedPath_indepFun

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal

/-- The actual first strict upper-record time capped by N is a genuine
finite stopping age for the right-continuous filtration. Before an
independent observation clock, its residual real duration is independent of
the full centred post-record Lévy path under the original product law. -/
theorem solution
    {Ω Θ : Type*} [mΩ : MeasurableSpace Ω] [MeasurableSpace Θ]
    {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (b : ℝ) (N : ℝ≥0)
    (Q : Measure Θ) [IsProbabilityMeasure Q]
    (e : Θ → ℝ≥0) (he : Measurable e)
    (hPos : (P.prod Q) {z : Ω × Θ |
      (min (twoSidedExitUpTime X b z.1) (N : ℝ≥0∞)).toNNReal < e z.2} ≠ 0) :
    let τ : Ω → ℝ≥0 := fun ω =>
      (min (twoSidedExitUpTime X b ω) (N : ℝ≥0∞)).toNNReal
    IndepFun
      (fun z : Ω × Θ => (e z.2 : ℝ) - (τ z.1 : ℝ))
      (fun z : Ω × Θ => fun s : ℝ≥0 =>
        X.X (τ z.1 + s) z.1 - X.X (τ z.1) z.1)
      ((P.prod Q)[|{z : Ω × Θ | τ z.1 < e z.2}]) := by
  letI : IsProbabilityMeasure P := X.isProbability
  let τ : Ω → ℝ≥0 := fun ω =>
    (min (twoSidedExitUpTime X b ω) (N : ℝ≥0∞)).toNNReal
  have hStop : ∀ s : ℝ≥0, MeasurableSet[𝓕.rightCont s]
      {ω : Ω | τ ω ≤ s} :=
    (firstRecord_capped_rightCont_stopping_and_clock_measurable X b N).1
  have hτ : Measurable τ :=
    (firstRecord_capped_rightCont_stopping_and_clock_measurable X b N).2
  obtain ⟨Y, hXY, _, _, _⟩ := levy_rightCont_process X
  have hind := avram_ws01e_b_levy_conditional_residual_clock_shiftedPath_indepFun
    Y τ hτ hStop Q e he hPos
  simpa only [hXY] using hind