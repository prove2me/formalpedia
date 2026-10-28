-- Prove2me | solution 1 for AvramDividend.Classical.identically_law_fixed_marks_expectation_ws01b
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-27T16:04:35.283406+00:00
-- url     : https://prove2.me/submissions/495d321a-1935-4481-99f3-148f9d9873ab

import Mathlib

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

/-- Exact expectation of a fixed finite sequence of marks sharing a law.
No private Poisson point-family definitions are required. -/
theorem solution
    {Ω E : Type*} [MeasurableSpace Ω] [MeasurableSpace E]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ν : Measure E)
    (Y : ℕ → Ω → E)
    (hYm : ∀ n, Measurable (Y n))
    (hYL : ∀ n, HasLaw (Y n) ν μ)
    (j : ℕ) (f : E → ℝ) (hf : Measurable f)
    (hfI : Integrable f ν) :
    (∫ ω, ∑ n ∈ Finset.range j, f (Y n ω) ∂μ) =
      (j : ℝ) * ∫ y, f y ∂ν := by
  have hInt (n : ℕ) :
      Integrable (fun ω => f (Y n ω)) μ := by
    have hm : Integrable f (Measure.map (Y n) μ) := by
      rwa [(hYL n).map_eq]
    exact hm.comp_measurable (hYm n)
  have hMean (n : ℕ) :
      (∫ ω, f (Y n ω) ∂μ) = ∫ y, f y ∂ν := by
    rw [← integral_map (hYm n).aemeasurable
      hf.aestronglyMeasurable]
    rw [(hYL n).map_eq]
  calc
    (∫ ω, ∑ n ∈ Finset.range j, f (Y n ω) ∂μ) =
        ∑ n ∈ Finset.range j, ∫ ω, f (Y n ω) ∂μ := by
          rw [integral_finset_sum _ (fun n hn => hInt n)]
    _ = ∑ n ∈ Finset.range j, ∫ y, f y ∂ν := by
          exact Finset.sum_congr rfl (fun n _ => hMean n)
    _ = (j : ℝ) * ∫ y, f y ∂ν := by
          simp [mul_comm]
