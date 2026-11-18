-- Prove2me | solution 1 for AvramDividend.Classical.avram_a27_original_physical_count_HasLaw_pgf_exact_20261117
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-17T21:58:40.026205+00:00
-- url     : https://prove2.me/submissions/82fce42e-8d3d-452d-9be7-cf354b73971a

import Mathlib.Probability.HasLaw
import Mathlib.Probability.Distributions.Poisson.Basic
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_chat06_poisson_count_pgf_general
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

theorem solution
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (K : Ω → ℕ) (r : ℝ≥0)
    (hLaw : HasLaw K (poissonMeasure r) P)
    (z : ℝ) :
    (∫ ω, z ^ (K ω) ∂P) = Real.exp ((r : ℝ) * (z - 1)) := by
  have hf : AEStronglyMeasurable (fun k : ℕ => z ^ k)
      (poissonMeasure r) := by
    exact (measurable_of_countable (fun k : ℕ => z ^ k)).aestronglyMeasurable
  calc
    (∫ ω, z ^ (K ω) ∂P) =
        (∫ k : ℕ, z ^ k ∂poissonMeasure r) := by
          simpa only [Function.comp_def] using hLaw.integral_comp hf
    _ = Real.exp ((r : ℝ) * (z - 1)) :=
        AvramDividend.Classical.chat06_poisson_count_pgf_general r z
