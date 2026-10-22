-- Prove2me | solution 1 for AvramDividend.Classical.chat06_laplace_random_mark_sum_without_pgf_assumption
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-21T11:39:33.684309+00:00
-- url     : https://prove2.me/submissions/74c23b5c-1408-4478-a148-d2bca8095cc4

import Mathlib.Probability.Distributions.Poisson.Basic
import Mathlib.Probability.HasLaw
import Mathlib.Probability.Independence.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Theorems.Thm_AvramDividend_Classical_chat06_laplace_random_mark_sum_of_indep_count
import Theorems.Thm_AvramDividend_Classical_chat06_poisson_count_pgf_general

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

/-- The marked random-sum Laplace identity follows from
count/mark independence, finite-mark moments and integrability;
the Poisson generating-function equation is now proved separately. -/
theorem solution
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P]
    (N : Ω → ℕ) (Y : ℕ → Ω → ℝ)
    (hN : Measurable N) (hY : ∀ n, Measurable (Y n))
    (hNY : IndepFun N (fun ω n => Y n ω) P)
    (r : ℝ≥0) (hLaw : HasLaw N (poissonMeasure r) P)
    (θ m : ℝ)
    (hFint : Integrable (fun ω =>
      Real.exp (θ * ∑ j ∈ Finset.range (N ω), Y j ω)) P)
    (hMarks : ∀ k, (∫ ω,
      Real.exp (θ * ∑ j ∈ Finset.range k, Y j ω) ∂P) = m ^ k) :
    (∫ ω, Real.exp (θ * ∑ j ∈ Finset.range (N ω), Y j ω) ∂P) =
      Real.exp ((r : ℝ) * (m - 1)) := by
  exact
    AvramDividend.Classical.chat06_laplace_random_mark_sum_of_indep_count
      P N Y hN hY hNY r hLaw θ m hFint hMarks
      (AvramDividend.Classical.chat06_poisson_count_pgf_general r m)
