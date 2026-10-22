-- Prove2me | solution 1 for AvramDividend.Classical.chat06_poisson_count_pgf_general
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-21T11:19:39.158989+00:00
-- url     : https://prove2.me/submissions/12f7e09c-8e44-4c64-887b-35b25ce319d8

import Mathlib.Probability.Distributions.Poisson.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Tactic.Ring

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory Real
open scoped NNReal ENNReal Nat

namespace AvramChat06

/-- The ordinary probability-generating function of a Poisson count,
valid at every real argument, including zero and negative values. -/
theorem poisson_count_pgf_general (r : ℝ≥0) (m : ℝ) :
    (∫ n : ℕ, m ^ n ∂poissonMeasure r) =
      Real.exp ((r : ℝ) * (m - 1)) := by
  rw [integral_poissonMeasure]
  simp only [smul_eq_mul]
  calc
    (∑' n : ℕ, Real.exp (-(r : ℝ)) *
        (r : ℝ) ^ n / n.factorial * m ^ n) =
      ∑' n : ℕ, Real.exp (-(r : ℝ)) *
        (((r : ℝ) * m) ^ n / n.factorial) := by
          congr 1
          funext n
          rw [mul_pow]
          ring
    _ = Real.exp (-(r : ℝ)) *
        ∑' n : ℕ, (((r : ℝ) * m) ^ n / n.factorial) :=
          tsum_mul_left
    _ = Real.exp (-(r : ℝ)) *
        Real.exp ((r : ℝ) * m) := by
          rw [(NormedSpace.expSeries_div_hasSum_exp
            ((r : ℝ) * m)).tsum_eq, exp_eq_exp_ℝ]
    _ = Real.exp ((r : ℝ) * (m - 1)) := by
          rw [← Real.exp_add]
          congr 1
          ring

end AvramChat06

open AvramChat06

theorem solution (r : ℝ≥0) (m : ℝ) :
    (∫ n : ℕ, m ^ n ∂poissonMeasure r) =
      Real.exp ((r : ℝ) * (m - 1)) := by
  exact poisson_count_pgf_general r m
