-- Prove2me | solution 1 for AvramDividend.Classical.avram_ubv_ito_jumps10_poisson_power_integrable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-07T10:57:21.697967+00:00
-- url     : https://prove2.me/submissions/7030b2f9-5557-4a09-aee1-3ccc23476b35

import Mathlib.Probability.Distributions.Poisson.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Tactic.Ring

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Classical MeasureTheory ProbabilityTheory Real
open scoped NNReal ENNReal Nat
noncomputable section

/-- The finite-band Poisson count has every real exponential moment. This
summability lemma is independent of identifying Avram's actual count law. -/
theorem solution (r : ℝ≥0) (a : ℝ) :
    Integrable (fun n : ℕ => a ^ n) (poissonMeasure r) := by
  rw [integrable_poissonMeasure_iff]
  simp_rw [norm_pow, Real.norm_eq_abs]
  have h : HasSum
      (fun n : ℕ => Real.exp (-(r : ℝ)) * (r : ℝ) ^ n / n ! * |a| ^ n)
      (Real.exp ((r : ℝ) * (|a| - 1))) := by
    convert (NormedSpace.expSeries_div_hasSum_exp ((r : ℝ) * |a|)).mul_left
      (Real.exp (-(r : ℝ))) using 1 <;>
      first
        | (funext n; rw [mul_pow]; ring)
        | (rw [← exp_eq_exp_ℝ, ← Real.exp_add]; congr 1; ring)
        | rfl
  exact h.summable
