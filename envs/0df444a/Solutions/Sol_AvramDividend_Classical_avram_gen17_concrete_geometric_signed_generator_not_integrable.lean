-- Prove2me | solution 1 for AvramDividend.Classical.avram_gen17_concrete_geometric_signed_generator_not_integrable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-07T17:39:05.363387+00:00
-- url     : https://prove2.me/submissions/d68545e1-21fb-436b-97a5-af8ad6012a4a

import Mathlib.Probability.Distributions.Geometric
import Mathlib.Tactic.Positivity
import Theorems.Thm_AvramDividend_Classical_avram_gen16_signed_geometric_generator_deficit_not_integrable

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory
noncomputable section

/-- A concrete dyadic initial reserve has a nonintegrable original generator
deficit under the half-geometric initial law. -/
theorem solution (p : unitInterval) (hp : p ≠ 0)
    (hhalf : (p : ℝ) = 1 / 2) :
    ¬ Integrable (fun k : ℕ =>
        (3 : ℝ) - 4 * Real.sqrt (1 / (16 * ((2 : ℝ) ^ k) ^ 2)) -
          2 / Real.sqrt (1 / (16 * ((2 : ℝ) ^ k) ^ 2)))
        (geometricMeasure p) := by
  let y : ℕ → ℝ := fun k => 1 / (16 * ((2 : ℝ) ^ k) ^ 2)
  have hpow : ∀ k : ℕ, (1 : ℝ) ≤ (2 : ℝ) ^ k := by
    intro k
    exact one_le_pow₀ (by norm_num)
  have hy : ∀ k, 0 < y k := by
    intro k
    dsimp [y]
    positivity
  have hsmall : ∀ k, y k ≤ 1 / 16 := by
    intro k
    dsimp [y]
    have hs : (1 : ℝ) ≤ ((2 : ℝ) ^ k) ^ 2 := by
      nlinarith [hpow k]
    have hd : (0 : ℝ) < 16 * ((2 : ℝ) ^ k) ^ 2 := by positivity
    apply (div_le_div_iff₀ hd (by norm_num : (0 : ℝ) < 16)).2
    nlinarith [hs]
  have hpower : ∀ k, y k ≤ 1 / ((2 : ℝ) ^ k) ^ 2 := by
    intro k
    dsimp [y]
    have hd : (0 : ℝ) < 16 * ((2 : ℝ) ^ k) ^ 2 := by positivity
    have hp2 : (0 : ℝ) < ((2 : ℝ) ^ k) ^ 2 := by positivity
    apply (div_le_div_iff₀ hd hp2).2
    nlinarith [hp2]
  have hyint : Integrable y (geometricMeasure p) := by
    apply Integrable.of_bound
      (measurable_of_countable y).aestronglyMeasurable (1 / 16)
    exact Filter.Eventually.of_forall (by
      intro k
      rw [Real.norm_eq_abs, abs_of_nonneg (le_of_lt (hy k))]
      exact hsmall k)
  simpa only [y] using
    (AvramDividend.Classical.avram_gen16_signed_geometric_generator_deficit_not_integrable
      p hp hhalf y hy hsmall hpower hyint)
