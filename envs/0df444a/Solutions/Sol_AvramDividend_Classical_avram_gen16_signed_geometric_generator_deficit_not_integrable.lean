-- Prove2me | solution 1 for AvramDividend.Classical.avram_gen16_signed_geometric_generator_deficit_not_integrable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-07T16:56:00.772576+00:00
-- url     : https://prove2.me/submissions/8788da40-e7a2-406d-808f-0d2ff9a276a4

import Mathlib.Probability.Distributions.Geometric
import Theorems.Thm_AvramDividend_Classical_avram_a19_singular_geometric_not_integrable

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory
noncomputable section

theorem solution
    (p : unitInterval) (hp : p ≠ 0) (hhalf : (p : ℝ) = 1 / 2)
    (y : ℕ → ℝ)
    (hy : ∀ k, 0 < y k)
    (hsmall : ∀ k, y k ≤ 1 / 16)
    (hpower : ∀ k, y k ≤ 1 / ((2 : ℝ) ^ k) ^ 2)
    (hyint : Integrable y (geometricMeasure p)) :
    ¬ Integrable (fun k : ℕ =>
        (3 : ℝ) - 4 * Real.sqrt (y k) - 2 / Real.sqrt (y k))
        (geometricMeasure p) := by
  intro hS
  have hAdd : Integrable
      (fun k : ℕ =>
        ((3 : ℝ) - 4 * Real.sqrt (y k) - 2 / Real.sqrt (y k)) + y k)
      (geometricMeasure p) := hS.add hyint
  have hEq :
      (fun k : ℕ => (3 : ℝ) + y k -
        4 * Real.sqrt (y k) - 2 / Real.sqrt (y k)) =
      (fun k : ℕ => ((3 : ℝ) - 4 * Real.sqrt (y k) -
        2 / Real.sqrt (y k)) + y k) := by
    funext k
    ring
  have hSum : Integrable
      (fun k : ℕ => (3 : ℝ) + y k -
        4 * Real.sqrt (y k) - 2 / Real.sqrt (y k))
      (geometricMeasure p) := by
    rw [hEq]
    exact hAdd
  have hpB : (p != 0) := by
    simp [hp]
  exact (AvramDividend.Classical.avram_a19_singular_geometric_not_integrable
    p hpB hhalf y hy hsmall hpower) hSum.neg
