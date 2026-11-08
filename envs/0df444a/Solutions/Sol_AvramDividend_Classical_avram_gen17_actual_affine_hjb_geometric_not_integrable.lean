-- Prove2me | solution 1 for AvramDividend.Classical.avram_gen17_actual_affine_hjb_geometric_not_integrable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-07T18:31:28.546492+00:00
-- url     : https://prove2.me/submissions/61640109-d4c7-4cb5-aaba-35d3ab98c8da

import Mathlib.Probability.Distributions.Geometric
import Mathlib.Tactic.Positivity
import Theorems.Thm_AvramDividend_Classical_avram_a19_singular_geometric_not_integrable

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory
noncomputable section

theorem solution (p : unitInterval) (hp : p ≠ 0)
    (hhalf : (p : ℝ) = 1 / 2) :
    ¬ Integrable (fun k : ℕ =>
      (3 : ℝ) + 1 / (16 * ((2 : ℝ) ^ k) ^ 2) -
        4 * Real.sqrt (1 / (16 * ((2 : ℝ) ^ k) ^ 2)) -
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
  intro h
  have hpbool : (p != 0) = true := bne_iff_ne.mpr hp
  have hsigned : Integrable (fun k : ℕ =>
      -(3 + y k - 4 * Real.sqrt (y k) - 2 / Real.sqrt (y k)))
      (geometricMeasure p) := by
    convert h.neg using 1 <;> (ext k; rfl)
  exact (AvramDividend.Classical.avram_a19_singular_geometric_not_integrable
    p hpbool hhalf y hy hsmall hpower) hsigned
