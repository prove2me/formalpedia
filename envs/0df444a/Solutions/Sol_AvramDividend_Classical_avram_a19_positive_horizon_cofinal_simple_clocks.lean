-- Prove2me | solution 1 for AvramDividend.Classical.avram_a19_positive_horizon_cofinal_simple_clocks
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-06T00:13:07.797859+00:00
-- url     : https://prove2.me/submissions/f90c8f2a-43a6-4dcd-8cc4-0a95f4fd713d

import Mathlib
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology
noncomputable section

theorem solution (T : ℝ) (hT : 0 < T) :
    ∃ u : ℕ → ℝ, Monotone u ∧ (∀ n, 0 ≤ u n) ∧
      (∀ n, u n < T) ∧
      (∀ s : ℝ, s < T → ∃ n, s < u n) := by
  let u : ℕ → ℝ := fun n => T - T / ((n : ℝ) + 1)
  refine ⟨u, ?_, ?_, ?_, ?_⟩
  · intro a b hab
    have ha : 0 < (a : ℝ) + 1 := by positivity
    have hb : 0 < (b : ℝ) + 1 := by positivity
    have hle : (a : ℝ) + 1 ≤ (b : ℝ) + 1 := by
      exact_mod_cast (Nat.add_le_add_right hab 1)
    have hdiv : T / ((b : ℝ) + 1) ≤ T / ((a : ℝ) + 1) := by
      apply (div_le_div_iff₀ hb ha).2
      nlinarith [mul_nonneg (le_of_lt hT) (sub_nonneg.mpr hle)]
    dsimp [u]
    linarith
  · intro n
    have hn : 0 < (n : ℝ) + 1 := by positivity
    have hle : (1 : ℝ) ≤ (n : ℝ) + 1 := by
      have hn0 : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
      linarith
    have hdiv : T / ((n : ℝ) + 1) ≤ T := by
      apply (div_le_iff₀ hn).2
      nlinarith [mul_nonneg (le_of_lt hT) (sub_nonneg.mpr hle)]
    dsimp [u]
    linarith
  · intro n
    have hdiv : 0 < T / ((n : ℝ) + 1) := by positivity
    dsimp [u]
    linarith
  · intro s hs
    have hdist : 0 < T - s := by linarith
    obtain ⟨n, hn⟩ := exists_nat_gt (T / (T - s))
    have hden : 0 < (n : ℝ) + 1 := by positivity
    have hgt : T / (T - s) < (n : ℝ) + 1 := by linarith
    have hprod : T < ((n : ℝ) + 1) * (T - s) := by
      exact (div_lt_iff₀ hdist).mp hgt
    have hsmall : T / ((n : ℝ) + 1) < T - s := by
      apply (div_lt_iff₀ hden).2
      nlinarith
    refine ⟨n, ?_⟩
    dsimp [u]
    linarith
