-- Prove2me | solution 1 for AvramDividend.Classical.avram_bv_residual9_coarse_original_grid_unbounded_cell
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-07T17:53:31.666685+00:00
-- url     : https://prove2.me/submissions/25d9828d-0b06-4cc2-ac65-50441f431067

import Mathlib.Data.NNReal.Defs
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open scoped NNReal

/-- The original stopped physical grid conditions allow cells whose
width never shrinks, even with the prescribed penultimate horizon. -/
theorem solution :
    ∃ u : ℕ → ℕ → NNReal,
      (∀ n, u n 0 = 0 ∧ ((u n (n + 1) : ℝ) = 3 - 3 / ((n : ℝ) + 2))) ∧
      (∀ n i, i < n + 1 → u n i ≤ u n (i + 1)) ∧
      (∀ n, (3 / 2 : ℝ) ≤ (u n (n + 1) : ℝ) - (u n n : ℝ)) := by
  have hcore (n : ℕ) : (3 / 2 : ℝ) ≤ 3 - 3 / ((n : ℝ) + 2) := by
    have hn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg _
    have hden : (0 : ℝ) < (n : ℝ) + 2 := by linarith
    have hfrac : 3 / ((n : ℝ) + 2) ≤ (3 / 2 : ℝ) := by
      apply (div_le_iff₀ hden).2
      nlinarith
    linarith
  let v : ℕ → NNReal := fun n =>
    ⟨3 - 3 / ((n : ℝ) + 2),
      le_trans (by norm_num : (0 : ℝ) ≤ 3 / 2) (hcore n)⟩
  let u : ℕ → ℕ → NNReal := fun n i => if i ≤ n then 0 else v n
  refine ⟨u, ?_, ?_, ?_⟩
  · intro n
    constructor
    · simp [u]
    · have hn : ¬ n + 1 ≤ n := by omega
      simp [u, hn, v]
      rfl
  · intro n i hi
    have hi' : i ≤ n := Nat.lt_succ_iff.mp hi
    simp [u, hi']
  · intro n
    have hn : ¬ n + 1 ≤ n := by omega
    simp [u, hn, v]
    change (3 / 2 : ℝ) ≤ 3 - 3 / ((n : ℝ) + 2)
    exact hcore n
