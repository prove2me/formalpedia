-- Prove2me | solution 1 for AvramDividend.Classical.avram_bvres9_nonrefining_physical_grid_exists
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-07T10:13:19.966386+00:00
-- url     : https://prove2.me/submissions/bdad0d5e-05b0-430a-a6a0-86c0dd79f3c7

import Mathlib.Data.NNReal.Defs
import Mathlib.Tactic.Positivity
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Classical
open scoped NNReal
noncomputable section

/-- The original endpoint and monotonicity constraints allow coarse grids. -/
theorem solution :
    ∃ u : ℕ → ℕ → ℝ≥0,
      (∀ n : ℕ, u n 0 = 0 ∧ ((u n (n + 1) : ℝ) = 3 - 3 / ((n : ℝ) + 2))) ∧
      (∀ (n i : ℕ), i < n + 1 → u n i ≤ u n (i + 1)) ∧
      (∀ n : ℕ, 1 ≤ n → (3 / 2 : ℝ) ≤
        (u n (n + 1) : ℝ) - (u n n : ℝ)) := by
  let tail : ℕ → ℝ≥0 := fun n =>
    ⟨3 - 3 / ((n : ℝ) + 2), by
      have hd : (0 : ℝ) < (n : ℝ) + 2 := by positivity
      have hb : 3 / ((n : ℝ) + 2) ≤ (3 : ℝ) := by
        apply (div_le_iff₀ hd).2
        have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
        nlinarith
      exact sub_nonneg.mpr hb⟩
  let u : ℕ → ℕ → ℝ≥0 := fun n i =>
    if i = 0 then 0 else if i ≤ n then 1 / 2 else tail n
  have hgrid : ∀ n, u n 0 = 0 ∧
      ((u n (n + 1) : ℝ) = 3 - 3 / ((n : ℝ) + 2)) := by
    intro n
    constructor
    · simp [u]
    · have h0 : n + 1 ≠ 0 := by omega
      have hle : ¬ n + 1 ≤ n := by omega
      simp only [u, if_neg h0, if_neg hle]
      rfl
  have hmono : ∀ n i, i < n + 1 → u n i ≤ u n (i + 1) := by
    intro n i hi
    have hin : i ≤ n := by omega
    by_cases h0 : i = 0
    · subst i
      simp [u]
    · have hnext0 : i + 1 ≠ 0 := by omega
      by_cases hnext : i + 1 ≤ n
      · simp [u, h0, hin, hnext0, hnext]
      · have hn : 1 ≤ n := by omega
        have hd : (0 : ℝ) < (n : ℝ) + 2 := by positivity
        have hfrac : 3 / ((n : ℝ) + 2) ≤ (1 : ℝ) := by
          apply (div_le_iff₀ hd).2
          have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
          nlinarith
        have htail : (1 / 2 : ℝ) ≤ 3 - 3 / ((n : ℝ) + 2) := by
          linarith
        have hcoetail : (tail n : ℝ) = 3 - 3 / ((n : ℝ) + 2) := rfl
        have hhalf : ((1 / 2 : ℝ≥0) : ℝ) = (1 / 2 : ℝ) := by norm_num
        have htail' : ((1 / 2 : ℝ≥0) : ℝ) ≤ (tail n : ℝ) := by
          rw [hhalf, hcoetail]
          exact htail
        have hle : (1 / 2 : ℝ≥0) ≤ tail n := by
          exact_mod_cast htail'
        simpa [u, h0, hin, hnext0, hnext] using hle
  have hcell : ∀ n, 1 ≤ n → (3 / 2 : ℝ) ≤
      (u n (n + 1) : ℝ) - (u n n : ℝ) := by
    intro n hn
    have h0 : n ≠ 0 := by omega
    have hnext0 : n + 1 ≠ 0 := by omega
    have hnext : ¬ n + 1 ≤ n := by omega
    have hd : (0 : ℝ) < (n : ℝ) + 2 := by positivity
    have hfrac : 3 / ((n : ℝ) + 2) ≤ (1 : ℝ) := by
      apply (div_le_iff₀ hd).2
      have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
      nlinarith
    have hbound : (3 / 2 : ℝ) ≤
        (3 - 3 / ((n : ℝ) + 2)) - 1 / 2 := by linarith
    have hcoetail : (tail n : ℝ) = 3 - 3 / ((n : ℝ) + 2) := rfl
    have hhalf : ((1 / 2 : ℝ≥0) : ℝ) = (1 / 2 : ℝ) := by norm_num
    simp only [u, if_neg hnext0, if_neg hnext, if_neg h0, if_pos (le_refl n)]
    rw [hcoetail, hhalf]
    exact hbound
  exact ⟨u, hgrid, hmono, hcell⟩
