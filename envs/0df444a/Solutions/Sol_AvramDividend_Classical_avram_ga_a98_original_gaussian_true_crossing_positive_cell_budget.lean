-- Prove2me | solution 1 for AvramDividend.Classical.avram_ga_a98_original_gaussian_true_crossing_positive_cell_budget
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-13T08:38:15.977321+00:00
-- url     : https://prove2.me/submissions/b45857b7-9e69-45ee-acd0-5a3cc41444b9

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_ga_a95_original_gaussian_uniform_mesh_true_crossing_card_le_one
import Theorems.Thm_AvramDividend_Classical_avram_ga_a97_single_crossing_positive_error_finset_bound
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical
open scoped NNReal

/-- The original Gaussian stopped physical mesh incurs no more than one positive stopping-crossing error budget. -/
theorem solution (n m : ℕ) (ρ : ℝ≥0)
    (f : ℕ → ℝ) (B : ℝ) (hB : 0 ≤ B)
    (hBound : ∀ i : ℕ, i < m →
      (i : ℝ≥0) * ((n : ℝ≥0) / ((m : ℝ≥0) + 1)) < ρ →
      ρ ≤ ((Nat.succ i : ℕ) : ℝ≥0) *
        ((n : ℝ≥0) / ((m : ℝ≥0) + 1)) →
        max (f i) 0 ≤ B) :
    (∑ i ∈ Finset.range m,
      if (i : ℝ≥0) * ((n : ℝ≥0) / ((m : ℝ≥0) + 1)) < ρ ∧
        ρ ≤ ((Nat.succ i : ℕ) : ℝ≥0) *
          ((n : ℝ≥0) / ((m : ℝ≥0) + 1))
      then max (f i) 0 else 0) ≤ B := by
  classical
  let S : Finset ℕ := (Finset.range m).filter (fun (i : ℕ) =>
    (i : ℝ≥0) * ((n : ℝ≥0) / ((m : ℝ≥0) + 1)) < ρ ∧
      ρ ≤ ((Nat.succ i : ℕ) : ℝ≥0) *
        ((n : ℝ≥0) / ((m : ℝ≥0) + 1)))
  have hCard : S.card ≤ 1 := by
    simpa only [S] using
      (avram_ga_a95_original_gaussian_uniform_mesh_true_crossing_card_le_one n m ρ)
  have hS (i : ℕ) (hi : i ∈ S) : max (f i) 0 ≤ B := by
    rcases Finset.mem_filter.mp hi with ⟨hiRange, hiCross⟩
    exact hBound i (Finset.mem_range.mp hiRange) hiCross.1 hiCross.2
  have h := avram_ga_a97_single_crossing_positive_error_finset_bound
    S f B hB hCard hS
  simpa only [S, Finset.sum_filter] using h
