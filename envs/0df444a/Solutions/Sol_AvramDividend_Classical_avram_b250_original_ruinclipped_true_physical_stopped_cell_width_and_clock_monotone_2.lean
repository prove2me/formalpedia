-- Prove2me | solution 2 for AvramDividend.Classical.avram_b250_original_ruinclipped_true_physical_stopped_cell_width_and_clock_monotone
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-14T21:40:47.492506+00:00
-- url     : https://prove2.me/submissions/3e256e18-a121-4b37-99d6-de385c0a5600

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical
open scoped NNReal
noncomputable section

theorem solution
    (n m : ℕ) (σ : ℝ≥0) :
    let Δ : ℝ≥0 := (n : ℝ≥0) / ((m : ℝ≥0) + 1)
    let v : ℕ → ℝ≥0 := fun i =>
      min ((i : ℝ≥0) * Δ) σ
    ∀ i : ℕ, v i ≤ v (i + 1) ∧
      ((v (i + 1) : ℝ) - (v i : ℝ)) ≤ (Δ : ℝ) := by
  intro Δ v i
  have hi : (i : ℝ≥0) ≤ ((i + 1 : ℕ) : ℝ≥0) := by
    exact_mod_cast Nat.le_succ i
  have hmult : (i : ℝ≥0) * Δ ≤ ((i + 1 : ℕ) : ℝ≥0) * Δ :=
    mul_le_mul_of_nonneg_right hi bot_le
  have horder : v i ≤ v (i + 1) := min_le_min_right σ hmult
  have heq : ((i + 1 : ℕ) : ℝ≥0) * Δ = (i : ℝ≥0) * Δ + Δ := by
    rw [Nat.cast_succ]
    ring
  have hstep : v (i + 1) ≤ v i + Δ := by
    dsimp [v]
    rw [heq]
    by_cases h : (i : ℝ≥0) * Δ ≤ σ
    · rw [min_eq_left h]
      exact min_le_left _ _
    · have h' : σ ≤ (i : ℝ≥0) * Δ := le_of_lt (lt_of_not_ge h)
      rw [min_eq_right h']
      exact (min_le_right _ _).trans (le_add_of_nonneg_right bot_le)
  have hreal : (v (i + 1) : ℝ) ≤ (v i : ℝ) + (Δ : ℝ) := by
    exact_mod_cast hstep
  exact ⟨horder, by linarith⟩
