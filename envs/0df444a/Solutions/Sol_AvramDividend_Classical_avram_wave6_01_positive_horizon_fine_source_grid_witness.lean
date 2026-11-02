-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave6_01_positive_horizon_fine_source_grid_witness
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-01T20:12:15.017493+00:00
-- url     : https://prove2.me/submissions/52a94fe9-053b-4335-b676-d67d18f831f5

import Mathlib
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Set Topology
open scoped NNReal ENNReal

theorem solution (T : ℝ≥0) (hT : 0 < T) :
    ∃ grid : ℕ → ℕ → ℝ≥0,
      (∀ n : ℕ, 0 < n →
        StrictMono (grid n) ∧ grid n 0 = 0 ∧ grid n n = T) ∧
      (∀ δ : ℝ, 0 < δ →
        ∀ᶠ n : ℕ in atTop, ∀ i : ℕ, i < n →
          dist (grid n i) (grid n (i + 1)) < δ) ∧
      (∀ n i : ℕ, i ≤ n → grid n i ≤ T) := by
  classical
  let step : ℕ → ℝ≥0 := fun n => T / (n : ℝ≥0)
  let grid : ℕ → ℕ → ℝ≥0 := fun n i => (i : ℝ≥0) * step n
  have hnext (n i : ℕ) :
      grid n (i + 1) = grid n i + step n := by
    simp only [grid, Nat.cast_add, Nat.cast_one, add_mul, one_mul]
  have ht (n : ℕ) : Monotone (grid n) := by
    intro i j hij
    exact mul_le_mul_of_nonneg_right (by exact_mod_cast hij) bot_le
  have hGrid (n : ℕ) (hn : 0 < n) :
      StrictMono (grid n) ∧ grid n 0 = 0 ∧ grid n n = T := by
    have hden : (0 : ℝ≥0) < (n : ℝ≥0) := by exact_mod_cast hn
    have hstep : 0 < step n := div_pos hT hden
    refine ⟨?_, ?_, ?_⟩
    · intro i j hij
      exact mul_lt_mul_of_pos_right (by exact_mod_cast hij) hstep
    · simp only [grid, Nat.cast_zero, zero_mul]
    · change (n : ℝ≥0) * (T / (n : ℝ≥0)) = T
      rw [← mul_div_assoc]
      exact mul_div_cancel_left₀ T (ne_of_gt hden)
  have hDist (n i : ℕ) :
      dist (grid n i) (grid n (i + 1)) = (step n : ℝ) := by
    rw [hnext, NNReal.dist_eq, NNReal.coe_add]
    have hlin : (grid n i : ℝ) -
        ((grid n i : ℝ) + (step n : ℝ)) =
        -(step n : ℝ) := by ring
    rw [hlin, abs_neg]
    exact abs_of_nonneg (step n).property
  have hInv :
      Tendsto (fun n : ℕ => (n : ℝ)⁻¹) atTop (𝓝 (0 : ℝ)) := by
    exact tendsto_inv_atTop_zero.comp
      (tendsto_natCast_atTop_atTop :
        Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop)
  have hWidth :
      Tendsto (fun n : ℕ => (step n : ℝ)) atTop (𝓝 (0 : ℝ)) := by
    simpa [step, NNReal.coe_div, div_eq_mul_inv] using
      (tendsto_const_nhds.mul hInv : Tendsto
        (fun n : ℕ => (T : ℝ) * (n : ℝ)⁻¹)
        atTop (𝓝 ((T : ℝ) * (0 : ℝ))))
  have hMesh : ∀ δ : ℝ, 0 < δ →
      ∀ᶠ n : ℕ in atTop, ∀ i : ℕ, i < n →
        dist (grid n i) (grid n (i + 1)) < δ := by
    intro δ hδ
    have hevent : ∀ᶠ n : ℕ in atTop,
        (step n : ℝ) < δ :=
      hWidth.eventually (eventually_lt_nhds hδ)
    filter_upwards [hevent] with n hn
    intro i hi
    simpa only [hDist] using hn
  have hBound : ∀ n i : ℕ, i ≤ n → grid n i ≤ T := by
    intro n i hi
    by_cases hn : n = 0
    · subst n
      simp [grid, step]
    · calc
        grid n i ≤ grid n n := ht n hi
        _ = T := (hGrid n (Nat.pos_of_ne_zero hn)).2.2
  exact ⟨grid, hGrid, hMesh, hBound⟩
