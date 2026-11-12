-- Prove2me | solution 1 for AvramDividend.Classical.avram_gledger163_true_uniform_clipped_mesh_first_crossing
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-11T21:26:36.416202+00:00
-- url     : https://prove2.me/submissions/fa768755-90b9-411b-88e6-5f23bca36f1c

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_gledger91_monotone_clipped_grid_first_crossing_index
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal
noncomputable section
theorem solution
    (n m : ℕ) (hn : 0 < n) (ρ : ℝ≥0) (hρn : ρ ≤ (n : ℝ≥0))
    (hρpos : 0 < ρ) :
    let Δ : ℝ≥0 := (n : ℝ≥0) / ((m : ℝ≥0) + 1)
    let v : ℕ → ℝ≥0 := fun i => min ((i : ℝ≥0) * Δ) ρ
    ∃ k : ℕ, k < m + 1 ∧ v k < ρ ∧ v (k + 1) = ρ ∧
      (∀ i : ℕ, i < k → v (i + 1) < ρ) ∧
      (∀ i : ℕ, k < i → v i = ρ) := by
  intro Δ v
  have hden : (m : ℝ≥0) + 1 ≠ 0 := by positivity
  have hscale : ((m : ℝ≥0) + 1) * Δ = (n : ℝ≥0) := by
    dsimp [Δ]
    rw [mul_div_cancel₀]
    exact hden
  have hv : Monotone v := by
    intro i k hik
    dsimp [v]
    apply min_le_min_right
    exact mul_le_mul_of_nonneg_right (Nat.cast_le.mpr hik) (by positivity)
  have hv0 : v 0 = 0 := by simp [v]
  have hvN : v (m + 1) = ρ := by
    change min (((m + 1 : ℕ) : ℝ≥0) * Δ) ρ = ρ
    have hcast : ((m + 1 : ℕ) : ℝ≥0) = (m : ℝ≥0) + 1 := by
      push_cast
      ring
    rw [hcast, hscale]
    exact min_eq_right hρn
  have hv0lt : v 0 < ρ := by
    simpa only [hv0] using hρpos
  obtain ⟨k, hkN, hvk, hstop⟩ :=
    avram_gledger91_monotone_clipped_grid_first_crossing_index
      v hv ρ hv0lt (m + 1) hvN
  refine ⟨k, hkN, hvk, hstop, ?_, ?_⟩
  · intro i hi
    exact lt_of_le_of_lt (hv (Nat.succ_le_iff.mpr hi)) hvk
  · intro i hi
    apply le_antisymm
    · exact min_le_right _ _
    · calc
        ρ = v (k + 1) := hstop.symm
        _ ≤ v i := hv (Nat.succ_le_iff.mpr hi)
