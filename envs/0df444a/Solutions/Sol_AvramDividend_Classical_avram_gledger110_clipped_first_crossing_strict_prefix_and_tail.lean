-- Prove2me | solution 1 for AvramDividend.Classical.avram_gledger110_clipped_first_crossing_strict_prefix_and_tail
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-11T13:33:11.786521+00:00
-- url     : https://prove2.me/submissions/93b97329-4e27-4f49-992b-3c95e05686b4

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_gledger89_clipped_uniform_grid_monotone_and_exhausts_stop
import Theorems.Thm_AvramDividend_Classical_avram_gledger91_monotone_clipped_grid_first_crossing_index

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal
noncomputable section

/-- Before the unique first crossing the clipped grid remains strictly
    pre-stopping; afterwards the grid has reached the constant stop. -/
theorem solution
    (n m : ℕ) (ρ : ℝ≥0) (hρn : ρ ≤ (n : ℝ≥0))
    (hρpos : 0 < ρ) :
    let Δ : ℝ≥0 := (n : ℝ≥0) / ((m : ℝ≥0) + 2)
    let v : ℕ → ℝ≥0 := fun i => min ((i : ℝ≥0) * Δ) ρ
    ∃ k : ℕ, k < m + 2 ∧ v k < ρ ∧ v (k + 1) = ρ ∧
      (∀ i : ℕ, i < k → v (i + 1) < ρ) ∧
      (∀ i : ℕ, k < i → v i = ρ) := by
  dsimp only
  let Δ : ℝ≥0 := (n : ℝ≥0) / ((m : ℝ≥0) + 2)
  let v : ℕ → ℝ≥0 := fun i => min ((i : ℝ≥0) * Δ) ρ
  have hgrid : Monotone v ∧ v 0 = 0 ∧ v (m + 2) = ρ := by
    simpa only [v, Δ] using
      (avram_gledger89_clipped_uniform_grid_monotone_and_exhausts_stop
        n m ρ hρn)
  rcases hgrid with ⟨hv, hv0, hvN⟩
  have hv0lt : v 0 < ρ := by
    simpa only [hv0] using hρpos
  obtain ⟨k, hkN, hvk, hstop⟩ :=
    avram_gledger91_monotone_clipped_grid_first_crossing_index
      v hv ρ hv0lt (m + 2) hvN
  refine ⟨k, hkN, hvk, hstop, ?_, ?_⟩
  · intro i hi
    exact lt_of_le_of_lt (hv (Nat.succ_le_iff.mpr hi)) hvk
  · intro i hi
    apply le_antisymm
    · exact min_le_right _ _
    · calc
        ρ = v (k + 1) := hstop.symm
        _ ≤ v i := hv (Nat.succ_le_iff.mpr hi)
