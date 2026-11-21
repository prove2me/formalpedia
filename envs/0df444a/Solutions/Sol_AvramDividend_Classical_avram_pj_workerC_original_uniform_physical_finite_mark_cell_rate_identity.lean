-- Prove2me | solution 1 for AvramDividend.Classical.avram_pj_workerC_original_uniform_physical_finite_mark_cell_rate_identity
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-20T08:26:32.689145+00:00
-- url     : https://prove2.me/submissions/f2aadacb-708e-41e1-ad92-87a921c43db0

import Mathlib
open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal
noncomputable section

/-- Every original uniform physical-grid cell has the same exact
finite negative-mark Lévy compensator rate. -/
theorem solution
    (n m i : ℕ) (mass : ℝ≥0∞) :
    (let Δ : ℝ≥0 := (n : ℝ≥0) / ((m : ℝ≥0) + 1)
     let grid : ℕ → ℝ≥0 := fun j => (j : ℝ≥0) * Δ
     ((((grid (i + 1) - grid i : ℝ≥0) : ℝ≥0∞) * mass).toReal)) =
      ((n : ℝ) / ((m : ℝ) + 1)) * mass.toReal := by
  dsimp
  have hGrid (d : ℝ≥0) :
      (((i + 1 : ℕ) : ℝ≥0) * d - (i : ℝ≥0) * d) = d := by
    rw [Nat.cast_add, Nat.cast_one, add_mul, one_mul]
    exact add_tsub_cancel_left _ _
  rw [hGrid, ENNReal.toReal_mul, ENNReal.coe_toReal]
  simp only [NNReal.coe_div, NNReal.coe_natCast, NNReal.coe_add,
    NNReal.coe_one]
