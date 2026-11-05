-- Prove2me | solution 1 for AvramDividend.Classical.avram_p3_2_caplinear_drift_cell_C1_derivative_remainder_exact
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-05T00:49:16.386011+00:00
-- url     : https://prove2.me/submissions/7c9af179-b3bb-4cce-8993-8c824ed2d2df

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

/-- Exact original capped drift cell equals true C1 generator drift plus Taylor remainder. -/
theorem solution
    (w : ℝ → ℝ) (C : ℝ≥0∞) (z c : ℝ)
    (hCap : C = ⊤ ∨ z ≤ C.toReal)
    (hUp : C = ⊤ ∨ z + c ≤ C.toReal) :
    let V : ℝ → ℝ := fun y =>
      if C = ⊤ then w y
      else if y ≤ C.toReal then w y
      else w C.toReal + (y - C.toReal)
    V (z + c) - V z =
      deriv w z * c +
      (w (z + c) - w z - deriv w z * c) := by
  intro V
  have hLeft : V z = w z := by
    by_cases ht : C = ⊤
    · simp [V, ht]
    · rcases hCap with hc | hz
      · exact (ht hc).elim
      · simp [V, ht, hz]
  have hRight : V (z + c) = w (z + c) := by
    by_cases ht : C = ⊤
    · simp [V, ht]
    · rcases hUp with hu | hz
      · exact (ht hu).elim
      · simp [V, ht, hz]
  rw [hLeft, hRight]
  ring
