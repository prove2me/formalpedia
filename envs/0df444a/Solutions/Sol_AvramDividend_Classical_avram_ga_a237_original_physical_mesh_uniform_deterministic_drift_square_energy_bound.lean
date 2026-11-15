-- Prove2me | solution 1 for AvramDividend.Classical.avram_ga_a237_original_physical_mesh_uniform_deterministic_drift_square_energy_bound
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-14T08:21:06.163219+00:00
-- url     : https://prove2.me/submissions/ece05669-3029-46c6-a1bd-5ec030d1475d

import Mathlib.Data.NNReal.Defs
import Mathlib.Tactic.Positivity
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open scoped NNReal
noncomputable section

theorem solution (n m : ℕ) (c : ℝ) :
    (m : ℝ) * ((((n : ℝ≥0) / ((m : ℝ≥0) + 1) : ℝ≥0) : ℝ) * c)^2
      ≤ ((n : ℝ) * c)^2 := by
  have hcast : ((((n : ℝ≥0) / ((m : ℝ≥0) + 1) : ℝ≥0) : ℝ)) =
      (n : ℝ) / ((m : ℝ) + 1) := by norm_cast
  rw [hcast]
  have hm : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg _
  have hden : 0 < ((m : ℝ) + 1)^2 := by positivity
  have hrel : (m : ℝ) ≤ ((m : ℝ) + 1)^2 := by
    nlinarith [sq_nonneg (m : ℝ)]
  calc
    (m : ℝ) * (((n : ℝ) / ((m : ℝ) + 1)) * c)^2 =
      (m : ℝ) * (((n : ℝ) * c) / ((m : ℝ) + 1))^2 := by ring
    _ = ((m : ℝ) * (((n : ℝ) * c)^2)) /
        (((m : ℝ) + 1)^2) := by
          rw [div_pow]
          ring
    _ ≤ ((n : ℝ) * c)^2 := by
      apply (div_le_iff₀ hden).2
      convert mul_le_mul_of_nonneg_right hrel (sq_nonneg ((n : ℝ) * c)) using 1
      · ring
