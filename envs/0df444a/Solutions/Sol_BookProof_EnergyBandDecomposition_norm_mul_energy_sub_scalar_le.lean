-- Prove2me | solution 1 for BookProof.EnergyBandDecomposition.norm_mul_energy_sub_scalar_le
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-09T06:37:14.638004+00:00
-- url     : https://prove2.me/submissions/8c7a86e4-e640-4244-8783-b90e4559d0b7

-- Generated from ChapterEnergyBandDecomposition.lean — solution of BookProof.EnergyBandDecomposition.norm_mul_energy_sub_scalar_le
import Mathlib
import Definitions.Def_ChapterEnergyBandDecomposition
import Theorems.Thm_BookProof_EnergyBandDecomposition_energy_sub_scalar_lt
open BookProof.EnergyBandDecomposition




open MeasureTheory

variable {X : Type*} {E : X → ℝ} {ε : ℝ} {k : ℤ} {x : X}

variable {X : Type*} {E : X → ℝ} {ε : ℝ} {k : ℤ} {x : X}

set_option maxHeartbeats 1000000 in
theorem solution (hε : 0 < ε) (hx : x ∈ band E ε k) (z : ℂ) :
    ‖(E x : ℂ) * z - ((k : ℝ) * ε : ℝ) * z‖ ≤ ε * ‖z‖ := by

  have h : ((E x : ℂ) * z - (((k : ℝ) * ε : ℝ) : ℂ) * z) = ((E x - k * ε : ℝ) : ℂ) * z := by
    push_cast
    ring
  rw [h, norm_mul, Complex.norm_real, Real.norm_eq_abs]
  exact mul_le_mul_of_nonneg_right (energy_sub_scalar_lt hε hx).le (norm_nonneg z)
