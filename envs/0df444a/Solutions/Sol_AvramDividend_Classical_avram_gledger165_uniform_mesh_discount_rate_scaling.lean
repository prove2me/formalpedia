-- Prove2me | solution 1 for AvramDividend.Classical.avram_gledger165_uniform_mesh_discount_rate_scaling
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-11T21:59:11.347678+00:00
-- url     : https://prove2.me/submissions/ca163233-6486-482b-a79c-edf12b19d252

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical
noncomputable section
theorem solution
    (n m : ℕ) (q K : ℝ) (hK : 0 ≤ K) :
    let δ : ℝ := (n : ℝ) / ((m : ℝ) + 1)
    (m : ℝ) * ((q * δ) ^ 2 * K) + 2 * q * δ * K ≤
      ((q * (n : ℝ)) ^ 2 * K + 2 * q * (n : ℝ) * K) /
        ((m : ℝ) + 1) := by
  intro δ
  have hM : (m : ℝ) + 1 ≠ 0 := by positivity
  have heq :
      ((q * (n : ℝ)) ^ 2 * K + 2 * q * (n : ℝ) * K) /
        ((m : ℝ) + 1) -
      ((m : ℝ) * ((q * δ) ^ 2 * K) + 2 * q * δ * K) =
      ((q * (n : ℝ)) ^ 2 * K) / (((m : ℝ) + 1) ^ 2) := by
    dsimp [δ]
    field_simp
    ring
  have hn : 0 ≤ ((q * (n : ℝ)) ^ 2 * K) /
      (((m : ℝ) + 1) ^ 2) :=
    div_nonneg (mul_nonneg (sq_nonneg _) hK) (sq_nonneg _)
  linarith
