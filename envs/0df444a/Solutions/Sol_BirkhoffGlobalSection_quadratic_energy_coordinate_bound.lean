-- Prove2me | solution 1 for BirkhoffGlobalSection.quadratic_energy_coordinate_bound
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-09-24T08:19:04.186484+00:00
-- url     : https://prove2.me/submissions/6baef0a7-e2fb-4ad8-98c9-a007452c9253

import Mathlib

theorem solution (M A B K u v : ℝ) (hM : 0 ≤ M)
    (hA : |A| ≤ M) (hB : |B| ≤ M) (hK : |K| ≤ M)
    (henergy : (u ^ 2 + v ^ 2) / 2 + A * u + B * v + K = 0) :
    |u| ≤ 4 * M + 4 ∧ |v| ≤ 4 * M + 4 := by
  have hAsq : A ^ 2 ≤ M ^ 2 := by
    have h := (sq_le_sq₀ (abs_nonneg A) hM).mpr hA
    simpa only [sq_abs] using h
  have hBsq : B ^ 2 ≤ M ^ 2 := by
    have h := (sq_le_sq₀ (abs_nonneg B) hM).mpr hB
    simpa only [sq_abs] using h
  have hsum : (u + A) ^ 2 + (v + B) ^ 2 ≤ 2 * M ^ 2 + 2 * M := by
    nlinarith only [henergy, hAsq, hBsq, (abs_le.mp hK).1]
  have huSq : (u + A) ^ 2 ≤ (2 * M + 2) ^ 2 := by
    nlinarith only [hsum, sq_nonneg (v + B), sq_nonneg M, hM]
  have hvSq : (v + B) ^ 2 ≤ (2 * M + 2) ^ 2 := by
    nlinarith only [hsum, sq_nonneg (u + A), sq_nonneg M, hM]
  have hshiftu : |u + A| ≤ 2 * M + 2 :=
    abs_le_of_sq_le_sq huSq (by linarith)
  have hshiftv : |v + B| ≤ 2 * M + 2 :=
    abs_le_of_sq_le_sq hvSq (by linarith)
  constructor
  · calc
      |u| = |(u + A) + (-A)| := by ring
      _ ≤ |u + A| + |-A| := abs_add_le _ _
      _ = |u + A| + |A| := by rw [abs_neg]
      _ ≤ 4 * M + 4 := by linarith
  · calc
      |v| = |(v + B) + (-B)| := by ring
      _ ≤ |v + B| + |-B| := abs_add_le _ _
      _ = |v + B| + |B| := by rw [abs_neg]
      _ ≤ 4 * M + 4 := by linarith
