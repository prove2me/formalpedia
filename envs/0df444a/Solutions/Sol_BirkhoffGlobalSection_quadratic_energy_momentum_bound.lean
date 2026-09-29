-- Prove2me | solution 1 for BirkhoffGlobalSection.quadratic_energy_momentum_bound
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-09-24T18:33:18.044218+00:00
-- url     : https://prove2.me/submissions/6958bf5d-983e-4956-b200-2bbf77043a19

import Mathlib

theorem solution (K A B C p q : ℝ)
    (hK : 0 ≤ K) (hA : |A| ≤ K) (hB : |B| ≤ K) (hC : -K ≤ C)
    (henergy : (p ^ 2 + q ^ 2) / 2 + A * p + B * q + C ≤ 0) :
    |p| ≤ 4 * (K + 1) ∧ |q| ≤ 4 * (K + 1) := by
  have hA2 : A ^ 2 ≤ K ^ 2 := by
    have h := (sq_le_sq₀ (abs_nonneg A) hK).mpr hA
    simpa only [sq_abs] using h
  have hB2 : B ^ 2 ≤ K ^ 2 := by
    have h := (sq_le_sq₀ (abs_nonneg B) hK).mpr hB
    simpa only [sq_abs] using h
  have hsum : (p + A) ^ 2 + (q + B) ^ 2 ≤ 2 * K ^ 2 + 2 * K := by
    nlinarith only [henergy, hA2, hB2, hC]
  have hpSq : (p + A) ^ 2 ≤ (2 * K + 2) ^ 2 := by
    nlinarith only [hsum, sq_nonneg (q + B), sq_nonneg K, hK]
  have hqSq : (q + B) ^ 2 ≤ (2 * K + 2) ^ 2 := by
    nlinarith only [hsum, sq_nonneg (p + A), sq_nonneg K, hK]
  have hpShift : |p + A| ≤ 2 * K + 2 :=
    abs_le_of_sq_le_sq hpSq (by linarith)
  have hqShift : |q + B| ≤ 2 * K + 2 :=
    abs_le_of_sq_le_sq hqSq (by linarith)
  constructor
  · calc
      |p| = |(p + A) + (-A)| := by ring
      _ ≤ |p + A| + |-A| := abs_add_le _ _
      _ = |p + A| + |A| := by rw [abs_neg]
      _ ≤ 4 * (K + 1) := by linarith
  · calc
      |q| = |(q + B) + (-B)| := by ring
      _ ≤ |q + B| + |-B| := abs_add_le _ _
      _ = |q + B| + |B| := by rw [abs_neg]
      _ ≤ 4 * (K + 1) := by linarith
