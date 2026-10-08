-- Prove2me | solution 1 for AvramDividend.Classical.esscher_tilted_tail_scalar_integrability_bound
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-08T08:04:42.760977+00:00
-- url     : https://prove2.me/submissions/34b497e4-6c34-405b-95c6-665905a05f1c

import Mathlib

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Set

/-- Esscher damping controls the tail-area factor by truncated quadratic jumps. -/
theorem solution
    (φ z : ℝ) (hφ : 0 < φ) (hz : 0 ≤ z) :
    Real.exp (-(φ * z)) * min (z ^ 2) z ≤
      (1 + φ⁻¹) * min 1 (z ^ 2) := by
  have hφz : 0 ≤ φ * z := mul_nonneg hφ.le hz
  have hexple : Real.exp (-(φ * z)) ≤ 1 :=
    Real.exp_le_one_iff.mpr (neg_nonpos.mpr hφz)
  have hexpge : 0 ≤ Real.exp (-(φ * z)) := (Real.exp_pos _).le
  have hinv : 0 ≤ φ⁻¹ := (inv_pos.mpr hφ).le
  have hlin : φ * z ≤ Real.exp (φ * z) := by
    have h := Real.add_one_le_exp (φ * z)
    linarith
  have hcancel : Real.exp (φ * z) * Real.exp (-(φ * z)) = 1 := by
    rw [← Real.exp_add]
    have hz0 : φ * z + -(φ * z) = 0 := by ring
    rw [hz0, Real.exp_zero]
  have hlarge : z * Real.exp (-(φ * z)) ≤ φ⁻¹ := by
    have hbound :
        (φ * z) * Real.exp (-(φ * z)) ≤ 1 := by
      calc
        (φ * z) * Real.exp (-(φ * z)) ≤
            Real.exp (φ * z) * Real.exp (-(φ * z)) :=
          mul_le_mul_of_nonneg_right hlin hexpge
        _ = 1 := hcancel
    calc
      z * Real.exp (-(φ * z)) =
          ((φ * z) * Real.exp (-(φ * z))) * φ⁻¹ := by
        field_simp [ne_of_gt hφ]
      _ ≤ 1 * φ⁻¹ := mul_le_mul_of_nonneg_right hbound hinv
      _ = φ⁻¹ := one_mul _
  by_cases hsmall : z ≤ 1
  · have hzsq : z ^ 2 ≤ z := by
      nlinarith [mul_nonneg hz (sub_nonneg.mpr hsmall)]
    have hsq1 : z ^ 2 ≤ 1 := by nlinarith
    rw [min_eq_left hzsq, min_eq_right hsq1]
    have hfirst :
        Real.exp (-(φ * z)) * z ^ 2 ≤ z ^ 2 := by
      nlinarith [mul_le_mul_of_nonneg_right hexple (sq_nonneg z)]
    nlinarith [mul_nonneg hinv (sq_nonneg z)]
  · have hzl : 1 ≤ z := le_of_lt (lt_of_not_ge hsmall)
    have hzz : z ≤ z ^ 2 := by
      nlinarith [mul_nonneg hz (sub_nonneg.mpr hzl)]
    have hsq1 : 1 ≤ z ^ 2 := by nlinarith
    rw [min_eq_right hzz, min_eq_left hsq1]
    nlinarith [hlarge]
