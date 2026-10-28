-- Prove2me | solution 1 for CliffordTApprox.Ancilla.rounding_error
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-26T11:19:47.944985+00:00
-- url     : https://prove2.me/submissions/7daa4715-3480-4668-a6da-221020f4c27b

import Mathlib
import Definitions.Def_CliffordTApprox_Ancilla_Setting

open QAlgorithms
open QAlgorithms.Papers.Independent.Renew46.P12

open CliffordTApprox.Ancilla in
theorem solution (k : ℕ) (φ : ℝ) (hφ₀ : 0 ≤ φ) (hφ₁ : φ ≤ Real.pi / 4) :
    ‖gammaApprox k φ - Complex.exp (φ * Complex.I)‖ ≤ Real.sqrt 2 / 2 ^ k := by
  set u : ℝ := (roundX k φ : ℝ) - 2 ^ k * Real.cos φ with hu
  set v : ℝ := (roundY k φ : ℝ) - 2 ^ k * Real.sin φ with hv
  have hu1 : u ^ 2 ≤ 1 := by
    have h1 := Int.floor_le ((2 : ℝ) ^ k * Real.cos φ)
    have h2 := Int.lt_floor_add_one ((2 : ℝ) ^ k * Real.cos φ)
    have : u ≤ 0 := by rw [hu]; unfold roundX; linarith
    have : -1 < u := by rw [hu]; unfold roundX; linarith
    nlinarith
  have hv1 : v ^ 2 ≤ 1 := by
    have h1 := Int.floor_le ((2 : ℝ) ^ k * Real.sin φ)
    have h2 := Int.lt_floor_add_one ((2 : ℝ) ^ k * Real.sin φ)
    have : v ≤ 0 := by rw [hv]; unfold roundY; linarith
    have : -1 < v := by rw [hv]; unfold roundY; linarith
    nlinarith
  have hexp : Complex.exp (φ * Complex.I) = (Real.cos φ : ℂ) + (Real.sin φ : ℂ) * Complex.I := by
    rw [Complex.exp_mul_I, Complex.ofReal_cos, Complex.ofReal_sin]
  have h2k : (2 : ℂ) ^ k ≠ 0 := pow_ne_zero _ two_ne_zero
  have key : gammaApprox k φ - Complex.exp (φ * Complex.I)
      = ((u : ℂ) + (v : ℂ) * Complex.I) / (2 : ℂ) ^ k := by
    unfold gammaApprox
    rw [hexp, hu, hv]
    push_cast
    field_simp
    ring
  rw [key, norm_div, Complex.norm_add_mul_I, norm_pow]
  have hn2 : ‖(2 : ℂ)‖ = 2 := by simp
  rw [hn2]
  apply div_le_div_of_nonneg_right _ (by positivity)
  apply Real.sqrt_le_sqrt
  linarith
