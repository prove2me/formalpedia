-- Prove2me | solution 1 for DatkoDelayWave.BoundaryDelay.eq19_no_imaginary_zeros_at_threshold
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T10:12:13.76698+00:00
-- url     : https://prove2.me/submissions/b03e88d4-8b47-4f2b-be7b-7d7e59f6b0c7

import Mathlib
import Definitions.Def_DatkoDelayWave_BoundaryDelay_DelayedWave

set_option autoImplicit false
open DatkoDelayWave.BoundaryDelay

lemma aux19 (a k η Ka : ℝ) (z w : ℂ) (ha : 0 < a) (hη : η ≠ 0) (hKa0 : 0 < Ka) (hKa1 : Ka < 1)
    (hk : k = (1 - Ka) / (1 + Ka)) (hz : ‖z‖ = Ka) (hw : ‖w‖ = 1)
    (hh : ((η : ℂ) * Complex.I + (a : ℂ)) * (1 + z)
      = -((η : ℂ) * Complex.I * ((k : ℂ) * w) * (1 - z))) : False := by
  have hk0 : 0 ≤ k := by rw [hk]; apply div_nonneg <;> linarith
  have hkK : k * (1 + Ka) = 1 - Ka := by rw [hk]; field_simp
  set A : ℝ := ‖(η : ℂ) * Complex.I + (a : ℂ)‖ with hA
  have hA2 : A ^ 2 = η ^ 2 + a ^ 2 := by
    rw [hA, Complex.sq_norm, Complex.normSq_apply]
    simp
    ring
  have h1 : |η| < A := by
    by_contra hcon
    push_neg at hcon
    have : A ^ 2 ≤ |η| ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hcon 2
    rw [sq_abs] at this
    nlinarith [sq_pos_of_pos ha]
  have h2 : 1 - Ka ≤ ‖1 + z‖ := by
    have := norm_sub_norm_le (1 : ℂ) (-z)
    simpa [hz, sub_neg_eq_add] using this
  have h3 : ‖1 - z‖ ≤ 1 + Ka := by
    have := norm_sub_le (1 : ℂ) z
    simpa [hz] using this
  have h4 := congrArg norm hh
  have hnη : ‖(η : ℂ)‖ = |η| := by rw [Complex.norm_real]; rfl
  have hnk : ‖(k : ℂ)‖ = k := by rw [Complex.norm_real, Real.norm_of_nonneg hk0]
  simp only [norm_mul, norm_neg, Complex.norm_I, mul_one, hw, hnη, hnk] at h4
  rw [← hA] at h4
  have h4' : A * ‖1 + z‖ = |η| * k * ‖1 - z‖ := by linarith [h4]
  have hpos : 0 < 1 - Ka := by linarith
  have h5 : A * ‖1 + z‖ ≥ A * (1 - Ka) := by
    apply mul_le_mul_of_nonneg_left h2 (norm_nonneg _)
  have h6 : |η| * k * ‖1 - z‖ ≤ |η| * k * (1 + Ka) :=
    mul_le_mul_of_nonneg_left h3 (mul_nonneg (abs_nonneg _) hk0)
  have h7 : |η| * k * (1 + Ka) = |η| * (1 - Ka) := by rw [mul_assoc, hkK]
  have h8 : 0 < |η| := abs_pos.mpr hη
  have h9 : |η| * (1 - Ka) < A * (1 - Ka) := mul_lt_mul_of_pos_right h1 hpos
  linarith

theorem solution (a k ε : ℝ) (ha : 0 < a)
    (hkK : k = (1 - K a) / (1 + K a)) (hε : 0 < ε) (η : ℝ) (hη : η ≠ 0) :
    h a k ε ((η : ℂ) * Complex.I) ≠ 0 := by
  intro hh
  have hK0 : 0 < K a := Real.exp_pos _
  have hK1 : K a < 1 := by
    unfold K
    have := Real.exp_lt_exp.mpr (show -2 * a < 0 by linarith)
    simpa using this
  have hz : ‖(K a : ℂ) * Complex.exp (-2 * ((η : ℂ) * Complex.I))‖ = K a := by
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hK0.le, Complex.norm_exp]
    simp
  have hw : ‖Complex.exp (-(ε : ℂ) * ((η : ℂ) * Complex.I))‖ = 1 := by
    rw [Complex.norm_exp]
    simp
  unfold h f at hh
  refine aux19 a k η (K a) _ _ ha hη hK0 hK1 hkK hz hw ?_
  linear_combination hh
