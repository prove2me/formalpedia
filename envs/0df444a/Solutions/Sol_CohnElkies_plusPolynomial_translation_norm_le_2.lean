-- Prove2me | solution 2 for CohnElkies.plusPolynomial_translation_norm_le
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T12:37:22.807374+00:00
-- url     : https://prove2.me/submissions/9e732dd0-9cca-48e4-a2eb-5f584fa1b8f2

import Mathlib
import Definitions.Def_SpherePacking
set_option autoImplicit true
open CohnElkies
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000
noncomputable section
open Filter MeasureTheory Set
open scoped Topology


theorem solution
    (ε u T : ℝ) :
    ‖plusPolynomial ε ((T : ℂ) + Complex.I * (u : ℂ)) -
        plusPolynomial ε (Complex.I * (u : ℂ))‖ ≤
      9 * (1 + |u|) ^ 2 * (|T| + |T| ^ 3) := by
  have key : plusPolynomial ε ((T : ℂ) + Complex.I * (u : ℂ)) - plusPolynomial ε (Complex.I * (u : ℂ)) =
      ((T ^ 2 * (1 - 3 * u) : ℝ) : ℂ) + ((T * (2 * u + 1 - 3 * u ^ 2 + T ^ 2) : ℝ) : ℂ) * Complex.I := by
    apply Complex.ext <;> simp [plusPolynomial, pow_two, pow_succ] <;> ring
  rw [key]
  set t := |T| with ht
  set s := |u| with hs
  have ht0 : 0 ≤ t := abs_nonneg T
  have hs0 : 0 ≤ s := abs_nonneg u
  have hT2 : T ^ 2 = t ^ 2 := (sq_abs T).symm
  have hu2 : u ^ 2 = s ^ 2 := (sq_abs u).symm
  have hus : u ≤ s := le_abs_self u
  have hus' : -u ≤ s := neg_le_abs u
  have hA : |T ^ 2 * (1 - 3 * u)| ≤ t ^ 2 * (1 + 3 * s) := by
    rw [abs_mul, abs_of_nonneg (sq_nonneg T), hT2]
    exact mul_le_mul_of_nonneg_left (abs_le.2 ⟨by linarith, by linarith⟩) (sq_nonneg t)
  have hB : |T * (2 * u + 1 - 3 * u ^ 2 + T ^ 2)| ≤ t * (1 + 2 * s + 3 * s ^ 2 + t ^ 2) := by
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_left (abs_le.2 ⟨by nlinarith, by nlinarith⟩) ht0
  have hN : ‖((T ^ 2 * (1 - 3 * u) : ℝ) : ℂ) + ((T * (2 * u + 1 - 3 * u ^ 2 + T ^ 2) : ℝ) : ℂ) * Complex.I‖ ≤
      |T ^ 2 * (1 - 3 * u)| + |T * (2 * u + 1 - 3 * u ^ 2 + T ^ 2)| := by
    refine (norm_add_le _ _).trans ?_
    rw [norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
      Real.norm_eq_abs]
  have h1 : t ^ 2 ≤ (t + t ^ 3) / 2 := by nlinarith [mul_nonneg ht0 (sq_nonneg (t - 1))]
  set X := t + t ^ 3 with hX
  have hX0 : 0 ≤ X := by positivity
  have htX : t ≤ X := by nlinarith [pow_nonneg ht0 3]
  have ht3X : t ^ 3 ≤ X := by linarith
  have e1 := mul_le_mul_of_nonneg_right h1 (by linarith : (0:ℝ) ≤ 1 + 3 * s)
  have e2 := mul_le_mul_of_nonneg_right htX (by positivity : (0:ℝ) ≤ 1 + 2 * s + 3 * s ^ 2)
  have e3 : X * ((1 + 3 * s) / 2 + (1 + 2 * s + 3 * s ^ 2) + 1) ≤ X * (9 * (1 + s) ^ 2) :=
    mul_le_mul_of_nonneg_left (by nlinarith) hX0
  have : t * (1 + 2 * s + 3 * s ^ 2 + t ^ 2) = t * (1 + 2 * s + 3 * s ^ 2) + t ^ 3 := by ring
  nlinarith

