-- Prove2me | solution 2 for CohnElkies.minusPolynomial_imaginary_norm_ge_three_beta
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T12:22:34.314991+00:00
-- url     : https://prove2.me/submissions/767c6538-f91f-41d9-a46d-043b01788dd5

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
    {ε u : ℝ} (hε : 0 < ε)
    (hu : 1 + ε / 4 ≤ u) :
    3 * beta ε ≤
      ‖minusPolynomial ε (Complex.I * (u : ℂ))‖ := by
  have e : minusPolynomial ε (Complex.I * (u : ℂ)) =
      (((1 - u ^ 2) * (1 + u) + beta ε : ℝ) : ℂ) := by
    unfold minusPolynomial
    apply Complex.ext <;> simp [pow_two, pow_three] <;> ring
  rw [e, Complex.norm_real, Real.norm_eq_abs]
  have hb : beta ε = ε / 4 := rfl
  have hβ : 0 < beta ε := by rw [hb]; positivity
  have hu1 : beta ε ≤ u - 1 := by rw [hb]; linarith
  have hu2 : 2 ≤ u + 1 := by linarith
  have key : (1 - u ^ 2) * (1 + u) + beta ε ≤ -(3 * beta ε) := by
    have h1 : (1 - u ^ 2) * (1 + u) = -((u - 1) * (u + 1) ^ 2) := by ring
    have h2 : beta ε * 4 ≤ (u - 1) * (u + 1) ^ 2 := by
      have : (4:ℝ) ≤ (u + 1) ^ 2 := by nlinarith
      nlinarith
    linarith
  rw [le_abs]
  right
  linarith

