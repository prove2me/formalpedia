-- Prove2me | solution 1 for ExplicitFormula.digamma_one_sub_sub_digamma
-- status  : ACCEPTED   (prove)
-- author  : @emmgaml
-- created : 2026-11-22T15:46:56.101872+00:00
-- url     : https://prove2.me/submissions/4ca191bd-9b51-413f-809f-9a5312331704

import Mathlib

open Filter Topology
open scoped Real ContDiff

set_option autoImplicit false

theorem solution (z : ℂ) (hz : ∀ n : ℤ, z ≠ n) :
    Complex.digamma (1 - z) - Complex.digamma z = π * Complex.cot (π * z) := by
  -- `z` and `1 - z` avoid the poles of `Γ`
  have hz' : ∀ m : ℕ, z ≠ -(m : ℂ) := by
    intro m h
    apply hz (-(m : ℤ))
    rw [h]; push_cast; ring
  have h1z : ∀ m : ℕ, 1 - z ≠ -(m : ℂ) := by
    intro m h
    apply hz ((m : ℤ) + 1)
    push_cast
    linear_combination -h
  have hG1 : Complex.Gamma z ≠ 0 := Complex.Gamma_ne_zero hz'
  have hG2 : Complex.Gamma (1 - z) ≠ 0 := Complex.Gamma_ne_zero h1z
  have hd1 : DifferentiableAt ℂ Complex.Gamma z := Complex.differentiableAt_Gamma z hz'
  have hd2 : DifferentiableAt ℂ Complex.Gamma (1 - z) := Complex.differentiableAt_Gamma _ h1z
  have hpi : (π : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  have hsin : Complex.sin (π * z) ≠ 0 := by
    intro h
    obtain ⟨k, hk⟩ := Complex.sin_eq_zero_iff.mp h
    apply hz k
    have : (π : ℂ) * z = π * k := by rw [hk]; ring
    exact mul_left_cancel₀ hpi this
  -- differentiability of the reflected factor
  have hlin : DifferentiableAt ℂ (fun w : ℂ => 1 - w) z :=
    (differentiableAt_const _).sub differentiableAt_id
  have hd2' : DifferentiableAt ℂ (fun w : ℂ => Complex.Gamma (1 - w)) z :=
    DifferentiableAt.comp (g := Complex.Gamma) (f := fun w : ℂ => 1 - w) z hd2 hlin
  -- log-derivative of the left side of the reflection formula
  have hL : logDeriv (fun w : ℂ => Complex.Gamma w * Complex.Gamma (1 - w)) z
      = Complex.digamma z - Complex.digamma (1 - z) := by
    rw [logDeriv_mul (f := Complex.Gamma) (g := fun w : ℂ => Complex.Gamma (1 - w)) z hG1 hG2 hd1 hd2']
    have hc : logDeriv (fun w : ℂ => Complex.Gamma (1 - w)) z
        = logDeriv Complex.Gamma (1 - z) * deriv (fun w : ℂ => 1 - w) z :=
      logDeriv_comp (f := Complex.Gamma) (g := fun w : ℂ => 1 - w) hd2 hlin
    have hderiv : deriv (fun w : ℂ => 1 - w) z = -1 := by
      have := ((hasDerivAt_id z).const_sub (1 : ℂ)).deriv
      simpa using this
    rw [hc, hderiv]
    simp only [Complex.digamma_def]
    ring
  -- log-derivative of the right side
  have hsd : DifferentiableAt ℂ (fun w : ℂ => Complex.sin (π * w)) z :=
    Complex.differentiableAt_sin.comp z ((differentiableAt_const _).mul differentiableAt_id)
  have hR : logDeriv (fun w : ℂ => (π : ℂ) / Complex.sin (π * w)) z
      = -(π * Complex.cot (π * z)) := by
    rw [logDeriv_div (f := fun _ : ℂ => (π : ℂ)) (g := fun w : ℂ => Complex.sin (π * w)) z hpi hsin
      (differentiableAt_const _) hsd]
    rw [logDeriv_const]
    have hc : logDeriv (fun w : ℂ => Complex.sin (π * w)) z
        = logDeriv Complex.sin (π * z) * deriv (fun w : ℂ => (π : ℂ) * w) z :=
      logDeriv_comp (f := Complex.sin) (g := fun w : ℂ => (π : ℂ) * w)
        Complex.differentiableAt_sin ((differentiableAt_const _).mul differentiableAt_id)
    have hderiv : deriv (fun w : ℂ => (π : ℂ) * w) z = π := by
      have := ((hasDerivAt_id z).const_mul (π : ℂ)).deriv
      simpa using this
    rw [hc, hderiv, Complex.logDeriv_sin]
    simp only [Pi.zero_apply]
    ring
  have hfun : (fun w : ℂ => Complex.Gamma w * Complex.Gamma (1 - w))
      = fun w : ℂ => (π : ℂ) / Complex.sin (π * w) := by
    funext w
    exact Complex.Gamma_mul_Gamma_one_sub w
  have key : Complex.digamma z - Complex.digamma (1 - z) = -(π * Complex.cot (π * z)) := by
    rw [← hL, ← hR, hfun]
  linear_combination -key
