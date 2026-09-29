-- Prove2me | solution 1 for DiazModulus.recip_pi_log_on_axis
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-23T16:22:04.483691+00:00
-- url     : https://prove2.me/submissions/1cc56f4b-4f97-4b64-8758-c31760fd2449

import Mathlib
import Definitions.Def_DiazModulus
import Theorems.Thm_DiazModulus_recip_pi_log_rational_line

open Complex ComplexConjugate

namespace OnAxis

noncomputable def cjQ : ℂ →ₐ[ℚ] ℂ :=
  (Complex.conjAe : ℂ ≃ₐ[ℝ] ℂ).toAlgHom.restrictScalars ℚ

theorem alg_conj {z : ℂ} (h : IsAlgebraic ℚ z) : IsAlgebraic ℚ (conj z) := by
  obtain ⟨p, hp0, hp⟩ := h
  refine ⟨p, hp0, ?_⟩
  have : Polynomial.aeval (cjQ z) p = cjQ (Polynomial.aeval z p) :=
    Polynomial.aeval_algHom_apply cjQ z p
  rw [show (conj z : ℂ) = cjQ z from rfl, this, hp, map_zero]

end OnAxis

open OnAxis in
/-- An exception `γ` to `(S)` lies on an axis. Its conjugate is an exception too, because
`γ̄/(πi) = -conj (γ/(πi))`; by the rational-line theorem `γ̄ = qγ` with `q` rational, and
comparing real and imaginary parts forces `q = 1` with `Im γ = 0`, or `Re γ = 0`. -/
theorem solution :
    ∀ γ : ℂ, IsAlgebraic ℚ γ →
      IsAlgebraic ℚ (Complex.exp (γ / (((Real.pi : ℝ) : ℂ) * Complex.I))) →
      γ.re = 0 ∨ γ.im = 0 := by
  intro γ hγ he
  by_cases h0 : γ = 0
  · left; rw [h0]; rfl
  have hconj : conj γ / (((Real.pi : ℝ) : ℂ) * Complex.I)
      = -conj (γ / (((Real.pi : ℝ) : ℂ) * Complex.I)) := by
    rw [map_div₀, map_mul, Complex.conj_ofReal, Complex.conj_I]
    ring
  have hce : IsAlgebraic ℚ (Complex.exp (conj γ / (((Real.pi : ℝ) : ℂ) * Complex.I))) := by
    rw [hconj, Complex.exp_neg, Complex.exp_conj]
    exact (alg_conj he).inv
  obtain ⟨q, hq⟩ :=
    DiazModulus.recip_pi_log_rational_line (conj γ) γ (alg_conj hγ) hγ h0 hce he
  have hre := congrArg Complex.re hq
  have him := congrArg Complex.im hq
  simp only [Complex.conj_re, Complex.conj_im, Complex.mul_re, Complex.mul_im,
    Complex.ratCast_re, Complex.ratCast_im, zero_mul, sub_zero, add_zero] at hre him
  by_cases hr : γ.re = 0
  · exact Or.inl hr
  · right
    have hq1 : (q : ℝ) = 1 := by
      have : ((q : ℝ) - 1) * γ.re = 0 := by linarith
      have := (mul_eq_zero.1 this).resolve_right hr
      linarith
    rw [hq1] at him
    linarith

#print axioms solution
