-- Prove2me | solution 1 for DiazModulus.recip_pi_not_log
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-08T17:24:06.613738+00:00
-- url     : https://prove2.me/submissions/c2b3aa2e-507b-42d0-bec8-aab5713ff5e4
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_DiazModulus
import Theorems.Thm_DiazModulus_recip_pi_not_log_real_gamma
import Theorems.Thm_DiazModulus_recip_pi_not_log_imag_gamma

-- The two children are not a case distinction: the real and imaginary axes do not cover the
-- non-zero algebraic numbers. They suffice because
--   S0 = { g in Qbar : g/(i*pi) is a logarithm of an algebraic number }
-- is a Q-subspace of Qbar closed under complex conjugation, so g in S0 forces both
-- Re g in S0 and i*(Im g) in S0, and g /= 0 makes at least one of them non-zero.
-- The reduction lemma is inlined: the platform cannot import local Solutions modules.

open Complex ComplexConjugate

namespace DiazModulus

noncomputable def cjQ : ℂ →ₐ[ℚ] ℂ :=
  (Complex.conjAe : ℂ ≃ₐ[ℝ] ℂ).toAlgHom.restrictScalars ℚ

theorem alg_conj {z : ℂ} (h : IsAlgebraic ℚ z) : IsAlgebraic ℚ (conj z) := by
  obtain ⟨p, hp0, hp⟩ := h
  refine ⟨p, hp0, ?_⟩
  have : Polynomial.aeval (cjQ z) p = cjQ (Polynomial.aeval z p) :=
    Polynomial.aeval_algHom_apply cjQ z p
  rw [show (conj z : ℂ) = cjQ z from rfl, this, hp, map_zero]

theorem alg_mul {z w : ℂ} (hz : IsAlgebraic ℚ z) (hw : IsAlgebraic ℚ w) :
    IsAlgebraic ℚ (z * w) := by
  rw [← mem_Qbar_iff] at *; exact Subfield.mul_mem _ hz hw

theorem alg_inv {z : ℂ} (hz : IsAlgebraic ℚ z) : IsAlgebraic ℚ z⁻¹ := by
  rw [← mem_Qbar_iff] at *; exact Subfield.inv_mem _ hz

theorem alg_add {z w : ℂ} (hz : IsAlgebraic ℚ z) (hw : IsAlgebraic ℚ w) :
    IsAlgebraic ℚ (z + w) := by
  rw [← mem_Qbar_iff] at *; exact Subfield.add_mem _ hz hw

theorem alg_sub {z w : ℂ} (hz : IsAlgebraic ℚ z) (hw : IsAlgebraic ℚ w) :
    IsAlgebraic ℚ (z - w) := by
  rw [← mem_Qbar_iff] at *; exact Subfield.sub_mem _ hz hw

theorem alg_div {z w : ℂ} (hz : IsAlgebraic ℚ z) (hw : IsAlgebraic ℚ w) :
    IsAlgebraic ℚ (z / w) := by
  rw [← mem_Qbar_iff] at *; exact Subfield.div_mem _ hz hw

theorem alg_two : IsAlgebraic ℚ (2 : ℂ) := by
  have h := alg_add (isAlgebraic_one (R := ℚ) (A := ℂ)) (isAlgebraic_one (R := ℚ) (A := ℂ))
  norm_num at h
  exact h

/-- `conj γ / (iπ) = -(conj (γ / (iπ)))`: conjugation flips the sign because `iπ` is purely
imaginary and `π` is real. -/
theorem conj_div_pi_I (γ : ℂ) :
    conj γ / (((Real.pi : ℝ) : ℂ) * Complex.I) = -(conj (γ / (((Real.pi : ℝ) : ℂ) * Complex.I))) := by
  rw [map_div₀]
  simp
  ring_nf

/-- **`S₀` is conjugation-stable.**  If `exp (γ/(iπ))` is algebraic then so is
`exp (conj γ/(iπ))`; explicitly it is the inverse of the conjugate. -/
theorem axis_conj {γ : ℂ}
    (h : IsAlgebraic ℚ (Complex.exp (γ / (((Real.pi : ℝ) : ℂ) * Complex.I)))) :
    IsAlgebraic ℚ (Complex.exp (conj γ / (((Real.pi : ℝ) : ℂ) * Complex.I))) := by
  rw [conj_div_pi_I, Complex.exp_neg, Complex.exp_conj]
  exact alg_inv (alg_conj h)

/-- **The axis lemma.**  If `γ` is algebraic and `γ/(iπ) ∈ ℒ`, then both `(γ.re : ℂ)` and
`γ.im * I` are algebraic and lie in `S₀` as well.  Since `γ = γ.re + γ.im * I`, at least one of
them is non-zero when `γ ≠ 0`. -/
theorem axis_split {γ : ℂ} (hγ : IsAlgebraic ℚ γ)
    (h : IsAlgebraic ℚ (Complex.exp (γ / (((Real.pi : ℝ) : ℂ) * Complex.I)))) :
    IsAlgebraic ℚ ((γ.re : ℂ)) ∧
    IsAlgebraic ℚ (Complex.exp (((γ.re : ℂ)) / (((Real.pi : ℝ) : ℂ) * Complex.I))) ∧
    IsAlgebraic ℚ (((γ.im : ℂ)) * Complex.I) ∧
    IsAlgebraic ℚ (Complex.exp ((((γ.im : ℂ)) * Complex.I) /
      (((Real.pi : ℝ) : ℂ) * Complex.I))) := by
  have hc : IsAlgebraic ℚ (conj γ) := alg_conj hγ
  have hec : IsAlgebraic ℚ (Complex.exp (conj γ / (((Real.pi : ℝ) : ℂ) * Complex.I))) :=
    axis_conj h
  -- the two coordinates, as halves
  have hre : ((γ.re : ℂ)) = (γ + conj γ) / 2 := by
    rw [Complex.add_conj]; push_cast; ring
  have him : ((γ.im : ℂ)) * Complex.I = (γ - conj γ) / 2 := by
    rw [Complex.sub_conj]; push_cast; ring
  refine ⟨by rw [hre]; exact alg_div (alg_add hγ hc) alg_two, ?_,
          by rw [him]; exact alg_div (alg_sub hγ hc) alg_two, ?_⟩
  · refine IsAlgebraic.of_pow (n := 2) two_pos ?_
    have : (Complex.exp (((γ.re : ℂ)) / (((Real.pi : ℝ) : ℂ) * Complex.I))) ^ 2
        = Complex.exp (γ / (((Real.pi : ℝ) : ℂ) * Complex.I))
          * Complex.exp (conj γ / (((Real.pi : ℝ) : ℂ) * Complex.I)) := by
      rw [← Complex.exp_add, ← Complex.exp_nat_mul]
      congr 1
      rw [hre]; ring
    rw [this]; exact alg_mul h hec
  · refine IsAlgebraic.of_pow (n := 2) two_pos ?_
    have : (Complex.exp ((((γ.im : ℂ)) * Complex.I) /
        (((Real.pi : ℝ) : ℂ) * Complex.I))) ^ 2
        = Complex.exp (γ / (((Real.pi : ℝ) : ℂ) * Complex.I))
          * (Complex.exp (conj γ / (((Real.pi : ℝ) : ℂ) * Complex.I)))⁻¹ := by
      rw [← Complex.exp_neg, ← Complex.exp_add, ← Complex.exp_nat_mul]
      congr 1
      rw [him]; ring
    rw [this]; exact alg_mul h (alg_inv hec)

/-! ## The reduction: the two children imply the parent -/

theorem recip_pi_not_log_of_axes
    (hRe : ∀ γ : ℂ, IsAlgebraic ℚ γ → γ ≠ 0 → γ.im = 0 →
      ¬ IsAlgebraic ℚ (Complex.exp (γ / (((Real.pi : ℝ) : ℂ) * Complex.I))))
    (hIm : ∀ γ : ℂ, IsAlgebraic ℚ γ → γ ≠ 0 → γ.re = 0 →
      ¬ IsAlgebraic ℚ (Complex.exp (γ / (((Real.pi : ℝ) : ℂ) * Complex.I)))) :
    ∀ γ : ℂ, IsAlgebraic ℚ γ → γ ≠ 0 →
      ¬ IsAlgebraic ℚ (Complex.exp (γ / (((Real.pi : ℝ) : ℂ) * Complex.I))) := by
  intro γ hγ hγ0 hexp
  obtain ⟨h1, h2, h3, h4⟩ := axis_split hγ hexp
  by_cases hr : ((γ.re : ℂ)) = 0
  · -- then `γ = γ.im * I` is non-zero and purely imaginary
    have hi : ((γ.im : ℂ)) * Complex.I ≠ 0 := by
      intro hz
      apply hγ0
      have : γ = ((γ.re : ℂ)) + ((γ.im : ℂ)) * Complex.I := by
        simp [Complex.ext_iff]
      rw [this, hr, hz, add_zero]
    exact hIm _ h3 hi (by simp) h4
  · exact hRe _ h1 hr (by simp) h2

/-! ## Witnesses: both halves of the split have non-empty ambient class -/

theorem witness_real : IsAlgebraic ℚ (1 : ℂ) ∧ (1 : ℂ) ≠ 0 ∧ (1 : ℂ).im = 0 :=
  ⟨isAlgebraic_one, one_ne_zero, by simp⟩

theorem witness_imag :
    IsAlgebraic ℚ Complex.I ∧ Complex.I ≠ 0 ∧ Complex.I.re = 0 := by
  refine ⟨⟨Polynomial.X ^ 2 + 1, ?_, ?_⟩, Complex.I_ne_zero, by simp⟩
  · intro h
    have := congrArg (Polynomial.coeff · 0) h
    simp at this
  · simp

end DiazModulus


open DiazModulus in
theorem solution :
    ∀ γ : ℂ, IsAlgebraic ℚ γ → γ ≠ 0 →
      ¬ IsAlgebraic ℚ (Complex.exp (γ / (((Real.pi : ℝ) : ℂ) * Complex.I))) :=
  DiazModulus.recip_pi_not_log_of_axes
    DiazModulus.recip_pi_not_log_real_gamma
    DiazModulus.recip_pi_not_log_imag_gamma
