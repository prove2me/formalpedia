-- Prove2me | solution 2 for DiazModulus.recip_pi_not_log
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-13T10:45:37.631491+00:00
-- url     : https://prove2.me/submissions/d0d9f756-9322-45b7-afab-a58093e7c16e
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_DiazModulus
import Theorems.Thm_DiazModulus_recip_pi_not_log_real_gamma
import Theorems.Thm_DiazModulus_recip_pi_not_log_imag_gamma

open Complex ComplexConjugate

-- The two children's hypotheses are NOT complementary: the real and imaginary axes do not
-- cover the non-zero algebraic numbers.  What makes them suffice is that
--   S₀ = {γ ∈ Q̄ : γ/(iπ) ∈ ℒ}
-- is closed under conj: conj(iπ) = -iπ, so conj γ/(iπ) = -conj(γ/(iπ)) and
-- exp(conj γ/(iπ)) = (conj (exp (γ/(iπ))))⁻¹.  Hence Re γ and i·Im γ stay in S₀ (their
-- exponentials are square roots of exp(γ/(iπ))·exp(conj γ/(iπ)) and its inverse), and
-- γ ≠ 0 forces one of them to be non-zero.
open DiazModulus in
theorem solution :
    ∀ γ : ℂ, IsAlgebraic ℚ γ → γ ≠ 0 →
      ¬ IsAlgebraic ℚ (Complex.exp (γ / (((Real.pi : ℝ) : ℂ) * Complex.I))) := by
  let cjQ : ℂ →ₐ[ℚ] ℂ := (Complex.conjAe : ℂ ≃ₐ[ℝ] ℂ).toAlgHom.restrictScalars ℚ
  have alg_conj : ∀ {z : ℂ}, IsAlgebraic ℚ z → IsAlgebraic ℚ (conj z) := by
    intro z h
    obtain ⟨p, hp0, hp⟩ := h
    refine ⟨p, hp0, ?_⟩
    have : Polynomial.aeval (cjQ z) p = cjQ (Polynomial.aeval z p) :=
      Polynomial.aeval_algHom_apply cjQ z p
    rw [show (conj z : ℂ) = cjQ z from rfl, this, hp, map_zero]
  have alg_mul : ∀ {z w : ℂ}, IsAlgebraic ℚ z → IsAlgebraic ℚ w → IsAlgebraic ℚ (z * w) := by
    intro z w hz hw; rw [← mem_Qbar_iff] at *; exact Subfield.mul_mem _ hz hw
  have alg_inv : ∀ {z : ℂ}, IsAlgebraic ℚ z → IsAlgebraic ℚ z⁻¹ := by
    intro z hz; rw [← mem_Qbar_iff] at *; exact Subfield.inv_mem _ hz
  have alg_add : ∀ {z w : ℂ}, IsAlgebraic ℚ z → IsAlgebraic ℚ w → IsAlgebraic ℚ (z + w) := by
    intro z w hz hw; rw [← mem_Qbar_iff] at *; exact Subfield.add_mem _ hz hw
  have alg_sub : ∀ {z w : ℂ}, IsAlgebraic ℚ z → IsAlgebraic ℚ w → IsAlgebraic ℚ (z - w) := by
    intro z w hz hw; rw [← mem_Qbar_iff] at *; exact Subfield.sub_mem _ hz hw
  have alg_div : ∀ {z w : ℂ}, IsAlgebraic ℚ z → IsAlgebraic ℚ w → IsAlgebraic ℚ (z / w) := by
    intro z w hz hw; rw [← mem_Qbar_iff] at *; exact Subfield.div_mem _ hz hw
  have alg_two : IsAlgebraic ℚ (2 : ℂ) := by
    have h := alg_add (isAlgebraic_one (R := ℚ) (A := ℂ)) (isAlgebraic_one (R := ℚ) (A := ℂ))
    norm_num at h
    exact h
  have conj_div : ∀ γ : ℂ, conj γ / (((Real.pi : ℝ) : ℂ) * Complex.I)
      = -(conj (γ / (((Real.pi : ℝ) : ℂ) * Complex.I))) := by
    intro γ; rw [map_div₀]; simp; ring_nf
  intro γ hγ hγ0 hexp
  have hc : IsAlgebraic ℚ (conj γ) := alg_conj hγ
  have hec : IsAlgebraic ℚ (Complex.exp (conj γ / (((Real.pi : ℝ) : ℂ) * Complex.I))) := by
    rw [conj_div, Complex.exp_neg, Complex.exp_conj]
    exact alg_inv (alg_conj hexp)
  have hre : ((γ.re : ℂ)) = (γ + conj γ) / 2 := by rw [Complex.add_conj]; push_cast; ring
  have him : ((γ.im : ℂ)) * Complex.I = (γ - conj γ) / 2 := by
    rw [Complex.sub_conj]; push_cast; ring
  have h1 : IsAlgebraic ℚ ((γ.re : ℂ)) := by rw [hre]; exact alg_div (alg_add hγ hc) alg_two
  have h3 : IsAlgebraic ℚ (((γ.im : ℂ)) * Complex.I) := by
    rw [him]; exact alg_div (alg_sub hγ hc) alg_two
  have h2 : IsAlgebraic ℚ
      (Complex.exp (((γ.re : ℂ)) / (((Real.pi : ℝ) : ℂ) * Complex.I))) := by
    refine IsAlgebraic.of_pow (n := 2) two_pos ?_
    have e : (Complex.exp (((γ.re : ℂ)) / (((Real.pi : ℝ) : ℂ) * Complex.I))) ^ 2
        = Complex.exp (γ / (((Real.pi : ℝ) : ℂ) * Complex.I))
          * Complex.exp (conj γ / (((Real.pi : ℝ) : ℂ) * Complex.I)) := by
      rw [← Complex.exp_add, ← Complex.exp_nat_mul]; congr 1; rw [hre]; ring
    rw [e]; exact alg_mul hexp hec
  have h4 : IsAlgebraic ℚ (Complex.exp ((((γ.im : ℂ)) * Complex.I) /
      (((Real.pi : ℝ) : ℂ) * Complex.I))) := by
    refine IsAlgebraic.of_pow (n := 2) two_pos ?_
    have e : (Complex.exp ((((γ.im : ℂ)) * Complex.I) /
        (((Real.pi : ℝ) : ℂ) * Complex.I))) ^ 2
        = Complex.exp (γ / (((Real.pi : ℝ) : ℂ) * Complex.I))
          * (Complex.exp (conj γ / (((Real.pi : ℝ) : ℂ) * Complex.I)))⁻¹ := by
      rw [← Complex.exp_neg, ← Complex.exp_add, ← Complex.exp_nat_mul]; congr 1
      rw [him]; ring
    rw [e]; exact alg_mul hexp (alg_inv hec)
  by_cases hr : ((γ.re : ℂ)) = 0
  · have hi : ((γ.im : ℂ)) * Complex.I ≠ 0 := by
      intro hz
      apply hγ0
      have : γ = ((γ.re : ℂ)) + ((γ.im : ℂ)) * Complex.I := by simp
      rw [this, hr, hz, add_zero]
    exact DiazModulus.recip_pi_not_log_imag_gamma _ h3 hi (by simp) h4
  · exact DiazModulus.recip_pi_not_log_real_gamma _ h1 hr (by simp) h2
