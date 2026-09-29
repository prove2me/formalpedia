-- Prove2me | solution 1 for DiazModulus.recip_pi_not_log_of_two_by_two_determinant_conjecture
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-24T11:05:21.758589+00:00
-- url     : https://prove2.me/submissions/d4b2d63d-c9b6-4d1d-898d-0ca4c7e28b30

import Mathlib
import Definitions.Def_DiazModulus
import Theorems.Thm_DiazModulus_hermite_lindemann_holds

open Complex ComplexConjugate

namespace P16_recip_pi_not_log_of_two_by_two_determinant_conjecture

theorem alg_iff_mem {z : ℂ} : IsAlgebraic ℚ z ↔ z ∈ DiazModulus.Qbar :=
  DiazModulus.mem_Qbar_iff.symm

theorem isAlg_rat (r : ℚ) : IsAlgebraic ℚ (r : ℂ) :=
  isAlgebraic_algebraMap r

noncomputable def cjQ : ℂ →ₐ[ℚ] ℂ :=
  (Complex.conjAe : ℂ ≃ₐ[ℝ] ℂ).toAlgHom.restrictScalars ℚ

theorem alg_conj {z : ℂ} (h : IsAlgebraic ℚ z) : IsAlgebraic ℚ (conj z) := by
  obtain ⟨p, hp0, hp⟩ := h
  refine ⟨p, hp0, ?_⟩
  have : Polynomial.aeval (cjQ z) p = cjQ (Polynomial.aeval z p) :=
    Polynomial.aeval_algHom_apply cjQ z p
  rw [show (conj z : ℂ) = cjQ z from rfl, this, hp, map_zero]

/-- `ℒ` is stable under conjugation. -/
theorem exp_conj_alg {w : ℂ} (hw : IsAlgebraic ℚ (Complex.exp w)) :
    IsAlgebraic ℚ (Complex.exp (conj w)) := by
  rw [Complex.exp_conj]; exact alg_conj hw

/-- Hermite–Lindemann in the form used here: a non-zero logarithm of an algebraic number is
transcendental. -/
theorem transc_of_exp {z : ℂ} (hz : z ≠ 0) (he : IsAlgebraic ℚ (Complex.exp z)) :
    Transcendental ℚ z := fun h => DiazModulus.hermite_lindemann_holds z hz h he

theorem rho_eq (u : ℂ) : u * conj u = ((‖u‖ : ℝ) : ℂ) ^ 2 := by
  rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]; push_cast; ring

theorem pI_ne_zero : ((Real.pi : ℝ) : ℂ) * Complex.I ≠ 0 :=
  mul_ne_zero (Complex.ofReal_ne_zero.2 Real.pi_ne_zero) Complex.I_ne_zero

theorem exp_pI_alg : IsAlgebraic ℚ (Complex.exp (((Real.pi : ℝ) : ℂ) * Complex.I)) := by
  rw [Complex.exp_pi_mul_I]; simpa using isAlg_rat (-1)

theorem conj_pI :
    conj (((Real.pi : ℝ) : ℂ) * Complex.I) = -(((Real.pi : ℝ) : ℂ) * Complex.I) := by
  rw [map_mul, Complex.conj_ofReal, Complex.conj_I]; ring

/-- `iπ` is transcendental, by Hermite–Lindemann, since `exp (iπ) = -1`. -/
theorem pI_transc : Transcendental ℚ (((Real.pi : ℝ) : ℂ) * Complex.I) :=
  transc_of_exp pI_ne_zero exp_pI_alg

theorem mem_tilde_of_log {z : ℂ} (h : IsAlgebraic ℚ (Complex.exp z)) :
    z ∈ DiazModulus.LogAlgTilde :=
  Submodule.subset_span (Set.mem_insert_of_mem _ h)

theorem one_mem_tilde : (1 : ℂ) ∈ DiazModulus.LogAlgTilde :=
  Submodule.subset_span (Set.mem_insert _ _)

theorem mem_tilde_of_alg {z : ℂ} (h : IsAlgebraic ℚ z) : z ∈ DiazModulus.LogAlgTilde := by
  have hs := Submodule.smul_mem DiazModulus.LogAlgTilde
    (⟨z, alg_iff_mem.1 h⟩ : ↥DiazModulus.Qbar) one_mem_tilde
  have he : (⟨z, alg_iff_mem.1 h⟩ : ↥DiazModulus.Qbar) • (1 : ℂ) = z := by
    rw [Algebra.smul_def, mul_one]; rfl
  rwa [he] at hs

/-- From `s z ∈ Q̄` with `s ∈ Q̄`, `s ≠ 0`, the number `z` is algebraic. -/
theorem alg_of_mul {s z : ℂ} (hs : s ∈ DiazModulus.Qbar) (hs0 : s ≠ 0)
    (h : s * z ∈ DiazModulus.Qbar) : IsAlgebraic ℚ z := by
  rw [alg_iff_mem]
  have : z = s⁻¹ * (s * z) := by field_simp
  rw [this]
  exact mul_mem (inv_mem hs) h

end P16_recip_pi_not_log_of_two_by_two_determinant_conjecture

open P16_recip_pi_not_log_of_two_by_two_determinant_conjecture in
theorem solution (hW : ∀ a b c d : ℂ, a ∈ DiazModulus.LogAlgTilde → b ∈ DiazModulus.LogAlgTilde → c ∈ DiazModulus.LogAlgTilde →
      d ∈ DiazModulus.LogAlgTilde →
      (∀ s t : ℂ, s ∈ DiazModulus.Qbar → t ∈ DiazModulus.Qbar → s * a + t * c ∈ DiazModulus.Qbar → s * b + t * d ∈ DiazModulus.Qbar →
        s = 0 ∧ t = 0) →
      (∀ s t : ℂ, s ∈ DiazModulus.Qbar → t ∈ DiazModulus.Qbar → s * a + t * b ∈ DiazModulus.Qbar → s * c + t * d ∈ DiazModulus.Qbar →
        s = 0 ∧ t = 0) →
      a * d - b * c ∉ DiazModulus.LogAlgTilde) :
    ∀ γ : ℂ, IsAlgebraic ℚ γ → γ ≠ 0 →
      ¬ IsAlgebraic ℚ (Complex.exp (γ / (((Real.pi : ℝ) : ℂ) * Complex.I))) := by
  intro γ hγ hγ0 he
  have hp0 := pI_ne_zero
  have hl0 : γ / (((Real.pi : ℝ) : ℂ) * Complex.I) ≠ 0 := div_ne_zero hγ0 hp0
  have hlt : Transcendental ℚ (γ / (((Real.pi : ℝ) : ℂ) * Complex.I)) := transc_of_exp hl0 he
  have hprod : γ / (((Real.pi : ℝ) : ℂ) * Complex.I) * (((Real.pi : ℝ) : ℂ) * Complex.I) = γ :=
    div_mul_cancel₀ γ hp0
  have hγQ : γ ∈ DiazModulus.Qbar := alg_iff_mem.1 hγ
  have hoQ : (1 : ℂ) ∈ DiazModulus.Qbar := one_mem _
  apply hW 1 (((Real.pi : ℝ) : ℂ) * Complex.I) (γ / (((Real.pi : ℝ) : ℂ) * Complex.I)) γ
    one_mem_tilde (mem_tilde_of_log exp_pI_alg) (mem_tilde_of_log he) (mem_tilde_of_alg hγ)
  · -- rows `(1, iπ)` and `(λ, γ)`: from `s iπ + t γ ∈ Q̄` get `s = 0`, then `t λ ∈ Q̄` gives `t = 0`
    intro s t hs ht h1 h2
    have hsp : s * (((Real.pi : ℝ) : ℂ) * Complex.I) ∈ DiazModulus.Qbar := by
      have := sub_mem h2 (mul_mem ht hγQ)
      simpa using this
    have hs0 : s = 0 := by
      by_contra hs0
      exact pI_transc (alg_of_mul hs hs0 hsp)
    subst hs0
    refine ⟨rfl, ?_⟩
    by_contra ht0
    exact hlt (alg_of_mul ht ht0 (by simpa using h1))
  · -- columns `(1, λ)` and `(iπ, γ)`: from `s + t iπ ∈ Q̄` get `t = 0`, then `s λ ∈ Q̄` gives `s = 0`
    intro s t hs ht h1 h2
    have htp : t * (((Real.pi : ℝ) : ℂ) * Complex.I) ∈ DiazModulus.Qbar := by
      have := sub_mem h1 (mul_mem hs hoQ)
      simpa using this
    have ht0 : t = 0 := by
      by_contra ht0
      exact pI_transc (alg_of_mul ht ht0 htp)
    subst ht0
    refine ⟨?_, rfl⟩
    by_contra hs0
    exact hlt (alg_of_mul hs hs0 (by simpa using h2))
  have hdet : 1 * γ - (((Real.pi : ℝ) : ℂ) * Complex.I) *
      (γ / (((Real.pi : ℝ) : ℂ) * Complex.I)) = 0 := by
    rw [mul_div_cancel₀ γ hp0]
    ring
  rw [hdet]
  exact zero_mem _

#print axioms solution
