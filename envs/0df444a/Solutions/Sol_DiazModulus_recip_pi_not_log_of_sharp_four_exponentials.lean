-- Prove2me | solution 1 for DiazModulus.recip_pi_not_log_of_sharp_four_exponentials
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-24T11:05:16.605518+00:00
-- url     : https://prove2.me/submissions/c431489f-d863-4bc0-8bd2-ced53f2fcf18

import Mathlib
import Definitions.Def_DiazModulus
import Theorems.Thm_DiazModulus_hermite_lindemann_holds

open Complex ComplexConjugate

namespace P16_recip_pi_not_log_of_sharp_four_exponentials

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

/-- `1` and a transcendental number are `ℚ`-linearly independent. -/
theorem li_one {z : ℂ} (hz : Transcendental ℚ z) : LinearIndependent ℚ ![(1 : ℂ), z] := by
  rw [LinearIndependent.pair_iff]
  intro s t h
  rw [Rat.smul_def, Rat.smul_def, mul_one] at h
  by_cases ht : t = 0
  · subst ht
    simp only [Rat.cast_zero, zero_mul, add_zero] at h
    exact ⟨by exact_mod_cast h, rfl⟩
  · exfalso
    apply hz
    have htC : (t : ℂ) ≠ 0 := by exact_mod_cast ht
    have hz' : z = ((-s / t : ℚ) : ℂ) := by
      push_cast
      field_simp
      linear_combination h
    rw [hz']
    exact isAlg_rat _

end P16_recip_pi_not_log_of_sharp_four_exponentials

open P16_recip_pi_not_log_of_sharp_four_exponentials in
theorem solution (hS4 : ∀ x₁ x₂ y₁ y₂ β₁₁ β₁₂ β₂₁ β₂₂ : ℂ,
      LinearIndependent ℚ ![x₁, x₂] → LinearIndependent ℚ ![y₁, y₂] →
      IsAlgebraic ℚ β₁₁ → IsAlgebraic ℚ β₁₂ → IsAlgebraic ℚ β₂₁ → IsAlgebraic ℚ β₂₂ →
      IsAlgebraic ℚ (Complex.exp (x₁ * y₁ - β₁₁)) → IsAlgebraic ℚ (Complex.exp (x₁ * y₂ - β₁₂)) →
      IsAlgebraic ℚ (Complex.exp (x₂ * y₁ - β₂₁)) → IsAlgebraic ℚ (Complex.exp (x₂ * y₂ - β₂₂)) →
      x₁ * y₁ = β₁₁ ∧ x₁ * y₂ = β₁₂ ∧ x₂ * y₁ = β₂₁ ∧ x₂ * y₂ = β₂₂) :
    ∀ γ : ℂ, IsAlgebraic ℚ γ → γ ≠ 0 →
      ¬ IsAlgebraic ℚ (Complex.exp (γ / (((Real.pi : ℝ) : ℂ) * Complex.I))) := by
  intro γ hγ hγ0 he
  have hp0 := pI_ne_zero
  have hl0 : γ / (((Real.pi : ℝ) : ℂ) * Complex.I) ≠ 0 := div_ne_zero hγ0 hp0
  have hlt : Transcendental ℚ (γ / (((Real.pi : ℝ) : ℂ) * Complex.I)) := transc_of_exp hl0 he
  have hprod : γ / (((Real.pi : ℝ) : ℂ) * Complex.I) * (((Real.pi : ℝ) : ℂ) * Complex.I) = γ :=
    div_mul_cancel₀ γ hp0
  obtain ⟨-, h12, -, -⟩ := hS4 1 (γ / (((Real.pi : ℝ) : ℂ) * Complex.I)) 1
    (((Real.pi : ℝ) : ℂ) * Complex.I) 1 0 0 γ
    (li_one hlt) (li_one pI_transc) isAlgebraic_one isAlgebraic_zero isAlgebraic_zero hγ
    (by simpa using (isAlgebraic_one : IsAlgebraic ℚ (1 : ℂ))) (by simpa using exp_pI_alg) (by simpa using he) (by rw [hprod]; simpa using (isAlgebraic_one : IsAlgebraic ℚ (1 : ℂ)))
  exact hp0 (by simpa using h12)

#print axioms solution
