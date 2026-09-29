-- Prove2me | solution 1 for DiazModulus.diaz_of_strong_five_exponentials
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-24T11:05:14.852933+00:00
-- url     : https://prove2.me/submissions/5a810def-3984-4cd2-8172-2fcaaa6619c4

import Mathlib
import Definitions.Def_DiazModulus
import Theorems.Thm_DiazModulus_hermite_lindemann_holds

open Complex ComplexConjugate

namespace P16_diaz_of_strong_five_exponentials

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

end P16_diaz_of_strong_five_exponentials

open P16_diaz_of_strong_five_exponentials in
theorem solution (hS5 : ∀ x₁ x₂ y₁ y₂ η α₁₁ α₁₂ α₂₁ α₂₂ β : ℂ,
      LinearIndependent ℚ ![x₁, x₂] → LinearIndependent ℚ ![y₁, y₂] →
      IsAlgebraic ℚ η → η ≠ 0 →
      IsAlgebraic ℚ α₁₁ → IsAlgebraic ℚ α₁₂ → IsAlgebraic ℚ α₂₁ → IsAlgebraic ℚ α₂₂ →
      IsAlgebraic ℚ β →
      IsAlgebraic ℚ (Complex.exp (x₁ * y₁ - α₁₁)) → IsAlgebraic ℚ (Complex.exp (x₁ * y₂ - α₁₂)) →
      IsAlgebraic ℚ (Complex.exp (x₂ * y₁ - α₂₁)) → IsAlgebraic ℚ (Complex.exp (x₂ * y₂ - α₂₂)) →
      IsAlgebraic ℚ (Complex.exp (η * x₂ / x₁ - β)) →
      x₁ * y₁ = α₁₁ ∧ x₁ * y₂ = α₁₂ ∧ x₂ * y₁ = α₂₁ ∧ x₂ * y₂ = α₂₂ ∧ η * x₂ = β * x₁) :
    DiazModulus.DiazModulusConjecture := by
  intro u hu0 hnorm he
  have hρ : IsAlgebraic ℚ (u * conj u) := by rw [rho_eq]; exact hnorm.pow 2
  have hut : Transcendental ℚ u := transc_of_exp hu0 he
  have hcut : Transcendental ℚ (conj u) := fun h => hut (by simpa using alg_conj h)
  obtain ⟨-, h12, -, -, -⟩ := hS5 1 u 1 (conj u) 1 1 0 0 (u * conj u) 0
    (li_one hut) (li_one hcut) isAlgebraic_one one_ne_zero isAlgebraic_one isAlgebraic_zero
    isAlgebraic_zero hρ isAlgebraic_zero
    (by simpa using (isAlgebraic_one : IsAlgebraic ℚ (1 : ℂ))) (by simpa using exp_conj_alg he) (by simpa using he) (by simpa using (isAlgebraic_one : IsAlgebraic ℚ (1 : ℂ))) (by simpa using he)
  exact hu0 (by simpa using h12)

#print axioms solution
