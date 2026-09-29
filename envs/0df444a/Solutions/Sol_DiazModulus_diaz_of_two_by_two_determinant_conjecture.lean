-- Prove2me | solution 1 for DiazModulus.diaz_of_two_by_two_determinant_conjecture
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-24T11:05:18.211558+00:00
-- url     : https://prove2.me/submissions/bfc75273-74e5-4eaf-92a1-9b83fe15975a

import Mathlib
import Definitions.Def_DiazModulus
import Theorems.Thm_DiazModulus_hermite_lindemann_holds

open Complex ComplexConjugate

namespace P16_diaz_of_two_by_two_determinant_conjecture

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

end P16_diaz_of_two_by_two_determinant_conjecture

open P16_diaz_of_two_by_two_determinant_conjecture in
theorem solution (hW : ∀ a b c d : ℂ, a ∈ DiazModulus.LogAlgTilde → b ∈ DiazModulus.LogAlgTilde → c ∈ DiazModulus.LogAlgTilde →
      d ∈ DiazModulus.LogAlgTilde →
      (∀ s t : ℂ, s ∈ DiazModulus.Qbar → t ∈ DiazModulus.Qbar → s * a + t * c ∈ DiazModulus.Qbar → s * b + t * d ∈ DiazModulus.Qbar →
        s = 0 ∧ t = 0) →
      (∀ s t : ℂ, s ∈ DiazModulus.Qbar → t ∈ DiazModulus.Qbar → s * a + t * b ∈ DiazModulus.Qbar → s * c + t * d ∈ DiazModulus.Qbar →
        s = 0 ∧ t = 0) →
      a * d - b * c ∉ DiazModulus.LogAlgTilde) :
    DiazModulus.DiazModulusConjecture := by
  intro u hu0 hnorm he
  have hρ : IsAlgebraic ℚ (u * conj u) := by rw [rho_eq]; exact hnorm.pow 2
  have hut : Transcendental ℚ u := transc_of_exp hu0 he
  have hcut : Transcendental ℚ (conj u) := fun h => hut (by simpa using alg_conj h)
  have hrQ : ((‖u‖ : ℝ) : ℂ) ∈ DiazModulus.Qbar := alg_iff_mem.1 hnorm
  -- the rows of `(H; I₂)` and the columns of `(I₂, H)` are `Q̄`-independent, `H` being symmetric
  have hind : ∀ s t : ℂ, s ∈ DiazModulus.Qbar → t ∈ DiazModulus.Qbar →
      s * u + t * ((‖u‖ : ℝ) : ℂ) ∈ DiazModulus.Qbar →
      s * ((‖u‖ : ℝ) : ℂ) + t * conj u ∈ DiazModulus.Qbar → s = 0 ∧ t = 0 := by
    intro s t hs ht h1 h2
    have hsu : s * u ∈ DiazModulus.Qbar := by
      have := sub_mem h1 (mul_mem ht hrQ)
      simpa using this
    have htu : t * conj u ∈ DiazModulus.Qbar := by
      have := sub_mem h2 (mul_mem hs hrQ)
      simpa using this
    constructor
    · by_contra hs0
      exact hut (alg_of_mul hs hs0 hsu)
    · by_contra ht0
      exact hcut (alg_of_mul ht ht0 htu)
  apply hW u ((‖u‖ : ℝ) : ℂ) ((‖u‖ : ℝ) : ℂ) (conj u) (mem_tilde_of_log he)
    (mem_tilde_of_alg hnorm) (mem_tilde_of_alg hnorm) (mem_tilde_of_log (exp_conj_alg he))
    hind hind
  have hdet : u * conj u - ((‖u‖ : ℝ) : ℂ) * ((‖u‖ : ℝ) : ℂ) = 0 := by
    rw [rho_eq]
    ring
  rw [hdet]
  exact zero_mem _

#print axioms solution
