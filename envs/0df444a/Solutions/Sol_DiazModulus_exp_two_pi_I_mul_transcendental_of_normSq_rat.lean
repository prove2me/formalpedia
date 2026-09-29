-- Prove2me | solution 1 for DiazModulus.exp_two_pi_I_mul_transcendental_of_normSq_rat
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-24T18:08:55.91798+00:00
-- url     : https://prove2.me/submissions/fe002d5f-ae82-41af-ae23-78eeebaa3bf0

import Mathlib
import Theorems.Thm_DiazModulus_log_pair_algebraicIndependent_of_mul_eq_rat_pi_sq
import Theorems.Thm_Transcendence_trdeg_adjoin_le_one_of_isAlgebraic_adjoin

open ComplexConjugate

namespace P17_a4

/-! Diaz's property (4-1) when `τ` is algebraic over `ℚ(π)`: a consequence of Proposition 1
(J. Théor. Nombres Bordeaux 9 (1997), p. 238). Write `T = 2πi` and `l₁ = T τ`. If `exp l₁` were
algebraic, Proposition 1 applied to `l₁` and `l₂ = conj l₁` (with `l₁ l₂ = 4 c π²`) would make
`l₁` and `T` algebraically independent over `ℚ`; but both are algebraic over `ℚ[π]`. -/

/-- Complex conjugation as a `ℚ`-algebra map. -/
noncomputable def cjQ : ℂ →ₐ[ℚ] ℂ :=
  (Complex.conjAe : ℂ ≃ₐ[ℝ] ℂ).toAlgHom.restrictScalars ℚ

theorem alg_conj {z : ℂ} (h : IsAlgebraic ℚ z) : IsAlgebraic ℚ (conj z) := by
  obtain ⟨p, hp0, hp⟩ := h
  refine ⟨p, hp0, ?_⟩
  have : Polynomial.aeval (cjQ z) p = cjQ (Polynomial.aeval z p) :=
    Polynomial.aeval_algHom_apply cjQ z p
  rw [show (conj z : ℂ) = cjQ z from rfl, this, hp, map_zero]

theorem exp_conj_alg {w : ℂ} (hw : IsAlgebraic ℚ (Complex.exp w)) :
    IsAlgebraic ℚ (Complex.exp (conj w)) := by
  rw [Complex.exp_conj]; exact alg_conj hw

theorem pi_ne_zero' : ((Real.pi : ℝ) : ℂ) ≠ 0 :=
  Complex.ofReal_ne_zero.2 Real.pi_ne_zero

theorem T_ne_zero : 2 * ((Real.pi : ℝ) : ℂ) * Complex.I ≠ 0 :=
  mul_ne_zero (mul_ne_zero two_ne_zero pi_ne_zero') Complex.I_ne_zero

/-- `l₁ = 2πiτ` is not a rational multiple of `2πi`, since `τ` is not real. -/
theorem hroot_of_im (τ : ℂ) (hτ : τ.im ≠ 0) (q : ℚ) :
    2 * ((Real.pi : ℝ) : ℂ) * Complex.I * τ ≠
      (q : ℂ) * (2 * ((Real.pi : ℝ) : ℂ) * Complex.I) := by
  intro h
  apply hτ
  have h' : (2 * ((Real.pi : ℝ) : ℂ) * Complex.I) * τ =
      (2 * ((Real.pi : ℝ) : ℂ) * Complex.I) * (q : ℂ) := by
    rw [h]; ring
  rw [mul_left_cancel₀ T_ne_zero h']
  simp

theorem c_ne_zero (τ : ℂ) (hτ : τ.im ≠ 0) (c : ℚ) (hc : τ * conj τ = (c : ℂ)) : c ≠ 0 := by
  intro h0
  apply hτ
  rw [h0, Rat.cast_zero, mul_eq_zero, map_eq_zero, or_self] at hc
  rw [hc]
  simp

theorem conj_T :
    conj (2 * ((Real.pi : ℝ) : ℂ) * Complex.I) = -(2 * ((Real.pi : ℝ) : ℂ) * Complex.I) := by
  rw [map_mul, map_mul, Complex.conj_ofReal, Complex.conj_I, map_ofNat]
  ring

theorem prod_eq (τ : ℂ) (c : ℚ) (hc : τ * conj τ = (c : ℂ)) :
    (2 * ((Real.pi : ℝ) : ℂ) * Complex.I * τ) * conj (2 * ((Real.pi : ℝ) : ℂ) * Complex.I * τ)
      = ((4 * c : ℚ) : ℂ) * ((Real.pi : ℝ) : ℂ) ^ 2 := by
  rw [map_mul conj (2 * ((Real.pi : ℝ) : ℂ) * Complex.I) τ, conj_T]
  have : (2 * ((Real.pi : ℝ) : ℂ) * Complex.I * τ) *
      (-(2 * ((Real.pi : ℝ) : ℂ) * Complex.I) * conj τ)
      = -(4 * Complex.I ^ 2) * ((Real.pi : ℝ) : ℂ) ^ 2 * (τ * conj τ) := by ring
  rw [this, hc, Complex.I_sq]
  push_cast
  ring

/-- The complex numbers algebraic over `ℚ[x]`, as a `ℚ`-subalgebra of `ℂ`. -/
noncomputable def E (x : ℂ) : Subalgebra ℚ ℂ :=
  (Subalgebra.algebraicClosure ↥(Algebra.adjoin ℚ ({x} : Set ℂ)) ℂ).restrictScalars ℚ

theorem mem_E_iff {x z : ℂ} : z ∈ E x ↔ IsAlgebraic ↥(Algebra.adjoin ℚ ({x} : Set ℂ)) z :=
  Iff.rfl

theorem mem_E_of_alg {x z : ℂ} (h : IsAlgebraic ℚ z) : z ∈ E x :=
  h.extendScalars (algebraMap ℚ ↥(Algebra.adjoin ℚ ({x} : Set ℂ))).injective

theorem self_mem_E (x : ℂ) : x ∈ E x := by
  rw [mem_E_iff]
  have h : x = algebraMap ↥(Algebra.adjoin ℚ ({x} : Set ℂ)) ℂ
      ⟨x, Algebra.subset_adjoin rfl⟩ := rfl
  rw [h]
  exact isAlgebraic_algebraMap _

theorem rat_alg (r : ℚ) : IsAlgebraic ℚ (r : ℂ) :=
  isAlgebraic_algebraMap r

/-- `i` is algebraic over `ℚ`: its square is `-1`. -/
theorem I_alg : IsAlgebraic ℚ Complex.I := by
  refine IsAlgebraic.of_pow (n := 2) (by norm_num) ?_
  rw [Complex.I_sq]
  simpa using rat_alg (-1)

theorem two_alg : IsAlgebraic ℚ (2 : ℂ) := by
  simpa using rat_alg 2

theorem T_mem_E : 2 * ((Real.pi : ℝ) : ℂ) * Complex.I ∈ E ((Real.pi : ℝ) : ℂ) :=
  mul_mem (mul_mem (mem_E_of_alg two_alg) (self_mem_E _)) (mem_E_of_alg I_alg)

/-- Two complex numbers algebraic over `ℚ[x]` are never algebraically independent over `ℚ`. -/
theorem not_indep (a b x : ℂ) (ha : a ∈ E x) (hb : b ∈ E x) :
    ¬ AlgebraicIndependent ℚ ![a, b] := by
  intro hind
  have htr : Algebra.trdeg ℚ ↥(Algebra.adjoin ℚ ({a, b} : Set ℂ)) ≤ 1 := by
    apply Transcendence.trdeg_adjoin_le_one_of_isAlgebraic_adjoin x
    intro s hs
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hs
    rcases hs with h | h
    · rw [h]; exact mem_E_iff.1 ha
    · rw [h]; exact mem_E_iff.1 hb
  have hmem : ∀ i, ![a, b] i ∈ Algebra.adjoin ℚ ({a, b} : Set ℂ) := by
    intro i
    fin_cases i
    · exact Algebra.subset_adjoin (by simp)
    · exact Algebra.subset_adjoin (by simp)
  let y : Fin 2 → ↥(Algebra.adjoin ℚ ({a, b} : Set ℂ)) := fun i => ⟨![a, b] i, hmem i⟩
  have hy : AlgebraicIndependent ℚ y :=
    AlgebraicIndependent.of_comp (Algebra.adjoin ℚ ({a, b} : Set ℂ)).val hind
  have h2 := hy.cardinalMk_le_trdeg.trans htr
  rw [Cardinal.mk_fin] at h2
  have h3 : (2 : ℕ) ≤ 1 := by exact_mod_cast h2
  omega

theorem main (τ : ℂ) (hτ : τ.im ≠ 0)
    (halg : IsAlgebraic ↥(Algebra.adjoin ℚ ({((Real.pi : ℝ) : ℂ)} : Set ℂ)) τ)
    (c : ℚ) (hc : τ * conj τ = (c : ℂ)) :
    Transcendental ℚ (Complex.exp (2 * ((Real.pi : ℝ) : ℂ) * Complex.I * τ)) := by
  intro hexp
  have hc4 : (4 * c : ℚ) ≠ 0 := mul_ne_zero (by norm_num) (c_ne_zero τ hτ c hc)
  obtain ⟨-, hind⟩ := DiazModulus.log_pair_algebraicIndependent_of_mul_eq_rat_pi_sq
    (2 * ((Real.pi : ℝ) : ℂ) * Complex.I * τ) (conj (2 * ((Real.pi : ℝ) : ℂ) * Complex.I * τ))
    hexp (exp_conj_alg hexp) (hroot_of_im τ hτ) (4 * c) hc4 (prod_eq τ c hc)
  have hτE : τ ∈ E ((Real.pi : ℝ) : ℂ) := mem_E_iff.2 halg
  exact not_indep _ _ ((Real.pi : ℝ) : ℂ) (mul_mem T_mem_E hτE) T_mem_E hind

end P17_a4

open P17_a4 in
theorem solution (τ : ℂ) (hτ : τ.im ≠ 0)
    (halg : IsAlgebraic ↥(Algebra.adjoin ℚ ({((Real.pi : ℝ) : ℂ)} : Set ℂ)) τ)
    (c : ℚ) (hc : τ * conj τ = (c : ℂ)) :
    Transcendental ℚ (Complex.exp (2 * ((Real.pi : ℝ) : ℂ) * Complex.I * τ)) := by
  exact main τ hτ halg c hc

#print axioms solution
