-- Prove2me | solution 1 for DiazModulus.log_two_pi_dependent_forces_transcendence
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-24T11:05:09.856495+00:00
-- url     : https://prove2.me/submissions/3dc0a92b-21d5-4d69-9729-0715823f2690

import Mathlib
import Definitions.Def_DiazModulus
import Theorems.Thm_DiazModulus_geometric_triple_not_logs
import Theorems.Thm_DiazModulus_hermite_lindemann_holds

open Complex ComplexConjugate

namespace P16_log_two_pi_dependent_forces_transcendence

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

/-- If every element of a `ℚ`-subalgebra `B ⊆ ℂ` is algebraic over `ℚ[x]` for one `x ∈ B`,
then `B` has transcendence degree at most one over `ℚ`. -/
theorem trdeg_le_one_of_adjoin_singleton
    {B : Subalgebra ℚ ℂ} {x : ℂ} (hxB : x ∈ B)
    (halg : ∀ y ∈ B, IsAlgebraic ↥(Algebra.adjoin ℚ ({x} : Set ℂ)) y) :
    Algebra.trdeg ℚ ↥B ≤ 1 := by
  set x' : (↥B) := ⟨x, hxB⟩ with hx'
  have hmap : Subalgebra.map B.val (Algebra.adjoin ℚ ({x'} : Set ↥B))
      = Algebra.adjoin ℚ ({x} : Set ℂ) := by
    rw [AlgHom.map_adjoin]
    congr 1
    simp [hx']
  let e : ↥(Algebra.adjoin ℚ ({x'} : Set ↥B)) ≃ₐ[ℚ] ↥(Algebra.adjoin ℚ ({x} : Set ℂ)) :=
    (Subalgebra.equivMapOfInjective _ B.val Subtype.val_injective).trans
      (Subalgebra.equivOfEq _ _ hmap)
  have : Algebra.IsAlgebraic ↥(Algebra.adjoin ℚ ({x'} : Set ↥B)) ↥B := by
    constructor
    intro y
    refine IsAlgebraic.of_ringHom_of_comp_eq (f := (e : _ →+* _))
      (g := (B.val : ↥B →+* ℂ)) (halg y y.2) e.surjective Subtype.val_injective ?_
    ext c
    rfl
  simpa using Algebra.IsAlgebraic.trdeg_le_cardinalMk ℚ ({x'} : Set ↥B)

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

theorem mem_E_of_mul {x a z : ℂ} (ha0 : a ≠ 0) (ha : a ∈ E x) (h : a * z ∈ E x) :
    z ∈ E x := by
  rw [mem_E_iff] at h ⊢
  exact IsAlgebraic.of_mul (mem_nonZeroDivisors_of_ne_zero ha0) (mem_E_iff.1 ha) h

theorem mem_E_of_sq {x z : ℂ} (h : z ^ 2 ∈ E x) : z ∈ E x :=
  (mem_E_iff.1 h).of_pow (by norm_num)

/-- Any `ℚ`-subalgebra of `E x` has transcendence degree at most one. -/
theorem trdeg_le_one_of_le_E {B : Subalgebra ℚ ℂ} {x : ℂ} (h : B ≤ E x) :
    Algebra.trdeg ℚ ↥B ≤ 1 :=
  (trdeg_le_of_injective (Subalgebra.inclusion h) (Subalgebra.inclusion_injective h)).trans
    (trdeg_le_one_of_adjoin_singleton (self_mem_E x) (fun _ hy => hy))

/-- The geometric triple `(w, w z, w z²)` with `w = l₂`, `z = l₁ / l₂`, and with the roles of
`l₁, l₂` exchanged; both lie in `E l₂`. -/
theorem core (l₁ l₂ : ℂ)
    (h₁ : IsAlgebraic ℚ (Complex.exp l₁)) (h₂ : IsAlgebraic ℚ (Complex.exp l₂))
    (hl₂ : l₂ ≠ 0) (hind : ∀ q : ℚ, l₁ ≠ (q : ℂ) * l₂) (h1E : l₁ ∈ E l₂) :
    Transcendental ℚ (Complex.exp (l₁ ^ 2 / l₂)) ∧
      Transcendental ℚ (Complex.exp (l₂ ^ 2 / l₁)) := by
  have hl₁ : l₁ ≠ 0 := by
    have := hind 0
    simpa using this
  have h2E : l₂ ∈ E l₂ := self_mem_E l₂
  constructor
  · intro h
    have hzE : l₁ / l₂ ∈ E l₂ :=
      mem_E_of_mul hl₂ h2E (by rw [mul_div_cancel₀ l₁ hl₂]; exact h1E)
    have htr : Algebra.trdeg ℚ ↥(Algebra.adjoin ℚ ({l₂, l₁ / l₂} : Set ℂ)) ≤ 1 := by
      refine trdeg_le_one_of_le_E (x := l₂) (Algebra.adjoin_le ?_)
      intro z hz
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
      rcases hz with h | h <;> rw [h] <;> assumption
    have hz : ∀ q : ℚ, l₁ / l₂ ≠ (q : ℂ) := by
      intro q hq
      apply hind q
      rw [div_eq_iff hl₂] at hq
      exact hq
    have e1 : l₂ * (l₁ / l₂) = l₁ := mul_div_cancel₀ l₁ hl₂
    have e2 : l₂ * (l₁ / l₂) ^ 2 = l₁ ^ 2 / l₂ := by field_simp
    exact DiazModulus.geometric_triple_not_logs l₂ (l₁ / l₂) hl₂ hz htr
      ⟨h₂, by rw [e1]; exact h₁, by rw [e2]; exact h⟩
  · intro h
    have hzE : l₂ / l₁ ∈ E l₂ :=
      mem_E_of_mul hl₁ h1E (by rw [mul_div_cancel₀ l₂ hl₁]; exact h2E)
    have htr : Algebra.trdeg ℚ ↥(Algebra.adjoin ℚ ({l₁, l₂ / l₁} : Set ℂ)) ≤ 1 := by
      refine trdeg_le_one_of_le_E (x := l₂) (Algebra.adjoin_le ?_)
      intro z hz
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
      rcases hz with h | h <;> rw [h] <;> assumption
    have hz : ∀ q : ℚ, l₂ / l₁ ≠ (q : ℂ) := by
      intro q hq
      rw [div_eq_iff hl₁] at hq
      have hq0 : (q : ℂ) ≠ 0 := by
        intro h0
        rw [h0, zero_mul] at hq
        exact hl₂ hq
      apply hind q⁻¹
      rw [hq]
      push_cast
      field_simp
    have e1 : l₁ * (l₂ / l₁) = l₂ := mul_div_cancel₀ l₂ hl₁
    have e2 : l₁ * (l₂ / l₁) ^ 2 = l₂ ^ 2 / l₁ := by field_simp
    exact DiazModulus.geometric_triple_not_logs l₁ (l₂ / l₁) hl₁ hz htr
      ⟨h₁, by rw [e1]; exact h₂, by rw [e2]; exact h⟩

end P16_log_two_pi_dependent_forces_transcendence

open P16_log_two_pi_dependent_forces_transcendence in
theorem solution (hdep : IsAlgebraic (↥(Algebra.adjoin ℚ ({((Real.pi : ℝ) : ℂ) * Complex.I} : Set ℂ))) ((Real.log 2 : ℝ) : ℂ)) :
    Transcendental ℚ (Complex.exp (Complex.I * ((Real.log 2 : ℝ) : ℂ) ^ 2 / ((Real.pi : ℝ) : ℂ))) ∧
      Transcendental ℚ (Complex.exp (((Real.pi : ℝ) : ℂ) ^ 2 / ((Real.log 2 : ℝ) : ℂ))) := by
  have hL0 : Real.log 2 ≠ 0 := (Real.log_pos (by norm_num)).ne'
  have h₁ : IsAlgebraic ℚ (Complex.exp ((Real.log 2 : ℝ) : ℂ)) := by
    rw [← Complex.ofReal_exp, Real.exp_log (by norm_num)]
    simpa using isAlg_rat 2
  have hind : ∀ q : ℚ, ((Real.log 2 : ℝ) : ℂ) ≠ (q : ℂ) * (((Real.pi : ℝ) : ℂ) * Complex.I) := by
    intro q h
    have h' := congrArg Complex.re h
    rw [Complex.ofReal_re] at h'
    have h0 : ((q : ℂ) * (((Real.pi : ℝ) : ℂ) * Complex.I)).re = 0 := by simp
    exact hL0 (h'.trans h0)
  obtain ⟨hA, hB⟩ := core _ _ h₁ exp_pI_alg pI_ne_zero hind hdep
  have hπ : ((Real.pi : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 Real.pi_ne_zero
  have hLC : ((Real.log 2 : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hL0
  constructor
  · intro h
    apply hA
    have e : ((Real.log 2 : ℝ) : ℂ) ^ 2 / (((Real.pi : ℝ) : ℂ) * Complex.I) =
        -(Complex.I * ((Real.log 2 : ℝ) : ℂ) ^ 2 / ((Real.pi : ℝ) : ℂ)) := by
      rw [div_mul_eq_div_div, div_eq_mul_inv (((Real.log 2 : ℝ) : ℂ) ^ 2 / ((Real.pi : ℝ) : ℂ)),
        Complex.inv_I]
      ring
    rw [e, Complex.exp_neg]
    exact h.inv
  · intro h
    apply hB
    have e : (((Real.pi : ℝ) : ℂ) * Complex.I) ^ 2 / ((Real.log 2 : ℝ) : ℂ) =
        -(((Real.pi : ℝ) : ℂ) ^ 2 / ((Real.log 2 : ℝ) : ℂ)) := by
      rw [mul_pow, Complex.I_sq]
      ring
    rw [e, Complex.exp_neg]
    exact h.inv

#print axioms solution
