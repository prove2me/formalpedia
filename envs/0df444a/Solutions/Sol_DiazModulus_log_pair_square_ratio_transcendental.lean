-- Prove2me | solution 1 for DiazModulus.log_pair_square_ratio_transcendental
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-24T11:05:07.976266+00:00
-- url     : https://prove2.me/submissions/18295c95-122e-4c1c-a6bb-8e96aa23ff6d

import Mathlib
import Definitions.Def_DiazModulus
import Theorems.Thm_DiazModulus_geometric_triple_not_logs

open Complex ComplexConjugate

namespace P16_log_pair_square_ratio_transcendental

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

end P16_log_pair_square_ratio_transcendental

open P16_log_pair_square_ratio_transcendental in
theorem solution (l₁ l₂ : ℂ)
    (h₁ : IsAlgebraic ℚ (Complex.exp l₁)) (h₂ : IsAlgebraic ℚ (Complex.exp l₂))
    (hl₂ : l₂ ≠ 0) (hind : ∀ q : ℚ, l₁ ≠ (q : ℂ) * l₂)
    (hdep : IsAlgebraic (↥(Algebra.adjoin ℚ ({l₂} : Set ℂ))) l₁) :
    Transcendental ℚ (Complex.exp (l₁ ^ 2 / l₂)) ∧ Transcendental ℚ (Complex.exp (l₂ ^ 2 / l₁)) := by
  exact core l₁ l₂ h₁ h₂ hl₂ hind hdep

#print axioms solution
