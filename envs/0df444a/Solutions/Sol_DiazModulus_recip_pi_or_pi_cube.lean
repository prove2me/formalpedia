-- Prove2me | solution 1 for DiazModulus.recip_pi_or_pi_cube
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-23T18:34:50.523148+00:00
-- url     : https://prove2.me/submissions/4ad3f260-298b-4cf1-b6ec-ace6ed576c53

import Mathlib
import Theorems.Thm_DiazModulus_geometric_triple_not_logs
import Theorems.Thm_DiazModulus_pi_transcendental

namespace RPPC

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

/-- The complex numbers algebraic over `ℚ[u]`, as a `ℚ`-subalgebra of `ℂ`. -/
noncomputable def E (u : ℂ) : Subalgebra ℚ ℂ :=
  (Subalgebra.algebraicClosure ↥(Algebra.adjoin ℚ ({u} : Set ℂ)) ℂ).restrictScalars ℚ

theorem mem_E_iff {u z : ℂ} : z ∈ E u ↔ IsAlgebraic ↥(Algebra.adjoin ℚ ({u} : Set ℂ)) z :=
  Iff.rfl

theorem mem_E_of_alg {u z : ℂ} (h : IsAlgebraic ℚ z) : z ∈ E u :=
  h.extendScalars (algebraMap ℚ ↥(Algebra.adjoin ℚ ({u} : Set ℂ))).injective

theorem self_mem_E (u : ℂ) : u ∈ E u := by
  rw [mem_E_iff]
  have h : u = algebraMap ↥(Algebra.adjoin ℚ ({u} : Set ℂ)) ℂ
      ⟨u, Algebra.subset_adjoin rfl⟩ := rfl
  rw [h]
  exact isAlgebraic_algebraMap _

theorem mem_E_of_mul {u a z : ℂ} (ha : a ≠ 0) (haE : a ∈ E u) (h : a * z ∈ E u) :
    z ∈ E u :=
  IsAlgebraic.of_mul (mem_nonZeroDivisors_of_ne_zero ha) (mem_E_iff.1 haE) (mem_E_iff.1 h)

theorem div_mem_E {u a b : ℂ} (ha : a ∈ E u) (hb : b ∈ E u) (hb0 : b ≠ 0) :
    a / b ∈ E u :=
  mem_E_of_mul hb0 hb (by rw [show b * (a / b) = a by field_simp]; exact ha)

/-- A pair `{w, z}` of elements algebraic over `ℚ[u]`, with `u ∈ ℚ[w, z]`, generates a
`ℚ`-algebra of transcendence degree at most one. -/
theorem trdeg_pair_le_one {u w z : ℂ} (hu : u ∈ Algebra.adjoin ℚ ({w, z} : Set ℂ))
    (hwE : w ∈ E u) (hzE : z ∈ E u) :
    Algebra.trdeg ℚ ↥(Algebra.adjoin ℚ ({w, z} : Set ℂ)) ≤ 1 := by
  refine trdeg_le_one_of_adjoin_singleton hu ?_
  have hle : Algebra.adjoin ℚ ({w, z} : Set ℂ) ≤ E u := by
    refine Algebra.adjoin_le ?_
    intro y hy
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
    rcases hy with rfl | rfl
    · exact hwE
    · exact hzE
  intro y hy
  exact mem_E_iff.1 (hle hy)

theorem exp_pi_I_alg : IsAlgebraic ℚ (Complex.exp (((Real.pi : ℝ) : ℂ) * Complex.I)) := by
  rw [Complex.exp_pi_mul_I]
  exact (isAlgebraic_one (R := ℚ) (A := ℂ)).neg

/-- `π²` is transcendental, since `π` is. -/
theorem not_alg_pi_sq : ¬ IsAlgebraic ℚ (((Real.pi : ℝ) : ℂ) ^ 2) := fun h =>
  DiazModulus.pi_transcendental (h.of_pow (by norm_num))

/-- `π²` is not a rational multiple of an algebraic number. -/
theorem pi_sq_ne_rat_mul {γ : ℂ} (hγ : IsAlgebraic ℚ γ) (q : ℚ) :
    ((Real.pi : ℝ) : ℂ) ^ 2 ≠ (q : ℂ) * γ := by
  intro h
  apply not_alg_pi_sq
  rw [h, show (q : ℂ) = algebraMap ℚ ℂ q by simp]
  exact (isAlgebraic_algebraMap q).mul hγ

end RPPC

open RPPC in
/-- Put `w₀ = πi`. Every number below is algebraic over `ℚ[w₀]`.
The first disjunction is the triple `w = γ / (πi)`, `z = (πi)² / γ`, where `wz = πi`.
The second disjunction is the triple `w = πi`, `z = γ / (πi)²`.
In both cases `z ∉ ℚ` because `π²` is not a rational multiple of `γ`. -/
theorem solution (γ : ℂ) (hγ : IsAlgebraic ℚ γ) (hγ0 : γ ≠ 0) :
    (Transcendental ℚ (Complex.exp (Complex.I * γ / ((Real.pi : ℝ) : ℂ))) ∨
      Transcendental ℚ (Complex.exp (Complex.I * ((Real.pi : ℝ) : ℂ) ^ 3 / γ))) ∧
    (Transcendental ℚ (Complex.exp (Complex.I * γ / ((Real.pi : ℝ) : ℂ))) ∨
      Transcendental ℚ (Complex.exp (Complex.I * γ ^ 2 / ((Real.pi : ℝ) : ℂ) ^ 3))) := by
  have hπ : ((Real.pi : ℝ) : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  set w : ℂ := ((Real.pi : ℝ) : ℂ) * Complex.I with hw_def
  have hw : w ≠ 0 := mul_ne_zero hπ Complex.I_ne_zero
  have hw2 : w ^ 2 = -((Real.pi : ℝ) : ℂ) ^ 2 := by
    rw [hw_def]
    linear_combination ((Real.pi : ℝ) : ℂ) ^ 2 * Complex.I_sq
  have hexpw : IsAlgebraic ℚ (Complex.exp w) := exp_pi_I_alg
  have hwE : w ∈ E w := self_mem_E w
  have hγE : γ ∈ E w := mem_E_of_alg hγ
  -- `e^{γ / (πi)} = (e^{iγ/π})⁻¹`
  have hγw : γ / w = -(Complex.I * γ / ((Real.pi : ℝ) : ℂ)) := by
    rw [hw_def]
    field_simp
    linear_combination Complex.I_sq
  refine ⟨?_, ?_⟩
  · -- the triple `w₁ = γ / (πi)`, `z₁ = (πi)² / γ`
    by_contra h
    simp only [not_or, Transcendental, not_not] at h
    obtain ⟨h1, h2⟩ := h
    have hw1 : γ / w ≠ 0 := div_ne_zero hγ0 hw
    have hz : ∀ q : ℚ, w ^ 2 / γ ≠ (q : ℂ) := by
      intro q hq
      have hq' : w ^ 2 = (q : ℂ) * γ := by
        rw [← hq]; field_simp
      apply pi_sq_ne_rat_mul hγ (-q)
      rw [hw2] at hq'
      push_cast
      linear_combination -hq'
    have hwA : w ∈ Algebra.adjoin ℚ ({γ / w, w ^ 2 / γ} : Set ℂ) := by
      have hmem : γ / w * (w ^ 2 / γ) ∈ Algebra.adjoin ℚ ({γ / w, w ^ 2 / γ} : Set ℂ) :=
        mul_mem (Algebra.subset_adjoin (by simp)) (Algebra.subset_adjoin (by simp))
      rwa [show γ / w * (w ^ 2 / γ) = w by field_simp] at hmem
    have htr : Algebra.trdeg ℚ ↥(Algebra.adjoin ℚ ({γ / w, w ^ 2 / γ} : Set ℂ)) ≤ 1 :=
      trdeg_pair_le_one hwA (div_mem_E hγE hwE hw) (div_mem_E (pow_mem hwE 2) hγE hγ0)
    have e1 : IsAlgebraic ℚ (Complex.exp (γ / w)) := by
      rw [hγw, Complex.exp_neg]
      exact h1.inv
    have e2 : IsAlgebraic ℚ (Complex.exp (γ / w * (w ^ 2 / γ))) := by
      rw [show γ / w * (w ^ 2 / γ) = w by field_simp]
      exact hexpw
    have e3 : IsAlgebraic ℚ (Complex.exp (γ / w * (w ^ 2 / γ) ^ 2)) := by
      have : γ / w * (w ^ 2 / γ) ^ 2 = -(Complex.I * ((Real.pi : ℝ) : ℂ) ^ 3 / γ) := by
        rw [hw_def]
        field_simp
        linear_combination Complex.I_sq
      rw [this, Complex.exp_neg]
      exact h2.inv
    exact DiazModulus.geometric_triple_not_logs (γ / w) (w ^ 2 / γ) hw1 hz htr ⟨e1, e2, e3⟩
  · -- the triple `w = πi`, `z = γ / (πi)²`
    by_contra h
    simp only [not_or, Transcendental, not_not] at h
    obtain ⟨h1, h2⟩ := h
    have hz : ∀ q : ℚ, γ / w ^ 2 ≠ (q : ℂ) := by
      intro q hq
      have hq0 : (q : ℂ) ≠ 0 := by
        rw [← hq]; exact div_ne_zero hγ0 (pow_ne_zero 2 hw)
      have hq' : γ = (q : ℂ) * w ^ 2 := by
        rw [← hq]; field_simp
      apply pi_sq_ne_rat_mul hγ (-q⁻¹)
      rw [hw2] at hq'
      push_cast
      field_simp
      linear_combination hq'
    have htr : Algebra.trdeg ℚ ↥(Algebra.adjoin ℚ ({w, γ / w ^ 2} : Set ℂ)) ≤ 1 :=
      trdeg_pair_le_one (Algebra.subset_adjoin (by simp)) hwE
        (div_mem_E hγE (pow_mem hwE 2) (pow_ne_zero 2 hw))
    have e2 : IsAlgebraic ℚ (Complex.exp (w * (γ / w ^ 2))) := by
      rw [show w * (γ / w ^ 2) = γ / w by field_simp, hγw, Complex.exp_neg]
      exact h1.inv
    have e3 : IsAlgebraic ℚ (Complex.exp (w * (γ / w ^ 2) ^ 2)) := by
      have : w * (γ / w ^ 2) ^ 2 = Complex.I * γ ^ 2 / ((Real.pi : ℝ) : ℂ) ^ 3 := by
        rw [hw_def]
        field_simp
        linear_combination (1 - Complex.I ^ 2) * Complex.I_sq
      rw [this]
      exact h2
    exact DiazModulus.geometric_triple_not_logs w (γ / w ^ 2) hw hz htr ⟨hexpw, e2, e3⟩

#print axioms solution
