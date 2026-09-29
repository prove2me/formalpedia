-- Prove2me | solution 1 for DiazModulus.diaz_number_forces_transcendence
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-23T18:34:48.575221+00:00
-- url     : https://prove2.me/submissions/ade0982b-7a72-4e11-83db-a52229d4dc74

import Mathlib
import Theorems.Thm_DiazModulus_geometric_triple_not_logs

namespace DNFT

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

theorem mem_E_of_sq {u z : ℂ} (h : z ^ 2 ∈ E u) : z ∈ E u :=
  (mem_E_iff.1 h).of_pow (by norm_num)

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

end DNFT

open DNFT in
/-- Put `w = πi`. Since `t² = ρ + w²`, the number `t` is algebraic over `ℚ[w]`.
(a) and (c) come from the triple `w = πi`, `z = t / (πi)`, where `wz = t`.
(b) comes from the triple `w = t`, `z = πi / t`, where `wz = πi`. -/
theorem solution (t : ℝ) (ht : t ≠ 0)
    (hexp : IsAlgebraic ℚ (Complex.exp (t : ℂ)))
    (hρ : IsAlgebraic ℚ (((t ^ 2 + Real.pi ^ 2 : ℝ)) : ℂ)) :
    Transcendental ℚ (Complex.exp (Complex.I * (t : ℂ) ^ 2 / ((Real.pi : ℝ) : ℂ))) ∧
      Transcendental ℚ (Complex.exp (((Real.pi : ℝ) : ℂ) ^ 2 / (t : ℂ))) ∧
      Transcendental ℚ (Complex.exp (((t ^ 2 + Real.pi ^ 2 : ℝ) : ℂ) / (((Real.pi : ℝ) : ℂ) * Complex.I))) := by
  have hπ : ((Real.pi : ℝ) : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have hT : (t : ℂ) ≠ 0 := by exact_mod_cast ht
  have hρeq : (((t ^ 2 + Real.pi ^ 2 : ℝ)) : ℂ) = (t : ℂ) ^ 2 + ((Real.pi : ℝ) : ℂ) ^ 2 := by
    norm_cast
  set w : ℂ := ((Real.pi : ℝ) : ℂ) * Complex.I with hw_def
  have hw : w ≠ 0 := mul_ne_zero hπ Complex.I_ne_zero
  have hw2 : w ^ 2 = -((Real.pi : ℝ) : ℂ) ^ 2 := by
    rw [hw_def]
    linear_combination ((Real.pi : ℝ) : ℂ) ^ 2 * Complex.I_sq
  have hexpw : IsAlgebraic ℚ (Complex.exp w) := exp_pi_I_alg
  -- `t` is algebraic over `ℚ[w]`, because `t² = ρ + w²`
  have hwE : w ∈ E w := self_mem_E w
  have hTE : (t : ℂ) ∈ E w := by
    apply mem_E_of_sq
    have : (t : ℂ) ^ 2 = (((t ^ 2 + Real.pi ^ 2 : ℝ)) : ℂ) + w ^ 2 := by
      rw [hρeq, hw2]; ring
    rw [this]
    exact add_mem (mem_E_of_alg hρ) (pow_mem hwE 2)
  -- the triple `w = πi`, `z = t / (πi)`
  have key : ¬ IsAlgebraic ℚ (Complex.exp (w * ((t : ℂ) / w) ^ 2)) := by
    intro h3
    have hz : ∀ q : ℚ, (t : ℂ) / w ≠ (q : ℂ) := by
      intro q hq
      have h1 : (t : ℂ) = (q : ℂ) * w := by
        rw [← hq]; field_simp
      have := congrArg Complex.re h1
      simp [hw_def] at this
      exact ht this
    have htr : Algebra.trdeg ℚ ↥(Algebra.adjoin ℚ ({w, (t : ℂ) / w} : Set ℂ)) ≤ 1 :=
      trdeg_pair_le_one (Algebra.subset_adjoin (by simp)) hwE (div_mem_E hTE hwE hw)
    have e2 : IsAlgebraic ℚ (Complex.exp (w * ((t : ℂ) / w))) := by
      rw [show w * ((t : ℂ) / w) = (t : ℂ) by field_simp]
      exact hexp
    exact DiazModulus.geometric_triple_not_logs w ((t : ℂ) / w) hw hz htr ⟨hexpw, e2, h3⟩
  refine ⟨?_, ?_, ?_⟩
  · -- (a): `w z² = t² / (πi) = -(i t² / π)`
    intro h
    apply key
    have : w * ((t : ℂ) / w) ^ 2 = -(Complex.I * (t : ℂ) ^ 2 / ((Real.pi : ℝ) : ℂ)) := by
      rw [hw_def]
      field_simp
      linear_combination Complex.I_sq
    rw [this, Complex.exp_neg]
    exact h.inv
  · -- (b): the triple `w = t`, `z = πi / t`
    intro h
    have hz : ∀ q : ℚ, w / (t : ℂ) ≠ (q : ℂ) := by
      intro q hq
      have h1 : w = (q : ℂ) * (t : ℂ) := by
        rw [← hq]; field_simp
      have := congrArg Complex.im h1
      simp [hw_def, Real.pi_ne_zero] at this
    have hwA : w ∈ Algebra.adjoin ℚ ({(t : ℂ), w / (t : ℂ)} : Set ℂ) := by
      have hmem : (t : ℂ) * (w / (t : ℂ)) ∈ Algebra.adjoin ℚ ({(t : ℂ), w / (t : ℂ)} : Set ℂ) :=
        mul_mem (Algebra.subset_adjoin (by simp)) (Algebra.subset_adjoin (by simp))
      rwa [show (t : ℂ) * (w / (t : ℂ)) = w by field_simp] at hmem
    have htr : Algebra.trdeg ℚ ↥(Algebra.adjoin ℚ ({(t : ℂ), w / (t : ℂ)} : Set ℂ)) ≤ 1 :=
      trdeg_pair_le_one hwA hTE (div_mem_E hwE hTE hT)
    have e2 : IsAlgebraic ℚ (Complex.exp ((t : ℂ) * (w / (t : ℂ)))) := by
      rw [show (t : ℂ) * (w / (t : ℂ)) = w by field_simp]
      exact hexpw
    have e3 : IsAlgebraic ℚ (Complex.exp ((t : ℂ) * (w / (t : ℂ)) ^ 2)) := by
      have : (t : ℂ) * (w / (t : ℂ)) ^ 2 = -(((Real.pi : ℝ) : ℂ) ^ 2 / (t : ℂ)) := by
        rw [div_pow, hw2]
        field_simp
      rw [this, Complex.exp_neg]
      exact h.inv
    exact DiazModulus.geometric_triple_not_logs (t : ℂ) (w / (t : ℂ)) hT hz htr ⟨hexp, e2, e3⟩
  · -- (c): `ρ / (πi) = t² / (πi) - πi`, so `e^{ρ/(πi)} = -e^{w z²}`
    intro h
    apply key
    have : w * ((t : ℂ) / w) ^ 2 = (((t ^ 2 + Real.pi ^ 2 : ℝ)) : ℂ) / w + w := by
      rw [hρeq, show ((Real.pi : ℝ) : ℂ) ^ 2 = -w ^ 2 by rw [hw2]; ring]
      field_simp
      ring
    rw [this, Complex.exp_add]
    exact h.mul hexpw

#print axioms solution
