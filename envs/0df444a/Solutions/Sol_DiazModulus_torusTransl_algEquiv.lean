-- Prove2me | solution 1 for DiazModulus.torusTransl_algEquiv
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-30T10:06:30.836979+00:00
-- url     : https://prove2.me/submissions/6ac9077e-1825-4de6-a646-0cecbf087f61

import Mathlib
import Definitions.Def_DiazMultiplicity
import Theorems.Thm_DiazModulus_exists_translation_algEquiv

open Complex ComplexConjugate

/-! # Translations are algebra automorphisms that move ideals of point sets and zero sets

The imported node `exists_translation_algEquiv` (C1.1's T6) at `(x, y) = g` gives an `AlgEquiv` `e` of `K[X, Y, Z]`
with the same values on the variables as `torusTransl g`, preserving every box and `J₀`; `MvPolynomial.algHom_ext`
identifies `e` with `torusTransl g`. With `eval_torusTransl`, `eval (z) (e f) = eval (z g) f`, so `f ∈ I(S).map e`
(i.e. `e⁻¹ f ∈ I(S)`) iff `f` vanishes at every `z` with `z g ∈ S`, and `z ∈ Z(𝔟.map e)` iff `z g ∈ Z(𝔟)`
(`Ideal.mem_map_of_equiv`). The composition rule `σ_g σ_h = σ_{gh}` and `σ_1 = id` are checked on the variables
(`MvPolynomial.algHom_ext`): `X ↦ X + x_h ↦ X + x_g + x_h`, `Y ↦ y_h Y ↦ y_h y_g Y`, `Z ↦ y_h⁻¹ y_g⁻¹ Z`. -/

namespace C13_V2
open DiazModulus MvPolynomial

/-- `σ_g ∘ σ_h = σ_{gh}` as algebra maps. -/
theorem torusTransl_comp {K A₀ A₁ : Type*} [Field K] (g h : TorusGroup K A₀ A₁) :
    (torusTransl g).comp (torusTransl h) = torusTransl (g * h) := by
  apply MvPolynomial.algHom_ext
  intro v
  rcases v with i | ⟨i, b⟩
  · simp [torusTransl, toAdd_mul, add_assoc]
  · cases b <;> simp [torusTransl, torusPt, torusPoint, mul_inv_rev] <;> ring

/-- `σ_1 = id`. -/
theorem torusTransl_one {K A₀ A₁ : Type*} [Field K] :
    torusTransl (1 : TorusGroup K A₀ A₁) = AlgHom.id K _ := by
  apply MvPolynomial.algHom_ext
  intro v
  rcases v with i | ⟨i, b⟩
  · simp [torusTransl]
  · cases b <;> simp [torusTransl, torusPt, torusPoint]

end C13_V2

open DiazModulus C13_V2 in
theorem solution {K A₀ A₁ : Type*} [Field K] (g : TorusGroup K A₀ A₁) :
    (∃ e : MvPolynomial (A₀ ⊕ (A₁ × Bool)) K ≃ₐ[K] (MvPolynomial (A₀ ⊕ (A₁ × Bool)) K), (∀ f, e f = torusTransl g f) ∧
      (∀ T : A₀ ⊕ A₁ → ℕ, (torusBox K A₀ A₁ T).map e.toLinearMap = torusBox K A₀ A₁ T) ∧
      (torusIdeal K A₀ A₁).map e = torusIdeal K A₀ A₁ ∧
      (∀ S : Set (TorusGroup K A₀ A₁), (torusVanishing S).map e = torusVanishing {z | z * g ∈ S}) ∧
      ∀ 𝔟 : Ideal (MvPolynomial (A₀ ⊕ (A₁ × Bool)) K), torusZero (𝔟.map e) = {z | z * g ∈ torusZero 𝔟}) ∧
    (∀ (h : TorusGroup K A₀ A₁) (f : MvPolynomial (A₀ ⊕ (A₁ × Bool)) K), torusTransl g (torusTransl h f) = torusTransl (g * h) f) ∧
    ∀ f : MvPolynomial (A₀ ⊕ (A₁ × Bool)) K, torusTransl (1 : TorusGroup K A₀ A₁) f = f := by
  refine ⟨?_, fun h f => by rw [← torusTransl_comp]; rfl,
    fun f => by rw [torusTransl_one]; rfl⟩
  obtain ⟨e, hX, hbox, hJ⟩ := DiazModulus.exists_translation_algEquiv (Multiplicative.toAdd g.1) g.2
  have hEq : (e : MvPolynomial (A₀ ⊕ (A₁ × Bool)) K →ₐ[K] _) = torusTransl g := by
    apply MvPolynomial.algHom_ext
    intro v
    rw [AlgEquiv.coe_toAlgHom, hX]
    rcases v with i | p
    · simp [torusTransl]
    · simp [torusTransl, torusPt]
  have he : ∀ f, e f = torusTransl g f := fun f => by
    rw [← hEq]; rfl
  have hev : ∀ z f, MvPolynomial.eval (torusPt z) (e f) = MvPolynomial.eval (torusPt (z * g)) f := by
    intro z f
    rw [he, eval_torusTransl]
  refine ⟨e, he, hbox, hJ, fun S => ?_, fun 𝔟 => ?_⟩
  · ext f
    rw [Ideal.mem_map_of_equiv]
    simp only [torusVanishing, Ideal.mem_iInf, RingHom.mem_ker, Set.mem_ofPred_eq]
    constructor
    · rintro ⟨q, hq, rfl⟩ z hz
      rw [hev]
      exact hq _ hz
    · intro hf
      refine ⟨e.symm f, fun s hs => ?_, e.apply_symm_apply f⟩
      have := hf (s * g⁻¹) (by simpa using hs)
      rw [← e.apply_symm_apply f, hev, inv_mul_cancel_right] at this
      exact this
  · ext z
    simp only [Set.mem_ofPred_eq, mem_torusZero]
    constructor
    · intro hz f hf
      rw [← hev]
      exact hz _ (Ideal.mem_map_of_mem e hf)
    · intro hz f hf
      obtain ⟨q, hq, rfl⟩ := (Ideal.mem_map_of_equiv e f).1 hf
      rw [hev]
      exact hz q hq
