-- Prove2me | solution 1 for DiazModulus.boxHilb_sup_span_add_le
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-29T08:21:30.751294+00:00
-- url     : https://prove2.me/submissions/57154a1d-171e-4d56-ade4-acb6b58a3cdf

import Mathlib
import Definitions.Def_DiazHilbertBox

open Complex ComplexConjugate

/-! # Cutting by a regular element: `h_{I+(P)}(T+D) + h_I(T) ≤ h_I(T+D)` (DALAG Lemma 8.5)

Work in `Q = S ⧸ I`. Let `W ⊆ Q` be the image of `F(T+D)` (dimension `h_I(T+D)`) and `W_T` the
image of `F(T)` (dimension `h_I(T)`). The image of `F(T+D)` in `S ⧸ (I + (P))` is the image of
`W` under the factor map `g : Q → S ⧸ (I + (P))`. Multiplication by `P` on `Q` is injective
(`P` is regular on `S ⧸ I`), so `P · W_T` has dimension `h_I(T)`; it lies in `W` because
`P ∈ F(D)` and `F(T) F(D) ⊆ F(T+D)`, and `g` kills it because `P t ∈ (P)`. Rank–nullity for `g`
restricted to `W` (`LinearMap.finrank_range_add_finrank_ker`) gives
`dim g(W) + dim (P · W_T) ≤ dim g(W) + dim (ker g ∩ W) = dim W`. -/

namespace C11_supSpan

open DiazModulus

/-- Rank–nullity on a finite-dimensional subspace: if `X ≤ W` and `g` kills `X`, then
`dim g(W) + dim X ≤ dim W`. -/
theorem finrank_map_add_le {K Q Q' : Type*} [Field K] [AddCommGroup Q] [Module K Q]
    [AddCommGroup Q'] [Module K Q'] (g : Q →ₗ[K] Q') (W X : Submodule K Q)
    [FiniteDimensional K W] (hXW : X ≤ W) (hX : ∀ x ∈ X, g x = 0) :
    Module.finrank K (W.map g) + Module.finrank K X ≤ Module.finrank K W := by
  have rn := LinearMap.finrank_range_add_finrank_ker (g.domRestrict W)
  rw [LinearMap.range_domRestrict] at rn
  have hle : X ≤ (LinearMap.ker (g.domRestrict W)).map W.subtype := by
    intro x hx
    exact ⟨⟨x, hXW hx⟩, by simp [LinearMap.mem_ker, hX x hx], rfl⟩
  have := Submodule.finrank_mono hle
  rw [Submodule.finrank_map_subtype_eq] at this
  omega

end C11_supSpan

open DiazModulus C11_supSpan in
theorem solution {K S B : Type*} [Field K] [CommRing S] [Algebra K S] (F : (B → ℕ) → Submodule K S)
    (hFmul : ∀ {Tₑ Uₑ : B → ℕ} {aₑ bₑ : S}, aₑ ∈ F Tₑ → bₑ ∈ F Uₑ → aₑ * bₑ ∈ F (Tₑ + Uₑ))
    (hFfin : ∀ Tₑ, FiniteDimensional K ↥(F Tₑ)) (I : Ideal S) (P : S) (D T : B → ℕ)
    (hP : P ∈ F D) (hreg : IsSMulRegular (S ⧸ I) P) :
    boxHilb F (I ⊔ Ideal.span {P}) (T + D) + boxHilb F I T ≤ boxHilb F I (T + D) := by
  set J := I ⊔ Ideal.span {P} with hJ
  have hIJ : I ≤ J := le_sup_left
  let mkI := (Ideal.Quotient.mkₐ K I).toLinearMap
  let g := (Ideal.Quotient.factorₐ K hIJ).toLinearMap
  let μ := LinearMap.mulLeft K (Ideal.Quotient.mk I P)
  have hμ : Function.Injective μ := by
    intro a b hab
    apply hreg
    simp only [Algebra.smul_def, Ideal.Quotient.algebraMap_eq]
    exact hab
  have hcomp : g ∘ₗ mkI = (Ideal.Quotient.mkₐ K J).toLinearMap := by
    ext x; rfl
  have := hFfin (T + D)
  have := hFfin T
  set W := (F (T + D)).map mkI with hW
  set X := ((F T).map mkI).map μ with hX
  have hXW : X ≤ W := by
    rintro _ ⟨_, ⟨t, ht, rfl⟩, rfl⟩
    refine ⟨t * P, hFmul ht hP, ?_⟩
    simp [mkI, μ, mul_comm]
  have hXg : ∀ x ∈ X, g x = 0 := by
    rintro _ ⟨_, ⟨t, ht, rfl⟩, rfl⟩
    show Ideal.Quotient.mk J (P * t) = 0
    rw [Ideal.Quotient.eq_zero_iff_mem]
    exact Ideal.mem_sup_right (Ideal.mul_mem_right t _ (Ideal.mem_span_singleton_self P))
  have key := finrank_map_add_le g W X hXW hXg
  have hXrank : Module.finrank K X = Module.finrank K ((F T).map mkI) :=
    (LinearEquiv.finrank_eq (Submodule.equivMapOfInjective μ hμ _)).symm
  have hmapJ : W.map g = (F (T + D)).map (Ideal.Quotient.mkₐ K J).toLinearMap := by
    rw [hW, ← Submodule.map_comp, hcomp]
  unfold boxHilb
  rw [← hmapJ, ← hXrank]
  exact key
