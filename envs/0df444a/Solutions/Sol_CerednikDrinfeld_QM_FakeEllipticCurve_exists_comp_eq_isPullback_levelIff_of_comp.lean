-- Prove2me | solution 1 for CerednikDrinfeld.QM.FakeEllipticCurve.exists_comp_eq_isPullback_levelIff_of_comp
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.837917+00:00
-- url     : https://prove2.me/submissions/f3077f74-43fc-54fb-ba6b-3208f54b0e04

import Mathlib
import Definitions.Def_CerednikDrinfeld_QMFineModuli
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_exists_comp_eq_isPullback_levelIff_of_comp

set_option autoImplicit false

open scoped TensorProduct Quaternion NumberField
open CategoryTheory AlgebraicGeometry QuaternionAlgebra CerednikDrinfeld CerednikDrinfeld.QM NeronModelInfra

namespace CancelBAux
open GoodReductionJacobian

theorem mul_val_congr {R : Type} [CommRing R] {A : Scheme.{0}} {f : A ⟶ Spec (CommRingCat.of R)}
    (L : RelativeGroupLaw R f) {T : Scheme.{0}} {t₁ t₂ : T ⟶ Spec (CommRingCat.of R)} (e : t₁ = t₂)
    (P₁ Q₁ : SchemeHomOver t₁ f) (P₂ Q₂ : SchemeHomOver t₂ f) (hP : P₁.1 = P₂.1) (hQ : Q₁.1 = Q₂.1) :
    (L.mul t₁ P₁ Q₁).1 = (L.mul t₂ P₂ Q₂).1 := by
  subst e
  have h1 : P₁ = P₂ := Subtype.ext hP
  have h2 : Q₁ = Q₂ := Subtype.ext hQ
  subst h1 h2
  rfl

end CancelBAux

theorem solution
    {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} {N : ℕ}
    {S₁ S₂ S₃ : Type} [CommRing S₁] [CommRing S₂] [CommRing S₃] (σ : S₁ →+* S₂) (τ : S₂ →+* S₃)
    (E₁ : FakeEllipticCurve Λ N S₁) (E₂ : FakeEllipticCurve Λ N S₂) (E₃ : FakeEllipticCurve Λ N S₃)
    (g : E₂.A ⟶ E₁.A) (hg : CategoryTheory.IsPullback g E₂.f E₁.f (Spec.map (CommRingCat.ofHom σ)))
    (h₁₂ :
      (∀ {T : Scheme.{0}} (t' : T ⟶ Spec (CommRingCat.of S₂)) (P Q : SchemeHomOver t' E₂.f),
        (E₂.L.mul t' P Q).1 ≫ g =
          (E₁.L.mul (t' ≫ Spec.map (CommRingCat.ofHom σ))
            ⟨P.1 ≫ g, by rw [Category.assoc, hg.w, ← Category.assoc, P.2]⟩
            ⟨Q.1 ≫ g, by rw [Category.assoc, hg.w, ← Category.assoc, Q.2]⟩).1) ∧
      (∀ x : ↥Λ, E₂.act x ≫ g = g ≫ E₁.act x) ∧
      (∀ {T : Scheme.{0}} (t' : T ⟶ Spec (CommRingCat.of S₂)) (P : SchemeHomOver t' E₂.f),
        FactorsThrough E₂.lev P → ∃ P₀ : T ⟶ E₁.C, P₀ ≫ E₁.lev = P.1 ≫ g) ∧
      (∀ {T : Scheme.{0}} (t' : T ⟶ Spec (CommRingCat.of S₂)) (P : SchemeHomOver t' E₂.f),
        (∃ P₀ : T ⟶ E₁.C, P₀ ≫ E₁.lev = P.1 ≫ g) → FactorsThrough E₂.lev P))
    (g' : E₃.A ⟶ E₁.A) (hg' : CategoryTheory.IsPullback g' E₃.f E₁.f (Spec.map (CommRingCat.ofHom (τ.comp σ))))
    (h₁₃ :
      (∀ {T : Scheme.{0}} (t' : T ⟶ Spec (CommRingCat.of S₃)) (P Q : SchemeHomOver t' E₃.f),
        (E₃.L.mul t' P Q).1 ≫ g' =
          (E₁.L.mul (t' ≫ Spec.map (CommRingCat.ofHom (τ.comp σ)))
            ⟨P.1 ≫ g', by rw [Category.assoc, hg'.w, ← Category.assoc, P.2]⟩
            ⟨Q.1 ≫ g', by rw [Category.assoc, hg'.w, ← Category.assoc, Q.2]⟩).1) ∧
      (∀ x : ↥Λ, E₃.act x ≫ g' = g' ≫ E₁.act x) ∧
      (∀ {T : Scheme.{0}} (t' : T ⟶ Spec (CommRingCat.of S₃)) (P : SchemeHomOver t' E₃.f),
        FactorsThrough E₃.lev P → ∃ P₀ : T ⟶ E₁.C, P₀ ≫ E₁.lev = P.1 ≫ g') ∧
      (∀ {T : Scheme.{0}} (t' : T ⟶ Spec (CommRingCat.of S₃)) (P : SchemeHomOver t' E₃.f),
        (∃ P₀ : T ⟶ E₁.C, P₀ ≫ E₁.lev = P.1 ≫ g') → FactorsThrough E₃.lev P)) :
    ∃ (h : E₃.A ⟶ E₂.A) (_ : h ≫ g = g') (hh : CategoryTheory.IsPullback h E₃.f E₂.f (Spec.map (CommRingCat.ofHom τ))),
      (∀ {T : Scheme.{0}} (t' : T ⟶ Spec (CommRingCat.of S₃)) (P Q : SchemeHomOver t' E₃.f),
        (E₃.L.mul t' P Q).1 ≫ h =
          (E₂.L.mul (t' ≫ Spec.map (CommRingCat.ofHom τ))
            ⟨P.1 ≫ h, by rw [Category.assoc, hh.w, ← Category.assoc, P.2]⟩
            ⟨Q.1 ≫ h, by rw [Category.assoc, hh.w, ← Category.assoc, Q.2]⟩).1) ∧
      (∀ x : ↥Λ, E₃.act x ≫ h = h ≫ E₂.act x) ∧
      (∀ {T : Scheme.{0}} (t' : T ⟶ Spec (CommRingCat.of S₃)) (P : SchemeHomOver t' E₃.f),
        FactorsThrough E₃.lev P → ∃ P₀ : T ⟶ E₂.C, P₀ ≫ E₂.lev = P.1 ≫ h) ∧
      (∀ {T : Scheme.{0}} (t' : T ⟶ Spec (CommRingCat.of S₃)) (P : SchemeHomOver t' E₃.f),
        (∃ P₀ : T ⟶ E₂.C, P₀ ≫ E₂.lev = P.1 ≫ h) → FactorsThrough E₃.lev P) := by
  obtain ⟨hmul, hact, hlev, hlev'⟩ := h₁₂
  obtain ⟨hmul₁₃, hact₁₃, hlev₁₃, hlev₁₃'⟩ := h₁₃
  have hSpec : Spec.map (CommRingCat.ofHom (τ.comp σ)) =
      Spec.map (CommRingCat.ofHom τ) ≫ Spec.map (CommRingCat.ofHom σ) := by
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
  have hw : g' ≫ E₁.f = (E₃.f ≫ Spec.map (CommRingCat.ofHom τ)) ≫ Spec.map (CommRingCat.ofHom σ) := by
    rw [hg'.w, hSpec, Category.assoc]
  let h : E₃.A ⟶ E₂.A := hg.lift g' (E₃.f ≫ Spec.map (CommRingCat.ofHom τ)) hw
  have hh₁ : h ≫ g = g' := hg.lift_fst _ _ _
  have hh₂ : h ≫ E₂.f = E₃.f ≫ Spec.map (CommRingCat.ofHom τ) := hg.lift_snd _ _ _
  have hcart : CategoryTheory.IsPullback h E₃.f E₂.f (Spec.map (CommRingCat.ofHom τ)) := by
    refine IsPullback.of_right ?_ hh₂ hg
    rw [hh₁, ← hSpec]
    exact hg'
  refine ⟨h, hh₁, hcart, ?_, ?_, ?_, ?_⟩
  ·
    intro T t' P Q
    apply hg.hom_ext
    · rw [Category.assoc, hh₁, hmul₁₃ t' P Q, hmul]
      refine CancelBAux.mul_val_congr E₁.L (by rw [hSpec, Category.assoc]) _ _ _ _ ?_ ?_
      · show P.1 ≫ g' = (P.1 ≫ h) ≫ g
        rw [Category.assoc, hh₁]
      · show Q.1 ≫ g' = (Q.1 ≫ h) ≫ g
        rw [Category.assoc, hh₁]
    · calc ((E₃.L.mul t' P Q).1 ≫ h) ≫ E₂.f = (E₃.L.mul t' P Q).1 ≫ (h ≫ E₂.f) := Category.assoc _ _ _
        _ = (E₃.L.mul t' P Q).1 ≫ (E₃.f ≫ Spec.map (CommRingCat.ofHom τ)) := congrArg _ hh₂
        _ = t' ≫ Spec.map (CommRingCat.ofHom τ) := by rw [← Category.assoc, (E₃.L.mul t' P Q).2]
        _ = _ := ((E₂.L.mul (t' ≫ Spec.map (CommRingCat.ofHom τ)) _ _).2).symm
  ·
    intro x
    apply hg.hom_ext
    · rw [Category.assoc, hh₁, hact₁₃, Category.assoc, hact, ← Category.assoc, hh₁]
    · rw [Category.assoc, hh₂, ← Category.assoc, E₃.act_over, Category.assoc, E₂.act_over, hh₂]
  ·
    intro T t' P hP
    obtain ⟨P₁, hP₁⟩ := hlev₁₃ t' P hP
    have hP' : FactorsThrough E₂.lev
        (⟨P.1 ≫ h, by rw [Category.assoc, hcart.w, ← Category.assoc, P.2]⟩ :
          SchemeHomOver (t' ≫ Spec.map (CommRingCat.ofHom τ)) E₂.f) :=
      hlev' (t' ≫ Spec.map (CommRingCat.ofHom τ)) _ ⟨P₁, by rw [hP₁, Category.assoc, hh₁]⟩
    exact hP'
  ·
    intro T t' P hP
    obtain ⟨P₀, hP₀⟩ := hP
    have hF : FactorsThrough E₂.lev
        (⟨P.1 ≫ h, by rw [Category.assoc, hcart.w, ← Category.assoc, P.2]⟩ :
          SchemeHomOver (t' ≫ Spec.map (CommRingCat.ofHom τ)) E₂.f) := ⟨P₀, hP₀⟩
    obtain ⟨P₁, hP₁⟩ := hlev (t' ≫ Spec.map (CommRingCat.ofHom τ)) _ hF
    refine hlev₁₃' t' P ⟨P₁, ?_⟩
    rw [hP₁]
    show (P.1 ≫ h) ≫ g = P.1 ≫ g'
    rw [Category.assoc, hh₁]

end S_CerednikDrinfeld_QM_FakeEllipticCurve_exists_comp_eq_isPullback_levelIff_of_comp
end P2MW
export P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_exists_comp_eq_isPullback_levelIff_of_comp (solution)
