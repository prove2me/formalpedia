-- Prove2me | solution 1 for CerednikDrinfeld.QM.FakeEllipticCurve.WithFullLevel.exists_isPullbackVia_comp_eq_of_isPullbackVia_comp
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.837917+00:00
-- url     : https://prove2.me/submissions/707333da-8aa3-564e-8c29-80c46f584f9a

import Definitions.Def_CerednikDrinfeld_QMFineModuliT
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_WithFullLevel_exists_isPullbackVia_comp_eq_of_isPullbackVia_comp

set_option autoImplicit false

open scoped Quaternion
open CategoryTheory AlgebraicGeometry QuaternionAlgebra CerednikDrinfeld CerednikDrinfeld.QM NeronModelInfra

namespace CanT

theorem mul_val_congr {R : Type} [CommRing R] {A : Scheme.{0}} {f : A ⟶ Spec (CommRingCat.of R)} (L : GoodReductionJacobian.RelativeGroupLaw R f)
    {T : Scheme.{0}} {t₁ t₂ : T ⟶ Spec (CommRingCat.of R)} (ht : t₁ = t₂) (P₁ Q₁ : SchemeHomOver t₁ f)
    (P₂ Q₂ : SchemeHomOver t₂ f) (hP : P₁.1 = P₂.1) (hQ : Q₁.1 = Q₂.1) :
    (L.mul t₁ P₁ Q₁).1 = (L.mul t₂ P₂ Q₂).1 := by
  subst ht
  cases Subtype.ext hP
  cases Subtype.ext hQ
  rfl

theorem specMap_comp {S S' S'' : Type} [CommRing S] [CommRing S'] [CommRing S''] (φ : S →+* S') (ψ : S' →+* S'') :
    Spec.map (CommRingCat.ofHom (ψ.comp φ)) = Spec.map (CommRingCat.ofHom ψ) ≫ Spec.map (CommRingCat.ofHom φ) := by
  rw [CommRingCat.ofHom_comp, Spec.map_comp]

end CanT

theorem solution
    {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} {N m ℓ : ℕ}
    {S S' S'' : Type} [CommRing S] [CommRing S'] [CommRing S''] (φ : S →+* S') (ψ : S' →+* S'')
    (u : FakeEllipticCurve.WithFullLevel Λ N m S) (u₁ : FakeEllipticCurve.WithFullLevel Λ N m S')
    (u'' : FakeEllipticCurve.WithFullLevel Λ N m S'')
    (Cu : u.1.ExtraLevel ℓ) (Cu₁ : u₁.1.ExtraLevel ℓ) (Cu'' : u''.1.ExtraLevel ℓ)
    (g₁ : u₁.1.A ⟶ u.1.A) (g : u''.1.A ⟶ u.1.A)
    (h₁ : FakeEllipticCurve.IsPullbackVia φ u.1 u₁.1 g₁) (h₁P : (u₁.2.P).1 ≫ g₁ = Spec.map (CommRingCat.ofHom φ) ≫ (u.2.P).1)
    (h₁L : (∀ {T₀ : Scheme.{0}} (t' : T₀ ⟶ Spec (CommRingCat.of S')) (P : SchemeHomOver t' u₁.1.f),
          (∃ P₀ : T₀ ⟶ u.1.C, P₀ ≫ u.1.lev = P.1 ≫ g₁) → FactorsThrough u₁.1.lev P))
    (h₁C : (∀ {T₀ : Scheme.{0}} (t' : T₀ ⟶ Spec (CommRingCat.of S')) (P : SchemeHomOver t' u₁.1.f),
          FactorsThrough Cu₁.levK P ↔ ∃ P₀ : T₀ ⟶ Cu.K, P₀ ≫ Cu.levK = P.1 ≫ g₁))
    (h : FakeEllipticCurve.IsPullbackVia (ψ.comp φ) u.1 u''.1 g) (hP : (u''.2.P).1 ≫ g = Spec.map (CommRingCat.ofHom (ψ.comp φ)) ≫ (u.2.P).1)
    (hC : (∀ {T₀ : Scheme.{0}} (t' : T₀ ⟶ Spec (CommRingCat.of S'')) (P : SchemeHomOver t' u''.1.f),
          FactorsThrough Cu''.levK P → ∃ P₀ : T₀ ⟶ Cu.K, P₀ ≫ Cu.levK = P.1 ≫ g)) :
    ∃ g' : u''.1.A ⟶ u₁.1.A, g' ≫ g₁ = g ∧
      FakeEllipticCurve.IsPullbackVia ψ u₁.1 u''.1 g' ∧ (u''.2.P).1 ≫ g' = Spec.map (CommRingCat.ofHom ψ) ≫ (u₁.2.P).1 ∧
      (∀ {T₀ : Scheme.{0}} (t' : T₀ ⟶ Spec (CommRingCat.of S'')) (P : SchemeHomOver t' u''.1.f),
          FactorsThrough Cu''.levK P → ∃ P₀ : T₀ ⟶ Cu₁.K, P₀ ≫ Cu₁.levK = P.1 ≫ g') := by
  obtain ⟨hg₁, hmul₁, hact₁, hlev₁⟩ := h₁
  obtain ⟨hg, hmul, hact, hlev⟩ := h
  have hcond : g ≫ u.1.f = (u''.1.f ≫ Spec.map (CommRingCat.ofHom ψ)) ≫ Spec.map (CommRingCat.ofHom φ) := by
    rw [hg.w, CanT.specMap_comp, Category.assoc]
  let G : u''.1.A ⟶ u₁.1.A := hg₁.lift g (u''.1.f ≫ Spec.map (CommRingCat.ofHom ψ)) hcond
  have hGg : G ≫ g₁ = g := hg₁.lift_fst _ _ _
  have hGf : G ≫ u₁.1.f = u''.1.f ≫ Spec.map (CommRingCat.ofHom ψ) := hg₁.lift_snd _ _ _
  have hGpb : CategoryTheory.IsPullback G u''.1.f u₁.1.f (Spec.map (CommRingCat.ofHom ψ)) := by
    refine CategoryTheory.IsPullback.of_right ?_ hGf hg₁
    rw [hGg, ← CanT.specMap_comp]
    exact hg
  have hGmul : ∀ {T : Scheme.{0}} (t' : T ⟶ Spec (CommRingCat.of S'')) (P₀ Q₀ : SchemeHomOver t' u''.1.f),
      (u''.1.L.mul t' P₀ Q₀).1 ≫ G =
        (u₁.1.L.mul (t' ≫ Spec.map (CommRingCat.ofHom ψ))
          ⟨P₀.1 ≫ G, by rw [Category.assoc, hGpb.w, ← Category.assoc, P₀.2]⟩
          ⟨Q₀.1 ≫ G, by rw [Category.assoc, hGpb.w, ← Category.assoc, Q₀.2]⟩).1 := by
    intro T t' P₀ Q₀
    apply hg₁.hom_ext
    · rw [Category.assoc, hGg, hmul t' P₀ Q₀, hmul₁]
      apply CanT.mul_val_congr u.1.L
      · rw [Category.assoc, CanT.specMap_comp]
      · simp only [Category.assoc, hGg]
      · simp only [Category.assoc, hGg]
    · rw [(u₁.1.L.mul _ _ _).2, Category.assoc ((u''.1.L.mul t' P₀ Q₀).1) G u₁.1.f, hGf, ← Category.assoc,
        (u''.1.L.mul t' P₀ Q₀).2]
  have hGact : ∀ x : ↥Λ, u''.1.act x ≫ G = G ≫ u₁.1.act x := by
    intro x
    apply hg₁.hom_ext
    · rw [Category.assoc, hGg, hact, Category.assoc, hact₁, ← Category.assoc, hGg]
    · rw [Category.assoc, hGf, ← Category.assoc, u''.1.act_over, Category.assoc, u₁.1.act_over, hGf]
  refine ⟨G, hGg, ⟨hGpb, hGmul, hGact, ?_⟩, ?_, ?_⟩
  · intro T t' Pt hPt
    obtain ⟨P₀, hP₀⟩ := hlev t' Pt hPt
    exact h₁L (t' ≫ Spec.map (CommRingCat.ofHom ψ)) ⟨Pt.1 ≫ G, by rw [Category.assoc, hGpb.w, ← Category.assoc, Pt.2]⟩
      ⟨P₀, by rw [hP₀, Category.assoc, hGg]⟩
  · apply hg₁.hom_ext
    · rw [Category.assoc, hGg, hP, Category.assoc, h₁P, ← Category.assoc, ← CanT.specMap_comp]
    · rw [Category.assoc, hGf, ← Category.assoc, (u''.2.P).2, Category.assoc, (u₁.2.P).2, Category.id_comp,
        Category.comp_id]
  · intro T t' Pt hPt
    obtain ⟨P₀, hP₀⟩ := hC t' Pt hPt
    have h2 := (h₁C (t' ≫ Spec.map (CommRingCat.ofHom ψ)) ⟨Pt.1 ≫ G, by rw [Category.assoc, hGpb.w, ← Category.assoc, Pt.2]⟩).mpr
      ⟨P₀, by rw [hP₀, Category.assoc, hGg]⟩
    exact h2

end S_CerednikDrinfeld_QM_FakeEllipticCurve_WithFullLevel_exists_isPullbackVia_comp_eq_of_isPullbackVia_comp
end P2MW
export P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_WithFullLevel_exists_isPullbackVia_comp_eq_of_isPullbackVia_comp (solution)
