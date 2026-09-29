-- Prove2me | solution 1 for CerednikDrinfeld.QM.FakeEllipticCurve.IsPullbackVia.exists_comp_eq_and_isPullbackVia_of_comp_eq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.837917+00:00
-- url     : https://prove2.me/submissions/4bb5b779-4341-5183-8e72-150baca96115

import Mathlib
import Definitions.Def_CerednikDrinfeld_QMFormalModuleOf
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_IsPullbackVia_exists_comp_eq_and_isPullbackVia_of_comp_eq

set_option autoImplicit false

p2m_open "CategoryTheory AlgebraicGeometry NeronModelInfra GoodReductionJacobian CerednikDrinfeld P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_IsPullbackVia_exists_comp_eq_and_isPullbackVia_of_comp_eq.CerednikDrinfeld CerednikDrinfeld.QM P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_IsPullbackVia_exists_comp_eq_and_isPullbackVia_of_comp_eq.CerednikDrinfeld.QM CerednikDrinfeld.QM.FakeEllipticCurve P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_IsPullbackVia_exists_comp_eq_and_isPullbackVia_of_comp_eq.CerednikDrinfeld.QM.FakeEllipticCurve"

open scoped Quaternion

namespace CerednikDrinfeld
p2m_export "CerednikDrinfeld" "QM.FakeEllipticCurve.IsPullbackVia tree QM.FakeEllipticCurve"
namespace QM
p2m_export "CerednikDrinfeld.QM" "FakeEllipticCurve.IsPullbackVia FactorsThrough FakeEllipticCurve"
namespace FakeEllipticCurve
p2m_export "CerednikDrinfeld.QM.FakeEllipticCurve" "IsPullbackVia IsPullback A f L C lev act_over"
namespace PullbackPaste
p2m_open "CerednikDrinfeld.QM.FakeEllipticCurve CerednikDrinfeld.QM CerednikDrinfeld"

theorem mul_val_congr {R : Type} [CommRing R] {A : Scheme.{0}} {f : A ⟶ Spec (CommRingCat.of R)}
    (L : RelativeGroupLaw R f) {T : Scheme.{0}} {t₁ t₂ : T ⟶ Spec (CommRingCat.of R)} (h : t₁ = t₂)
    (P₁ Q₁ : SchemeHomOver t₁ f) (P₂ Q₂ : SchemeHomOver t₂ f) (hP : P₁.1 = P₂.1) (hQ : Q₁.1 = Q₂.1) :
    (L.mul t₁ P₁ Q₁).1 = (L.mul t₂ P₂ Q₂).1 := by
  subst h
  obtain rfl : P₁ = P₂ := Subtype.ext hP
  obtain rfl : Q₁ = Q₂ := Subtype.ext hQ
  rfl

end CerednikDrinfeld.QM.FakeEllipticCurve.PullbackPaste

open CerednikDrinfeld.QM.FakeEllipticCurve.PullbackPaste in
theorem solution
    {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} {N : ℕ}
    {S S' S'' : Type} [CommRing S] [CommRing S'] [CommRing S'']
    (φ : S →+* S') (ψ : S' →+* S'') (χ : S →+* S'') (hχ : ψ.comp φ = χ)
    (E : FakeEllipticCurve Λ N S) (E' : FakeEllipticCurve Λ N S') (E'' : FakeEllipticCurve Λ N S'')

    (g' : E'.A ⟶ E.A) (h' : IsPullbackVia φ E E' g')
    (hlev' : ∀ {T : Scheme.{0}} (t' : T ⟶ Spec (CommRingCat.of S')) (P : SchemeHomOver t' E'.f),
      (∃ P₀ : T ⟶ E.C, P₀ ≫ E.lev = P.1 ≫ g') → FactorsThrough E'.lev P)

    (g : E''.A ⟶ E.A) (h : IsPullbackVia χ E E'' g) :
    ∃ g'' : E''.A ⟶ E'.A, g'' ≫ g' = g ∧ g'' ≫ E'.f = E''.f ≫ Spec.map (CommRingCat.ofHom ψ) ∧
      (∀ k : E''.A ⟶ E'.A, k ≫ g' = g → k ≫ E'.f = E''.f ≫ Spec.map (CommRingCat.ofHom ψ) → k = g'') ∧
      IsPullbackVia ψ E' E'' g'' := by
  subst hχ
  obtain ⟨hg', h'mul, h'act, h'lev⟩ := h'
  obtain ⟨hg, hmul, hact, hlev⟩ := h

  have hcomp : Spec.map (CommRingCat.ofHom (ψ.comp φ)) =
      Spec.map (CommRingCat.ofHom ψ) ≫ Spec.map (CommRingCat.ofHom φ) := by
    rw [CommRingCat.ofHom_comp, Spec.map_comp]

  have hw : g ≫ E.f = (E''.f ≫ Spec.map (CommRingCat.ofHom ψ)) ≫ Spec.map (CommRingCat.ofHom φ) := by
    rw [hg.w, hcomp, Category.assoc]
  set e : E''.A ⟶ E'.A := hg'.lift g (E''.f ≫ Spec.map (CommRingCat.ofHom ψ)) hw with he
  have he₁ : e ≫ g' = g := hg'.lift_fst _ _ _
  have he₂ : e ≫ E'.f = E''.f ≫ Spec.map (CommRingCat.ofHom ψ) := hg'.lift_snd _ _ _

  have hsq : CategoryTheory.IsPullback e E''.f E'.f (Spec.map (CommRingCat.ofHom ψ)) := by
    refine CategoryTheory.IsPullback.of_right ?_ he₂ hg'
    rw [he₁, ← hcomp]
    exact hg
  refine ⟨e, he₁, he₂, ?_, hsq, ?_, ?_, ?_⟩
  ·
    intro k hk₁ hk₂
    exact hg'.hom_ext (by rw [hk₁, he₁]) (by rw [hk₂, he₂])
  ·
    intro T t' P Q
    apply hg'.hom_ext
    · rw [Category.assoc, he₁, hmul t' P Q, h'mul]
      apply mul_val_congr E.L
      · rw [Category.assoc, hcomp]
      · show P.1 ≫ g = (P.1 ≫ e) ≫ g'
        rw [Category.assoc, he₁]
      · show Q.1 ≫ g = (Q.1 ≫ e) ≫ g'
        rw [Category.assoc, he₁]
    · rw [Category.assoc, he₂, (E'.L.mul _ _ _).2, ← Category.assoc, (E''.L.mul t' P Q).2]
  ·
    intro x
    apply hg'.hom_ext
    · rw [Category.assoc, he₁, hact x, Category.assoc, h'act x, ← Category.assoc, he₁]
    · rw [Category.assoc, he₂, ← Category.assoc, E''.act_over x, Category.assoc, E'.act_over x, he₂]
  ·
    intro T t' P hP
    obtain ⟨P₀, hP₀⟩ := hlev t' P hP
    exact hlev' (t' ≫ Spec.map (CommRingCat.ofHom ψ))
      ⟨P.1 ≫ e, by rw [Category.assoc, he₂, ← Category.assoc, P.2]⟩ ⟨P₀, by rw [hP₀, Category.assoc, he₁]⟩

end S_CerednikDrinfeld_QM_FakeEllipticCurve_IsPullbackVia_exists_comp_eq_and_isPullbackVia_of_comp_eq
end P2MW
export P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_IsPullbackVia_exists_comp_eq_and_isPullbackVia_of_comp_eq (solution)
