-- Prove2me | solution 1 for CerednikDrinfeld.QM.FakeEllipticCurve.FullLevel.exists_comp_eq_specMap_comp_of_isPullbackVia
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.837917+00:00
-- url     : https://prove2.me/submissions/50ecf317-08be-5b18-8bf2-9773beb532ca

import Definitions.Def_CerednikDrinfeld_QMFineModuli
import Definitions.Def_CerednikDrinfeld_QMFormalModuleOf
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_FullLevel_exists_comp_eq_specMap_comp_of_isPullbackVia

set_option autoImplicit false

open scoped TensorProduct Quaternion NumberField
p2m_open "CategoryTheory AlgebraicGeometry QuaternionAlgebra CerednikDrinfeld P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_FullLevel_exists_comp_eq_specMap_comp_of_isPullbackVia.CerednikDrinfeld CerednikDrinfeld.QM P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_FullLevel_exists_comp_eq_specMap_comp_of_isPullbackVia.CerednikDrinfeld.QM NeronModelInfra"

set_option linter.unusedVariables false

open GoodReductionJacobian

namespace CerednikDrinfeld
p2m_export "CerednikDrinfeld" "QM.FakeEllipticCurve"
namespace QM
p2m_export "CerednikDrinfeld.QM" "FakeEllipticCurve.sectionAt mapPt_coe pushPt nsmulPt geomPoint FakeEllipticCurve FakeEllipticCurve.IsPullbackVia"
namespace FakeEllipticCurve
p2m_export "CerednikDrinfeld.QM.FakeEllipticCurve" "sectionAt FullLevel IsPullback A f act L act_over IsPullbackVia"
namespace PullbackFullLevelAux
p2m_open "CerednikDrinfeld.QM.FakeEllipticCurve CerednikDrinfeld.QM CerednikDrinfeld"

theorem nsmul_comp {S : Type} [CommRing S] {A : Scheme.{0}} {f : A ⟶ Spec (CommRingCat.of S)}
    (L : RelativeGroupLaw S f) {T T' : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of S)) (t' : T' ⟶ Spec (CommRingCat.of S))
    (ψ : T' ⟶ T) (hψ : ψ ≫ t = t') (k : ℕ) (x : SchemeHomOver t f) :
    schemeHomOverComp ψ hψ (nsmulPt L t k x) = nsmulPt L t' k (schemeHomOverComp ψ hψ x) := by
  induction k with
  | zero => simp only [nsmulPt]; exact L.one_natural t t' ψ hψ
  | succ k ih => simp only [nsmulPt]; rw [L.mul_natural, ih]

variable {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} {N : ℕ}
  {S S' : Type} [CommRing S] [CommRing S'] {φ : S →+* S'}
  {E : FakeEllipticCurve Λ N S} {E' : FakeEllipticCurve Λ N S'} {g : E'.A ⟶ E.A}

def imPt (hw : g ≫ E.f = E'.f ≫ Spec.map (CommRingCat.ofHom φ))
    {T : Scheme.{0}} {t' : T ⟶ Spec (CommRingCat.of S')} {t : T ⟶ Spec (CommRingCat.of S)}
    (ht : t' ≫ Spec.map (CommRingCat.ofHom φ) = t) (R : SchemeHomOver t' E'.f) : SchemeHomOver t E.f :=
  ⟨R.1 ≫ g, by rw [Category.assoc, hw, ← Category.assoc, R.2, ht]⟩

@[scoped simp] theorem imPt_coe (hw : g ≫ E.f = E'.f ≫ Spec.map (CommRingCat.ofHom φ))
    {T : Scheme.{0}} {t' : T ⟶ Spec (CommRingCat.of S')} {t : T ⟶ Spec (CommRingCat.of S)}
    (ht : t' ≫ Spec.map (CommRingCat.ofHom φ) = t) (R : SchemeHomOver t' E'.f) :
    (imPt hw ht R).1 = R.1 ≫ g := rfl

theorem imPt_injective (hpb : CategoryTheory.IsPullback g E'.f E.f (Spec.map (CommRingCat.ofHom φ)))
    {T : Scheme.{0}} {t' : T ⟶ Spec (CommRingCat.of S')} {t : T ⟶ Spec (CommRingCat.of S)}
    (ht : t' ≫ Spec.map (CommRingCat.ofHom φ) = t) {R₁ R₂ : SchemeHomOver t' E'.f}
    (h : imPt hpb.w ht R₁ = imPt hpb.w ht R₂) : R₁ = R₂ :=
  Subtype.ext (hpb.hom_ext (congrArg Subtype.val h) (by rw [R₁.2, R₂.2]))

theorem imPt_surjective (hpb : CategoryTheory.IsPullback g E'.f E.f (Spec.map (CommRingCat.ofHom φ)))
    {T : Scheme.{0}} {t' : T ⟶ Spec (CommRingCat.of S')} {t : T ⟶ Spec (CommRingCat.of S)}
    (ht : t' ≫ Spec.map (CommRingCat.ofHom φ) = t) (R₀ : SchemeHomOver t E.f) :
    ∃ R : SchemeHomOver t' E'.f, imPt hpb.w ht R = R₀ := by
  subst ht
  exact ⟨⟨hpb.lift R₀.1 t' R₀.2, hpb.lift_snd _ _ _⟩, Subtype.ext (hpb.lift_fst _ _ _)⟩

theorem imPt_mul (hpb : CategoryTheory.IsPullback g E'.f E.f (Spec.map (CommRingCat.ofHom φ)))
    (hmul : ∀ {T : Scheme.{0}} (t' : T ⟶ Spec (CommRingCat.of S')) (P Q : SchemeHomOver t' E'.f),
      (E'.L.mul t' P Q).1 ≫ g =
        (E.L.mul (t' ≫ Spec.map (CommRingCat.ofHom φ))
          ⟨P.1 ≫ g, by rw [Category.assoc, hpb.w, ← Category.assoc, P.2]⟩
          ⟨Q.1 ≫ g, by rw [Category.assoc, hpb.w, ← Category.assoc, Q.2]⟩).1)
    {T : Scheme.{0}} {t' : T ⟶ Spec (CommRingCat.of S')} {t : T ⟶ Spec (CommRingCat.of S)}
    (ht : t' ≫ Spec.map (CommRingCat.ofHom φ) = t) (R Q : SchemeHomOver t' E'.f) :
    imPt hpb.w ht (E'.L.mul t' R Q) = E.L.mul t (imPt hpb.w ht R) (imPt hpb.w ht Q) := by
  subst ht
  exact Subtype.ext (hmul t' R Q)

theorem imPt_one (hpb : CategoryTheory.IsPullback g E'.f E.f (Spec.map (CommRingCat.ofHom φ)))
    (hmul : ∀ {T : Scheme.{0}} (t' : T ⟶ Spec (CommRingCat.of S')) (P Q : SchemeHomOver t' E'.f),
      (E'.L.mul t' P Q).1 ≫ g =
        (E.L.mul (t' ≫ Spec.map (CommRingCat.ofHom φ))
          ⟨P.1 ≫ g, by rw [Category.assoc, hpb.w, ← Category.assoc, P.2]⟩
          ⟨Q.1 ≫ g, by rw [Category.assoc, hpb.w, ← Category.assoc, Q.2]⟩).1)
    {T : Scheme.{0}} {t' : T ⟶ Spec (CommRingCat.of S')} {t : T ⟶ Spec (CommRingCat.of S)}
    (ht : t' ≫ Spec.map (CommRingCat.ofHom φ) = t) :
    imPt hpb.w ht (E'.L.one t') = E.L.one t := by
  have h : E.L.mul t (imPt hpb.w ht (E'.L.one t')) (imPt hpb.w ht (E'.L.one t')) = imPt hpb.w ht (E'.L.one t') := by
    rw [← imPt_mul hpb hmul ht, E'.L.one_mul]
  generalize imPt hpb.w ht (E'.L.one t') = x at h ⊢
  calc x
      = E.L.mul t (E.L.one t) x := (E.L.one_mul t x).symm
    _ = E.L.mul t (E.L.mul t (E.L.inv t x) x) x := by rw [E.L.inv_mul_cancel]
    _ = E.L.mul t (E.L.inv t x) (E.L.mul t x x) := by rw [E.L.mul_assoc]
    _ = E.L.mul t (E.L.inv t x) x := by rw [h]
    _ = E.L.one t := E.L.inv_mul_cancel t x

theorem imPt_nsmul (hpb : CategoryTheory.IsPullback g E'.f E.f (Spec.map (CommRingCat.ofHom φ)))
    (hmul : ∀ {T : Scheme.{0}} (t' : T ⟶ Spec (CommRingCat.of S')) (P Q : SchemeHomOver t' E'.f),
      (E'.L.mul t' P Q).1 ≫ g =
        (E.L.mul (t' ≫ Spec.map (CommRingCat.ofHom φ))
          ⟨P.1 ≫ g, by rw [Category.assoc, hpb.w, ← Category.assoc, P.2]⟩
          ⟨Q.1 ≫ g, by rw [Category.assoc, hpb.w, ← Category.assoc, Q.2]⟩).1)
    {T : Scheme.{0}} {t' : T ⟶ Spec (CommRingCat.of S')} {t : T ⟶ Spec (CommRingCat.of S)}
    (ht : t' ≫ Spec.map (CommRingCat.ofHom φ) = t) (k : ℕ) (R : SchemeHomOver t' E'.f) :
    imPt hpb.w ht (nsmulPt E'.L t' k R) = nsmulPt E.L t k (imPt hpb.w ht R) := by
  induction k with
  | zero => simp only [nsmulPt]; exact imPt_one hpb hmul ht
  | succ k ih => simp only [nsmulPt]; rw [imPt_mul hpb hmul ht, ih]

theorem imPt_act (hw : g ≫ E.f = E'.f ≫ Spec.map (CommRingCat.ofHom φ))
    (hact : ∀ x : ↥Λ, E'.act x ≫ g = g ≫ E.act x)
    {T : Scheme.{0}} {t' : T ⟶ Spec (CommRingCat.of S')} {t : T ⟶ Spec (CommRingCat.of S)}
    (ht : t' ≫ Spec.map (CommRingCat.ofHom φ) = t) (x : ↥Λ) (R : SchemeHomOver t' E'.f) :
    imPt hw ht (pushPt (E'.act x) (E'.act_over x) R) = pushPt (E.act x) (E.act_over x) (imPt hw ht R) :=
  Subtype.ext (by simp only [imPt_coe, pushPt, mapPt_coe, Category.assoc, hact])

theorem act_comp {T T' : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of S)) (t' : T' ⟶ Spec (CommRingCat.of S))
    (ψ : T' ⟶ T) (hψ : ψ ≫ t = t') (x : ↥Λ) (R : SchemeHomOver t E.f) :
    schemeHomOverComp ψ hψ (pushPt (E.act x) (E.act_over x) R) = pushPt (E.act x) (E.act_over x) (schemeHomOverComp ψ hψ R) :=
  Subtype.ext (by simp only [schemeHomOverComp_coe, pushPt, mapPt_coe, Category.assoc])

end CerednikDrinfeld.QM.FakeEllipticCurve.PullbackFullLevelAux
p2m_reactivate "P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_FullLevel_exists_comp_eq_specMap_comp_of_isPullbackVia.CerednikDrinfeld P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_FullLevel_exists_comp_eq_specMap_comp_of_isPullbackVia.CerednikDrinfeld.QM P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_FullLevel_exists_comp_eq_specMap_comp_of_isPullbackVia.CerednikDrinfeld.QM.FakeEllipticCurve P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_FullLevel_exists_comp_eq_specMap_comp_of_isPullbackVia.CerednikDrinfeld.QM.FakeEllipticCurve.PullbackFullLevelAux"
p2m_reactivate "P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_FullLevel_exists_comp_eq_specMap_comp_of_isPullbackVia.CerednikDrinfeld P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_FullLevel_exists_comp_eq_specMap_comp_of_isPullbackVia.CerednikDrinfeld.QM P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_FullLevel_exists_comp_eq_specMap_comp_of_isPullbackVia.CerednikDrinfeld.QM.FakeEllipticCurve"
p2m_reactivate "P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_FullLevel_exists_comp_eq_specMap_comp_of_isPullbackVia.CerednikDrinfeld P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_FullLevel_exists_comp_eq_specMap_comp_of_isPullbackVia.CerednikDrinfeld.QM"
p2m_reactivate "P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_FullLevel_exists_comp_eq_specMap_comp_of_isPullbackVia.CerednikDrinfeld"

open CerednikDrinfeld.QM.FakeEllipticCurve.PullbackFullLevelAux

theorem solution
    {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} {N : ℕ} (m : ℕ)
    {S S' : Type} [CommRing S] [CommRing S'] (φ : S →+* S')
    (E : FakeEllipticCurve Λ N S) (E' : FakeEllipticCurve Λ N S') (g : E'.A ⟶ E.A)
    (hg : FakeEllipticCurve.IsPullbackVia φ E E' g) (P : E.FullLevel m) :
    ∃ P' : E'.FullLevel m, (P'.P).1 ≫ g = Spec.map (CommRingCat.ofHom φ) ≫ (P.P).1 := by
  obtain ⟨hpb, hmul, hact, -⟩ := hg

  obtain ⟨P', hP'g⟩ : ∃ P' : SchemeHomOver (𝟙 (Spec (CommRingCat.of S'))) E'.f,
      P'.1 ≫ g = Spec.map (CommRingCat.ofHom φ) ≫ (P.P).1 :=
    ⟨⟨hpb.lift (Spec.map (CommRingCat.ofHom φ) ≫ (P.P).1) (𝟙 _)
        (by rw [Category.assoc, P.P.2, Category.comp_id, Category.id_comp]), hpb.lift_snd _ _ _⟩,
      hpb.lift_fst _ _ _⟩

  have key0 : imPt hpb.w (Category.id_comp (Spec.map (CommRingCat.ofHom φ))) P' =
      schemeHomOverComp (Spec.map (CommRingCat.ofHom φ)) (Category.comp_id _) P.P :=
    Subtype.ext hP'g

  have hgeo : ∀ (k : Type) [Field k] (sk : S' →+* k),
      geomPoint k sk ≫ Spec.map (CommRingCat.ofHom φ) = geomPoint k (sk.comp φ) := by
    intro k _ sk
    simp only [geomPoint, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
  have hsec : ∀ (k : Type) [Field k] (sk : S' →+* k),
      imPt hpb.w (hgeo k sk) (FakeEllipticCurve.sectionAt P' k sk) = FakeEllipticCurve.sectionAt P.P k (sk.comp φ) := by
    intro k _ sk
    apply Subtype.ext
    simp only [imPt_coe, FakeEllipticCurve.sectionAt, schemeHomOverComp_coe, Category.assoc, hP'g]
    rw [← Category.assoc, hgeo k sk]
  refine ⟨⟨P', ?_, ?_, ?_⟩, hP'g⟩
  ·
    apply imPt_injective hpb (Category.id_comp (Spec.map (CommRingCat.ofHom φ)))
    rw [imPt_nsmul hpb hmul, imPt_one hpb hmul, key0, ← nsmul_comp, P.torsion, E.L.one_natural]
  ·
    intro k _ _ sk Q hQ
    have hQ' : nsmulPt E.L (geomPoint k (sk.comp φ)) m (imPt hpb.w (hgeo k sk) Q) = E.L.one _ := by
      rw [← imPt_nsmul hpb hmul (hgeo k sk), hQ, imPt_one hpb hmul (hgeo k sk)]
    obtain ⟨x, hx⟩ := P.generates k (sk.comp φ) (imPt hpb.w (hgeo k sk) Q) hQ'
    refine ⟨x, imPt_injective hpb (hgeo k sk) ?_⟩
    rw [imPt_act hpb.w hact (hgeo k sk), hsec k sk, hx]
  ·
    intro k _ _ sk x
    rw [← P.annihilator k (sk.comp φ) x, ← hsec k sk, ← imPt_act hpb.w hact (hgeo k sk)]
    constructor
    · intro h; rw [h, imPt_one hpb hmul (hgeo k sk)]
    · intro h; exact imPt_injective hpb (hgeo k sk) (by rw [h, imPt_one hpb hmul (hgeo k sk)])

end S_CerednikDrinfeld_QM_FakeEllipticCurve_FullLevel_exists_comp_eq_specMap_comp_of_isPullbackVia
end P2MW
export P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_FullLevel_exists_comp_eq_specMap_comp_of_isPullbackVia (solution)
