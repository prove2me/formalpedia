-- Prove2me | solution 1 for CerednikDrinfeld.QM.FakeEllipticCurve.exists_hom_extension_of_isPullback_of_isDiscreteValuationRing
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.141142+00:00
-- url     : https://prove2.me/submissions/72c133ad-563c-583e-8294-2bd95e5fedbc

import Definitions.Def_CerednikDrinfeld_FakeEllipticFrobenius
import Theorems.Thm_AlgebraicGeometry_eq_of_forall_specMap_comp_eq_of_smooth_of_isSeparated
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawBaseChange
import Definitions.Def_AlgebraicGeometry_NeronModelEndomorphismExtension
import Theorems.Thm_GoodReductionJacobian_AbelianSchemePropertyBundle_existsUnique_extension_hom_of_genericFibre
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_exists_hom_extension_of_isPullback_of_isDiscreteValuationRing
p2m_attr_erase "instance" "instTopologicallyFGOfFiniteType"
p2m_attr_erase "simp" "RegularLocalRingQuotientAscent.dualNumberFst_apply"

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra CerednikDrinfeld CerednikDrinfeld.QM CerednikDrinfeld.QM.FakeEllipticCurve
open scoped Quaternion
open GoodReductionJacobian

namespace E1DvrAux

noncomputable def mulMor {R : Type} [CommRing R] {A : Scheme.{0}} {f : A ⟶ Spec (CommRingCat.of R)}
    (L : GoodReductionJacobian.RelativeGroupLaw R f) : pullback f f ⟶ A :=
  (L.mul (pullback.fst f f ≫ f) ⟨pullback.fst f f, rfl⟩ ⟨pullback.snd f f, pullback.condition.symm⟩).1

theorem mulMor_over {R : Type} [CommRing R] {A : Scheme.{0}} {f : A ⟶ Spec (CommRingCat.of R)}
    (L : GoodReductionJacobian.RelativeGroupLaw R f) : mulMor L ≫ f = pullback.fst f f ≫ f :=
  (L.mul (pullback.fst f f ≫ f) _ _).2

theorem mul_val_eq_lift_mulMor {R : Type} [CommRing R] {A : Scheme.{0}} {f : A ⟶ Spec (CommRingCat.of R)}
    (L : GoodReductionJacobian.RelativeGroupLaw R f) {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of R))
    (P Q : SchemeHomOver t f) :
    (L.mul t P Q).1 = pullback.lift P.1 Q.1 (P.2.trans Q.2.symm) ≫ mulMor L := by
  have hψ : pullback.lift P.1 Q.1 (P.2.trans Q.2.symm) ≫ (pullback.fst f f ≫ f) = t := by
    rw [← Category.assoc, pullback.lift_fst, P.2]
  have hnat := L.mul_natural (pullback.fst f f ≫ f) t (pullback.lift P.1 Q.1 (P.2.trans Q.2.symm)) hψ
    ⟨pullback.fst f f, rfl⟩ ⟨pullback.snd f f, pullback.condition.symm⟩
  have hP : GoodReductionJacobian.schemeHomOverComp (pullback.lift P.1 Q.1 (P.2.trans Q.2.symm)) hψ ⟨pullback.fst f f, rfl⟩ = P :=
    Subtype.ext (pullback.lift_fst _ _ _)
  have hQ : GoodReductionJacobian.schemeHomOverComp (pullback.lift P.1 Q.1 (P.2.trans Q.2.symm)) hψ
      ⟨pullback.snd f f, pullback.condition.symm⟩ = Q :=
    Subtype.ext (pullback.lift_snd _ _ _)
  rw [hP, hQ] at hnat
  rw [← hnat]
  rfl

end E1DvrAux

theorem density
    {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} {N : ℕ}
    {R : Type} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    {K : Type} [Field K] [Algebra R K] [IsFractionRing R K]
    (𝒜 𝒟 : FakeEllipticCurve Λ N R) (E d : FakeEllipticCurve Λ N K)
    (gE : E.A ⟶ 𝒜.A) (hgE : CategoryTheory.IsPullback gE E.f 𝒜.f (Spec.map (CommRingCat.ofHom (algebraMap R K))))
    (hgE_mul : ∀ {T : Scheme.{0}} (t' : T ⟶ Spec (CommRingCat.of K)) (P Q : SchemeHomOver t' E.f),
      (E.L.mul t' P Q).1 ≫ gE =
        (𝒜.L.mul (t' ≫ Spec.map (CommRingCat.ofHom (algebraMap R K)))
          ⟨P.1 ≫ gE, by rw [Category.assoc, hgE.w, ← Category.assoc, P.2]⟩
          ⟨Q.1 ≫ gE, by rw [Category.assoc, hgE.w, ← Category.assoc, Q.2]⟩).1)
    (hgE_act : ∀ x : ↥Λ, E.act x ≫ gE = gE ≫ 𝒜.act x)
    (gd : d.A ⟶ 𝒟.A) (hgd : CategoryTheory.IsPullback gd d.f 𝒟.f (Spec.map (CommRingCat.ofHom (algebraMap R K))))
    (hgd_mul : ∀ {T : Scheme.{0}} (t' : T ⟶ Spec (CommRingCat.of K)) (P Q : SchemeHomOver t' d.f),
      (d.L.mul t' P Q).1 ≫ gd =
        (𝒟.L.mul (t' ≫ Spec.map (CommRingCat.ofHom (algebraMap R K)))
          ⟨P.1 ≫ gd, by rw [Category.assoc, hgd.w, ← Category.assoc, P.2]⟩
          ⟨Q.1 ≫ gd, by rw [Category.assoc, hgd.w, ← Category.assoc, Q.2]⟩).1)
    (hgd_act : ∀ x : ↥Λ, d.act x ≫ gd = gd ≫ 𝒟.act x)
    (φ : E.A ⟶ d.A) (hφ : φ ≫ d.f = E.f)
    (hφ_mul : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of K)) (P Q : SchemeHomOver t E.f),
      mapPt φ hφ (E.L.mul t P Q) = d.L.mul t (mapPt φ hφ P) (mapPt φ hφ Q))
    (hφ_act : ∀ x : ↥Λ, E.act x ≫ φ = φ ≫ d.act x)
    (Φ : 𝒜.A ⟶ 𝒟.A) (hΦ : Φ ≫ 𝒟.f = 𝒜.f) (hext : gE ≫ Φ = φ ≫ gd) :
    (∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of R)) (P Q : SchemeHomOver t 𝒜.f),
        mapPt Φ hΦ (𝒜.L.mul t P Q) = 𝒟.L.mul t (mapPt Φ hΦ P) (mapPt Φ hΦ Q)) ∧
      (∀ x : ↥Λ, 𝒜.act x ≫ Φ = Φ ≫ 𝒟.act x) := by
  haveI : Smooth 𝒜.f := 𝒜.bundle.smooth
  haveI : IsProper 𝒟.f := 𝒟.bundle.proper
  have halg : Spec.map (CommRingCat.ofHom (algebraMap R (AlgebraicClosure K))) =
      Spec.map (CommRingCat.ofHom (algebraMap K (AlgebraicClosure K))) ≫ Spec.map (CommRingCat.ofHom (algebraMap R K)) := by
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, ← IsScalarTower.algebraMap_eq]

  have key_pt : ∀ x : Spec (CommRingCat.of (AlgebraicClosure K)) ⟶ 𝒜.A,
      x ≫ 𝒜.f = Spec.map (CommRingCat.ofHom (algebraMap R (AlgebraicClosure K))) →
      ∃ x' : SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap K (AlgebraicClosure K)))) E.f, x'.1 ≫ gE = x := by
    intro x hx
    refine ⟨⟨hgE.lift x (Spec.map (CommRingCat.ofHom (algebraMap K (AlgebraicClosure K)))) (by rw [hx, halg]), hgE.lift_snd _ _ _⟩,
      hgE.lift_fst _ _ _⟩

  have mulA_congr : ∀ {T : Scheme.{0}} {t₁ t₂ : T ⟶ Spec (CommRingCat.of R)} (h : t₁ = t₂)
      (P₁ Q₁ : SchemeHomOver t₁ 𝒜.f) (P₂ Q₂ : SchemeHomOver t₂ 𝒜.f), P₁.1 = P₂.1 → Q₁.1 = Q₂.1 →
      (𝒜.L.mul t₁ P₁ Q₁).1 = (𝒜.L.mul t₂ P₂ Q₂).1 := by
    rintro T t₁ t₂ rfl P₁ Q₁ P₂ Q₂ hP hQ
    obtain rfl : P₁ = P₂ := Subtype.ext hP; obtain rfl : Q₁ = Q₂ := Subtype.ext hQ; rfl
  have mulD_congr : ∀ {T : Scheme.{0}} {t₁ t₂ : T ⟶ Spec (CommRingCat.of R)} (h : t₁ = t₂)
      (P₁ Q₁ : SchemeHomOver t₁ 𝒟.f) (P₂ Q₂ : SchemeHomOver t₂ 𝒟.f), P₁.1 = P₂.1 → Q₁.1 = Q₂.1 →
      (𝒟.L.mul t₁ P₁ Q₁).1 = (𝒟.L.mul t₂ P₂ Q₂).1 := by
    rintro T t₁ t₂ rfl P₁ Q₁ P₂ Q₂ hP hQ
    obtain rfl : P₁ = P₂ := Subtype.ext hP; obtain rfl : Q₁ = Q₂ := Subtype.ext hQ; rfl

  let ΦΦ : pullback 𝒜.f 𝒜.f ⟶ pullback 𝒟.f 𝒟.f :=
    pullback.map 𝒜.f 𝒜.f 𝒟.f 𝒟.f Φ Φ (𝟙 _) (by rw [hΦ, Category.comp_id]) (by rw [hΦ, Category.comp_id])
  have hΦΦ_fst : ΦΦ ≫ pullback.fst 𝒟.f 𝒟.f = pullback.fst 𝒜.f 𝒜.f ≫ Φ := pullback.lift_fst _ _ _
  have hΦΦ_snd : ΦΦ ≫ pullback.snd 𝒟.f 𝒟.f = pullback.snd 𝒜.f 𝒜.f ≫ Φ := pullback.lift_snd _ _ _

  have hm : E1DvrAux.mulMor 𝒜.L ≫ Φ = ΦΦ ≫ E1DvrAux.mulMor 𝒟.L := by
    apply AlgebraicGeometry.eq_of_forall_specMap_comp_eq_of_smooth_of_isSeparated (R := R) K
      (AlgebraicClosure K) (pullback.fst 𝒜.f 𝒜.f ≫ 𝒜.f) 𝒟.f
    · rw [Category.assoc, hΦ, E1DvrAux.mulMor_over]
    · rw [Category.assoc, E1DvrAux.mulMor_over, ← Category.assoc, hΦΦ_fst, Category.assoc, hΦ]
    · intro x hx
      obtain ⟨P', hP'⟩ := key_pt (x ≫ pullback.fst 𝒜.f 𝒜.f) (by rw [Category.assoc]; exact hx)
      obtain ⟨Q', hQ'⟩ := key_pt (x ≫ pullback.snd 𝒜.f 𝒜.f) (by rw [Category.assoc, ← pullback.condition]; exact hx)

      let Px : SchemeHomOver (x ≫ pullback.fst 𝒜.f 𝒜.f ≫ 𝒜.f) 𝒜.f := ⟨x ≫ pullback.fst 𝒜.f 𝒜.f, rfl⟩
      let Qx : SchemeHomOver (x ≫ pullback.fst 𝒜.f 𝒜.f ≫ 𝒜.f) 𝒜.f :=
        ⟨x ≫ pullback.snd 𝒜.f 𝒜.f, by rw [Category.assoc, ← pullback.condition]⟩
      have hxlift : x = pullback.lift Px.1 Qx.1 (Px.2.trans Qx.2.symm) := by
        apply pullback.hom_ext
        · exact (pullback.lift_fst _ _ _).symm
        · exact (pullback.lift_snd _ _ _).symm
      have hbase : x ≫ pullback.fst 𝒜.f 𝒜.f ≫ 𝒜.f =
          Spec.map (CommRingCat.ofHom (algebraMap K (AlgebraicClosure K))) ≫ Spec.map (CommRingCat.ofHom (algebraMap R K)) := by
        rw [hx, halg]

      have hL : x ≫ E1DvrAux.mulMor 𝒜.L ≫ Φ = ((E.L.mul (Spec.map (CommRingCat.ofHom (algebraMap K (AlgebraicClosure K)))) P' Q').1 ≫ φ) ≫ gd := by
        rw [← Category.assoc, hxlift, ← E1DvrAux.mul_val_eq_lift_mulMor 𝒜.L _ Px Qx,
          mulA_congr hbase Px Qx ⟨P'.1 ≫ gE, by rw [Category.assoc, hgE.w, ← Category.assoc, P'.2]⟩
            ⟨Q'.1 ≫ gE, by rw [Category.assoc, hgE.w, ← Category.assoc, Q'.2]⟩ hP'.symm hQ'.symm,
          ← hgE_mul, Category.assoc, hext, Category.assoc]

      let Px' : SchemeHomOver (x ≫ pullback.fst 𝒜.f 𝒜.f ≫ 𝒜.f) 𝒟.f := ⟨(x ≫ ΦΦ) ≫ pullback.fst 𝒟.f 𝒟.f, by
        simp only [Category.assoc]; rw [reassoc_of% hΦΦ_fst, hΦ]⟩
      let Qx' : SchemeHomOver (x ≫ pullback.fst 𝒜.f 𝒜.f ≫ 𝒜.f) 𝒟.f := ⟨(x ≫ ΦΦ) ≫ pullback.snd 𝒟.f 𝒟.f, by
        simp only [Category.assoc]; rw [reassoc_of% hΦΦ_snd, hΦ, ← pullback.condition]⟩
      have hxlift' : x ≫ ΦΦ = pullback.lift Px'.1 Qx'.1 (Px'.2.trans Qx'.2.symm) := by
        apply pullback.hom_ext
        · exact (pullback.lift_fst _ _ _).symm
        · exact (pullback.lift_snd _ _ _).symm
      have hR : x ≫ ΦΦ ≫ E1DvrAux.mulMor 𝒟.L = ((d.L.mul (Spec.map (CommRingCat.ofHom (algebraMap K (AlgebraicClosure K)))) (mapPt φ hφ P') (mapPt φ hφ Q')).1) ≫ gd := by
        rw [← Category.assoc, hxlift', ← E1DvrAux.mul_val_eq_lift_mulMor 𝒟.L _ Px' Qx', hgd_mul]
        refine mulD_congr hbase Px' Qx' _ _ ?_ ?_
        · show (x ≫ ΦΦ) ≫ pullback.fst 𝒟.f 𝒟.f = (P'.1 ≫ φ) ≫ gd
          rw [Category.assoc, hΦΦ_fst, ← Category.assoc, ← hP', Category.assoc, Category.assoc, hext]
        · show (x ≫ ΦΦ) ≫ pullback.snd 𝒟.f 𝒟.f = (Q'.1 ≫ φ) ≫ gd
          rw [Category.assoc, hΦΦ_snd, ← Category.assoc, ← hQ', Category.assoc, Category.assoc, hext]
      rw [hL, hR, ← hφ_mul]
      rfl
  constructor
  · intro T t P Q
    apply Subtype.ext
    show (𝒜.L.mul t P Q).1 ≫ Φ = (𝒟.L.mul t (mapPt Φ hΦ P) (mapPt Φ hΦ Q)).1
    rw [E1DvrAux.mul_val_eq_lift_mulMor 𝒜.L, E1DvrAux.mul_val_eq_lift_mulMor 𝒟.L, Category.assoc, hm, ← Category.assoc]
    congr 1
    apply pullback.hom_ext
    · rw [pullback.lift_fst, Category.assoc, hΦΦ_fst, ← Category.assoc, pullback.lift_fst]; rfl
    · rw [pullback.lift_snd, Category.assoc, hΦΦ_snd, ← Category.assoc, pullback.lift_snd]; rfl
  · intro x₀
    apply AlgebraicGeometry.eq_of_forall_specMap_comp_eq_of_smooth_of_isSeparated (R := R) K
      (AlgebraicClosure K) 𝒜.f 𝒟.f
    · rw [Category.assoc, hΦ, 𝒜.act_over]
    · rw [Category.assoc, 𝒟.act_over, hΦ]
    · intro x hx
      obtain ⟨P', hP'⟩ := key_pt x hx
      rw [← hP', Category.assoc, Category.assoc, ← Category.assoc gE, ← hgE_act, Category.assoc, hext,
        ← Category.assoc (E.act x₀), hφ_act, Category.assoc, hgd_act, ← Category.assoc gE, hext]
      simp only [Category.assoc]

theorem slot_ext
    {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} {N : ℕ}
    {R : Type} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    {K : Type} [Field K] [Algebra R K] [IsFractionRing R K]
    (𝒜 𝒟 : FakeEllipticCurve Λ N R) (E d : FakeEllipticCurve Λ N K)
    (gE : E.A ⟶ 𝒜.A) (hgE : CategoryTheory.IsPullback gE E.f 𝒜.f (Spec.map (CommRingCat.ofHom (algebraMap R K))))
    (hgE_mul : ∀ {T : Scheme.{0}} (t' : T ⟶ Spec (CommRingCat.of K)) (P Q : SchemeHomOver t' E.f),
      (E.L.mul t' P Q).1 ≫ gE =
        (𝒜.L.mul (t' ≫ Spec.map (CommRingCat.ofHom (algebraMap R K)))
          ⟨P.1 ≫ gE, by rw [Category.assoc, hgE.w, ← Category.assoc, P.2]⟩
          ⟨Q.1 ≫ gE, by rw [Category.assoc, hgE.w, ← Category.assoc, Q.2]⟩).1)
    (hgE_act : ∀ x : ↥Λ, E.act x ≫ gE = gE ≫ 𝒜.act x)
    (gd : d.A ⟶ 𝒟.A) (hgd : CategoryTheory.IsPullback gd d.f 𝒟.f (Spec.map (CommRingCat.ofHom (algebraMap R K))))
    (hgd_mul : ∀ {T : Scheme.{0}} (t' : T ⟶ Spec (CommRingCat.of K)) (P Q : SchemeHomOver t' d.f),
      (d.L.mul t' P Q).1 ≫ gd =
        (𝒟.L.mul (t' ≫ Spec.map (CommRingCat.ofHom (algebraMap R K)))
          ⟨P.1 ≫ gd, by rw [Category.assoc, hgd.w, ← Category.assoc, P.2]⟩
          ⟨Q.1 ≫ gd, by rw [Category.assoc, hgd.w, ← Category.assoc, Q.2]⟩).1)
    (hgd_act : ∀ x : ↥Λ, d.act x ≫ gd = gd ≫ 𝒟.act x)
    (φ : E.A ⟶ d.A) (hφ : φ ≫ d.f = E.f)
    (hφ_mul : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of K)) (P Q : SchemeHomOver t E.f),
      mapPt φ hφ (E.L.mul t P Q) = d.L.mul t (mapPt φ hφ P) (mapPt φ hφ Q))
    (hφ_act : ∀ x : ↥Λ, E.act x ≫ φ = φ ≫ d.act x) :
    ∃ (Φ : 𝒜.A ⟶ 𝒟.A) (hΦ : Φ ≫ 𝒟.f = 𝒜.f), gE ≫ Φ = φ ≫ gd := by

  let cE : IsPullback gE E.f 𝒜.f (specGenericFibreInclusion R K) := hgE
  let cd : IsPullback gd d.f 𝒟.f (specGenericFibreInclusion R K) := hgd
  let eE : E.A ≅ pullback 𝒜.f (specGenericFibreInclusion R K) := cE.isoPullback
  let ed : d.A ≅ pullback 𝒟.f (specGenericFibreInclusion R K) := cd.isoPullback
  have eE_fst : eE.hom ≫ pullback.fst 𝒜.f (specGenericFibreInclusion R K) = gE := cE.isoPullback_hom_fst
  have eE_snd : eE.hom ≫ pullback.snd 𝒜.f (specGenericFibreInclusion R K) = E.f := cE.isoPullback_hom_snd
  have ed_fst : ed.hom ≫ pullback.fst 𝒟.f (specGenericFibreInclusion R K) = gd := cd.isoPullback_hom_fst
  have ed_snd : ed.hom ≫ pullback.snd 𝒟.f (specGenericFibreInclusion R K) = d.f := cd.isoPullback_hom_snd

  let φK : SchemeHomOver (RelativeGroupLaw.genericFibreStr K 𝒜.f) (RelativeGroupLaw.genericFibreStr K 𝒟.f) :=
    ⟨eE.inv ≫ φ ≫ ed.hom, by
      show (eE.inv ≫ φ ≫ ed.hom) ≫ pullback.snd 𝒟.f (specGenericFibreInclusion R K) = pullback.snd 𝒜.f (specGenericFibreInclusion R K)
      rw [Category.assoc, Category.assoc, ed_snd, hφ, ← eE_snd, Iso.inv_hom_id_assoc]⟩
  have eE_inv_fst : eE.inv ≫ gE = pullback.fst 𝒜.f (specGenericFibreInclusion R K) := by
    rw [← eE_fst, Iso.inv_hom_id_assoc]
  have eE_inv_snd : eE.inv ≫ E.f = pullback.snd 𝒜.f (specGenericFibreInclusion R K) := by
    rw [← eE_snd, Iso.inv_hom_id_assoc]
  have ed_inv_fst : ed.inv ≫ gd = pullback.fst 𝒟.f (specGenericFibreInclusion R K) := by
    rw [← ed_fst, Iso.inv_hom_id_assoc]
  have hφK : ∀ {S : Scheme.{0}} (s : S ⟶ Spec (CommRingCat.of K))
      (x y : SchemeHomOver s (RelativeGroupLaw.genericFibreStr K 𝒜.f)),
      NeronModelInfra.schemeHomOverComp ((𝒜.L.genericFibre K).mul s x y) φK =
        (𝒟.L.genericFibre K).mul s (NeronModelInfra.schemeHomOverComp x φK)
          (NeronModelInfra.schemeHomOverComp y φK) := by
    intro S s x y
    have hsι : s ≫ Spec.map (CommRingCat.ofHom (algebraMap R K)) = s ≫ specGenericFibreInclusion R K := rfl

    let toE : SchemeHomOver s (RelativeGroupLaw.genericFibreStr K 𝒜.f) → SchemeHomOver s E.f := fun z =>
      ⟨z.1 ≫ eE.inv, by rw [Category.assoc, eE_inv_snd]; exact z.2⟩

    have htoBase : ∀ z : SchemeHomOver s (RelativeGroupLaw.genericFibreStr K 𝒜.f),
        RelativeGroupLaw.baseChangePointToBase (specGenericFibreInclusion R K) z =
          ⟨(toE z).1 ≫ gE, by rw [Category.assoc, hgE.w, ← Category.assoc, (toE z).2]; rfl⟩ := by
      intro z; apply Subtype.ext
      simp only [RelativeGroupLaw.baseChangePointToBase_coe, toE, Category.assoc, eE_inv_fst]

    have htoBase' : ∀ z : SchemeHomOver s (RelativeGroupLaw.genericFibreStr K 𝒜.f),
        RelativeGroupLaw.baseChangePointToBase (specGenericFibreInclusion R K) (NeronModelInfra.schemeHomOverComp z φK) =
          ⟨(mapPt φ hφ (toE z)).1 ≫ gd, by rw [Category.assoc, hgd.w, ← Category.assoc, (mapPt φ hφ (toE z)).2]; rfl⟩ := by
      intro z; apply Subtype.ext
      show (z.1 ≫ (eE.inv ≫ φ ≫ ed.hom)) ≫ pullback.fst 𝒟.f (specGenericFibreInclusion R K) = ((z.1 ≫ eE.inv) ≫ φ) ≫ gd
      simp only [Category.assoc, ed_fst]

    have hlift : ∀ (m : SchemeHomOver s E.f) (h),
        pullback.lift (m.1 ≫ gE) s h ≫ eE.inv = m.1 := by
      intro m h
      rw [← cancel_mono eE.hom, Category.assoc, Iso.inv_hom_id, Category.comp_id]
      apply pullback.hom_ext
      · rw [pullback.lift_fst, Category.assoc, eE_fst]
      · rw [pullback.lift_snd, Category.assoc, eE_snd, m.2]

    have hY : (𝒜.L.mul (s ≫ specGenericFibreInclusion R K)
        (RelativeGroupLaw.baseChangePointToBase (specGenericFibreInclusion R K) x)
        (RelativeGroupLaw.baseChangePointToBase (specGenericFibreInclusion R K) y)).1 = (E.L.mul s (toE x) (toE y)).1 ≫ gE := by
      rw [htoBase x, htoBase y]
      exact (hgE_mul s (toE x) (toE y)).symm
    have hZ : (𝒟.L.mul (s ≫ specGenericFibreInclusion R K)
        (RelativeGroupLaw.baseChangePointToBase (specGenericFibreInclusion R K) (NeronModelInfra.schemeHomOverComp x φK))
        (RelativeGroupLaw.baseChangePointToBase (specGenericFibreInclusion R K) (NeronModelInfra.schemeHomOverComp y φK))).1
          = (E.L.mul s (toE x) (toE y)).1 ≫ φ ≫ gd := by
      rw [htoBase' x, htoBase' y]
      have h1 := (hgd_mul s (mapPt φ hφ (toE x)) (mapPt φ hφ (toE y))).symm
      rw [← hφ_mul] at h1
      exact h1
    have hlift2 : pullback.lift (𝒜.L.mul (s ≫ specGenericFibreInclusion R K)
        (RelativeGroupLaw.baseChangePointToBase (specGenericFibreInclusion R K) x)
        (RelativeGroupLaw.baseChangePointToBase (specGenericFibreInclusion R K) y)).1 s
          (𝒜.L.mul (s ≫ specGenericFibreInclusion R K) _ _).2 ≫ eE.inv = (E.L.mul s (toE x) (toE y)).1 := by
      rw [← cancel_mono eE.hom, Category.assoc, Iso.inv_hom_id, Category.comp_id]
      apply pullback.hom_ext
      · rw [pullback.lift_fst, Category.assoc, eE_fst]; exact hY
      · rw [pullback.lift_snd, Category.assoc, eE_snd]; exact ((E.L.mul s (toE x) (toE y)).2).symm
    apply Subtype.ext
    rw [NeronModelInfra.schemeHomOverComp_coe, RelativeGroupLaw.baseChange_mul, RelativeGroupLaw.baseChange_mul,
      RelativeGroupLaw.baseChangePointOfBase_coe, RelativeGroupLaw.baseChangePointOfBase_coe]
    apply pullback.hom_ext
    · rw [pullback.lift_fst, hZ]
      show (pullback.lift _ s _ ≫ (eE.inv ≫ φ ≫ ed.hom)) ≫ pullback.fst 𝒟.f (specGenericFibreInclusion R K) = _
      simp only [Category.assoc]
      rw [ed_fst, ← Category.assoc, hlift2]
    · rw [pullback.lift_snd, Category.assoc]
      show pullback.lift _ _ _ ≫ φK.1 ≫ RelativeGroupLaw.genericFibreStr K 𝒟.f = s
      rw [φK.2, pullback.lift_snd]
  haveI : Smooth 𝒜.f := 𝒜.bundle.smooth
  obtain ⟨Φ', ⟨hΦ'K, hΦ'mul⟩, huniq⟩ :=
    GoodReductionJacobian.AbelianSchemePropertyBundle.existsUnique_extension_hom_of_genericFibre R K 𝒟.bundle 𝒟.L 𝒜.L φK hφK
  refine ⟨Φ'.1, Φ'.2, ?_⟩

  have h := congrArg Subtype.val hΦ'K
  simp only [genericFibreRestrict] at h

  have h2 := congrArg (fun k => eE.hom ≫ k ≫ pullback.fst 𝒟.f (specGenericFibreInclusion R K)) h
  rw [pullback.lift_fst, ← Category.assoc, eE_fst] at h2
  rw [h2]
  show eE.hom ≫ (eE.inv ≫ φ ≫ ed.hom) ≫ pullback.fst 𝒟.f (specGenericFibreInclusion R K) = φ ≫ gd
  rw [Category.assoc, Category.assoc, Iso.hom_inv_id_assoc, ed_fst]

theorem solution
    {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} {N : ℕ}
    {R : Type} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    {K : Type} [Field K] [Algebra R K] [IsFractionRing R K]
    (𝒜 𝒟 : FakeEllipticCurve Λ N R) (E d : FakeEllipticCurve Λ N K)
    (gE : E.A ⟶ 𝒜.A) (hgE : CategoryTheory.IsPullback gE E.f 𝒜.f (Spec.map (CommRingCat.ofHom (algebraMap R K))))
    (hgE_mul : ∀ {T : Scheme.{0}} (t' : T ⟶ Spec (CommRingCat.of K)) (P Q : SchemeHomOver t' E.f),
      (E.L.mul t' P Q).1 ≫ gE =
        (𝒜.L.mul (t' ≫ Spec.map (CommRingCat.ofHom (algebraMap R K)))
          ⟨P.1 ≫ gE, by rw [Category.assoc, hgE.w, ← Category.assoc, P.2]⟩
          ⟨Q.1 ≫ gE, by rw [Category.assoc, hgE.w, ← Category.assoc, Q.2]⟩).1)
    (hgE_act : ∀ x : ↥Λ, E.act x ≫ gE = gE ≫ 𝒜.act x)
    (gd : d.A ⟶ 𝒟.A) (hgd : CategoryTheory.IsPullback gd d.f 𝒟.f (Spec.map (CommRingCat.ofHom (algebraMap R K))))
    (hgd_mul : ∀ {T : Scheme.{0}} (t' : T ⟶ Spec (CommRingCat.of K)) (P Q : SchemeHomOver t' d.f),
      (d.L.mul t' P Q).1 ≫ gd =
        (𝒟.L.mul (t' ≫ Spec.map (CommRingCat.ofHom (algebraMap R K)))
          ⟨P.1 ≫ gd, by rw [Category.assoc, hgd.w, ← Category.assoc, P.2]⟩
          ⟨Q.1 ≫ gd, by rw [Category.assoc, hgd.w, ← Category.assoc, Q.2]⟩).1)
    (hgd_act : ∀ x : ↥Λ, d.act x ≫ gd = gd ≫ 𝒟.act x)
    (φ : E.A ⟶ d.A) (hφ : φ ≫ d.f = E.f)
    (hφ_mul : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of K)) (P Q : SchemeHomOver t E.f),
      mapPt φ hφ (E.L.mul t P Q) = d.L.mul t (mapPt φ hφ P) (mapPt φ hφ Q))
    (hφ_act : ∀ x : ↥Λ, E.act x ≫ φ = φ ≫ d.act x) :
    ∃ (Φ : 𝒜.A ⟶ 𝒟.A) (hΦ : Φ ≫ 𝒟.f = 𝒜.f),
      gE ≫ Φ = φ ≫ gd ∧
      (∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of R)) (P Q : SchemeHomOver t 𝒜.f),
        mapPt Φ hΦ (𝒜.L.mul t P Q) = 𝒟.L.mul t (mapPt Φ hΦ P) (mapPt Φ hΦ Q)) ∧
      (∀ x : ↥Λ, 𝒜.act x ≫ Φ = Φ ≫ 𝒟.act x) := by
  obtain ⟨Φ, hΦ, hext⟩ := slot_ext 𝒜 𝒟 E d gE hgE hgE_mul hgE_act gd hgd hgd_mul hgd_act φ hφ hφ_mul hφ_act
  have hd := density 𝒜 𝒟 E d gE hgE hgE_mul hgE_act gd hgd hgd_mul hgd_act φ hφ hφ_mul hφ_act Φ hΦ hext
  exact ⟨Φ, hΦ, hext, hd.1, hd.2⟩

end S_CerednikDrinfeld_QM_FakeEllipticCurve_exists_hom_extension_of_isPullback_of_isDiscreteValuationRing
end P2MW
export P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_exists_hom_extension_of_isPullback_of_isDiscreteValuationRing (solution)
