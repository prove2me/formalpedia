-- Prove2me | solution 1 for CerednikDrinfeld.QM.FakeEllipticCurve.mapPt_mul_and_act_comp_of_comp_eq_of_isPullback_valuationSubring
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.141142+00:00
-- url     : https://prove2.me/submissions/3ba89d0b-9b2d-5de8-8e2d-cccf02aa8b8d

import Definitions.Def_CerednikDrinfeld_FakeEllipticFrobenius
import Theorems.Thm_AlgebraicGeometry_eq_of_forall_specMap_comp_eq_of_smooth_of_isSeparated
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_mapPt_mul_and_act_comp_of_comp_eq_of_isPullback_valuationSubring

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra CerednikDrinfeld CerednikDrinfeld.QM CerednikDrinfeld.QM.FakeEllipticCurve
open scoped Quaternion

namespace A5Aux

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

end A5Aux

theorem solution
    {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} {N : ℕ}
    (O : ValuationSubring (AlgebraicClosure ℚ))
    (𝒜 𝒟 : FakeEllipticCurve Λ N ↥O) (E d : FakeEllipticCurve Λ N (AlgebraicClosure ℚ))
    (gE : E.A ⟶ 𝒜.A) (hgE : CategoryTheory.IsPullback gE E.f 𝒜.f (Spec.map (CommRingCat.ofHom O.subtype)))
    (hgE_mul : ∀ {T : Scheme.{0}} (t' : T ⟶ Spec (CommRingCat.of (AlgebraicClosure ℚ))) (P Q : SchemeHomOver t' E.f),
      (E.L.mul t' P Q).1 ≫ gE =
        (𝒜.L.mul (t' ≫ Spec.map (CommRingCat.ofHom O.subtype))
          ⟨P.1 ≫ gE, by rw [Category.assoc, hgE.w, ← Category.assoc, P.2]⟩
          ⟨Q.1 ≫ gE, by rw [Category.assoc, hgE.w, ← Category.assoc, Q.2]⟩).1)
    (hgE_act : ∀ x : ↥Λ, E.act x ≫ gE = gE ≫ 𝒜.act x)
    (gd : d.A ⟶ 𝒟.A) (hgd : CategoryTheory.IsPullback gd d.f 𝒟.f (Spec.map (CommRingCat.ofHom O.subtype)))
    (hgd_mul : ∀ {T : Scheme.{0}} (t' : T ⟶ Spec (CommRingCat.of (AlgebraicClosure ℚ))) (P Q : SchemeHomOver t' d.f),
      (d.L.mul t' P Q).1 ≫ gd =
        (𝒟.L.mul (t' ≫ Spec.map (CommRingCat.ofHom O.subtype))
          ⟨P.1 ≫ gd, by rw [Category.assoc, hgd.w, ← Category.assoc, P.2]⟩
          ⟨Q.1 ≫ gd, by rw [Category.assoc, hgd.w, ← Category.assoc, Q.2]⟩).1)
    (hgd_act : ∀ x : ↥Λ, d.act x ≫ gd = gd ≫ 𝒟.act x)
    (φ : E.A ⟶ d.A) (hφ : φ ≫ d.f = E.f)
    (hφ_mul : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of (AlgebraicClosure ℚ))) (P Q : SchemeHomOver t E.f),
      mapPt φ hφ (E.L.mul t P Q) = d.L.mul t (mapPt φ hφ P) (mapPt φ hφ Q))
    (hφ_act : ∀ x : ↥Λ, E.act x ≫ φ = φ ≫ d.act x)
    (Φ : 𝒜.A ⟶ 𝒟.A) (hΦ : Φ ≫ 𝒟.f = 𝒜.f) (hext : gE ≫ Φ = φ ≫ gd) :
    (∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of ↥O)) (P Q : SchemeHomOver t 𝒜.f),
        mapPt Φ hΦ (𝒜.L.mul t P Q) = 𝒟.L.mul t (mapPt Φ hΦ P) (mapPt Φ hΦ Q)) ∧
      (∀ x : ↥Λ, 𝒜.act x ≫ Φ = Φ ≫ 𝒟.act x) := by
  haveI : Smooth 𝒜.f := 𝒜.bundle.smooth
  haveI : IsProper 𝒟.f := 𝒟.bundle.proper
  have halg : Spec.map (CommRingCat.ofHom (algebraMap ↥O (AlgebraicClosure ℚ))) = Spec.map (CommRingCat.ofHom O.subtype) := rfl

  have key_pt : ∀ x : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ 𝒜.A,
      x ≫ 𝒜.f = Spec.map (CommRingCat.ofHom (algebraMap ↥O (AlgebraicClosure ℚ))) →
      ∃ x' : SchemeHomOver (𝟙 (Spec (CommRingCat.of (AlgebraicClosure ℚ)))) E.f, x'.1 ≫ gE = x := by
    intro x hx
    refine ⟨⟨hgE.lift x (𝟙 _) (by rw [hx, halg, Category.id_comp]), hgE.lift_snd _ _ _⟩, hgE.lift_fst _ _ _⟩

  have mulA_congr : ∀ {T : Scheme.{0}} {t₁ t₂ : T ⟶ Spec (CommRingCat.of ↥O)} (h : t₁ = t₂)
      (P₁ Q₁ : SchemeHomOver t₁ 𝒜.f) (P₂ Q₂ : SchemeHomOver t₂ 𝒜.f), P₁.1 = P₂.1 → Q₁.1 = Q₂.1 →
      (𝒜.L.mul t₁ P₁ Q₁).1 = (𝒜.L.mul t₂ P₂ Q₂).1 := by
    rintro T t₁ t₂ rfl P₁ Q₁ P₂ Q₂ hP hQ
    obtain rfl : P₁ = P₂ := Subtype.ext hP; obtain rfl : Q₁ = Q₂ := Subtype.ext hQ; rfl
  have mulD_congr : ∀ {T : Scheme.{0}} {t₁ t₂ : T ⟶ Spec (CommRingCat.of ↥O)} (h : t₁ = t₂)
      (P₁ Q₁ : SchemeHomOver t₁ 𝒟.f) (P₂ Q₂ : SchemeHomOver t₂ 𝒟.f), P₁.1 = P₂.1 → Q₁.1 = Q₂.1 →
      (𝒟.L.mul t₁ P₁ Q₁).1 = (𝒟.L.mul t₂ P₂ Q₂).1 := by
    rintro T t₁ t₂ rfl P₁ Q₁ P₂ Q₂ hP hQ
    obtain rfl : P₁ = P₂ := Subtype.ext hP; obtain rfl : Q₁ = Q₂ := Subtype.ext hQ; rfl

  let ΦΦ : pullback 𝒜.f 𝒜.f ⟶ pullback 𝒟.f 𝒟.f :=
    pullback.map 𝒜.f 𝒜.f 𝒟.f 𝒟.f Φ Φ (𝟙 _) (by rw [hΦ, Category.comp_id]) (by rw [hΦ, Category.comp_id])
  have hΦΦ_fst : ΦΦ ≫ pullback.fst 𝒟.f 𝒟.f = pullback.fst 𝒜.f 𝒜.f ≫ Φ := pullback.lift_fst _ _ _
  have hΦΦ_snd : ΦΦ ≫ pullback.snd 𝒟.f 𝒟.f = pullback.snd 𝒜.f 𝒜.f ≫ Φ := pullback.lift_snd _ _ _

  have hm : A5Aux.mulMor 𝒜.L ≫ Φ = ΦΦ ≫ A5Aux.mulMor 𝒟.L := by
    apply AlgebraicGeometry.eq_of_forall_specMap_comp_eq_of_smooth_of_isSeparated (R := ↥O) (AlgebraicClosure ℚ)
      (AlgebraicClosure ℚ) (pullback.fst 𝒜.f 𝒜.f ≫ 𝒜.f) 𝒟.f
    · rw [Category.assoc, hΦ, A5Aux.mulMor_over]
    · rw [Category.assoc, A5Aux.mulMor_over, ← Category.assoc, hΦΦ_fst, Category.assoc, hΦ]
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
      have hbase : x ≫ pullback.fst 𝒜.f 𝒜.f ≫ 𝒜.f = 𝟙 _ ≫ Spec.map (CommRingCat.ofHom O.subtype) := by
        rw [hx, halg, Category.id_comp]

      have hL : x ≫ A5Aux.mulMor 𝒜.L ≫ Φ = ((E.L.mul (𝟙 _) P' Q').1 ≫ φ) ≫ gd := by
        rw [← Category.assoc, hxlift, ← A5Aux.mul_val_eq_lift_mulMor 𝒜.L _ Px Qx,
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
      have hR : x ≫ ΦΦ ≫ A5Aux.mulMor 𝒟.L = ((d.L.mul (𝟙 _) (mapPt φ hφ P') (mapPt φ hφ Q')).1) ≫ gd := by
        rw [← Category.assoc, hxlift', ← A5Aux.mul_val_eq_lift_mulMor 𝒟.L _ Px' Qx', hgd_mul]
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
    rw [A5Aux.mul_val_eq_lift_mulMor 𝒜.L, A5Aux.mul_val_eq_lift_mulMor 𝒟.L, Category.assoc, hm, ← Category.assoc]
    congr 1
    apply pullback.hom_ext
    · rw [pullback.lift_fst, Category.assoc, hΦΦ_fst, ← Category.assoc, pullback.lift_fst]; rfl
    · rw [pullback.lift_snd, Category.assoc, hΦΦ_snd, ← Category.assoc, pullback.lift_snd]; rfl
  · intro x₀
    apply AlgebraicGeometry.eq_of_forall_specMap_comp_eq_of_smooth_of_isSeparated (R := ↥O) (AlgebraicClosure ℚ)
      (AlgebraicClosure ℚ) 𝒜.f 𝒟.f
    · rw [Category.assoc, hΦ, 𝒜.act_over]
    · rw [Category.assoc, 𝒟.act_over, hΦ]
    · intro x hx
      obtain ⟨P', hP'⟩ := key_pt x hx
      rw [← hP', Category.assoc, Category.assoc, ← Category.assoc gE, ← hgE_act, Category.assoc, hext,
        ← Category.assoc (E.act x₀), hφ_act, Category.assoc, hgd_act, ← Category.assoc gE, hext]
      simp only [Category.assoc]

end S_CerednikDrinfeld_QM_FakeEllipticCurve_mapPt_mul_and_act_comp_of_comp_eq_of_isPullback_valuationSubring
end P2MW
export P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_mapPt_mul_and_act_comp_of_comp_eq_of_isPullback_valuationSubring (solution)
