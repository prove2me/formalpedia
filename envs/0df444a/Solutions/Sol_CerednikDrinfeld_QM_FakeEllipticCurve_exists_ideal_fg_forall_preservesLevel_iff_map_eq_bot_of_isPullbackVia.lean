-- Prove2me | solution 1 for CerednikDrinfeld.QM.FakeEllipticCurve.exists_ideal_fg_forall_preservesLevel_iff_map_eq_bot_of_isPullbackVia
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.141142+00:00
-- url     : https://prove2.me/submissions/5ef31006-1bc7-5e21-8d72-152a180e85a2

import Definitions.Def_CerednikDrinfeld_QMIsogeny
import Definitions.Def_CerednikDrinfeld_QMRigidification

import Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_factorsThrough_lev_of_exists_comp_eq_of_isPullback
import Theorems.Thm_AlgebraicGeometry_exists_ideal_fg_forall_exists_comp_eq_pullback_fst_iff_map_eq_bot_of_isFinite_of_flat
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_exists_ideal_fg_forall_preservesLevel_iff_map_eq_bot_of_isPullbackVia

set_option autoImplicit false

open scoped TensorProduct Quaternion NumberField
open CategoryTheory AlgebraicGeometry QuaternionAlgebra CerednikDrinfeld CerednikDrinfeld.QM NeronModelInfra GoodReductionJacobian

namespace P3A

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

theorem lfp_of_comp_aux : ∀ {X Y Z : Scheme.{0}} (f : X ⟶ Y) (g : Y ⟶ Z),
    LocallyOfFinitePresentation (f ≫ g) → LocallyOfFiniteType g → LocallyOfFinitePresentation f := by
  intro X Y Z f g h hg
  wlog hZ : IsAffine Z generalizing X Y Z
  · rw [IsZariskiLocalAtTarget.iff_of_iSup_eq_top (P := @LocallyOfFinitePresentation) _
      (g.iSup_preimage_eq_top (iSup_affineOpens_eq_top Z))]
    intro U
    have H := IsZariskiLocalAtTarget.restrict h U.1
    rw [morphismRestrict_comp] at H
    exact this _ _ H (IsZariskiLocalAtTarget.restrict hg U.1) inferInstance
  wlog hY : IsAffine Y generalizing X Y
  · rw [IsZariskiLocalAtTarget.iff_of_iSup_eq_top (P := @LocallyOfFinitePresentation) _ (iSup_affineOpens_eq_top Y)]
    intro U
    have H := HasRingHomProperty.comp_of_isOpenImmersion @LocallyOfFinitePresentation (f ⁻¹ᵁ U.1).ι (f ≫ g) h
    rw [← morphismRestrict_ι_assoc] at H
    exact this _ _ H inferInstance inferInstance
  wlog hX : IsAffine X generalizing X
  · rw [IsZariskiLocalAtSource.iff_of_iSup_eq_top (P := @LocallyOfFinitePresentation) _ (iSup_affineOpens_eq_top X)]
    intro U
    have H := HasRingHomProperty.comp_of_isOpenImmersion @LocallyOfFinitePresentation U.1.ι (f ≫ g) h
    rw [← Category.assoc] at H
    exact this _ H inferInstance
  rw [HasRingHomProperty.iff_of_isAffine (P := @LocallyOfFinitePresentation)] at h ⊢
  rw [HasRingHomProperty.iff_of_isAffine (P := @LocallyOfFiniteType)] at hg
  rw [Scheme.Hom.comp_appTop, CommRingCat.hom_comp] at h
  exact RingHom.FinitePresentation.of_comp_finiteType _ h hg

theorem lfp_of_comp {X Y Z : Scheme.{0}} (f : X ⟶ Y) (g : Y ⟶ Z)
    [LocallyOfFinitePresentation (f ≫ g)] [LocallyOfFiniteType g] : LocallyOfFinitePresentation f :=
  lfp_of_comp_aux f g ‹_› ‹_›

end P3A

open CategoryTheory.Limits in
theorem solution
    {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} {N : ℕ}
    (S : Type) [CommRing S] (E A : FakeEllipticCurve Λ N S)
    (φ : E.A ⟶ A.A) (hφ : φ ≫ A.f = E.f) :
    ∃ J : Ideal S, J.FG ∧
      ∀ (T : Type) [CommRing T] (ψ : S →+* T)
        (E' A' : FakeEllipticCurve Λ N T) (gE : E'.A ⟶ E.A) (_ : FakeEllipticCurve.IsPullbackVia ψ E E' gE)
        (gA : A'.A ⟶ A.A) (_ : FakeEllipticCurve.IsPullbackVia ψ A A' gA)
        (φ' : E'.A ⟶ A'.A) (hφ' : φ' ≫ A'.f = E'.f),
        φ' ≫ gA = gE ≫ φ →
          (FakeEllipticCurve.PreservesLevel E' A' φ' hφ' ↔ J.map ψ = ⊥) := by
  classical

  haveI : IsFinite (E.lev ≫ E.f) := E.lev_finite
  haveI : Flat (E.lev ≫ E.f) := E.lev_flat
  haveI : LocallyOfFinitePresentation (E.lev ≫ E.f) := E.lev_finitePresentation
  haveI : IsClosedImmersion A.lev := A.lev_closed
  haveI : LocallyOfFinitePresentation (A.lev ≫ A.f) := A.lev_finitePresentation
  haveI : Smooth A.f := A.bundle.smooth
  haveI : LocallyOfFiniteType A.f := inferInstance
  haveI : LocallyOfFinitePresentation A.lev := P3A.lfp_of_comp A.lev A.f

  set h : E.C ⟶ A.A := E.lev ≫ φ with hh
  obtain ⟨J, hJfg, hJ⟩ :=
    AlgebraicGeometry.exists_ideal_fg_forall_exists_comp_eq_pullback_fst_iff_map_eq_bot_of_isFinite_of_flat
      S E.C (pullback h A.lev) (E.lev ≫ E.f) (pullback.fst h A.lev)
  refine ⟨J, hJfg, ?_⟩
  intro T _ ψ E' A' gE hgE gA hgA φ' hφ' hcomm
  rw [← hJ T ψ]
  obtain ⟨sqE, hmulE, hactE, hlevE⟩ := hgE
  obtain ⟨sqA, hmulA, hactA, hlevA⟩ := hgA

  set p₁ := pullback.fst (E.lev ≫ E.f) (Spec.map (CommRingCat.ofHom ψ)) with hp₁
  set p₂ := pullback.snd (E.lev ≫ E.f) (Spec.map (CommRingCat.ofHom ψ)) with hp₂
  constructor
  · intro hPL

    have hw : (p₁ ≫ E.lev) ≫ E.f = p₂ ≫ Spec.map (CommRingCat.ofHom ψ) := by
      rw [Category.assoc]; exact pullback.condition
    let R₁ : pullback (E.lev ≫ E.f) (Spec.map (CommRingCat.ofHom ψ)) ⟶ E'.A := sqE.lift (p₁ ≫ E.lev) p₂ hw
    have hR₁g : R₁ ≫ gE = p₁ ≫ E.lev := sqE.lift_fst _ _ hw
    have hR₁f : R₁ ≫ E'.f = p₂ := sqE.lift_snd _ _ hw
    have hR : FactorsThrough E'.lev (⟨R₁, hR₁f⟩ : SchemeHomOver p₂ E'.f) :=
      CerednikDrinfeld.QM.FakeEllipticCurve.factorsThrough_lev_of_exists_comp_eq_of_isPullback ψ E E' gE sqE hmulE hlevE
        p₂ ⟨R₁, hR₁f⟩ ⟨p₁, hR₁g.symm⟩
    obtain ⟨Q, hQ⟩ := hPL p₂ ⟨R₁, hR₁f⟩ hR

    obtain ⟨Q₁, hQ₁⟩ := hlevA (A'.lev ≫ A'.f) ⟨A'.lev, rfl⟩ ⟨𝟙 _, Category.id_comp _⟩
    have hm : p₁ ≫ h = (Q ≫ Q₁) ≫ A.lev := by
      simp only [Category.assoc, hQ₁]
      rw [← Category.assoc Q, hQ]
      simp only [mapPt_coe, Category.assoc, hcomm]
      rw [← Category.assoc R₁, hR₁g, Category.assoc, hh]
    exact ⟨pullback.lift p₁ (Q ≫ Q₁) hm, pullback.lift_fst _ _ _⟩
  · rintro ⟨ℓ, hℓ⟩
    intro T₀ t P hP
    obtain ⟨P₀, hP₀⟩ := hlevE t P hP
    apply CerednikDrinfeld.QM.FakeEllipticCurve.factorsThrough_lev_of_exists_comp_eq_of_isPullback ψ A A' gA sqA hmulA hlevA t
    have hu : P₀ ≫ (E.lev ≫ E.f) = t ≫ Spec.map (CommRingCat.ofHom ψ) := by
      rw [← Category.assoc, hP₀, Category.assoc, sqE.w, ← Category.assoc, P.2]
    refine ⟨pullback.lift P₀ t hu ≫ ℓ ≫ pullback.snd h A.lev, ?_⟩
    simp only [mapPt_coe, Category.assoc]
    rw [← pullback.condition, ← Category.assoc ℓ, hℓ, ← Category.assoc, pullback.lift_fst, hh, ← Category.assoc, hP₀,
      Category.assoc, hcomm]

end S_CerednikDrinfeld_QM_FakeEllipticCurve_exists_ideal_fg_forall_preservesLevel_iff_map_eq_bot_of_isPullbackVia
end P2MW
export P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_exists_ideal_fg_forall_preservesLevel_iff_map_eq_bot_of_isPullbackVia (solution)
