-- Prove2me | solution 1 for CerednikDrinfeld.QM.FakeEllipticCurve.WithFullLevel.iso_of_comp_hom_eq_of_isPullbackVia_fstHom
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.837917+00:00
-- url     : https://prove2.me/submissions/f0f767e0-e5bd-52a6-990e-ea323e9d5829

import Mathlib
import Definitions.Def_CerednikDrinfeld_QMFineModuli
import Definitions.Def_CerednikDrinfeld_QMFormalModuleOf
import Definitions.Def_GoodReductionJacobian_BareDeformation

import Theorems.Thm_GoodReductionJacobian_AbelianSchemePropertyBundle_geometricallyIntegral_of_commRing
import Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_eq_of_comp_eq_of_isPullback_of_isArtinianRing
import Theorems.Thm_AlgebraicGeometry_geometricallyIrreducible_iff_bijective_appTop_of_isProper_of_smooth
import Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_hom_eq_of_comp_eq_of_isPullback_fstHom
import Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_FullLevel_existsUnique_comp_eq_specMap_comp_of_isNilpotent_ker
import Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_etale_lev_and_forall_factorsThrough_iff_of_isUnit
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_WithFullLevel_iso_of_comp_hom_eq_of_isPullbackVia_fstHom
p2m_attr_erase "instance" "AdicCompletion.instIsLocalRingMaximalIdeal TwoChartCech.Sections.M0_moduleA TwoChartCech.Sections.M1_module TwoChartCech.Cover.A01_algebra TwoChartCech.Cover.A0_algebra TwoChartCech.Cover.A1_commRing TwoChartCech.Cover.A1_algebra TwoChartCech.Sections.M01_module TwoChartCech.Sections.M0_addCommGroup TwoChartCech.Sections.M0_tower TwoChartCech.Sections.M01_addCommGroup TwoChartCech.Cover.A0_commRing TwoChartCech.Sections.M1_tower TwoChartCech.Sections.M01_moduleA TwoChartCech.Sections.M0_module TwoChartCech.Sections.M1_moduleA TwoChartCech.Sections.M1_addCommGroup TwoChartCech.Cover.A01_commRing TwoChartCech.Sections.M01_tower CoherentBaseChange.TwoTermComplex.C0_module CoherentBaseChange.TwoTermComplex.C0_addCommGroup CoherentBaseChange.TwoTermComplex.C1_module CoherentBaseChange.TwoTermComplex.C1_addCommGroup CoherentBaseChange.TwoTermComplex.C0_free CoherentBaseChange.TwoTermComplex.C1_finite CoherentBaseChange.TwoTermComplex.C0_finite CoherentBaseChange.TwoTermComplex.C1_free"
p2m_attr_erase "simp" "GoodReductionJacobian.RelativeGroupLaw.baseChangePointToBase_ofBase GoodReductionJacobian.RelativeGroupLaw.baseChangePointToBase_coe GoodReductionJacobian.RelativeGroupLaw.baseChangePointOfBase_coe GoodReductionJacobian.RelativeGroupLaw.baseChange_inv GoodReductionJacobian.RelativeGroupLaw.baseChangePointOfBase_toBase GoodReductionJacobian.RelativeGroupLaw.baseChange_mul GoodReductionJacobian.RelativeGroupLaw.baseChange_one GoodReductionJacobian.RelativeGroupLaw.nsmul_zero GoodReductionJacobian.RelativeGroupLaw.mem_torsionSubset GoodReductionJacobian.RelativeGroupLaw.nsmul_succ NeronModelInfra.NeronModelPropertyBundle.endExtensionEquiv_symm_restrict NeronModelInfra.schemeHomOverComp_id_left NeronModelInfra.schemeHomOverComp_id_right NeronModelInfra.schemeHomOverId_coe NeronModelInfra.NeronModelPropertyBundle.endExtensionEquiv_apply NeronModelInfra.NeronModelPropertyBundle.restrict_endExtensionEquiv_symm NeronModelInfra.schemeHomOverComp_coe NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_fst NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_snd NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_fst NeronSpecialFibreInfra.neronEndRestrictEquiv_apply NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_fst_assoc NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_snd NeronSpecialFibreInfra.neronEndExtension_genericFibreRestrict NeronSpecialFibreInfra.specClosedFibreInclusion_eq NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_fst_assoc NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_snd_assoc NeronSpecialFibreInfra.genericFibreRestrict_neronEndExtension NeronSpecialFibreInfra.homOverId_coe NeronSpecialFibreInfra.homOverComp_coe NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_snd_assoc GoodReductionJacobian.RelativeGroupLaw.fibre_inv GoodReductionJacobian.RelativeGroupLaw.fibrePointToBase_coe GoodReductionJacobian.RelativeGroupLaw.fibrePointOfBase_toBase GoodReductionJacobian.RelativeGroupLaw.fibre_mul GoodReductionJacobian.RelativeGroupLaw.fibrePointToBase_ofBase GoodReductionJacobian.RelativeGroupLaw.fibre_one GoodReductionJacobian.RelativeGroupLaw.fibrePointOfBase_coe AlgebraicGeometry.schemeFibreEndo_snd AlgebraicGeometry.schemeFibreEndo_fst"
p2m_attr_erase "simp" "RegularLocalRingQuotientAscent.dualNumberFst_apply AlgebraicGeometry.Scheme.TwoAffineOpenCover.mk.injEq AlgebraicGeometry.Scheme.TwoAffineOpenCover.mk.sizeOf_spec AlgebraicGeometry.Scheme.TwoAffineOpenCover.pullback_U1 AlgebraicGeometry.Scheme.TwoAffineOpenCover.pullback_U0 TwoChartCech.Sections.mk.injEq TwoChartCech.Cover.mk.injEq TwoChartCech.GrothendieckComplex.mk.injEq TwoChartCech.Sections.mk.sizeOf_spec TwoChartCech.Cover.mk.sizeOf_spec TwoChartCech.Cover.lineBundle_r0_apply TwoChartCech.GrothendieckComplex.mk.sizeOf_spec TwoChartCech.Cover.lineBundle_r1_apply CoherentBaseChange.TwoTermComplex.mk.sizeOf_spec CoherentBaseChange.TwoTermComplex.mk.injEq"

set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option synthInstance.maxHeartbeats 320000
set_option linter.unusedVariables false

open scoped TensorProduct Quaternion
p2m_open "CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra~schemeHomOverComp~schemeHomOverComp_coe GoodReductionJacobian P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_WithFullLevel_iso_of_comp_hom_eq_of_isPullbackVia_fstHom.GoodReductionJacobian QuaternionAlgebra CerednikDrinfeld CerednikDrinfeld.QM"

universe v u

noncomputable section

namespace GoodReductionJacobian
p2m_export "GoodReductionJacobian" "AbelianSchemePropertyBundle schemeHomOverComp schemeHomOverComp_coe RelativeGroupLaw AbelianSchemePropertyBundle.geometricallyIntegral_of_commRing RelativeGroupLaw.eq_of_comp_eq_of_isPullback_of_isArtinianRing"
namespace P2mIsoUp
p2m_open "GoodReductionJacobian"

section PointCalc

variable {R : Type u} [CommRing R] {A : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of R)} (L : RelativeGroupLaw R f)

theorem val_mul_natural {T T' : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of R)} {t' : T' ⟶ Spec (CommRingCat.of R)}
    (ψ : T' ⟶ T) (hψ : ψ ≫ t = t') (P Q : SchemeHomOver t f) :
    ψ ≫ (L.mul t P Q).1 = (L.mul t' ⟨ψ ≫ P.1, by rw [Category.assoc, P.2, hψ]⟩ ⟨ψ ≫ Q.1, by rw [Category.assoc, Q.2, hψ]⟩).1 :=
  congrArg Subtype.val (L.mul_natural t t' ψ hψ P Q)

theorem val_one_natural {T T' : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of R)} {t' : T' ⟶ Spec (CommRingCat.of R)}
    (ψ : T' ⟶ T) (hψ : ψ ≫ t = t') :
    ψ ≫ (L.one t).1 = (L.one t').1 :=
  congrArg Subtype.val (L.one_natural t t' ψ hψ)

theorem inv_natural {T T' : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (t' : T' ⟶ Spec (CommRingCat.of R))
    (ψ : T' ⟶ T) (hψ : ψ ≫ t = t') (P : SchemeHomOver t f) :
    schemeHomOverComp ψ hψ (L.inv t P) = L.inv t' (schemeHomOverComp ψ hψ P) := by
  letI := L.pointGroup t'
  have h : L.mul t' (schemeHomOverComp ψ hψ (L.inv t P)) (schemeHomOverComp ψ hψ P) = L.one t' := by
    rw [← L.mul_natural, L.inv_mul_cancel, L.one_natural]
  exact eq_inv_of_mul_eq_one_left h

theorem val_inv_natural {T T' : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of R)} {t' : T' ⟶ Spec (CommRingCat.of R)}
    (ψ : T' ⟶ T) (hψ : ψ ≫ t = t') (P : SchemeHomOver t f) :
    ψ ≫ (L.inv t P).1 = (L.inv t' ⟨ψ ≫ P.1, by rw [Category.assoc, P.2, hψ]⟩).1 :=
  congrArg Subtype.val (inv_natural L t t' ψ hψ P)

theorem eq_one_of_mul_self {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (P : SchemeHomOver t f)
    (h : L.mul t P P = P) : P = L.one t := by
  letI := L.pointGroup t
  exact mul_eq_left.mp h

theorem inv_one_pt {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) : L.inv t (L.one t) = L.one t := by
  letI := L.pointGroup t
  exact _root_.inv_one

theorem val_mul_congr {T : Scheme.{u}} {t t' : T ⟶ Spec (CommRingCat.of R)} (h : t = t') (P Q : SchemeHomOver t f) :
    (L.mul t P Q).1 = (L.mul t' ⟨P.1, P.2.trans h⟩ ⟨Q.1, Q.2.trans h⟩).1 := by
  subst h; rfl

theorem val_one_congr {T : Scheme.{u}} {t t' : T ⟶ Spec (CommRingCat.of R)} (h : t = t') :
    (L.one t).1 = (L.one t').1 := by
  subst h; rfl

theorem val_mul_congr' {T : Scheme.{u}} {t t' : T ⟶ Spec (CommRingCat.of R)} (h : t = t')
    {P Q : SchemeHomOver t f} {P' Q' : SchemeHomOver t' f} (hP : P.1 = P'.1) (hQ : Q.1 = Q'.1) :
    (L.mul t P Q).1 = (L.mul t' P' Q').1 := by
  subst h
  rw [Subtype.ext hP, Subtype.ext hQ]

theorem pt_ext {T : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of R)} {P Q : SchemeHomOver t f} (h : P.1 = Q.1) : P = Q :=
  Subtype.ext h

theorem val_mul_congr_pts {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) {P P' Q Q' : SchemeHomOver t f}
    (hP : P.1 = P'.1) (hQ : Q.1 = Q'.1) : (L.mul t P Q).1 = (L.mul t P' Q').1 := by
  rw [pt_ext hP, pt_ext hQ]

theorem val_mul_eq_lift_comp {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (P Q P' Q' : SchemeHomOver t f)
    (X Y : SchemeHomOver (pullback.fst f f ≫ f) f)
    (hX : P'.1 = pullback.lift P.1 Q.1 (P.2.trans Q.2.symm) ≫ X.1)
    (hY : Q'.1 = pullback.lift P.1 Q.1 (P.2.trans Q.2.symm) ≫ Y.1) :
    (L.mul t P' Q').1 = pullback.lift P.1 Q.1 (P.2.trans Q.2.symm) ≫ (L.mul (pullback.fst f f ≫ f) X Y).1 := by
  have hpair : pullback.lift P.1 Q.1 (P.2.trans Q.2.symm) ≫ (pullback.fst f f ≫ f) = t := by
    rw [← Category.assoc, pullback.lift_fst, P.2]
  rw [val_mul_natural L _ hpair]
  exact val_mul_congr_pts L t hX hY

theorem val_mul_eq_one_of {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (a b : T ⟶ A)
    (ha : a ≫ f = t) (hb : b ≫ f = t) (ha1 : a = (L.one t).1) (hb1 : b = (L.one t).1) :
    (L.mul t ⟨a, ha⟩ ⟨b, hb⟩).1 = (L.one t).1 := by
  rw [pt_ext (P := (⟨a, ha⟩ : SchemeHomOver t f)) (Q := L.one t) ha1,
    pt_ext (P := (⟨b, hb⟩ : SchemeHomOver t f)) (Q := L.one t) hb1, L.mul_one]

end PointCalc

end GoodReductionJacobian.P2mIsoUp

open GoodReductionJacobian.P2mIsoUp

namespace P2mIsoUpInst
scoped instance instModuleFiniteDualNumber (k : Type) [Field k] : Module.Finite k (DualNumber k) :=
  inferInstanceAs (Module.Finite k (k × k))
scoped instance instIsArtinianRingDualNumber (k : Type) [Field k] : IsArtinianRing (DualNumber k) :=
  IsArtinianRing.of_finite k (DualNumber k)
end P2mIsoUpInst
p2m_reactivate "P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_WithFullLevel_iso_of_comp_hom_eq_of_isPullbackVia_fstHom.P2mIsoUpInst"

namespace GoodReductionJacobian
p2m_export "GoodReductionJacobian" "AbelianSchemePropertyBundle schemeHomOverComp schemeHomOverComp_coe RelativeGroupLaw AbelianSchemePropertyBundle.geometricallyIntegral_of_commRing RelativeGroupLaw.eq_of_comp_eq_of_isPullback_of_isArtinianRing"
namespace P2mIsoUp
p2m_open "GoodReductionJacobian"
section Transl
variable {R : Type u} [CommRing R] {A : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of R)} (L : RelativeGroupLaw R f)

private def _root_.GoodReductionJacobian.P2mIsoUp.trans (Q : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) f) : A ⟶ A :=
  (L.mul f ⟨𝟙 A, Category.id_comp f⟩ ⟨f ≫ Q.1, by rw [Category.assoc, Q.2, Category.comp_id]⟩).1

p2m_export "GoodReductionJacobian.P2mIsoUp" "trans"
theorem trans_over (Q : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) f) : trans L Q ≫ f = f :=
  (L.mul f _ _).2

theorem comp_trans {X : Scheme.{u}} (x : X ⟶ A) (Q : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) f) :
    x ≫ trans L Q = (L.mul (x ≫ f) ⟨x, rfl⟩ ⟨(x ≫ f) ≫ Q.1, by rw [Category.assoc, Q.2, Category.comp_id]⟩).1 := by
  unfold trans
  rw [val_mul_natural L x rfl]
  exact val_mul_congr_pts L _ (Category.comp_id x) (Category.assoc _ _ _).symm

theorem trans_comp (Q Q' : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) f) :
    trans L Q ≫ trans L Q' = trans L (L.mul (𝟙 _) Q Q') := by
  rw [comp_trans]
  have h2 : (⟨(trans L Q ≫ f) ≫ Q'.1, by rw [Category.assoc, Q'.2, Category.comp_id]⟩ : SchemeHomOver (trans L Q ≫ f) f).1
      = (schemeHomOverComp f (Category.comp_id f) Q').1 := by
    rw [schemeHomOverComp_coe, trans_over]
  rw [val_mul_congr' L (trans_over L Q) (P' := ⟨trans L Q, trans_over L Q⟩) rfl h2]
  have key : L.mul f (L.mul f ⟨𝟙 A, Category.id_comp f⟩ (schemeHomOverComp f (Category.comp_id f) Q))
        (schemeHomOverComp f (Category.comp_id f) Q')
      = L.mul f ⟨𝟙 A, Category.id_comp f⟩ (schemeHomOverComp f (Category.comp_id f) (L.mul (𝟙 _) Q Q')) := by
    rw [L.mul_assoc, ← L.mul_natural]
  have key' := congrArg Subtype.val key
  refine Eq.trans ?_ (key'.trans ?_)
  · apply val_mul_congr_pts L f _ rfl
    show trans L Q = _
    unfold trans
    exact val_mul_congr_pts L f rfl (by rw [schemeHomOverComp_coe])
  · unfold trans
    exact val_mul_congr_pts L f rfl (by rw [schemeHomOverComp_coe])

theorem trans_one : trans L (L.one (𝟙 _)) = 𝟙 A := by
  unfold trans
  have h : (⟨f ≫ (L.one (𝟙 _)).1, by rw [Category.assoc, (L.one (𝟙 _)).2, Category.comp_id]⟩ : SchemeHomOver f f) = L.one f := by
    apply pt_ext
    exact val_one_natural L f (Category.comp_id f)
  rw [h, L.mul_one]

def transIso (Q : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) f) : A ≅ A where
  hom := trans L Q
  inv := trans L (L.inv (𝟙 _) Q)
  hom_inv_id := by rw [trans_comp, L.mul_inv_cancel, trans_one]
  inv_hom_id := by rw [trans_comp, L.inv_mul_cancel, trans_one]

end Transl
p2m_reactivate "P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_WithFullLevel_iso_of_comp_hom_eq_of_isPullbackVia_fstHom.P2mIsoUpInst"
end GoodReductionJacobian.P2mIsoUp
p2m_reactivate "P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_WithFullLevel_iso_of_comp_hom_eq_of_isPullbackVia_fstHom.P2mIsoUpInst"
p2m_reactivate "P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_WithFullLevel_iso_of_comp_hom_eq_of_isPullbackVia_fstHom.P2mIsoUpInst"

namespace GoodReductionJacobian
p2m_export "GoodReductionJacobian" "AbelianSchemePropertyBundle schemeHomOverComp schemeHomOverComp_coe RelativeGroupLaw AbelianSchemePropertyBundle.geometricallyIntegral_of_commRing RelativeGroupLaw.eq_of_comp_eq_of_isPullback_of_isArtinianRing"
namespace P2mIsoUp
p2m_open "GoodReductionJacobian"

theorem val_mul_eq_lift_comp' {R : Type u} [CommRing R] {A A' : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of R)}
    {f' : A' ⟶ Spec (CommRingCat.of R)} (L' : RelativeGroupLaw R f')
    {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (P Q : SchemeHomOver t f) (P' Q' : SchemeHomOver t f')
    (X Y : SchemeHomOver (pullback.fst f f ≫ f) f')
    (hX : P'.1 = pullback.lift P.1 Q.1 (P.2.trans Q.2.symm) ≫ X.1)
    (hY : Q'.1 = pullback.lift P.1 Q.1 (P.2.trans Q.2.symm) ≫ Y.1) :
    (L'.mul t P' Q').1 = pullback.lift P.1 Q.1 (P.2.trans Q.2.symm) ≫ (L'.mul (pullback.fst f f ≫ f) X Y).1 := by
  have hpair : pullback.lift P.1 Q.1 (P.2.trans Q.2.symm) ≫ (pullback.fst f f ≫ f) = t := by
    rw [← Category.assoc, pullback.lift_fst, P.2]
  rw [val_mul_natural L' _ hpair]
  exact val_mul_congr_pts L' t hX hY
end GoodReductionJacobian.P2mIsoUp
p2m_reactivate "P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_WithFullLevel_iso_of_comp_hom_eq_of_isPullbackVia_fstHom.P2mIsoUpInst"
p2m_reactivate "P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_WithFullLevel_iso_of_comp_hom_eq_of_isPullbackVia_fstHom.P2mIsoUpInst"

open GoodReductionJacobian.P2mIsoUp

theorem solution
    {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} {N m : ℕ}
    (k : Type) [Field k] (hN : IsUnit ((N : ℕ) : k)) (hm' : IsUnit ((m : ℕ) : k))
    (u : FakeEllipticCurve.WithFullLevel Λ N m k)
    (w t : FakeEllipticCurve.WithFullLevel Λ N m (DualNumber k))
    (gw : u.1.A ⟶ w.1.A) (hgw : FakeEllipticCurve.IsPullbackVia (TrivSqZeroExt.fstHom k k k).toRingHom w.1 u.1 gw)
    (hgwP : (u.2.P).1 ≫ gw = Spec.map (CommRingCat.ofHom (TrivSqZeroExt.fstHom k k k).toRingHom) ≫ (w.2.P).1)
    (gt : u.1.A ⟶ t.1.A) (hgt : FakeEllipticCurve.IsPullbackVia (TrivSqZeroExt.fstHom k k k).toRingHom t.1 u.1 gt)
    (hgtP : (u.2.P).1 ≫ gt = Spec.map (CommRingCat.ofHom (TrivSqZeroExt.fstHom k k k).toRingHom) ≫ (t.2.P).1)
    (e : w.1.A ≅ t.1.A) (he : e.hom ≫ t.1.f = w.1.f) (hge : gw ≫ e.hom = gt) :
    FakeEllipticCurve.WithFullLevel.Iso w t := by
  classical
  obtain ⟨hgwc, hgwmul, hgwact, hgwlev⟩ := hgw
  obtain ⟨hgtc, hgtmul, hgtact, hgtlev⟩ := hgt
  have hew : (w.1.L.one (𝟙 _)).1 ≫ w.1.f = 𝟙 _ := (w.1.L.one (𝟙 _)).2
  have het : (t.1.L.one (𝟙 _)).1 ≫ t.1.f = 𝟙 _ := (t.1.L.one (𝟙 _)).2
  have heu : (u.1.L.one (𝟙 _)).1 ≫ u.1.f = 𝟙 _ := (u.1.L.one (𝟙 _)).2

  have hg_one : ∀ (v : FakeEllipticCurve.WithFullLevel Λ N m (DualNumber k)) (g : u.1.A ⟶ v.1.A)
      (hgc : IsPullback g u.1.f v.1.f (Spec.map (CommRingCat.ofHom (TrivSqZeroExt.fstHom k k k).toRingHom)))
      (hgmul : ∀ {T : Scheme.{0}} (t' : T ⟶ Spec (CommRingCat.of k)) (P Q : SchemeHomOver t' u.1.f),
        (u.1.L.mul t' P Q).1 ≫ g =
          (v.1.L.mul (t' ≫ Spec.map (CommRingCat.ofHom (TrivSqZeroExt.fstHom k k k).toRingHom))
            ⟨P.1 ≫ g, by rw [Category.assoc, hgc.w, ← Category.assoc, P.2]⟩
            ⟨Q.1 ≫ g, by rw [Category.assoc, hgc.w, ← Category.assoc, Q.2]⟩).1),
      (u.1.L.one (𝟙 _)).1 ≫ g = Spec.map (CommRingCat.ofHom (TrivSqZeroExt.fstHom k k k).toRingHom) ≫ (v.1.L.one (𝟙 _)).1 := by
    intro v g hgc hgmul
    have hidem := hgmul (𝟙 _) (u.1.L.one (𝟙 _)) (u.1.L.one (𝟙 _))
    rw [u.1.L.one_mul] at hidem
    have hpt : (⟨(u.1.L.one (𝟙 _)).1 ≫ g, by rw [Category.assoc, hgc.w, ← Category.assoc, (u.1.L.one (𝟙 _)).2]⟩ :
        SchemeHomOver (𝟙 _ ≫ Spec.map (CommRingCat.ofHom (TrivSqZeroExt.fstHom k k k).toRingHom)) v.1.f)
        = v.1.L.one (𝟙 _ ≫ Spec.map (CommRingCat.ofHom (TrivSqZeroExt.fstHom k k k).toRingHom)) := by
      apply eq_one_of_mul_self
      apply pt_ext
      exact hidem.symm
    rw [show (u.1.L.one (𝟙 _)).1 ≫ g = (v.1.L.one (𝟙 _ ≫ Spec.map (CommRingCat.ofHom (TrivSqZeroExt.fstHom k k k).toRingHom))).1 from
      congrArg Subtype.val hpt, val_one_congr v.1.L (Category.id_comp _),
      ← val_one_natural v.1.L (Spec.map (CommRingCat.ofHom (TrivSqZeroExt.fstHom k k k).toRingHom)) (Category.comp_id _)]
  have hgw_one := hg_one w gw hgwc hgwmul
  have hgt_one := hg_one t gt hgtc hgtmul

  let ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of (DualNumber k)))) t.1.f :=
    ⟨(w.1.L.one (𝟙 _)).1 ≫ e.hom, by rw [Category.assoc, he, hew]⟩
  let e' : w.1.A ≅ t.1.A := e ≪≫ transIso t.1.L (t.1.L.inv (𝟙 _) ε)
  have he'hom : e'.hom = e.hom ≫ trans t.1.L (t.1.L.inv (𝟙 _) ε) := rfl
  have he' : e'.hom ≫ t.1.f = w.1.f := by
    rw [he'hom, Category.assoc, trans_over, he]

  have hεS : Spec.map (CommRingCat.ofHom (TrivSqZeroExt.fstHom k k k).toRingHom) ≫ ε.1
      = (t.1.L.one (Spec.map (CommRingCat.ofHom (TrivSqZeroExt.fstHom k k k).toRingHom))).1 := by
    show Spec.map (CommRingCat.ofHom (TrivSqZeroExt.fstHom k k k).toRingHom) ≫ (w.1.L.one (𝟙 _)).1 ≫ e.hom = _
    rw [← Category.assoc, ← hgw_one, Category.assoc, hge, hgt_one,
      val_one_natural t.1.L (Spec.map (CommRingCat.ofHom (TrivSqZeroExt.fstHom k k k).toRingHom)) (Category.comp_id _)]
  have hεinvS : Spec.map (CommRingCat.ofHom (TrivSqZeroExt.fstHom k k k).toRingHom) ≫ (t.1.L.inv (𝟙 _) ε).1
      = (t.1.L.one (Spec.map (CommRingCat.ofHom (TrivSqZeroExt.fstHom k k k).toRingHom))).1 := by
    rw [val_inv_natural t.1.L (Spec.map (CommRingCat.ofHom (TrivSqZeroExt.fstHom k k k).toRingHom)) (Category.comp_id _) ε]
    have hpt : (⟨Spec.map (CommRingCat.ofHom (TrivSqZeroExt.fstHom k k k).toRingHom) ≫ ε.1, by rw [Category.assoc, ε.2, Category.comp_id]⟩ :
        SchemeHomOver (Spec.map (CommRingCat.ofHom (TrivSqZeroExt.fstHom k k k).toRingHom)) t.1.f)
        = t.1.L.one (Spec.map (CommRingCat.ofHom (TrivSqZeroExt.fstHom k k k).toRingHom)) := pt_ext hεS
    rw [hpt, inv_one_pt]

  have hge' : gw ≫ e'.hom = gt := by
    rw [he'hom, ← Category.assoc, hge, comp_trans]
    have hc : (⟨(gt ≫ t.1.f) ≫ (t.1.L.inv (𝟙 _) ε).1, by rw [Category.assoc, (t.1.L.inv (𝟙 _) ε).2, Category.comp_id]⟩ :
        SchemeHomOver (gt ≫ t.1.f) t.1.f) = t.1.L.one (gt ≫ t.1.f) := by
      apply pt_ext
      show (gt ≫ t.1.f) ≫ (t.1.L.inv (𝟙 _) ε).1 = (t.1.L.one (gt ≫ t.1.f)).1
      rw [hgtc.w, Category.assoc, hεinvS, val_one_natural t.1.L u.1.f rfl]
    rw [hc, t.1.L.mul_one]

  have he'_one : (w.1.L.one (𝟙 _)).1 ≫ e'.hom = (t.1.L.one (𝟙 _)).1 := by
    rw [he'hom, ← Category.assoc, comp_trans]
    have h1 : (⟨(w.1.L.one (𝟙 _)).1 ≫ e.hom, rfl⟩ : SchemeHomOver (((w.1.L.one (𝟙 _)).1 ≫ e.hom) ≫ t.1.f) t.1.f).1 = ε.1 := rfl
    have h2 : (⟨(((w.1.L.one (𝟙 _)).1 ≫ e.hom) ≫ t.1.f) ≫ (t.1.L.inv (𝟙 _) ε).1, by rw [Category.assoc, (t.1.L.inv (𝟙 _) ε).2, Category.comp_id]⟩ :
        SchemeHomOver (((w.1.L.one (𝟙 _)).1 ≫ e.hom) ≫ t.1.f) t.1.f).1 = (t.1.L.inv (𝟙 _) ε).1 := by
      show (((w.1.L.one (𝟙 _)).1 ≫ e.hom) ≫ t.1.f) ≫ (t.1.L.inv (𝟙 _) ε).1 = (t.1.L.inv (𝟙 _) ε).1
      rw [ε.2, Category.id_comp]
    rw [val_mul_congr' t.1.L ε.2 h1 h2, t.1.L.mul_inv_cancel]

  haveI : IsProper w.1.f := w.1.bundle.proper
  haveI : Smooth w.1.f := w.1.bundle.smooth
  haveI : IsProper t.1.f := t.1.bundle.proper
  haveI : Smooth t.1.f := t.1.bundle.smooth
  have hfst_surj : Function.Surjective (TrivSqZeroExt.fstHom k k k).toRingHom := fun x => ⟨TrivSqZeroExt.inl x, rfl⟩
  haveI hGIw : GeometricallyIntegral w.1.f := AbelianSchemePropertyBundle.geometricallyIntegral_of_commRing w.1.bundle
  have hbij : ∀ {X : Scheme.{0}} (q : X ⟶ Spec (CommRingCat.of (DualNumber k))) [IsProper q] [Smooth q] [GeometricallyIrreducible q]
      (s : Spec (CommRingCat.of (DualNumber k)) ⟶ X), s ≫ q = 𝟙 _ →
      Function.Bijective (pullback.snd q (Spec.map (CommRingCat.ofHom (TrivSqZeroExt.fstHom k k k).toRingHom))).appTop := by
    intro X q _ _ _ s hs
    haveI : Smooth (pullback.snd q (Spec.map (CommRingCat.ofHom (TrivSqZeroExt.fstHom k k k).toRingHom))) :=
      MorphismProperty.pullback_snd _ _ inferInstance
    haveI : Nonempty ↥(pullback q (Spec.map (CommRingCat.ofHom (TrivSqZeroExt.fstHom k k k).toRingHom))) :=
      ⟨(pullback.lift (Spec.map (CommRingCat.ofHom (TrivSqZeroExt.fstHom k k k).toRingHom) ≫ s) (𝟙 _)
        (by rw [Category.assoc, hs, Category.comp_id, Category.id_comp])).base (IsLocalRing.closedPoint _)⟩
    have hb := (AlgebraicGeometry.geometricallyIrreducible_iff_bijective_appTop_of_isProper_of_smooth
      (pullback.snd q (Spec.map (CommRingCat.ofHom (TrivSqZeroExt.fstHom k k k).toRingHom)))).mp inferInstance
    rw [CommRingCat.hom_comp, RingHom.coe_comp] at hb
    exact (Function.Bijective.of_comp_iff _
      (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of k)).inv)).mp hb

  have hhom :
      (w.1.L.mul (pullback.fst w.1.f w.1.f ≫ w.1.f) ⟨pullback.fst w.1.f w.1.f, rfl⟩ ⟨pullback.snd w.1.f w.1.f, pullback.condition.symm⟩).1 ≫ e'.hom
        = (t.1.L.mul (pullback.fst w.1.f w.1.f ≫ w.1.f) ⟨pullback.fst w.1.f w.1.f ≫ e'.hom, by rw [Category.assoc, he']⟩
            ⟨pullback.snd w.1.f w.1.f ≫ e'.hom, by rw [Category.assoc, he', pullback.condition]⟩).1 := by
    haveI : Smooth (pullback.fst w.1.f w.1.f) := MorphismProperty.pullback_fst _ _ inferInstance
    haveI : GeometricallyIrreducible (pullback.fst w.1.f w.1.f ≫ w.1.f) := GeometricallyIrreducible.comp _ _
    have hsP : pullback.lift (w.1.L.one (𝟙 _)).1 (w.1.L.one (𝟙 _)).1 rfl ≫ (pullback.fst w.1.f w.1.f ≫ w.1.f) = 𝟙 _ := by
      rw [← Category.assoc, pullback.lift_fst, hew]
    have hiP : IsPullback (pullback.fst (pullback.fst w.1.f w.1.f ≫ w.1.f) (Spec.map (CommRingCat.ofHom (TrivSqZeroExt.fstHom k k k).toRingHom)))
        (pullback.snd (pullback.fst w.1.f w.1.f ≫ w.1.f) (Spec.map (CommRingCat.ofHom (TrivSqZeroExt.fstHom k k k).toRingHom)))
        (pullback.fst w.1.f w.1.f ≫ w.1.f) (Spec.map (CommRingCat.ofHom (TrivSqZeroExt.fstHom k k k).toRingHom)) :=
      IsPullback.of_hasPullback _ _
    set iP := pullback.fst (pullback.fst w.1.f w.1.f ≫ w.1.f) (Spec.map (CommRingCat.ofHom (TrivSqZeroExt.fstHom k k k).toRingHom)) with hiPdef
    set fP := pullback.snd (pullback.fst w.1.f w.1.f ≫ w.1.f) (Spec.map (CommRingCat.ofHom (TrivSqZeroExt.fstHom k k k).toRingHom)) with hfPdef
    have ht₀ : iP ≫ (pullback.fst w.1.f w.1.f ≫ w.1.f) = fP ≫ Spec.map (CommRingCat.ofHom (TrivSqZeroExt.fstHom k k k).toRingHom) := hiP.w
    have hw₁ : (iP ≫ pullback.fst w.1.f w.1.f) ≫ w.1.f = fP ≫ Spec.map (CommRingCat.ofHom (TrivSqZeroExt.fstHom k k k).toRingHom) := by
      rw [Category.assoc]; exact ht₀
    have hw₂ : (iP ≫ pullback.snd w.1.f w.1.f) ≫ w.1.f = fP ≫ Spec.map (CommRingCat.ofHom (TrivSqZeroExt.fstHom k k k).toRingHom) := by
      rw [Category.assoc, ← pullback.condition]; exact ht₀
    have hP₀ : hgwc.lift _ _ hw₁ ≫ gw = iP ≫ pullback.fst w.1.f w.1.f := hgwc.lift_fst _ _ _
    have hQ₀ : hgwc.lift _ _ hw₂ ≫ gw = iP ≫ pullback.snd w.1.f w.1.f := hgwc.lift_fst _ _ _
    have hP₀f : hgwc.lift _ _ hw₁ ≫ u.1.f = fP := hgwc.lift_snd _ _ _
    have hQ₀f : hgwc.lift _ _ hw₂ ≫ u.1.f = fP := hgwc.lift_snd _ _ _
    apply GoodReductionJacobian.RelativeGroupLaw.eq_of_comp_eq_of_isPullback_of_isArtinianRing
      (TrivSqZeroExt.fstHom k k k).toRingHom hfst_surj t.1.L
      (hbij (pullback.fst w.1.f w.1.f ≫ w.1.f) _ hsP) iP hiP _ hsP _ _
      (by rw [Category.assoc, he']; exact (w.1.L.mul _ _ _).2) (t.1.L.mul _ _ _).2
    ·
      have hD := hgwmul fP ⟨_, hP₀f⟩ ⟨_, hQ₀f⟩
      have hD' := hgtmul fP ⟨_, hP₀f⟩ ⟨_, hQ₀f⟩
      rw [← Category.assoc, val_mul_natural w.1.L iP rfl, val_mul_natural t.1.L iP rfl]
      have e1 : (w.1.L.mul (iP ≫ (pullback.fst w.1.f w.1.f ≫ w.1.f))
          ⟨iP ≫ pullback.fst w.1.f w.1.f, by rw [Category.assoc]⟩
          ⟨iP ≫ pullback.snd w.1.f w.1.f, by rw [Category.assoc, ← pullback.condition]⟩).1
          = (u.1.L.mul fP ⟨_, hP₀f⟩ ⟨_, hQ₀f⟩).1 ≫ gw := by
        rw [hD]; exact val_mul_congr' w.1.L ht₀ hP₀.symm hQ₀.symm
      rw [e1, Category.assoc, hge', hD']
      exact val_mul_congr' t.1.L ht₀.symm
        (by show hgwc.lift _ _ hw₁ ≫ gt = iP ≫ (pullback.fst w.1.f w.1.f ≫ e'.hom)
            rw [← hge', ← Category.assoc, hP₀, Category.assoc])
        (by show hgwc.lift _ _ hw₂ ≫ gt = iP ≫ (pullback.snd w.1.f w.1.f ≫ e'.hom)
            rw [← hge', ← Category.assoc, hQ₀, Category.assoc])
    ·
      have h1 : pullback.lift (w.1.L.one (𝟙 _)).1 (w.1.L.one (𝟙 _)).1 rfl ≫ pullback.fst w.1.f w.1.f = (w.1.L.one (𝟙 _)).1 :=
        pullback.lift_fst _ _ _
      have h2 : pullback.lift (w.1.L.one (𝟙 _)).1 (w.1.L.one (𝟙 _)).1 rfl ≫ pullback.snd w.1.f w.1.f = (w.1.L.one (𝟙 _)).1 :=
        pullback.lift_snd _ _ _
      rw [← Category.assoc, val_mul_natural w.1.L _ hsP, val_mul_natural t.1.L _ hsP,
        val_mul_eq_one_of w.1.L (𝟙 _) _ _ _ _ h1 h2, he'_one,
        val_mul_eq_one_of t.1.L (𝟙 _) _ _ _ _ (by rw [← Category.assoc, h1, he'_one]) (by rw [← Category.assoc, h2, he'_one])]

  have hmulE : ∀ {T : Scheme.{0}} (t'' : T ⟶ Spec (CommRingCat.of (DualNumber k))) (P Q : SchemeHomOver t'' w.1.f),
      mapPt e'.hom he' (w.1.L.mul t'' P Q) = t.1.L.mul t'' (mapPt e'.hom he' P) (mapPt e'.hom he' Q) := by
    intro T t'' P Q
    apply pt_ext
    rw [mapPt_coe]
    have eL := val_mul_eq_lift_comp w.1.L t'' P Q P Q ⟨pullback.fst w.1.f w.1.f, rfl⟩ ⟨pullback.snd w.1.f w.1.f, pullback.condition.symm⟩
      (pullback.lift_fst _ _ _).symm (pullback.lift_snd _ _ _).symm
    have eR := val_mul_eq_lift_comp' t.1.L t'' P Q (mapPt e'.hom he' P) (mapPt e'.hom he' Q)
      ⟨pullback.fst w.1.f w.1.f ≫ e'.hom, by rw [Category.assoc, he']⟩
      ⟨pullback.snd w.1.f w.1.f ≫ e'.hom, by rw [Category.assoc, he', pullback.condition]⟩
      (by rw [mapPt_coe, ← Category.assoc, pullback.lift_fst])
      (by rw [mapPt_coe, ← Category.assoc, pullback.lift_snd])
    rw [eL, eR, Category.assoc, hhom]

  have hactE : ∀ x : ↥Λ, w.1.act x ≫ e'.hom = e'.hom ≫ t.1.act x := by
    intro x
    have he₁ : (w.1.act x ≫ e'.hom) ≫ t.1.f = w.1.f := by rw [Category.assoc, he', w.1.act_over]
    have he₂ : (e'.hom ≫ t.1.act x) ≫ t.1.f = w.1.f := by rw [Category.assoc, t.1.act_over, he']
    refine CerednikDrinfeld.QM.FakeEllipticCurve.hom_eq_of_comp_eq_of_isPullback_fstHom u.1 w.1 t.1 gw hgwc
      (w.1.act x ≫ e'.hom) (e'.hom ≫ t.1.act x) he₁ he₂ ?_ ?_ ?_
    · intro T t'' P Q
      apply pt_ext
      rw [mapPt_coe, ← Category.assoc]
      have h1 := congrArg Subtype.val (w.1.act_hom x t'' P Q)
      simp only [mapPt_coe] at h1
      rw [h1]
      have h2 := congrArg Subtype.val (hmulE t'' (pushPt (w.1.act x) (w.1.act_over x) P) (pushPt (w.1.act x) (w.1.act_over x) Q))
      rw [mapPt_coe] at h2
      rw [h2]
      exact val_mul_congr_pts t.1.L t'' (by simp only [mapPt_coe, Category.assoc]) (by simp only [mapPt_coe, Category.assoc])
    · intro T t'' P Q
      apply pt_ext
      rw [mapPt_coe, ← Category.assoc]
      have h1 := congrArg Subtype.val (hmulE t'' P Q)
      rw [mapPt_coe] at h1
      rw [h1]
      have h2 := congrArg Subtype.val (t.1.act_hom x t'' (mapPt e'.hom he' P) (mapPt e'.hom he' Q))
      simp only [mapPt_coe] at h2
      rw [h2]
      exact val_mul_congr_pts t.1.L t'' (by simp only [mapPt_coe, Category.assoc]) (by simp only [mapPt_coe, Category.assoc])
    · rw [← Category.assoc, ← hgwact, Category.assoc, hge', hgtact, ← Category.assoc, hge']

  have hinvf : e'.inv ≫ w.1.f = t.1.f := by rw [Iso.inv_comp_eq, he']
  have mapPt_inj : ∀ {T : Scheme.{0}} {t'' : T ⟶ Spec (CommRingCat.of (DualNumber k))} (P Q : SchemeHomOver t'' w.1.f),
      mapPt e'.hom he' P = mapPt e'.hom he' Q → P = Q := by
    intro T t'' P Q h
    have h1 := congrArg Subtype.val h
    rw [mapPt_coe, mapPt_coe] at h1
    exact pt_ext ((cancel_mono e'.hom).mp h1)
  have mapPt_surj : ∀ {T : Scheme.{0}} {t'' : T ⟶ Spec (CommRingCat.of (DualNumber k))} (Q : SchemeHomOver t'' t.1.f),
      mapPt e'.hom he' (mapPt e'.inv hinvf Q) = Q := by
    intro T t'' Q
    apply pt_ext
    rw [mapPt_coe, mapPt_coe, Category.assoc, Iso.inv_hom_id, Category.comp_id]
  have mapPt_one : ∀ {T : Scheme.{0}} (t'' : T ⟶ Spec (CommRingCat.of (DualNumber k))),
      mapPt e'.hom he' (w.1.L.one t'') = t.1.L.one t'' := by
    intro T t''
    apply eq_one_of_mul_self
    have h := hmulE t'' (w.1.L.one t'') (w.1.L.one t'')
    rw [w.1.L.one_mul] at h
    exact h.symm
  have mapPt_nsmul : ∀ {T : Scheme.{0}} (t'' : T ⟶ Spec (CommRingCat.of (DualNumber k))) (n : ℕ) (P : SchemeHomOver t'' w.1.f),
      mapPt e'.hom he' (nsmulPt w.1.L t'' n P) = nsmulPt t.1.L t'' n (mapPt e'.hom he' P) := by
    intro T t'' n P
    induction n with
    | zero => exact mapPt_one t''
    | succ n ih =>
      show mapPt e'.hom he' (w.1.L.mul t'' (nsmulPt w.1.L t'' n P) P) = t.1.L.mul t'' (nsmulPt t.1.L t'' n (mapPt e'.hom he' P)) (mapPt e'.hom he' P)
      rw [hmulE, ih]
  have mapPt_pushPt : ∀ (x : ↥Λ) {T : Scheme.{0}} {t'' : T ⟶ Spec (CommRingCat.of (DualNumber k))} (P : SchemeHomOver t'' w.1.f),
      mapPt e'.hom he' (pushPt (w.1.act x) (w.1.act_over x) P) = pushPt (t.1.act x) (t.1.act_over x) (mapPt e'.hom he' P) := by
    intro x T t'' P
    apply pt_ext
    simp only [mapPt_coe, Category.assoc, hactE]
  have mapPt_sectionAt : ∀ (P : SchemeHomOver (𝟙 (Spec (CommRingCat.of (DualNumber k)))) w.1.f) (K : Type) [Field K] (sk : DualNumber k →+* K),
      mapPt e'.hom he' (FakeEllipticCurve.sectionAt P K sk) = FakeEllipticCurve.sectionAt (mapPt e'.hom he' P) K sk := by
    intro P K _ sk
    apply pt_ext
    simp only [mapPt_coe, FakeEllipticCurve.sectionAt, schemeHomOverComp_coe, Category.assoc]

  let P' : t.1.FullLevel m :=
    { P := mapPt e'.hom he' w.2.P
      torsion := by rw [← mapPt_nsmul, w.2.torsion, mapPt_one]
      generates := by
        intro K _ _ sk Q hQ
        have hQ' : nsmulPt w.1.L (geomPoint K sk) m (mapPt e'.inv hinvf Q) = w.1.L.one (geomPoint K sk) := by
          apply mapPt_inj
          rw [mapPt_nsmul, mapPt_surj, mapPt_one, hQ]
        obtain ⟨x, hx⟩ := w.2.generates K sk (mapPt e'.inv hinvf Q) hQ'
        refine ⟨x, ?_⟩
        rw [← mapPt_sectionAt, ← mapPt_pushPt, hx, mapPt_surj]
      annihilator := by
        intro K _ _ sk x
        rw [← w.2.annihilator K sk x, ← mapPt_sectionAt, ← mapPt_pushPt, ← mapPt_one]
        exact ⟨fun h => mapPt_inj _ _ h, fun h => by rw [h]⟩ }
  have hm'' : IsUnit ((m : ℕ) : DualNumber k) := by
    have h := hm'.map (algebraMap k (DualNumber k))
    rwa [map_natCast] at h
  have hInil : IsNilpotent (RingHom.ker (TrivSqZeroExt.fstHom k k k).toRingHom) := by
    have hmul : RingHom.ker (TrivSqZeroExt.fstHom k k k).toRingHom * RingHom.ker (TrivSqZeroExt.fstHom k k k).toRingHom = ⊥ := by
      rw [eq_bot_iff, Ideal.mul_le]
      intro x hx y hy
      rw [RingHom.mem_ker] at hx hy
      change TrivSqZeroExt.fst x = 0 at hx
      change TrivSqZeroExt.fst y = 0 at hy
      rw [Submodule.mem_bot]
      ext <;> simp [hx, hy]
    have h2 : RingHom.ker (TrivSqZeroExt.fstHom k k k).toRingHom ^ 2 = ⊥ := by rw [pow_two]; exact hmul
    exact ⟨2, h2⟩
  have hgen : mapPt e'.hom he' w.2.P = t.2.P := by
    obtain ⟨P₁, hP₁, huniq⟩ := CerednikDrinfeld.QM.FakeEllipticCurve.FullLevel.existsUnique_comp_eq_specMap_comp_of_isNilpotent_ker
      t.1 u.1 m hm'' (TrivSqZeroExt.fstHom k k k).toRingHom hfst_surj hInil gt hgtc hgtmul hgtact u.2
    have h1 : P' = P₁ := huniq P' (by
      show (u.2.P).1 ≫ gt = Spec.map (CommRingCat.ofHom (TrivSqZeroExt.fstHom k k k).toRingHom) ≫ ((w.2.P).1 ≫ e'.hom)
      rw [← hge', ← Category.assoc, hgwP, Category.assoc])
    have h2 : t.2 = P₁ := huniq t.2 hgtP
    have h3 : P' = t.2 := h1.trans h2.symm
    exact congrArg FakeEllipticCurve.FullLevel.P h3

  have hN' : ∀ (K : Type) [Field K] (σ : k →+* K), ((N : ℕ) : K) ≠ 0 := by
    intro K _ σ
    have h := hN.map σ
    rw [map_natCast] at h
    exact h.ne_zero
  haveI hNz : NeZero N := ⟨by
    rintro hN0
    rw [hN0, Nat.cast_zero] at hN
    exact not_isUnit_zero hN⟩
  have hNε : IsUnit ((N : ℕ) : DualNumber k) := by
    have h := hN.map (algebraMap k (DualNumber k))
    rwa [map_natCast] at h

  have hcount : ∀ (v : FakeEllipticCurve.WithFullLevel Λ N m (DualNumber k)) (g : u.1.A ⟶ v.1.A)
      (hgc : IsPullback g u.1.f v.1.f (Spec.map (CommRingCat.ofHom (TrivSqZeroExt.fstHom k k k).toRingHom)))
      (hglev : ∀ {T : Scheme.{0}} (t' : T ⟶ Spec (CommRingCat.of k)) (P : SchemeHomOver t' u.1.f),
        FactorsThrough u.1.lev P → ∃ P₀ : T ⟶ v.1.C, P₀ ≫ v.1.lev = P.1 ≫ g)
      (K : Type) [Field K] [IsAlgClosed K] (sk₀ : k →+* K) (R₀ : SchemeHomOver (geomPoint K sk₀) u.1.f)
      (hR : (R₀.1 ≫ g) ≫ v.1.f = geomPoint K (sk₀.comp (TrivSqZeroExt.fstHom k k k).toRingHom)),
      FactorsThrough v.1.lev (⟨R₀.1 ≫ g, hR⟩ : SchemeHomOver (geomPoint K (sk₀.comp (TrivSqZeroExt.fstHom k k k).toRingHom)) v.1.f)
        → FactorsThrough u.1.lev R₀ := by
    intro v g hgc hglev K _ _ sk₀ R₀ hR hv
    have hbase : geomPoint K (sk₀.comp (TrivSqZeroExt.fstHom k k k).toRingHom)
        = geomPoint K sk₀ ≫ Spec.map (CommRingCat.ofHom (TrivSqZeroExt.fstHom k k k).toRingHom) := by
      show Spec.map _ = Spec.map _ ≫ Spec.map _
      rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
    obtain ⟨eu, -⟩ := u.1.lev_fibre K sk₀ (hN' K sk₀)
    obtain ⟨ev, -⟩ := v.1.lev_fibre K (sk₀.comp (TrivSqZeroExt.fstHom k k k).toRingHom) (hN' K sk₀)
    haveI : Fintype {P : SchemeHomOver (geomPoint K sk₀) u.1.f // FactorsThrough u.1.lev P} := Fintype.ofEquiv _ eu
    haveI : Fintype {Q : SchemeHomOver (geomPoint K (sk₀.comp (TrivSqZeroExt.fstHom k k k).toRingHom)) v.1.f // FactorsThrough v.1.lev Q} :=
      Fintype.ofEquiv _ ev
    let φ : {P : SchemeHomOver (geomPoint K sk₀) u.1.f // FactorsThrough u.1.lev P} →
        {Q : SchemeHomOver (geomPoint K (sk₀.comp (TrivSqZeroExt.fstHom k k k).toRingHom)) v.1.f // FactorsThrough v.1.lev Q} :=
      fun P => ⟨⟨P.1.1 ≫ g, by rw [Category.assoc, hgc.w, ← Category.assoc, P.1.2, hbase]⟩, hglev _ P.1 P.2⟩
    have hφinj : Function.Injective φ := by
      intro P P' h
      have h1 : P.1.1 ≫ g = P'.1.1 ≫ g := congrArg (fun Q => Q.1.1) h
      apply Subtype.ext
      apply pt_ext
      exact hgc.hom_ext h1 (by rw [P.1.2, P'.1.2])
    have hcard : Fintype.card {P : SchemeHomOver (geomPoint K sk₀) u.1.f // FactorsThrough u.1.lev P}
        = Fintype.card {Q : SchemeHomOver (geomPoint K (sk₀.comp (TrivSqZeroExt.fstHom k k k).toRingHom)) v.1.f // FactorsThrough v.1.lev Q} :=
      Fintype.card_eq.mpr ⟨eu.symm.trans ev⟩
    have hφbij := (Fintype.bijective_iff_injective_and_card φ).mpr ⟨hφinj, hcard⟩
    obtain ⟨P, hP⟩ := hφbij.2 ⟨⟨R₀.1 ≫ g, hR⟩, hv⟩
    have hPR : P.1 = R₀ := by
      have h1 : P.1.1 ≫ g = R₀.1 ≫ g := congrArg (fun Q => Q.1.1) hP
      apply pt_ext
      exact hgc.hom_ext h1 (by rw [P.1.2, R₀.2])
    rw [← hPR]
    exact P.2

  have hsk : ∀ (K : Type) [Field K] (sk : DualNumber k →+* K),
      sk = (sk.comp (algebraMap k (DualNumber k))).comp (TrivSqZeroExt.fstHom k k k).toRingHom := by
    intro K _ sk
    apply DualNumber.ringHom_ext
    · ext r
      simp
    · have h0 : sk DualNumber.eps = 0 := ((DualNumber.isNilpotent_eps).map sk).eq_zero
      rw [h0]
      simp

  have hgeo : ∀ (K : Type) [Field K] [IsAlgClosed K] (sk : DualNumber k →+* K) (R : SchemeHomOver (geomPoint K sk) w.1.f),
      FactorsThrough w.1.lev R ↔ FactorsThrough t.1.lev (mapPt e'.hom he' R) := by
    intro K _ _ sk R
    set sk₀ : k →+* K := sk.comp (algebraMap k (DualNumber k)) with hsk₀
    have hsk' : sk = sk₀.comp (TrivSqZeroExt.fstHom k k k).toRingHom := hsk K sk
    have hbase : geomPoint K sk = geomPoint K sk₀ ≫ Spec.map (CommRingCat.ofHom (TrivSqZeroExt.fstHom k k k).toRingHom) := by
      show Spec.map _ = Spec.map _ ≫ Spec.map _
      rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, ← hsk']
    have hw₀ : R.1 ≫ w.1.f = geomPoint K sk₀ ≫ Spec.map (CommRingCat.ofHom (TrivSqZeroExt.fstHom k k k).toRingHom) := R.2.trans hbase
    let R₀ : SchemeHomOver (geomPoint K sk₀) u.1.f := ⟨hgwc.lift R.1 (geomPoint K sk₀) hw₀, hgwc.lift_snd _ _ _⟩
    have hR₀ : R₀.1 ≫ gw = R.1 := hgwc.lift_fst _ _ _
    have hRw : (R₀.1 ≫ gw) ≫ w.1.f = geomPoint K (sk₀.comp (TrivSqZeroExt.fstHom k k k).toRingHom) := by
      rw [hR₀, R.2, hsk']
    have hRt : (R₀.1 ≫ gt) ≫ t.1.f = geomPoint K (sk₀.comp (TrivSqZeroExt.fstHom k k k).toRingHom) := by
      rw [← hge', ← Category.assoc, hR₀, Category.assoc, he', R.2, hsk']
    have e1 : FactorsThrough w.1.lev R ↔
        FactorsThrough w.1.lev (⟨R₀.1 ≫ gw, hRw⟩ : SchemeHomOver (geomPoint K (sk₀.comp (TrivSqZeroExt.fstHom k k k).toRingHom)) w.1.f) := by
      show (∃ P₀, P₀ ≫ w.1.lev = R.1) ↔ (∃ P₀, P₀ ≫ w.1.lev = R₀.1 ≫ gw)
      rw [hR₀]
    have e2 : FactorsThrough t.1.lev (mapPt e'.hom he' R) ↔
        FactorsThrough t.1.lev (⟨R₀.1 ≫ gt, hRt⟩ : SchemeHomOver (geomPoint K (sk₀.comp (TrivSqZeroExt.fstHom k k k).toRingHom)) t.1.f) := by
      show (∃ P₀, P₀ ≫ t.1.lev = (mapPt e'.hom he' R).1) ↔ (∃ P₀, P₀ ≫ t.1.lev = R₀.1 ≫ gt)
      rw [mapPt_coe, ← hR₀, Category.assoc, hge']
    rw [e1, e2]
    constructor
    · intro h
      exact hgtlev _ R₀ (hcount w gw hgwc hgwlev K sk₀ R₀ hRw h)
    · intro h
      exact hgwlev _ R₀ (hcount t gt hgtc hgtlev K sk₀ R₀ hRt h)

  have hlevE : ∀ {T : Scheme.{0}} (t'' : T ⟶ Spec (CommRingCat.of (DualNumber k))) (P : SchemeHomOver t'' w.1.f),
      FactorsThrough w.1.lev P ↔ FactorsThrough t.1.lev (mapPt e'.hom he' P) := by
    obtain ⟨-, hwiff⟩ := CerednikDrinfeld.QM.FakeEllipticCurve.etale_lev_and_forall_factorsThrough_iff_of_isUnit w.1 hNε
    obtain ⟨-, htiff⟩ := CerednikDrinfeld.QM.FakeEllipticCurve.etale_lev_and_forall_factorsThrough_iff_of_isUnit t.1 hNε
    intro T t'' P
    rw [hwiff t'' P, htiff t'' (mapPt e'.hom he' P)]
    have hcomp : ∀ (K : Type) [Field K] (sk : DualNumber k →+* K) (τ : Spec (CommRingCat.of K) ⟶ T) (hτ : τ ≫ t'' = geomPoint K sk),
        schemeHomOverComp τ hτ (mapPt e'.hom he' P) = mapPt e'.hom he' (schemeHomOverComp τ hτ P) := by
      intro K _ sk τ hτ
      apply pt_ext
      simp only [schemeHomOverComp_coe, mapPt_coe, Category.assoc]
    constructor
    · rintro ⟨h1, h2⟩
      refine ⟨by rw [← mapPt_nsmul, h1, mapPt_one], fun K _ _ sk τ hτ => ?_⟩
      rw [hcomp K sk τ hτ, ← hgeo K sk]
      exact h2 K sk τ hτ
    · rintro ⟨h1, h2⟩
      refine ⟨mapPt_inj _ _ (by rw [mapPt_nsmul, mapPt_one, h1]), fun K _ _ sk τ hτ => ?_⟩
      rw [hgeo K sk, ← hcomp K sk τ hτ]
      exact h2 K sk τ hτ

  exact ⟨e', he', hmulE, hactE, hlevE, hgen⟩

end
end S_CerednikDrinfeld_QM_FakeEllipticCurve_WithFullLevel_iso_of_comp_hom_eq_of_isPullbackVia_fstHom
end P2MW
export P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_WithFullLevel_iso_of_comp_hom_eq_of_isPullbackVia_fstHom (solution)
