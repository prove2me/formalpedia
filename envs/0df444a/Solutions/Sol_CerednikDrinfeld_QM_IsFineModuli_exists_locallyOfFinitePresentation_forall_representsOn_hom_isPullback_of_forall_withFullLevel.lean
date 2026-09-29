-- Prove2me | solution 1 for CerednikDrinfeld.QM.IsFineModuli.exists_locallyOfFinitePresentation_forall_representsOn_hom_isPullback_of_forall_withFullLevel
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.141142+00:00
-- url     : https://prove2.me/submissions/37ca2548-5b34-5329-b479-5a2437812006

import Mathlib
import Definitions.Def_CerednikDrinfeld_QMFineModuli
import Definitions.Def_CerednikDrinfeld_QMFineModuliT
import Definitions.Def_CerednikDrinfeld_QMIsogenyPairRep
import Definitions.Def_CerednikDrinfeld_QMRigidification
import Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_exists_isPullback_levelIff
import Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_IsogenyPair_existsUnique_hom_isPullback_of_representsOn
import Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_IsPullbackVia_exists_comp_eq_and_isPullbackVia_of_comp_eq
import Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_WithFullLevel_exists_isPullback
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_QM_IsFineModuli_exists_locallyOfFinitePresentation_forall_representsOn_hom_isPullback_of_forall_withFullLevel
p2m_attr_erase "instance" "AlgebraicGeometry.Scheme.Hom.opensMapFinal AlgebraicGeometry.RelPicard.RigidifiedLineBundle.setoid AlgebraicGeometry.RelPicard.RigidifiedLineBundle.instInhabited AlgebraicGeometry.ChowDatum.hι_closed AlgebraicGeometry.ChowDatumProj.hιN_closed AlgebraicGeometry.ChowDatumProj.hp_proper AlgebraicGeometry.ChowDatum.hp_isoU AlgebraicGeometry.ChowDatum.hp_proper AlgebraicGeometry.ProjSpace.algebraAway AlgebraicGeometry.ProjSpace.instIsProperProdOverπ AlgebraicGeometry.ChowDatumProj.hp_isoU AlgebraicGeometry.ProjSpace.isProper_π AlgebraicGeometry.ProjSpace.finiteType_mvPolynomial PresheafOfModules.instMonoidalClosed PresheafOfModules.InternalHom.instModuleCarrierObjOppositeCommRingCatSubtypePiFamilyMemAddSubgroupNaturalFamilies PresheafOfModules.InternalHom.instModuleCarrierObjOppositeRingCatCompCommRingCatForget₂RingHomCarrierCarrierAbPresheaf PresheafOfModules.InternalHom.instSMulCarrierObjOppositeCommRingCatSubtypePiFamilyMemAddSubgroupNaturalFamilies AlgebraicGeometry.Scheme.PresheafOfModules.symmetricCategory SheafOfModules.instFaithfulRingSheafPModToPMod SheafOfModules.symmetricCategory AlgebraicGeometry.Scheme.PresheafOfModules.monoidalCategory AlgebraicGeometry.Scheme.PresheafOfModules.monoidalClosed SheafOfModules.instFullRingSheafPModToPMod SheafOfModules.monoidalCategory AlgebraicGeometry.Scheme.Modules.symmetricCategory SheafOfModules.monoidalClosed SheafOfModules.instIsLocalizationPModRingSheafSheafifyFunctorPresheafW SheafOfModules.sheafifyFunctor_monoidal AlgebraicGeometry.Scheme.Modules.monoidalClosed AlgebraicGeometry.instMonoidalPresheafOfModulesModulesSheafify AlgebraicGeometry.Scheme.Modules.monoidalCategory"
p2m_attr_erase "simp" "GoodReductionJacobian.RelativeGroupLaw.baseChangePointToBase_ofBase GoodReductionJacobian.RelativeGroupLaw.baseChangePointToBase_coe GoodReductionJacobian.RelativeGroupLaw.baseChangePointOfBase_coe GoodReductionJacobian.RelativeGroupLaw.baseChange_inv GoodReductionJacobian.RelativeGroupLaw.baseChangePointOfBase_toBase GoodReductionJacobian.RelativeGroupLaw.baseChange_mul GoodReductionJacobian.RelativeGroupLaw.baseChange_one GoodReductionJacobian.RelativeGroupLaw.nsmul_zero GoodReductionJacobian.RelativeGroupLaw.mem_torsionSubset GoodReductionJacobian.RelativeGroupLaw.nsmul_succ NeronModelInfra.NeronModelPropertyBundle.endExtensionEquiv_symm_restrict NeronModelInfra.schemeHomOverComp_id_left NeronModelInfra.schemeHomOverComp_id_right NeronModelInfra.schemeHomOverId_coe NeronModelInfra.NeronModelPropertyBundle.endExtensionEquiv_apply NeronModelInfra.NeronModelPropertyBundle.restrict_endExtensionEquiv_symm NeronModelInfra.schemeHomOverComp_coe NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_fst NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_snd NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_fst NeronSpecialFibreInfra.neronEndRestrictEquiv_apply NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_fst_assoc NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_snd NeronSpecialFibreInfra.neronEndExtension_genericFibreRestrict NeronSpecialFibreInfra.specClosedFibreInclusion_eq NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_fst_assoc NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_snd_assoc NeronSpecialFibreInfra.genericFibreRestrict_neronEndExtension NeronSpecialFibreInfra.homOverId_coe NeronSpecialFibreInfra.homOverComp_coe NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_snd_assoc GoodReductionJacobian.RelativeGroupLaw.fibre_inv GoodReductionJacobian.RelativeGroupLaw.fibrePointToBase_coe GoodReductionJacobian.RelativeGroupLaw.fibrePointOfBase_toBase GoodReductionJacobian.RelativeGroupLaw.fibre_mul GoodReductionJacobian.RelativeGroupLaw.fibrePointToBase_ofBase GoodReductionJacobian.RelativeGroupLaw.fibre_one GoodReductionJacobian.RelativeGroupLaw.fibrePointOfBase_coe AlgebraicGeometry.schemeFibreEndo_snd AlgebraicGeometry.schemeFibreEndo_fst"
p2m_attr_erase "simp" "RegularLocalRingQuotientAscent.dualNumberFst_apply AlgebraicGeometry.PolarisedAbelianScheme.mk.injEq AlgebraicGeometry.PolarisedAbelianScheme.mk.sizeOf_spec AlgebraicGeometry.RelPicard.RigidifiedLineBundle.mk.sizeOf_spec AlgebraicGeometry.RelPicard.RigidifiedLineBundle.mk.injEq AlgebraicGeometry.Scheme.Modules.ProjPresentation.mk.injEq AlgebraicGeometry.Scheme.Modules.ProjPresentation.mk.sizeOf_spec AlgebraicGeometry.ChowDatumProj.mk.sizeOf_spec AlgebraicGeometry.ChowDatum.mk.sizeOf_spec AlgebraicGeometry.ChowDatumProj.mk.injEq AlgebraicGeometry.ChowDatum.mk.injEq PresheafOfModules.InternalHom.presheaf_map_apply PresheafOfModules.InternalHom.curryFamily_app PresheafOfModules.InternalHom.add_app PresheafOfModules.InternalHom.smul_app PresheafOfModules.InternalHom.zero_app PresheafOfModules.ihomObj_map_val PresheafOfModules.ihomFunctor_map PresheafOfModules.InternalHom.restrict_app PresheafOfModules.InternalHom.postcomp_app PresheafOfModules.InternalHom.neg_app PresheafOfModules.curry'_app_val PresheafOfModules.InternalHom.presheaf_obj PresheafOfModules.ihomFunctor_obj PresheafOfModules.ihomObj_obj PresheafOfModules.InternalHom.sub_app PresheafOfModules.ihomMap_app_val SheafOfModules.tensorUnit_eq AlgebraicGeometry.Scheme.Modules.tensorUnit_eq"

set_option autoImplicit false

open scoped TensorProduct Quaternion NumberField
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry QuaternionAlgebra CerednikDrinfeld CerednikDrinfeld.QM NeronModelInfra GoodReductionJacobian

noncomputable section

namespace RelRepGlue

universe u

variable {N : ℕ} {𝒪 : Type} [CommRing 𝒪]
  {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} {n : ℕ} {M : Scheme.{0}} {fM : M ⟶ Spec (CommRingCat.of 𝒪)}
  {ptF : ∀ (S : Type) [CommRing S] (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of 𝒪)),
    FakeEllipticCurve.WithFullLevel Λ N n S → SchemeHomOver s fM}
  (C : Type) [CommRing C] [Algebra 𝒪 C]

theorem mul_val_congr {R : Type} [CommRing R] {A : Scheme.{0}} {f : A ⟶ Spec (CommRingCat.of R)}
    (L : RelativeGroupLaw R f) {T : Scheme.{0}} {t₁ t₂ : T ⟶ Spec (CommRingCat.of R)} (h : t₁ = t₂)
    (P Q : SchemeHomOver t₁ f) (P' Q' : SchemeHomOver t₂ f) (hP : P.1 = P'.1) (hQ : Q.1 = Q'.1) :
    (L.mul t₁ P Q).1 = (L.mul t₂ P' Q').1 := by
  subst h
  obtain ⟨P, hP1⟩ := P; obtain ⟨P', hP1'⟩ := P'; obtain ⟨Q, hQ1⟩ := Q; obtain ⟨Q', hQ1'⟩ := Q'
  simp only at hP hQ
  subst hP; subst hQ; rfl

theorem isPullback_of_iso_of_isPullback {N' m : ℕ} {S S' : Type} [CommRing S] [CommRing S'] (φ : S →+* S')
    (u : FakeEllipticCurve.WithFullLevel Λ N' m S) (v w : FakeEllipticCurve.WithFullLevel Λ N' m S')
    (hw : FakeEllipticCurve.WithFullLevel.IsPullback φ u w) (hvw : FakeEllipticCurve.WithFullLevel.Iso v w) :
    FakeEllipticCurve.WithFullLevel.IsPullback φ u v := by
  obtain ⟨g, hg, hmul, hact, hlev, hP⟩ := hw
  obtain ⟨e, he, emul, eact, elev, eP⟩ := hvw
  have sq1 : IsPullback e.hom v.1.f w.1.f (𝟙 _) := IsPullback.of_horiz_isIso ⟨by rw [he, Category.comp_id]⟩
  have sq : IsPullback (e.hom ≫ g) v.1.f u.1.f (Spec.map (CommRingCat.ofHom φ)) := by
    simpa using sq1.paste_horiz hg
  refine ⟨e.hom ≫ g, sq, ?_, ?_, ?_, ?_⟩
  · intro T t' P Q
    have h1 := congrArg Subtype.val (emul t' P Q)
    simp only [mapPt_coe] at h1
    rw [← Category.assoc, h1, hmul t' (mapPt e.hom he P) (mapPt e.hom he Q)]
    exact mul_val_congr u.1.L rfl _ _ _ _ (by simp [Category.assoc]) (by simp [Category.assoc])
  · intro x
    rw [← Category.assoc, eact x, Category.assoc, hact x, Category.assoc]
  · intro T t' P hPlev
    obtain ⟨P₀, hP₀⟩ := hlev t' (mapPt e.hom he P) ((elev t' P).mp hPlev)
    exact ⟨P₀, by rw [hP₀, mapPt_coe, Category.assoc]⟩
  · rw [← Category.assoc, show (v.2.P).1 ≫ e.hom = (w.2.P).1 from congrArg Subtype.val eP, hP]

abbrev MC (fM : M ⟶ Spec (CommRingCat.of 𝒪)) (C : Type) [CommRing C] [Algebra 𝒪 C] : Scheme.{0} :=
  pullback fM (Spec.map (CommRingCat.ofHom (algebraMap 𝒪 C)))

abbrev πC (fM : M ⟶ Spec (CommRingCat.of 𝒪)) (C : Type) [CommRing C] [Algebra 𝒪 C] :
    MC fM C ⟶ Spec (CommRingCat.of C) :=
  pullback.snd fM (Spec.map (CommRingCat.ofHom (algebraMap 𝒪 C)))

theorem spec_tower (S : Type) [CommRing S] [Algebra C S] [Algebra 𝒪 S] [IsScalarTower 𝒪 C S] :
    Spec.map (CommRingCat.ofHom (algebraMap C S)) ≫ Spec.map (CommRingCat.ofHom (algebraMap 𝒪 C)) =
      Spec.map (CommRingCat.ofHom (algebraMap 𝒪 S)) := by
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, ← IsScalarTower.algebraMap_eq 𝒪 C S]

noncomputable def ptFC (hM : IsFineModuli Λ N n M fM ptF) (S : Type) [CommRing S] [Algebra C S] [Algebra 𝒪 S] [IsScalarTower 𝒪 C S]
    (u : FakeEllipticCurve.WithFullLevel Λ N n S) :
    SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap C S))) (πC fM C) :=
  ⟨pullback.lift (ptF S (Spec.map (CommRingCat.ofHom (algebraMap 𝒪 S))) u).1
      (Spec.map (CommRingCat.ofHom (algebraMap C S)))
      (by rw [(ptF S (Spec.map (CommRingCat.ofHom (algebraMap 𝒪 S))) u).2, spec_tower C S]),
    pullback.lift_snd _ _ _⟩

@[scoped simp] theorem ptFC_fst (hM : IsFineModuli Λ N n M fM ptF) (S : Type) [CommRing S] [Algebra C S] [Algebra 𝒪 S] [IsScalarTower 𝒪 C S]
    (u : FakeEllipticCurve.WithFullLevel Λ N n S) :
    (ptFC C hM S u).1 ≫ pullback.fst fM (Spec.map (CommRingCat.ofHom (algebraMap 𝒪 C))) =
      (ptF S (Spec.map (CommRingCat.ofHom (algebraMap 𝒪 S))) u).1 :=
  pullback.lift_fst _ _ _

theorem ptFC_snd (hM : IsFineModuli Λ N n M fM ptF) (S : Type) [CommRing S] [Algebra C S] [Algebra 𝒪 S] [IsScalarTower 𝒪 C S]
    (u : FakeEllipticCurve.WithFullLevel Λ N n S) :
    (ptFC C hM S u).1 ≫ πC fM C = Spec.map (CommRingCat.ofHom (algebraMap C S)) :=
  (ptFC C hM S u).2

theorem ptFC_iso (hM : IsFineModuli Λ N n M fM ptF) (S : Type) [CommRing S] [Algebra C S] [Algebra 𝒪 S] [IsScalarTower 𝒪 C S]
    (u u' : FakeEllipticCurve.WithFullLevel Λ N n S) (h : FakeEllipticCurve.WithFullLevel.Iso u u') :
    ptFC C hM S u = ptFC C hM S u' := by
  apply Subtype.ext
  apply pullback.hom_ext
  · rw [ptFC_fst, ptFC_fst, hM.ptF_iso S _ u u' h]
  · rw [ptFC_snd, ptFC_snd]

theorem algHom_comp_algebraMap_tower {S S' : Type} [CommRing S] [Algebra C S] [Algebra 𝒪 S] [IsScalarTower 𝒪 C S]
    [CommRing S'] [Algebra C S'] [Algebra 𝒪 S'] [IsScalarTower 𝒪 C S'] (φ : S →ₐ[C] S') :
    (φ : S →+* S').comp (algebraMap 𝒪 S) = algebraMap 𝒪 S' := by
  rw [IsScalarTower.algebraMap_eq 𝒪 C S, IsScalarTower.algebraMap_eq 𝒪 C S', ← RingHom.comp_assoc, AlgHom.comp_algebraMap]

theorem ptFC_pullback (hM : IsFineModuli Λ N n M fM ptF) (S S' : Type) [CommRing S] [Algebra C S] [Algebra 𝒪 S] [IsScalarTower 𝒪 C S]
    [CommRing S'] [Algebra C S'] [Algebra 𝒪 S'] [IsScalarTower 𝒪 C S'] (φ : S →ₐ[C] S')
    (u : FakeEllipticCurve.WithFullLevel Λ N n S) (u' : FakeEllipticCurve.WithFullLevel Λ N n S')
    (h : FakeEllipticCurve.WithFullLevel.IsPullback (φ : S →+* S') u u') :
    (ptFC C hM S' u').1 = Spec.map (CommRingCat.ofHom (φ : S →+* S')) ≫ (ptFC C hM S u).1 := by
  apply pullback.hom_ext
  · rw [ptFC_fst, Category.assoc, ptFC_fst]
    refine hM.ptF_pullback S S' (φ : S →+* S') _ _ ?_ u u' h
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, algHom_comp_algebraMap_tower C φ]
  · rw [ptFC_snd, Category.assoc, ptFC_snd, ← Spec.map_comp, ← CommRingCat.ofHom_comp, AlgHom.comp_algebraMap]

theorem ptFC_surjective (hM : IsFineModuli Λ N n M fM ptF) (S : Type) [CommRing S] [Algebra C S] [Algebra 𝒪 S] [IsScalarTower 𝒪 C S]
    (x : SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap C S))) (πC fM C)) :
    ∃ u : FakeEllipticCurve.WithFullLevel Λ N n S, ptFC C hM S u = x := by
  obtain ⟨u, hu⟩ := hM.ptF_surjective S (Spec.map (CommRingCat.ofHom (algebraMap 𝒪 S)))
    ⟨x.1 ≫ pullback.fst fM (Spec.map (CommRingCat.ofHom (algebraMap 𝒪 C))), by
      rw [Category.assoc, pullback.condition, ← Category.assoc, x.2, spec_tower C S]⟩
  refine ⟨u, Subtype.ext (pullback.hom_ext ?_ ?_)⟩
  · rw [ptFC_fst, hu]
  · rw [ptFC_snd, x.2]

theorem ptFC_injective (hM : IsFineModuli Λ N n M fM ptF) (S : Type) [CommRing S] [Algebra C S] [Algebra 𝒪 S] [IsScalarTower 𝒪 C S]
    (u u' : FakeEllipticCurve.WithFullLevel Λ N n S) (h : ptFC C hM S u = ptFC C hM S u') :
    FakeEllipticCurve.WithFullLevel.Iso u u' := by
  refine hM.ptF_injective S (Spec.map (CommRingCat.ofHom (algebraMap 𝒪 S))) u u' (Subtype.ext ?_)
  rw [← ptFC_fst C hM S u, ← ptFC_fst C hM S u', h]

abbrev ringOf (U : (MC fM C).affineOpens) : Type := Γ(MC fM C, U.1)

noncomputable def chartι (U : (MC fM C).affineOpens) : Spec (CommRingCat.of (ringOf (fM := fM) C U)) ⟶ MC fM C :=
  U.2.isoSpec.inv ≫ U.1.ι

scoped instance chartι_isOpenImmersion (U : (MC fM C).affineOpens) : IsOpenImmersion (chartι C U) := by
  unfold chartι; infer_instance

noncomputable def toRingOfC (U : (MC fM C).affineOpens) : C →+* ringOf (fM := fM) C U :=
  (Spec.preimage (chartι C U ≫ πC fM C)).hom

theorem spec_toRingOfC (U : (MC fM C).affineOpens) :
    Spec.map (CommRingCat.ofHom (toRingOfC C U)) = chartι C U ≫ πC fM C := by
  simp [toRingOfC]

@[reducible] noncomputable def algebraC (U : (MC fM C).affineOpens) : Algebra C (ringOf (fM := fM) C U) :=
  (toRingOfC C U).toAlgebra

@[reducible] noncomputable def algebraO (U : (MC fM C).affineOpens) : Algebra 𝒪 (ringOf (fM := fM) C U) :=
  ((toRingOfC C U).comp (algebraMap 𝒪 C)).toAlgebra

attribute [scoped instance] algebraC algebraO

scoped instance isScalarTower_ringOf (U : (MC fM C).affineOpens) : IsScalarTower 𝒪 C (ringOf (fM := fM) C U) :=
  IsScalarTower.of_algebraMap_eq (fun _ => rfl)

theorem algebraMap_ringOf_eq (U : (MC fM C).affineOpens) : algebraMap C (ringOf (fM := fM) C U) = toRingOfC C U := rfl

theorem spec_algebraMap_C (U : (MC fM C).affineOpens) :
    Spec.map (CommRingCat.ofHom (algebraMap C (ringOf (fM := fM) C U))) = chartι C U ≫ πC fM C :=
  spec_toRingOfC C U

theorem isNilpotent_algebraMap_ringOf {π : 𝒪} (hC : IsNilpotent (algebraMap 𝒪 C π)) (U : (MC fM C).affineOpens) :
    IsNilpotent (algebraMap 𝒪 (ringOf (fM := fM) C U) π) := by
  rw [IsScalarTower.algebraMap_apply 𝒪 C]
  exact hC.map (algebraMap C (ringOf (fM := fM) C U))

noncomputable def ψU {Onr : Type} [CommRing Onr] [Algebra 𝒪 Onr] (ψ : Onr →ₐ[𝒪] C) (U : (MC fM C).affineOpens) :
    Onr →ₐ[𝒪] ringOf (fM := fM) C U :=
  (IsScalarTower.toAlgHom 𝒪 C (ringOf (fM := fM) C U)).comp ψ

theorem ψU_eq {Onr : Type} [CommRing Onr] [Algebra 𝒪 Onr] (ψ : Onr →ₐ[𝒪] C) (U : (MC fM C).affineOpens) :
    ψU C ψ U = (IsScalarTower.toAlgHom 𝒪 C (ringOf (fM := fM) C U)).comp ψ := rfl

theorem exists_uof (hM : IsFineModuli Λ N n M fM ptF) (U : (MC fM C).affineOpens) :
    ∃ uU : FakeEllipticCurve.WithFullLevel Λ N n (ringOf (fM := fM) C U), (ptFC C hM (ringOf C U) uU).1 = chartι C U := by
  obtain ⟨uU, h⟩ := ptFC_surjective C hM (ringOf C U) ⟨chartι C U, (spec_algebraMap_C C U).symm⟩
  exact ⟨uU, by rw [h]⟩

noncomputable def uof (hM : IsFineModuli Λ N n M fM ptF) (U : (MC fM C).affineOpens) : FakeEllipticCurve.WithFullLevel Λ N n (ringOf (fM := fM) C U) :=
  (exists_uof C hM U).choose

theorem ptFC_uof (hM : IsFineModuli Λ N n M fM ptF) (U : (MC fM C).affineOpens) : (ptFC C hM (ringOf C U) (uof C hM U)).1 = chartι C U :=
  (exists_uof C hM U).choose_spec

noncomputable def resRing {U V : (MC fM C).affineOpens} (hVU : V ≤ U) : ringOf (fM := fM) C U →+* ringOf (fM := fM) C V :=
  ((MC fM C).presheaf.map (homOfLE hVU).op).hom

theorem spec_resRing_isoSpec {U V : (MC fM C).affineOpens} (hVU : V ≤ U) :
    Spec.map (CommRingCat.ofHom (resRing C hVU)) ≫ U.2.isoSpec.inv = V.2.isoSpec.inv ≫ (MC fM C).homOfLE hVU := by
  rw [← cancel_mono U.1.ι, Category.assoc, Category.assoc, IsAffineOpen.isoSpec_inv_ι, Scheme.homOfLE_ι,
    IsAffineOpen.isoSpec_inv_ι]
  simp only [resRing, CommRingCat.ofHom_hom]
  exact IsAffineOpen.map_fromSpec U.2 V.2 (homOfLE hVU).op

theorem spec_resRing_comp_chartι {U V : (MC fM C).affineOpens} (hVU : V ≤ U) :
    Spec.map (CommRingCat.ofHom (resRing C hVU)) ≫ chartι C U = chartι C V := by
  simp only [chartι]
  rw [← Category.assoc, spec_resRing_isoSpec C hVU, Category.assoc, Scheme.homOfLE_ι]

theorem resRing_comp_algebraMap {U V : (MC fM C).affineOpens} (hVU : V ≤ U) :
    (resRing C hVU).comp (algebraMap C (ringOf (fM := fM) C U)) = algebraMap C (ringOf (fM := fM) C V) := by
  have key : Spec.map (CommRingCat.ofHom ((resRing C hVU).comp (algebraMap C (ringOf (fM := fM) C U)))) =
      Spec.map (CommRingCat.ofHom (algebraMap C (ringOf (fM := fM) C V))) := by
    rw [CommRingCat.ofHom_comp, Spec.map_comp, spec_algebraMap_C, spec_algebraMap_C, ← Category.assoc,
      spec_resRing_comp_chartι]
  exact congrArg CommRingCat.Hom.hom (Spec.map_injective key)

noncomputable def resAlgHom {U V : (MC fM C).affineOpens} (hVU : V ≤ U) :
    ringOf (fM := fM) C U →ₐ[C] ringOf (fM := fM) C V :=
  { toRingHom := resRing C hVU
    commutes' := fun c => RingHom.congr_fun (resRing_comp_algebraMap C hVU) c }

@[scoped simp] theorem coe_resAlgHom {U V : (MC fM C).affineOpens} (hVU : V ≤ U) :
    (resAlgHom C hVU : ringOf (fM := fM) C U →+* ringOf (fM := fM) C V) = resRing C hVU :=
  RingHom.ext fun _ => rfl

theorem uof_isPullback (hM : IsFineModuli Λ N n M fM ptF) {U V : (MC fM C).affineOpens} (hVU : V ≤ U) :
    FakeEllipticCurve.WithFullLevel.IsPullback (resRing C hVU) (uof C hM U) (uof C hM V) := by
  obtain ⟨w, hw⟩ := FakeEllipticCurve.WithFullLevel.exists_isPullback (resRing C hVU) (uof C hM U)
  have h1 := ptFC_pullback C hM (ringOf C U) (ringOf C V) (resAlgHom C hVU) (uof C hM U) w
    (by rw [coe_resAlgHom]; exact hw)
  rw [coe_resAlgHom, ptFC_uof C hM U, spec_resRing_comp_chartι, ← ptFC_uof C hM V] at h1
  have h2 : ptFC C hM (ringOf C V) (uof C hM V) = ptFC C hM (ringOf C V) w := Subtype.ext h1.symm
  exact isPullback_of_iso_of_isPullback _ _ _ _ hw (ptFC_injective C hM _ _ _ h2)

section Sec

variable {S : Type} [CommRing S] (t₁ : Spec (CommRingCat.of S) ⟶ MC fM C)

def SecIdx : Type :=
  {p : (Spec (CommRingCat.of S)).affineOpens × (MC fM C).affineOpens //
    (p.1 : (Spec (CommRingCat.of S)).Opens) ≤ t₁ ⁻¹ᵁ p.2}

noncomputable scoped instance : Preorder (SecIdx C t₁) := Preorder.lift fun p => p.1

theorem exists_secIdx (x : ↥(Spec (CommRingCat.of S))) (O : (Spec (CommRingCat.of S)).Opens) (hx : x ∈ O)
    (O₁ : (MC fM C).Opens) (hx₁ : t₁ x ∈ O₁) :
    ∃ p : SecIdx C t₁, x ∈ (p.1.1 : (Spec (CommRingCat.of S)).Opens) ∧ (p.1.1 : (Spec (CommRingCat.of S)).Opens) ≤ O ∧
      (p.1.2 : (MC fM C).Opens) ≤ O₁ := by
  obtain ⟨_, ⟨U, hU, rfl⟩, hxU, hUO⟩ := (MC fM C).isBasis_affineOpens.exists_subset_of_mem_open hx₁ O₁.2
  obtain ⟨_, ⟨W, hW, rfl⟩, hxW, hWO⟩ := (Spec (CommRingCat.of S)).isBasis_affineOpens.exists_subset_of_mem_open
    (show x ∈ ((t₁ ⁻¹ᵁ U) ⊓ O : (Spec (CommRingCat.of S)).Opens) from ⟨hxU, hx⟩) ((t₁ ⁻¹ᵁ U) ⊓ O).2
  exact ⟨⟨(⟨W, hW⟩, ⟨U, hU⟩), fun y hy => (hWO hy).1⟩, hxW, fun y hy => (hWO hy).2, hUO⟩

noncomputable def secCover : (Spec (CommRingCat.of S)).OpenCover :=
  Scheme.Cover.mkOfCovers (SecIdx C t₁) (fun p => p.1.1) (fun p => (p.1.1 : (Spec (CommRingCat.of S)).Opens).ι)
    (fun x => by
      obtain ⟨p, hx, -⟩ := exists_secIdx C t₁ x ⊤ trivial ⊤ trivial
      exact ⟨p, ⟨x, hx⟩, rfl⟩)

noncomputable scoped instance : Preorder (secCover C t₁).I₀ := inferInstanceAs (Preorder (SecIdx C t₁))

noncomputable scoped instance : Scheme.Cover.LocallyDirected (secCover C t₁) where
  trans {p q} hpq := (Spec (CommRingCat.of S)).homOfLE
    (show (p.1.1 : (Spec (CommRingCat.of S)).Opens) ≤ q.1.1 from (leOfHom hpq).1)
  trans_id p := by simp [secCover]; rfl
  trans_comp hpq hqr := by simp [secCover]; exact (Scheme.homOfLE_homOfLE _ _ _).symm
  w hpq := by simp [secCover]; try exact Scheme.homOfLE_ι _ _
  property_trans {p q} hpq :=
    (inferInstance : IsOpenImmersion ((Spec (CommRingCat.of S)).homOfLE
      (show (p.1.1 : (Spec (CommRingCat.of S)).Opens) ≤ q.1.1 from (leOfHom hpq).1)))
  directed {p q} x := by
    let y : ↥(Spec (CommRingCat.of S)) := (pullback.fst ((secCover C t₁).f p) ((secCover C t₁).f q) ≫ (secCover C t₁).f p) x
    have hyp : y ∈ (p.1.1 : (Spec (CommRingCat.of S)).Opens) := by
      simp only [y, Scheme.Hom.comp_apply]
      exact ((pullback.fst ((secCover C t₁).f p) ((secCover C t₁).f q)) x).2
    have hyq : y ∈ (q.1.1 : (Spec (CommRingCat.of S)).Opens) := by
      have : y = (pullback.snd ((secCover C t₁).f p) ((secCover C t₁).f q) ≫ (secCover C t₁).f q) x := by
        simp only [y, pullback.condition]
      rw [this, Scheme.Hom.comp_apply]
      exact ((pullback.snd ((secCover C t₁).f p) ((secCover C t₁).f q)) x).2
    obtain ⟨k, hyk, hkW, hkU⟩ := exists_secIdx C t₁ y ((p.1.1 : (Spec (CommRingCat.of S)).Opens) ⊓ q.1.1) ⟨hyp, hyq⟩
      ((p.1.2 : (MC fM C).Opens) ⊓ q.1.2) ⟨p.2 hyp, q.2 hyq⟩
    refine ⟨k, homOfLE ⟨fun z hz => (hkW hz).1, fun z hz => (hkU hz).1⟩,
      homOfLE ⟨fun z hz => (hkW hz).2, fun z hz => (hkU hz).2⟩, ⟨y, hyk⟩, ?_⟩
    apply (pullback.fst ((secCover C t₁).f p) ((secCover C t₁).f q) ≫ (secCover C t₁).f p).isOpenEmbedding.injective
    rw [← Scheme.Hom.comp_apply, pullback.lift_fst_assoc]
    change ((Spec (CommRingCat.of S)).homOfLE _ ≫ (p.1.1 : (Spec (CommRingCat.of S)).Opens).ι) ⟨y, hyk⟩ = y
    rw [Scheme.homOfLE_ι]
    rfl

abbrev Wring (p : SecIdx C t₁) : Type := Γ(Spec (CommRingCat.of S), (p.1.1 : (Spec (CommRingCat.of S)).Opens))

noncomputable def Wι (p : SecIdx C t₁) : Spec (CommRingCat.of (Wring C t₁ p)) ⟶ Spec (CommRingCat.of S) :=
  p.1.1.2.isoSpec.inv ≫ (p.1.1 : (Spec (CommRingCat.of S)).Opens).ι

scoped instance Wι_isOpenImmersion (p : SecIdx C t₁) : IsOpenImmersion (Wι C t₁ p) := by
  unfold Wι; infer_instance

noncomputable def rW (p : SecIdx C t₁) : S →+* Wring C t₁ p := (Spec.preimage (Wι C t₁ p)).hom

theorem spec_rW (p : SecIdx C t₁) : Spec.map (CommRingCat.ofHom (rW C t₁ p)) = Wι C t₁ p := by
  simp [rW]

@[reducible] noncomputable def algebraWS (p : SecIdx C t₁) : Algebra S (Wring C t₁ p) := (rW C t₁ p).toAlgebra

attribute [scoped instance] algebraWS

theorem algebraMap_W_eq (p : SecIdx C t₁) : algebraMap S (Wring C t₁ p) = rW C t₁ p := rfl

theorem spec_algebraMap_W (p : SecIdx C t₁) :
    Spec.map (CommRingCat.ofHom (algebraMap S (Wring C t₁ p))) = Wι C t₁ p :=
  spec_rW C t₁ p

variable [Algebra C S] [Algebra 𝒪 S] [IsScalarTower 𝒪 C S]

@[reducible] noncomputable def algebraWC (p : SecIdx C t₁) : Algebra C (Wring C t₁ p) :=
  ((algebraMap S (Wring C t₁ p)).comp (algebraMap C S)).toAlgebra

@[reducible] noncomputable def algebraWO (p : SecIdx C t₁) : Algebra 𝒪 (Wring C t₁ p) :=
  ((algebraMap S (Wring C t₁ p)).comp (algebraMap 𝒪 S)).toAlgebra

attribute [scoped instance] algebraWC algebraWO

scoped instance isScalarTower_CSW (p : SecIdx C t₁) : IsScalarTower C S (Wring C t₁ p) :=
  IsScalarTower.of_algebraMap_eq (fun _ => rfl)

scoped instance isScalarTower_OSW (p : SecIdx C t₁) : IsScalarTower 𝒪 S (Wring C t₁ p) :=
  IsScalarTower.of_algebraMap_eq (fun _ => rfl)

scoped instance isScalarTower_OCW (p : SecIdx C t₁) : IsScalarTower 𝒪 C (Wring C t₁ p) :=
  IsScalarTower.of_algebraMap_eq (fun x => congrArg (algebraMap S (Wring C t₁ p)) (IsScalarTower.algebraMap_apply 𝒪 C S x))

omit [Algebra C S] [Algebra 𝒪 S] [IsScalarTower 𝒪 C S] in

noncomputable def cmap (p : SecIdx C t₁) :
    (p.1.1 : (Spec (CommRingCat.of S)).Opens).toScheme ⟶ (p.1.2 : (MC fM C).Opens).toScheme :=
  t₁.resLE (p.1.2 : (MC fM C).Opens) (p.1.1 : (Spec (CommRingCat.of S)).Opens) p.2

omit [Algebra C S] [Algebra 𝒪 S] [IsScalarTower 𝒪 C S] in

noncomputable def φW (p : SecIdx C t₁) : ringOf (fM := fM) C p.1.2 →+* Wring C t₁ p :=
  (Spec.preimage (p.1.1.2.isoSpec.inv ≫ cmap C t₁ p ≫ p.1.2.2.isoSpec.hom)).hom

omit [Algebra C S] [Algebra 𝒪 S] [IsScalarTower 𝒪 C S] in
theorem spec_φW (p : SecIdx C t₁) :
    Spec.map (CommRingCat.ofHom (φW C t₁ p)) = p.1.1.2.isoSpec.inv ≫ cmap C t₁ p ≫ p.1.2.2.isoSpec.hom := by
  simp [φW]

omit [Algebra C S] [Algebra 𝒪 S] [IsScalarTower 𝒪 C S] in
theorem spec_φW_chartι (p : SecIdx C t₁) :
    Spec.map (CommRingCat.ofHom (φW C t₁ p)) ≫ chartι C p.1.2 = Wι C t₁ p ≫ t₁ := by
  rw [spec_φW]; simp only [chartι, Wι, cmap, Category.assoc, Iso.hom_inv_id_assoc, Scheme.Hom.resLE_comp_ι]

omit [Algebra C S] [Algebra 𝒪 S] [IsScalarTower 𝒪 C S] in
theorem ringHom_eq_of_spec_map_eq {A B : Type} [CommRing A] [CommRing B] {f g : A →+* B}
    (h : Spec.map (CommRingCat.ofHom f) = Spec.map (CommRingCat.ofHom g)) : f = g :=
  congrArg CommRingCat.Hom.hom (Spec.map_injective h)

theorem φW_comp_algebraMap (ht₁ : t₁ ≫ πC fM C = Spec.map (CommRingCat.ofHom (algebraMap C S))) (p : SecIdx C t₁) :
    (φW C t₁ p).comp (algebraMap C (ringOf (fM := fM) C p.1.2)) = algebraMap C (Wring C t₁ p) := by
  apply ringHom_eq_of_spec_map_eq
  rw [CommRingCat.ofHom_comp, Spec.map_comp, spec_algebraMap_C, ← Category.assoc, spec_φW_chartι,
    Category.assoc, ht₁, IsScalarTower.algebraMap_eq C S (Wring C t₁ p), CommRingCat.ofHom_comp, Spec.map_comp,
    spec_algebraMap_W]

noncomputable def φWAlgHom (ht₁ : t₁ ≫ πC fM C = Spec.map (CommRingCat.ofHom (algebraMap C S))) (p : SecIdx C t₁) :
    ringOf (fM := fM) C p.1.2 →ₐ[C] Wring C t₁ p :=
  { toRingHom := φW C t₁ p
    commutes' := fun c => RingHom.congr_fun (φW_comp_algebraMap C t₁ ht₁ p) c }

@[scoped simp] theorem coe_φWAlgHom (ht₁ : t₁ ≫ πC fM C = Spec.map (CommRingCat.ofHom (algebraMap C S))) (p : SecIdx C t₁) :
    (φWAlgHom C t₁ ht₁ p : ringOf (fM := fM) C p.1.2 →+* Wring C t₁ p) = φW C t₁ p :=
  RingHom.ext fun _ => rfl

theorem isPullback_uof_of_ptFC_eq (hM : IsFineModuli Λ N n M fM ptF) (U : (MC fM C).affineOpens)
    {T : Type} [CommRing T] [Algebra C T] [Algebra 𝒪 T] [IsScalarTower 𝒪 C T]
    (ψ : ringOf (fM := fM) C U →ₐ[C] T) (v : FakeEllipticCurve.WithFullLevel Λ N n T)
    (hv : (ptFC C hM T v).1 = Spec.map (CommRingCat.ofHom (ψ : ringOf (fM := fM) C U →+* T)) ≫ chartι C U) :
    FakeEllipticCurve.WithFullLevel.IsPullback (ψ : ringOf (fM := fM) C U →+* T) (uof C hM U) v := by
  obtain ⟨w, hw⟩ := FakeEllipticCurve.WithFullLevel.exists_isPullback (ψ : ringOf (fM := fM) C U →+* T) (uof C hM U)
  have h1 := ptFC_pullback C hM _ _ ψ (uof C hM U) w hw
  rw [ptFC_uof C hM U, ← hv] at h1
  exact isPullback_of_iso_of_isPullback _ _ _ _ hw (ptFC_injective C hM _ _ _ (Subtype.ext h1.symm))

theorem isPullback_uof_of_isPullback_algebraMap (hM : IsFineModuli Λ N n M fM ptF)
    (u : FakeEllipticCurve.WithFullLevel Λ N n S) (ht₁ : (ptFC C hM S u).1 = t₁) (p : SecIdx C t₁)
    (w : FakeEllipticCurve.WithFullLevel Λ N n (Wring C t₁ p))
    (hw : FakeEllipticCurve.WithFullLevel.IsPullback (algebraMap S (Wring C t₁ p)) u w) :
    FakeEllipticCurve.WithFullLevel.IsPullback (φW C t₁ p) (uof C hM p.1.2) w := by
  have ht₁' : t₁ ≫ πC fM C = Spec.map (CommRingCat.ofHom (algebraMap C S)) := by rw [← ht₁, ptFC_snd]
  have key := ptFC_pullback C hM S (Wring C t₁ p) (IsScalarTower.toAlgHom C S (Wring C t₁ p)) u w hw
  rw [← coe_φWAlgHom C t₁ ht₁' p]
  refine isPullback_uof_of_ptFC_eq C hM p.1.2 (φWAlgHom C t₁ ht₁' p) w ?_
  rw [key, coe_φWAlgHom, spec_φW_chartι, ht₁]
  congr 1
  exact spec_algebraMap_W C t₁ p

end Sec

section S2Generic

variable (fM) in

structure ChartData where

  Z : (MC fM C).affineOpens → Scheme.{0}

  ζ : ∀ U : (MC fM C).affineOpens, Z U ⟶ Spec (CommRingCat.of (ringOf (fM := fM) C U))

  trans : ∀ {U V : (MC fM C).affineOpens}, V ≤ U → (Z V ⟶ Z U)

  trans_isPullback : ∀ {U V : (MC fM C).affineOpens} (hVU : V ≤ U),
    IsPullback (trans hVU) (ζ V) (ζ U) (Spec.map (CommRingCat.ofHom (resRing C hVU)))

  trans_id : ∀ U : (MC fM C).affineOpens, trans (le_refl U) = 𝟙 _

  trans_comp : ∀ {U V W : (MC fM C).affineOpens} (hWV : W ≤ V) (hVU : V ≤ U),
    trans hWV ≫ trans hVU = trans (hWV.trans hVU)

variable (D : ChartData fM C)

noncomputable def gluingData : Scheme.Cover.RelativeGluingData (MC fM C).directedAffineCover where
  functor :=
    { obj := fun U => D.Z U
      map := fun {V U} f => D.trans (leOfHom f)
      map_id := fun U => D.trans_id U
      map_comp := fun {W V U} f g => (D.trans_comp (leOfHom f) (leOfHom g)).symm }
  natTrans :=
    { app := fun U => D.ζ U ≫ U.2.isoSpec.inv
      naturality := by
        intro V U f
        simp only [Scheme.Cover.functorOfLocallyDirected_obj, Scheme.Cover.functorOfLocallyDirected_map]
        rw [← Category.assoc, (D.trans_isPullback (leOfHom f)).w, Category.assoc, Category.assoc]
        congr 1
        exact spec_resRing_isoSpec C (leOfHom f) }
  equifibered := by
    intro V U f
    simp only [Scheme.Cover.functorOfLocallyDirected_map]
    have sq : IsPullback (Spec.map (CommRingCat.ofHom (resRing C (leOfHom f)))) V.2.isoSpec.inv U.2.isoSpec.inv
        ((MC fM C).homOfLE (leOfHom f)) :=
      IsPullback.of_vert_isIso ⟨spec_resRing_isoSpec C (leOfHom f)⟩
    exact (D.trans_isPullback (leOfHom f)).paste_vert sq

noncomputable abbrev R : Scheme.{0} := (gluingData C D).glued

noncomputable abbrev qR : R C D ⟶ MC fM C := (gluingData C D).toBase

noncomputable abbrev ιR (U : (MC fM C).affineOpens) : D.Z U ⟶ R C D := (gluingData C D).cover.f U

theorem ιR_eq (U : (MC fM C).affineOpens) : ιR C D U = colimit.ι (gluingData C D).functor U := rfl

scoped instance ιR_isOpenImmersion (U : (MC fM C).affineOpens) : IsOpenImmersion (ιR C D U) :=
  (gluingData C D).cover.map_prop U

@[scoped simp] theorem trans_ιR {U V : (MC fM C).affineOpens} (hVU : V ≤ U) : D.trans hVU ≫ ιR C D U = ιR C D V := by
  rw [ιR_eq, ιR_eq]
  exact colimit.w (gluingData C D).functor (homOfLE hVU)

theorem ιR_qR (U : (MC fM C).affineOpens) : ιR C D U ≫ qR C D = D.ζ U ≫ chartι C U := by
  change colimit.ι (gluingData C D).functor U ≫ (gluingData C D).toBase = _
  rw [Scheme.Cover.RelativeGluingData.ι_toBase]
  change (D.ζ U ≫ U.2.isoSpec.inv) ≫ U.1.ι = _
  simp only [chartι, Category.assoc]

theorem ιR_isPullback' (U : (MC fM C).affineOpens) :
    IsPullback (D.ζ U ≫ U.2.isoSpec.inv) (ιR C D U) U.1.ι (qR C D) :=
  (gluingData C D).isPullback_natTrans_ι_toBase U

theorem ιR_isPullback (U : (MC fM C).affineOpens) :
    IsPullback (D.ζ U) (ιR C D U) (chartι C U) (qR C D) :=
  (ιR_isPullback' C D U).of_iso (Iso.refl _) U.2.isoSpec (Iso.refl _) (Iso.refl _)
    (by simp) (by simp) (by simp only [Iso.refl_hom, Category.comp_id, chartι, Iso.hom_inv_id_assoc]) (by simp)

theorem ιR_hom_ext {Y : Scheme.{0}} (f g : R C D ⟶ Y) (h : ∀ U : (MC fM C).affineOpens, ιR C D U ≫ f = ιR C D U ≫ g) :
    f = g :=
  Scheme.Cover.hom_ext (gluingData C D).cover f g h

theorem qR_of_forall (P : MorphismProperty Scheme.{0}) [IsZariskiLocalAtTarget P]
    (h : ∀ U : (MC fM C).affineOpens, P (D.ζ U)) : P (qR C D) := by
  apply IsZariskiLocalAtTarget.of_openCover (MC fM C).directedAffineCover
  intro U
  have sq := ((gluingData C D).isPullback_natTrans_ι_toBase U).flip
  have e : sq.isoPullback.hom ≫ pullback.snd _ _ = (gluingData C D).natTrans.app U :=
    sq.isoPullback_hom_snd
  have hP : P ((gluingData C D).natTrans.app U) := by
    change P (D.ζ U ≫ U.2.isoSpec.inv)
    exact (P.cancel_right_of_respectsIso _ _).mpr (h U)
  rw [← e] at hP
  exact (P.cancel_left_of_respectsIso _ _).mp hP

theorem etale_qR (h : ∀ U : (MC fM C).affineOpens, Etale (D.ζ U)) : Etale (qR C D) :=
  qR_of_forall C D @Etale h

theorem locallyOfFinitePresentation_qR (h : ∀ U : (MC fM C).affineOpens, LocallyOfFinitePresentation (D.ζ U)) :
    LocallyOfFinitePresentation (qR C D) :=
  qR_of_forall C D @LocallyOfFinitePresentation h

end S2Generic

section KeyGeneric

variable {S : Type} [CommRing S] (t₁ : Spec (CommRingCat.of S) ⟶ MC fM C)

omit C in

theorem spec_res_isoSpec_inv (X : Scheme.{0}) {U V : X.affineOpens} (h : V ≤ U) :
    Spec.map (X.presheaf.map (homOfLE h).op) ≫ U.2.isoSpec.inv = V.2.isoSpec.inv ≫ X.homOfLE h := by
  rw [← cancel_mono U.1.ι, Category.assoc, Category.assoc, IsAffineOpen.isoSpec_inv_ι, Scheme.homOfLE_ι,
    IsAffineOpen.isoSpec_inv_ι]
  exact IsAffineOpen.map_fromSpec U.2 V.2 (homOfLE h).op

omit C in

theorem homOfLE_isoSpec (X : Scheme.{0}) {U V : X.affineOpens} (h : V ≤ U) :
    X.homOfLE h ≫ U.2.isoSpec.hom = V.2.isoSpec.hom ≫ Spec.map (X.presheaf.map (homOfLE h).op) := by
  have key := spec_res_isoSpec_inv X h
  calc X.homOfLE h ≫ U.2.isoSpec.hom = V.2.isoSpec.hom ≫ (V.2.isoSpec.inv ≫ X.homOfLE h) ≫ U.2.isoSpec.hom := by
        simp
    _ = V.2.isoSpec.hom ≫ (Spec.map (X.presheaf.map (homOfLE h).op) ≫ U.2.isoSpec.inv) ≫ U.2.isoSpec.hom := by
        rw [key]
    _ = V.2.isoSpec.hom ≫ Spec.map (X.presheaf.map (homOfLE h).op) := by simp

noncomputable def ρW {k p : SecIdx C t₁} (h : k ≤ p) : Wring C t₁ p →+* Wring C t₁ k :=
  ((Spec (CommRingCat.of S)).presheaf.map (homOfLE h.1).op).hom

theorem homOfLE_isoSpec_W {k p : SecIdx C t₁} (h : k ≤ p) :
    (Spec (CommRingCat.of S)).homOfLE h.1 ≫ p.1.1.2.isoSpec.hom =
      k.1.1.2.isoSpec.hom ≫ Spec.map (CommRingCat.ofHom (ρW C t₁ h)) := by
  rw [homOfLE_isoSpec]; rfl

theorem spec_ρW_Wι {k p : SecIdx C t₁} (h : k ≤ p) :
    Spec.map (CommRingCat.ofHom (ρW C t₁ h)) ≫ Wι C t₁ p = Wι C t₁ k := by
  simp only [Wι]
  rw [← Category.assoc, show Spec.map (CommRingCat.ofHom (ρW C t₁ h)) ≫ p.1.1.2.isoSpec.inv =
    k.1.1.2.isoSpec.inv ≫ (Spec (CommRingCat.of S)).homOfLE h.1 from spec_res_isoSpec_inv _ h.1,
    Category.assoc, Scheme.homOfLE_ι]

theorem spec_φW_res {k p : SecIdx C t₁} (h : k ≤ p) :
    Spec.map (CommRingCat.ofHom (ρW C t₁ h)) ≫ Spec.map (CommRingCat.ofHom (φW C t₁ p)) =
      Spec.map (CommRingCat.ofHom (φW C t₁ k)) ≫ Spec.map (CommRingCat.ofHom (resRing C h.2)) := by
  rw [← cancel_mono (chartι C p.1.2), Category.assoc, Category.assoc, spec_φW_chartι, spec_resRing_comp_chartι,
    spec_φW_chartι, ← Category.assoc, spec_ρW_Wι]

theorem secCover_f (p : SecIdx C t₁) : (secCover C t₁).f p = (p.1.1 : (Spec (CommRingCat.of S)).Opens).ι := rfl

noncomputable def isoW (p : SecIdx C t₁) : (secCover C t₁).X p ≅ Spec (CommRingCat.of (Wring C t₁ p)) :=
  p.1.1.2.isoSpec

@[reassoc] theorem isoW_hom_Wι (p : SecIdx C t₁) : (isoW C t₁ p).hom ≫ Wι C t₁ p = (secCover C t₁).f p := by
  show p.1.1.2.isoSpec.hom ≫ Wι C t₁ p = (p.1.1 : (Spec (CommRingCat.of S)).Opens).ι
  rw [Wι, Iso.hom_inv_id_assoc]

noncomputable def transW {k p : SecIdx C t₁} (hkp : k ⟶ p) : (secCover C t₁).X k ⟶ (secCover C t₁).X p :=
  Scheme.Cover.trans (secCover C t₁) hkp

theorem transW_eq {k p : SecIdx C t₁} (hkp : k ⟶ p) : transW C t₁ hkp = Scheme.Cover.trans (secCover C t₁) hkp := rfl

@[reassoc] theorem transW_isoW {k p : SecIdx C t₁} (hkp : k ⟶ p) :
    transW C t₁ hkp ≫ (isoW C t₁ p).hom =
      (isoW C t₁ k).hom ≫ Spec.map (CommRingCat.ofHom (ρW C t₁ (leOfHom hkp))) :=
  homOfLE_isoSpec_W C t₁ (leOfHom hkp)

variable (D : ChartData fM C) {ZS : Scheme.{0}} (ζS : ZS ⟶ Spec (CommRingCat.of S))

noncomputable abbrev zsCover : ZS.OpenCover := (secCover C t₁).pullback₁ ζS

theorem zsCover_f (p : SecIdx C t₁) : (zsCover C t₁ ζS).f p = pullback.fst ζS ((secCover C t₁).f p) := rfl

noncomputable def transP {k p : SecIdx C t₁} (hkp : k ⟶ p) :
    pullback ζS ((secCover C t₁).f k) ⟶ pullback ζS ((secCover C t₁).f p) :=
  Scheme.Cover.trans (zsCover C t₁ ζS) hkp

theorem transP_eq {k p : SecIdx C t₁} (hkp : k ⟶ p) : transP C t₁ ζS hkp = Scheme.Cover.trans (zsCover C t₁ ζS) hkp :=
  rfl

@[reassoc] theorem transP_fst {k p : SecIdx C t₁} (hkp : k ⟶ p) :
    transP C t₁ ζS hkp ≫ pullback.fst ζS ((secCover C t₁).f p) = pullback.fst ζS ((secCover C t₁).f k) := by
  change pullback.lift _ _ _ ≫ pullback.fst _ _ = _
  rw [pullback.lift_fst, Category.comp_id]

@[reassoc] theorem transP_snd {k p : SecIdx C t₁} (hkp : k ⟶ p) :
    transP C t₁ ζS hkp ≫ pullback.snd ζS ((secCover C t₁).f p) =
      pullback.snd ζS ((secCover C t₁).f k) ≫ transW C t₁ hkp := by
  change pullback.lift _ _ _ ≫ pullback.snd _ _ = _
  rw [pullback.lift_snd]
  rfl

structure LocalComparison where

  ZW : SecIdx C t₁ → Scheme.{0}

  ιW : ∀ p, ZW p ⟶ ZS

  ζW : ∀ p, ZW p ⟶ Spec (CommRingCat.of (Wring C t₁ p))

  sq : ∀ p, IsPullback (ζW p) (ιW p) (Wι C t₁ p) ζS

  c : ∀ p, ZW p ⟶ D.Z p.1.2

  c_isPullback : ∀ p, IsPullback (c p) (ζW p) (D.ζ p.1.2) (Spec.map (CommRingCat.ofHom (φW C t₁ p)))

  compat : ∀ {k p : SecIdx C t₁} (h : k ≤ p) (r : ZW k ⟶ ZW p), r ≫ ιW p = ιW k → r ≫ c p = c k ≫ D.trans h.2

variable {D ζS} (L : LocalComparison C t₁ D ζS)

namespace LocalComparison

noncomputable def incl {k p : SecIdx C t₁} (h : k ≤ p) : L.ZW k ⟶ L.ZW p :=
  (L.sq p).lift (L.ζW k ≫ Spec.map (CommRingCat.ofHom (ρW C t₁ h))) (L.ιW k)
    (by rw [Category.assoc, spec_ρW_Wι, (L.sq k).w])

@[reassoc (attr := simp)] theorem incl_ιW {k p : SecIdx C t₁} (h : k ≤ p) : incl C t₁ L h ≫ L.ιW p = L.ιW k :=
  (L.sq p).lift_snd _ _ _

@[reassoc (attr := simp)] theorem incl_ζW {k p : SecIdx C t₁} (h : k ≤ p) :
    incl C t₁ L h ≫ L.ζW p = L.ζW k ≫ Spec.map (CommRingCat.ofHom (ρW C t₁ h)) :=
  (L.sq p).lift_fst _ _ _

@[reassoc] theorem incl_c {k p : SecIdx C t₁} (h : k ≤ p) : incl C t₁ L h ≫ L.c p = L.c k ≫ D.trans h.2 :=
  L.compat h _ (incl_ιW C t₁ L h)

noncomputable def eL (p : SecIdx C t₁) : pullback ζS ((secCover C t₁).f p) ⟶ L.ZW p :=
  (L.sq p).lift (pullback.snd _ _ ≫ (isoW C t₁ p).hom) (pullback.fst _ _)
    (by rw [pullback.condition, Category.assoc, isoW_hom_Wι])

@[reassoc (attr := simp)] theorem eL_ιW (p : SecIdx C t₁) : eL C t₁ L p ≫ L.ιW p = pullback.fst _ _ :=
  (L.sq p).lift_snd _ _ _

@[reassoc (attr := simp)] theorem eL_ζW (p : SecIdx C t₁) :
    eL C t₁ L p ≫ L.ζW p = pullback.snd _ _ ≫ (isoW C t₁ p).hom :=
  (L.sq p).lift_fst _ _ _

noncomputable def sL (p : SecIdx C t₁) : L.ZW p ⟶ pullback ζS ((secCover C t₁).f p) :=
  pullback.lift (L.ιW p) (L.ζW p ≫ (isoW C t₁ p).inv)
    (by rw [← (L.sq p).w, Category.assoc, ← isoW_hom_Wι, Iso.inv_hom_id_assoc])

@[reassoc (attr := simp)] theorem sL_fst (p : SecIdx C t₁) : sL C t₁ L p ≫ pullback.fst _ _ = L.ιW p :=
  pullback.lift_fst _ _ _

@[reassoc (attr := simp)] theorem sL_snd (p : SecIdx C t₁) :
    sL C t₁ L p ≫ pullback.snd _ _ = L.ζW p ≫ (isoW C t₁ p).inv :=
  pullback.lift_snd _ _ _

theorem sL_eL (p : SecIdx C t₁) : sL C t₁ L p ≫ eL C t₁ L p = 𝟙 _ := by
  apply (L.sq p).hom_ext
  · rw [Category.assoc, eL_ζW, Category.id_comp, sL_snd_assoc, Iso.inv_hom_id, Category.comp_id]
  · rw [Category.assoc, eL_ιW, Category.id_comp, sL_fst]

noncomputable def gL (p : SecIdx C t₁) : pullback ζS ((secCover C t₁).f p) ⟶ R C D :=
  eL C t₁ L p ≫ L.c p ≫ ιR C D p.1.2

theorem trans_eL {k p : SecIdx C t₁} (hkp : k ⟶ p) :
    transP C t₁ ζS hkp ≫ eL C t₁ L p = eL C t₁ L k ≫ incl C t₁ L (leOfHom hkp) := by
  apply (L.sq p).hom_ext
  · rw [Category.assoc, eL_ζW, Category.assoc, incl_ζW, eL_ζW_assoc, ← transW_isoW, transP_snd_assoc]
  · rw [Category.assoc, eL_ιW, Category.assoc, incl_ιW, eL_ιW, transP_fst]

theorem trans_gL {k p : SecIdx C t₁} (hkp : k ⟶ p) :
    transP C t₁ ζS hkp ≫ gL C t₁ L p = gL C t₁ L k := by
  rw [gL, gL, ← Category.assoc, trans_eL, Category.assoc, incl_c_assoc, trans_ιR]

noncomputable def kappa : ZS ⟶ R C D :=
  (zsCover C t₁ ζS).glueMorphismsOfLocallyDirected (gL C t₁ L) (fun hkp => trans_gL C t₁ L hkp)

theorem f_kappa (p : SecIdx C t₁) : (zsCover C t₁ ζS).f p ≫ kappa C t₁ L = gL C t₁ L p :=
  (zsCover C t₁ ζS).map_glueMorphismsOfLocallyDirected _ _ p

@[reassoc] theorem fst_kappa (p : SecIdx C t₁) :
    pullback.fst ζS ((secCover C t₁).f p) ≫ kappa C t₁ L = gL C t₁ L p :=
  f_kappa C t₁ L p

theorem ιW_kappa (p : SecIdx C t₁) : L.ιW p ≫ kappa C t₁ L = L.c p ≫ ιR C D p.1.2 := by
  rw [← sL_fst C t₁ L p, Category.assoc, fst_kappa, gL, ← Category.assoc, sL_eL, Category.id_comp]

theorem kappa_qR : kappa C t₁ L ≫ qR C D = ζS ≫ t₁ := by
  apply Scheme.Cover.hom_ext (zsCover C t₁ ζS)
  intro p
  change pullback.fst ζS ((secCover C t₁).f p) ≫ _ = pullback.fst ζS ((secCover C t₁).f p) ≫ _
  rw [fst_kappa_assoc, gL, Category.assoc, Category.assoc, ιR_qR, ← Category.assoc (L.c p),
    (L.c_isPullback p).w, Category.assoc, spec_φW_chartι, eL_ζW_assoc, isoW_hom_Wι_assoc, pullback.condition_assoc]

theorem kappa_unique (κ' : ZS ⟶ R C D) (h : ∀ p, L.ιW p ≫ κ' = L.c p ≫ ιR C D p.1.2) : κ' = kappa C t₁ L := by
  apply Scheme.Cover.hom_ext (zsCover C t₁ ζS)
  intro p
  change pullback.fst ζS ((secCover C t₁).f p) ≫ _ = pullback.fst ζS ((secCover C t₁).f p) ≫ _
  rw [fst_kappa, gL, ← h p, ← eL_ιW C t₁ L p, Category.assoc]

section Cartesian

variable {T : Scheme.{0}} (a : T ⟶ Spec (CommRingCat.of S)) (b : T ⟶ R C D) (hab : b ≫ qR C D = a ≫ t₁)

noncomputable abbrev tCover : T.OpenCover := (secCover C t₁).pullback₁ a

noncomputable def transT {k p : SecIdx C t₁} (hkp : k ⟶ p) :
    pullback a ((secCover C t₁).f k) ⟶ pullback a ((secCover C t₁).f p) :=
  Scheme.Cover.trans (tCover C t₁ a) hkp

@[reassoc] theorem transT_fst {k p : SecIdx C t₁} (hkp : k ⟶ p) :
    transT C t₁ a hkp ≫ pullback.fst a ((secCover C t₁).f p) = pullback.fst a ((secCover C t₁).f k) := by
  change pullback.lift _ _ _ ≫ pullback.fst _ _ = _
  rw [pullback.lift_fst, Category.comp_id]

@[reassoc] theorem transT_snd {k p : SecIdx C t₁} (hkp : k ⟶ p) :
    transT C t₁ a hkp ≫ pullback.snd a ((secCover C t₁).f p) =
      pullback.snd a ((secCover C t₁).f k) ≫ transW C t₁ hkp := by
  change pullback.lift _ _ _ ≫ pullback.snd _ _ = _
  rw [pullback.lift_snd]
  rfl

noncomputable def ellT (p : SecIdx C t₁) : pullback a ((secCover C t₁).f p) ⟶ D.Z p.1.2 :=
  (ιR_isPullback C D p.1.2).lift
    (pullback.snd a ((secCover C t₁).f p) ≫ (isoW C t₁ p).hom ≫ Spec.map (CommRingCat.ofHom (φW C t₁ p)))
    (pullback.fst a ((secCover C t₁).f p) ≫ b)
    (by rw [Category.assoc, Category.assoc, spec_φW_chartι, isoW_hom_Wι_assoc, ← pullback.condition_assoc,
      Category.assoc, hab])

@[reassoc] theorem ellT_ζ (p : SecIdx C t₁) :
    ellT C t₁ a b hab p ≫ D.ζ p.1.2 =
      pullback.snd a ((secCover C t₁).f p) ≫ (isoW C t₁ p).hom ≫ Spec.map (CommRingCat.ofHom (φW C t₁ p)) :=
  (ιR_isPullback C D p.1.2).lift_fst _ _ _

@[reassoc] theorem ellT_ιR (p : SecIdx C t₁) :
    ellT C t₁ a b hab p ≫ ιR C D p.1.2 = pullback.fst a ((secCover C t₁).f p) ≫ b :=
  (ιR_isPullback C D p.1.2).lift_snd _ _ _

noncomputable def nT (p : SecIdx C t₁) : pullback a ((secCover C t₁).f p) ⟶ L.ZW p :=
  (L.c_isPullback p).lift (ellT C t₁ a b hab p) (pullback.snd a ((secCover C t₁).f p) ≫ (isoW C t₁ p).hom)
    (by rw [ellT_ζ, Category.assoc])

@[reassoc] theorem nT_c (p : SecIdx C t₁) : nT C t₁ L a b hab p ≫ L.c p = ellT C t₁ a b hab p :=
  (L.c_isPullback p).lift_fst _ _ _

@[reassoc] theorem nT_ζW (p : SecIdx C t₁) :
    nT C t₁ L a b hab p ≫ L.ζW p = pullback.snd a ((secCover C t₁).f p) ≫ (isoW C t₁ p).hom :=
  (L.c_isPullback p).lift_snd _ _ _

noncomputable def mT (p : SecIdx C t₁) : pullback a ((secCover C t₁).f p) ⟶ ZS :=
  nT C t₁ L a b hab p ≫ L.ιW p

theorem mT_ζS (p : SecIdx C t₁) : mT C t₁ L a b hab p ≫ ζS = pullback.fst a ((secCover C t₁).f p) ≫ a := by
  rw [mT, Category.assoc, ← (L.sq p).w, nT_ζW_assoc, isoW_hom_Wι, pullback.condition]

theorem mT_kappa (p : SecIdx C t₁) : mT C t₁ L a b hab p ≫ kappa C t₁ L = pullback.fst a ((secCover C t₁).f p) ≫ b := by
  rw [mT, Category.assoc, ιW_kappa, nT_c_assoc, ellT_ιR]

theorem transT_nT {k p : SecIdx C t₁} (hkp : k ⟶ p) :
    transT C t₁ a hkp ≫ nT C t₁ L a b hab p = nT C t₁ L a b hab k ≫ incl C t₁ L (leOfHom hkp) := by
  apply (L.c_isPullback p).hom_ext
  ·
    simp only [Category.assoc]
    rw [nT_c, incl_c, nT_c_assoc]
    apply (ιR_isPullback C D p.1.2).hom_ext
    · simp only [Category.assoc]
      rw [ellT_ζ, (D.trans_isPullback (leOfHom hkp).2).w, ellT_ζ_assoc, ← spec_φW_res C t₁ (leOfHom hkp),
        ← transW_isoW_assoc, transT_snd_assoc]
    · simp only [Category.assoc]
      rw [ellT_ιR, trans_ιR, ellT_ιR, transT_fst_assoc]
  · simp only [Category.assoc]
    rw [nT_ζW, incl_ζW, nT_ζW_assoc, ← transW_isoW, transT_snd_assoc]

theorem transT_mT {k p : SecIdx C t₁} (hkp : k ⟶ p) :
    transT C t₁ a hkp ≫ mT C t₁ L a b hab p = mT C t₁ L a b hab k := by
  rw [mT, mT, ← Category.assoc, transT_nT, Category.assoc, incl_ιW]

noncomputable def liftT : T ⟶ ZS :=
  (tCover C t₁ a).glueMorphismsOfLocallyDirected (mT C t₁ L a b hab) (fun hkp => transT_mT C t₁ L a b hab hkp)

@[reassoc] theorem fst_liftT (p : SecIdx C t₁) :
    pullback.fst a ((secCover C t₁).f p) ≫ liftT C t₁ L a b hab = mT C t₁ L a b hab p :=
  (tCover C t₁ a).map_glueMorphismsOfLocallyDirected _ _ p

theorem liftT_kappa : liftT C t₁ L a b hab ≫ kappa C t₁ L = b := by
  apply Scheme.Cover.hom_ext (tCover C t₁ a)
  intro p
  change pullback.fst a ((secCover C t₁).f p) ≫ _ = pullback.fst a ((secCover C t₁).f p) ≫ _
  rw [fst_liftT_assoc, mT_kappa]

theorem liftT_ζS : liftT C t₁ L a b hab ≫ ζS = a := by
  apply Scheme.Cover.hom_ext (tCover C t₁ a)
  intro p
  change pullback.fst a ((secCover C t₁).f p) ≫ _ = pullback.fst a ((secCover C t₁).f p) ≫ _
  rw [fst_liftT_assoc, mT_ζS]

theorem liftT_unique (m : T ⟶ ZS) (hm₁ : m ≫ kappa C t₁ L = b) (hm₂ : m ≫ ζS = a) : m = liftT C t₁ L a b hab := by
  apply Scheme.Cover.hom_ext (tCover C t₁ a)
  intro p
  change pullback.fst a ((secCover C t₁).f p) ≫ _ = pullback.fst a ((secCover C t₁).f p) ≫ _
  rw [fst_liftT, mT]

  set n' : pullback a ((secCover C t₁).f p) ⟶ L.ZW p :=
    (L.sq p).lift (pullback.snd a ((secCover C t₁).f p) ≫ (isoW C t₁ p).hom) (pullback.fst a ((secCover C t₁).f p) ≫ m)
      (by rw [Category.assoc, isoW_hom_Wι, Category.assoc, hm₂, pullback.condition]) with hn'
  have hn'ι : n' ≫ L.ιW p = pullback.fst a ((secCover C t₁).f p) ≫ m := (L.sq p).lift_snd _ _ _
  have hn'ζ : n' ≫ L.ζW p = pullback.snd a ((secCover C t₁).f p) ≫ (isoW C t₁ p).hom := (L.sq p).lift_fst _ _ _
  rw [← hn'ι]
  congr 1
  apply (L.c_isPullback p).hom_ext
  · rw [nT_c]
    apply (ιR_isPullback C D p.1.2).hom_ext
    · rw [Category.assoc, (L.c_isPullback p).w, ← Category.assoc, hn'ζ, ellT_ζ, Category.assoc]
    · rw [Category.assoc, ← ιW_kappa, ← Category.assoc, hn'ι, Category.assoc, hm₁, ellT_ιR]
  · rw [hn'ζ, nT_ζW]

end Cartesian

theorem isPullback_kappa : IsPullback (kappa C t₁ L) ζS (qR C D) t₁ := by
  refine ⟨⟨kappa_qR C t₁ L⟩, ⟨Limits.PullbackCone.IsLimit.mk _ (fun s => liftT C t₁ L s.snd s.fst s.condition)
    (fun s => liftT_kappa C t₁ L s.snd s.fst s.condition) (fun s => liftT_ζS C t₁ L s.snd s.fst s.condition) ?_⟩⟩
  intro s m hm₁ hm₂
  exact liftT_unique C t₁ L s.snd s.fst s.condition m hm₁ hm₂

end LocalComparison

theorem exists_hom_isPullback_of_localComparison :
    ∃ κ : ZS ⟶ R C D,
      (∀ p, L.ιW p ≫ κ = L.c p ≫ ιR C D p.1.2) ∧ κ ≫ qR C D = ζS ≫ t₁ ∧ IsPullback κ ζS (qR C D) t₁ ∧
      ∀ κ' : ZS ⟶ R C D, (∀ p, L.ιW p ≫ κ' = L.c p ≫ ιR C D p.1.2) → κ' = κ :=
  ⟨LocalComparison.kappa C t₁ L, LocalComparison.ιW_kappa C t₁ L, LocalComparison.kappa_qR C t₁ L,
    LocalComparison.isPullback_kappa C t₁ L, LocalComparison.kappa_unique C t₁ L⟩

end KeyGeneric

end RelRepGlue
p2m_reactivate "P2MW.S_CerednikDrinfeld_QM_IsFineModuli_exists_locallyOfFinitePresentation_forall_representsOn_hom_isPullback_of_forall_withFullLevel.RelRepGlue"

end
p2m_reactivate "P2MW.S_CerednikDrinfeld_QM_IsFineModuli_exists_locallyOfFinitePresentation_forall_representsOn_hom_isPullback_of_forall_withFullLevel.RelRepGlue"

set_option autoImplicit false

open scoped TensorProduct Quaternion NumberField
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry QuaternionAlgebra CerednikDrinfeld CerednikDrinfeld.QM NeronModelInfra GoodReductionJacobian

noncomputable section

namespace RelRepGlue

variable {N : ℕ} {𝒪 : Type} [CommRing 𝒪]
  {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} {n : ℕ} {M : Scheme.{0}} {fM : M ⟶ Spec (CommRingCat.of 𝒪)}
  {ptF : ∀ (S : Type) [CommRing S] (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of 𝒪)),
    FakeEllipticCurve.WithFullLevel Λ N n S → SchemeHomOver s fM}
  (C : Type) [CommRing C] [Algebra 𝒪 C]

section PairData

variable (r d : ℕ)

structure PairDatum {S : Type} [CommRing S] (E A : FakeEllipticCurve Λ N S) where
  X : Scheme.{0}
  ξ : X ⟶ Spec (CommRingCat.of S)
  lfp : LocallyOfFinitePresentation ξ
  pt : FakeEllipticCurve.IsogenyPair.PtFamily r d E A ξ
  rep : FakeEllipticCurve.IsogenyPair.RepresentsOn r d E A ξ pt

def HLoc (𝔄 : FakeEllipticCurve Λ N C) : Prop :=
  ∀ (S : Type) [CommRing S] [Algebra C S] [Algebra 𝒪 S] [IsScalarTower 𝒪 C S]
    (u : FakeEllipticCurve.WithFullLevel Λ N n S)
    (A : FakeEllipticCurve Λ N S) (gA : A.A ⟶ 𝔄.A) (_ : FakeEllipticCurve.IsPullbackVia (algebraMap C S) 𝔄 A gA),
    ∃ (X : Scheme.{0}) (ξ : X ⟶ Spec (CommRingCat.of S)) (_ : LocallyOfFinitePresentation ξ)
      (pt : FakeEllipticCurve.IsogenyPair.PtFamily r d u.1 A ξ),
      FakeEllipticCurve.IsogenyPair.RepresentsOn r d u.1 A ξ pt

variable {r d}

theorem nonempty_pairDatum {𝔄 : FakeEllipticCurve Λ N C} (hloc : HLoc (𝒪 := 𝒪) (n := n) C r d 𝔄)
    {S : Type} [CommRing S] [Algebra C S] [Algebra 𝒪 S] [IsScalarTower 𝒪 C S]
    (u : FakeEllipticCurve.WithFullLevel Λ N n S)
    (A : FakeEllipticCurve Λ N S) (gA : A.A ⟶ 𝔄.A) (hgA : FakeEllipticCurve.IsPullbackVia (algebraMap C S) 𝔄 A gA) :
    Nonempty (PairDatum (N := N) (Λ := Λ) r d u.1 A) := by
  obtain ⟨X, ξ, hξ, pt, h⟩ := hloc S u A gA hgA
  exact ⟨⟨X, ξ, hξ, pt, h⟩⟩

def datumOf {𝔄 : FakeEllipticCurve Λ N C} (hloc : HLoc (𝒪 := 𝒪) (n := n) C r d 𝔄)
    {S : Type} [CommRing S] [Algebra C S] [Algebra 𝒪 S] [IsScalarTower 𝒪 C S]
    (u : FakeEllipticCurve.WithFullLevel Λ N n S)
    (A : FakeEllipticCurve Λ N S) (gA : A.A ⟶ 𝔄.A) (hgA : FakeEllipticCurve.IsPullbackVia (algebraMap C S) 𝔄 A gA) :
    PairDatum (N := N) (Λ := Λ) r d u.1 A :=
  (nonempty_pairDatum C hloc u A gA hgA).some

theorem PairDatum.pt_congr {S : Type} [CommRing S] {E A : FakeEllipticCurve Λ N S} (D : PairDatum (N := N) (Λ := Λ) r d E A)
    {T : Type} [CommRing T] [Algebra S T] (E' A' : FakeEllipticCurve Λ N T)
    {gE₁ gE₂ : E'.A ⟶ E.A} (hE : gE₁ = gE₂)
    (h₁ : FakeEllipticCurve.IsPullbackVia (algebraMap S T) E E' gE₁) (h₂ : FakeEllipticCurve.IsPullbackVia (algebraMap S T) E E' gE₂)
    {gA₁ gA₂ : A'.A ⟶ A.A} (hA : gA₁ = gA₂)
    (k₁ : FakeEllipticCurve.IsPullbackVia (algebraMap S T) A A' gA₁) (k₂ : FakeEllipticCurve.IsPullbackVia (algebraMap S T) A A' gA₂)
    (φ : E'.A ⟶ A'.A) (φ' : A'.A ⟶ E'.A) (hφ : φ ≫ A'.f = E'.f)
    (hp : FakeEllipticCurve.IsIsogenyPair (r ^ d) E' A' φ φ') (hl : FakeEllipticCurve.PreservesLevel E' A' φ hφ) :
    (D.pt T E' A' gE₁ h₁ gA₁ k₁ φ φ' hφ hp hl).1 = (D.pt T E' A' gE₂ h₂ gA₂ k₂ φ φ' hφ hp hl).1 := by
  subst hE hA; rfl

theorem PairDatum.pt_congr' {S : Type} [CommRing S] {E A : FakeEllipticCurve Λ N S} (D : PairDatum (N := N) (Λ := Λ) r d E A)
    {T : Type} [CommRing T] (i₁ i₂ : Algebra S T) (hi : i₁ = i₂) (E' A' : FakeEllipticCurve Λ N T)
    {gE₁ gE₂ : E'.A ⟶ E.A} (hE : gE₁ = gE₂)
    (h₁ : FakeEllipticCurve.IsPullbackVia (@algebraMap S T _ _ i₁) E E' gE₁)
    (h₂ : FakeEllipticCurve.IsPullbackVia (@algebraMap S T _ _ i₂) E E' gE₂)
    {gA₁ gA₂ : A'.A ⟶ A.A} (hA : gA₁ = gA₂)
    (k₁ : FakeEllipticCurve.IsPullbackVia (@algebraMap S T _ _ i₁) A A' gA₁)
    (k₂ : FakeEllipticCurve.IsPullbackVia (@algebraMap S T _ _ i₂) A A' gA₂)
    (φ : E'.A ⟶ A'.A) (φ' : A'.A ⟶ E'.A) (hφ : φ ≫ A'.f = E'.f)
    (hp : FakeEllipticCurve.IsIsogenyPair (r ^ d) E' A' φ φ') (hl : FakeEllipticCurve.PreservesLevel E' A' φ hφ) :
    (@PairDatum.pt _ _ _ _ _ _ _ _ _ _ D T _ i₁ E' A' gE₁ h₁ gA₁ k₁ φ φ' hφ hp hl).1 =
      (@PairDatum.pt _ _ _ _ _ _ _ _ _ _ D T _ i₂ E' A' gE₂ h₂ gA₂ k₂ φ φ' hφ hp hl).1 := by
  subst hi hE hA; rfl

end PairData
p2m_reactivate "P2MW.S_CerednikDrinfeld_QM_IsFineModuli_exists_locallyOfFinitePresentation_forall_representsOn_hom_isPullback_of_forall_withFullLevel.RelRepGlue"

theorem presheaf_map_hom_eq_id {U : (MC fM C).Opens} (φ : U ⟶ U) : ((MC fM C).presheaf.map φ.op).hom = RingHom.id _ := by
  obtain rfl : φ = 𝟙 _ := Subsingleton.elim _ _
  rw [op_id, (MC fM C).presheaf.map_id]; rfl

theorem presheaf_map_hom_comp {U V W : (MC fM C).Opens} (φ : W ⟶ V) (ψ : V ⟶ U) (χ : W ⟶ U) :
    ((MC fM C).presheaf.map φ.op).hom.comp ((MC fM C).presheaf.map ψ.op).hom = ((MC fM C).presheaf.map χ.op).hom := by
  obtain rfl : χ = φ ≫ ψ := Subsingleton.elim _ _
  rw [op_comp, (MC fM C).presheaf.map_comp]; rfl

theorem resRing_refl (U : (MC fM C).affineOpens) : resRing (fM := fM) C (le_refl U) = RingHom.id (ringOf C U) :=
  presheaf_map_hom_eq_id C _

theorem resRing_comp {U V W : (MC fM C).affineOpens} (hWV : W ≤ V) (hVU : V ≤ U) :
    (resRing (fM := fM) C hWV).comp (resRing C hVU) = resRing C (hWV.trans hVU) :=
  presheaf_map_hom_comp C _ _ _

section ConstCurve

variable (𝔄 : FakeEllipticCurve Λ N C)

theorem exists_pullback_const (S : Type) [CommRing S] [Algebra C S] :
    ∃ (A : FakeEllipticCurve Λ N S) (g : A.A ⟶ 𝔄.A), FakeEllipticCurve.IsPullbackVia (algebraMap C S) 𝔄 A g ∧
      ∀ {T : Scheme.{0}} (t' : T ⟶ Spec (CommRingCat.of S)) (P : SchemeHomOver t' A.f),
        (∃ P₀ : T ⟶ 𝔄.C, P₀ ≫ 𝔄.lev = P.1 ≫ g) → FactorsThrough A.lev P := by
  obtain ⟨A, g, hg, hmul, hact, hlev, hlev'⟩ := FakeEllipticCurve.exists_isPullback_levelIff (algebraMap C S) 𝔄
  exact ⟨A, g, ⟨hg, hmul, hact, hlev⟩, hlev'⟩

def Aof (U : (MC fM C).affineOpens) : FakeEllipticCurve Λ N (ringOf (fM := fM) C U) :=
  (exists_pullback_const C 𝔄 (ringOf (fM := fM) C U)).choose

def gAof (U : (MC fM C).affineOpens) : (Aof (fM := fM) C 𝔄 U).A ⟶ 𝔄.A :=
  (exists_pullback_const C 𝔄 (ringOf (fM := fM) C U)).choose_spec.choose

theorem gAof_spec (U : (MC fM C).affineOpens) :
    FakeEllipticCurve.IsPullbackVia (algebraMap C (ringOf (fM := fM) C U)) 𝔄 (Aof C 𝔄 U) (gAof C 𝔄 U) ∧
      ∀ {T : Scheme.{0}} (t' : T ⟶ Spec (CommRingCat.of (ringOf (fM := fM) C U))) (P : SchemeHomOver t' (Aof C 𝔄 U).f),
        (∃ P₀ : T ⟶ 𝔄.C, P₀ ≫ 𝔄.lev = P.1 ≫ gAof C 𝔄 U) → FactorsThrough (Aof C 𝔄 U).lev P :=
  (exists_pullback_const C 𝔄 (ringOf (fM := fM) C U)).choose_spec.choose_spec

theorem existsUnique_gA {U V : (MC fM C).affineOpens} (hVU : V ≤ U) :
    ∃ g : (Aof (fM := fM) C 𝔄 V).A ⟶ (Aof (fM := fM) C 𝔄 U).A,
      g ≫ gAof C 𝔄 U = gAof C 𝔄 V ∧
      g ≫ (Aof C 𝔄 U).f = (Aof C 𝔄 V).f ≫ Spec.map (CommRingCat.ofHom (resRing C hVU)) ∧
      (∀ k : (Aof (fM := fM) C 𝔄 V).A ⟶ (Aof (fM := fM) C 𝔄 U).A, k ≫ gAof C 𝔄 U = gAof C 𝔄 V →
        k ≫ (Aof C 𝔄 U).f = (Aof C 𝔄 V).f ≫ Spec.map (CommRingCat.ofHom (resRing C hVU)) → k = g) ∧
      FakeEllipticCurve.IsPullbackVia (resRing C hVU) (Aof C 𝔄 U) (Aof C 𝔄 V) g :=
  FakeEllipticCurve.IsPullbackVia.exists_comp_eq_and_isPullbackVia_of_comp_eq
    (algebraMap C (ringOf (fM := fM) C U)) (resRing C hVU) (algebraMap C (ringOf (fM := fM) C V))
    (resRing_comp_algebraMap C hVU) 𝔄 (Aof C 𝔄 U) (Aof C 𝔄 V)
    (gAof C 𝔄 U) (gAof_spec C 𝔄 U).1 (fun t' P h => (gAof_spec C 𝔄 U).2 t' P h)
    (gAof C 𝔄 V) (gAof_spec C 𝔄 V).1

def gA {U V : (MC fM C).affineOpens} (hVU : V ≤ U) : (Aof (fM := fM) C 𝔄 V).A ⟶ (Aof (fM := fM) C 𝔄 U).A :=
  (existsUnique_gA C 𝔄 hVU).choose

theorem gA_comp_gAof {U V : (MC fM C).affineOpens} (hVU : V ≤ U) : gA C 𝔄 hVU ≫ gAof C 𝔄 U = gAof C 𝔄 V :=
  (existsUnique_gA C 𝔄 hVU).choose_spec.1

theorem gA_over {U V : (MC fM C).affineOpens} (hVU : V ≤ U) :
    gA C 𝔄 hVU ≫ (Aof C 𝔄 U).f = (Aof C 𝔄 V).f ≫ Spec.map (CommRingCat.ofHom (resRing C hVU)) :=
  (existsUnique_gA C 𝔄 hVU).choose_spec.2.1

theorem gA_unique {U V : (MC fM C).affineOpens} (hVU : V ≤ U)
    (k : (Aof (fM := fM) C 𝔄 V).A ⟶ (Aof (fM := fM) C 𝔄 U).A) (h1 : k ≫ gAof C 𝔄 U = gAof C 𝔄 V)
    (h2 : k ≫ (Aof C 𝔄 U).f = (Aof C 𝔄 V).f ≫ Spec.map (CommRingCat.ofHom (resRing C hVU))) : k = gA C 𝔄 hVU :=
  (existsUnique_gA C 𝔄 hVU).choose_spec.2.2.1 k h1 h2

theorem gA_isPullbackVia {U V : (MC fM C).affineOpens} (hVU : V ≤ U) :
    FakeEllipticCurve.IsPullbackVia (resRing C hVU) (Aof C 𝔄 U) (Aof C 𝔄 V) (gA C 𝔄 hVU) :=
  (existsUnique_gA C 𝔄 hVU).choose_spec.2.2.2

theorem gA_refl (U : (MC fM C).affineOpens) : gA C 𝔄 (le_refl U) = 𝟙 _ := by
  refine (gA_unique C 𝔄 (le_refl U) (𝟙 _) (Category.id_comp _) ?_).symm
  rw [resRing_refl, Category.id_comp]
  change (Aof C 𝔄 U).f = (Aof C 𝔄 U).f ≫ Spec.map (𝟙 _)
  rw [Spec.map_id, Category.comp_id]

theorem gA_comp {U V W : (MC fM C).affineOpens} (hWV : W ≤ V) (hVU : V ≤ U) :
    gA C 𝔄 hWV ≫ gA C 𝔄 hVU = gA C 𝔄 (hWV.trans hVU) := by
  refine gA_unique C 𝔄 (hWV.trans hVU) _ ?_ ?_
  · rw [Category.assoc, gA_comp_gAof, gA_comp_gAof]
  · rw [Category.assoc, gA_over, ← Category.assoc, gA_over, Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp,
      resRing_comp]

end ConstCurve
p2m_reactivate "P2MW.S_CerednikDrinfeld_QM_IsFineModuli_exists_locallyOfFinitePresentation_forall_representsOn_hom_isPullback_of_forall_withFullLevel.RelRepGlue"

section Universal

theorem isPullbackVia_comp {N' : ℕ} {S S' S'' : Type} [CommRing S] [CommRing S'] [CommRing S'']
    (φ : S →+* S') (ψ : S' →+* S'')
    (E : FakeEllipticCurve Λ N' S) (E' : FakeEllipticCurve Λ N' S') (E'' : FakeEllipticCurve Λ N' S'')
    (g' : E'.A ⟶ E.A) (g'' : E''.A ⟶ E'.A)
    (h' : FakeEllipticCurve.IsPullbackVia φ E E' g') (h'' : FakeEllipticCurve.IsPullbackVia ψ E' E'' g'') :
    FakeEllipticCurve.IsPullbackVia (ψ.comp φ) E E'' (g'' ≫ g') := by
  obtain ⟨hg', mul', act', lev'⟩ := h'
  obtain ⟨hg'', mul'', act'', lev''⟩ := h''
  have hSpec : Spec.map (CommRingCat.ofHom (ψ.comp φ)) =
      Spec.map (CommRingCat.ofHom ψ) ≫ Spec.map (CommRingCat.ofHom φ) := by
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
  have sq : IsPullback (g'' ≫ g') E''.f E.f (Spec.map (CommRingCat.ofHom (ψ.comp φ))) := by
    rw [hSpec]; exact hg''.paste_horiz hg'
  refine ⟨sq, ?_, ?_, ?_⟩
  · intro T t P Q
    rw [← Category.assoc, mul'' t P Q, mul' (t ≫ Spec.map (CommRingCat.ofHom ψ))]
    exact mul_val_congr E.L (by rw [hSpec, Category.assoc]) _ _ _ _ (by simp [Category.assoc]) (by simp [Category.assoc])
  · intro x
    rw [← Category.assoc, act'' x, Category.assoc, act' x, Category.assoc]
  · intro T t P hP
    obtain ⟨P₀, hP₀⟩ := lev'' t P hP
    obtain ⟨P₁, hP₁⟩ := lev' (t ≫ Spec.map (CommRingCat.ofHom ψ)) ⟨P.1 ≫ g'', by
      rw [Category.assoc, hg''.w, ← Category.assoc, P.2]⟩ ⟨P₀, hP₀⟩
    exact ⟨P₁, by rw [hP₁, Category.assoc]⟩

theorem isPullbackVia_id {N' : ℕ} {S : Type} [CommRing S] (E : FakeEllipticCurve Λ N' S) :
    FakeEllipticCurve.IsPullbackVia (RingHom.id S) E E (𝟙 E.A) := by
  have hS : Spec.map (CommRingCat.ofHom (RingHom.id S)) = 𝟙 _ := by
    rw [CommRingCat.ofHom_id]; exact Spec.map_id _
  have sq : IsPullback (𝟙 E.A) E.f E.f (Spec.map (CommRingCat.ofHom (RingHom.id S))) := by
    rw [hS]; exact IsPullback.of_horiz_isIso ⟨by simp⟩
  refine ⟨sq, ?_, ?_, ?_⟩
  · intro T t P Q
    rw [Category.comp_id]
    exact mul_val_congr E.L (by rw [hS, Category.comp_id]) _ _ _ _ (by simp) (by simp)
  · intro x; simp
  · intro T t P hP
    obtain ⟨P₀, h⟩ := hP
    exact ⟨P₀, by rw [h, Category.comp_id]⟩

theorem isPullbackVia_congr {N' : ℕ} {S S' : Type} [CommRing S] [CommRing S'] {φ ψ : S →+* S'} (h : φ = ψ)
    (E : FakeEllipticCurve Λ N' S) (E' : FakeEllipticCurve Λ N' S') (g : E'.A ⟶ E.A)
    (hg : FakeEllipticCurve.IsPullbackVia φ E E' g) : FakeEllipticCurve.IsPullbackVia ψ E E' g := by
  subst h; exact hg

def HRig (Λ : Submodule ℤ ℍ[ℚ, a, b]) (N n : ℕ) (C : Type) [CommRing C] : Prop :=
  ∀ (S : Type) [CommRing S] [Algebra C S] (u : FakeEllipticCurve.WithFullLevel Λ N n S)
    (e : u.1.A ≅ u.1.A) (he : e.hom ≫ u.1.f = u.1.f),
    (∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of S)) (P Q : SchemeHomOver t u.1.f),
      mapPt e.hom he (u.1.L.mul t P Q) = u.1.L.mul t (mapPt e.hom he P) (mapPt e.hom he Q)) →
    (∀ x : ↥Λ, u.1.act x ≫ e.hom = e.hom ≫ u.1.act x) →
    mapPt e.hom he u.2.P = u.2.P → e = Iso.refl u.1.A

theorem comparison_unique (hrig : HRig Λ N n C) {S S' : Type} [CommRing S] [CommRing S'] [Algebra C S'] (φ : S →+* S')
    (u : FakeEllipticCurve.WithFullLevel Λ N n S) (u' : FakeEllipticCurve.WithFullLevel Λ N n S')
    (g₁ g₂ : u'.1.A ⟶ u.1.A)
    (h₁ : FakeEllipticCurve.IsPullbackVia φ u.1 u'.1 g₁) (hP₁ : (u'.2.P).1 ≫ g₁ = Spec.map (CommRingCat.ofHom φ) ≫ (u.2.P).1)
    (h₂ : FakeEllipticCurve.IsPullbackVia φ u.1 u'.1 g₂) (hP₂ : (u'.2.P).1 ≫ g₂ = Spec.map (CommRingCat.ofHom φ) ≫ (u.2.P).1) :
    g₁ = g₂ := by
  obtain ⟨hg₁, mul₁, act₁, -⟩ := h₁
  obtain ⟨hg₂, mul₂, act₂, -⟩ := h₂
  set θ : u'.1.A ⟶ u'.1.A := hg₂.lift g₁ u'.1.f hg₁.w with hθdef
  have hθ₁ : θ ≫ g₂ = g₁ := hg₂.lift_fst _ _ _
  have hθ₂ : θ ≫ u'.1.f = u'.1.f := hg₂.lift_snd _ _ _
  set θ' : u'.1.A ⟶ u'.1.A := hg₁.lift g₂ u'.1.f hg₂.w with hθ'def
  have hθ'₁ : θ' ≫ g₁ = g₂ := hg₁.lift_fst _ _ _
  have hθ'₂ : θ' ≫ u'.1.f = u'.1.f := hg₁.lift_snd _ _ _
  have h1 : θ ≫ θ' = 𝟙 _ :=
    hg₁.hom_ext (by rw [Category.assoc, hθ'₁, hθ₁, Category.id_comp]) (by rw [Category.assoc, hθ'₂, hθ₂, Category.id_comp])
  have h2 : θ' ≫ θ = 𝟙 _ :=
    hg₂.hom_ext (by rw [Category.assoc, hθ₁, hθ'₁, Category.id_comp]) (by rw [Category.assoc, hθ₂, hθ'₂, Category.id_comp])
  let e : u'.1.A ≅ u'.1.A := ⟨θ, θ', h1, h2⟩
  have he : e.hom ≫ u'.1.f = u'.1.f := hθ₂
  have hmul : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of S')) (P Q : SchemeHomOver t u'.1.f),
      mapPt e.hom he (u'.1.L.mul t P Q) = u'.1.L.mul t (mapPt e.hom he P) (mapPt e.hom he Q) := by
    intro T t P Q
    apply Subtype.ext
    apply hg₂.hom_ext
    · change ((u'.1.L.mul t P Q).1 ≫ θ) ≫ g₂ = (u'.1.L.mul t (mapPt θ he P) (mapPt θ he Q)).1 ≫ g₂
      rw [Category.assoc, hθ₁, mul₁ t P Q, mul₂ t (mapPt θ he P) (mapPt θ he Q)]
      exact mul_val_congr u.1.L rfl _ _ _ _ (by simp [mapPt_coe, Category.assoc, hθ₁])
        (by simp [mapPt_coe, Category.assoc, hθ₁])
    · change ((u'.1.L.mul t P Q).1 ≫ θ) ≫ u'.1.f = (u'.1.L.mul t (mapPt θ he P) (mapPt θ he Q)).1 ≫ u'.1.f
      rw [Category.assoc, hθ₂, (u'.1.L.mul t P Q).2, (u'.1.L.mul t _ _).2]
  have hact : ∀ x : ↥Λ, u'.1.act x ≫ e.hom = e.hom ≫ u'.1.act x := by
    intro x
    apply hg₂.hom_ext
    · change (u'.1.act x ≫ θ) ≫ g₂ = (θ ≫ u'.1.act x) ≫ g₂
      rw [Category.assoc, hθ₁, act₁ x, Category.assoc, act₂ x, ← Category.assoc, hθ₁]
    · change (u'.1.act x ≫ θ) ≫ u'.1.f = (θ ≫ u'.1.act x) ≫ u'.1.f
      rw [Category.assoc, hθ₂, u'.1.act_over, Category.assoc, u'.1.act_over, hθ₂]
  have hPe : mapPt e.hom he u'.2.P = u'.2.P := by
    apply Subtype.ext
    apply hg₂.hom_ext
    · change ((u'.2.P).1 ≫ θ) ≫ g₂ = (u'.2.P).1 ≫ g₂
      rw [Category.assoc, hθ₁, hP₁, hP₂]
    · change ((u'.2.P).1 ≫ θ) ≫ u'.1.f = (u'.2.P).1 ≫ u'.1.f
      rw [Category.assoc, hθ₂]
  have hE := hrig S' u' e he hmul hact hPe
  have hθ : θ = 𝟙 _ := congrArg Iso.hom hE
  rw [← hθ₁, hθ, Category.id_comp]

variable (hM : IsFineModuli Λ N n M fM ptF)

theorem exists_gU {U V : (MC fM C).affineOpens} (hVU : V ≤ U) :
    ∃ g : (uof C hM V).1.A ⟶ (uof C hM U).1.A,
      FakeEllipticCurve.IsPullbackVia (resRing C hVU) (uof C hM U).1 (uof C hM V).1 g ∧
      ((uof C hM V).2.P).1 ≫ g = Spec.map (CommRingCat.ofHom (resRing C hVU)) ≫ ((uof C hM U).2.P).1 := by
  obtain ⟨g, hg, hmul, hact, hlev, hP⟩ := uof_isPullback C hM hVU
  exact ⟨g, ⟨hg, hmul, hact, hlev⟩, hP⟩

def gU {U V : (MC fM C).affineOpens} (hVU : V ≤ U) : (uof C hM V).1.A ⟶ (uof C hM U).1.A :=
  (exists_gU C hM hVU).choose

theorem gU_isPullbackVia {U V : (MC fM C).affineOpens} (hVU : V ≤ U) :
    FakeEllipticCurve.IsPullbackVia (resRing C hVU) (uof C hM U).1 (uof C hM V).1 (gU C hM hVU) :=
  (exists_gU C hM hVU).choose_spec.1

theorem gU_P {U V : (MC fM C).affineOpens} (hVU : V ≤ U) :
    ((uof C hM V).2.P).1 ≫ gU C hM hVU = Spec.map (CommRingCat.ofHom (resRing C hVU)) ≫ ((uof C hM U).2.P).1 :=
  (exists_gU C hM hVU).choose_spec.2

theorem gU_refl (hrig : HRig Λ N n C) (U : (MC fM C).affineOpens) : gU C hM (le_refl U) = 𝟙 _ := by
  refine comparison_unique C hrig (resRing C (le_refl U)) (uof C hM U) (uof C hM U) _ _
    (gU_isPullbackVia C hM (le_refl U)) (gU_P C hM (le_refl U)) ?_ ?_
  · exact isPullbackVia_congr (resRing_refl C U).symm _ _ _ (isPullbackVia_id (uof C hM U).1)
  · rw [resRing_refl, Category.comp_id]
    change ((uof C hM U).2.P).1 = Spec.map (𝟙 _) ≫ ((uof C hM U).2.P).1
    rw [Spec.map_id, Category.id_comp]

theorem gU_comp (hrig : HRig Λ N n C) {U V W : (MC fM C).affineOpens} (hWV : W ≤ V) (hVU : V ≤ U) :
    gU C hM hWV ≫ gU C hM hVU = gU C hM (hWV.trans hVU) := by
  refine comparison_unique C hrig (resRing C (hWV.trans hVU)) (uof C hM U) (uof C hM W) _ _ ?_ ?_
    (gU_isPullbackVia C hM (hWV.trans hVU)) (gU_P C hM (hWV.trans hVU))
  · exact isPullbackVia_congr (resRing_comp C hWV hVU) _ _ _
      (isPullbackVia_comp (resRing C hVU) (resRing C hWV) _ _ _ _ _ (gU_isPullbackVia C hM hVU) (gU_isPullbackVia C hM hWV))
  · rw [← Category.assoc, gU_P C hM hWV, Category.assoc, gU_P C hM hVU, ← Category.assoc, ← Spec.map_comp,
      ← CommRingCat.ofHom_comp, resRing_comp]

end Universal
p2m_reactivate "P2MW.S_CerednikDrinfeld_QM_IsFineModuli_exists_locallyOfFinitePresentation_forall_representsOn_hom_isPullback_of_forall_withFullLevel.RelRepGlue"

section Charts

variable (𝔄 : FakeEllipticCurve Λ N C) {r d : ℕ} (hloc : HLoc (𝒪 := 𝒪) (n := n) C r d 𝔄) (hM : IsFineModuli Λ N n M fM ptF)
  (hrig : HRig Λ N n C)

def DU (U : (MC fM C).affineOpens) : PairDatum (N := N) (Λ := Λ) r d (uof C hM U).1 (Aof C 𝔄 U) :=
  datumOf C hloc (uof C hM U) (Aof C 𝔄 U) (gAof C 𝔄 U) (gAof_spec C 𝔄 U).1

def TransSpec {U V : (MC fM C).affineOpens} (hVU : V ≤ U) (e : (DU C 𝔄 hloc hM V).X ⟶ (DU C 𝔄 hloc hM U).X) : Prop :=
  letI : Algebra (ringOf (fM := fM) C U) (ringOf (fM := fM) C V) := (resRing C hVU).toAlgebra
  CategoryTheory.IsPullback e (DU C 𝔄 hloc hM V).ξ (DU C 𝔄 hloc hM U).ξ
      (Spec.map (CommRingCat.ofHom (algebraMap (ringOf (fM := fM) C U) (ringOf (fM := fM) C V)))) ∧
    ∀ (T : Type) [CommRing T] [Algebra (ringOf (fM := fM) C V) T] [Algebra (ringOf (fM := fM) C U) T]
      [IsScalarTower (ringOf (fM := fM) C U) (ringOf (fM := fM) C V) T]
      (E' A' : FakeEllipticCurve Λ N T)
      (gE' : E'.A ⟶ (uof C hM V).1.A)
      (hgE' : FakeEllipticCurve.IsPullbackVia (algebraMap (ringOf (fM := fM) C V) T) (uof C hM V).1 E' gE')
      (gA' : A'.A ⟶ (Aof C 𝔄 V).A)
      (hgA' : FakeEllipticCurve.IsPullbackVia (algebraMap (ringOf (fM := fM) C V) T) (Aof C 𝔄 V) A' gA')
      (hgE : FakeEllipticCurve.IsPullbackVia (algebraMap (ringOf (fM := fM) C U) T) (uof C hM U).1 E' (gE' ≫ gU C hM hVU))
      (hgA : FakeEllipticCurve.IsPullbackVia (algebraMap (ringOf (fM := fM) C U) T) (Aof C 𝔄 U) A' (gA' ≫ gA C 𝔄 hVU))
      (φ : E'.A ⟶ A'.A) (φ' : A'.A ⟶ E'.A) (hφ : φ ≫ A'.f = E'.f)
      (hp : FakeEllipticCurve.IsIsogenyPair (r ^ d) E' A' φ φ') (hl : FakeEllipticCurve.PreservesLevel E' A' φ hφ),
      ((DU C 𝔄 hloc hM V).pt T E' A' gE' hgE' gA' hgA' φ φ' hφ hp hl).1 ≫ e =
        ((DU C 𝔄 hloc hM U).pt T E' A' (gE' ≫ gU C hM hVU) hgE (gA' ≫ gA C 𝔄 hVU) hgA φ φ' hφ hp hl).1

theorem existsUnique_trans {U V : (MC fM C).affineOpens} (hVU : V ≤ U) :
    ∃! e : (DU C 𝔄 hloc hM V).X ⟶ (DU C 𝔄 hloc hM U).X, TransSpec C 𝔄 hloc hM hVU e := by
  letI : Algebra (ringOf (fM := fM) C U) (ringOf (fM := fM) C V) := (resRing C hVU).toAlgebra
  exact CerednikDrinfeld.QM.FakeEllipticCurve.IsogenyPair.existsUnique_hom_isPullback_of_representsOn r d
    (ringOf (fM := fM) C U) (uof C hM U).1 (Aof C 𝔄 U) (DU C 𝔄 hloc hM U).X (DU C 𝔄 hloc hM U).ξ
    (DU C 𝔄 hloc hM U).pt (DU C 𝔄 hloc hM U).rep
    (ringOf (fM := fM) C V) (uof C hM V).1 (Aof C 𝔄 V)
    (gU C hM hVU) (gU_isPullbackVia C hM hVU) (gA C 𝔄 hVU) (gA_isPullbackVia C 𝔄 hVU)
    (DU C 𝔄 hloc hM V).X (DU C 𝔄 hloc hM V).ξ (DU C 𝔄 hloc hM V).pt (DU C 𝔄 hloc hM V).rep

def transX {U V : (MC fM C).affineOpens} (hVU : V ≤ U) : (DU C 𝔄 hloc hM V).X ⟶ (DU C 𝔄 hloc hM U).X :=
  (existsUnique_trans C 𝔄 hloc hM hVU).exists.choose

theorem transX_spec {U V : (MC fM C).affineOpens} (hVU : V ≤ U) :
    TransSpec C 𝔄 hloc hM hVU (transX C 𝔄 hloc hM hVU) :=
  (existsUnique_trans C 𝔄 hloc hM hVU).exists.choose_spec

theorem transX_isPullback {U V : (MC fM C).affineOpens} (hVU : V ≤ U) :
    IsPullback (transX C 𝔄 hloc hM hVU) (DU C 𝔄 hloc hM V).ξ (DU C 𝔄 hloc hM U).ξ
      (Spec.map (CommRingCat.ofHom (resRing C hVU))) :=
  (transX_spec C 𝔄 hloc hM hVU).1

include hrig in
theorem transX_id (U : (MC fM C).affineOpens) : transX C 𝔄 hloc hM (le_refl U) = 𝟙 _ := by
  refine ((existsUnique_trans C 𝔄 hloc hM (le_refl U)).unique (transX_spec C 𝔄 hloc hM (le_refl U)) ?_)
  letI : Algebra (ringOf (fM := fM) C U) (ringOf (fM := fM) C U) := (resRing C (le_refl U)).toAlgebra
  refine ⟨?_, ?_⟩
  · have hS : Spec.map (CommRingCat.ofHom (algebraMap (ringOf (fM := fM) C U) (ringOf (fM := fM) C U))) = 𝟙 _ := by
      change Spec.map (CommRingCat.ofHom (resRing C (le_refl U))) = 𝟙 _
      rw [resRing_refl, CommRingCat.ofHom_id]; exact Spec.map_id _
    rw [hS]; exact IsPullback.of_horiz_isIso ⟨by simp⟩
  · intro T instT instV instU instTow E' A' gE' hgE' gA' hgA' hgE hgA φ φ' hφ hp hl
    rw [Category.comp_id]
    have hE : gE' = gE' ≫ gU C hM (le_refl U) := by rw [gU_refl C hM hrig, Category.comp_id]
    have hA : gA' = gA' ≫ gA C 𝔄 (le_refl U) := by rw [gA_refl, Category.comp_id]
    have hi : instV = instU := by
      refine Algebra.algebra_ext _ _ fun x => ?_
      have h := @IsScalarTower.algebraMap_apply (ringOf (fM := fM) C U) (ringOf (fM := fM) C U) T _ _ _
        ((resRing C (le_refl U)).toAlgebra) instV instU instTow x
      rw [h]
      change _ = @algebraMap (ringOf (fM := fM) C U) T _ _ instV (resRing C (le_refl U) x)
      rw [resRing_refl]; rfl
    exact PairDatum.pt_congr' _ instV instU hi E' A' hE hgE' hgE hA hgA' hgA φ φ' hφ hp hl

include hrig in
theorem transX_comp {U V W : (MC fM C).affineOpens} (hWV : W ≤ V) (hVU : V ≤ U) :
    transX C 𝔄 hloc hM hWV ≫ transX C 𝔄 hloc hM hVU = transX C 𝔄 hloc hM (hWV.trans hVU) := by
  refine ((existsUnique_trans C 𝔄 hloc hM (hWV.trans hVU)).unique ?_ (transX_spec C 𝔄 hloc hM (hWV.trans hVU)))
  letI instUW : Algebra (ringOf (fM := fM) C U) (ringOf (fM := fM) C W) := (resRing C (hWV.trans hVU)).toAlgebra
  have hSpec : Spec.map (CommRingCat.ofHom (algebraMap (ringOf (fM := fM) C U) (ringOf (fM := fM) C W))) =
      Spec.map (CommRingCat.ofHom (resRing C hWV)) ≫ Spec.map (CommRingCat.ofHom (resRing C hVU)) := by
    change Spec.map (CommRingCat.ofHom (resRing C (hWV.trans hVU))) = _
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, resRing_comp]
  refine ⟨?_, ?_⟩
  · rw [hSpec]
    exact (transX_isPullback C 𝔄 hloc hM hWV).paste_horiz (transX_isPullback C 𝔄 hloc hM hVU)
  · intro T _ instW instU instUW' E' A' gE' hgE' gA' hgA' hgE hgA φ φ' hφ hp hl

    letI instV : Algebra (ringOf (fM := fM) C V) T := ((algebraMap (ringOf (fM := fM) C W) T).comp (resRing C hWV)).toAlgebra
    letI instVW : Algebra (ringOf (fM := fM) C V) (ringOf (fM := fM) C W) := (resRing C hWV).toAlgebra
    letI instUV : Algebra (ringOf (fM := fM) C U) (ringOf (fM := fM) C V) := (resRing C hVU).toAlgebra
    haveI : IsScalarTower (ringOf (fM := fM) C V) (ringOf (fM := fM) C W) T :=
      IsScalarTower.of_algebraMap_eq (fun x => rfl)
    have hUT : ∀ x, algebraMap (ringOf (fM := fM) C U) T x =
        algebraMap (ringOf (fM := fM) C W) T (resRing C hWV (resRing C hVU x)) := by
      intro x
      rw [IsScalarTower.algebraMap_apply (ringOf (fM := fM) C U) (ringOf (fM := fM) C W) T x]
      change algebraMap (ringOf (fM := fM) C W) T (resRing C (hWV.trans hVU) x) = _
      rw [← resRing_comp C hWV hVU]; rfl
    haveI : IsScalarTower (ringOf (fM := fM) C U) (ringOf (fM := fM) C V) T :=
      IsScalarTower.of_algebraMap_eq (fun x => hUT x)
    have hgE₁ : FakeEllipticCurve.IsPullbackVia (algebraMap (ringOf (fM := fM) C V) T) (uof C hM V).1 E' (gE' ≫ gU C hM hWV) :=
      isPullbackVia_comp (resRing C hWV) (algebraMap (ringOf (fM := fM) C W) T) _ _ _ _ _ (gU_isPullbackVia C hM hWV) hgE'
    have hgA₁ : FakeEllipticCurve.IsPullbackVia (algebraMap (ringOf (fM := fM) C V) T) (Aof C 𝔄 V) A' (gA' ≫ gA C 𝔄 hWV) :=
      isPullbackVia_comp (resRing C hWV) (algebraMap (ringOf (fM := fM) C W) T) _ _ _ _ _ (gA_isPullbackVia C 𝔄 hWV) hgA'
    have hgE₂ : FakeEllipticCurve.IsPullbackVia (algebraMap (ringOf (fM := fM) C U) T) (uof C hM U).1 E'
        ((gE' ≫ gU C hM hWV) ≫ gU C hM hVU) :=
      isPullbackVia_congr (RingHom.ext fun x => (hUT x).symm) _ _ _
        (isPullbackVia_comp (resRing C hVU) (algebraMap (ringOf (fM := fM) C V) T) _ _ _ _ _ (gU_isPullbackVia C hM hVU) hgE₁)
    have hgA₂ : FakeEllipticCurve.IsPullbackVia (algebraMap (ringOf (fM := fM) C U) T) (Aof C 𝔄 U) A'
        ((gA' ≫ gA C 𝔄 hWV) ≫ gA C 𝔄 hVU) :=
      isPullbackVia_congr (RingHom.ext fun x => (hUT x).symm) _ _ _
        (isPullbackVia_comp (resRing C hVU) (algebraMap (ringOf (fM := fM) C V) T) _ _ _ _ _ (gA_isPullbackVia C 𝔄 hVU) hgA₁)
    rw [← Category.assoc, (transX_spec C 𝔄 hloc hM hWV).2 T E' A' gE' hgE' gA' hgA' hgE₁ hgA₁ φ φ' hφ hp hl,
      (transX_spec C 𝔄 hloc hM hVU).2 T E' A' (gE' ≫ gU C hM hWV) hgE₁ (gA' ≫ gA C 𝔄 hWV) hgA₁ hgE₂ hgA₂ φ φ' hφ hp hl]
    have hE : (gE' ≫ gU C hM hWV) ≫ gU C hM hVU = gE' ≫ gU C hM (hWV.trans hVU) := by
      rw [Category.assoc, gU_comp C hM hrig]
    have hA : (gA' ≫ gA C 𝔄 hWV) ≫ gA C 𝔄 hVU = gA' ≫ gA C 𝔄 (hWV.trans hVU) := by
      rw [Category.assoc, gA_comp]
    exact PairDatum.pt_congr _ E' A' hE hgE₂ hgE hA hgA₂ hgA φ φ' hφ hp hl

def chartData : ChartData fM C where
  Z U := (DU C 𝔄 hloc hM U).X
  ζ U := (DU C 𝔄 hloc hM U).ξ
  trans hVU := transX C 𝔄 hloc hM hVU
  trans_isPullback hVU := transX_isPullback C 𝔄 hloc hM hVU
  trans_id U := transX_id C 𝔄 hloc hM hrig U
  trans_comp hWV hVU := transX_comp C 𝔄 hloc hM hrig hWV hVU

abbrev Xd : Scheme.{0} := R C (chartData C 𝔄 hloc hM hrig)

abbrev qd : Xd C 𝔄 hloc hM hrig ⟶ MC fM C := qR C (chartData C 𝔄 hloc hM hrig)

theorem locallyOfFinitePresentation_qd : LocallyOfFinitePresentation (qd C 𝔄 hloc hM hrig) :=
  qR_of_forall C (chartData C 𝔄 hloc hM hrig) @LocallyOfFinitePresentation fun U => (DU C 𝔄 hloc hM U).lfp

end Charts
p2m_reactivate "P2MW.S_CerednikDrinfeld_QM_IsFineModuli_exists_locallyOfFinitePresentation_forall_representsOn_hom_isPullback_of_forall_withFullLevel.RelRepGlue"

end RelRepGlue
p2m_reactivate "P2MW.S_CerednikDrinfeld_QM_IsFineModuli_exists_locallyOfFinitePresentation_forall_representsOn_hom_isPullback_of_forall_withFullLevel.RelRepGlue"

end
p2m_reactivate "P2MW.S_CerednikDrinfeld_QM_IsFineModuli_exists_locallyOfFinitePresentation_forall_representsOn_hom_isPullback_of_forall_withFullLevel.RelRepGlue"

set_option autoImplicit false

open scoped TensorProduct Quaternion NumberField
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry QuaternionAlgebra CerednikDrinfeld CerednikDrinfeld.QM NeronModelInfra GoodReductionJacobian

noncomputable section

namespace RelRepGlue

variable {N : ℕ} {𝒪 : Type} [CommRing 𝒪]
  {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} {n : ℕ} {M : Scheme.{0}} {fM : M ⟶ Spec (CommRingCat.of 𝒪)}
  {ptF : ∀ (S : Type) [CommRing S] (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of 𝒪)),
    FakeEllipticCurve.WithFullLevel Λ N n S → SchemeHomOver s fM}
  (C : Type) [CommRing C] [Algebra 𝒪 C]

theorem isPullback_of_ptFC_eq (hM : IsFineModuli Λ N n M fM ptF)
    {T T' : Type} [CommRing T] [Algebra C T] [Algebra 𝒪 T] [IsScalarTower 𝒪 C T]
    [CommRing T'] [Algebra C T'] [Algebra 𝒪 T'] [IsScalarTower 𝒪 C T'] (ψ : T →ₐ[C] T')
    (v : FakeEllipticCurve.WithFullLevel Λ N n T) (w : FakeEllipticCurve.WithFullLevel Λ N n T')
    (h : (ptFC C hM T' w).1 = Spec.map (CommRingCat.ofHom (ψ : T →+* T')) ≫ (ptFC C hM T v).1) :
    FakeEllipticCurve.WithFullLevel.IsPullback (ψ : T →+* T') v w := by
  obtain ⟨w', hw'⟩ := FakeEllipticCurve.WithFullLevel.exists_isPullback (ψ : T →+* T') v
  have h1 := ptFC_pullback C hM _ _ ψ v w' hw'
  rw [← h] at h1
  exact isPullback_of_iso_of_isPullback _ _ _ _ hw' (ptFC_injective C hM _ _ _ (Subtype.ext h1.symm))

section LocalE

variable (𝔄 : FakeEllipticCurve Λ N C) {r d : ℕ} (hloc : HLoc (𝒪 := 𝒪) (n := n) C r d 𝔄) (hM : IsFineModuli Λ N n M fM ptF)
  (hrig : HRig Λ N n C)
  (S : Type) [CommRing S] [Algebra C S] [Algebra 𝒪 S] [IsScalarTower 𝒪 C S]
  (u : FakeEllipticCurve.WithFullLevel Λ N n S)
  (A : FakeEllipticCurve Λ N S) (gA₀ : A.A ⟶ 𝔄.A) (hgA₀ : FakeEllipticCurve.IsPullbackVia (algebraMap C S) 𝔄 A gA₀)
  (X : Scheme.{0}) (ξ : X ⟶ Spec (CommRingCat.of S))
  (pt : FakeEllipticCurve.IsogenyPair.PtFamily r d u.1 A ξ)
  (hX : FakeEllipticCurve.IsogenyPair.RepresentsOn r d u.1 A ξ pt)

abbrev tu : Spec (CommRingCat.of S) ⟶ MC fM C := (ptFC C hM S u).1

theorem tu_snd : tu C hM S u ≫ πC fM C = Spec.map (CommRingCat.ofHom (algebraMap C S)) := ptFC_snd C hM S u

def up (p : SecIdx C (tu C hM S u)) : FakeEllipticCurve.WithFullLevel Λ N n (Wring C (tu C hM S u) p) :=
  (FakeEllipticCurve.WithFullLevel.exists_isPullback (algebraMap S (Wring C (tu C hM S u) p)) u).choose

theorem up_isPullback (p : SecIdx C (tu C hM S u)) :
    FakeEllipticCurve.WithFullLevel.IsPullback (algebraMap S (Wring C (tu C hM S u) p)) u (up C hM S u p) :=
  (FakeEllipticCurve.WithFullLevel.exists_isPullback (algebraMap S (Wring C (tu C hM S u) p)) u).choose_spec

def gp (p : SecIdx C (tu C hM S u)) : (up C hM S u p).1.A ⟶ u.1.A := (up_isPullback C hM S u p).choose

theorem gp_via (p : SecIdx C (tu C hM S u)) :
    FakeEllipticCurve.IsPullbackVia (algebraMap S (Wring C (tu C hM S u) p)) u.1 (up C hM S u p).1 (gp C hM S u p) := by
  obtain ⟨hg, hmul, hact, hlev, -⟩ := (up_isPullback C hM S u p).choose_spec
  exact ⟨hg, hmul, hact, hlev⟩

theorem gp_P (p : SecIdx C (tu C hM S u)) :
    ((up C hM S u p).2.P).1 ≫ gp C hM S u p =
      Spec.map (CommRingCat.ofHom (algebraMap S (Wring C (tu C hM S u) p))) ≫ (u.2.P).1 :=
  (up_isPullback C hM S u p).choose_spec.2.2.2.2

theorem up_isPullback_uof (p : SecIdx C (tu C hM S u)) :
    FakeEllipticCurve.WithFullLevel.IsPullback (φW C (tu C hM S u) p) (uof C hM p.1.2) (up C hM S u p) :=
  isPullback_uof_of_isPullback_algebraMap C (tu C hM S u) hM u rfl p (up C hM S u p) (up_isPullback C hM S u p)

def kU (p : SecIdx C (tu C hM S u)) : (up C hM S u p).1.A ⟶ (uof C hM p.1.2).1.A := (up_isPullback_uof C hM S u p).choose

theorem kU_via (p : SecIdx C (tu C hM S u)) :
    FakeEllipticCurve.IsPullbackVia (φW C (tu C hM S u) p) (uof C hM p.1.2).1 (up C hM S u p).1 (kU C hM S u p) := by
  obtain ⟨hg, hmul, hact, hlev, -⟩ := (up_isPullback_uof C hM S u p).choose_spec
  exact ⟨hg, hmul, hact, hlev⟩

theorem kU_P (p : SecIdx C (tu C hM S u)) :
    ((up C hM S u p).2.P).1 ≫ kU C hM S u p =
      Spec.map (CommRingCat.ofHom (φW C (tu C hM S u) p)) ≫ ((uof C hM p.1.2).2.P).1 :=
  (up_isPullback_uof C hM S u p).choose_spec.2.2.2.2

theorem exists_Ap (p : SecIdx C (tu C hM S u)) :
    ∃ (A' : FakeEllipticCurve Λ N (Wring C (tu C hM S u) p)) (g : A'.A ⟶ A.A),
      FakeEllipticCurve.IsPullbackVia (algebraMap S (Wring C (tu C hM S u) p)) A A' g ∧
      ∀ {T : Scheme.{0}} (t' : T ⟶ Spec (CommRingCat.of (Wring C (tu C hM S u) p))) (P : SchemeHomOver t' A'.f),
        (∃ P₀ : T ⟶ A.C, P₀ ≫ A.lev = P.1 ≫ g) → FactorsThrough A'.lev P := by
  obtain ⟨A', g, hg, hmul, hact, hlev, hlev'⟩ :=
    FakeEllipticCurve.exists_isPullback_levelIff (algebraMap S (Wring C (tu C hM S u) p)) A
  exact ⟨A', g, ⟨hg, hmul, hact, hlev⟩, hlev'⟩

def Ap (p : SecIdx C (tu C hM S u)) : FakeEllipticCurve Λ N (Wring C (tu C hM S u) p) := (exists_Ap C hM S u A p).choose

def hAp (p : SecIdx C (tu C hM S u)) : (Ap C hM S u A p).A ⟶ A.A := (exists_Ap C hM S u A p).choose_spec.choose

theorem hAp_via (p : SecIdx C (tu C hM S u)) :
    FakeEllipticCurve.IsPullbackVia (algebraMap S (Wring C (tu C hM S u) p)) A (Ap C hM S u A p) (hAp C hM S u A p) :=
  (exists_Ap C hM S u A p).choose_spec.choose_spec.1

theorem hAp_levelIff (p : SecIdx C (tu C hM S u)) {T : Scheme.{0}}
    (t' : T ⟶ Spec (CommRingCat.of (Wring C (tu C hM S u) p))) (P : SchemeHomOver t' (Ap C hM S u A p).f)
    (h : ∃ P₀ : T ⟶ A.C, P₀ ≫ A.lev = P.1 ≫ hAp C hM S u A p) : FactorsThrough (Ap C hM S u A p).lev P :=
  (exists_Ap C hM S u A p).choose_spec.choose_spec.2 t' P h

include hgA₀ in

theorem hAp_gA₀_via (p : SecIdx C (tu C hM S u)) :
    FakeEllipticCurve.IsPullbackVia (algebraMap C (Wring C (tu C hM S u) p)) 𝔄 (Ap C hM S u A p)
      (hAp C hM S u A p ≫ gA₀) :=
  isPullbackVia_congr (IsScalarTower.algebraMap_eq C S (Wring C (tu C hM S u) p)).symm _ _ _
    (isPullbackVia_comp _ _ _ _ _ _ _ hgA₀ (hAp_via C hM S u A p))

include hgA₀ in

theorem exists_kA (p : SecIdx C (tu C hM S u)) :
    ∃ k : (Ap C hM S u A p).A ⟶ (Aof (fM := fM) C 𝔄 p.1.2).A,
      k ≫ gAof C 𝔄 p.1.2 = hAp C hM S u A p ≫ gA₀ ∧
      k ≫ (Aof C 𝔄 p.1.2).f = (Ap C hM S u A p).f ≫ Spec.map (CommRingCat.ofHom (φW C (tu C hM S u) p)) ∧
      (∀ k' : (Ap C hM S u A p).A ⟶ (Aof (fM := fM) C 𝔄 p.1.2).A, k' ≫ gAof C 𝔄 p.1.2 = hAp C hM S u A p ≫ gA₀ →
        k' ≫ (Aof C 𝔄 p.1.2).f = (Ap C hM S u A p).f ≫ Spec.map (CommRingCat.ofHom (φW C (tu C hM S u) p)) → k' = k) ∧
      FakeEllipticCurve.IsPullbackVia (φW C (tu C hM S u) p) (Aof C 𝔄 p.1.2) (Ap C hM S u A p) k :=
  FakeEllipticCurve.IsPullbackVia.exists_comp_eq_and_isPullbackVia_of_comp_eq
    (algebraMap C (ringOf (fM := fM) C p.1.2)) (φW C (tu C hM S u) p) (algebraMap C (Wring C (tu C hM S u) p))
    (φW_comp_algebraMap C (tu C hM S u) (tu_snd C hM S u) p) 𝔄 (Aof C 𝔄 p.1.2) (Ap C hM S u A p)
    (gAof C 𝔄 p.1.2) (gAof_spec C 𝔄 p.1.2).1 (fun t' P h => (gAof_spec C 𝔄 p.1.2).2 t' P h)
    (hAp C hM S u A p ≫ gA₀) (hAp_gA₀_via C 𝔄 hM S u A gA₀ hgA₀ p)

def kA (p : SecIdx C (tu C hM S u)) : (Ap C hM S u A p).A ⟶ (Aof (fM := fM) C 𝔄 p.1.2).A :=
  (exists_kA C 𝔄 hM S u A gA₀ hgA₀ p).choose

theorem kA_gAof (p : SecIdx C (tu C hM S u)) : kA C 𝔄 hM S u A gA₀ hgA₀ p ≫ gAof C 𝔄 p.1.2 = hAp C hM S u A p ≫ gA₀ :=
  (exists_kA C 𝔄 hM S u A gA₀ hgA₀ p).choose_spec.1

theorem kA_over (p : SecIdx C (tu C hM S u)) :
    kA C 𝔄 hM S u A gA₀ hgA₀ p ≫ (Aof C 𝔄 p.1.2).f =
      (Ap C hM S u A p).f ≫ Spec.map (CommRingCat.ofHom (φW C (tu C hM S u) p)) :=
  (exists_kA C 𝔄 hM S u A gA₀ hgA₀ p).choose_spec.2.1

theorem kA_unique (p : SecIdx C (tu C hM S u)) (k' : (Ap C hM S u A p).A ⟶ (Aof (fM := fM) C 𝔄 p.1.2).A)
    (h1 : k' ≫ gAof C 𝔄 p.1.2 = hAp C hM S u A p ≫ gA₀)
    (h2 : k' ≫ (Aof C 𝔄 p.1.2).f = (Ap C hM S u A p).f ≫ Spec.map (CommRingCat.ofHom (φW C (tu C hM S u) p))) :
    k' = kA C 𝔄 hM S u A gA₀ hgA₀ p :=
  (exists_kA C 𝔄 hM S u A gA₀ hgA₀ p).choose_spec.2.2.1 k' h1 h2

theorem kA_via (p : SecIdx C (tu C hM S u)) :
    FakeEllipticCurve.IsPullbackVia (φW C (tu C hM S u) p) (Aof C 𝔄 p.1.2) (Ap C hM S u A p) (kA C 𝔄 hM S u A gA₀ hgA₀ p) :=
  (exists_kA C 𝔄 hM S u A gA₀ hgA₀ p).choose_spec.2.2.2

def Dp (p : SecIdx C (tu C hM S u)) : PairDatum (N := N) (Λ := Λ) r d (up C hM S u p).1 (Ap C hM S u A p) :=
  datumOf C hloc (up C hM S u p) (Ap C hM S u A p) (hAp C hM S u A p ≫ gA₀) (hAp_gA₀_via C 𝔄 hM S u A gA₀ hgA₀ p)

def IotaSpec (p : SecIdx C (tu C hM S u)) (e : (Dp C 𝔄 hloc hM S u A gA₀ hgA₀ p).X ⟶ X) : Prop :=
  CategoryTheory.IsPullback e (Dp C 𝔄 hloc hM S u A gA₀ hgA₀ p).ξ ξ
      (Spec.map (CommRingCat.ofHom (algebraMap S (Wring C (tu C hM S u) p)))) ∧
    ∀ (T : Type) [CommRing T] [Algebra (Wring C (tu C hM S u) p) T] [Algebra S T]
      [IsScalarTower S (Wring C (tu C hM S u) p) T]
      (E' A' : FakeEllipticCurve Λ N T)
      (gE' : E'.A ⟶ (up C hM S u p).1.A)
      (hgE' : FakeEllipticCurve.IsPullbackVia (algebraMap (Wring C (tu C hM S u) p) T) (up C hM S u p).1 E' gE')
      (gA' : A'.A ⟶ (Ap C hM S u A p).A)
      (hgA' : FakeEllipticCurve.IsPullbackVia (algebraMap (Wring C (tu C hM S u) p) T) (Ap C hM S u A p) A' gA')
      (hgE : FakeEllipticCurve.IsPullbackVia (algebraMap S T) u.1 E' (gE' ≫ gp C hM S u p))
      (hgA : FakeEllipticCurve.IsPullbackVia (algebraMap S T) A A' (gA' ≫ hAp C hM S u A p))
      (φ : E'.A ⟶ A'.A) (φ' : A'.A ⟶ E'.A) (hφ : φ ≫ A'.f = E'.f)
      (hp : FakeEllipticCurve.IsIsogenyPair (r ^ d) E' A' φ φ') (hl : FakeEllipticCurve.PreservesLevel E' A' φ hφ),
      ((Dp C 𝔄 hloc hM S u A gA₀ hgA₀ p).pt T E' A' gE' hgE' gA' hgA' φ φ' hφ hp hl).1 ≫ e =
        (pt T E' A' (gE' ≫ gp C hM S u p) hgE (gA' ≫ hAp C hM S u A p) hgA φ φ' hφ hp hl).1

include hX in
theorem existsUnique_iota (p : SecIdx C (tu C hM S u)) :
    ∃! e : (Dp C 𝔄 hloc hM S u A gA₀ hgA₀ p).X ⟶ X, IotaSpec C 𝔄 hloc hM S u A gA₀ hgA₀ X ξ pt p e :=
  CerednikDrinfeld.QM.FakeEllipticCurve.IsogenyPair.existsUnique_hom_isPullback_of_representsOn r d
    S u.1 A X ξ pt hX (Wring C (tu C hM S u) p) (up C hM S u p).1 (Ap C hM S u A p)
    (gp C hM S u p) (gp_via C hM S u p) (hAp C hM S u A p) (hAp_via C hM S u A p)
    (Dp C 𝔄 hloc hM S u A gA₀ hgA₀ p).X (Dp C 𝔄 hloc hM S u A gA₀ hgA₀ p).ξ (Dp C 𝔄 hloc hM S u A gA₀ hgA₀ p).pt (Dp C 𝔄 hloc hM S u A gA₀ hgA₀ p).rep

def iota (p : SecIdx C (tu C hM S u)) : (Dp C 𝔄 hloc hM S u A gA₀ hgA₀ p).X ⟶ X := (existsUnique_iota C 𝔄 hloc hM S u A gA₀ hgA₀ X ξ pt hX p).exists.choose

theorem iota_spec (p : SecIdx C (tu C hM S u)) : IotaSpec C 𝔄 hloc hM S u A gA₀ hgA₀ X ξ pt p (iota C 𝔄 hloc hM S u A gA₀ hgA₀ X ξ pt hX p) :=
  (existsUnique_iota C 𝔄 hloc hM S u A gA₀ hgA₀ X ξ pt hX p).exists.choose_spec

theorem iota_unique (p : SecIdx C (tu C hM S u)) (e : (Dp C 𝔄 hloc hM S u A gA₀ hgA₀ p).X ⟶ X)
    (he : IotaSpec C 𝔄 hloc hM S u A gA₀ hgA₀ X ξ pt p e) : e = iota C 𝔄 hloc hM S u A gA₀ hgA₀ X ξ pt hX p :=
  (existsUnique_iota C 𝔄 hloc hM S u A gA₀ hgA₀ X ξ pt hX p).unique he (iota_spec C 𝔄 hloc hM S u A gA₀ hgA₀ X ξ pt hX p)

theorem iota_sq (p : SecIdx C (tu C hM S u)) :
    IsPullback (Dp C 𝔄 hloc hM S u A gA₀ hgA₀ p).ξ (iota C 𝔄 hloc hM S u A gA₀ hgA₀ X ξ pt hX p) (Wι C (tu C hM S u) p) ξ := by
  rw [← spec_algebraMap_W]
  exact (iota_spec C 𝔄 hloc hM S u A gA₀ hgA₀ X ξ pt hX p).1.flip

def CSpec (p : SecIdx C (tu C hM S u)) (e : (Dp C 𝔄 hloc hM S u A gA₀ hgA₀ p).X ⟶ (DU C 𝔄 hloc hM p.1.2).X) : Prop :=
  letI : Algebra (ringOf (fM := fM) C p.1.2) (Wring C (tu C hM S u) p) := (φW C (tu C hM S u) p).toAlgebra
  CategoryTheory.IsPullback e (Dp C 𝔄 hloc hM S u A gA₀ hgA₀ p).ξ (DU C 𝔄 hloc hM p.1.2).ξ
      (Spec.map (CommRingCat.ofHom (algebraMap (ringOf (fM := fM) C p.1.2) (Wring C (tu C hM S u) p)))) ∧
    ∀ (T : Type) [CommRing T] [Algebra (Wring C (tu C hM S u) p) T] [Algebra (ringOf (fM := fM) C p.1.2) T]
      [IsScalarTower (ringOf (fM := fM) C p.1.2) (Wring C (tu C hM S u) p) T]
      (E' A' : FakeEllipticCurve Λ N T)
      (gE' : E'.A ⟶ (up C hM S u p).1.A)
      (hgE' : FakeEllipticCurve.IsPullbackVia (algebraMap (Wring C (tu C hM S u) p) T) (up C hM S u p).1 E' gE')
      (gA' : A'.A ⟶ (Ap C hM S u A p).A)
      (hgA' : FakeEllipticCurve.IsPullbackVia (algebraMap (Wring C (tu C hM S u) p) T) (Ap C hM S u A p) A' gA')
      (hgE : FakeEllipticCurve.IsPullbackVia (algebraMap (ringOf (fM := fM) C p.1.2) T) (uof C hM p.1.2).1 E'
        (gE' ≫ kU C hM S u p))
      (hgA : FakeEllipticCurve.IsPullbackVia (algebraMap (ringOf (fM := fM) C p.1.2) T) (Aof C 𝔄 p.1.2) A'
        (gA' ≫ kA C 𝔄 hM S u A gA₀ hgA₀ p))
      (φ : E'.A ⟶ A'.A) (φ' : A'.A ⟶ E'.A) (hφ : φ ≫ A'.f = E'.f)
      (hp : FakeEllipticCurve.IsIsogenyPair (r ^ d) E' A' φ φ') (hl : FakeEllipticCurve.PreservesLevel E' A' φ hφ),
      ((Dp C 𝔄 hloc hM S u A gA₀ hgA₀ p).pt T E' A' gE' hgE' gA' hgA' φ φ' hφ hp hl).1 ≫ e =
        ((DU C 𝔄 hloc hM p.1.2).pt T E' A' (gE' ≫ kU C hM S u p) hgE (gA' ≫ kA C 𝔄 hM S u A gA₀ hgA₀ p) hgA
          φ φ' hφ hp hl).1

theorem existsUnique_c (p : SecIdx C (tu C hM S u)) :
    ∃! e : (Dp C 𝔄 hloc hM S u A gA₀ hgA₀ p).X ⟶ (DU C 𝔄 hloc hM p.1.2).X, CSpec C 𝔄 hloc hM S u A gA₀ hgA₀ p e := by
  letI : Algebra (ringOf (fM := fM) C p.1.2) (Wring C (tu C hM S u) p) := (φW C (tu C hM S u) p).toAlgebra
  exact CerednikDrinfeld.QM.FakeEllipticCurve.IsogenyPair.existsUnique_hom_isPullback_of_representsOn r d
    (ringOf (fM := fM) C p.1.2) (uof C hM p.1.2).1 (Aof C 𝔄 p.1.2)
    (DU C 𝔄 hloc hM p.1.2).X (DU C 𝔄 hloc hM p.1.2).ξ (DU C 𝔄 hloc hM p.1.2).pt (DU C 𝔄 hloc hM p.1.2).rep
    (Wring C (tu C hM S u) p) (up C hM S u p).1 (Ap C hM S u A p)
    (kU C hM S u p) (kU_via C hM S u p) (kA C 𝔄 hM S u A gA₀ hgA₀ p) (kA_via C 𝔄 hM S u A gA₀ hgA₀ p)
    (Dp C 𝔄 hloc hM S u A gA₀ hgA₀ p).X (Dp C 𝔄 hloc hM S u A gA₀ hgA₀ p).ξ (Dp C 𝔄 hloc hM S u A gA₀ hgA₀ p).pt (Dp C 𝔄 hloc hM S u A gA₀ hgA₀ p).rep

def cmp (p : SecIdx C (tu C hM S u)) : (Dp C 𝔄 hloc hM S u A gA₀ hgA₀ p).X ⟶ (DU C 𝔄 hloc hM p.1.2).X :=
  (existsUnique_c C 𝔄 hloc hM S u A gA₀ hgA₀ p).exists.choose

theorem cmp_spec (p : SecIdx C (tu C hM S u)) : CSpec C 𝔄 hloc hM S u A gA₀ hgA₀ p (cmp C 𝔄 hloc hM S u A gA₀ hgA₀ p) :=
  (existsUnique_c C 𝔄 hloc hM S u A gA₀ hgA₀ p).exists.choose_spec

theorem cmp_unique (p : SecIdx C (tu C hM S u)) (e : (Dp C 𝔄 hloc hM S u A gA₀ hgA₀ p).X ⟶ (DU C 𝔄 hloc hM p.1.2).X)
    (he : CSpec C 𝔄 hloc hM S u A gA₀ hgA₀ p e) : e = cmp C 𝔄 hloc hM S u A gA₀ hgA₀ p :=
  (existsUnique_c C 𝔄 hloc hM S u A gA₀ hgA₀ p).unique he (cmp_spec C 𝔄 hloc hM S u A gA₀ hgA₀ p)

theorem cmp_isPullback (p : SecIdx C (tu C hM S u)) :
    IsPullback (cmp C 𝔄 hloc hM S u A gA₀ hgA₀ p) (Dp C 𝔄 hloc hM S u A gA₀ hgA₀ p).ξ (DU C 𝔄 hloc hM p.1.2).ξ
      (Spec.map (CommRingCat.ofHom (φW C (tu C hM S u) p))) :=
  (cmp_spec C 𝔄 hloc hM S u A gA₀ hgA₀ p).1

omit hgA₀ hX in
theorem isPullbackVia_of_eq {N' : ℕ} {T T' : Type} [CommRing T] [CommRing T'] {φ : T →+* T'}
    {E : FakeEllipticCurve Λ N' T} {E' : FakeEllipticCurve Λ N' T'} {g g' : E'.A ⟶ E.A} (h : g = g')
    (hg : FakeEllipticCurve.IsPullbackVia φ E E' g) : FakeEllipticCurve.IsPullbackVia φ E E' g' := by
  subst h; exact hg

theorem pt_congr_raw {T : Type} [CommRing T] [Algebra S T] (E' A' : FakeEllipticCurve Λ N T)
    {gE₁ gE₂ : E'.A ⟶ u.1.A} (hE : gE₁ = gE₂)
    (h₁ : FakeEllipticCurve.IsPullbackVia (algebraMap S T) u.1 E' gE₁) (h₂ : FakeEllipticCurve.IsPullbackVia (algebraMap S T) u.1 E' gE₂)
    {gA₁ gA₂ : A'.A ⟶ A.A} (hA : gA₁ = gA₂)
    (k₁ : FakeEllipticCurve.IsPullbackVia (algebraMap S T) A A' gA₁) (k₂ : FakeEllipticCurve.IsPullbackVia (algebraMap S T) A A' gA₂)
    (φ : E'.A ⟶ A'.A) (φ' : A'.A ⟶ E'.A) (hφ : φ ≫ A'.f = E'.f)
    (hp : FakeEllipticCurve.IsIsogenyPair (r ^ d) E' A' φ φ') (hl : FakeEllipticCurve.PreservesLevel E' A' φ hφ) :
    (pt T E' A' gE₁ h₁ gA₁ k₁ φ φ' hφ hp hl).1 = (pt T E' A' gE₂ h₂ gA₂ k₂ φ φ' hφ hp hl).1 := by
  subst hE hA; rfl

theorem ρW_comp_algebraMap {k p : SecIdx C (tu C hM S u)} (h : k ≤ p) :
    (ρW C (tu C hM S u) h).comp (algebraMap S (Wring C (tu C hM S u) p)) = algebraMap S (Wring C (tu C hM S u) k) := by
  apply ringHom_eq_of_spec_map_eq
  rw [CommRingCat.ofHom_comp, Spec.map_comp, spec_algebraMap_W, spec_algebraMap_W, spec_ρW_Wι]

theorem ρW_comp_algebraMap_C {k p : SecIdx C (tu C hM S u)} (h : k ≤ p) :
    (ρW C (tu C hM S u) h).comp (algebraMap C (Wring C (tu C hM S u) p)) = algebraMap C (Wring C (tu C hM S u) k) := by
  change (ρW C (tu C hM S u) h).comp ((algebraMap S _).comp (algebraMap C S)) = (algebraMap S _).comp (algebraMap C S)
  rw [← RingHom.comp_assoc, ρW_comp_algebraMap]

theorem ρW_comp_φW {k p : SecIdx C (tu C hM S u)} (h : k ≤ p) :
    (ρW C (tu C hM S u) h).comp (φW C (tu C hM S u) p) = (φW C (tu C hM S u) k).comp (resRing C h.2) := by
  apply ringHom_eq_of_spec_map_eq
  rw [CommRingCat.ofHom_comp, Spec.map_comp, CommRingCat.ofHom_comp, Spec.map_comp, spec_φW_res]

def ρWAlgHom {k p : SecIdx C (tu C hM S u)} (h : k ≤ p) : Wring C (tu C hM S u) p →ₐ[C] Wring C (tu C hM S u) k :=
  { toRingHom := ρW C (tu C hM S u) h
    commutes' := fun c => RingHom.congr_fun (ρW_comp_algebraMap_C C hM S u h) c }

@[scoped simp] theorem coe_ρWAlgHom {k p : SecIdx C (tu C hM S u)} (h : k ≤ p) :
    (ρWAlgHom C hM S u h : Wring C (tu C hM S u) p →+* Wring C (tu C hM S u) k) = ρW C (tu C hM S u) h :=
  RingHom.ext fun _ => rfl

theorem ptFC_up (p : SecIdx C (tu C hM S u)) :
    (ptFC C hM (Wring C (tu C hM S u) p) (up C hM S u p)).1 =
      Spec.map (CommRingCat.ofHom (algebraMap S (Wring C (tu C hM S u) p))) ≫ tu C hM S u :=
  ptFC_pullback C hM S (Wring C (tu C hM S u) p) (IsScalarTower.toAlgHom C S (Wring C (tu C hM S u) p)) u
    (up C hM S u p) (up_isPullback C hM S u p)

theorem exists_mU {k p : SecIdx C (tu C hM S u)} (h : k ≤ p) :
    ∃ m : (up C hM S u k).1.A ⟶ (up C hM S u p).1.A,
      FakeEllipticCurve.IsPullbackVia (ρW C (tu C hM S u) h) (up C hM S u p).1 (up C hM S u k).1 m ∧
      ((up C hM S u k).2.P).1 ≫ m = Spec.map (CommRingCat.ofHom (ρW C (tu C hM S u) h)) ≫ ((up C hM S u p).2.P).1 := by
  have key := isPullback_of_ptFC_eq C hM (ρWAlgHom C hM S u h) (up C hM S u p) (up C hM S u k) (by
    rw [ptFC_up, ptFC_up, coe_ρWAlgHom, ← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp,
      ρW_comp_algebraMap])
  rw [coe_ρWAlgHom] at key
  obtain ⟨m, hg, hmul, hact, hlev, hP⟩ := key
  exact ⟨m, ⟨hg, hmul, hact, hlev⟩, hP⟩

def mU {k p : SecIdx C (tu C hM S u)} (h : k ≤ p) : (up C hM S u k).1.A ⟶ (up C hM S u p).1.A :=
  (exists_mU C hM S u h).choose

theorem mU_via {k p : SecIdx C (tu C hM S u)} (h : k ≤ p) :
    FakeEllipticCurve.IsPullbackVia (ρW C (tu C hM S u) h) (up C hM S u p).1 (up C hM S u k).1 (mU C hM S u h) :=
  (exists_mU C hM S u h).choose_spec.1

theorem mU_P {k p : SecIdx C (tu C hM S u)} (h : k ≤ p) :
    ((up C hM S u k).2.P).1 ≫ mU C hM S u h =
      Spec.map (CommRingCat.ofHom (ρW C (tu C hM S u) h)) ≫ ((up C hM S u p).2.P).1 :=
  (exists_mU C hM S u h).choose_spec.2

theorem exists_mA {k p : SecIdx C (tu C hM S u)} (h : k ≤ p) :
    ∃ m : (Ap C hM S u A k).A ⟶ (Ap C hM S u A p).A, m ≫ hAp C hM S u A p = hAp C hM S u A k ∧
      FakeEllipticCurve.IsPullbackVia (ρW C (tu C hM S u) h) (Ap C hM S u A p) (Ap C hM S u A k) m := by
  obtain ⟨m, h1, -, -, h4⟩ := FakeEllipticCurve.IsPullbackVia.exists_comp_eq_and_isPullbackVia_of_comp_eq
    (algebraMap S (Wring C (tu C hM S u) p)) (ρW C (tu C hM S u) h) (algebraMap S (Wring C (tu C hM S u) k))
    (ρW_comp_algebraMap C hM S u h) A (Ap C hM S u A p) (Ap C hM S u A k)
    (hAp C hM S u A p) (hAp_via C hM S u A p) (fun t' P hh => hAp_levelIff C hM S u A p t' P hh)
    (hAp C hM S u A k) (hAp_via C hM S u A k)
  exact ⟨m, h1, h4⟩

def mA {k p : SecIdx C (tu C hM S u)} (h : k ≤ p) : (Ap C hM S u A k).A ⟶ (Ap C hM S u A p).A :=
  (exists_mA C hM S u A h).choose

theorem mA_hAp {k p : SecIdx C (tu C hM S u)} (h : k ≤ p) : mA C hM S u A h ≫ hAp C hM S u A p = hAp C hM S u A k :=
  (exists_mA C hM S u A h).choose_spec.1

theorem mA_via {k p : SecIdx C (tu C hM S u)} (h : k ≤ p) :
    FakeEllipticCurve.IsPullbackVia (ρW C (tu C hM S u) h) (Ap C hM S u A p) (Ap C hM S u A k) (mA C hM S u A h) :=
  (exists_mA C hM S u A h).choose_spec.2

include hrig in

theorem mU_gp {k p : SecIdx C (tu C hM S u)} (h : k ≤ p) : mU C hM S u h ≫ gp C hM S u p = gp C hM S u k := by
  refine comparison_unique C hrig (algebraMap S (Wring C (tu C hM S u) k)) u (up C hM S u k) _ _ ?_ ?_
    (gp_via C hM S u k) (gp_P C hM S u k)
  · exact isPullbackVia_congr (ρW_comp_algebraMap C hM S u h) _ _ _
      (isPullbackVia_comp _ _ _ _ _ _ _ (gp_via C hM S u p) (mU_via C hM S u h))
  · rw [← Category.assoc, mU_P, Category.assoc, gp_P, ← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp,
      ρW_comp_algebraMap]

include hrig in

theorem mU_kU {k p : SecIdx C (tu C hM S u)} (h : k ≤ p) :
    mU C hM S u h ≫ kU C hM S u p = kU C hM S u k ≫ gU C hM h.2 := by
  refine comparison_unique C hrig ((φW C (tu C hM S u) k).comp (resRing C h.2)) (uof C hM p.1.2) (up C hM S u k) _ _
    ?_ ?_ ?_ ?_
  · exact isPullbackVia_congr (ρW_comp_φW C hM S u h) _ _ _
      (isPullbackVia_comp _ _ _ _ _ _ _ (kU_via C hM S u p) (mU_via C hM S u h))
  · rw [← Category.assoc, mU_P, Category.assoc, kU_P, ← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp,
      ρW_comp_φW]
  · exact isPullbackVia_comp _ _ _ _ _ _ _ (gU_isPullbackVia C hM h.2) (kU_via C hM S u k)
  · rw [← Category.assoc, kU_P, Category.assoc, gU_P, ← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp]

theorem mA_kA {k p : SecIdx C (tu C hM S u)} (h : k ≤ p) :
    mA C hM S u A h ≫ kA C 𝔄 hM S u A gA₀ hgA₀ p = kA C 𝔄 hM S u A gA₀ hgA₀ k ≫ gA C 𝔄 h.2 := by
  have hψ : ((φW C (tu C hM S u) k).comp (resRing C h.2)).comp (algebraMap C (ringOf (fM := fM) C p.1.2)) =
      algebraMap C (Wring C (tu C hM S u) k) := by
    rw [RingHom.comp_assoc, resRing_comp_algebraMap, φW_comp_algebraMap C (tu C hM S u) (tu_snd C hM S u) k]
  obtain ⟨k₀, -, -, huniq, -⟩ := FakeEllipticCurve.IsPullbackVia.exists_comp_eq_and_isPullbackVia_of_comp_eq
    (algebraMap C (ringOf (fM := fM) C p.1.2)) ((φW C (tu C hM S u) k).comp (resRing C h.2))
    (algebraMap C (Wring C (tu C hM S u) k)) hψ 𝔄 (Aof C 𝔄 p.1.2) (Ap C hM S u A k)
    (gAof C 𝔄 p.1.2) (gAof_spec C 𝔄 p.1.2).1 (fun t' P hh => (gAof_spec C 𝔄 p.1.2).2 t' P hh)
    (hAp C hM S u A k ≫ gA₀) (hAp_gA₀_via C 𝔄 hM S u A gA₀ hgA₀ k)
  have e1 := huniq (mA C hM S u A h ≫ kA C 𝔄 hM S u A gA₀ hgA₀ p)
    (by rw [Category.assoc, kA_gAof, ← Category.assoc, mA_hAp])
    (by rw [Category.assoc, kA_over, ← Category.assoc, (mA_via C hM S u A h).1.w, Category.assoc, CommRingCat.ofHom_comp,
          Spec.map_comp, spec_φW_res])
  have e2 := huniq (kA C 𝔄 hM S u A gA₀ hgA₀ k ≫ gA C 𝔄 h.2)
    (by rw [Category.assoc, gA_comp_gAof, kA_gAof])
    (by rw [Category.assoc, gA_over, ← Category.assoc, kA_over, Category.assoc, CommRingCat.ofHom_comp, Spec.map_comp])
  rw [e1, e2]

scoped instance iota_isOpenImmersion (p : SecIdx C (tu C hM S u)) : IsOpenImmersion (iota C 𝔄 hloc hM S u A gA₀ hgA₀ X ξ pt hX p) :=
  MorphismProperty.of_isPullback (iota_sq C 𝔄 hloc hM S u A gA₀ hgA₀ X ξ pt hX p) inferInstance

def RSpec {k p : SecIdx C (tu C hM S u)} (h : k ≤ p) (e : (Dp C 𝔄 hloc hM S u A gA₀ hgA₀ k).X ⟶ (Dp C 𝔄 hloc hM S u A gA₀ hgA₀ p).X) : Prop :=
  letI : Algebra (Wring C (tu C hM S u) p) (Wring C (tu C hM S u) k) := (ρW C (tu C hM S u) h).toAlgebra
  CategoryTheory.IsPullback e (Dp C 𝔄 hloc hM S u A gA₀ hgA₀ k).ξ (Dp C 𝔄 hloc hM S u A gA₀ hgA₀ p).ξ
      (Spec.map (CommRingCat.ofHom (algebraMap (Wring C (tu C hM S u) p) (Wring C (tu C hM S u) k)))) ∧
    ∀ (T : Type) [CommRing T] [Algebra (Wring C (tu C hM S u) k) T] [Algebra (Wring C (tu C hM S u) p) T]
      [IsScalarTower (Wring C (tu C hM S u) p) (Wring C (tu C hM S u) k) T]
      (E' A' : FakeEllipticCurve Λ N T)
      (gE' : E'.A ⟶ (up C hM S u k).1.A)
      (hgE' : FakeEllipticCurve.IsPullbackVia (algebraMap (Wring C (tu C hM S u) k) T) (up C hM S u k).1 E' gE')
      (gA' : A'.A ⟶ (Ap C hM S u A k).A)
      (hgA' : FakeEllipticCurve.IsPullbackVia (algebraMap (Wring C (tu C hM S u) k) T) (Ap C hM S u A k) A' gA')
      (hgE : FakeEllipticCurve.IsPullbackVia (algebraMap (Wring C (tu C hM S u) p) T) (up C hM S u p).1 E'
        (gE' ≫ mU C hM S u h))
      (hgA : FakeEllipticCurve.IsPullbackVia (algebraMap (Wring C (tu C hM S u) p) T) (Ap C hM S u A p) A'
        (gA' ≫ mA C hM S u A h))
      (φ : E'.A ⟶ A'.A) (φ' : A'.A ⟶ E'.A) (hφ : φ ≫ A'.f = E'.f)
      (hp : FakeEllipticCurve.IsIsogenyPair (r ^ d) E' A' φ φ') (hl : FakeEllipticCurve.PreservesLevel E' A' φ hφ),
      ((Dp C 𝔄 hloc hM S u A gA₀ hgA₀ k).pt T E' A' gE' hgE' gA' hgA' φ φ' hφ hp hl).1 ≫ e =
        ((Dp C 𝔄 hloc hM S u A gA₀ hgA₀ p).pt T E' A' (gE' ≫ mU C hM S u h) hgE (gA' ≫ mA C hM S u A h) hgA φ φ' hφ hp hl).1

theorem exists_rcan {k p : SecIdx C (tu C hM S u)} (h : k ≤ p) :
    ∃ e : (Dp C 𝔄 hloc hM S u A gA₀ hgA₀ k).X ⟶ (Dp C 𝔄 hloc hM S u A gA₀ hgA₀ p).X, RSpec C 𝔄 hloc hM S u A gA₀ hgA₀ h e := by
  letI : Algebra (Wring C (tu C hM S u) p) (Wring C (tu C hM S u) k) := (ρW C (tu C hM S u) h).toAlgebra
  exact (CerednikDrinfeld.QM.FakeEllipticCurve.IsogenyPair.existsUnique_hom_isPullback_of_representsOn r d
    (Wring C (tu C hM S u) p) (up C hM S u p).1 (Ap C hM S u A p)
    (Dp C 𝔄 hloc hM S u A gA₀ hgA₀ p).X (Dp C 𝔄 hloc hM S u A gA₀ hgA₀ p).ξ (Dp C 𝔄 hloc hM S u A gA₀ hgA₀ p).pt (Dp C 𝔄 hloc hM S u A gA₀ hgA₀ p).rep
    (Wring C (tu C hM S u) k) (up C hM S u k).1 (Ap C hM S u A k)
    (mU C hM S u h) (mU_via C hM S u h) (mA C hM S u A h) (mA_via C hM S u A h)
    (Dp C 𝔄 hloc hM S u A gA₀ hgA₀ k).X (Dp C 𝔄 hloc hM S u A gA₀ hgA₀ k).ξ (Dp C 𝔄 hloc hM S u A gA₀ hgA₀ k).pt (Dp C 𝔄 hloc hM S u A gA₀ hgA₀ k).rep).exists

def rcan {k p : SecIdx C (tu C hM S u)} (h : k ≤ p) : (Dp C 𝔄 hloc hM S u A gA₀ hgA₀ k).X ⟶ (Dp C 𝔄 hloc hM S u A gA₀ hgA₀ p).X :=
  (exists_rcan C 𝔄 hloc hM S u A gA₀ hgA₀ h).choose

theorem rcan_spec {k p : SecIdx C (tu C hM S u)} (h : k ≤ p) : RSpec C 𝔄 hloc hM S u A gA₀ hgA₀ h (rcan C 𝔄 hloc hM S u A gA₀ hgA₀ h) :=
  (exists_rcan C 𝔄 hloc hM S u A gA₀ hgA₀ h).choose_spec

theorem rcan_isPullback {k p : SecIdx C (tu C hM S u)} (h : k ≤ p) :
    IsPullback (rcan C 𝔄 hloc hM S u A gA₀ hgA₀ h) (Dp C 𝔄 hloc hM S u A gA₀ hgA₀ k).ξ (Dp C 𝔄 hloc hM S u A gA₀ hgA₀ p).ξ
      (Spec.map (CommRingCat.ofHom (ρW C (tu C hM S u) h))) :=
  (rcan_spec C 𝔄 hloc hM S u A gA₀ hgA₀ h).1

include hrig in

theorem rcan_iota {k p : SecIdx C (tu C hM S u)} (h : k ≤ p) :
    rcan C 𝔄 hloc hM S u A gA₀ hgA₀ h ≫ iota C 𝔄 hloc hM S u A gA₀ hgA₀ X ξ pt hX p = iota C 𝔄 hloc hM S u A gA₀ hgA₀ X ξ pt hX k := by
  apply iota_unique
  constructor
  · have sq := (rcan_isPullback C 𝔄 hloc hM S u A gA₀ hgA₀ h).paste_horiz (iota_spec C 𝔄 hloc hM S u A gA₀ hgA₀ X ξ pt hX p).1
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, ρW_comp_algebraMap] at sq
    exact sq
  · intro T _ _ _ _ E' A' gE' hgE' gA' hgA' hgE hgA φ φ' hφ hp hl
    letI algP : Algebra (Wring C (tu C hM S u) p) T :=
      ((algebraMap (Wring C (tu C hM S u) k) T).comp (ρW C (tu C hM S u) h)).toAlgebra
    letI : Algebra (Wring C (tu C hM S u) p) (Wring C (tu C hM S u) k) := (ρW C (tu C hM S u) h).toAlgebra
    haveI : IsScalarTower (Wring C (tu C hM S u) p) (Wring C (tu C hM S u) k) T := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
    haveI : IsScalarTower S (Wring C (tu C hM S u) p) T := IsScalarTower.of_algebraMap_eq (fun x => by
      rw [IsScalarTower.algebraMap_apply S (Wring C (tu C hM S u) k) T x]
      change _ = algebraMap (Wring C (tu C hM S u) k) T (ρW C (tu C hM S u) h (algebraMap S (Wring C (tu C hM S u) p) x))
      rw [← RingHom.comp_apply (ρW C (tu C hM S u) h), ρW_comp_algebraMap])
    have hgEp : FakeEllipticCurve.IsPullbackVia (algebraMap (Wring C (tu C hM S u) p) T) (up C hM S u p).1 E'
        (gE' ≫ mU C hM S u h) :=
      isPullbackVia_comp _ _ _ _ _ _ _ (mU_via C hM S u h) hgE'
    have hgAp : FakeEllipticCurve.IsPullbackVia (algebraMap (Wring C (tu C hM S u) p) T) (Ap C hM S u A p) A'
        (gA' ≫ mA C hM S u A h) :=
      isPullbackVia_comp _ _ _ _ _ _ _ (mA_via C hM S u A h) hgA'
    have hgES : FakeEllipticCurve.IsPullbackVia (algebraMap S T) u.1 E' ((gE' ≫ mU C hM S u h) ≫ gp C hM S u p) :=
      isPullbackVia_of_eq (by rw [Category.assoc, mU_gp C hM hrig S u h]) hgE
    have hgAS : FakeEllipticCurve.IsPullbackVia (algebraMap S T) A A' ((gA' ≫ mA C hM S u A h) ≫ hAp C hM S u A p) :=
      isPullbackVia_of_eq (by rw [Category.assoc, mA_hAp]) hgA
    rw [← Category.assoc, (rcan_spec C 𝔄 hloc hM S u A gA₀ hgA₀ h).2 T E' A' gE' hgE' gA' hgA' hgEp hgAp φ φ' hφ hp hl,
      (iota_spec C 𝔄 hloc hM S u A gA₀ hgA₀ X ξ pt hX p).2 T E' A' _ hgEp _ hgAp hgES hgAS φ φ' hφ hp hl]
    exact pt_congr_raw S u A X ξ pt E' A' (by rw [Category.assoc, mU_gp C hM hrig S u h]) hgES hgE
      (by rw [Category.assoc, mA_hAp]) hgAS hgA φ φ' hφ hp hl

def PsiSpec {k p : SecIdx C (tu C hM S u)} (h : k ≤ p) (e : (Dp C 𝔄 hloc hM S u A gA₀ hgA₀ k).X ⟶ (DU C 𝔄 hloc hM p.1.2).X) : Prop :=
  letI : Algebra (ringOf (fM := fM) C p.1.2) (Wring C (tu C hM S u) k) := ((φW C (tu C hM S u) k).comp (resRing C h.2)).toAlgebra
  CategoryTheory.IsPullback e (Dp C 𝔄 hloc hM S u A gA₀ hgA₀ k).ξ (DU C 𝔄 hloc hM p.1.2).ξ
      (Spec.map (CommRingCat.ofHom (algebraMap (ringOf (fM := fM) C p.1.2) (Wring C (tu C hM S u) k)))) ∧
    ∀ (T : Type) [CommRing T] [Algebra (Wring C (tu C hM S u) k) T] [Algebra (ringOf (fM := fM) C p.1.2) T]
      [IsScalarTower (ringOf (fM := fM) C p.1.2) (Wring C (tu C hM S u) k) T]
      (E' A' : FakeEllipticCurve Λ N T)
      (gE' : E'.A ⟶ (up C hM S u k).1.A)
      (hgE' : FakeEllipticCurve.IsPullbackVia (algebraMap (Wring C (tu C hM S u) k) T) (up C hM S u k).1 E' gE')
      (gA' : A'.A ⟶ (Ap C hM S u A k).A)
      (hgA' : FakeEllipticCurve.IsPullbackVia (algebraMap (Wring C (tu C hM S u) k) T) (Ap C hM S u A k) A' gA')
      (hgE : FakeEllipticCurve.IsPullbackVia (algebraMap (ringOf (fM := fM) C p.1.2) T) (uof C hM p.1.2).1 E'
        (gE' ≫ (kU C hM S u k ≫ gU C hM h.2)))
      (hgA : FakeEllipticCurve.IsPullbackVia (algebraMap (ringOf (fM := fM) C p.1.2) T) (Aof C 𝔄 p.1.2) A'
        (gA' ≫ (kA C 𝔄 hM S u A gA₀ hgA₀ k ≫ gA C 𝔄 h.2)))
      (φ : E'.A ⟶ A'.A) (φ' : A'.A ⟶ E'.A) (hφ : φ ≫ A'.f = E'.f)
      (hp : FakeEllipticCurve.IsIsogenyPair (r ^ d) E' A' φ φ') (hl : FakeEllipticCurve.PreservesLevel E' A' φ hφ),
      ((Dp C 𝔄 hloc hM S u A gA₀ hgA₀ k).pt T E' A' gE' hgE' gA' hgA' φ φ' hφ hp hl).1 ≫ e =
        ((DU C 𝔄 hloc hM p.1.2).pt T E' A' (gE' ≫ (kU C hM S u k ≫ gU C hM h.2)) hgE
          (gA' ≫ (kA C 𝔄 hM S u A gA₀ hgA₀ k ≫ gA C 𝔄 h.2)) hgA φ φ' hφ hp hl).1

theorem psiSpec_unique {k p : SecIdx C (tu C hM S u)} (h : k ≤ p)
    (e₁ e₂ : (Dp C 𝔄 hloc hM S u A gA₀ hgA₀ k).X ⟶ (DU C 𝔄 hloc hM p.1.2).X)
    (h₁ : PsiSpec C 𝔄 hloc hM S u A gA₀ hgA₀ h e₁) (h₂ : PsiSpec C 𝔄 hloc hM S u A gA₀ hgA₀ h e₂) : e₁ = e₂ := by
  letI : Algebra (ringOf (fM := fM) C p.1.2) (Wring C (tu C hM S u) k) := ((φW C (tu C hM S u) k).comp (resRing C h.2)).toAlgebra
  exact (CerednikDrinfeld.QM.FakeEllipticCurve.IsogenyPair.existsUnique_hom_isPullback_of_representsOn r d
    (ringOf (fM := fM) C p.1.2) (uof C hM p.1.2).1 (Aof C 𝔄 p.1.2)
    (DU C 𝔄 hloc hM p.1.2).X (DU C 𝔄 hloc hM p.1.2).ξ (DU C 𝔄 hloc hM p.1.2).pt (DU C 𝔄 hloc hM p.1.2).rep
    (Wring C (tu C hM S u) k) (up C hM S u k).1 (Ap C hM S u A k)
    (kU C hM S u k ≫ gU C hM h.2)
    (isPullbackVia_comp _ _ _ _ _ _ _ (gU_isPullbackVia C hM h.2) (kU_via C hM S u k))
    (kA C 𝔄 hM S u A gA₀ hgA₀ k ≫ gA C 𝔄 h.2)
    (isPullbackVia_comp _ _ _ _ _ _ _ (gA_isPullbackVia C 𝔄 h.2) (kA_via C 𝔄 hM S u A gA₀ hgA₀ k))
    (Dp C 𝔄 hloc hM S u A gA₀ hgA₀ k).X (Dp C 𝔄 hloc hM S u A gA₀ hgA₀ k).ξ (Dp C 𝔄 hloc hM S u A gA₀ hgA₀ k).pt (Dp C 𝔄 hloc hM S u A gA₀ hgA₀ k).rep).unique h₁ h₂

theorem psiSpec_cmp_transX {k p : SecIdx C (tu C hM S u)} (h : k ≤ p) :
    PsiSpec C 𝔄 hloc hM S u A gA₀ hgA₀ h (cmp C 𝔄 hloc hM S u A gA₀ hgA₀ k ≫ transX C 𝔄 hloc hM h.2) := by
  letI algψ : Algebra (ringOf (fM := fM) C p.1.2) (Wring C (tu C hM S u) k) :=
    ((φW C (tu C hM S u) k).comp (resRing C h.2)).toAlgebra
  constructor
  · have sq := (cmp_isPullback C 𝔄 hloc hM S u A gA₀ hgA₀ k).paste_horiz (transX_isPullback C 𝔄 hloc hM h.2)
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp] at sq
    exact sq
  · intro T _ _ _ _ E' A' gE' hgE' gA' hgA' hgE hgA φ φ' hφ hp hl
    letI algUk : Algebra (ringOf (fM := fM) C k.1.2) T := ((algebraMap (Wring C (tu C hM S u) k) T).comp (φW C (tu C hM S u) k)).toAlgebra
    letI : Algebra (ringOf (fM := fM) C k.1.2) (Wring C (tu C hM S u) k) := (φW C (tu C hM S u) k).toAlgebra
    haveI : IsScalarTower (ringOf (fM := fM) C k.1.2) (Wring C (tu C hM S u) k) T := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
    letI : Algebra (ringOf (fM := fM) C p.1.2) (ringOf (fM := fM) C k.1.2) := (resRing C h.2).toAlgebra
    haveI : IsScalarTower (ringOf (fM := fM) C p.1.2) (ringOf (fM := fM) C k.1.2) T :=
      IsScalarTower.of_algebraMap_eq (fun x =>
        (IsScalarTower.algebraMap_apply (ringOf (fM := fM) C p.1.2) (Wring C (tu C hM S u) k) T x).trans rfl)
    have hgEk : FakeEllipticCurve.IsPullbackVia (algebraMap (ringOf (fM := fM) C k.1.2) T) (uof C hM k.1.2).1 E'
        (gE' ≫ kU C hM S u k) :=
      isPullbackVia_comp _ _ _ _ _ _ _ (kU_via C hM S u k) hgE'
    have hgAk : FakeEllipticCurve.IsPullbackVia (algebraMap (ringOf (fM := fM) C k.1.2) T) (Aof C 𝔄 k.1.2) A'
        (gA' ≫ kA C 𝔄 hM S u A gA₀ hgA₀ k) :=
      isPullbackVia_comp _ _ _ _ _ _ _ (kA_via C 𝔄 hM S u A gA₀ hgA₀ k) hgA'
    have hgE₂ : FakeEllipticCurve.IsPullbackVia (algebraMap (ringOf (fM := fM) C p.1.2) T) (uof C hM p.1.2).1 E'
        ((gE' ≫ kU C hM S u k) ≫ gU C hM h.2) := isPullbackVia_of_eq (Category.assoc _ _ _).symm hgE
    have hgA₂ : FakeEllipticCurve.IsPullbackVia (algebraMap (ringOf (fM := fM) C p.1.2) T) (Aof C 𝔄 p.1.2) A'
        ((gA' ≫ kA C 𝔄 hM S u A gA₀ hgA₀ k) ≫ gA C 𝔄 h.2) := isPullbackVia_of_eq (Category.assoc _ _ _).symm hgA
    rw [← Category.assoc, (cmp_spec C 𝔄 hloc hM S u A gA₀ hgA₀ k).2 T E' A' gE' hgE' gA' hgA' hgEk hgAk φ φ' hφ hp hl,
      (transX_spec C 𝔄 hloc hM h.2).2 T E' A' _ hgEk _ hgAk hgE₂ hgA₂ φ φ' hφ hp hl]
    exact PairDatum.pt_congr _ E' A' (Category.assoc _ _ _) hgE₂ hgE (Category.assoc _ _ _) hgA₂ hgA φ φ' hφ hp hl

include hrig in

theorem psiSpec_rcan_cmp {k p : SecIdx C (tu C hM S u)} (h : k ≤ p) :
    PsiSpec C 𝔄 hloc hM S u A gA₀ hgA₀ h (rcan C 𝔄 hloc hM S u A gA₀ hgA₀ h ≫ cmp C 𝔄 hloc hM S u A gA₀ hgA₀ p) := by
  letI algψ : Algebra (ringOf (fM := fM) C p.1.2) (Wring C (tu C hM S u) k) :=
    ((φW C (tu C hM S u) k).comp (resRing C h.2)).toAlgebra
  constructor
  · have sq := (rcan_isPullback C 𝔄 hloc hM S u A gA₀ hgA₀ h).paste_horiz (cmp_isPullback C 𝔄 hloc hM S u A gA₀ hgA₀ p)
    rw [spec_φW_res, ← Spec.map_comp, ← CommRingCat.ofHom_comp] at sq
    exact sq
  · intro T _ _ _ _ E' A' gE' hgE' gA' hgA' hgE hgA φ φ' hφ hp hl
    letI algP : Algebra (Wring C (tu C hM S u) p) T :=
      ((algebraMap (Wring C (tu C hM S u) k) T).comp (ρW C (tu C hM S u) h)).toAlgebra
    letI : Algebra (Wring C (tu C hM S u) p) (Wring C (tu C hM S u) k) := (ρW C (tu C hM S u) h).toAlgebra
    haveI : IsScalarTower (Wring C (tu C hM S u) p) (Wring C (tu C hM S u) k) T := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
    letI : Algebra (ringOf (fM := fM) C p.1.2) (Wring C (tu C hM S u) p) := (φW C (tu C hM S u) p).toAlgebra
    haveI : IsScalarTower (ringOf (fM := fM) C p.1.2) (Wring C (tu C hM S u) p) T :=
      IsScalarTower.of_algebraMap_eq (fun x => by
        rw [IsScalarTower.algebraMap_apply (ringOf (fM := fM) C p.1.2) (Wring C (tu C hM S u) k) T x]
        change algebraMap (Wring C (tu C hM S u) k) T (((φW C (tu C hM S u) k).comp (resRing C h.2)) x) =
          algebraMap (Wring C (tu C hM S u) k) T ((ρW C (tu C hM S u) h) ((φW C (tu C hM S u) p) x))
        rw [← ρW_comp_φW C hM S u h]; rfl)
    have hgEp : FakeEllipticCurve.IsPullbackVia (algebraMap (Wring C (tu C hM S u) p) T) (up C hM S u p).1 E'
        (gE' ≫ mU C hM S u h) :=
      isPullbackVia_comp _ _ _ _ _ _ _ (mU_via C hM S u h) hgE'
    have hgAp : FakeEllipticCurve.IsPullbackVia (algebraMap (Wring C (tu C hM S u) p) T) (Ap C hM S u A p) A'
        (gA' ≫ mA C hM S u A h) :=
      isPullbackVia_comp _ _ _ _ _ _ _ (mA_via C hM S u A h) hgA'
    have hgEU : FakeEllipticCurve.IsPullbackVia (algebraMap (ringOf (fM := fM) C p.1.2) T) (uof C hM p.1.2).1 E'
        ((gE' ≫ mU C hM S u h) ≫ kU C hM S u p) :=
      isPullbackVia_of_eq (by rw [Category.assoc, mU_kU C hM hrig S u h]) hgE
    have hgAU : FakeEllipticCurve.IsPullbackVia (algebraMap (ringOf (fM := fM) C p.1.2) T) (Aof C 𝔄 p.1.2) A'
        ((gA' ≫ mA C hM S u A h) ≫ kA C 𝔄 hM S u A gA₀ hgA₀ p) :=
      isPullbackVia_of_eq (by rw [Category.assoc, mA_kA]) hgA
    rw [← Category.assoc, (rcan_spec C 𝔄 hloc hM S u A gA₀ hgA₀ h).2 T E' A' gE' hgE' gA' hgA' hgEp hgAp φ φ' hφ hp hl,
      (cmp_spec C 𝔄 hloc hM S u A gA₀ hgA₀ p).2 T E' A' _ hgEp _ hgAp hgEU hgAU φ φ' hφ hp hl]
    exact PairDatum.pt_congr _ E' A' (by rw [Category.assoc, mU_kU C hM hrig S u h]) hgEU hgE
      (by rw [Category.assoc, mA_kA]) hgAU hgA φ φ' hφ hp hl

include hrig in

theorem cmp_compat {k p : SecIdx C (tu C hM S u)} (h : k ≤ p)
    (rr : (Dp C 𝔄 hloc hM S u A gA₀ hgA₀ k).X ⟶ (Dp C 𝔄 hloc hM S u A gA₀ hgA₀ p).X)
    (hrr : rr ≫ iota C 𝔄 hloc hM S u A gA₀ hgA₀ X ξ pt hX p = iota C 𝔄 hloc hM S u A gA₀ hgA₀ X ξ pt hX k) :
    rr ≫ cmp C 𝔄 hloc hM S u A gA₀ hgA₀ p = cmp C 𝔄 hloc hM S u A gA₀ hgA₀ k ≫ transX C 𝔄 hloc hM h.2 := by
  obtain rfl : rr = rcan C 𝔄 hloc hM S u A gA₀ hgA₀ h := by
    rw [← cancel_mono (iota C 𝔄 hloc hM S u A gA₀ hgA₀ X ξ pt hX p), hrr, rcan_iota C 𝔄 hloc hM hrig S u A gA₀ hgA₀ X ξ pt hX h]
  exact psiSpec_unique C 𝔄 hloc hM S u A gA₀ hgA₀ h _ _ (psiSpec_rcan_cmp C 𝔄 hloc hM hrig S u A gA₀ hgA₀ h)
    (psiSpec_cmp_transX C 𝔄 hloc hM S u A gA₀ hgA₀ h)

def localComparison : LocalComparison C (tu C hM S u) (chartData C 𝔄 hloc hM hrig) ξ where
  ZW p := (Dp C 𝔄 hloc hM S u A gA₀ hgA₀ p).X
  ιW p := iota C 𝔄 hloc hM S u A gA₀ hgA₀ X ξ pt hX p
  ζW p := (Dp C 𝔄 hloc hM S u A gA₀ hgA₀ p).ξ
  sq p := iota_sq C 𝔄 hloc hM S u A gA₀ hgA₀ X ξ pt hX p
  c p := cmp C 𝔄 hloc hM S u A gA₀ hgA₀ p
  c_isPullback p := cmp_isPullback C 𝔄 hloc hM S u A gA₀ hgA₀ p
  compat h rr hrr := cmp_compat C 𝔄 hloc hM hrig S u A gA₀ hgA₀ X ξ pt hX h rr hrr

def kappaD : X ⟶ Xd C 𝔄 hloc hM hrig :=
  LocalComparison.kappa C (tu C hM S u) (localComparison C 𝔄 hloc hM hrig S u A gA₀ hgA₀ X ξ pt hX)

theorem kappaD_qd : kappaD C 𝔄 hloc hM hrig S u A gA₀ hgA₀ X ξ pt hX ≫ qd C 𝔄 hloc hM hrig = ξ ≫ tu C hM S u :=
  LocalComparison.kappa_qR C _ _

theorem kappaD_B1 :
    kappaD C 𝔄 hloc hM hrig S u A gA₀ hgA₀ X ξ pt hX ≫ qd C 𝔄 hloc hM hrig ≫
        pullback.fst fM (Spec.map (CommRingCat.ofHom (algebraMap 𝒪 C))) =
      ξ ≫ (ptF S (Spec.map (CommRingCat.ofHom (algebraMap 𝒪 S))) u).1 ∧
    kappaD C 𝔄 hloc hM hrig S u A gA₀ hgA₀ X ξ pt hX ≫ qd C 𝔄 hloc hM hrig ≫
        pullback.snd fM (Spec.map (CommRingCat.ofHom (algebraMap 𝒪 C))) =
      ξ ≫ Spec.map (CommRingCat.ofHom (algebraMap C S)) := by
  constructor
  · rw [← Category.assoc, kappaD_qd, Category.assoc, ptFC_fst]
  · rw [← Category.assoc, kappaD_qd, Category.assoc]
    exact congrArg (ξ ≫ ·) (ptFC_snd C hM S u)

theorem kappaD_isPullback :
    IsPullback (kappaD C 𝔄 hloc hM hrig S u A gA₀ hgA₀ X ξ pt hX) ξ (qd C 𝔄 hloc hM hrig) (tu C hM S u) :=
  LocalComparison.isPullback_kappa C _ _

theorem kappaD_B2 (T : Scheme.{0}) (x : T ⟶ Xd C 𝔄 hloc hM hrig) (t : T ⟶ Spec (CommRingCat.of S))
    (h1 : x ≫ qd C 𝔄 hloc hM hrig ≫ pullback.fst fM (Spec.map (CommRingCat.ofHom (algebraMap 𝒪 C))) =
      t ≫ (ptF S (Spec.map (CommRingCat.ofHom (algebraMap 𝒪 S))) u).1)
    (h2 : x ≫ qd C 𝔄 hloc hM hrig ≫ pullback.snd fM (Spec.map (CommRingCat.ofHom (algebraMap 𝒪 C))) =
      t ≫ Spec.map (CommRingCat.ofHom (algebraMap C S))) :
    ∃! y : T ⟶ X, y ≫ kappaD C 𝔄 hloc hM hrig S u A gA₀ hgA₀ X ξ pt hX = x ∧ y ≫ ξ = t := by
  have hx : x ≫ qd C 𝔄 hloc hM hrig = t ≫ tu C hM S u := by
    apply pullback.hom_ext
    · rw [Category.assoc, h1, Category.assoc, ptFC_fst]
    · rw [Category.assoc, h2, Category.assoc]
      exact (congrArg (t ≫ ·) (ptFC_snd C hM S u)).symm
  have H := kappaD_isPullback C 𝔄 hloc hM hrig S u A gA₀ hgA₀ X ξ pt hX
  refine ⟨H.lift x t hx, ⟨H.lift_fst _ _ _, H.lift_snd _ _ _⟩, ?_⟩
  rintro y ⟨hy1, hy2⟩
  exact H.hom_ext (by rw [hy1, H.lift_fst]) (by rw [hy2, H.lift_snd])

theorem iota_kappaD (p : SecIdx C (tu C hM S u)) :
    iota C 𝔄 hloc hM S u A gA₀ hgA₀ X ξ pt hX p ≫ kappaD C 𝔄 hloc hM hrig S u A gA₀ hgA₀ X ξ pt hX =
      cmp C 𝔄 hloc hM S u A gA₀ hgA₀ p ≫ ιR C (chartData C 𝔄 hloc hM hrig) p.1.2 :=
  LocalComparison.ιW_kappa C _ _ p

theorem kappaD_unique (κ' : X ⟶ Xd C 𝔄 hloc hM hrig)
    (h : ∀ p, iota C 𝔄 hloc hM S u A gA₀ hgA₀ X ξ pt hX p ≫ κ' = cmp C 𝔄 hloc hM S u A gA₀ hgA₀ p ≫ ιR C (chartData C 𝔄 hloc hM hrig) p.1.2) :
    κ' = kappaD C 𝔄 hloc hM hrig S u A gA₀ hgA₀ X ξ pt hX :=
  LocalComparison.kappa_unique C _ _ κ' h

end LocalE
p2m_reactivate "P2MW.S_CerednikDrinfeld_QM_IsFineModuli_exists_locallyOfFinitePresentation_forall_representsOn_hom_isPullback_of_forall_withFullLevel.RelRepGlue"

end RelRepGlue
p2m_reactivate "P2MW.S_CerednikDrinfeld_QM_IsFineModuli_exists_locallyOfFinitePresentation_forall_representsOn_hom_isPullback_of_forall_withFullLevel.RelRepGlue"

end
p2m_reactivate "P2MW.S_CerednikDrinfeld_QM_IsFineModuli_exists_locallyOfFinitePresentation_forall_representsOn_hom_isPullback_of_forall_withFullLevel.RelRepGlue"

set_option autoImplicit false

open scoped TensorProduct Quaternion NumberField
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry QuaternionAlgebra CerednikDrinfeld CerednikDrinfeld.QM NeronModelInfra GoodReductionJacobian

noncomputable section

namespace RelRepGlue

variable {N : ℕ} {𝒪 : Type} [CommRing 𝒪]
  {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} {n : ℕ} {M : Scheme.{0}} {fM : M ⟶ Spec (CommRingCat.of 𝒪)}
  {ptF : ∀ (S : Type) [CommRing S] (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of 𝒪)),
    FakeEllipticCurve.WithFullLevel Λ N n S → SchemeHomOver s fM}
  (C : Type) [CommRing C] [Algebra 𝒪 C]

section GenE

variable (𝔄 : FakeEllipticCurve Λ N C) {r d : ℕ} (hloc : HLoc (𝒪 := 𝒪) (n := n) C r d 𝔄) (hM : IsFineModuli Λ N n M fM ptF)
  (hrig : HRig Λ N n C)
  (S : Type) [CommRing S] [Algebra C S] [Algebra 𝒪 S] [IsScalarTower 𝒪 C S]
  (u : FakeEllipticCurve.WithFullLevel Λ N n S)
  (A : FakeEllipticCurve Λ N S) (gA₀ : A.A ⟶ 𝔄.A) (hgA₀ : FakeEllipticCurve.IsPullbackVia (algebraMap C S) 𝔄 A gA₀)
  (X : Scheme.{0}) (ξ : X ⟶ Spec (CommRingCat.of S))
  (pt : FakeEllipticCurve.IsogenyPair.PtFamily r d u.1 A ξ)
  (hX : FakeEllipticCurve.IsogenyPair.RepresentsOn r d u.1 A ξ pt)

  (B : Type) [CommRing B] [Algebra S B] [Algebra C B] [Algebra 𝒪 B] [IsScalarTower C S B] [IsScalarTower 𝒪 C B]
  (v : FakeEllipticCurve.WithFullLevel Λ N n B) (gv : v.1.A ⟶ u.1.A)
  (hgv : FakeEllipticCurve.IsPullbackVia (algebraMap S B) u.1 v.1 gv)
  (AB : FakeEllipticCurve Λ N B) (kB : AB.A ⟶ A.A) (hkB : FakeEllipticCurve.IsPullbackVia (algebraMap S B) A AB kB)
  (DB : PairDatum (N := N) (Λ := Λ) r d v.1 AB)

def GenIotaSpec (e : DB.X ⟶ X) : Prop :=
  CategoryTheory.IsPullback e DB.ξ ξ (Spec.map (CommRingCat.ofHom (algebraMap S B))) ∧
    ∀ (T : Type) [CommRing T] [Algebra B T] [Algebra S T] [IsScalarTower S B T]
      (E' A' : FakeEllipticCurve Λ N T)
      (gE' : E'.A ⟶ v.1.A) (hgE' : FakeEllipticCurve.IsPullbackVia (algebraMap B T) v.1 E' gE')
      (gA' : A'.A ⟶ AB.A) (hgA' : FakeEllipticCurve.IsPullbackVia (algebraMap B T) AB A' gA')
      (hgE : FakeEllipticCurve.IsPullbackVia (algebraMap S T) u.1 E' (gE' ≫ gv))
      (hgA : FakeEllipticCurve.IsPullbackVia (algebraMap S T) A A' (gA' ≫ kB))
      (φ : E'.A ⟶ A'.A) (φ' : A'.A ⟶ E'.A) (hφ : φ ≫ A'.f = E'.f)
      (hp : FakeEllipticCurve.IsIsogenyPair (r ^ d) E' A' φ φ') (hl : FakeEllipticCurve.PreservesLevel E' A' φ hφ),
      (DB.pt T E' A' gE' hgE' gA' hgA' φ φ' hφ hp hl).1 ≫ e = (pt T E' A' (gE' ≫ gv) hgE (gA' ≫ kB) hgA φ φ' hφ hp hl).1

include hX hgv hkB in
theorem existsUnique_genIota : ∃! e : DB.X ⟶ X, GenIotaSpec S u A X ξ pt B v gv AB kB DB e :=
  CerednikDrinfeld.QM.FakeEllipticCurve.IsogenyPair.existsUnique_hom_isPullback_of_representsOn r d
    S u.1 A X ξ pt hX B v.1 AB gv hgv kB hkB DB.X DB.ξ DB.pt DB.rep

def genIota : DB.X ⟶ X := (existsUnique_genIota S u A X ξ pt hX B v gv hgv AB kB hkB DB).exists.choose

theorem genIota_spec : GenIotaSpec S u A X ξ pt B v gv AB kB DB (genIota S u A X ξ pt hX B v gv hgv AB kB hkB DB) :=
  (existsUnique_genIota S u A X ξ pt hX B v gv hgv AB kB hkB DB).exists.choose_spec

theorem genIota_unique (e : DB.X ⟶ X) (he : GenIotaSpec S u A X ξ pt B v gv AB kB DB e) :
    e = genIota S u A X ξ pt hX B v gv hgv AB kB hkB DB :=
  (existsUnique_genIota S u A X ξ pt hX B v gv hgv AB kB hkB DB).unique he (genIota_spec S u A X ξ pt hX B v gv hgv AB kB hkB DB)

theorem genIota_isPullback :
    IsPullback (genIota S u A X ξ pt hX B v gv hgv AB kB hkB DB) DB.ξ ξ (Spec.map (CommRingCat.ofHom (algebraMap S B))) :=
  (genIota_spec S u A X ξ pt hX B v gv hgv AB kB hkB DB).1

scoped instance genIota_isOpenImmersion_of [IsOpenImmersion (Spec.map (CommRingCat.ofHom (algebraMap S B)))] :
    IsOpenImmersion (genIota S u A X ξ pt hX B v gv hgv AB kB hkB DB) :=
  MorphismProperty.of_isPullback (genIota_isPullback S u A X ξ pt hX B v gv hgv AB kB hkB DB).flip inferInstance

variable (U : (MC fM C).affineOpens) (ψ : ringOf (fM := fM) C U →+* B)
  (hψ : Spec.map (CommRingCat.ofHom ψ) ≫ chartι C U = (ptFC C hM B v).1)
  (hψC : ψ.comp (algebraMap C (ringOf (fM := fM) C U)) = algebraMap C B)

def ψAlgHom : ringOf (fM := fM) C U →ₐ[C] B :=
  { toRingHom := ψ, commutes' := fun c => RingHom.congr_fun hψC c }

@[scoped simp] theorem coe_ψAlgHom : (ψAlgHom C B U ψ hψC : ringOf (fM := fM) C U →+* B) = ψ := RingHom.ext fun _ => rfl

include hψ hψC in

theorem v_isPullback_uof : FakeEllipticCurve.WithFullLevel.IsPullback ψ (uof C hM U) v := by
  rw [← coe_ψAlgHom C B U ψ hψC]
  exact isPullback_uof_of_ptFC_eq C hM U (ψAlgHom C B U ψ hψC) v (by rw [coe_ψAlgHom, hψ])

def kvU : v.1.A ⟶ (uof C hM U).1.A := (v_isPullback_uof C hM B v U ψ hψ hψC).choose

theorem kvU_via : FakeEllipticCurve.IsPullbackVia ψ (uof C hM U).1 v.1 (kvU C hM B v U ψ hψ hψC) := by
  obtain ⟨hg, hmul, hact, hlev, -⟩ := (v_isPullback_uof C hM B v U ψ hψ hψC).choose_spec
  exact ⟨hg, hmul, hact, hlev⟩

theorem kvU_P : (v.2.P).1 ≫ kvU C hM B v U ψ hψ hψC = Spec.map (CommRingCat.ofHom ψ) ≫ ((uof C hM U).2.P).1 :=
  (v_isPullback_uof C hM B v U ψ hψ hψC).choose_spec.2.2.2.2

include hrig in

theorem kvU_unique (k' : v.1.A ⟶ (uof C hM U).1.A) (h1 : FakeEllipticCurve.IsPullbackVia ψ (uof C hM U).1 v.1 k')
    (h2 : (v.2.P).1 ≫ k' = Spec.map (CommRingCat.ofHom ψ) ≫ ((uof C hM U).2.P).1) : k' = kvU C hM B v U ψ hψ hψC :=
  comparison_unique C hrig ψ (uof C hM U) v _ _ h1 h2 (kvU_via C hM B v U ψ hψ hψC) (kvU_P C hM B v U ψ hψ hψC)

include hgA₀ hkB in

theorem kB_gA₀_via : FakeEllipticCurve.IsPullbackVia (algebraMap C B) 𝔄 AB (kB ≫ gA₀) :=
  isPullbackVia_congr (IsScalarTower.algebraMap_eq C S B).symm _ _ _ (isPullbackVia_comp _ _ _ _ _ _ _ hgA₀ hkB)

include hgA₀ hkB hψC in

theorem exists_kAU :
    ∃ k : AB.A ⟶ (Aof (fM := fM) C 𝔄 U).A,
      k ≫ gAof C 𝔄 U = kB ≫ gA₀ ∧ k ≫ (Aof C 𝔄 U).f = AB.f ≫ Spec.map (CommRingCat.ofHom ψ) ∧
      (∀ k' : AB.A ⟶ (Aof (fM := fM) C 𝔄 U).A, k' ≫ gAof C 𝔄 U = kB ≫ gA₀ →
        k' ≫ (Aof C 𝔄 U).f = AB.f ≫ Spec.map (CommRingCat.ofHom ψ) → k' = k) ∧
      FakeEllipticCurve.IsPullbackVia ψ (Aof C 𝔄 U) AB k :=
  FakeEllipticCurve.IsPullbackVia.exists_comp_eq_and_isPullbackVia_of_comp_eq
    (algebraMap C (ringOf (fM := fM) C U)) ψ (algebraMap C B) hψC 𝔄 (Aof C 𝔄 U) AB
    (gAof C 𝔄 U) (gAof_spec C 𝔄 U).1 (fun t' P h => (gAof_spec C 𝔄 U).2 t' P h) (kB ≫ gA₀)
    (kB_gA₀_via C 𝔄 S A gA₀ hgA₀ B AB kB hkB)

def kAU : AB.A ⟶ (Aof (fM := fM) C 𝔄 U).A := (exists_kAU C 𝔄 S A gA₀ hgA₀ B AB kB hkB U ψ hψC).choose

theorem kAU_gAof : kAU C 𝔄 S A gA₀ hgA₀ B AB kB hkB U ψ hψC ≫ gAof C 𝔄 U = kB ≫ gA₀ :=
  (exists_kAU C 𝔄 S A gA₀ hgA₀ B AB kB hkB U ψ hψC).choose_spec.1

theorem kAU_over : kAU C 𝔄 S A gA₀ hgA₀ B AB kB hkB U ψ hψC ≫ (Aof C 𝔄 U).f = AB.f ≫ Spec.map (CommRingCat.ofHom ψ) :=
  (exists_kAU C 𝔄 S A gA₀ hgA₀ B AB kB hkB U ψ hψC).choose_spec.2.1

theorem kAU_unique (k' : AB.A ⟶ (Aof (fM := fM) C 𝔄 U).A) (h1 : k' ≫ gAof C 𝔄 U = kB ≫ gA₀)
    (h2 : k' ≫ (Aof C 𝔄 U).f = AB.f ≫ Spec.map (CommRingCat.ofHom ψ)) : k' = kAU C 𝔄 S A gA₀ hgA₀ B AB kB hkB U ψ hψC :=
  (exists_kAU C 𝔄 S A gA₀ hgA₀ B AB kB hkB U ψ hψC).choose_spec.2.2.1 k' h1 h2

theorem kAU_via : FakeEllipticCurve.IsPullbackVia ψ (Aof C 𝔄 U) AB (kAU C 𝔄 S A gA₀ hgA₀ B AB kB hkB U ψ hψC) :=
  (exists_kAU C 𝔄 S A gA₀ hgA₀ B AB kB hkB U ψ hψC).choose_spec.2.2.2

def GenCSpec (e : DB.X ⟶ (DU C 𝔄 hloc hM U).X) : Prop :=
  letI : Algebra (ringOf (fM := fM) C U) B := ψ.toAlgebra
  CategoryTheory.IsPullback e DB.ξ (DU C 𝔄 hloc hM U).ξ
      (Spec.map (CommRingCat.ofHom (algebraMap (ringOf (fM := fM) C U) B))) ∧
    ∀ (T : Type) [CommRing T] [Algebra B T] [Algebra (ringOf (fM := fM) C U) T] [IsScalarTower (ringOf (fM := fM) C U) B T]
      (E' A' : FakeEllipticCurve Λ N T)
      (gE' : E'.A ⟶ v.1.A) (hgE' : FakeEllipticCurve.IsPullbackVia (algebraMap B T) v.1 E' gE')
      (gA' : A'.A ⟶ AB.A) (hgA' : FakeEllipticCurve.IsPullbackVia (algebraMap B T) AB A' gA')
      (hgE : FakeEllipticCurve.IsPullbackVia (algebraMap (ringOf (fM := fM) C U) T) (uof C hM U).1 E'
        (gE' ≫ kvU C hM B v U ψ hψ hψC))
      (hgA : FakeEllipticCurve.IsPullbackVia (algebraMap (ringOf (fM := fM) C U) T) (Aof C 𝔄 U) A'
        (gA' ≫ kAU C 𝔄 S A gA₀ hgA₀ B AB kB hkB U ψ hψC))
      (φ : E'.A ⟶ A'.A) (φ' : A'.A ⟶ E'.A) (hφ : φ ≫ A'.f = E'.f)
      (hp : FakeEllipticCurve.IsIsogenyPair (r ^ d) E' A' φ φ') (hl : FakeEllipticCurve.PreservesLevel E' A' φ hφ),
      (DB.pt T E' A' gE' hgE' gA' hgA' φ φ' hφ hp hl).1 ≫ e =
        ((DU C 𝔄 hloc hM U).pt T E' A' (gE' ≫ kvU C hM B v U ψ hψ hψC) hgE
          (gA' ≫ kAU C 𝔄 S A gA₀ hgA₀ B AB kB hkB U ψ hψC) hgA φ φ' hφ hp hl).1

theorem existsUnique_genC : ∃! e : DB.X ⟶ (DU C 𝔄 hloc hM U).X, GenCSpec C 𝔄 hloc hM S A gA₀ hgA₀ B v AB kB hkB DB U ψ hψ hψC e := by
  letI : Algebra (ringOf (fM := fM) C U) B := ψ.toAlgebra
  exact CerednikDrinfeld.QM.FakeEllipticCurve.IsogenyPair.existsUnique_hom_isPullback_of_representsOn r d
    (ringOf (fM := fM) C U) (uof C hM U).1 (Aof C 𝔄 U)
    (DU C 𝔄 hloc hM U).X (DU C 𝔄 hloc hM U).ξ (DU C 𝔄 hloc hM U).pt (DU C 𝔄 hloc hM U).rep
    B v.1 AB (kvU C hM B v U ψ hψ hψC) (kvU_via C hM B v U ψ hψ hψC)
    (kAU C 𝔄 S A gA₀ hgA₀ B AB kB hkB U ψ hψC) (kAU_via C 𝔄 S A gA₀ hgA₀ B AB kB hkB U ψ hψC)
    DB.X DB.ξ DB.pt DB.rep

def genC : DB.X ⟶ (DU C 𝔄 hloc hM U).X :=
  (existsUnique_genC C 𝔄 hloc hM S A gA₀ hgA₀ B v AB kB hkB DB U ψ hψ hψC).exists.choose

theorem genC_spec : GenCSpec C 𝔄 hloc hM S A gA₀ hgA₀ B v AB kB hkB DB U ψ hψ hψC
    (genC C 𝔄 hloc hM S A gA₀ hgA₀ B v AB kB hkB DB U ψ hψ hψC) :=
  (existsUnique_genC C 𝔄 hloc hM S A gA₀ hgA₀ B v AB kB hkB DB U ψ hψ hψC).exists.choose_spec

theorem genC_unique (e : DB.X ⟶ (DU C 𝔄 hloc hM U).X) (he : GenCSpec C 𝔄 hloc hM S A gA₀ hgA₀ B v AB kB hkB DB U ψ hψ hψC e) :
    e = genC C 𝔄 hloc hM S A gA₀ hgA₀ B v AB kB hkB DB U ψ hψ hψC :=
  (existsUnique_genC C 𝔄 hloc hM S A gA₀ hgA₀ B v AB kB hkB DB U ψ hψ hψC).unique he
    (genC_spec C 𝔄 hloc hM S A gA₀ hgA₀ B v AB kB hkB DB U ψ hψ hψC)

theorem genC_isPullback :
    IsPullback (genC C 𝔄 hloc hM S A gA₀ hgA₀ B v AB kB hkB DB U ψ hψ hψC) DB.ξ (DU C 𝔄 hloc hM U).ξ
      (Spec.map (CommRingCat.ofHom ψ)) :=
  (genC_spec C 𝔄 hloc hM S A gA₀ hgA₀ B v AB kB hkB DB U ψ hψ hψC).1

end GenE
p2m_reactivate "P2MW.S_CerednikDrinfeld_QM_IsFineModuli_exists_locallyOfFinitePresentation_forall_representsOn_hom_isPullback_of_forall_withFullLevel.RelRepGlue"

section Bridges

variable (𝔄 : FakeEllipticCurve Λ N C) {r d : ℕ} (hloc : HLoc (𝒪 := 𝒪) (n := n) C r d 𝔄) (hM : IsFineModuli Λ N n M fM ptF)
  (hrig : HRig Λ N n C)
  (S : Type) [CommRing S] [Algebra C S] [Algebra 𝒪 S] [IsScalarTower 𝒪 C S]
  (u : FakeEllipticCurve.WithFullLevel Λ N n S)
  (A : FakeEllipticCurve Λ N S) (gA₀ : A.A ⟶ 𝔄.A) (hgA₀ : FakeEllipticCurve.IsPullbackVia (algebraMap C S) 𝔄 A gA₀)
  (X : Scheme.{0}) (ξ : X ⟶ Spec (CommRingCat.of S))
  (pt : FakeEllipticCurve.IsogenyPair.PtFamily r d u.1 A ξ)
  (hX : FakeEllipticCurve.IsogenyPair.RepresentsOn r d u.1 A ξ pt)

theorem spec_φW_chartι_eq_ptFC_up (p : SecIdx C (tu C hM S u)) :
    Spec.map (CommRingCat.ofHom (φW C (tu C hM S u) p)) ≫ chartι C p.1.2 =
      (ptFC C hM (Wring C (tu C hM S u) p) (up C hM S u p)).1 := by
  rw [spec_φW_chartι, ptFC_up, spec_algebraMap_W]

theorem φW_comp_algebraMap_up (p : SecIdx C (tu C hM S u)) :
    (φW C (tu C hM S u) p).comp (algebraMap C (ringOf (fM := fM) C p.1.2)) = algebraMap C (Wring C (tu C hM S u) p) :=
  φW_comp_algebraMap C (tu C hM S u) (tu_snd C hM S u) p

theorem genIota_eq_iota (p : SecIdx C (tu C hM S u)) :
    genIota S u A X ξ pt hX (Wring C (tu C hM S u) p) (up C hM S u p) (gp C hM S u p) (gp_via C hM S u p)
        (Ap C hM S u A p) (hAp C hM S u A p) (hAp_via C hM S u A p) (Dp C 𝔄 hloc hM S u A gA₀ hgA₀ p) =
      iota C 𝔄 hloc hM S u A gA₀ hgA₀ X ξ pt hX p :=
  iota_unique C 𝔄 hloc hM S u A gA₀ hgA₀ X ξ pt hX p _
    (genIota_spec S u A X ξ pt hX (Wring C (tu C hM S u) p) (up C hM S u p) (gp C hM S u p) (gp_via C hM S u p)
      (Ap C hM S u A p) (hAp C hM S u A p) (hAp_via C hM S u A p) (Dp C 𝔄 hloc hM S u A gA₀ hgA₀ p))

include hrig in

theorem kvU_eq_kU (p : SecIdx C (tu C hM S u)) :
    kvU C hM (Wring C (tu C hM S u) p) (up C hM S u p) p.1.2 (φW C (tu C hM S u) p)
        (spec_φW_chartι_eq_ptFC_up C hM S u p) (φW_comp_algebraMap_up C hM S u p) =
      kU C hM S u p :=
  (kvU_unique C hM hrig (Wring C (tu C hM S u) p) (up C hM S u p) p.1.2 (φW C (tu C hM S u) p)
    (spec_φW_chartι_eq_ptFC_up C hM S u p) (φW_comp_algebraMap_up C hM S u p) (kU C hM S u p) (kU_via C hM S u p)
    (kU_P C hM S u p)).symm

theorem kAU_eq_kA (p : SecIdx C (tu C hM S u)) :
    kAU C 𝔄 S A gA₀ hgA₀ (Wring C (tu C hM S u) p) (Ap C hM S u A p) (hAp C hM S u A p) (hAp_via C hM S u A p) p.1.2
        (φW C (tu C hM S u) p) (φW_comp_algebraMap_up C hM S u p) =
      kA C 𝔄 hM S u A gA₀ hgA₀ p :=
  (kAU_unique C 𝔄 S A gA₀ hgA₀ (Wring C (tu C hM S u) p) (Ap C hM S u A p) (hAp C hM S u A p) (hAp_via C hM S u A p) p.1.2
    (φW C (tu C hM S u) p) (φW_comp_algebraMap_up C hM S u p) (kA C 𝔄 hM S u A gA₀ hgA₀ p)
    (kA_gAof C 𝔄 hM S u A gA₀ hgA₀ p) (kA_over C 𝔄 hM S u A gA₀ hgA₀ p)).symm

include hrig in

theorem genC_eq_cmp (p : SecIdx C (tu C hM S u)) :
    genC C 𝔄 hloc hM S A gA₀ hgA₀ (Wring C (tu C hM S u) p) (up C hM S u p) (Ap C hM S u A p) (hAp C hM S u A p)
        (hAp_via C hM S u A p) (Dp C 𝔄 hloc hM S u A gA₀ hgA₀ p) p.1.2 (φW C (tu C hM S u) p)
        (spec_φW_chartι_eq_ptFC_up C hM S u p) (φW_comp_algebraMap_up C hM S u p) =
      cmp C 𝔄 hloc hM S u A gA₀ hgA₀ p := by
  apply cmp_unique
  have hs := genC_spec C 𝔄 hloc hM S A gA₀ hgA₀ (Wring C (tu C hM S u) p) (up C hM S u p) (Ap C hM S u A p)
    (hAp C hM S u A p) (hAp_via C hM S u A p) (Dp C 𝔄 hloc hM S u A gA₀ hgA₀ p) p.1.2 (φW C (tu C hM S u) p)
    (spec_φW_chartι_eq_ptFC_up C hM S u p) (φW_comp_algebraMap_up C hM S u p)
  refine ⟨hs.1, ?_⟩
  intro T _ _ _ _ E' A' gE' hgE' gA' hgA' hgE hgA φ φ' hφ hp hl
  have hgEU := isPullbackVia_of_eq (congrArg (gE' ≫ ·) (kvU_eq_kU C hM hrig S u p).symm) hgE
  have hgAU := isPullbackVia_of_eq (congrArg (gA' ≫ ·) (kAU_eq_kA C 𝔄 hM S u A gA₀ hgA₀ p).symm) hgA
  rw [hs.2 T E' A' gE' hgE' gA' hgA' hgEU hgAU φ φ' hφ hp hl]
  exact PairDatum.pt_congr _ E' A' (congrArg (gE' ≫ ·) (kvU_eq_kU C hM hrig S u p)) hgEU hgE
    (congrArg (gA' ≫ ·) (kAU_eq_kA C 𝔄 hM S u A gA₀ hgA₀ p)) hgAU hgA φ φ' hφ hp hl

end Bridges
p2m_reactivate "P2MW.S_CerednikDrinfeld_QM_IsFineModuli_exists_locallyOfFinitePresentation_forall_representsOn_hom_isPullback_of_forall_withFullLevel.RelRepGlue"

end RelRepGlue
p2m_reactivate "P2MW.S_CerednikDrinfeld_QM_IsFineModuli_exists_locallyOfFinitePresentation_forall_representsOn_hom_isPullback_of_forall_withFullLevel.RelRepGlue"

end
p2m_reactivate "P2MW.S_CerednikDrinfeld_QM_IsFineModuli_exists_locallyOfFinitePresentation_forall_representsOn_hom_isPullback_of_forall_withFullLevel.RelRepGlue"

set_option autoImplicit false

open scoped TensorProduct Quaternion NumberField
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry QuaternionAlgebra CerednikDrinfeld CerednikDrinfeld.QM NeronModelInfra GoodReductionJacobian

noncomputable section

namespace RelRepGlue

variable {N : ℕ} {𝒪 : Type} [CommRing 𝒪]
  {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} {n : ℕ} {M : Scheme.{0}} {fM : M ⟶ Spec (CommRingCat.of 𝒪)}
  {ptF : ∀ (S : Type) [CommRing S] (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of 𝒪)),
    FakeEllipticCurve.WithFullLevel Λ N n S → SchemeHomOver s fM}
  (C : Type) [CommRing C] [Algebra 𝒪 C]

section ChartEq

variable (𝔄 : FakeEllipticCurve Λ N C) {r d : ℕ} (hloc : HLoc (𝒪 := 𝒪) (n := n) C r d 𝔄) (hM : IsFineModuli Λ N n M fM ptF)
  (hrig : HRig Λ N n C)
  (S : Type) [CommRing S] [Algebra C S] [Algebra 𝒪 S] [IsScalarTower 𝒪 C S]
  (u : FakeEllipticCurve.WithFullLevel Λ N n S)
  (A : FakeEllipticCurve Λ N S) (gA₀ : A.A ⟶ 𝔄.A) (hgA₀ : FakeEllipticCurve.IsPullbackVia (algebraMap C S) 𝔄 A gA₀)
  (X : Scheme.{0}) (ξ : X ⟶ Spec (CommRingCat.of S))
  (pt : FakeEllipticCurve.IsogenyPair.PtFamily r d u.1 A ξ)
  (hX : FakeEllipticCurve.IsogenyPair.RepresentsOn r d u.1 A ξ pt)

  (B : Type) [CommRing B] [Algebra S B] [Algebra C B] [Algebra 𝒪 B] [IsScalarTower C S B] [IsScalarTower 𝒪 C B]
  (v : FakeEllipticCurve.WithFullLevel Λ N n B) (gv : v.1.A ⟶ u.1.A)
  (hgv : FakeEllipticCurve.IsPullbackVia (algebraMap S B) u.1 v.1 gv)
  (hgvP : (v.2.P).1 ≫ gv = Spec.map (CommRingCat.ofHom (algebraMap S B)) ≫ (u.2.P).1)
  (AB : FakeEllipticCurve Λ N B) (kB : AB.A ⟶ A.A) (hkB : FakeEllipticCurve.IsPullbackVia (algebraMap S B) A AB kB)
  (DB : PairDatum (N := N) (Λ := Λ) r d v.1 AB)

  (U : (MC fM C).affineOpens) (ψ : ringOf (fM := fM) C U →+* B)
  (hψ : Spec.map (CommRingCat.ofHom ψ) ≫ chartι C U = (ptFC C hM B v).1)
  (hψC : ψ.comp (algebraMap C (ringOf (fM := fM) C U)) = algebraMap C B)

local notation "tS" => tu C hM S u
local notation "tB" => tu C hM B v
local notation "hkB₀" => kB_gA₀_via C 𝔄 S A gA₀ hgA₀ B AB kB hkB
local notation "WrS" => Wring C (tu C hM S u)
local notation "WrB" => Wring C (tu C hM B v)
local notation "upS" => up C hM S u
local notation "upB" => up C hM B v
local notation "gpS" => gp C hM S u
local notation "gpB" => gp C hM B v
local notation "ApS" => Ap C hM S u A
local notation "ApB" => Ap C hM B v AB
local notation "hApS" => hAp C hM S u A
local notation "hApB" => hAp C hM B v AB
local notation "kUS" => kU C hM S u
local notation "kAS" => kA C 𝔄 hM S u A gA₀ hgA₀
local notation "DpS" => Dp C 𝔄 hloc hM S u A gA₀ hgA₀
local notation "DpB" => Dp C 𝔄 hloc hM B v AB (kB ≫ gA₀) hkB₀
local notation "ιS" => iota C 𝔄 hloc hM S u A gA₀ hgA₀ X ξ pt hX
local notation "ιB" => iota C 𝔄 hloc hM B v AB (kB ≫ gA₀) hkB₀ DB.X DB.ξ DB.pt DB.rep
local notation "cS" => cmp C 𝔄 hloc hM S u A gA₀ hgA₀
local notation "genIB" => genIota S u A X ξ pt hX B v gv hgv AB kB hkB DB
local notation "genCB" => genC C 𝔄 hloc hM S A gA₀ hgA₀ B v AB kB hkB DB U ψ hψ hψC
local notation "kvUB" => kvU C hM B v U ψ hψ hψC
local notation "kAUB" => kAU C 𝔄 S A gA₀ hgA₀ B AB kB hkB U ψ hψC

include hgv hgvP in
theorem v_isPullback : FakeEllipticCurve.WithFullLevel.IsPullback (algebraMap S B) u v := by
  obtain ⟨hg, hmul, hact, hlev⟩ := hgv
  exact ⟨gv, hg, hmul, hact, hlev, hgvP⟩

include gv hgv hgvP in

theorem tB_eq : tB = Spec.map (CommRingCat.ofHom (algebraMap S B)) ≫ tS := by
  have h := ptFC_pullback C hM S B (IsScalarTower.toAlgHom C S B) u v
    (by rw [IsScalarTower.coe_toAlgHom]; exact v_isPullback S u B v gv hgv hgvP)
  rw [IsScalarTower.coe_toAlgHom] at h
  exact h

include hψ in
theorem tB_mem (x : ↥(Spec (CommRingCat.of B))) : tB x ∈ (U : (MC fM C).Opens) := by
  rw [show tB = Spec.map (CommRingCat.ofHom ψ) ≫ chartι C U from hψ.symm]
  simp only [chartι, Scheme.Hom.comp_apply]
  exact (U.2.isoSpec.inv (Spec.map (CommRingCat.ofHom ψ) x)).2

structure CIdx where
  WS : (Spec (CommRingCat.of S)).affineOpens
  hWS : (WS : (Spec (CommRingCat.of S)).Opens) ≤ tS ⁻¹ᵁ (U : (MC fM C).Opens)
  W : (Spec (CommRingCat.of B)).affineOpens
  hW : (W : (Spec (CommRingCat.of B)).Opens) ≤
    Spec.map (CommRingCat.ofHom (algebraMap S B)) ⁻¹ᵁ (WS : (Spec (CommRingCat.of S)).Opens)

local notation "CIdx'" => CIdx C hM S u B U

def pOf (j : CIdx') : SecIdx C tS := ⟨(j.WS, U), j.hWS⟩

include gv hgv hgvP in

def sOf (j : CIdx') : SecIdx C tB :=
  ⟨(j.W, U), fun x hx => by
    show tB x ∈ (U : (MC fM C).Opens)
    rw [tB_eq C hM S u B v gv hgv hgvP, Scheme.Hom.comp_apply]
    exact j.hWS (j.hW hx)⟩

local notation "𝓅" => pOf C hM S u B U
local notation "𝓈" => sOf C hM S u B v gv hgv hgvP U

@[scoped simp] theorem pOf_fst (j : CIdx') : (𝓅 j).1 = (j.WS, U) := rfl
@[scoped simp] theorem sOf_fst (j : CIdx') : (𝓈 j).1 = (j.W, U) := rfl

include gv hgv hgvP hψ in
theorem exists_cIdx (x : ↥(Spec (CommRingCat.of B))) : ∃ j : CIdx', x ∈ (j.W : (Spec (CommRingCat.of B)).Opens) := by
  have hxU := tB_mem C hM B v U ψ hψ x
  rw [tB_eq C hM S u B v gv hgv hgvP, Scheme.Hom.comp_apply] at hxU
  obtain ⟨_, ⟨WS, hWS, rfl⟩, hyW, hWO⟩ := (Spec (CommRingCat.of S)).isBasis_affineOpens.exists_subset_of_mem_open
    (show Spec.map (CommRingCat.ofHom (algebraMap S B)) x ∈ (tS ⁻¹ᵁ (U : (MC fM C).Opens)) from hxU)
    (tS ⁻¹ᵁ (U : (MC fM C).Opens)).2
  obtain ⟨_, ⟨W, hW, rfl⟩, hxW, hWO'⟩ := (Spec (CommRingCat.of B)).isBasis_affineOpens.exists_subset_of_mem_open
    (show x ∈ (Spec.map (CommRingCat.ofHom (algebraMap S B)) ⁻¹ᵁ WS) from hyW)
    (Spec.map (CommRingCat.ofHom (algebraMap S B)) ⁻¹ᵁ WS).2
  exact ⟨⟨⟨WS, hWS⟩, hWO, ⟨W, hW⟩, hWO'⟩, hxW⟩

def bCover : (Spec (CommRingCat.of B)).OpenCover :=
  Scheme.Cover.mkOfCovers CIdx' (fun j => (secCover C tB).X (𝓈 j)) (fun j => (secCover C tB).f (𝓈 j))
    (fun x => by
      obtain ⟨j, hx⟩ := exists_cIdx C hM S u B v gv hgv hgvP U ψ hψ x
      exact ⟨j, ⟨x, hx⟩, rfl⟩)

def eB (j : CIdx') : pullback DB.ξ ((secCover C tB).f (𝓈 j)) ⟶ (DpB (𝓈 j)).X :=
  (iota_sq C 𝔄 hloc hM B v AB (kB ≫ gA₀) hkB₀ DB.X DB.ξ DB.pt DB.rep (𝓈 j)).lift
    (pullback.snd _ _ ≫ (isoW C tB (𝓈 j)).hom) (pullback.fst _ _)
    (by rw [pullback.condition, Category.assoc, isoW_hom_Wι])

@[reassoc] theorem eB_ι (j : CIdx') : eB C 𝔄 hloc hM S u A gA₀ hgA₀ B v gv hgv hgvP AB kB hkB DB U j ≫ ιB (𝓈 j) = pullback.fst _ _ :=
  (iota_sq C 𝔄 hloc hM B v AB (kB ≫ gA₀) hkB₀ DB.X DB.ξ DB.pt DB.rep (𝓈 j)).lift_snd _ _ _

include ψ hψ in

theorem hom_ext_ιB {Y : Scheme.{0}} (F G : DB.X ⟶ Y) (h : ∀ j : CIdx', ιB (𝓈 j) ≫ F = ιB (𝓈 j) ≫ G) : F = G := by
  apply Scheme.Cover.hom_ext ((bCover C hM S u B v gv hgv hgvP U ψ hψ).pullback₁ DB.ξ)
  intro j
  change pullback.fst DB.ξ ((secCover C tB).f (𝓈 j)) ≫ F = pullback.fst DB.ξ ((secCover C tB).f (𝓈 j)) ≫ G
  rw [← eB_ι C 𝔄 hloc hM S u A gA₀ hgA₀ B v gv hgv hgvP AB kB hkB DB U j, Category.assoc, Category.assoc, h j]

section OneIdx

local notation "tB_eq'" => tB_eq C hM S u B v gv hgv hgvP

def resSB (j : CIdx') : (j.W : (Spec (CommRingCat.of B)).Opens).toScheme ⟶ (j.WS : (Spec (CommRingCat.of S)).Opens).toScheme :=
  (Spec.map (CommRingCat.ofHom (algebraMap S B))).resLE (j.WS : (Spec (CommRingCat.of S)).Opens)
    (j.W : (Spec (CommRingCat.of B)).Opens) j.hW

def chi (j : CIdx') : WrS (𝓅 j) →+* WrB (𝓈 j) :=
  (Spec.preimage (j.W.2.isoSpec.inv ≫ resSB C hM S u B U j ≫ j.WS.2.isoSpec.hom)).hom

local notation "χ'" => chi C hM S u B v gv hgv hgvP U

theorem spec_chi (j : CIdx') : Spec.map (CommRingCat.ofHom (χ' j)) = j.W.2.isoSpec.inv ≫ resSB C hM S u B U j ≫ j.WS.2.isoSpec.hom :=
  Spec.map_preimage (j.W.2.isoSpec.inv ≫ resSB C hM S u B U j ≫ j.WS.2.isoSpec.hom)

theorem spec_chi_Wι (j : CIdx') : Spec.map (CommRingCat.ofHom (χ' j)) ≫ Wι C tS (𝓅 j) =
    Wι C tB (𝓈 j) ≫ Spec.map (CommRingCat.ofHom (algebraMap S B)) := by
  rw [spec_chi]
  change (j.W.2.isoSpec.inv ≫ resSB C hM S u B U j ≫ j.WS.2.isoSpec.hom) ≫
      (j.WS.2.isoSpec.inv ≫ (j.WS : (Spec (CommRingCat.of S)).Opens).ι) =
    (j.W.2.isoSpec.inv ≫ (j.W : (Spec (CommRingCat.of B)).Opens).ι) ≫ Spec.map (CommRingCat.ofHom (algebraMap S B))
  simp only [resSB, Category.assoc, Iso.hom_inv_id_assoc, Scheme.Hom.resLE_comp_ι]

local notation "spec_χ_Wι'" => spec_chi_Wι C hM S u B v gv hgv hgvP U

theorem chi_comp_algebraMap (j : CIdx') :
    (χ' j).comp (algebraMap S (WrS (𝓅 j))) = (algebraMap B (WrB (𝓈 j))).comp (algebraMap S B) := by
  apply ringHom_eq_of_spec_map_eq
  rw [CommRingCat.ofHom_comp, Spec.map_comp, spec_algebraMap_W, spec_chi_Wι, CommRingCat.ofHom_comp, Spec.map_comp,
    spec_algebraMap_W]

local notation "χ_alg'" => chi_comp_algebraMap C hM S u B v gv hgv hgvP U

theorem chi_comp_algebraMap_C (j : CIdx') : (χ' j).comp (algebraMap C (WrS (𝓅 j))) = algebraMap C (WrB (𝓈 j)) := by
  rw [IsScalarTower.algebraMap_eq C S (WrS (𝓅 j)), ← RingHom.comp_assoc, chi_comp_algebraMap, RingHom.comp_assoc,
    ← IsScalarTower.algebraMap_eq C S B, ← IsScalarTower.algebraMap_eq C B (WrB (𝓈 j))]

def chiAlgHom (j : CIdx') : WrS (𝓅 j) →ₐ[C] WrB (𝓈 j) :=
  { toRingHom := χ' j
    commutes' := fun c => RingHom.congr_fun (chi_comp_algebraMap_C C hM S u B v gv hgv hgvP U j) c }

theorem coe_chiAlgHom (j : CIdx') : (chiAlgHom C hM S u B v gv hgv hgvP U j : WrS (𝓅 j) →+* WrB (𝓈 j)) = χ' j :=
  RingHom.ext fun _ => rfl

def ψs (j : CIdx') : ringOf (fM := fM) C U →+* WrB (𝓈 j) := (algebraMap B (WrB (𝓈 j))).comp ψ

local notation "ψs'" => ψs C hM S u B v gv hgv hgvP U ψ

theorem ψs_def (j : CIdx') : ψs' j = (algebraMap B (WrB (𝓈 j))).comp ψ := rfl

include hψ in
theorem hψs (j : CIdx') : Spec.map (CommRingCat.ofHom (ψs' j)) ≫ chartι C U = (ptFC C hM (WrB (𝓈 j)) (upB (𝓈 j))).1 := by
  rw [ψs_def, CommRingCat.ofHom_comp, Spec.map_comp, Category.assoc, hψ, ptFC_up, spec_algebraMap_W]

include hψC in
theorem hψsC (j : CIdx') : (ψs' j).comp (algebraMap C (ringOf (fM := fM) C U)) = algebraMap C (WrB (𝓈 j)) := by
  rw [ψs_def, RingHom.comp_assoc, hψC, ← IsScalarTower.algebraMap_eq C B]

local notation "hψs'" => hψs C hM S u B v gv hgv hgvP U ψ hψ
local notation "hψsC'" => hψsC C hM S u B v gv hgv hgvP U ψ hψC

include hψ in

theorem φW_eq_ψs (j : CIdx') : φW C tB (𝓈 j) = ψs' j := by
  apply ringHom_eq_of_spec_map_eq
  have h1 : Spec.map (CommRingCat.ofHom (φW C tB (𝓈 j))) ≫ chartι C U = Wι C tB (𝓈 j) ≫ tB := spec_φW_chartι C tB (𝓈 j)
  have h2 : Spec.map (CommRingCat.ofHom (ψs' j)) ≫ chartι C U = Wι C tB (𝓈 j) ≫ tB := by
    rw [hψs C hM S u B v gv hgv hgvP U ψ hψ j, ptFC_up, spec_algebraMap_W]
  exact (cancel_mono (chartι C U)).mp (h1.trans h2.symm)

include hψ in

theorem chi_comp_φW (j : CIdx') : (χ' j).comp (φW C tS (𝓅 j)) = ψs' j := by
  rw [← φW_eq_ψs C hM S u B v gv hgv hgvP U ψ hψ j]
  apply ringHom_eq_of_spec_map_eq
  have h1 : Spec.map (CommRingCat.ofHom ((χ' j).comp (φW C tS (𝓅 j)))) ≫ chartι C U = Wι C tB (𝓈 j) ≫ tB := by
    rw [CommRingCat.ofHom_comp, Spec.map_comp, Category.assoc]
    show Spec.map (CommRingCat.ofHom (χ' j)) ≫ Spec.map (CommRingCat.ofHom (φW C tS (𝓅 j))) ≫ chartι C (𝓅 j).1.2 = _
    rw [spec_φW_chartι, ← Category.assoc, spec_chi_Wι, Category.assoc, ← tB_eq C hM S u B v gv hgv hgvP]
  have h2 : Spec.map (CommRingCat.ofHom (φW C tB (𝓈 j))) ≫ chartι C U = Wι C tB (𝓈 j) ≫ tB := spec_φW_chartι C tB (𝓈 j)
  exact (cancel_mono (chartι C U)).mp (h1.trans h2.symm)

local notation "χ_φW'" => chi_comp_φW C hM S u B v gv hgv hgvP U ψ hψ

@[reducible] def algSW (j : CIdx') : Algebra S (WrB (𝓈 j)) := ((algebraMap B (WrB (𝓈 j))).comp (algebraMap S B)).toAlgebra

@[reducible] def algχ (j : CIdx') : Algebra (WrS (𝓅 j)) (WrB (𝓈 j)) := (χ' j).toAlgebra

local notation "algSW'" => algSW C hM S u B v gv hgv hgvP U
local notation "algχ'" => algχ C hM S u B v gv hgv hgvP U

theorem towerCSW (j : CIdx') : letI := algSW' j; IsScalarTower C S (WrB (𝓈 j)) := by
  letI := algSW' j
  exact IsScalarTower.of_algebraMap_eq (fun x => by
    show algebraMap C (WrB (𝓈 j)) x = algebraMap B (WrB (𝓈 j)) (algebraMap S B (algebraMap C S x))
    rw [← IsScalarTower.algebraMap_apply C S B x, ← IsScalarTower.algebraMap_apply C B (WrB (𝓈 j)) x])

theorem towerCχW (j : CIdx') : letI := algχ' j; IsScalarTower C (WrS (𝓅 j)) (WrB (𝓈 j)) := by
  letI := algχ' j
  exact IsScalarTower.of_algebraMap_eq (fun x => (RingHom.congr_fun (chi_comp_algebraMap_C C hM S u B v gv hgv hgvP U j) x).symm)

local notation "towerCSW'" => towerCSW C hM S u B v gv hgv hgvP U
local notation "towerCχW'" => towerCχW C hM S u B v gv hgv hgvP U

theorem exists_mu (j : CIdx') : ∃ m : (upB (𝓈 j)).1.A ⟶ (upS (𝓅 j)).1.A,
    FakeEllipticCurve.IsPullbackVia (χ' j) (upS (𝓅 j)).1 (upB (𝓈 j)).1 m ∧
      ((upB (𝓈 j)).2.P).1 ≫ m = Spec.map (CommRingCat.ofHom (χ' j)) ≫ ((upS (𝓅 j)).2.P).1 := by
  have key := isPullback_of_ptFC_eq C hM (chiAlgHom C hM S u B v gv hgv hgvP U j) (upS (𝓅 j)) (upB (𝓈 j)) (by
    rw [coe_chiAlgHom, ptFC_up, ptFC_up, spec_algebraMap_W, spec_algebraMap_W, ← Category.assoc, spec_chi_Wι,
      Category.assoc, ← tB_eq C hM S u B v gv hgv hgvP])
  rw [coe_chiAlgHom] at key
  obtain ⟨m, hg, hmul, hact, hlev, hP⟩ := key
  exact ⟨m, ⟨hg, hmul, hact, hlev⟩, hP⟩

def mu (j : CIdx') : (upB (𝓈 j)).1.A ⟶ (upS (𝓅 j)).1.A := (exists_mu C hM S u B v gv hgv hgvP U j).choose

local notation "μ" => mu C hM S u B v gv hgv hgvP U

theorem mu_via (j : CIdx') : FakeEllipticCurve.IsPullbackVia (χ' j) (upS (𝓅 j)).1 (upB (𝓈 j)).1 (μ j) :=
  (exists_mu C hM S u B v gv hgv hgvP U j).choose_spec.1

theorem mu_P (j : CIdx') : ((upB (𝓈 j)).2.P).1 ≫ μ j = Spec.map (CommRingCat.ofHom (χ' j)) ≫ ((upS (𝓅 j)).2.P).1 :=
  (exists_mu C hM S u B v gv hgv hgvP U j).choose_spec.2

local notation "mu_via'" => mu_via C hM S u B v gv hgv hgvP U

include hkB in
theorem exists_nu (j : CIdx') : ∃ m : (ApB (𝓈 j)).A ⟶ (ApS (𝓅 j)).A, m ≫ hApS (𝓅 j) = hApB (𝓈 j) ≫ kB ∧
    FakeEllipticCurve.IsPullbackVia (χ' j) (ApS (𝓅 j)) (ApB (𝓈 j)) m := by
  obtain ⟨m, h1, -, -, h4⟩ := FakeEllipticCurve.IsPullbackVia.exists_comp_eq_and_isPullbackVia_of_comp_eq
    (algebraMap S (WrS (𝓅 j))) (χ' j) ((algebraMap B (WrB (𝓈 j))).comp (algebraMap S B))
    (chi_comp_algebraMap C hM S u B v gv hgv hgvP U j) A (ApS (𝓅 j)) (ApB (𝓈 j))
    (hApS (𝓅 j)) (hAp_via C hM S u A (𝓅 j)) (fun t' P hh => hAp_levelIff C hM S u A (𝓅 j) t' P hh)
    (hApB (𝓈 j) ≫ kB) (isPullbackVia_comp _ _ _ _ _ _ _ hkB (hAp_via C hM B v AB (𝓈 j)))
  exact ⟨m, h1, h4⟩

def nu (j : CIdx') : (ApB (𝓈 j)).A ⟶ (ApS (𝓅 j)).A := (exists_nu C hM S u A B v gv hgv hgvP AB kB hkB U j).choose

local notation "ν" => nu C hM S u A B v gv hgv hgvP AB kB hkB U

theorem nu_hAp (j : CIdx') : ν j ≫ hApS (𝓅 j) = hApB (𝓈 j) ≫ kB :=
  (exists_nu C hM S u A B v gv hgv hgvP AB kB hkB U j).choose_spec.1

theorem nu_via (j : CIdx') : FakeEllipticCurve.IsPullbackVia (χ' j) (ApS (𝓅 j)) (ApB (𝓈 j)) (ν j) :=
  (exists_nu C hM S u A B v gv hgv hgvP AB kB hkB U j).choose_spec.2

local notation "nu_hAp'" => nu_hAp C hM S u A B v gv hgv hgvP AB kB hkB U
local notation "nu_via'" => nu_via C hM S u A B v gv hgv hgvP AB kB hkB U

include hgv in

theorem gpv_via (j : CIdx') : FakeEllipticCurve.IsPullbackVia ((algebraMap B (WrB (𝓈 j))).comp (algebraMap S B)) u.1
    (upB (𝓈 j)).1 (gpB (𝓈 j) ≫ gv) :=
  isPullbackVia_comp _ _ _ _ _ _ _ hgv (gp_via C hM B v (𝓈 j))

include hkB in

theorem hApk_via (j : CIdx') : FakeEllipticCurve.IsPullbackVia ((algebraMap B (WrB (𝓈 j))).comp (algebraMap S B)) A
    (ApB (𝓈 j)) (hApB (𝓈 j) ≫ kB) :=
  isPullbackVia_comp _ _ _ _ _ _ _ hkB (hAp_via C hM B v AB (𝓈 j))

local notation "gpv_via'" => gpv_via C hM S u B v gv hgv hgvP U
local notation "hApk_via'" => hApk_via C hM S u A B v gv hgv hgvP AB kB hkB U

include hrig in

theorem mu_gp (j : CIdx') : μ j ≫ gpS (𝓅 j) = gpB (𝓈 j) ≫ gv := by
  refine comparison_unique C hrig ((algebraMap B (WrB (𝓈 j))).comp (algebraMap S B)) u (upB (𝓈 j)) _ _ ?_ ?_
    (gpv_via C hM S u B v gv hgv hgvP U j) ?_
  · exact isPullbackVia_congr (chi_comp_algebraMap C hM S u B v gv hgv hgvP U j) _ _ _
      (isPullbackVia_comp _ _ _ _ _ _ _ (gp_via C hM S u (𝓅 j)) (mu_via C hM S u B v gv hgv hgvP U j))
  · rw [← Category.assoc, mu_P, Category.assoc, gp_P, ← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp,
      chi_comp_algebraMap]
  · rw [← Category.assoc, gp_P, Category.assoc, hgvP, ← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp]

local notation "mu_gp'" => mu_gp C hM hrig S u B v gv hgv hgvP U

def kvUs (j : CIdx') : (upB (𝓈 j)).1.A ⟶ (uof C hM U).1.A := kvU C hM (WrB (𝓈 j)) (upB (𝓈 j)) U (ψs' j) (hψs' j) (hψsC' j)

local notation "kvUs'" => kvUs C hM S u B v gv hgv hgvP U ψ hψ hψC

theorem kvUs_def (j : CIdx') : kvUs' j = kvU C hM (WrB (𝓈 j)) (upB (𝓈 j)) U (ψs' j) (hψs' j) (hψsC' j) := rfl

def kAUs (j : CIdx') : (ApB (𝓈 j)).A ⟶ (Aof (fM := fM) C 𝔄 U).A :=
  letI := algSW' j
  haveI := towerCSW' j
  kAU C 𝔄 S A gA₀ hgA₀ (WrB (𝓈 j)) (ApB (𝓈 j)) (hApB (𝓈 j) ≫ kB) (hApk_via' j) U (ψs' j) (hψsC' j)

local notation "kAUs'" => kAUs C 𝔄 hM S u A gA₀ hgA₀ B v gv hgv hgvP AB kB hkB U ψ hψC

include hrig in

theorem mu_kU (j : CIdx') : μ j ≫ kUS (𝓅 j) = kvUs' j := by
  refine kvU_unique C hM hrig (WrB (𝓈 j)) (upB (𝓈 j)) U (ψs' j) (hψs' j) (hψsC' j) _ ?_ ?_
  · exact isPullbackVia_congr (chi_comp_φW C hM S u B v gv hgv hgvP U ψ hψ j) _ _ _
      (isPullbackVia_comp _ _ _ _ _ _ _ (kU_via C hM S u (𝓅 j)) (mu_via C hM S u B v gv hgv hgvP U j))
  · have key : ((upB (𝓈 j)).2.P).1 ≫ μ j ≫ kUS (𝓅 j) =
        Spec.map (CommRingCat.ofHom ((χ' j).comp (φW C tS (𝓅 j)))) ≫ ((uof C hM (𝓅 j).1.2).2.P).1 := by
      rw [← Category.assoc, mu_P, Category.assoc, kU_P, ← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
    rw [chi_comp_φW C hM S u B v gv hgv hgvP U ψ hψ j] at key
    exact key

local notation "mu_kU'" => mu_kU C hM hrig S u B v gv hgv hgvP U ψ hψ hψC

include hψ in

theorem nu_kA (j : CIdx') : ν j ≫ kAS (𝓅 j) = kAUs' j := by
  letI := algSW' j
  haveI := towerCSW' j
  show _ = kAU C 𝔄 S A gA₀ hgA₀ (WrB (𝓈 j)) (ApB (𝓈 j)) (hApB (𝓈 j) ≫ kB) (hApk_via' j) U (ψs' j) (hψsC' j)
  refine kAU_unique C 𝔄 S A gA₀ hgA₀ (WrB (𝓈 j)) (ApB (𝓈 j)) (hApB (𝓈 j) ≫ kB) (hApk_via' j) U (ψs' j) (hψsC' j) _ ?_ ?_
  · show (ν j ≫ kAS (𝓅 j)) ≫ gAof C 𝔄 (𝓅 j).1.2 = _
    rw [Category.assoc, kA_gAof, ← Category.assoc, nu_hAp, Category.assoc]
  · have key : (ν j ≫ kAS (𝓅 j)) ≫ (Aof C 𝔄 (𝓅 j).1.2).f =
        (ApB (𝓈 j)).f ≫ Spec.map (CommRingCat.ofHom ((χ' j).comp (φW C tS (𝓅 j)))) := by
      rw [Category.assoc, kA_over, ← Category.assoc, (nu_via C hM S u A B v gv hgv hgvP AB kB hkB U j).1.w, Category.assoc,
        ← Spec.map_comp, ← CommRingCat.ofHom_comp]
    rw [chi_comp_φW C hM S u B v gv hgv hgvP U ψ hψ j] at key
    exact key

local notation "nu_kA'" => nu_kA C 𝔄 hM S u A gA₀ hgA₀ B v gv hgv hgvP AB kB hkB U ψ hψ hψC

include hrig in

theorem gp_kvU (j : CIdx') : gpB (𝓈 j) ≫ kvUB = kvUs' j := by
  refine kvU_unique C hM hrig (WrB (𝓈 j)) (upB (𝓈 j)) U (ψs' j) (hψs' j) (hψsC' j) _ ?_ ?_
  · exact isPullbackVia_comp _ _ _ _ _ _ _ (kvU_via C hM B v U ψ hψ hψC) (gp_via C hM B v (𝓈 j))
  · rw [← Category.assoc, gp_P, Category.assoc, kvU_P, ← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
    rfl

local notation "gp_kvU'" => gp_kvU C hM hrig S u B v gv hgv hgvP U ψ hψ hψC

theorem hAp_kAU (j : CIdx') : hApB (𝓈 j) ≫ kAUB = kAUs' j := by
  letI := algSW' j
  haveI := towerCSW' j
  show _ = kAU C 𝔄 S A gA₀ hgA₀ (WrB (𝓈 j)) (ApB (𝓈 j)) (hApB (𝓈 j) ≫ kB) (hApk_via' j) U (ψs' j) (hψsC' j)
  refine kAU_unique C 𝔄 S A gA₀ hgA₀ (WrB (𝓈 j)) (ApB (𝓈 j)) (hApB (𝓈 j) ≫ kB) (hApk_via' j) U (ψs' j) (hψsC' j) _ ?_ ?_
  · rw [Category.assoc, kAU_gAof, Category.assoc]
  · rw [Category.assoc, kAU_over, ← Category.assoc, (hAp_via C hM B v AB (𝓈 j)).1.w, Category.assoc, ← Spec.map_comp,
      ← CommRingCat.ofHom_comp]
    rfl

local notation "hAp_kAU'" => hAp_kAU C 𝔄 hM S u A gA₀ hgA₀ B v gv hgv hgvP AB kB hkB U ψ hψC

def mX (j : CIdx') : (DpB (𝓈 j)).X ⟶ (DpS (𝓅 j)).X :=
  letI := algχ' j
  haveI := towerCχW' j
  genIota (WrS (𝓅 j)) (upS (𝓅 j)) (ApS (𝓅 j)) (DpS (𝓅 j)).X (DpS (𝓅 j)).ξ (DpS (𝓅 j)).pt (DpS (𝓅 j)).rep
    (WrB (𝓈 j)) (upB (𝓈 j)) (μ j) (mu_via' j) (ApB (𝓈 j)) (ν j) (nu_via' j) (DpB (𝓈 j))

local notation "mX'" => mX C 𝔄 hloc hM S u A gA₀ hgA₀ B v gv hgv hgvP AB kB hkB U

theorem mX_spec (j : CIdx') : letI := algχ' j
    GenIotaSpec (WrS (𝓅 j)) (upS (𝓅 j)) (ApS (𝓅 j)) (DpS (𝓅 j)).X (DpS (𝓅 j)).ξ (DpS (𝓅 j)).pt
      (WrB (𝓈 j)) (upB (𝓈 j)) (μ j) (ApB (𝓈 j)) (ν j) (DpB (𝓈 j)) (mX' j) := by
  letI := algχ' j
  haveI := towerCχW' j
  exact genIota_spec _ _ _ _ _ _ (DpS (𝓅 j)).rep _ _ _ (mu_via' j) _ _ (nu_via' j) _

local notation "mX_spec'" => mX_spec C 𝔄 hloc hM S u A gA₀ hgA₀ B v gv hgv hgvP AB kB hkB U

def GX (j : CIdx') : (DpB (𝓈 j)).X ⟶ X :=
  letI := algSW' j
  haveI := towerCSW' j
  genIota S u A X ξ pt hX (WrB (𝓈 j)) (upB (𝓈 j)) (gpB (𝓈 j) ≫ gv) (gpv_via' j) (ApB (𝓈 j)) (hApB (𝓈 j) ≫ kB)
    (hApk_via' j) (DpB (𝓈 j))

local notation "GX'" => GX C 𝔄 hloc hM S u A gA₀ hgA₀ X ξ pt hX B v gv hgv hgvP AB kB hkB U

def GCX (j : CIdx') : (DpB (𝓈 j)).X ⟶ (DU C 𝔄 hloc hM U).X :=
  letI := algSW' j
  haveI := towerCSW' j
  genC C 𝔄 hloc hM S A gA₀ hgA₀ (WrB (𝓈 j)) (upB (𝓈 j)) (ApB (𝓈 j)) (hApB (𝓈 j) ≫ kB) (hApk_via' j) (DpB (𝓈 j)) U
    (ψs' j) (hψs' j) (hψsC' j)

local notation "GCX'" => GCX C 𝔄 hloc hM S u A gA₀ hgA₀ B v gv hgv hgvP AB kB hkB U ψ hψ hψC

theorem ιB_GX (j : CIdx') : ιB (𝓈 j) ≫ genIB = GX' j := by
  letI := algSW' j
  haveI := towerCSW' j
  show _ = genIota S u A X ξ pt hX (WrB (𝓈 j)) (upB (𝓈 j)) (gpB (𝓈 j) ≫ gv) (gpv_via' j) (ApB (𝓈 j)) (hApB (𝓈 j) ≫ kB)
    (hApk_via' j) (DpB (𝓈 j))
  apply genIota_unique
  constructor
  · have sq := (iota_spec C 𝔄 hloc hM B v AB (kB ≫ gA₀) hkB₀ DB.X DB.ξ DB.pt DB.rep (𝓈 j)).1.paste_horiz
      (genIota_isPullback S u A X ξ pt hX B v gv hgv AB kB hkB DB)
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp] at sq
    exact sq
  · intro T _ _ _ _ E' A' gE' hgE' gA' hgA' hgE hgA φ φ' hφ hp hl
    letI : Algebra B T := ((algebraMap (WrB (𝓈 j)) T).comp (algebraMap B (WrB (𝓈 j)))).toAlgebra
    haveI : IsScalarTower B (WrB (𝓈 j)) T := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
    haveI : IsScalarTower S B T := IsScalarTower.of_algebraMap_eq (fun x =>
      IsScalarTower.algebraMap_apply S (WrB (𝓈 j)) T x)
    have hgEB : FakeEllipticCurve.IsPullbackVia (algebraMap B T) v.1 E' (gE' ≫ gpB (𝓈 j)) :=
      isPullbackVia_comp _ _ _ _ _ _ _ (gp_via C hM B v (𝓈 j)) hgE'
    have hgAB : FakeEllipticCurve.IsPullbackVia (algebraMap B T) AB A' (gA' ≫ hApB (𝓈 j)) :=
      isPullbackVia_comp _ _ _ _ _ _ _ (hAp_via C hM B v AB (𝓈 j)) hgA'
    have hgES : FakeEllipticCurve.IsPullbackVia (algebraMap S T) u.1 E' ((gE' ≫ gpB (𝓈 j)) ≫ gv) :=
      isPullbackVia_of_eq (Category.assoc _ _ _).symm hgE
    have hgAS : FakeEllipticCurve.IsPullbackVia (algebraMap S T) A A' ((gA' ≫ hApB (𝓈 j)) ≫ kB) :=
      isPullbackVia_of_eq (Category.assoc _ _ _).symm hgA
    rw [← Category.assoc,
      (iota_spec C 𝔄 hloc hM B v AB (kB ≫ gA₀) hkB₀ DB.X DB.ξ DB.pt DB.rep (𝓈 j)).2 T E' A' gE' hgE' gA' hgA' hgEB hgAB
        φ φ' hφ hp hl,
      (genIota_spec S u A X ξ pt hX B v gv hgv AB kB hkB DB).2 T E' A' _ hgEB _ hgAB hgES hgAS φ φ' hφ hp hl]
    exact pt_congr_raw S u A X ξ pt E' A' (Category.assoc _ _ _) hgES hgE (Category.assoc _ _ _) hgAS hgA φ φ' hφ hp hl

local notation "ιB_GX'" => ιB_GX C 𝔄 hloc hM S u A gA₀ hgA₀ X ξ pt hX B v gv hgv hgvP AB kB hkB DB U

include hrig in

theorem mX_ιS (j : CIdx') : mX' j ≫ ιS (𝓅 j) = GX' j := by
  letI := algSW' j
  haveI := towerCSW' j
  letI := algχ' j
  haveI := towerCχW' j
  show _ = genIota S u A X ξ pt hX (WrB (𝓈 j)) (upB (𝓈 j)) (gpB (𝓈 j) ≫ gv) (gpv_via' j) (ApB (𝓈 j)) (hApB (𝓈 j) ≫ kB)
    (hApk_via' j) (DpB (𝓈 j))
  apply genIota_unique
  constructor
  · have sq := (mX_spec' j).1.paste_horiz (iota_spec C 𝔄 hloc hM S u A gA₀ hgA₀ X ξ pt hX (𝓅 j)).1
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp] at sq
    have e : (algebraMap (WrS (𝓅 j)) (WrB (𝓈 j))).comp (algebraMap S (WrS (𝓅 j))) = algebraMap S (WrB (𝓈 j)) :=
      chi_comp_algebraMap C hM S u B v gv hgv hgvP U j
    rw [e] at sq
    exact sq
  · intro T _ _ _ _ E' A' gE' hgE' gA' hgA' hgE hgA φ φ' hφ hp hl
    letI : Algebra (WrS (𝓅 j)) T := ((algebraMap (WrB (𝓈 j)) T).comp (χ' j)).toAlgebra
    haveI : IsScalarTower (WrS (𝓅 j)) (WrB (𝓈 j)) T := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
    haveI : IsScalarTower S (WrS (𝓅 j)) T := IsScalarTower.of_algebraMap_eq (fun x => by
      show algebraMap S T x = algebraMap (WrB (𝓈 j)) T (χ' j (algebraMap S (WrS (𝓅 j)) x))
      rw [IsScalarTower.algebraMap_apply S (WrB (𝓈 j)) T x, ← RingHom.comp_apply (χ' j),
        chi_comp_algebraMap C hM S u B v gv hgv hgvP U j]
      rfl)
    have hgEp : FakeEllipticCurve.IsPullbackVia (algebraMap (WrS (𝓅 j)) T) (upS (𝓅 j)).1 E' (gE' ≫ μ j) :=
      isPullbackVia_comp _ _ _ _ _ _ _ (mu_via' j) hgE'
    have hgAp : FakeEllipticCurve.IsPullbackVia (algebraMap (WrS (𝓅 j)) T) (ApS (𝓅 j)) A' (gA' ≫ ν j) :=
      isPullbackVia_comp _ _ _ _ _ _ _ (nu_via' j) hgA'
    have hgES : FakeEllipticCurve.IsPullbackVia (algebraMap S T) u.1 E' ((gE' ≫ μ j) ≫ gpS (𝓅 j)) :=
      isPullbackVia_of_eq (by rw [Category.assoc, mu_gp C hM hrig S u B v gv hgv hgvP U j]) hgE
    have hgAS : FakeEllipticCurve.IsPullbackVia (algebraMap S T) A A' ((gA' ≫ ν j) ≫ hApS (𝓅 j)) :=
      isPullbackVia_of_eq (by rw [Category.assoc, nu_hAp]) hgA
    rw [← Category.assoc, (mX_spec' j).2 T E' A' gE' hgE' gA' hgA' hgEp hgAp φ φ' hφ hp hl,
      (iota_spec C 𝔄 hloc hM S u A gA₀ hgA₀ X ξ pt hX (𝓅 j)).2 T E' A' _ hgEp _ hgAp hgES hgAS φ φ' hφ hp hl]
    exact pt_congr_raw S u A X ξ pt E' A' (by rw [Category.assoc, mu_gp C hM hrig S u B v gv hgv hgvP U j]) hgES hgE
      (by rw [Category.assoc, nu_hAp]) hgAS hgA φ φ' hφ hp hl

local notation "mX_ιS'" => mX_ιS C 𝔄 hloc hM hrig S u A gA₀ hgA₀ X ξ pt hX B v gv hgv hgvP AB kB hkB U

include hrig in

theorem mX_cS (j : CIdx') : mX' j ≫ cS (𝓅 j) = GCX' j := by
  letI := algSW' j
  haveI := towerCSW' j
  letI := algχ' j
  haveI := towerCχW' j
  show _ = genC C 𝔄 hloc hM S A gA₀ hgA₀ (WrB (𝓈 j)) (upB (𝓈 j)) (ApB (𝓈 j)) (hApB (𝓈 j) ≫ kB) (hApk_via' j) (DpB (𝓈 j)) U
    (ψs' j) (hψs' j) (hψsC' j)
  apply genC_unique
  letI algU : Algebra (ringOf (fM := fM) C U) (WrB (𝓈 j)) := (ψs' j).toAlgebra
  constructor
  · have sq := (mX_spec' j).1.paste_horiz (cmp_isPullback C 𝔄 hloc hM S u A gA₀ hgA₀ (𝓅 j))
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp] at sq
    have e : (algebraMap (WrS (𝓅 j)) (WrB (𝓈 j))).comp (φW C tS (𝓅 j)) = algebraMap (ringOf (fM := fM) C U) (WrB (𝓈 j)) :=
      chi_comp_φW C hM S u B v gv hgv hgvP U ψ hψ j
    rw [e] at sq
    exact sq
  · intro T _ _ instUT instTow E' A' gE' hgE' gA' hgA' hgE hgA φ φ' hφ hp hl
    letI : Algebra (WrS (𝓅 j)) T := ((algebraMap (WrB (𝓈 j)) T).comp (χ' j)).toAlgebra
    haveI : IsScalarTower (WrS (𝓅 j)) (WrB (𝓈 j)) T := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
    letI instUT' : Algebra (ringOf (fM := fM) C U) T := instUT
    haveI instTow' : IsScalarTower (ringOf (fM := fM) C U) (WrB (𝓈 j)) T := instTow
    letI algUp : Algebra (ringOf (fM := fM) C (𝓅 j).1.2) (WrS (𝓅 j)) := (φW C tS (𝓅 j)).toAlgebra
    haveI : IsScalarTower (ringOf (fM := fM) C (𝓅 j).1.2) (WrS (𝓅 j)) T := IsScalarTower.of_algebraMap_eq (fun x => by
      show algebraMap (ringOf (fM := fM) C U) T x = algebraMap (WrB (𝓈 j)) T (χ' j (φW C tS (𝓅 j) x))
      rw [IsScalarTower.algebraMap_apply (ringOf (fM := fM) C U) (WrB (𝓈 j)) T x, ← RingHom.comp_apply (χ' j),
        chi_comp_φW C hM S u B v gv hgv hgvP U ψ hψ j]
      rfl)
    have hgEp : FakeEllipticCurve.IsPullbackVia (algebraMap (WrS (𝓅 j)) T) (upS (𝓅 j)).1 E' (gE' ≫ μ j) :=
      isPullbackVia_comp _ _ _ _ _ _ _ (mu_via' j) hgE'
    have hgAp : FakeEllipticCurve.IsPullbackVia (algebraMap (WrS (𝓅 j)) T) (ApS (𝓅 j)) A' (gA' ≫ ν j) :=
      isPullbackVia_comp _ _ _ _ _ _ _ (nu_via' j) hgA'
    have hgEU : FakeEllipticCurve.IsPullbackVia (algebraMap (ringOf (fM := fM) C (𝓅 j).1.2) T) (uof C hM (𝓅 j).1.2).1 E'
        ((gE' ≫ μ j) ≫ kUS (𝓅 j)) :=
      isPullbackVia_of_eq (by rw [Category.assoc, mu_kU C hM hrig S u B v gv hgv hgvP U ψ hψ hψC j]; try rfl) hgE
    have hgAU : FakeEllipticCurve.IsPullbackVia (algebraMap (ringOf (fM := fM) C (𝓅 j).1.2) T) (Aof C 𝔄 (𝓅 j).1.2) A'
        ((gA' ≫ ν j) ≫ kAS (𝓅 j)) :=
      isPullbackVia_of_eq (by rw [Category.assoc, nu_kA C 𝔄 hM S u A gA₀ hgA₀ B v gv hgv hgvP AB kB hkB U ψ hψ hψC j]; try rfl) hgA
    rw [← Category.assoc, (mX_spec' j).2 T E' A' gE' hgE' gA' hgA' hgEp hgAp φ φ' hφ hp hl,
      (cmp_spec C 𝔄 hloc hM S u A gA₀ hgA₀ (𝓅 j)).2 T E' A' _ hgEp _ hgAp hgEU hgAU φ φ' hφ hp hl]
    exact PairDatum.pt_congr _ E' A' (by rw [Category.assoc, mu_kU C hM hrig S u B v gv hgv hgvP U ψ hψ hψC j]; try rfl) hgEU hgE
      (by rw [Category.assoc, nu_kA C 𝔄 hM S u A gA₀ hgA₀ B v gv hgv hgvP AB kB hkB U ψ hψ hψC j]; try rfl) hgAU hgA φ φ' hφ hp hl

local notation "mX_cS'" => mX_cS C 𝔄 hloc hM hrig S u A gA₀ hgA₀ B v gv hgv hgvP AB kB hkB U ψ hψ hψC

include hrig in

theorem ιB_GCX (j : CIdx') : ιB (𝓈 j) ≫ genCB = GCX' j := by
  letI := algSW' j
  haveI := towerCSW' j
  show _ = genC C 𝔄 hloc hM S A gA₀ hgA₀ (WrB (𝓈 j)) (upB (𝓈 j)) (ApB (𝓈 j)) (hApB (𝓈 j) ≫ kB) (hApk_via' j) (DpB (𝓈 j)) U
    (ψs' j) (hψs' j) (hψsC' j)
  apply genC_unique
  letI algU : Algebra (ringOf (fM := fM) C U) (WrB (𝓈 j)) := (ψs' j).toAlgebra
  constructor
  · have sq := (iota_spec C 𝔄 hloc hM B v AB (kB ≫ gA₀) hkB₀ DB.X DB.ξ DB.pt DB.rep (𝓈 j)).1.paste_horiz
      (genC_isPullback C 𝔄 hloc hM S A gA₀ hgA₀ B v AB kB hkB DB U ψ hψ hψC)
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp] at sq
    exact sq
  · intro T _ _ _ _ E' A' gE' hgE' gA' hgA' hgE hgA φ φ' hφ hp hl
    letI : Algebra B T := ((algebraMap (WrB (𝓈 j)) T).comp (algebraMap B (WrB (𝓈 j)))).toAlgebra
    haveI : IsScalarTower B (WrB (𝓈 j)) T := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
    letI algUB : Algebra (ringOf (fM := fM) C U) B := ψ.toAlgebra
    haveI : IsScalarTower (ringOf (fM := fM) C U) B T := IsScalarTower.of_algebraMap_eq (fun x => by
      show algebraMap (ringOf (fM := fM) C U) T x = algebraMap (WrB (𝓈 j)) T (algebraMap B (WrB (𝓈 j)) (ψ x))
      rw [IsScalarTower.algebraMap_apply (ringOf (fM := fM) C U) (WrB (𝓈 j)) T x]
      rfl)
    have hgEB : FakeEllipticCurve.IsPullbackVia (algebraMap B T) v.1 E' (gE' ≫ gpB (𝓈 j)) :=
      isPullbackVia_comp _ _ _ _ _ _ _ (gp_via C hM B v (𝓈 j)) hgE'
    have hgAB : FakeEllipticCurve.IsPullbackVia (algebraMap B T) AB A' (gA' ≫ hApB (𝓈 j)) :=
      isPullbackVia_comp _ _ _ _ _ _ _ (hAp_via C hM B v AB (𝓈 j)) hgA'
    have hgEU : FakeEllipticCurve.IsPullbackVia (algebraMap (ringOf (fM := fM) C U) T) (uof C hM U).1 E'
        ((gE' ≫ gpB (𝓈 j)) ≫ kvUB) :=
      isPullbackVia_of_eq (by rw [Category.assoc, gp_kvU C hM hrig S u B v gv hgv hgvP U ψ hψ hψC j]; try rfl) hgE
    have hgAU : FakeEllipticCurve.IsPullbackVia (algebraMap (ringOf (fM := fM) C U) T) (Aof C 𝔄 U) A'
        ((gA' ≫ hApB (𝓈 j)) ≫ kAUB) :=
      isPullbackVia_of_eq (by rw [Category.assoc, hAp_kAU C 𝔄 hM S u A gA₀ hgA₀ B v gv hgv hgvP AB kB hkB U ψ hψC j]; try rfl) hgA
    rw [← Category.assoc,
      (iota_spec C 𝔄 hloc hM B v AB (kB ≫ gA₀) hkB₀ DB.X DB.ξ DB.pt DB.rep (𝓈 j)).2 T E' A' gE' hgE' gA' hgA' hgEB hgAB
        φ φ' hφ hp hl,
      (genC_spec C 𝔄 hloc hM S A gA₀ hgA₀ B v AB kB hkB DB U ψ hψ hψC).2 T E' A' _ hgEB _ hgAB hgEU hgAU φ φ' hφ hp hl]
    exact PairDatum.pt_congr _ E' A' (by rw [Category.assoc, gp_kvU C hM hrig S u B v gv hgv hgvP U ψ hψ hψC j]; try rfl) hgEU hgE
      (by rw [Category.assoc, hAp_kAU C 𝔄 hM S u A gA₀ hgA₀ B v gv hgv hgvP AB kB hkB U ψ hψC j]; try rfl) hgAU hgA φ φ' hφ hp hl

local notation "ιB_GCX'" => ιB_GCX C 𝔄 hloc hM hrig S u A gA₀ hgA₀ B v gv hgv hgvP AB kB hkB DB U ψ hψ hψC

include hrig in

theorem chart_eq_piece (j : CIdx') : ιB (𝓈 j) ≫ genIB ≫ kappaD C 𝔄 hloc hM hrig S u A gA₀ hgA₀ X ξ pt hX =
    ιB (𝓈 j) ≫ genCB ≫ ιR C (chartData C 𝔄 hloc hM hrig) U := by
  rw [← Category.assoc, ιB_GX (hgA₀ := hgA₀), ← mX_ιS C 𝔄 hloc hM hrig S u A gA₀ hgA₀ X ξ pt hX B v gv hgv hgvP AB kB hkB U j,
    Category.assoc]
  show mX' j ≫ ιS (𝓅 j) ≫ kappaD C 𝔄 hloc hM hrig S u A gA₀ hgA₀ X ξ pt hX = _
  rw [iota_kappaD, ← Category.assoc, mX_cS C 𝔄 hloc hM hrig S u A gA₀ hgA₀ B v gv hgv hgvP AB kB hkB U ψ hψ hψC j,
    ← ιB_GCX C 𝔄 hloc hM hrig S u A gA₀ hgA₀ B v gv hgv hgvP AB kB hkB DB U ψ hψ hψC j]
  exact Category.assoc _ _ _

end OneIdx
p2m_reactivate "P2MW.S_CerednikDrinfeld_QM_IsFineModuli_exists_locallyOfFinitePresentation_forall_representsOn_hom_isPullback_of_forall_withFullLevel.RelRepGlue"

include hrig hgvP in

theorem genIota_kappaD : genIB ≫ kappaD C 𝔄 hloc hM hrig S u A gA₀ hgA₀ X ξ pt hX = genCB ≫ ιR C (chartData C 𝔄 hloc hM hrig) U :=
  hom_ext_ιB C 𝔄 hloc hM S u A gA₀ hgA₀ B v gv hgv hgvP AB kB hkB DB U ψ hψ _ _
    (fun j => chart_eq_piece C 𝔄 hloc hM hrig S u A gA₀ hgA₀ X ξ pt hX B v gv hgv hgvP AB kB hkB DB U ψ hψ hψC j)

end ChartEq
p2m_reactivate "P2MW.S_CerednikDrinfeld_QM_IsFineModuli_exists_locallyOfFinitePresentation_forall_representsOn_hom_isPullback_of_forall_withFullLevel.RelRepGlue"

section Natural

variable (𝔄 : FakeEllipticCurve Λ N C) {r d : ℕ} (hloc : HLoc (𝒪 := 𝒪) (n := n) C r d 𝔄) (hM : IsFineModuli Λ N n M fM ptF)
  (hrig : HRig Λ N n C)
  (S : Type) [CommRing S] [Algebra C S] [Algebra 𝒪 S] [IsScalarTower 𝒪 C S]
  (u : FakeEllipticCurve.WithFullLevel Λ N n S)
  (A : FakeEllipticCurve Λ N S) (gA₀ : A.A ⟶ 𝔄.A) (hgA₀ : FakeEllipticCurve.IsPullbackVia (algebraMap C S) 𝔄 A gA₀)
  (X : Scheme.{0}) (ξ : X ⟶ Spec (CommRingCat.of S))
  (pt : FakeEllipticCurve.IsogenyPair.PtFamily r d u.1 A ξ)
  (hX : FakeEllipticCurve.IsogenyPair.RepresentsOn r d u.1 A ξ pt)

theorem kappaD_natural
    (S' : Type) [CommRing S'] [Algebra C S'] [Algebra 𝒪 S'] [IsScalarTower 𝒪 C S']
    [Algebra S S'] [IsScalarTower C S S'] [IsScalarTower 𝒪 S S']
    (u' : FakeEllipticCurve.WithFullLevel Λ N n S')
    (g : u'.1.A ⟶ u.1.A) (hg : FakeEllipticCurve.IsPullbackVia (algebraMap S S') u.1 u'.1 g)
    (hgP : (u'.2.P).1 ≫ g = Spec.map (CommRingCat.ofHom (algebraMap S S')) ≫ (u.2.P).1)
    (A' : FakeEllipticCurve Λ N S') (hA : A'.A ⟶ A.A) (hhA : FakeEllipticCurve.IsPullbackVia (algebraMap S S') A A' hA)
    (hgA' : FakeEllipticCurve.IsPullbackVia (algebraMap C S') 𝔄 A' (hA ≫ gA₀))
    (X' : Scheme.{0}) (ξ' : X' ⟶ Spec (CommRingCat.of S'))
    (pt' : FakeEllipticCurve.IsogenyPair.PtFamily r d u'.1 A' ξ')
    (hX' : FakeEllipticCurve.IsogenyPair.RepresentsOn r d u'.1 A' ξ' pt')
    (e : X' ⟶ X)
    (he₁ : CategoryTheory.IsPullback e ξ' ξ (Spec.map (CommRingCat.ofHom (algebraMap S S'))))
    (he₂ : ∀ (T : Type) [CommRing T] [Algebra S' T] [Algebra S T] [IsScalarTower S S' T]
        (E'' A'' : FakeEllipticCurve Λ N T)
        (gE'' : E''.A ⟶ u'.1.A) (hgE'' : FakeEllipticCurve.IsPullbackVia (algebraMap S' T) u'.1 E'' gE'')
        (gA'' : A''.A ⟶ A'.A) (hgA'' : FakeEllipticCurve.IsPullbackVia (algebraMap S' T) A' A'' gA'')
        (hgE : FakeEllipticCurve.IsPullbackVia (algebraMap S T) u.1 E'' (gE'' ≫ g))
        (hgAA : FakeEllipticCurve.IsPullbackVia (algebraMap S T) A A'' (gA'' ≫ hA))
        (φ : E''.A ⟶ A''.A) (φ' : A''.A ⟶ E''.A) (hφ : φ ≫ A''.f = E''.f)
        (hp : FakeEllipticCurve.IsIsogenyPair (r ^ d) E'' A'' φ φ') (hl : FakeEllipticCurve.PreservesLevel E'' A'' φ hφ),
        (pt' T E'' A'' gE'' hgE'' gA'' hgA'' φ φ' hφ hp hl).1 ≫ e =
          (pt T E'' A'' (gE'' ≫ g) hgE (gA'' ≫ hA) hgAA φ φ' hφ hp hl).1) :
    e ≫ kappaD C 𝔄 hloc hM hrig S u A gA₀ hgA₀ X ξ pt hX =
      kappaD C 𝔄 hloc hM hrig S' u' A' (hA ≫ gA₀) hgA' X' ξ' pt' hX' := by
  refine kappaD_unique C 𝔄 hloc hM hrig S' u' A' (hA ≫ gA₀) hgA' X' ξ' pt' hX' _ (fun p' => ?_)

  letI algS : Algebra S (Wring C (tu C hM S' u') p') :=
    ((algebraMap S' (Wring C (tu C hM S' u') p')).comp (algebraMap S S')).toAlgebra
  haveI : IsScalarTower S S' (Wring C (tu C hM S' u') p') := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  haveI : IsScalarTower C S (Wring C (tu C hM S' u') p') := IsScalarTower.of_algebraMap_eq (fun x => by
    show algebraMap C (Wring C (tu C hM S' u') p') x =
      algebraMap S' (Wring C (tu C hM S' u') p') (algebraMap S S' (algebraMap C S x))
    rw [← IsScalarTower.algebraMap_apply C S S' x, ← IsScalarTower.algebraMap_apply C S' (Wring C (tu C hM S' u') p') x])
  have hgv : FakeEllipticCurve.IsPullbackVia (algebraMap S (Wring C (tu C hM S' u') p')) u.1 (up C hM S' u' p').1
      (gp C hM S' u' p' ≫ g) :=
    isPullbackVia_comp _ _ _ _ _ _ _ hg (gp_via C hM S' u' p')
  have hgvP : ((up C hM S' u' p').2.P).1 ≫ (gp C hM S' u' p' ≫ g) =
      Spec.map (CommRingCat.ofHom (algebraMap S (Wring C (tu C hM S' u') p'))) ≫ (u.2.P).1 := by
    rw [← Category.assoc, gp_P, Category.assoc, hgP, ← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
  have hkB : FakeEllipticCurve.IsPullbackVia (algebraMap S (Wring C (tu C hM S' u') p')) A (Ap C hM S' u' A' p')
      (hAp C hM S' u' A' p' ≫ hA) :=
    isPullbackVia_comp _ _ _ _ _ _ _ hhA (hAp_via C hM S' u' A' p')
  have key := genIota_kappaD C 𝔄 hloc hM hrig S u A gA₀ hgA₀ X ξ pt hX (Wring C (tu C hM S' u') p') (up C hM S' u' p')
    (gp C hM S' u' p' ≫ g) hgv hgvP (Ap C hM S' u' A' p') (hAp C hM S' u' A' p' ≫ hA) hkB
    (Dp C 𝔄 hloc hM S' u' A' (hA ≫ gA₀) hgA' p') p'.1.2 (φW C (tu C hM S' u') p')
    (spec_φW_chartι_eq_ptFC_up C hM S' u' p') (φW_comp_algebraMap_up C hM S' u' p')

  have h1 : iota C 𝔄 hloc hM S' u' A' (hA ≫ gA₀) hgA' X' ξ' pt' hX' p' ≫ e =
      genIota S u A X ξ pt hX (Wring C (tu C hM S' u') p') (up C hM S' u' p') (gp C hM S' u' p' ≫ g) hgv
        (Ap C hM S' u' A' p') (hAp C hM S' u' A' p' ≫ hA) hkB (Dp C 𝔄 hloc hM S' u' A' (hA ≫ gA₀) hgA' p') := by
    apply genIota_unique
    constructor
    · have sq := (iota_spec C 𝔄 hloc hM S' u' A' (hA ≫ gA₀) hgA' X' ξ' pt' hX' p').1.paste_horiz he₁
      rw [← Spec.map_comp, ← CommRingCat.ofHom_comp] at sq
      exact sq
    · intro T _ _ _ _ E' A'' gE' hgE' gA' hgA'T hgE hgA φ φ' hφ hp hl
      letI : Algebra S' T := ((algebraMap (Wring C (tu C hM S' u') p') T).comp (algebraMap S' (Wring C (tu C hM S' u') p'))).toAlgebra
      haveI : IsScalarTower S' (Wring C (tu C hM S' u') p') T := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
      haveI : IsScalarTower S S' T := IsScalarTower.of_algebraMap_eq (fun x =>
        IsScalarTower.algebraMap_apply S (Wring C (tu C hM S' u') p') T x)
      have hgE1 : FakeEllipticCurve.IsPullbackVia (algebraMap S' T) u'.1 E' (gE' ≫ gp C hM S' u' p') :=
        isPullbackVia_comp _ _ _ _ _ _ _ (gp_via C hM S' u' p') hgE'
      have hgA1 : FakeEllipticCurve.IsPullbackVia (algebraMap S' T) A' A'' (gA' ≫ hAp C hM S' u' A' p') :=
        isPullbackVia_comp _ _ _ _ _ _ _ (hAp_via C hM S' u' A' p') hgA'T
      have hgE2 : FakeEllipticCurve.IsPullbackVia (algebraMap S T) u.1 E' ((gE' ≫ gp C hM S' u' p') ≫ g) :=
        isPullbackVia_of_eq (Category.assoc _ _ _).symm hgE
      have hgA2 : FakeEllipticCurve.IsPullbackVia (algebraMap S T) A A'' ((gA' ≫ hAp C hM S' u' A' p') ≫ hA) :=
        isPullbackVia_of_eq (Category.assoc _ _ _).symm hgA
      rw [← Category.assoc,
        (iota_spec C 𝔄 hloc hM S' u' A' (hA ≫ gA₀) hgA' X' ξ' pt' hX' p').2 T E' A'' gE' hgE' gA' hgA'T hgE1 hgA1
          φ φ' hφ hp hl,
        he₂ T E' A'' _ hgE1 _ hgA1 hgE2 hgA2 φ φ' hφ hp hl]
      exact pt_congr_raw S u A X ξ pt E' A'' (Category.assoc _ _ _) hgE2 hgE (Category.assoc _ _ _) hgA2 hgA φ φ' hφ hp hl
  have h2 : genC C 𝔄 hloc hM S A gA₀ hgA₀ (Wring C (tu C hM S' u') p') (up C hM S' u' p') (Ap C hM S' u' A' p')
      (hAp C hM S' u' A' p' ≫ hA) hkB (Dp C 𝔄 hloc hM S' u' A' (hA ≫ gA₀) hgA' p') p'.1.2 (φW C (tu C hM S' u') p')
      (spec_φW_chartι_eq_ptFC_up C hM S' u' p') (φW_comp_algebraMap_up C hM S' u' p') =
      cmp C 𝔄 hloc hM S' u' A' (hA ≫ gA₀) hgA' p' := by
    apply cmp_unique
    have hs := genC_spec C 𝔄 hloc hM S A gA₀ hgA₀ (Wring C (tu C hM S' u') p') (up C hM S' u' p') (Ap C hM S' u' A' p')
      (hAp C hM S' u' A' p' ≫ hA) hkB (Dp C 𝔄 hloc hM S' u' A' (hA ≫ gA₀) hgA' p') p'.1.2 (φW C (tu C hM S' u') p')
      (spec_φW_chartι_eq_ptFC_up C hM S' u' p') (φW_comp_algebraMap_up C hM S' u' p')
    have hkA : kAU C 𝔄 S A gA₀ hgA₀ (Wring C (tu C hM S' u') p') (Ap C hM S' u' A' p') (hAp C hM S' u' A' p' ≫ hA) hkB
        p'.1.2 (φW C (tu C hM S' u') p') (φW_comp_algebraMap_up C hM S' u' p') = kA C 𝔄 hM S' u' A' (hA ≫ gA₀) hgA' p' :=
      kA_unique C 𝔄 hM S' u' A' (hA ≫ gA₀) hgA' p' _ (by rw [kAU_gAof, Category.assoc]) (kAU_over _ _ _ _ _ _ _ _ _ _ _ _ _)
    refine ⟨hs.1, ?_⟩
    intro T _ _ _ _ E' A'' gE' hgE' gA' hgA'T hgE hgA φ φ' hφ hp hl
    have hgEU := isPullbackVia_of_eq (congrArg (gE' ≫ ·) (kvU_eq_kU C hM hrig S' u' p').symm) hgE
    have hgAU := isPullbackVia_of_eq (congrArg (gA' ≫ ·) hkA.symm) hgA
    rw [hs.2 T E' A'' gE' hgE' gA' hgA'T hgEU hgAU φ φ' hφ hp hl]
    exact PairDatum.pt_congr _ E' A'' (congrArg (gE' ≫ ·) (kvU_eq_kU C hM hrig S' u' p')) hgEU hgE
      (congrArg (gA' ≫ ·) hkA) hgAU hgA φ φ' hφ hp hl
  rw [← Category.assoc, h1, key, h2]

end Natural
p2m_reactivate "P2MW.S_CerednikDrinfeld_QM_IsFineModuli_exists_locallyOfFinitePresentation_forall_representsOn_hom_isPullback_of_forall_withFullLevel.RelRepGlue"

end RelRepGlue
p2m_reactivate "P2MW.S_CerednikDrinfeld_QM_IsFineModuli_exists_locallyOfFinitePresentation_forall_representsOn_hom_isPullback_of_forall_withFullLevel.RelRepGlue"

end
p2m_reactivate "P2MW.S_CerednikDrinfeld_QM_IsFineModuli_exists_locallyOfFinitePresentation_forall_representsOn_hom_isPullback_of_forall_withFullLevel.RelRepGlue"

set_option autoImplicit false

open scoped TensorProduct Quaternion NumberField
open CategoryTheory AlgebraicGeometry QuaternionAlgebra CerednikDrinfeld CerednikDrinfeld.QM NeronModelInfra GoodReductionJacobian

open RelRepGlue in
theorem solution
    {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} {N : ℕ} (r d : ℕ)

    (𝒪 : Type) [CommRing 𝒪] (n : ℕ) (M : Scheme.{0}) (fM : M ⟶ Spec (CommRingCat.of 𝒪))
    (ptF : ∀ (S : Type) [CommRing S] (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of 𝒪)),
      FakeEllipticCurve.WithFullLevel Λ N n S → SchemeHomOver s fM)
    (hM : IsFineModuli Λ N n M fM ptF)

    (C : Type) [CommRing C] [Algebra 𝒪 C] (𝔄 : FakeEllipticCurve Λ N C)

    (hrig : ∀ (S : Type) [CommRing S] [Algebra C S] (u : FakeEllipticCurve.WithFullLevel Λ N n S)
      (e : u.1.A ≅ u.1.A) (he : e.hom ≫ u.1.f = u.1.f),
      (∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of S)) (P Q : SchemeHomOver t u.1.f),
        mapPt e.hom he (u.1.L.mul t P Q) = u.1.L.mul t (mapPt e.hom he P) (mapPt e.hom he Q)) →
      (∀ x : ↥Λ, u.1.act x ≫ e.hom = e.hom ≫ u.1.act x) →
      mapPt e.hom he u.2.P = u.2.P → e = Iso.refl u.1.A)

    (hloc : ∀ (S : Type) [CommRing S] [Algebra C S] [Algebra 𝒪 S] [IsScalarTower 𝒪 C S]
      (u : FakeEllipticCurve.WithFullLevel Λ N n S)
      (A : FakeEllipticCurve Λ N S) (gA : A.A ⟶ 𝔄.A) (_ : FakeEllipticCurve.IsPullbackVia (algebraMap C S) 𝔄 A gA),
      ∃ (X : Scheme.{0}) (ξ : X ⟶ Spec (CommRingCat.of S)) (_ : LocallyOfFinitePresentation ξ)
        (pt : FakeEllipticCurve.IsogenyPair.PtFamily r d u.1 A ξ),
        FakeEllipticCurve.IsogenyPair.RepresentsOn r d u.1 A ξ pt) :
    ∃ (Xd : Scheme.{0}) (q : Xd ⟶ Limits.pullback fM (Spec.map (CommRingCat.ofHom (algebraMap 𝒪 C)))) (_ : LocallyOfFinitePresentation q)
      (κ : ∀ (S : Type) [CommRing S] [Algebra C S] [Algebra 𝒪 S] [IsScalarTower 𝒪 C S]
        (u : FakeEllipticCurve.WithFullLevel Λ N n S)
        (A : FakeEllipticCurve Λ N S) (gA : A.A ⟶ 𝔄.A) (_ : FakeEllipticCurve.IsPullbackVia (algebraMap C S) 𝔄 A gA)
        (X : Scheme.{0}) (ξ : X ⟶ Spec (CommRingCat.of S))
        (pt : FakeEllipticCurve.IsogenyPair.PtFamily r d u.1 A ξ),
        FakeEllipticCurve.IsogenyPair.RepresentsOn r d u.1 A ξ pt → (X ⟶ Xd)),

      (∀ (S : Type) [CommRing S] [Algebra C S] [Algebra 𝒪 S] [IsScalarTower 𝒪 C S]
          (u : FakeEllipticCurve.WithFullLevel Λ N n S)
          (A : FakeEllipticCurve Λ N S) (gA : A.A ⟶ 𝔄.A) (hgA : FakeEllipticCurve.IsPullbackVia (algebraMap C S) 𝔄 A gA)
          (X : Scheme.{0}) (ξ : X ⟶ Spec (CommRingCat.of S))
          (pt : FakeEllipticCurve.IsogenyPair.PtFamily r d u.1 A ξ)
          (hX : FakeEllipticCurve.IsogenyPair.RepresentsOn r d u.1 A ξ pt),
          κ S u A gA hgA X ξ pt hX ≫ q ≫ Limits.pullback.fst fM (Spec.map (CommRingCat.ofHom (algebraMap 𝒪 C))) =
              ξ ≫ (ptF S (Spec.map (CommRingCat.ofHom (algebraMap 𝒪 S))) u).1 ∧
          κ S u A gA hgA X ξ pt hX ≫ q ≫ Limits.pullback.snd fM (Spec.map (CommRingCat.ofHom (algebraMap 𝒪 C))) =
              ξ ≫ Spec.map (CommRingCat.ofHom (algebraMap C S))) ∧

      (∀ (S : Type) [CommRing S] [Algebra C S] [Algebra 𝒪 S] [IsScalarTower 𝒪 C S]
          (u : FakeEllipticCurve.WithFullLevel Λ N n S)
          (A : FakeEllipticCurve Λ N S) (gA : A.A ⟶ 𝔄.A) (hgA : FakeEllipticCurve.IsPullbackVia (algebraMap C S) 𝔄 A gA)
          (X : Scheme.{0}) (ξ : X ⟶ Spec (CommRingCat.of S))
          (pt : FakeEllipticCurve.IsogenyPair.PtFamily r d u.1 A ξ)
          (hX : FakeEllipticCurve.IsogenyPair.RepresentsOn r d u.1 A ξ pt)
          (T : Scheme.{0}) (x : T ⟶ Xd) (t : T ⟶ Spec (CommRingCat.of S)),
          x ≫ q ≫ Limits.pullback.fst fM (Spec.map (CommRingCat.ofHom (algebraMap 𝒪 C))) = t ≫ (ptF S (Spec.map (CommRingCat.ofHom (algebraMap 𝒪 S))) u).1 →
          x ≫ q ≫ Limits.pullback.snd fM (Spec.map (CommRingCat.ofHom (algebraMap 𝒪 C))) = t ≫ Spec.map (CommRingCat.ofHom (algebraMap C S)) →
            ∃! y : T ⟶ X, y ≫ κ S u A gA hgA X ξ pt hX = x ∧ y ≫ ξ = t) ∧

      (∀ (S S' : Type) [CommRing S] [Algebra C S] [Algebra 𝒪 S] [IsScalarTower 𝒪 C S]
          [CommRing S'] [Algebra C S'] [Algebra 𝒪 S'] [IsScalarTower 𝒪 C S']
          [Algebra S S'] [IsScalarTower C S S'] [IsScalarTower 𝒪 S S']
          (u : FakeEllipticCurve.WithFullLevel Λ N n S) (u' : FakeEllipticCurve.WithFullLevel Λ N n S')
          (g : u'.1.A ⟶ u.1.A) (hg : FakeEllipticCurve.IsPullbackVia (algebraMap S S') u.1 u'.1 g)
          (_ : (u'.2.P).1 ≫ g = Spec.map (CommRingCat.ofHom (algebraMap S S')) ≫ (u.2.P).1)
          (A : FakeEllipticCurve Λ N S) (gA : A.A ⟶ 𝔄.A) (hgA : FakeEllipticCurve.IsPullbackVia (algebraMap C S) 𝔄 A gA)
          (A' : FakeEllipticCurve Λ N S') (hA : A'.A ⟶ A.A) (hhA : FakeEllipticCurve.IsPullbackVia (algebraMap S S') A A' hA)
          (hgA' : FakeEllipticCurve.IsPullbackVia (algebraMap C S') 𝔄 A' (hA ≫ gA))
          (X : Scheme.{0}) (ξ : X ⟶ Spec (CommRingCat.of S))
          (pt : FakeEllipticCurve.IsogenyPair.PtFamily r d u.1 A ξ)
          (hX : FakeEllipticCurve.IsogenyPair.RepresentsOn r d u.1 A ξ pt)
          (X' : Scheme.{0}) (ξ' : X' ⟶ Spec (CommRingCat.of S'))
          (pt' : FakeEllipticCurve.IsogenyPair.PtFamily r d u'.1 A' ξ')
          (hX' : FakeEllipticCurve.IsogenyPair.RepresentsOn r d u'.1 A' ξ' pt')
          (e : X' ⟶ X),
          CategoryTheory.IsPullback e ξ' ξ (Spec.map (CommRingCat.ofHom (algebraMap S S'))) →
          (∀ (T : Type) [CommRing T] [Algebra S' T] [Algebra S T] [IsScalarTower S S' T]
              (E'' A'' : FakeEllipticCurve Λ N T)
              (gE'' : E''.A ⟶ u'.1.A) (hgE'' : FakeEllipticCurve.IsPullbackVia (algebraMap S' T) u'.1 E'' gE'')
              (gA'' : A''.A ⟶ A'.A) (hgA'' : FakeEllipticCurve.IsPullbackVia (algebraMap S' T) A' A'' gA'')
              (hgE : FakeEllipticCurve.IsPullbackVia (algebraMap S T) u.1 E'' (gE'' ≫ g))
              (hgAA : FakeEllipticCurve.IsPullbackVia (algebraMap S T) A A'' (gA'' ≫ hA))
              (φ : E''.A ⟶ A''.A) (φ' : A''.A ⟶ E''.A) (hφ : φ ≫ A''.f = E''.f)
              (hp : FakeEllipticCurve.IsIsogenyPair (r ^ d) E'' A'' φ φ') (hl : FakeEllipticCurve.PreservesLevel E'' A'' φ hφ),
              (pt' T E'' A'' gE'' hgE'' gA'' hgA'' φ φ' hφ hp hl).1 ≫ e =
                (pt T E'' A'' (gE'' ≫ g) hgE (gA'' ≫ hA) hgAA φ φ' hφ hp hl).1) →
            e ≫ κ S u A gA hgA X ξ pt hX = κ S' u' A' (hA ≫ gA) hgA' X' ξ' pt' hX') := by
  have hloc' : RelRepGlue.HLoc (𝒪 := 𝒪) (n := n) C r d 𝔄 := fun S _ _ _ _ u A gA hgA => hloc S u A gA hgA
  have hrig' : RelRepGlue.HRig Λ N n C := fun S _ _ u e he h1 h2 h3 => hrig S u e he h1 h2 h3
  refine ⟨Xd C 𝔄 hloc' hM hrig', qd C 𝔄 hloc' hM hrig', locallyOfFinitePresentation_qd C 𝔄 hloc' hM hrig',
    fun S _ _ _ _ u A gA hgA X ξ pt hX => kappaD C 𝔄 hloc' hM hrig' S u A gA hgA X ξ pt hX, ?_, ?_, ?_⟩
  · intro S _ _ _ _ u A gA hgA X ξ pt hX
    exact kappaD_B1 C 𝔄 hloc' hM hrig' S u A gA hgA X ξ pt hX
  · intro S _ _ _ _ u A gA hgA X ξ pt hX T x t h1 h2
    exact kappaD_B2 C 𝔄 hloc' hM hrig' S u A gA hgA X ξ pt hX T x t h1 h2
  · intro S S' _ _ _ _ _ _ _ _ _ _ _ u u' g hg hgP A gA hgA A' hA hhA hgA' X ξ pt hX X' ξ' pt' hX' e he₁ he₂
    exact kappaD_natural C 𝔄 hloc' hM hrig' S u A gA hgA X ξ pt hX S' u' g hg hgP A' hA hhA hgA' X' ξ' pt' hX' e he₁ he₂

end S_CerednikDrinfeld_QM_IsFineModuli_exists_locallyOfFinitePresentation_forall_representsOn_hom_isPullback_of_forall_withFullLevel
end P2MW
export P2MW.S_CerednikDrinfeld_QM_IsFineModuli_exists_locallyOfFinitePresentation_forall_representsOn_hom_isPullback_of_forall_withFullLevel (solution)
