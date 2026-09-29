-- Prove2me | solution 1 for CerednikDrinfeld.QM.FakeEllipticCurve.nonempty_mumfordBundle_iso_unit_of_pullback_iso_unit_of_ker_mul_maximalIdeal
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.141142+00:00
-- url     : https://prove2.me/submissions/e54ae194-da53-5f59-8ff6-b63e9a958204

import Definitions.Def_CerednikDrinfeld_QMFineModuli
import Definitions.Def_AlgebraicGeometry_PolarisedAbelianScheme
import Definitions.Def_AlgebraicGeometry_PolarisationRosati
import Definitions.Def_CerednikDrinfeld_QMCanonicalPol
import Definitions.Def_SheafOfModules_MonoidalV2
import Definitions.Def_AlgebraicGeometry_ModulesPullbackMonoidalV2
import Theorems.Thm_GoodReductionJacobian_AbelianSchemePropertyBundle_nonempty_iso_of_pullback_iso_of_sliceAt_one_of_isPullback_of_ker_mul_self_of_isNoetherianRing
import Theorems.Thm_AlgebraicGeometry_Polarisation_nonempty_mumfordBundle_iso_of_iso
import Theorems.Thm_AlgebraicGeometry_Polarisation_nonempty_mumfordBundle_pullback_iso_pullback_mumfordBundle_of_isPullback
import Theorems.Thm_GoodReductionJacobian_AbelianSchemePropertyBundle_nonempty_pullback_sliceAt_one_pullback_mumfordBundle_iso_unit_of_comp_one_eq
import Theorems.Thm_GoodReductionJacobian_AbelianSchemePropertyBundle_of_isPullback
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_dual_monoidalV2
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_tensor_monoidalV2
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_nonempty_mumfordBundle_iso_unit_of_pullback_iso_unit_of_ker_mul_maximalIdeal
p2m_attr_erase "instance" "AlgebraicGeometry.OModulePresheaf.isScalarTower AlgebraicGeometry.Scheme.OrderedAffineCover.instLinearOrder AlgebraicGeometry.OModulePresheaf.module AlgebraicGeometry.Scheme.OrderedAffineCover.instFintype AlgebraicGeometry.Scheme.OrderedAffineCover.instFintypeIdx AlgebraicGeometry.OModulePresheaf.addCommGroup AlgebraicGeometry.Scheme.OrderedAffineCover.instDecidableEqIdx AlgebraicGeometry.OModulePresheaf.moduleSections TwoChartCech.Sections.M0_moduleA TwoChartCech.Sections.M1_module TwoChartCech.Cover.A01_algebra TwoChartCech.Cover.A0_algebra TwoChartCech.Cover.A1_commRing TwoChartCech.Cover.A1_algebra TwoChartCech.Sections.M01_module TwoChartCech.Sections.M0_addCommGroup TwoChartCech.Sections.M0_tower TwoChartCech.Sections.M01_addCommGroup TwoChartCech.Cover.A0_commRing TwoChartCech.Sections.M1_tower TwoChartCech.Sections.M01_moduleA TwoChartCech.Sections.M0_module TwoChartCech.Sections.M1_moduleA TwoChartCech.Sections.M1_addCommGroup TwoChartCech.Cover.A01_commRing TwoChartCech.Sections.M01_tower CoherentBaseChange.TwoTermComplex.C0_module CoherentBaseChange.TwoTermComplex.C0_addCommGroup CoherentBaseChange.TwoTermComplex.C1_module CoherentBaseChange.TwoTermComplex.C1_addCommGroup CoherentBaseChange.TwoTermComplex.C0_free CoherentBaseChange.TwoTermComplex.C1_finite CoherentBaseChange.TwoTermComplex.C0_finite CoherentBaseChange.TwoTermComplex.C1_free PresheafOfModules.ExteriorPower.instModulePresheafAb AlgebraicGeometry.OModulePresheaf.Leray.relAltC_scalarTower AlgebraicGeometry.OModulePresheaf.Leray.ker_relAltd_modΓ AlgebraicGeometry.OModulePresheaf.Leray.relAltC_modΓ AlgebraicGeometry.OModulePresheaf.Leray.biC_abGrp AlgebraicGeometry.OModulePresheaf.Leray.relAltH_modΓ"
p2m_attr_erase "instance" "AlgebraicGeometry.OModulePresheaf.Leray.ker_relAltd_smul AlgebraicGeometry.OModulePresheaf.Leray.relAltH_scalarTower AlgebraicGeometry.OModulePresheaf.Leray.relAltH_smul AlgebraicGeometry.OModulePresheaf.Leray.biC_module AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instDecidableEqIdx AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instFintype AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instLinearOrder AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instFintypeIdx DoubleComplex.instModuleE₂I DoubleComplex.Bounded.modR DoubleComplex.instModuleE₂II DoubleComplex.instAddCommGroupE₂II DoubleComplex.Bounded.abGrp DoubleComplex.instAddCommGroupE₂I AlgebraicGeometry.Scheme.OrderedOpenFamily.instFintype AlgebraicGeometry.Scheme.OrderedOpenFamily.instDecidableEqIdx AlgebraicGeometry.Scheme.OrderedOpenFamily.instLinearOrder AlgebraicGeometry.Scheme.OrderedOpenFamily.instFintypeIdx CochainCx.Bounded.abGrp CochainCx.Bounded.modR AlgebraicGeometry.SubalgebraStages.compactSpace_pullback AlgebraicGeometry.SubalgebraStages.quasiSeparatedSpace_pullback AlgebraicGeometry.SubalgebraStages.compactSpace_obj AlgebraicGeometry.SubalgebraStages.quasiSeparatedSpace_obj AlgebraicGeometry.SubalgebraStages.quasiCompact_snd AlgebraicGeometry.SubalgebraStages.isAffineHom_leg AlgebraicGeometry.SubalgebraStages.isAffineHom_trans AlgebraicGeometry.SubalgebraStages.isAffineHom_diagram_map AlgebraicGeometry.SubalgebraStages.quasiSeparated_snd AlgebraicGeometry.SubalgebraStages.isCofiltered_op IsDirectLimit.Module.instDirectLimitCoeLinearMapIdOfOfNonempty AdicCompletion.instIsLocalRingMaximalIdeal"
p2m_attr_erase "simp" "AlgebraicGeometry.Scheme.OrderedAffineCover.mk.injEq AlgebraicGeometry.OModulePresheaf.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCover.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.mk.injEq AlgebraicGeometry.Scheme.TwoAffineOpenCover.mk.injEq AlgebraicGeometry.Scheme.TwoAffineOpenCover.mk.sizeOf_spec AlgebraicGeometry.Scheme.TwoAffineOpenCover.pullback_U1 AlgebraicGeometry.Scheme.TwoAffineOpenCover.pullback_U0 TwoChartCech.Sections.mk.injEq TwoChartCech.Cover.mk.injEq TwoChartCech.GrothendieckComplex.mk.injEq TwoChartCech.Sections.mk.sizeOf_spec TwoChartCech.Cover.mk.sizeOf_spec TwoChartCech.Cover.lineBundle_r0_apply TwoChartCech.GrothendieckComplex.mk.sizeOf_spec TwoChartCech.Cover.lineBundle_r1_apply CoherentBaseChange.TwoTermComplex.mk.sizeOf_spec CoherentBaseChange.TwoTermComplex.mk.injEq AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_neg AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_zero AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_sub AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_add AlgebraicGeometry.Scheme.Hom.kaehlerPresheaf_obj PresheafOfModules.exteriorPower_map_ιMulti PresheafOfModules.ExteriorPower.appₗ_apply AlgebraicGeometry.Scheme.Modules.exteriorPower_obj AlgebraicGeometry.OModulePresheaf.Leray.restrictToPreimage_U AlgebraicGeometry.Scheme.OrderedAffineCover.toCoverOf_U AlgebraicGeometry.Scheme.OrderedAffineCoverOf.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCoverOf.mk.injEq AlgebraicGeometry.Scheme.OrderedAffineCover.restrict_U AlgebraicGeometry.OModulePresheaf.Hom.mk.injEq AlgebraicGeometry.OModulePresheaf.Hom.id_app AlgebraicGeometry.OModulePresheaf.AffHom.appSections_apply AlgebraicGeometry.OModulePresheaf.AffHom.comp_app AlgebraicGeometry.OModulePresheaf.AffSES.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.AffHom.kerMap_coe AlgebraicGeometry.OModulePresheaf.AffHom.id_app AlgebraicGeometry.OModulePresheaf.Hom.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.Hom.toAffHom_app"
p2m_attr_erase "simp" "AlgebraicGeometry.OModulePresheaf.SES.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.AffHom.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.Hom.comp_app AlgebraicGeometry.OModulePresheaf.SES.mk.injEq AlgebraicGeometry.OModulePresheaf.AffHom.mk.injEq AlgebraicGeometry.OModulePresheaf.Hom.appSections_apply AlgebraicGeometry.OModulePresheaf.AffSES.mk.injEq DoubleComplex.Bounded.mk.injEq DoubleComplex.Bounded.mk.sizeOf_spec DoubleComplex.Convergence.mk.injEq DoubleComplex.Convergence.mk.sizeOf_spec DoubleComplex.SubQuot.mk.sizeOf_spec DoubleComplex.SubQuot.mk.injEq RegularLocalRingQuotientAscent.dualNumberFst_apply GoodReductionJacobian.RelativeGroupLaw.baseChangePointToBase_ofBase GoodReductionJacobian.RelativeGroupLaw.baseChangePointToBase_coe GoodReductionJacobian.RelativeGroupLaw.baseChangePointOfBase_coe GoodReductionJacobian.RelativeGroupLaw.baseChange_inv GoodReductionJacobian.RelativeGroupLaw.baseChangePointOfBase_toBase GoodReductionJacobian.RelativeGroupLaw.baseChange_mul GoodReductionJacobian.RelativeGroupLaw.baseChange_one NeronModelInfra.NeronModelPropertyBundle.endExtensionEquiv_symm_restrict NeronModelInfra.schemeHomOverComp_id_left NeronModelInfra.schemeHomOverComp_id_right NeronModelInfra.schemeHomOverId_coe NeronModelInfra.NeronModelPropertyBundle.endExtensionEquiv_apply NeronModelInfra.NeronModelPropertyBundle.restrict_endExtensionEquiv_symm NeronModelInfra.schemeHomOverComp_coe NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_fst NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_snd NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_fst NeronSpecialFibreInfra.neronEndRestrictEquiv_apply NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_fst_assoc NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_snd NeronSpecialFibreInfra.neronEndExtension_genericFibreRestrict NeronSpecialFibreInfra.specClosedFibreInclusion_eq NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_fst_assoc NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_snd_assoc NeronSpecialFibreInfra.genericFibreRestrict_neronEndExtension NeronSpecialFibreInfra.homOverId_coe"
p2m_attr_erase "simp" "NeronSpecialFibreInfra.homOverComp_coe NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_snd_assoc GoodReductionJacobian.RelativeGroupLaw.fibre_inv GoodReductionJacobian.RelativeGroupLaw.fibrePointToBase_coe GoodReductionJacobian.RelativeGroupLaw.fibrePointOfBase_toBase GoodReductionJacobian.RelativeGroupLaw.fibre_mul GoodReductionJacobian.RelativeGroupLaw.fibrePointToBase_ofBase GoodReductionJacobian.RelativeGroupLaw.fibre_one GoodReductionJacobian.RelativeGroupLaw.fibrePointOfBase_coe AlgebraicGeometry.schemeFibreEndo_snd AlgebraicGeometry.schemeFibreEndo_fst AlgebraicGeometry.Scheme.OrderedOpenFamily.mk.injEq AlgebraicGeometry.Scheme.OrderedOpenFamily.mk.sizeOf_spec CochainCx.Bounded.mk.sizeOf_spec CochainCx.Bounded.mk.injEq AlgebraicGeometry.SubalgebraStages.specCone_π_app AlgebraicGeometry.SubalgebraStages.specLeg_specHom AlgebraicGeometry.SubalgebraStages.specLeg_specTrans AlgebraicGeometry.SubalgebraStages.cone_pt AlgebraicGeometry.SubalgebraStages.trans_fst AlgebraicGeometry.SubalgebraStages.diagram_obj AlgebraicGeometry.SubalgebraStages.leg_snd AlgebraicGeometry.SubalgebraStages.diagram_map AlgebraicGeometry.SubalgebraStages.specTrans_refl AlgebraicGeometry.SubalgebraStages.trans_snd AlgebraicGeometry.SubalgebraStages.specTrans_specHom AlgebraicGeometry.SubalgebraStages.specCone_pt AlgebraicGeometry.SubalgebraStages.cone_π_app AlgebraicGeometry.SubalgebraStages.specDiagram_map AlgebraicGeometry.SubalgebraStages.specDiagram_obj AlgebraicGeometry.SubalgebraStages.leg_fst AlgebraicGeometry.SubalgebraStages.leg_trans IsDirectLimit.Module.linearEquiv_symm_apply IsDirectLimit.linearEquiv_symm_apply IsDirectLimit.lift_of IsDirectLimit.Module.linearEquiv_apply IsDirectLimit.Module.lift_of IsDirectLimit.Equiv_apply"

set_option autoImplicit false

open scoped TensorProduct Quaternion
p2m_open "CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry QuaternionAlgebra CerednikDrinfeld CerednikDrinfeld.QM NeronModelInfra GoodReductionJacobian AlgebraicGeometry.Polarisation"

namespace LambdaInf

theorem mul_val_congr {R : Type} [CommRing R] {A : Scheme.{0}} {f : A ⟶ Spec (CommRingCat.of R)}
    (L : RelativeGroupLaw R f) {T : Scheme.{0}} {t₁ t₂ : T ⟶ Spec (CommRingCat.of R)} (h : t₁ = t₂)
    (P₁ Q₁ : SchemeHomOver t₁ f) (P₂ Q₂ : SchemeHomOver t₂ f) (hP : P₁.1 = P₂.1) (hQ : Q₁.1 = Q₂.1) :
    (L.mul t₁ P₁ Q₁).1 = (L.mul t₂ P₂ Q₂).1 := by
  subst h
  obtain rfl : P₁ = P₂ := Subtype.ext hP
  obtain rfl : Q₁ = Q₂ := Subtype.ext hQ
  rfl

section transition

variable {S : Type} [CommRing S] {A : Scheme.{0}} (f : A ⟶ Spec (CommRingCat.of S))
  (R₁ R₀ : Type) [CommRing R₁] [CommRing R₀] [Algebra S R₁] [Algebra S R₀]
  (φ : R₁ →+* R₀) (hφ : φ.comp (algebraMap S R₁) = algebraMap S R₀)
  (t : pullback f (Spec.map (CommRingCat.ofHom (algebraMap S R₀))) ⟶ pullback f (Spec.map (CommRingCat.ofHom (algebraMap S R₁))))
  (ht₁ : t ≫ pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap S R₁))) = pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap S R₀))))
  (ht₂ : t ≫ pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap S R₁))) =
    pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap S R₀))) ≫ Spec.map (CommRingCat.ofHom φ))

include hφ in
theorem spec_comp : Spec.map (CommRingCat.ofHom φ) ≫ Spec.map (CommRingCat.ofHom (algebraMap S R₁)) =
    Spec.map (CommRingCat.ofHom (algebraMap S R₀)) := by
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, hφ]

include hφ ht₁ ht₂ in

theorem isPullback_transition :
    IsPullback t (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap S R₀))))
      (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap S R₁)))) (Spec.map (CommRingCat.ofHom φ)) := by
  refine IsPullback.of_right (h₁₂ := pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap S R₁)))) ?_ ht₂
    (IsPullback.of_hasPullback f (Spec.map (CommRingCat.ofHom (algebraMap S R₁))))
  rw [ht₁, spec_comp R₁ R₀ φ hφ]
  exact IsPullback.of_hasPullback f (Spec.map (CommRingCat.ofHom (algebraMap S R₀)))

variable (LS : RelativeGroupLaw S f)
  (L₁ : RelativeGroupLaw R₁ (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap S R₁)))))
  (hL₁ : ∀ (T : Scheme) (t' : T ⟶ Spec (CommRingCat.of R₁))
      (P Q : SchemeHomOver t' (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap S R₁))))),
      (L₁.mul t' P Q).1 ≫ pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap S R₁))) =
        (LS.mul (t' ≫ (Spec.map (CommRingCat.ofHom (algebraMap S R₁))))
          ⟨P.1 ≫ pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap S R₁))), by rw [Category.assoc, pullback.condition, ← Category.assoc, P.2]⟩
          ⟨Q.1 ≫ pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap S R₁))), by rw [Category.assoc, pullback.condition, ← Category.assoc, Q.2]⟩).1)
  (L₀ : RelativeGroupLaw R₀ (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap S R₀)))))
  (hL₀ : ∀ (T : Scheme) (t' : T ⟶ Spec (CommRingCat.of R₀))
      (P Q : SchemeHomOver t' (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap S R₀))))),
      (L₀.mul t' P Q).1 ≫ pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap S R₀))) =
        (LS.mul (t' ≫ (Spec.map (CommRingCat.ofHom (algebraMap S R₀))))
          ⟨P.1 ≫ pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap S R₀))), by rw [Category.assoc, pullback.condition, ← Category.assoc, P.2]⟩
          ⟨Q.1 ≫ pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap S R₀))), by rw [Category.assoc, pullback.condition, ← Category.assoc, Q.2]⟩).1)

include hφ ht₁ ht₂ hL₁ hL₀ in

theorem transition_mul {T : Scheme.{0}} (t' : T ⟶ Spec (CommRingCat.of R₀))
    (P Q : SchemeHomOver t' (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap S R₀))))) :
    (L₀.mul t' P Q).1 ≫ t =
      (L₁.mul (t' ≫ Spec.map (CommRingCat.ofHom φ))
        ⟨P.1 ≫ t, by rw [Category.assoc, (isPullback_transition f R₁ R₀ φ hφ t ht₁ ht₂).w, ← Category.assoc, P.2]⟩
        ⟨Q.1 ≫ t, by rw [Category.assoc, (isPullback_transition f R₁ R₀ φ hφ t ht₁ ht₂).w, ← Category.assoc, Q.2]⟩).1 := by
  apply pullback.hom_ext
  · rw [Category.assoc, ht₁, hL₀, hL₁]
    exact mul_val_congr LS (by rw [Category.assoc, spec_comp R₁ R₀ φ hφ]) _ _ _ _
      (by change P.1 ≫ _ = (P.1 ≫ t) ≫ _; rw [Category.assoc, ht₁])
      (by change Q.1 ≫ _ = (Q.1 ≫ t) ≫ _; rw [Category.assoc, ht₁])
  · have h1 : ((L₀.mul t' P Q).1 ≫ t) ≫ pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap S R₁))) =
        t' ≫ Spec.map (CommRingCat.ofHom φ) := by
      rw [Category.assoc, ht₂, ← Category.assoc, (L₀.mul t' P Q).2]
    rw [h1]
    exact ((L₁.mul _ _ _).2).symm

end transition

theorem ker_mul_ker_eq_bot {R₁ R₀ : Type} [CommRing R₁] [IsLocalRing R₁] [CommRing R₀] [Nontrivial R₀]
    (φ : R₁ →+* R₀) (hsmall : ∀ x ∈ RingHom.ker φ, ∀ m ∈ IsLocalRing.maximalIdeal R₁, x * m = 0) :
    RingHom.ker φ * RingHom.ker φ = ⊥ ∧ IsLocalRing.maximalIdeal R₁ * RingHom.ker φ = ⊥ := by
  have hle : RingHom.ker φ ≤ IsLocalRing.maximalIdeal R₁ := IsLocalRing.le_maximalIdeal (RingHom.ker_ne_top φ)
  refine ⟨eq_bot_iff.2 (Ideal.mul_le.2 fun x hx y hy => ?_), eq_bot_iff.2 (Ideal.mul_le.2 fun m hm x hx => ?_)⟩
  · exact (Ideal.mem_bot).2 (hsmall x hx y (hle hy))
  · rw [mul_comm]; exact (Ideal.mem_bot).2 (hsmall x hx m hm)

theorem nonempty_dual_unit_iso (X : Scheme.{0}) :
    Nonempty (Scheme.Modules.dual (𝟙_ X.Modules) ≅ 𝟙_ X.Modules) := by
  obtain ⟨-, ⟨e⟩⟩ := Scheme.Modules.IsInvertible.dual_monoidalV2 (Scheme.Modules.isInvertible_unit X)
  exact ⟨(λ_ _).symm ≪≫ e⟩

theorem nonempty_mumfordBundle_unit_iso {S : Type} [CommRing S] {A : Scheme.{0}}
    (f : A ⟶ Spec (CommRingCat.of S)) (L : RelativeGroupLaw S f) :
    Nonempty (mumfordBundle f L (𝟙_ _) ≅ 𝟙_ _) := by
  obtain ⟨ed⟩ := nonempty_dual_unit_iso A
  unfold mumfordBundle
  exact ⟨(Scheme.Modules.pullbackTensorUnitObjIso _ ⊗ᵢ
    (((Scheme.Modules.pullback _).mapIso ed ≪≫ Scheme.Modules.pullbackTensorUnitObjIso _) ⊗ᵢ
      ((Scheme.Modules.pullback _).mapIso ed ≪≫ Scheme.Modules.pullbackTensorUnitObjIso _))) ≪≫
    λ_ _ ≪≫ λ_ _⟩

theorem isInvertible_mumfordBundle {S : Type} [CommRing S] {A : Scheme.{0}}
    (f : A ⟶ Spec (CommRingCat.of S)) (L : RelativeGroupLaw S f) {𝓛 : A.Modules} (h : Scheme.Modules.IsInvertible 𝓛) :
    Scheme.Modules.IsInvertible (mumfordBundle f L 𝓛) := by
  have hd := (Scheme.Modules.IsInvertible.dual_monoidalV2 h).1
  unfold mumfordBundle
  exact Scheme.Modules.IsInvertible.tensor_monoidalV2 (Scheme.Modules.IsInvertible.pullback _ h)
    (Scheme.Modules.IsInvertible.tensor_monoidalV2 (Scheme.Modules.IsInvertible.pullback _ hd)
      (Scheme.Modules.IsInvertible.pullback _ hd))

end LambdaInf

open LambdaInf in
theorem solution
    {q q' : ℕ} [Fact q.Prime] [Fact q'.Prime] (hqq' : q' ≠ q)
    {a b : ℚ} (hB : IsIndefiniteRamifiedExactlyAt a b q q')
    (Λ : Submodule ℤ ℍ[ℚ, a, b]) (hΛ : IsMaximalOrder Λ)
    (μ : ↥Λ) (hμ : (μ : ℍ[ℚ, a, b]) * (μ : ℍ[ℚ, a, b]) = -(((q * q' : ℕ) : ℚ) • (1 : ℍ[ℚ, a, b])))
    (star : ↥Λ → ↥Λ) (hstar : ∀ x : ↥Λ, (μ : ℍ[ℚ, a, b]) * (star x : ℍ[ℚ, a, b]) = Star.star (x : ℍ[ℚ, a, b]) * μ)
    (N : ℕ) (S : Type) [CommRing S] (E : FakeEllipticCurve Λ N S)

    (R₁ R₀ : Type) [CommRing R₁] [IsLocalRing R₁] [IsNoetherianRing R₁]
    [CommRing R₀] [Nontrivial R₀] [Algebra S R₁] [Algebra S R₀]
    (φ : R₁ →ₐ[S] R₀) (hφ : Function.Surjective φ)
    (hsmall : ∀ x ∈ RingHom.ker φ.toRingHom, ∀ m ∈ IsLocalRing.maximalIdeal R₁, x * m = 0)

    (t : pullback E.f (Spec.map (CommRingCat.ofHom (algebraMap S R₀))) ⟶ pullback E.f (Spec.map (CommRingCat.ofHom (algebraMap S R₁))))
    (ht₁ : t ≫ pullback.fst E.f (Spec.map (CommRingCat.ofHom (algebraMap S R₁))) = pullback.fst E.f (Spec.map (CommRingCat.ofHom (algebraMap S R₀))))
    (ht₂ : t ≫ pullback.snd E.f (Spec.map (CommRingCat.ofHom (algebraMap S R₁))) =
      pullback.snd E.f (Spec.map (CommRingCat.ofHom (algebraMap S R₀))) ≫ Spec.map (CommRingCat.ofHom φ.toRingHom))

    (L₁ : RelativeGroupLaw R₁ (pullback.snd E.f (Spec.map (CommRingCat.ofHom (algebraMap S R₁)))))
    (hL₁ : ∀ (T : Scheme) (t' : T ⟶ Spec (CommRingCat.of R₁))
        (P Q : SchemeHomOver t' (pullback.snd E.f (Spec.map (CommRingCat.ofHom (algebraMap S R₁))))),
        (L₁.mul t' P Q).1 ≫ pullback.fst E.f (Spec.map (CommRingCat.ofHom (algebraMap S R₁))) =
          (E.L.mul (t' ≫ (Spec.map (CommRingCat.ofHom (algebraMap S R₁))))
            ⟨P.1 ≫ pullback.fst E.f (Spec.map (CommRingCat.ofHom (algebraMap S R₁))), by rw [Category.assoc, pullback.condition, ← Category.assoc, P.2]⟩
            ⟨Q.1 ≫ pullback.fst E.f (Spec.map (CommRingCat.ofHom (algebraMap S R₁))), by rw [Category.assoc, pullback.condition, ← Category.assoc, Q.2]⟩).1)
    (L₀ : RelativeGroupLaw R₀ (pullback.snd E.f (Spec.map (CommRingCat.ofHom (algebraMap S R₀)))))
    (hL₀ : ∀ (T : Scheme) (t' : T ⟶ Spec (CommRingCat.of R₀))
        (P Q : SchemeHomOver t' (pullback.snd E.f (Spec.map (CommRingCat.ofHom (algebraMap S R₀))))),
        (L₀.mul t' P Q).1 ≫ pullback.fst E.f (Spec.map (CommRingCat.ofHom (algebraMap S R₀))) =
          (E.L.mul (t' ≫ (Spec.map (CommRingCat.ofHom (algebraMap S R₀))))
            ⟨P.1 ≫ pullback.fst E.f (Spec.map (CommRingCat.ofHom (algebraMap S R₀))), by rw [Category.assoc, pullback.condition, ← Category.assoc, P.2]⟩
            ⟨Q.1 ≫ pullback.fst E.f (Spec.map (CommRingCat.ofHom (algebraMap S R₀))), by rw [Category.assoc, pullback.condition, ← Category.assoc, Q.2]⟩).1)
    (d : (pullback E.f (Spec.map (CommRingCat.ofHom (algebraMap S R₁)))).Modules) (hd : Scheme.Modules.IsInvertible d) (hd₀ : Nonempty ((Scheme.Modules.pullback t).obj d ≅ 𝟙_ _)) :
    Nonempty (mumfordBundle (pullback.snd E.f (Spec.map (CommRingCat.ofHom (algebraMap S R₁)))) L₁ d ≅ 𝟙_ _) := by
  classical
  letI instAlg : Algebra R₁ R₀ := φ.toRingHom.toAlgebra
  have hφc : φ.toRingHom.comp (algebraMap S R₁) = algebraMap S R₀ := RingHom.ext fun x => φ.commutes x
  obtain ⟨hK, hKm⟩ := ker_mul_ker_eq_bot φ.toRingHom hsmall

  have hg := isPullback_transition E.f R₁ R₀ φ.toRingHom hφc t ht₁ ht₂
  have hg_mul := fun {T : Scheme.{0}} => transition_mul E.f R₁ R₀ φ.toRingHom hφc t ht₁ ht₂ E.L L₁ hL₁ L₀ hL₀ (T := T)

  have hA : AbelianSchemePropertyBundle R₁ (pullback.snd E.f (Spec.map (CommRingCat.ofHom (algebraMap S R₁)))) :=
    AbelianSchemePropertyBundle.of_isPullback E.bundle
      (IsPullback.of_hasPullback E.f (Spec.map (CommRingCat.ofHom (algebraMap S R₁))))

  have hM : Scheme.Modules.IsInvertible (mumfordBundle (pullback.snd E.f (Spec.map (CommRingCat.ofHom (algebraMap S R₁)))) L₁ d) :=
    isInvertible_mumfordBundle _ L₁ hd
  have hM' : Scheme.Modules.IsInvertible
      (𝟙_ (pullback (pullback.snd E.f (Spec.map (CommRingCat.ofHom (algebraMap S R₁))))
        (pullback.snd E.f (Spec.map (CommRingCat.ofHom (algebraMap S R₁))))).Modules) :=
    Scheme.Modules.isInvertible_unit _

  obtain ⟨e0⟩ := hd₀
  obtain ⟨ebc⟩ := nonempty_mumfordBundle_pullback_iso_pullback_mumfordBundle_of_isPullback R₁ R₀ φ.toRingHom
    (pullback.snd E.f (Spec.map (CommRingCat.ofHom (algebraMap S R₁)))) L₁
    (pullback.snd E.f (Spec.map (CommRingCat.ofHom (algebraMap S R₀)))) L₀ t hg hg_mul d hd
  obtain ⟨ecg⟩ := nonempty_mumfordBundle_iso_of_iso (pullback.snd E.f (Spec.map (CommRingCat.ofHom (algebraMap S R₀)))) L₀ e0
  obtain ⟨eun⟩ := nonempty_mumfordBundle_unit_iso (pullback.snd E.f (Spec.map (CommRingCat.ofHom (algebraMap S R₀)))) L₀

  obtain ⟨⟨es1⟩, ⟨es2⟩⟩ :=
    AbelianSchemePropertyBundle.nonempty_pullback_sliceAt_one_pullback_mumfordBundle_iso_unit_of_comp_one_eq L₁ hA d hd
      (𝟙 _) (𝟙 _) (Category.id_comp _) (Category.id_comp _) (Category.comp_id _) (Category.comp_id _)
      (𝟙 _) (by simp) (by simp)
  obtain ⟨e⟩ :=
    AbelianSchemePropertyBundle.nonempty_iso_of_pullback_iso_of_sliceAt_one_of_isPullback_of_ker_mul_self_of_isNoetherianRing
      hφ hK hKm L₁ hA L₀ t hg hg_mul _ _ hM hM'
      ⟨ebc.symm ≪≫ ecg ≪≫ eun ≪≫ (Scheme.Modules.pullbackTensorUnitObjIso _).symm⟩
      ⟨((Scheme.Modules.pullback _).mapIso ((Scheme.Modules.pullbackId _).app _)).symm ≪≫ es1⟩
      ⟨((Scheme.Modules.pullback _).mapIso ((Scheme.Modules.pullback _).mapIso
          ((Scheme.Modules.pullbackId _).app _))).symm ≪≫ es2⟩
      ⟨Scheme.Modules.pullbackTensorUnitObjIso _⟩
      ⟨(Scheme.Modules.pullback _).mapIso (Scheme.Modules.pullbackTensorUnitObjIso _) ≪≫
          Scheme.Modules.pullbackTensorUnitObjIso _⟩
  exact ⟨e⟩

end S_CerednikDrinfeld_QM_FakeEllipticCurve_nonempty_mumfordBundle_iso_unit_of_pullback_iso_unit_of_ker_mul_maximalIdeal
end P2MW
export P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_nonempty_mumfordBundle_iso_unit_of_pullback_iso_unit_of_ker_mul_maximalIdeal (solution)
