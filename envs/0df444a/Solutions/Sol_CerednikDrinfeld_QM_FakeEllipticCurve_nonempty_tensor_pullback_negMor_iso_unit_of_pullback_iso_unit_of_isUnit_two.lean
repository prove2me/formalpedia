-- Prove2me | solution 1 for CerednikDrinfeld.QM.FakeEllipticCurve.nonempty_tensor_pullback_negMor_iso_unit_of_pullback_iso_unit_of_isUnit_two
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.141142+00:00
-- url     : https://prove2.me/submissions/f6b0a02e-958f-5c14-8ae7-2ea9f0d47666

import Definitions.Def_CerednikDrinfeld_QMFineModuli
import Definitions.Def_AlgebraicGeometry_PolarisedAbelianScheme
import Definitions.Def_AlgebraicGeometry_PolarisationRosati
import Definitions.Def_CerednikDrinfeld_QMCanonicalPol
import Definitions.Def_SheafOfModules_MonoidalV2
import Definitions.Def_AlgebraicGeometry_ModulesPullbackMonoidalV2
import Theorems.Thm_GoodReductionJacobian_AbelianSchemePropertyBundle_nonempty_iso_unit_of_pullback_iso_unit_of_isSymmetric_of_ker_mul_maximalIdeal_of_isUnit_two_of_isNoetherianRing
import Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_comp_negMor_eq_negMor_comp_of_compatible_univ
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_tensor_monoidalV2
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_nonempty_tensor_pullback_negMor_iso_unit_of_pullback_iso_unit_of_isUnit_two
p2m_attr_erase "instance" "AlgebraicGeometry.OModulePresheaf.isScalarTower AlgebraicGeometry.Scheme.OrderedAffineCover.instLinearOrder AlgebraicGeometry.OModulePresheaf.module AlgebraicGeometry.Scheme.OrderedAffineCover.instFintype AlgebraicGeometry.Scheme.OrderedAffineCover.instFintypeIdx AlgebraicGeometry.OModulePresheaf.addCommGroup AlgebraicGeometry.Scheme.OrderedAffineCover.instDecidableEqIdx AlgebraicGeometry.OModulePresheaf.moduleSections TwoChartCech.Sections.M0_moduleA TwoChartCech.Sections.M1_module TwoChartCech.Cover.A01_algebra TwoChartCech.Cover.A0_algebra TwoChartCech.Cover.A1_commRing TwoChartCech.Cover.A1_algebra TwoChartCech.Sections.M01_module TwoChartCech.Sections.M0_addCommGroup TwoChartCech.Sections.M0_tower TwoChartCech.Sections.M01_addCommGroup TwoChartCech.Cover.A0_commRing TwoChartCech.Sections.M1_tower TwoChartCech.Sections.M01_moduleA TwoChartCech.Sections.M0_module TwoChartCech.Sections.M1_moduleA TwoChartCech.Sections.M1_addCommGroup TwoChartCech.Cover.A01_commRing TwoChartCech.Sections.M01_tower CoherentBaseChange.TwoTermComplex.C0_module CoherentBaseChange.TwoTermComplex.C0_addCommGroup CoherentBaseChange.TwoTermComplex.C1_module CoherentBaseChange.TwoTermComplex.C1_addCommGroup CoherentBaseChange.TwoTermComplex.C0_free CoherentBaseChange.TwoTermComplex.C1_finite CoherentBaseChange.TwoTermComplex.C0_finite CoherentBaseChange.TwoTermComplex.C1_free PresheafOfModules.ExteriorPower.instModulePresheafAb AlgebraicGeometry.SubalgebraStages.compactSpace_pullback AlgebraicGeometry.SubalgebraStages.quasiSeparatedSpace_pullback AlgebraicGeometry.SubalgebraStages.compactSpace_obj AlgebraicGeometry.SubalgebraStages.quasiSeparatedSpace_obj AlgebraicGeometry.SubalgebraStages.quasiCompact_snd"
p2m_attr_erase "instance" "AlgebraicGeometry.SubalgebraStages.isAffineHom_leg AlgebraicGeometry.SubalgebraStages.isAffineHom_trans AlgebraicGeometry.SubalgebraStages.isAffineHom_diagram_map AlgebraicGeometry.SubalgebraStages.quasiSeparated_snd AlgebraicGeometry.SubalgebraStages.isCofiltered_op IsDirectLimit.Module.instDirectLimitCoeLinearMapIdOfOfNonempty AdicCompletion.instIsLocalRingMaximalIdeal AlgebraicGeometry.OModulePresheaf.Leray.relAltC_scalarTower AlgebraicGeometry.OModulePresheaf.Leray.ker_relAltd_modΓ AlgebraicGeometry.OModulePresheaf.Leray.relAltC_modΓ AlgebraicGeometry.OModulePresheaf.Leray.biC_abGrp AlgebraicGeometry.OModulePresheaf.Leray.relAltH_modΓ AlgebraicGeometry.OModulePresheaf.Leray.ker_relAltd_smul AlgebraicGeometry.OModulePresheaf.Leray.relAltH_scalarTower AlgebraicGeometry.OModulePresheaf.Leray.relAltH_smul AlgebraicGeometry.OModulePresheaf.Leray.biC_module AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instDecidableEqIdx AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instFintype AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instLinearOrder AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instFintypeIdx DoubleComplex.instModuleE₂I DoubleComplex.Bounded.modR DoubleComplex.instModuleE₂II DoubleComplex.instAddCommGroupE₂II DoubleComplex.Bounded.abGrp DoubleComplex.instAddCommGroupE₂I AlgebraicGeometry.Scheme.OrderedOpenFamily.instFintype AlgebraicGeometry.Scheme.OrderedOpenFamily.instDecidableEqIdx AlgebraicGeometry.Scheme.OrderedOpenFamily.instLinearOrder AlgebraicGeometry.Scheme.OrderedOpenFamily.instFintypeIdx CochainCx.Bounded.abGrp CochainCx.Bounded.modR"
p2m_attr_erase "simp" "AlgebraicGeometry.Scheme.OrderedAffineCover.mk.injEq AlgebraicGeometry.OModulePresheaf.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCover.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.mk.injEq AlgebraicGeometry.Scheme.TwoAffineOpenCover.mk.injEq AlgebraicGeometry.Scheme.TwoAffineOpenCover.mk.sizeOf_spec AlgebraicGeometry.Scheme.TwoAffineOpenCover.pullback_U1 AlgebraicGeometry.Scheme.TwoAffineOpenCover.pullback_U0 TwoChartCech.Sections.mk.injEq TwoChartCech.Cover.mk.injEq TwoChartCech.GrothendieckComplex.mk.injEq TwoChartCech.Sections.mk.sizeOf_spec TwoChartCech.Cover.mk.sizeOf_spec TwoChartCech.Cover.lineBundle_r0_apply TwoChartCech.GrothendieckComplex.mk.sizeOf_spec TwoChartCech.Cover.lineBundle_r1_apply CoherentBaseChange.TwoTermComplex.mk.sizeOf_spec CoherentBaseChange.TwoTermComplex.mk.injEq AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_neg AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_zero AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_sub AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_add AlgebraicGeometry.Scheme.Hom.kaehlerPresheaf_obj PresheafOfModules.exteriorPower_map_ιMulti PresheafOfModules.ExteriorPower.appₗ_apply AlgebraicGeometry.Scheme.Modules.exteriorPower_obj AlgebraicGeometry.SubalgebraStages.specCone_π_app AlgebraicGeometry.SubalgebraStages.specLeg_specHom AlgebraicGeometry.SubalgebraStages.specLeg_specTrans AlgebraicGeometry.SubalgebraStages.cone_pt AlgebraicGeometry.SubalgebraStages.trans_fst AlgebraicGeometry.SubalgebraStages.diagram_obj AlgebraicGeometry.SubalgebraStages.leg_snd AlgebraicGeometry.SubalgebraStages.diagram_map AlgebraicGeometry.SubalgebraStages.specTrans_refl AlgebraicGeometry.SubalgebraStages.trans_snd AlgebraicGeometry.SubalgebraStages.specTrans_specHom AlgebraicGeometry.SubalgebraStages.specCone_pt AlgebraicGeometry.SubalgebraStages.cone_π_app AlgebraicGeometry.SubalgebraStages.specDiagram_map"
p2m_attr_erase "simp" "AlgebraicGeometry.SubalgebraStages.specDiagram_obj AlgebraicGeometry.SubalgebraStages.leg_fst AlgebraicGeometry.SubalgebraStages.leg_trans IsDirectLimit.Module.linearEquiv_symm_apply IsDirectLimit.linearEquiv_symm_apply IsDirectLimit.lift_of IsDirectLimit.Module.linearEquiv_apply IsDirectLimit.Module.lift_of IsDirectLimit.Equiv_apply RegularLocalRingQuotientAscent.dualNumberFst_apply GoodReductionJacobian.RelativeGroupLaw.baseChangePointToBase_ofBase GoodReductionJacobian.RelativeGroupLaw.baseChangePointToBase_coe GoodReductionJacobian.RelativeGroupLaw.baseChangePointOfBase_coe GoodReductionJacobian.RelativeGroupLaw.baseChange_inv GoodReductionJacobian.RelativeGroupLaw.baseChangePointOfBase_toBase GoodReductionJacobian.RelativeGroupLaw.baseChange_mul GoodReductionJacobian.RelativeGroupLaw.baseChange_one NeronModelInfra.NeronModelPropertyBundle.endExtensionEquiv_symm_restrict NeronModelInfra.schemeHomOverComp_id_left NeronModelInfra.schemeHomOverComp_id_right NeronModelInfra.schemeHomOverId_coe NeronModelInfra.NeronModelPropertyBundle.endExtensionEquiv_apply NeronModelInfra.NeronModelPropertyBundle.restrict_endExtensionEquiv_symm NeronModelInfra.schemeHomOverComp_coe NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_fst NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_snd NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_fst NeronSpecialFibreInfra.neronEndRestrictEquiv_apply NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_fst_assoc NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_snd NeronSpecialFibreInfra.neronEndExtension_genericFibreRestrict NeronSpecialFibreInfra.specClosedFibreInclusion_eq NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_fst_assoc NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_snd_assoc NeronSpecialFibreInfra.genericFibreRestrict_neronEndExtension NeronSpecialFibreInfra.homOverId_coe NeronSpecialFibreInfra.homOverComp_coe NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_snd_assoc GoodReductionJacobian.RelativeGroupLaw.fibre_inv GoodReductionJacobian.RelativeGroupLaw.fibrePointToBase_coe"
p2m_attr_erase "simp" "GoodReductionJacobian.RelativeGroupLaw.fibrePointOfBase_toBase GoodReductionJacobian.RelativeGroupLaw.fibre_mul GoodReductionJacobian.RelativeGroupLaw.fibrePointToBase_ofBase GoodReductionJacobian.RelativeGroupLaw.fibre_one GoodReductionJacobian.RelativeGroupLaw.fibrePointOfBase_coe AlgebraicGeometry.schemeFibreEndo_snd AlgebraicGeometry.schemeFibreEndo_fst AlgebraicGeometry.OModulePresheaf.Leray.restrictToPreimage_U AlgebraicGeometry.Scheme.OrderedAffineCover.toCoverOf_U AlgebraicGeometry.Scheme.OrderedAffineCoverOf.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCoverOf.mk.injEq AlgebraicGeometry.Scheme.OrderedAffineCover.restrict_U AlgebraicGeometry.OModulePresheaf.Hom.mk.injEq AlgebraicGeometry.OModulePresheaf.Hom.id_app AlgebraicGeometry.OModulePresheaf.AffHom.appSections_apply AlgebraicGeometry.OModulePresheaf.AffHom.comp_app AlgebraicGeometry.OModulePresheaf.AffSES.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.AffHom.kerMap_coe AlgebraicGeometry.OModulePresheaf.AffHom.id_app AlgebraicGeometry.OModulePresheaf.Hom.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.Hom.toAffHom_app AlgebraicGeometry.OModulePresheaf.SES.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.AffHom.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.Hom.comp_app AlgebraicGeometry.OModulePresheaf.SES.mk.injEq AlgebraicGeometry.OModulePresheaf.AffHom.mk.injEq AlgebraicGeometry.OModulePresheaf.Hom.appSections_apply AlgebraicGeometry.OModulePresheaf.AffSES.mk.injEq DoubleComplex.Bounded.mk.injEq DoubleComplex.Bounded.mk.sizeOf_spec DoubleComplex.Convergence.mk.injEq DoubleComplex.Convergence.mk.sizeOf_spec DoubleComplex.SubQuot.mk.sizeOf_spec DoubleComplex.SubQuot.mk.injEq AlgebraicGeometry.Scheme.OrderedOpenFamily.mk.injEq AlgebraicGeometry.Scheme.OrderedOpenFamily.mk.sizeOf_spec CochainCx.Bounded.mk.sizeOf_spec CochainCx.Bounded.mk.injEq"

set_option autoImplicit false

open scoped TensorProduct Quaternion
p2m_open "CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry QuaternionAlgebra CerednikDrinfeld CerednikDrinfeld.QM NeronModelInfra~schemeHomOverComp GoodReductionJacobian AlgebraicGeometry.Polarisation"

namespace NegInverts

theorem negMor_comp_negMor {S : Type} [CommRing S] {A : Scheme.{0}} (f : A ⟶ Spec (CommRingCat.of S))
    (L : RelativeGroupLaw S f) : negMor f L ≫ negMor f L = 𝟙 A := by
  letI := L.pointGroup f
  have hn : negMor f L ≫ f = f := negMor_over f L
  have key : ∀ x : SchemeHomOver f f,
      schemeHomOverComp (negMor f L) hn (L.inv f x) = L.inv f (schemeHomOverComp (negMor f L) hn x) := by
    intro x
    change schemeHomOverComp (negMor f L) hn x⁻¹ = (schemeHomOverComp (negMor f L) hn x)⁻¹
    apply eq_inv_of_mul_eq_one_left
    change L.mul f (schemeHomOverComp (negMor f L) hn (L.inv f x)) (schemeHomOverComp (negMor f L) hn x) = L.one f
    rw [← L.mul_natural f f (negMor f L) hn, L.inv_mul_cancel, RelativeGroupLaw.one_natural]
  have h1 : schemeHomOverComp (negMor f L) hn (idPt f) = L.inv f (idPt f) := Subtype.ext (Category.comp_id _)
  have h2 := key (idPt f)
  rw [h1] at h2
  have h3 : L.inv f (L.inv f (idPt f)) = idPt f := by
    change ((idPt f)⁻¹)⁻¹ = idPt f
    exact inv_inv _
  exact congrArg Subtype.val (h2.trans h3)

theorem locIso_of_iso {S : Type} [CommRing S] {X : Scheme.{0}} (g : X ⟶ Spec (CommRingCat.of S))
    {M M' : X.Modules} (e : M ≅ M') : LocIsoOnBase g M M' :=
  fun _ => ⟨⊤, trivial, ⟨(Scheme.Modules.pullback _).mapIso e⟩⟩

theorem nonempty_pullback_negMor_tensor_iso {S : Type} [CommRing S] {A : Scheme.{0}} (f : A ⟶ Spec (CommRingCat.of S))
    (L : RelativeGroupLaw S f) (d : A.Modules) :
    Nonempty ((Scheme.Modules.pullback (negMor f L)).obj (d ⊗ (Scheme.Modules.pullback (negMor f L)).obj d) ≅
      d ⊗ (Scheme.Modules.pullback (negMor f L)).obj d) := by
  have e2 : (Scheme.Modules.pullback (negMor f L)).obj ((Scheme.Modules.pullback (negMor f L)).obj d) ≅ d :=
    (Scheme.Modules.pullbackComp (negMor f L) (negMor f L)).app d ≪≫
      (Scheme.Modules.pullbackCongr (negMor_comp_negMor f L)).app d ≪≫ (Scheme.Modules.pullbackId A).app d
  exact ⟨Scheme.Modules.pullbackTensorObjIso _ _ _ ≪≫ (Iso.refl _ ⊗ᵢ e2) ≪≫ β_ _ _⟩

end NegInverts

open NegInverts in
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
    (h2 : IsUnit (2 : R₁))
    (d : (pullback E.f (Spec.map (CommRingCat.ofHom (algebraMap S R₁)))).Modules) (hd : Scheme.Modules.IsInvertible d) (hd₀ : Nonempty ((Scheme.Modules.pullback t).obj d ≅ 𝟙_ _)) :
    Nonempty (d ⊗ (Scheme.Modules.pullback (negMor (pullback.snd E.f (Spec.map (CommRingCat.ofHom (algebraMap S R₁)))) L₁)).obj d ≅ 𝟙_ _) := by
  classical
  have hφc : φ.toRingHom.comp (algebraMap S R₁) = algebraMap S R₀ := RingHom.ext fun x => φ.commutes x

  have hcomm := RelativeGroupLaw.comp_negMor_eq_negMor_comp_of_compatible_univ E.L R₁ R₀ φ.toRingHom hφc L₁ L₀ hL₁ hL₀ t ht₁ ht₂

  have hM : Scheme.Modules.IsInvertible
      (d ⊗ (Scheme.Modules.pullback (negMor (pullback.snd E.f (Spec.map (CommRingCat.ofHom (algebraMap S R₁)))) L₁)).obj d) :=
    Scheme.Modules.IsInvertible.tensor_monoidalV2 hd (Scheme.Modules.IsInvertible.pullback _ hd)

  obtain ⟨e0⟩ := hd₀
  have e1 : (Scheme.Modules.pullback t).obj
      ((Scheme.Modules.pullback (negMor (pullback.snd E.f (Spec.map (CommRingCat.ofHom (algebraMap S R₁)))) L₁)).obj d) ≅ 𝟙_ _ :=
    (Scheme.Modules.pullbackComp t _).app d ≪≫ (Scheme.Modules.pullbackCongr hcomm).app d ≪≫
      ((Scheme.Modules.pullbackComp _ t).app d).symm ≪≫ (Scheme.Modules.pullback _).mapIso e0 ≪≫
      Scheme.Modules.pullbackTensorUnitObjIso _
  have h0 : Nonempty ((Scheme.Modules.pullback t).obj
      (d ⊗ (Scheme.Modules.pullback (negMor (pullback.snd E.f (Spec.map (CommRingCat.ofHom (algebraMap S R₁)))) L₁)).obj d) ≅ 𝟙_ _) :=
    ⟨Scheme.Modules.pullbackTensorObjIso _ _ _ ≪≫ (e0 ⊗ᵢ e1) ≪≫ λ_ _⟩

  obtain ⟨esym⟩ := nonempty_pullback_negMor_tensor_iso _ L₁ d
  have hsym : IsSymmetric (pullback.snd E.f (Spec.map (CommRingCat.ofHom (algebraMap S R₁)))) L₁
      (d ⊗ (Scheme.Modules.pullback (negMor (pullback.snd E.f (Spec.map (CommRingCat.ofHom (algebraMap S R₁)))) L₁)).obj d) :=
    locIso_of_iso _ esym
  exact AbelianSchemePropertyBundle.nonempty_iso_unit_of_pullback_iso_unit_of_isSymmetric_of_ker_mul_maximalIdeal_of_isUnit_two_of_isNoetherianRing
    E.L E.bundle R₁ R₀ φ hφ hsmall h2 t ht₁ ht₂ L₁ hL₁ _ hM h0 hsym

end S_CerednikDrinfeld_QM_FakeEllipticCurve_nonempty_tensor_pullback_negMor_iso_unit_of_pullback_iso_unit_of_isUnit_two
end P2MW
export P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_nonempty_tensor_pullback_negMor_iso_unit_of_pullback_iso_unit_of_isUnit_two (solution)
