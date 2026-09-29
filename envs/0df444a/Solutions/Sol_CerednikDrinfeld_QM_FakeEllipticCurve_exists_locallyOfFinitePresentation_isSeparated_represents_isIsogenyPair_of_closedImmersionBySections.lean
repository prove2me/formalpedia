-- Prove2me | solution 1 for CerednikDrinfeld.QM.FakeEllipticCurve.exists_locallyOfFinitePresentation_isSeparated_represents_isIsogenyPair_of_closedImmersionBySections
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.141142+00:00
-- url     : https://prove2.me/submissions/9be58dcf-da1a-5758-824e-95fc13f785ca

import Definitions.Def_CerednikDrinfeld_QMIsogeny
import Definitions.Def_CerednikDrinfeld_QMRigidification
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_ModulesProjPresentation
import Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_exists_represents_homPair_act_comp_eq_of_closedImmersionBySections
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_exists_locallyOfFinitePresentation_isSeparated_represents_isIsogenyPair_of_closedImmersionBySections
p2m_attr_erase "instance" "PresheafOfModules.instMonoidalClosed PresheafOfModules.InternalHom.instModuleCarrierObjOppositeCommRingCatSubtypePiFamilyMemAddSubgroupNaturalFamilies PresheafOfModules.InternalHom.instModuleCarrierObjOppositeRingCatCompCommRingCatForget₂RingHomCarrierCarrierAbPresheaf PresheafOfModules.InternalHom.instSMulCarrierObjOppositeCommRingCatSubtypePiFamilyMemAddSubgroupNaturalFamilies AlgebraicGeometry.Scheme.PresheafOfModules.symmetricCategory SheafOfModules.instFaithfulRingSheafPModToPMod SheafOfModules.symmetricCategory AlgebraicGeometry.Scheme.PresheafOfModules.monoidalCategory AlgebraicGeometry.Scheme.PresheafOfModules.monoidalClosed SheafOfModules.instFullRingSheafPModToPMod SheafOfModules.monoidalCategory AlgebraicGeometry.Scheme.Modules.symmetricCategory SheafOfModules.monoidalClosed SheafOfModules.instIsLocalizationPModRingSheafSheafifyFunctorPresheafW SheafOfModules.sheafifyFunctor_monoidal AlgebraicGeometry.Scheme.Modules.monoidalClosed AlgebraicGeometry.instMonoidalPresheafOfModulesModulesSheafify AlgebraicGeometry.Scheme.Modules.monoidalCategory PresheafOfModules.PullbackMonoidal.pullback_monoidal PresheafOfModules.PullbackMonoidal.isIso_δ PresheafOfModules.pushforward_laxMonoidal PresheafOfModules.PullbackMonoidal.isIso_η PresheafOfModules.free_monoidal PresheafOfModules.restrictScalars_laxMonoidal PresheafOfModules.PullbackMonoidal.isIso_δ_gS PresheafOfModules.pullback_oplaxMonoidal PresheafOfModules.PullbackMonoidal.instPreservesColimitsOfSizeCompOppositeCommRingCatRingCatForget₂RingHomCarrierCarrierPb PresheafOfModules.pullback_monoidal' AlgebraicGeometry.Scheme.Modules.preservesBinaryProducts_opensMap AlgebraicGeometry.Scheme.Modules.pullback_monoidal AlgebraicGeometry.Scheme.Modules.sheafify_isLocalization' AlgebraicGeometry.Scheme.Modules.preservesTerminal_opensMap AlgebraicGeometry.Scheme.Modules.pullback₀_monoidal AlgebraicGeometry.Scheme.Modules.preservesFiniteProducts_opensMap AlgebraicGeometry.Scheme.Modules.instLiftingPresheafOfModulesSheafifyPresheafWOpensCarrierCarrierCommRingCatGrothendieckTopologyObjFunctorOppositeIsSheafSheafCompPullback₀Pullback AlgebraicGeometry.OModulePresheaf.isScalarTower AlgebraicGeometry.Scheme.OrderedAffineCover.instLinearOrder AlgebraicGeometry.OModulePresheaf.module AlgebraicGeometry.Scheme.OrderedAffineCover.instFintype AlgebraicGeometry.Scheme.OrderedAffineCover.instFintypeIdx"
p2m_attr_erase "instance" "AlgebraicGeometry.OModulePresheaf.addCommGroup AlgebraicGeometry.Scheme.OrderedAffineCover.instDecidableEqIdx AlgebraicGeometry.OModulePresheaf.moduleSections TwoChartCech.Sections.M0_moduleA TwoChartCech.Sections.M1_module TwoChartCech.Cover.A01_algebra TwoChartCech.Cover.A0_algebra TwoChartCech.Cover.A1_commRing TwoChartCech.Cover.A1_algebra TwoChartCech.Sections.M01_module TwoChartCech.Sections.M0_addCommGroup TwoChartCech.Sections.M0_tower TwoChartCech.Sections.M01_addCommGroup TwoChartCech.Cover.A0_commRing TwoChartCech.Sections.M1_tower TwoChartCech.Sections.M01_moduleA TwoChartCech.Sections.M0_module TwoChartCech.Sections.M1_moduleA TwoChartCech.Sections.M1_addCommGroup TwoChartCech.Cover.A01_commRing TwoChartCech.Sections.M01_tower CoherentBaseChange.TwoTermComplex.C0_module CoherentBaseChange.TwoTermComplex.C0_addCommGroup CoherentBaseChange.TwoTermComplex.C1_module CoherentBaseChange.TwoTermComplex.C1_addCommGroup CoherentBaseChange.TwoTermComplex.C0_free CoherentBaseChange.TwoTermComplex.C1_finite CoherentBaseChange.TwoTermComplex.C0_finite CoherentBaseChange.TwoTermComplex.C1_free AlgebraicGeometry.ProjSpace.twistObj.addCommGroup AlgebraicGeometry.ProjSpace.twistFam.module AlgebraicGeometry.ProjSpace.twistObj.module AlgebraicGeometry.ProjSpace.twistObj.moduleSections AlgebraicGeometry.ProjSpace.twistFam.addCommGroup ProjSpaceCech.GradedModule.H.module ProjSpaceCech.GradedModule.H.addCommGroup ProjSpaceCech.GradedModule.sec.instAdd ProjSpaceCech.GradedModule.sec.instNeg ProjSpaceCech.GradedModule.acg ProjSpaceCech.GradedModule.Frac.setoid"
p2m_attr_erase "instance" "ProjSpaceCech.GradedModule.modR ProjSpaceCech.GradedModule.sec.instModule ProjSpaceCech.GradedModule.sec.instAddCommGroup ProjSpaceCech.GradedModule.sec.instZero ProjSpaceCech.GradedModule.Presentation.fJ ProjSpaceCech.GradedModule.sec.instSMul ProjSpaceCech.Twist.H.module ProjSpaceCech.Idx.instFintype ProjSpaceCech.Twist.H.addCommGroup ProjSpaceCech.Idx.instDecidableEq ProjSpaceCech.Twist.Mon.instDecidableEq ProjSpaceCech.Twist.cochain.instAddCommGroup ProjSpaceCech.Twist.cochain.instModule AlgebraicGeometry.OModulePresheaf.instSubsingletonObjZero AlgebraicGeometry.OModulePresheaf.Leray.relAltC_scalarTower AlgebraicGeometry.OModulePresheaf.Leray.ker_relAltd_modΓ AlgebraicGeometry.OModulePresheaf.Leray.relAltC_modΓ AlgebraicGeometry.OModulePresheaf.Leray.biC_abGrp AlgebraicGeometry.OModulePresheaf.Leray.relAltH_modΓ AlgebraicGeometry.OModulePresheaf.Leray.ker_relAltd_smul AlgebraicGeometry.OModulePresheaf.Leray.relAltH_scalarTower AlgebraicGeometry.OModulePresheaf.Leray.relAltH_smul AlgebraicGeometry.OModulePresheaf.Leray.biC_module AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instDecidableEqIdx AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instFintype AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instLinearOrder AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instFintypeIdx DoubleComplex.instModuleE₂I DoubleComplex.Bounded.modR DoubleComplex.instModuleE₂II DoubleComplex.instAddCommGroupE₂II DoubleComplex.Bounded.abGrp DoubleComplex.instAddCommGroupE₂I AlgebraicGeometry.Scheme.Modules.GlueOfCocycle.instSMulCarrierObjOppositeOpensCarrierCarrierCommRingCatPresheafOpOpensSubtypeForallMinMemAddSubgroupFamilies AlgebraicGeometry.Scheme.Modules.GlueOfCocycle.instModulePreGlue AlgebraicGeometry.Scheme.Modules.GlueOfCocycle.instModuleCarrierObjOppositeOpensCarrierCarrierCommRingCatPresheafOpOpensSubtypeForallMinMemAddSubgroupFamilies IsDirectLimit.Module.instDirectLimitCoeLinearMapIdOfOfNonempty AlgebraicGeometry.SubalgebraStages.compactSpace_pullback AlgebraicGeometry.SubalgebraStages.quasiSeparatedSpace_pullback AlgebraicGeometry.SubalgebraStages.compactSpace_obj"
p2m_attr_erase "instance" "AlgebraicGeometry.SubalgebraStages.quasiSeparatedSpace_obj AlgebraicGeometry.SubalgebraStages.quasiCompact_snd AlgebraicGeometry.SubalgebraStages.isAffineHom_leg AlgebraicGeometry.SubalgebraStages.isAffineHom_trans AlgebraicGeometry.SubalgebraStages.isAffineHom_diagram_map AlgebraicGeometry.SubalgebraStages.quasiSeparated_snd AlgebraicGeometry.SubalgebraStages.isCofiltered_op instTopologicallyFGOfFiniteType AlgebraicCurve.CurveModel.isProper AlgebraicCurve.CurveModel.isIntegral AlgebraicCurve.CurveModel.smooth AlgebraicCurve.CurveModel.locallyOfFiniteType_gluedToBase AlgebraicCurve.CurveModel.isFractionRing_overlap AlgebraicCurve.CurveModel.isLocallyNoetherian_glued AlgebraicCurve.CurveModel.jacobsonSpace_glued AlgebraicCurve.CurveModel.isOpenImmersion_ι₀ AlgebraicCurve.CurveModel.isIntegral_glued AlgebraicCurve.CurveModel.quasiSeparated_gluedToBase AlgebraicCurve.CurveModel.compactSpace_glued AlgebraicCurve.CurveModel.isIntegral_adjoin_chartRing AlgebraicCurve.CurveModel.isFractionRing_overlap_functionField AlgebraicCurve.CurveModel.isProper_gluedToBase AlgebraicCurve.CurveModel.isOpenImmersion_ιU AlgebraicCurve.CurveModel.isOpenImmersion_f₀ AlgebraicCurve.CurveModel.isOpenImmersion_fInf AlgebraicCurve.CurveModel.isOpenImmersion_ιInf AlgebraicCurve.CurveModel.algebra_overlap_functionField AlgebraicCurve.CurveModel.quasiCompact_gluedToBase AlgebraicCurve.CurveModel.algebraAdjoin AlgebraicCurve.CurveModel.isDedekindDomain_chartRing AlgebraicCurve.CurveModel.isIntegralClosure AlgebraicCurve.CurveModel.finite_chartRing AlgebraicCurve.CurveModel.centre_isPrime AlgebraicCurve.CurveModel.isFractionRing_chartRing AlgebraicCurve.CurveModel.finiteType_chartRing AlgebraicCurve.CurveModel.isNoetherianRing_chartRing AlgebraicCurve.CurveModel.isScalarTower_base_adjoin AlgebraicCurve.CurveModel.isScalarTower_adjoin AlgebraicCurve.CurveModel.chartRing_finitePresentation AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation"
p2m_attr_erase "instance" "AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation AdicCompletion.instIsLocalRingMaximalIdeal"
p2m_attr_erase "simp" "AlgebraicGeometry.PolarisedAbelianScheme.mk.injEq AlgebraicGeometry.PolarisedAbelianScheme.mk.sizeOf_spec GoodReductionJacobian.RelativeGroupLaw.nsmul_zero GoodReductionJacobian.RelativeGroupLaw.mem_torsionSubset GoodReductionJacobian.RelativeGroupLaw.nsmul_succ PresheafOfModules.InternalHom.presheaf_map_apply PresheafOfModules.InternalHom.curryFamily_app PresheafOfModules.InternalHom.add_app PresheafOfModules.InternalHom.smul_app PresheafOfModules.InternalHom.zero_app PresheafOfModules.ihomObj_map_val PresheafOfModules.ihomFunctor_map PresheafOfModules.InternalHom.restrict_app PresheafOfModules.InternalHom.postcomp_app PresheafOfModules.InternalHom.neg_app PresheafOfModules.curry'_app_val PresheafOfModules.InternalHom.presheaf_obj PresheafOfModules.ihomFunctor_obj PresheafOfModules.ihomObj_obj PresheafOfModules.InternalHom.sub_app PresheafOfModules.ihomMap_app_val SheafOfModules.tensorUnit_eq AlgebraicGeometry.Scheme.Modules.tensorUnit_eq PresheafOfModules.freeεIso_hom_app PresheafOfModules.freeμIso_hom_app AlgebraicGeometry.HilbertFunctor.Point.mk.injEq AlgebraicGeometry.HilbertFunctor.Point.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCover.mk.injEq AlgebraicGeometry.OModulePresheaf.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCover.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.mk.injEq AlgebraicGeometry.Scheme.TwoAffineOpenCover.mk.injEq AlgebraicGeometry.Scheme.TwoAffineOpenCover.mk.sizeOf_spec AlgebraicGeometry.Scheme.TwoAffineOpenCover.pullback_U1 AlgebraicGeometry.Scheme.TwoAffineOpenCover.pullback_U0 TwoChartCech.Sections.mk.injEq TwoChartCech.Cover.mk.injEq TwoChartCech.GrothendieckComplex.mk.injEq TwoChartCech.Sections.mk.sizeOf_spec TwoChartCech.Cover.mk.sizeOf_spec"
p2m_attr_erase "simp" "TwoChartCech.Cover.lineBundle_r0_apply TwoChartCech.GrothendieckComplex.mk.sizeOf_spec TwoChartCech.Cover.lineBundle_r1_apply CoherentBaseChange.TwoTermComplex.mk.sizeOf_spec CoherentBaseChange.TwoTermComplex.mk.injEq AlgebraicGeometry.ProjSpace.twistObj.mk.injEq AlgebraicGeometry.ProjSpace.twistObj.zero_val AlgebraicGeometry.ProjSpace.twistObj.add_val AlgebraicGeometry.ProjSpace.twist_res_val AlgebraicGeometry.ProjSpace.twist_smul_val AlgebraicGeometry.ProjSpace.twistGradeToObj_val AlgebraicGeometry.ProjSpace.twistObj.smul_val AlgebraicGeometry.ProjSpace.twistGradeEquiv_apply_val AlgebraicGeometry.ProjSpace.twistObj.mk.sizeOf_spec ProjSpaceCech.GradedModule.mk.injEq ProjSpaceCech.GradedModule.mk.sizeOf_spec ProjSpaceCech.GradedModule.Frac.mk.sizeOf_spec ProjSpaceCech.GradedModule.Presentation.mk.injEq ProjSpaceCech.GradedModule.Frac.mk.injEq ProjSpaceCech.GradedModule.Presentation.mk.sizeOf_spec ProjSpaceCech.GradedModule.Hom.shift_toLinearMap ProjSpaceCech.GradedModule.Hom.mk.sizeOf_spec ProjSpaceCech.GradedModule.Hom.mk.injEq AlgebraicGeometry.OModulePresheaf.Hom.mk.injEq AlgebraicGeometry.OModulePresheaf.Hom.id_app AlgebraicGeometry.OModulePresheaf.AffHom.appSections_apply AlgebraicGeometry.OModulePresheaf.AffHom.comp_app AlgebraicGeometry.OModulePresheaf.AffSES.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.AffHom.kerMap_coe AlgebraicGeometry.OModulePresheaf.AffHom.id_app AlgebraicGeometry.OModulePresheaf.Hom.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.Hom.toAffHom_app AlgebraicGeometry.OModulePresheaf.SES.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.AffHom.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.Hom.comp_app AlgebraicGeometry.OModulePresheaf.SES.mk.injEq AlgebraicGeometry.OModulePresheaf.AffHom.mk.injEq AlgebraicGeometry.OModulePresheaf.Hom.appSections_apply AlgebraicGeometry.OModulePresheaf.AffSES.mk.injEq AlgebraicGeometry.OModulePresheaf.prod_obj"
p2m_attr_erase "simp" "AlgebraicGeometry.OModulePresheaf.restrOpen_obj AlgebraicGeometry.OModulePresheaf.DevissageStep.mk.injEq AlgebraicGeometry.OModulePresheaf.pushforward_obj AlgebraicGeometry.OModulePresheaf.im_obj AlgebraicGeometry.OModulePresheaf.pow_obj AlgebraicGeometry.OModulePresheaf.fstHom_app AlgebraicGeometry.OModulePresheaf.ker_obj AlgebraicGeometry.OModulePresheaf.coker_obj AlgebraicGeometry.OModulePresheaf.DevissageStep.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCover.preimage_U AlgebraicGeometry.OModulePresheaf.sndHom_app AlgebraicGeometry.Scheme.Modules.tensorPow_zero AlgebraicGeometry.Scheme.Modules.tensorPow_succ AlgebraicGeometry.Scheme.Modules.tensorSections_zero_right AlgebraicGeometry.Scheme.Modules.map_unitSection AlgebraicGeometry.Scheme.Modules.tensorSectionsBilin_apply AlgebraicGeometry.Scheme.Modules.tensorPowSection_zero AlgebraicGeometry.Scheme.Modules.tensorSections_zero_left AlgebraicGeometry.OModulePresheaf.Leray.restrictToPreimage_U AlgebraicGeometry.Scheme.OrderedAffineCover.toCoverOf_U AlgebraicGeometry.Scheme.OrderedAffineCoverOf.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCoverOf.mk.injEq AlgebraicGeometry.Scheme.OrderedAffineCover.restrict_U DoubleComplex.Bounded.mk.injEq DoubleComplex.Bounded.mk.sizeOf_spec DoubleComplex.Convergence.mk.injEq DoubleComplex.Convergence.mk.sizeOf_spec DoubleComplex.SubQuot.mk.sizeOf_spec DoubleComplex.SubQuot.mk.injEq AlgebraicGeometry.Scheme.Modules.glueComponent_glueMk AlgebraicGeometry.Scheme.Modules.UnitCocycle.mk.injEq AlgebraicGeometry.Scheme.Modules.UnitCocycle.mk.sizeOf_spec IsDirectLimit.Module.linearEquiv_symm_apply IsDirectLimit.linearEquiv_symm_apply IsDirectLimit.lift_of IsDirectLimit.Module.linearEquiv_apply IsDirectLimit.Module.lift_of IsDirectLimit.Equiv_apply AlgebraicGeometry.SubalgebraStages.specCone_π_app AlgebraicGeometry.SubalgebraStages.specLeg_specHom"
p2m_attr_erase "simp" "AlgebraicGeometry.SubalgebraStages.specLeg_specTrans AlgebraicGeometry.SubalgebraStages.cone_pt AlgebraicGeometry.SubalgebraStages.trans_fst AlgebraicGeometry.SubalgebraStages.diagram_obj AlgebraicGeometry.SubalgebraStages.leg_snd AlgebraicGeometry.SubalgebraStages.diagram_map AlgebraicGeometry.SubalgebraStages.specTrans_refl AlgebraicGeometry.SubalgebraStages.trans_snd AlgebraicGeometry.SubalgebraStages.specTrans_specHom AlgebraicGeometry.SubalgebraStages.specCone_pt AlgebraicGeometry.SubalgebraStages.cone_π_app AlgebraicGeometry.SubalgebraStages.specDiagram_map AlgebraicGeometry.SubalgebraStages.specDiagram_obj AlgebraicGeometry.SubalgebraStages.leg_fst AlgebraicGeometry.SubalgebraStages.leg_trans CategoryTheory.Functor.OverTotal.ofFibre_fst CategoryTheory.Functor.overTotal_map_fst GoodReductionJacobian.RelativeGroupLaw.baseChangePointToBase_ofBase GoodReductionJacobian.RelativeGroupLaw.baseChangePointToBase_coe GoodReductionJacobian.RelativeGroupLaw.baseChangePointOfBase_coe GoodReductionJacobian.RelativeGroupLaw.baseChange_inv GoodReductionJacobian.RelativeGroupLaw.baseChangePointOfBase_toBase GoodReductionJacobian.RelativeGroupLaw.baseChange_mul GoodReductionJacobian.RelativeGroupLaw.baseChange_one NeronModelInfra.NeronModelPropertyBundle.endExtensionEquiv_symm_restrict NeronModelInfra.schemeHomOverComp_id_left NeronModelInfra.schemeHomOverComp_id_right NeronModelInfra.schemeHomOverId_coe NeronModelInfra.NeronModelPropertyBundle.endExtensionEquiv_apply NeronModelInfra.NeronModelPropertyBundle.restrict_endExtensionEquiv_symm NeronModelInfra.schemeHomOverComp_coe NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_fst NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_snd NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_fst NeronSpecialFibreInfra.neronEndRestrictEquiv_apply NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_fst_assoc NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_snd NeronSpecialFibreInfra.neronEndExtension_genericFibreRestrict NeronSpecialFibreInfra.specClosedFibreInclusion_eq NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_fst_assoc"
p2m_attr_erase "simp" "NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_snd_assoc NeronSpecialFibreInfra.genericFibreRestrict_neronEndExtension NeronSpecialFibreInfra.homOverId_coe NeronSpecialFibreInfra.homOverComp_coe NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_snd_assoc GoodReductionJacobian.RelativeGroupLaw.fibre_inv GoodReductionJacobian.RelativeGroupLaw.fibrePointToBase_coe GoodReductionJacobian.RelativeGroupLaw.fibrePointOfBase_toBase GoodReductionJacobian.RelativeGroupLaw.fibre_mul GoodReductionJacobian.RelativeGroupLaw.fibrePointToBase_ofBase GoodReductionJacobian.RelativeGroupLaw.fibre_one GoodReductionJacobian.RelativeGroupLaw.fibrePointOfBase_coe AlgebraicGeometry.schemeFibreEndo_snd AlgebraicGeometry.schemeFibreEndo_fst RegularLocalRingQuotientAscent.dualNumberFst_apply AlgebraicCurve.CurveModel.mk.injEq AlgebraicCurve.CurveModel.mk.sizeOf_spec AlgebraicCurve.CurveModel.coe_gInf AlgebraicCurve.CurveModel.coe_tInvChart AlgebraicCurve.CurveModel.ιInf_gluedToBase_assoc AlgebraicCurve.CurveModel.ιInf_gluedToBase AlgebraicCurve.CurveModel.primeOfι₀_asIdeal AlgebraicCurve.CurveModel.coe_tChart AlgebraicCurve.CurveModel.ι₀_gluedToBase_assoc AlgebraicCurve.CurveModel.primeOfιInf_asIdeal AlgebraicCurve.CurveModel.ι₀_gluedToBase AlgebraicCurve.CurveModel.coe_tma AlgebraicCurve.CurveModel.coe_primeEquivChartPlaces AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint"

set_option autoImplicit false

open scoped TensorProduct Quaternion NumberField
open CategoryTheory AlgebraicGeometry QuaternionAlgebra CerednikDrinfeld CerednikDrinfeld.QM NeronModelInfra GoodReductionJacobian
open CategoryTheory.Limits

namespace BridgeSol

theorem forall_act_comp_eq_of_forall_basis
    {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} {N : ℕ} {S : Type} [CommRing S]
    {ι : Type} [Fintype ι] (β : ι → ↥Λ) (hβ : ∀ x : ↥Λ, ∃ c : ι → ℤ, x = ∑ j, c j • β j)
    (E A : FakeEllipticCurve Λ N S) (φ : E.A ⟶ A.A) (hφ : φ ≫ A.f = E.f)
    (hmul : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of S)) (P Q : SchemeHomOver t E.f),
      mapPt φ hφ (E.L.mul t P Q) = A.L.mul t (mapPt φ hφ P) (mapPt φ hφ Q))
    (hβlin : ∀ j : ι, E.act (β j) ≫ φ = φ ≫ A.act (β j)) :
    ∀ x : ↥Λ, E.act x ≫ φ = φ ≫ A.act x := by
  classical

  letI GE : Group (SchemeHomOver E.f E.f) := E.L.pointGroup E.f
  letI GA : Group (SchemeHomOver E.f A.f) := A.L.pointGroup E.f
  let P1 : SchemeHomOver E.f E.f := ⟨𝟙 E.A, Category.id_comp _⟩
  let aE : ↥Λ → SchemeHomOver E.f E.f := fun x => pushPt (E.act x) (E.act_over x) P1
  let Pφ : SchemeHomOver E.f A.f := mapPt φ hφ P1
  let aA : ↥Λ → SchemeHomOver E.f A.f := fun x => pushPt (A.act x) (A.act_over x) Pφ

  let F : SchemeHomOver E.f E.f →* SchemeHomOver E.f A.f := MonoidHom.mk' (fun P => mapPt φ hφ P) (fun P Q => hmul E.f P Q)
  have hF : ∀ P : SchemeHomOver E.f E.f, F P = mapPt φ hφ P := fun _ => rfl

  have haE_add : ∀ x y : ↥Λ, aE (x + y) = aE x * aE y := fun x y => E.act_add x y E.f P1
  have haA_add : ∀ x y : ↥Λ, aA (x + y) = aA x * aA y := fun x y => A.act_add x y E.f Pφ
  have haE_zero : aE 0 = 1 := by
    have h := haE_add 0 0; rw [add_zero] at h
    have h3 : aE 0 * aE 0 = aE 0 * 1 := by rw [mul_one]; exact h.symm
    exact mul_left_cancel h3
  have haA_zero : aA 0 = 1 := by
    have h := haA_add 0 0; rw [add_zero] at h
    have h3 : aA 0 * aA 0 = aA 0 * 1 := by rw [mul_one]; exact h.symm
    exact mul_left_cancel h3
  have haE_neg : ∀ x : ↥Λ, aE (-x) = (aE x)⁻¹ := by
    intro x
    have h := haE_add x (-x); rw [add_neg_cancel, haE_zero] at h
    exact (eq_inv_of_mul_eq_one_right h.symm)
  have haA_neg : ∀ x : ↥Λ, aA (-x) = (aA x)⁻¹ := by
    intro x
    have h := haA_add x (-x); rw [add_neg_cancel, haA_zero] at h
    exact (eq_inv_of_mul_eq_one_right h.symm)

  have key : ∀ x : ↥Λ, (E.act x ≫ φ = φ ≫ A.act x) ↔ F (aE x) = aA x := by
    intro x
    rw [hF]
    constructor
    · intro h
      apply Subtype.ext
      show (𝟙 E.A ≫ E.act x) ≫ φ = (𝟙 E.A ≫ φ) ≫ A.act x
      rw [Category.id_comp, Category.id_comp, h]
    · intro h
      have h' := congrArg Subtype.val h
      change (𝟙 E.A ≫ E.act x) ≫ φ = (𝟙 E.A ≫ φ) ≫ A.act x at h'
      rwa [Category.id_comp, Category.id_comp] at h'

  have lin_zero : F (aE 0) = aA 0 := by rw [haE_zero, haA_zero, map_one]
  have lin_add : ∀ x y : ↥Λ, F (aE x) = aA x → F (aE y) = aA y → F (aE (x + y)) = aA (x + y) := by
    intro x y hx hy; rw [haE_add, haA_add, map_mul, hx, hy]
  have lin_neg : ∀ x : ↥Λ, F (aE x) = aA x → F (aE (-x)) = aA (-x) := by
    intro x hx; rw [haE_neg, haA_neg, map_inv, hx]
  have lin_zsmul : ∀ (n : ℤ) (x : ↥Λ), F (aE x) = aA x → F (aE (n • x)) = aA (n • x) := by
    intro n x hx
    induction n using Int.induction_on with
    | zero => rw [zero_smul]; exact lin_zero
    | succ n ih => rw [add_smul, one_smul]; exact lin_add _ _ ih hx
    | pred n ih => rw [sub_smul, one_smul, sub_eq_add_neg]; exact lin_add _ _ ih (lin_neg _ hx)
  have lin_sum : ∀ (c : ι → ℤ) (s : Finset ι), F (aE (∑ j ∈ s, c j • β j)) = aA (∑ j ∈ s, c j • β j) := by
    intro c s
    induction s using Finset.induction_on with
    | empty => rw [Finset.sum_empty]; exact lin_zero
    | insert j s hj ih => rw [Finset.sum_insert hj]; exact lin_add _ _ (lin_zsmul _ _ ((key _).mp (hβlin j))) ih
  intro x
  obtain ⟨c, rfl⟩ := hβ x
  exact (key _).mpr (lin_sum c Finset.univ)

theorem mul_val_congr {R : Type} [CommRing R] {A : Scheme.{0}} {f : A ⟶ Spec (CommRingCat.of R)}
    (L : RelativeGroupLaw R f) {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of R))
    {X X' Y Y' : SchemeHomOver t f} (hX : X.1 = X'.1) (hY : Y.1 = Y'.1) :
    (L.mul t X Y).1 = (L.mul t X' Y').1 := by
  have h1 : X = X' := Subtype.ext hX
  have h2 : Y = Y' := Subtype.ext hY
  rw [h1, h2]

theorem isHom_transport
    {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} {N : ℕ} {S : Type} [CommRing S]
    (E A : FakeEllipticCurve Λ N S) {T : Type} [CommRing T] [Algebra S T]
    (E' A' : FakeEllipticCurve Λ N T)
    (gE : E'.A ⟶ E.A) (hgE : FakeEllipticCurve.IsPullbackVia (algebraMap S T) E E' gE)
    (gA : A'.A ⟶ A.A) (hgA : FakeEllipticCurve.IsPullbackVia (algebraMap S T) A A' gA)
    (eE : E'.A ≅ pullback E.f (Spec.map (CommRingCat.ofHom (algebraMap S T))))
    (heE₁ : eE.hom ≫ pullback.fst E.f (Spec.map (CommRingCat.ofHom (algebraMap S T))) = gE)
    (heE₂ : eE.hom ≫ pullback.snd E.f (Spec.map (CommRingCat.ofHom (algebraMap S T))) = E'.f)
    (φ : E'.A ⟶ A'.A) (hφ : φ ≫ A'.f = E'.f)
    (hφmul : ∀ {T₀ : Scheme.{0}} (t : T₀ ⟶ Spec (CommRingCat.of T)) (P Q : SchemeHomOver t E'.f),
      mapPt φ hφ (E'.L.mul t P Q) = A'.L.mul t (mapPt φ hφ P) (mapPt φ hφ Q))
    (hφh : (eE.inv ≫ φ ≫ gA) ≫ A.f =
      pullback.snd E.f (Spec.map (CommRingCat.ofHom (algebraMap S T))) ≫ Spec.map (CommRingCat.ofHom (algebraMap S T))) :
    ∀ (T₀ : Scheme.{0}) (t' : T₀ ⟶ Spec (CommRingCat.of T))
      (P Q : SchemeHomOver (t' ≫ Spec.map (CommRingCat.ofHom (algebraMap S T))) E.f),
      pullback.lift (E.L.mul (t' ≫ Spec.map (CommRingCat.ofHom (algebraMap S T))) P Q).1 t'
          (E.L.mul (t' ≫ Spec.map (CommRingCat.ofHom (algebraMap S T))) P Q).2 ≫ (eE.inv ≫ φ ≫ gA) =
        (A.L.mul (t' ≫ Spec.map (CommRingCat.ofHom (algebraMap S T)))
          ⟨pullback.lift P.1 t' P.2 ≫ (eE.inv ≫ φ ≫ gA), by rw [Category.assoc, hφh, ← Category.assoc, pullback.lift_snd]⟩
          ⟨pullback.lift Q.1 t' Q.2 ≫ (eE.inv ≫ φ ≫ gA), by rw [Category.assoc, hφh, ← Category.assoc, pullback.lift_snd]⟩).1 := by
  intro T₀ t' P Q
  obtain ⟨hgEsq, hgEmul, -, -⟩ := hgE
  obtain ⟨hgAsq, hgAmul, -, -⟩ := hgA

  have hinv_fst : eE.inv ≫ gE = pullback.fst E.f (Spec.map (CommRingCat.ofHom (algebraMap S T))) := by
    rw [← heE₁, ← Category.assoc, eE.inv_hom_id, Category.id_comp]
  have hinv_snd : eE.inv ≫ E'.f = pullback.snd E.f (Spec.map (CommRingCat.ofHom (algebraMap S T))) := by
    rw [← heE₂, ← Category.assoc, eE.inv_hom_id, Category.id_comp]

  let Pt : SchemeHomOver t' E'.f := ⟨pullback.lift P.1 t' P.2 ≫ eE.inv, by rw [Category.assoc, hinv_snd, pullback.lift_snd]⟩
  let Qt : SchemeHomOver t' E'.f := ⟨pullback.lift Q.1 t' Q.2 ≫ eE.inv, by rw [Category.assoc, hinv_snd, pullback.lift_snd]⟩
  have hPt : Pt.1 ≫ gE = P.1 := by
    show (pullback.lift P.1 t' P.2 ≫ eE.inv) ≫ gE = P.1
    rw [Category.assoc, hinv_fst, pullback.lift_fst]
  have hQt : Qt.1 ≫ gE = Q.1 := by
    show (pullback.lift Q.1 t' Q.2 ≫ eE.inv) ≫ gE = Q.1
    rw [Category.assoc, hinv_fst, pullback.lift_fst]

  have hA : pullback.lift (E.L.mul (t' ≫ (Spec.map (CommRingCat.ofHom (algebraMap S T)))) P Q).1 t' (E.L.mul (t' ≫ (Spec.map (CommRingCat.ofHom (algebraMap S T)))) P Q).2 ≫ eE.inv = (E'.L.mul t' Pt Qt).1 := by
    rw [← cancel_mono eE.hom, Category.assoc, eE.inv_hom_id, Category.comp_id]
    apply pullback.hom_ext
    · rw [pullback.lift_fst, Category.assoc, heE₁, hgEmul t' Pt Qt]
      exact mul_val_congr E.L (t' ≫ (Spec.map (CommRingCat.ofHom (algebraMap S T)))) hPt.symm hQt.symm
    · rw [pullback.lift_snd, Category.assoc, heE₂]; exact (E'.L.mul t' Pt Qt).2.symm

  calc pullback.lift (E.L.mul (t' ≫ (Spec.map (CommRingCat.ofHom (algebraMap S T)))) P Q).1 t' (E.L.mul (t' ≫ (Spec.map (CommRingCat.ofHom (algebraMap S T)))) P Q).2 ≫ (eE.inv ≫ φ ≫ gA)
      = (pullback.lift (E.L.mul (t' ≫ (Spec.map (CommRingCat.ofHom (algebraMap S T)))) P Q).1 t' (E.L.mul (t' ≫ (Spec.map (CommRingCat.ofHom (algebraMap S T)))) P Q).2 ≫ eE.inv) ≫ φ ≫ gA := by
          simp only [Category.assoc]
    _ = ((E'.L.mul t' Pt Qt).1 ≫ φ) ≫ gA := by rw [hA, Category.assoc]
    _ = (mapPt φ hφ (E'.L.mul t' Pt Qt)).1 ≫ gA := rfl
    _ = (A'.L.mul t' (mapPt φ hφ Pt) (mapPt φ hφ Qt)).1 ≫ gA := by rw [hφmul t' Pt Qt]
    _ = (A.L.mul (t' ≫ (Spec.map (CommRingCat.ofHom (algebraMap S T)))) ⟨(mapPt φ hφ Pt).1 ≫ gA, by rw [Category.assoc, hgAsq.w, ← Category.assoc, (mapPt φ hφ Pt).2]⟩
          ⟨(mapPt φ hφ Qt).1 ≫ gA, by rw [Category.assoc, hgAsq.w, ← Category.assoc, (mapPt φ hφ Qt).2]⟩).1 :=
          hgAmul t' (mapPt φ hφ Pt) (mapPt φ hφ Qt)
    _ = _ := by
          apply mul_val_congr A.L (t' ≫ (Spec.map (CommRingCat.ofHom (algebraMap S T))))
          · show ((pullback.lift P.1 t' P.2 ≫ eE.inv) ≫ φ) ≫ gA = pullback.lift P.1 t' P.2 ≫ (eE.inv ≫ φ ≫ gA)
            simp only [Category.assoc]
          · show ((pullback.lift Q.1 t' Q.2 ≫ eE.inv) ≫ φ) ≫ gA = pullback.lift Q.1 t' Q.2 ≫ (eE.inv ≫ φ ≫ gA)
            simp only [Category.assoc]

theorem mul_comp_presIso
    {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} {N : ℕ} {S : Type} [CommRing S]
    (E : FakeEllipticCurve Λ N S) {T : Type} [CommRing T] [Algebra S T] (E' : FakeEllipticCurve Λ N T)
    (gE : E'.A ⟶ E.A) (hgE : FakeEllipticCurve.IsPullbackVia (algebraMap S T) E E' gE)
    (eE : E'.A ≅ pullback E.f (Spec.map (CommRingCat.ofHom (algebraMap S T))))
    (heE₁ : eE.hom ≫ pullback.fst E.f (Spec.map (CommRingCat.ofHom (algebraMap S T))) = gE)
    (heE₂ : eE.hom ≫ pullback.snd E.f (Spec.map (CommRingCat.ofHom (algebraMap S T))) = E'.f)
    {T₀ : Scheme.{0}} (t : T₀ ⟶ Spec (CommRingCat.of T)) (P Q : SchemeHomOver t E'.f) :
    (E'.L.mul t P Q).1 ≫ eE.hom =
      pullback.lift (E.L.mul (t ≫ Spec.map (CommRingCat.ofHom (algebraMap S T)))
          ⟨P.1 ≫ gE, by rw [Category.assoc, (hgE.elim fun h _ => h).w, ← Category.assoc, P.2]⟩
          ⟨Q.1 ≫ gE, by rw [Category.assoc, (hgE.elim fun h _ => h).w, ← Category.assoc, Q.2]⟩).1 t
        (E.L.mul (t ≫ Spec.map (CommRingCat.ofHom (algebraMap S T))) _ _).2 := by
  obtain ⟨hsq, hmul, -, -⟩ := hgE
  apply pullback.hom_ext
  · rw [pullback.lift_fst, Category.assoc, heE₁, hmul t P Q]
  · rw [pullback.lift_snd, Category.assoc, heE₂]; exact (E'.L.mul t P Q).2

theorem act_comp_presIso
    {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} {N : ℕ} {S : Type} [CommRing S]
    (E : FakeEllipticCurve Λ N S) {T : Type} [CommRing T] [Algebra S T] (E' : FakeEllipticCurve Λ N T)
    (gE : E'.A ⟶ E.A) (hgE : FakeEllipticCurve.IsPullbackVia (algebraMap S T) E E' gE)
    (eE : E'.A ≅ pullback E.f (Spec.map (CommRingCat.ofHom (algebraMap S T))))
    (heE₁ : eE.hom ≫ pullback.fst E.f (Spec.map (CommRingCat.ofHom (algebraMap S T))) = gE)
    (heE₂ : eE.hom ≫ pullback.snd E.f (Spec.map (CommRingCat.ofHom (algebraMap S T))) = E'.f)
    (x : ↥Λ) :
    E'.act x ≫ eE.hom = eE.hom ≫
      pullback.lift (pullback.fst E.f (Spec.map (CommRingCat.ofHom (algebraMap S T))) ≫ E.act x)
        (pullback.snd E.f (Spec.map (CommRingCat.ofHom (algebraMap S T))))
        (by rw [Category.assoc, E.act_over]; exact pullback.condition) := by
  obtain ⟨hsq, -, hact, -⟩ := hgE
  apply pullback.hom_ext
  · simp only [Category.assoc, pullback.lift_fst, heE₁, hact x]
    rw [← Category.assoc, heE₁]
  · simp only [Category.assoc, pullback.lift_snd, heE₂, E'.act_over]

theorem exists_isIsogenyPair_of_hom
    {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} {N : ℕ} {S : Type} [CommRing S]
    {ι : Type} [Fintype ι] (β : ι → ↥Λ) (hβ : ∀ x : ↥Λ, ∃ c : ι → ℤ, x = ∑ j, c j • β j) (r d : ℕ)
    (E A : FakeEllipticCurve Λ N S) {T : Type} [CommRing T] [Algebra S T]
    (E' A' : FakeEllipticCurve Λ N T)
    (gE : E'.A ⟶ E.A) (hgE : FakeEllipticCurve.IsPullbackVia (algebraMap S T) E E' gE)
    (gA : A'.A ⟶ A.A) (hgA : FakeEllipticCurve.IsPullbackVia (algebraMap S T) A A' gA)
    (eE : E'.A ≅ pullback E.f (Spec.map (CommRingCat.ofHom (algebraMap S T))))
    (heE₁ : eE.hom ≫ pullback.fst E.f (Spec.map (CommRingCat.ofHom (algebraMap S T))) = gE)
    (heE₂ : eE.hom ≫ pullback.snd E.f (Spec.map (CommRingCat.ofHom (algebraMap S T))) = E'.f)
    (eA : A'.A ≅ pullback A.f (Spec.map (CommRingCat.ofHom (algebraMap S T))))
    (heA₁ : eA.hom ≫ pullback.fst A.f (Spec.map (CommRingCat.ofHom (algebraMap S T))) = gA)
    (heA₂ : eA.hom ≫ pullback.snd A.f (Spec.map (CommRingCat.ofHom (algebraMap S T))) = A'.f)
    (φh : pullback E.f (Spec.map (CommRingCat.ofHom (algebraMap S T))) ⟶ A.A)
    (hφh : φh ≫ A.f = pullback.snd E.f (Spec.map (CommRingCat.ofHom (algebraMap S T))) ≫ Spec.map (CommRingCat.ofHom (algebraMap S T)))
    (φh' : pullback A.f (Spec.map (CommRingCat.ofHom (algebraMap S T))) ⟶ E.A)
    (hφh' : φh' ≫ E.f = pullback.snd A.f (Spec.map (CommRingCat.ofHom (algebraMap S T))) ≫ Spec.map (CommRingCat.ofHom (algebraMap S T)))
    (h₁ : ∀ (T₀ : Scheme.{0}) (t' : T₀ ⟶ Spec (CommRingCat.of T)) (P Q : SchemeHomOver (t' ≫ Spec.map (CommRingCat.ofHom (algebraMap S T))) E.f),
        pullback.lift (E.L.mul (t' ≫ Spec.map (CommRingCat.ofHom (algebraMap S T))) P Q).1 t' (E.L.mul (t' ≫ Spec.map (CommRingCat.ofHom (algebraMap S T))) P Q).2 ≫ φh =
          (A.L.mul (t' ≫ Spec.map (CommRingCat.ofHom (algebraMap S T)))
            ⟨pullback.lift P.1 t' P.2 ≫ φh, by rw [Category.assoc, hφh, ← Category.assoc, pullback.lift_snd]⟩
            ⟨pullback.lift Q.1 t' Q.2 ≫ φh, by rw [Category.assoc, hφh, ← Category.assoc, pullback.lift_snd]⟩).1)
    (h₂ : ∀ (T₀ : Scheme.{0}) (t' : T₀ ⟶ Spec (CommRingCat.of T)) (P Q : SchemeHomOver (t' ≫ Spec.map (CommRingCat.ofHom (algebraMap S T))) A.f),
        pullback.lift (A.L.mul (t' ≫ Spec.map (CommRingCat.ofHom (algebraMap S T))) P Q).1 t' (A.L.mul (t' ≫ Spec.map (CommRingCat.ofHom (algebraMap S T))) P Q).2 ≫ φh' =
          (E.L.mul (t' ≫ Spec.map (CommRingCat.ofHom (algebraMap S T)))
            ⟨pullback.lift P.1 t' P.2 ≫ φh', by rw [Category.assoc, hφh', ← Category.assoc, pullback.lift_snd]⟩
            ⟨pullback.lift Q.1 t' Q.2 ≫ φh', by rw [Category.assoc, hφh', ← Category.assoc, pullback.lift_snd]⟩).1)
    (h₃E : ∀ i : ι, pullback.lift (pullback.fst E.f (Spec.map (CommRingCat.ofHom (algebraMap S T))) ≫ E.act (β i))
        (pullback.snd E.f (Spec.map (CommRingCat.ofHom (algebraMap S T)))) (by rw [Category.assoc, E.act_over]; exact pullback.condition) ≫ φh = φh ≫ A.act (β i))
    (h₃A : ∀ i : ι, pullback.lift (pullback.fst A.f (Spec.map (CommRingCat.ofHom (algebraMap S T))) ≫ A.act (β i))
        (pullback.snd A.f (Spec.map (CommRingCat.ofHom (algebraMap S T)))) (by rw [Category.assoc, A.act_over]; exact pullback.condition) ≫ φh' = φh' ≫ E.act (β i))
    (h₃d : ∀ hd : (((r ^ d : ℕ) : ℚ) : ℍ[ℚ, a, b]) ∈ Λ,
        pullback.lift φh (pullback.snd E.f (Spec.map (CommRingCat.ofHom (algebraMap S T)))) hφh ≫ φh' =
            pullback.fst E.f (Spec.map (CommRingCat.ofHom (algebraMap S T))) ≫ E.act ⟨_, hd⟩ ∧
        pullback.lift φh' (pullback.snd A.f (Spec.map (CommRingCat.ofHom (algebraMap S T)))) hφh' ≫ φh =
            pullback.fst A.f (Spec.map (CommRingCat.ofHom (algebraMap S T))) ≫ A.act ⟨_, hd⟩) :
    ∃ (φ : E'.A ⟶ A'.A) (φ' : A'.A ⟶ E'.A) (hφ : φ ≫ A'.f = E'.f),
      FakeEllipticCurve.IsIsogenyPair (r ^ d) E' A' φ φ' ∧ φ ≫ gA = eE.hom ≫ φh ∧ φ' ≫ gE = eA.hom ≫ φh' := by
  obtain ⟨hsqE, hmulE, hactE, hlevE⟩ := hgE
  obtain ⟨hsqA, hmulA, hactA, hlevA⟩ := hgA

  let φ : E'.A ⟶ A'.A := hsqA.lift (eE.hom ≫ φh) E'.f (by rw [Category.assoc, hφh, ← Category.assoc, heE₂])
  let φ' : A'.A ⟶ E'.A := hsqE.lift (eA.hom ≫ φh') A'.f (by rw [Category.assoc, hφh', ← Category.assoc, heA₂])
  have hφgA : φ ≫ gA = eE.hom ≫ φh := hsqA.lift_fst _ _ _
  have hφf : φ ≫ A'.f = E'.f := hsqA.lift_snd _ _ _
  have hφ'gE : φ' ≫ gE = eA.hom ≫ φh' := hsqE.lift_fst _ _ _
  have hφ'f : φ' ≫ E'.f = A'.f := hsqE.lift_snd _ _ _
  have hhom : ∀ {T₀ : Scheme.{0}} (t : T₀ ⟶ Spec (CommRingCat.of T)) (P Q : SchemeHomOver t E'.f),
      mapPt φ hφf (E'.L.mul t P Q) = A'.L.mul t (mapPt φ hφf P) (mapPt φ hφf Q) := by
    intro T₀ t P Q
    apply Subtype.ext
    apply hsqA.hom_ext
    · show ((E'.L.mul t P Q).1 ≫ φ) ≫ gA = (A'.L.mul t (mapPt φ hφf P) (mapPt φ hφf Q)).1 ≫ gA
      rw [Category.assoc, hφgA, ← Category.assoc,
        mul_comp_presIso E E' gE ⟨hsqE, hmulE, hactE, hlevE⟩ eE heE₁ heE₂ t P Q, h₁,
        hmulA t (mapPt φ hφf P) (mapPt φ hφf Q)]
      apply mul_val_congr A.L
      · show pullback.lift (P.1 ≫ gE) t _ ≫ φh = (P.1 ≫ φ) ≫ gA
        have e1 : (P.1 ≫ φ) ≫ gA = (P.1 ≫ eE.hom) ≫ φh := by simp only [Category.assoc, hφgA]
        rw [e1]; congr 1
        apply pullback.hom_ext
        · simp only [Category.assoc, pullback.lift_fst, heE₁]
        · simp only [Category.assoc, pullback.lift_snd, heE₂]; exact P.2.symm
      · show pullback.lift (Q.1 ≫ gE) t _ ≫ φh = (Q.1 ≫ φ) ≫ gA
        have e1 : (Q.1 ≫ φ) ≫ gA = (Q.1 ≫ eE.hom) ≫ φh := by simp only [Category.assoc, hφgA]
        rw [e1]; congr 1
        apply pullback.hom_ext
        · simp only [Category.assoc, pullback.lift_fst, heE₁]
        · simp only [Category.assoc, pullback.lift_snd, heE₂]; exact Q.2.symm
    · show ((E'.L.mul t P Q).1 ≫ φ) ≫ A'.f = (A'.L.mul t (mapPt φ hφf P) (mapPt φ hφf Q)).1 ≫ A'.f
      rw [Category.assoc, hφf, (E'.L.mul t P Q).2, (A'.L.mul t _ _).2]
  have hhom' : ∀ {T₀ : Scheme.{0}} (t : T₀ ⟶ Spec (CommRingCat.of T)) (P Q : SchemeHomOver t A'.f),
      mapPt φ' hφ'f (A'.L.mul t P Q) = E'.L.mul t (mapPt φ' hφ'f P) (mapPt φ' hφ'f Q) := by
    intro T₀ t P Q
    apply Subtype.ext
    apply hsqE.hom_ext
    · show ((A'.L.mul t P Q).1 ≫ φ') ≫ gE = (E'.L.mul t (mapPt φ' hφ'f P) (mapPt φ' hφ'f Q)).1 ≫ gE
      rw [Category.assoc, hφ'gE, ← Category.assoc,
        mul_comp_presIso A A' gA ⟨hsqA, hmulA, hactA, hlevA⟩ eA heA₁ heA₂ t P Q, h₂,
        hmulE t (mapPt φ' hφ'f P) (mapPt φ' hφ'f Q)]
      apply mul_val_congr E.L
      · show pullback.lift (P.1 ≫ gA) t _ ≫ φh' = (P.1 ≫ φ') ≫ gE
        have e1 : (P.1 ≫ φ') ≫ gE = (P.1 ≫ eA.hom) ≫ φh' := by simp only [Category.assoc, hφ'gE]
        rw [e1]; congr 1
        apply pullback.hom_ext
        · simp only [Category.assoc, pullback.lift_fst, heA₁]
        · simp only [Category.assoc, pullback.lift_snd, heA₂]; exact P.2.symm
      · show pullback.lift (Q.1 ≫ gA) t _ ≫ φh' = (Q.1 ≫ φ') ≫ gE
        have e1 : (Q.1 ≫ φ') ≫ gE = (Q.1 ≫ eA.hom) ≫ φh' := by simp only [Category.assoc, hφ'gE]
        rw [e1]; congr 1
        apply pullback.hom_ext
        · simp only [Category.assoc, pullback.lift_fst, heA₁]
        · simp only [Category.assoc, pullback.lift_snd, heA₂]; exact Q.2.symm
    · show ((A'.L.mul t P Q).1 ≫ φ') ≫ E'.f = (E'.L.mul t (mapPt φ' hφ'f P) (mapPt φ' hφ'f Q)).1 ≫ E'.f
      rw [Category.assoc, hφ'f, (A'.L.mul t P Q).2, (E'.L.mul t _ _).2]

  have hβlin : ∀ j : ι, E'.act (β j) ≫ φ = φ ≫ A'.act (β j) := by
    intro j
    apply hsqA.hom_ext
    · calc (E'.act (β j) ≫ φ) ≫ gA = E'.act (β j) ≫ eE.hom ≫ φh := by rw [Category.assoc, hφgA]
        _ = eE.hom ≫ φh ≫ A.act (β j) := by
              rw [← Category.assoc, act_comp_presIso E E' gE ⟨hsqE, hmulE, hactE, hlevE⟩ eE heE₁ heE₂ (β j), Category.assoc, h₃E j]
        _ = (φ ≫ A'.act (β j)) ≫ gA := by
              rw [Category.assoc, hactA (β j)]; simp only [← Category.assoc, hφgA]
    · simp only [Category.assoc, hφf, E'.act_over, A'.act_over]
  have hlin := forall_act_comp_eq_of_forall_basis β hβ E' A' φ hφf hhom hβlin
  have hβlin' : ∀ j : ι, A'.act (β j) ≫ φ' = φ' ≫ E'.act (β j) := by
    intro j
    apply hsqE.hom_ext
    · calc (A'.act (β j) ≫ φ') ≫ gE = A'.act (β j) ≫ eA.hom ≫ φh' := by rw [Category.assoc, hφ'gE]
        _ = eA.hom ≫ φh' ≫ E.act (β j) := by
              rw [← Category.assoc, act_comp_presIso A A' gA ⟨hsqA, hmulA, hactA, hlevA⟩ eA heA₁ heA₂ (β j), Category.assoc, h₃A j]
        _ = (φ' ≫ E'.act (β j)) ≫ gE := by
              rw [Category.assoc, hactE (β j)]; simp only [← Category.assoc, hφ'gE]
    · simp only [Category.assoc, hφ'f, A'.act_over, E'.act_over]
  have hlin' := forall_act_comp_eq_of_forall_basis β hβ A' E' φ' hφ'f hhom' hβlin'

  have hφeA : φ ≫ eA.hom = eE.hom ≫ pullback.lift φh (pullback.snd E.f (Spec.map (CommRingCat.ofHom (algebraMap S T)))) hφh := by
    apply pullback.hom_ext
    · rw [Category.assoc, heA₁, hφgA, Category.assoc, pullback.lift_fst]
    · rw [Category.assoc, heA₂, hφf, Category.assoc, pullback.lift_snd, heE₂]
  have hφ'eE : φ' ≫ eE.hom = eA.hom ≫ pullback.lift φh' (pullback.snd A.f (Spec.map (CommRingCat.ofHom (algebraMap S T)))) hφh' := by
    apply pullback.hom_ext
    · rw [Category.assoc, heE₁, hφ'gE, Category.assoc, pullback.lift_fst]
    · rw [Category.assoc, heE₂, hφ'f, Category.assoc, pullback.lift_snd, heA₂]
  have hdeg : ∀ hd : (((r ^ d : ℕ) : ℚ) : ℍ[ℚ, a, b]) ∈ Λ,
      φ ≫ φ' = E'.act ⟨_, hd⟩ ∧ φ' ≫ φ = A'.act ⟨_, hd⟩ := by
    intro hd
    obtain ⟨hd₁, hd₂⟩ := h₃d hd
    constructor
    · apply hsqE.hom_ext
      · rw [Category.assoc, hφ'gE, ← Category.assoc, hφeA, Category.assoc, hd₁, ← Category.assoc, heE₁, hactE]
      · rw [Category.assoc, hφ'f, hφf, E'.act_over]
    · apply hsqA.hom_ext
      · rw [Category.assoc, hφgA, ← Category.assoc, hφ'eE, Category.assoc, hd₂, ← Category.assoc, heA₁, hactA]
      · rw [Category.assoc, hφf, hφ'f, A'.act_over]
  exact ⟨φ, φ', hφf, ⟨hφf, hφ'f, hhom, hhom', hlin, hlin', hdeg⟩, hφgA, hφ'gE⟩

theorem presIso_inv_act
    {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} {N : ℕ} {S : Type} [CommRing S]
    (E : FakeEllipticCurve Λ N S) {T : Type} [CommRing T] [Algebra S T] (E' : FakeEllipticCurve Λ N T)
    (gE : E'.A ⟶ E.A) (hgE : FakeEllipticCurve.IsPullbackVia (algebraMap S T) E E' gE)
    (eE : E'.A ≅ pullback E.f (Spec.map (CommRingCat.ofHom (algebraMap S T))))
    (heE₁ : eE.hom ≫ pullback.fst E.f (Spec.map (CommRingCat.ofHom (algebraMap S T))) = gE)
    (heE₂ : eE.hom ≫ pullback.snd E.f (Spec.map (CommRingCat.ofHom (algebraMap S T))) = E'.f)
    (x : ↥Λ) :
    pullback.lift (pullback.fst E.f (Spec.map (CommRingCat.ofHom (algebraMap S T))) ≫ E.act x)
        (pullback.snd E.f (Spec.map (CommRingCat.ofHom (algebraMap S T))))
        (by rw [Category.assoc, E.act_over]; exact pullback.condition) ≫ eE.inv = eE.inv ≫ E'.act x := by
  have h := act_comp_presIso E E' gE hgE eE heE₁ heE₂ x
  rw [← cancel_mono eE.hom]
  simp only [Category.assoc, eE.inv_hom_id, Category.comp_id]
  rw [h, eE.inv_hom_id_assoc]

theorem lin_transport
    {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} {N : ℕ} {S : Type} [CommRing S]
    (E A : FakeEllipticCurve Λ N S) {T : Type} [CommRing T] [Algebra S T]
    (E' A' : FakeEllipticCurve Λ N T)
    (gE : E'.A ⟶ E.A) (hgE : FakeEllipticCurve.IsPullbackVia (algebraMap S T) E E' gE)
    (gA : A'.A ⟶ A.A) (hgA : FakeEllipticCurve.IsPullbackVia (algebraMap S T) A A' gA)
    (eE : E'.A ≅ pullback E.f (Spec.map (CommRingCat.ofHom (algebraMap S T))))
    (heE₁ : eE.hom ≫ pullback.fst E.f (Spec.map (CommRingCat.ofHom (algebraMap S T))) = gE)
    (heE₂ : eE.hom ≫ pullback.snd E.f (Spec.map (CommRingCat.ofHom (algebraMap S T))) = E'.f)
    (φ : E'.A ⟶ A'.A) (x : ↥Λ) (hlin : E'.act x ≫ φ = φ ≫ A'.act x) :
    pullback.lift (pullback.fst E.f (Spec.map (CommRingCat.ofHom (algebraMap S T))) ≫ E.act x)
        (pullback.snd E.f (Spec.map (CommRingCat.ofHom (algebraMap S T))))
        (by rw [Category.assoc, E.act_over]; exact pullback.condition) ≫ (eE.inv ≫ φ ≫ gA) = (eE.inv ≫ φ ≫ gA) ≫ A.act x := by
  obtain ⟨-, -, hactA, -⟩ := hgA
  rw [← Category.assoc, presIso_inv_act E E' gE hgE eE heE₁ heE₂ x]
  simp only [Category.assoc]
  rw [← Category.assoc (E'.act x), hlin, Category.assoc, hactA x]

theorem deg_transport
    {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} {N : ℕ} {S : Type} [CommRing S]
    (E A : FakeEllipticCurve Λ N S) {T : Type} [CommRing T] [Algebra S T]
    (E' A' : FakeEllipticCurve Λ N T)
    (gE : E'.A ⟶ E.A) (hgE : FakeEllipticCurve.IsPullbackVia (algebraMap S T) E E' gE)
    (gA : A'.A ⟶ A.A) (hgA : FakeEllipticCurve.IsPullbackVia (algebraMap S T) A A' gA)
    (eE : E'.A ≅ pullback E.f (Spec.map (CommRingCat.ofHom (algebraMap S T))))
    (heE₁ : eE.hom ≫ pullback.fst E.f (Spec.map (CommRingCat.ofHom (algebraMap S T))) = gE)
    (heE₂ : eE.hom ≫ pullback.snd E.f (Spec.map (CommRingCat.ofHom (algebraMap S T))) = E'.f)
    (eA : A'.A ≅ pullback A.f (Spec.map (CommRingCat.ofHom (algebraMap S T))))
    (heA₁ : eA.hom ≫ pullback.fst A.f (Spec.map (CommRingCat.ofHom (algebraMap S T))) = gA)
    (heA₂ : eA.hom ≫ pullback.snd A.f (Spec.map (CommRingCat.ofHom (algebraMap S T))) = A'.f)
    (φ : E'.A ⟶ A'.A) (hφ : φ ≫ A'.f = E'.f) (φ' : A'.A ⟶ E'.A) (x : ↥Λ) (hdeg : φ ≫ φ' = E'.act x)
    (hφh : (eE.inv ≫ φ ≫ gA) ≫ A.f =
      pullback.snd E.f (Spec.map (CommRingCat.ofHom (algebraMap S T))) ≫ Spec.map (CommRingCat.ofHom (algebraMap S T))) :
    pullback.lift (eE.inv ≫ φ ≫ gA) (pullback.snd E.f (Spec.map (CommRingCat.ofHom (algebraMap S T)))) hφh ≫ (eA.inv ≫ φ' ≫ gE) =
      pullback.fst E.f (Spec.map (CommRingCat.ofHom (algebraMap S T))) ≫ E.act x := by
  obtain ⟨-, -, hactE, -⟩ := hgE
  have hinv_fst : eE.inv ≫ gE = pullback.fst E.f (Spec.map (CommRingCat.ofHom (algebraMap S T))) := by
    rw [← heE₁, ← Category.assoc, eE.inv_hom_id, Category.id_comp]
  have hinv_snd : eE.inv ≫ E'.f = pullback.snd E.f (Spec.map (CommRingCat.ofHom (algebraMap S T))) := by
    rw [← heE₂, ← Category.assoc, eE.inv_hom_id, Category.id_comp]
  have hL : pullback.lift (eE.inv ≫ φ ≫ gA) (pullback.snd E.f (Spec.map (CommRingCat.ofHom (algebraMap S T)))) hφh =
      eE.inv ≫ φ ≫ eA.hom := by
    apply pullback.hom_ext
    · simp only [pullback.lift_fst, Category.assoc, heA₁]
    · simp only [pullback.lift_snd, Category.assoc, heA₂, hφ, hinv_snd]
  rw [hL]
  simp only [Category.assoc]
  rw [eA.hom_inv_id_assoc, ← Category.assoc φ φ', hdeg, hactE x, ← Category.assoc, hinv_fst]

noncomputable def presIso {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} {N : ℕ} {S : Type} [CommRing S]
    (E : FakeEllipticCurve Λ N S) {T : Type} [CommRing T] [Algebra S T] (E' : FakeEllipticCurve Λ N T)
    (gE : E'.A ⟶ E.A) (hgE : FakeEllipticCurve.IsPullbackVia (algebraMap S T) E E' gE) :
    E'.A ≅ pullback E.f (Spec.map (CommRingCat.ofHom (algebraMap S T))) := hgE.fst.isoPullback

theorem presIso_hom_fst {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} {N : ℕ} {S : Type} [CommRing S]
    (E : FakeEllipticCurve Λ N S) {T : Type} [CommRing T] [Algebra S T] (E' : FakeEllipticCurve Λ N T)
    (gE : E'.A ⟶ E.A) (hgE : FakeEllipticCurve.IsPullbackVia (algebraMap S T) E E' gE) :
    (presIso E E' gE hgE).hom ≫ pullback.fst E.f (Spec.map (CommRingCat.ofHom (algebraMap S T))) = gE :=
  hgE.fst.isoPullback_hom_fst

theorem presIso_hom_snd {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} {N : ℕ} {S : Type} [CommRing S]
    (E : FakeEllipticCurve Λ N S) {T : Type} [CommRing T] [Algebra S T] (E' : FakeEllipticCurve Λ N T)
    (gE : E'.A ⟶ E.A) (hgE : FakeEllipticCurve.IsPullbackVia (algebraMap S T) E E' gE) :
    (presIso E E' gE hgE).hom ≫ pullback.snd E.f (Spec.map (CommRingCat.ofHom (algebraMap S T))) = E'.f :=
  hgE.fst.isoPullback_hom_snd

theorem presIso_inv_snd {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} {N : ℕ} {S : Type} [CommRing S]
    (E : FakeEllipticCurve Λ N S) {T : Type} [CommRing T] [Algebra S T] (E' : FakeEllipticCurve Λ N T)
    (gE : E'.A ⟶ E.A) (hgE : FakeEllipticCurve.IsPullbackVia (algebraMap S T) E E' gE) :
    (presIso E E' gE hgE).inv ≫ E'.f = pullback.snd E.f (Spec.map (CommRingCat.ofHom (algebraMap S T))) := by
  rw [← cancel_epi (presIso E E' gE hgE).hom, Iso.hom_inv_id_assoc, presIso_hom_snd]

theorem presIso_inv_fst {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} {N : ℕ} {S : Type} [CommRing S]
    (E : FakeEllipticCurve Λ N S) {T : Type} [CommRing T] [Algebra S T] (E' : FakeEllipticCurve Λ N T)
    (gE : E'.A ⟶ E.A) (hgE : FakeEllipticCurve.IsPullbackVia (algebraMap S T) E E' gE) :
    (presIso E E' gE hgE).inv ≫ gE = pullback.fst E.f (Spec.map (CommRingCat.ofHom (algebraMap S T))) := by
  rw [← cancel_epi (presIso E E' gE hgE).hom, Iso.hom_inv_id_assoc, presIso_hom_fst]

theorem trh_over {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} {N : ℕ} {S : Type} [CommRing S]
    (E A : FakeEllipticCurve Λ N S) {T : Type} [CommRing T] [Algebra S T] (E' A' : FakeEllipticCurve Λ N T)
    (gE : E'.A ⟶ E.A) (hgE : FakeEllipticCurve.IsPullbackVia (algebraMap S T) E E' gE)
    (gA : A'.A ⟶ A.A) (hgA : FakeEllipticCurve.IsPullbackVia (algebraMap S T) A A' gA)
    (φ : E'.A ⟶ A'.A) (hφ : φ ≫ A'.f = E'.f) :
    ((presIso E E' gE hgE).inv ≫ φ ≫ gA) ≫ A.f =
      pullback.snd E.f (Spec.map (CommRingCat.ofHom (algebraMap S T))) ≫ Spec.map (CommRingCat.ofHom (algebraMap S T)) := by
  simp only [Category.assoc]
  rw [hgA.fst.w, ← Category.assoc φ, hφ, ← Category.assoc, presIso_inv_snd]

theorem presIso_inv_comp_iso {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} {N : ℕ} {S : Type} [CommRing S]
    (E : FakeEllipticCurve Λ N S) {T : Type} [CommRing T] [Algebra S T] (E' E'' : FakeEllipticCurve Λ N T)
    (gE : E'.A ⟶ E.A) (hgE : FakeEllipticCurve.IsPullbackVia (algebraMap S T) E E' gE)
    (gE'' : E''.A ⟶ E.A) (hgE'' : FakeEllipticCurve.IsPullbackVia (algebraMap S T) E E'' gE'')
    (iE : E'.A ≅ E''.A) (hiE : iE.hom ≫ E''.f = E'.f) (hg : iE.hom ≫ gE'' = gE) :
    (presIso E E' gE hgE).inv ≫ iE.hom = (presIso E E'' gE'' hgE'').inv := by
  have h : iE.hom ≫ (presIso E E'' gE'' hgE'').hom = (presIso E E' gE hgE).hom := by
    apply pullback.hom_ext
    · rw [Category.assoc, presIso_hom_fst, presIso_hom_fst, hg]
    · rw [Category.assoc, presIso_hom_snd, presIso_hom_snd, hiE]
  rw [← cancel_mono (presIso E E'' gE'' hgE'').hom, Category.assoc, h, Iso.inv_hom_id, Iso.inv_hom_id]

theorem presIso_baseChange {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} {N : ℕ} {S : Type} [CommRing S]
    (E : FakeEllipticCurve Λ N S) {T T' : Type} [CommRing T] [Algebra S T] [CommRing T'] [Algebra S T'] (f : T →ₐ[S] T')
    (E' : FakeEllipticCurve Λ N T) (gE : E'.A ⟶ E.A) (hgE : FakeEllipticCurve.IsPullbackVia (algebraMap S T) E E' gE)
    (E'' : FakeEllipticCurve Λ N T') (hE : E''.A ⟶ E'.A) (hhE : FakeEllipticCurve.IsPullbackVia (f : T →+* T') E' E'' hE)
    (hgE'' : FakeEllipticCurve.IsPullbackVia (algebraMap S T') E E'' (hE ≫ gE))
    (hs : Spec.map (CommRingCat.ofHom (f : T →+* T')) ≫ Spec.map (CommRingCat.ofHom (algebraMap S T)) = Spec.map (CommRingCat.ofHom (algebraMap S T'))) :
    (presIso E E'' (hE ≫ gE) hgE'').inv ≫ hE =
      pullback.lift (pullback.fst E.f (Spec.map (CommRingCat.ofHom (algebraMap S T'))))
        (pullback.snd E.f (Spec.map (CommRingCat.ofHom (algebraMap S T'))) ≫ Spec.map (CommRingCat.ofHom (f : T →+* T')))
        (by rw [Category.assoc, hs]; exact pullback.condition) ≫ (presIso E E' gE hgE).inv := by
  have h : hE ≫ (presIso E E' gE hgE).hom = (presIso E E'' (hE ≫ gE) hgE'').hom ≫
      pullback.lift (pullback.fst E.f (Spec.map (CommRingCat.ofHom (algebraMap S T'))))
        (pullback.snd E.f (Spec.map (CommRingCat.ofHom (algebraMap S T'))) ≫ Spec.map (CommRingCat.ofHom (f : T →+* T')))
        (by rw [Category.assoc, hs]; exact pullback.condition) := by
    apply pullback.hom_ext
    · simp only [Category.assoc, pullback.lift_fst, presIso_hom_fst]
    · simp only [Category.assoc, pullback.lift_snd, presIso_hom_snd]
      rw [← Category.assoc, presIso_hom_snd]; exact hhE.fst.w
  rw [← cancel_mono (presIso E E' gE hgE).hom]
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  rw [h, Iso.inv_hom_id_assoc]

end BridgeSol

open BridgeSol in
theorem solution
    {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} {N : ℕ}
    (β : Fin (2 * 2) → ↥Λ) (hβ : ∀ x : ↥Λ, ∃! c : Fin (2 * 2) → ℤ, x = ∑ j, c j • β j) (r d : ℕ)
    (S : Type) [CommRing S] (E A : FakeEllipticCurve Λ N S)
    (𝓛E : E.A.Modules) (hE₁ : Scheme.Modules.IsInvertible 𝓛E) (hE₂ : Scheme.Modules.ClosedImmersionBySections 𝓛E E.f)
    (𝓛A : A.A.Modules) (hA₁ : Scheme.Modules.IsInvertible 𝓛A) (hA₂ : Scheme.Modules.ClosedImmersionBySections 𝓛A A.f) :
    ∃ (Z : Scheme.{0}) (ζ : Z ⟶ Spec (CommRingCat.of S)) (_ : LocallyOfFinitePresentation ζ) (_ : IsSeparated ζ)
      (ptZ : ∀ (T : Type) [CommRing T] [Algebra S T]
        (E' A' : FakeEllipticCurve Λ N T) (gE : E'.A ⟶ E.A) (_ : FakeEllipticCurve.IsPullbackVia (algebraMap S T) E E' gE)
        (gA : A'.A ⟶ A.A) (_ : FakeEllipticCurve.IsPullbackVia (algebraMap S T) A A' gA)
        (φ : E'.A ⟶ A'.A) (φ' : A'.A ⟶ E'.A) (hφ : φ ≫ A'.f = E'.f),
        FakeEllipticCurve.IsIsogenyPair (r ^ d) E' A' φ φ' →
          SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap S T))) ζ),

      (∀ (T : Type) [CommRing T] [Algebra S T]
          (E' A' : FakeEllipticCurve Λ N T) (gE : E'.A ⟶ E.A) (hgE : FakeEllipticCurve.IsPullbackVia (algebraMap S T) E E' gE)
          (gA : A'.A ⟶ A.A) (hgA : FakeEllipticCurve.IsPullbackVia (algebraMap S T) A A' gA)
          (φ : E'.A ⟶ A'.A) (φ' : A'.A ⟶ E'.A) (hφ : φ ≫ A'.f = E'.f)
          (hp : FakeEllipticCurve.IsIsogenyPair (r ^ d) E' A' φ φ')
          (E'' A'' : FakeEllipticCurve Λ N T) (gE'' : E''.A ⟶ E.A) (hgE'' : FakeEllipticCurve.IsPullbackVia (algebraMap S T) E E'' gE'')
          (gA'' : A''.A ⟶ A.A) (hgA'' : FakeEllipticCurve.IsPullbackVia (algebraMap S T) A A'' gA'')
          (ψ : E''.A ⟶ A''.A) (ψ' : A''.A ⟶ E''.A) (hψ : ψ ≫ A''.f = E''.f)
          (hq : FakeEllipticCurve.IsIsogenyPair (r ^ d) E'' A'' ψ ψ')
          (iE : E'.A ≅ E''.A) (hiE : iE.hom ≫ E''.f = E'.f) (iA : A'.A ≅ A''.A) (hiA : iA.hom ≫ A''.f = A'.f),
          FakeEllipticCurve.IsoVia E' E'' iE hiE → FakeEllipticCurve.IsoVia A' A'' iA hiA →
          iE.hom ≫ gE'' = gE → iA.hom ≫ gA'' = gA → iE.hom ≫ ψ = φ ≫ iA.hom → iA.hom ≫ ψ' = φ' ≫ iE.hom →
            ptZ T E' A' gE hgE gA hgA φ φ' hφ hp = ptZ T E'' A'' gE'' hgE'' gA'' hgA'' ψ ψ' hψ hq) ∧

      (∀ (T T' : Type) [CommRing T] [Algebra S T] [CommRing T'] [Algebra S T'] (f : T →ₐ[S] T')
          (E' A' : FakeEllipticCurve Λ N T) (gE : E'.A ⟶ E.A) (hgE : FakeEllipticCurve.IsPullbackVia (algebraMap S T) E E' gE)
          (gA : A'.A ⟶ A.A) (hgA : FakeEllipticCurve.IsPullbackVia (algebraMap S T) A A' gA)
          (φ : E'.A ⟶ A'.A) (φ' : A'.A ⟶ E'.A) (hφ : φ ≫ A'.f = E'.f)
          (hp : FakeEllipticCurve.IsIsogenyPair (r ^ d) E' A' φ φ')
          (E'' A'' : FakeEllipticCurve Λ N T') (hE : E''.A ⟶ E'.A) (hhE : FakeEllipticCurve.IsPullbackVia (f : T →+* T') E' E'' hE)
          (hA : A''.A ⟶ A'.A) (hhA : FakeEllipticCurve.IsPullbackVia (f : T →+* T') A' A'' hA)
          (hgE'' : FakeEllipticCurve.IsPullbackVia (algebraMap S T') E E'' (hE ≫ gE))
          (hgA'' : FakeEllipticCurve.IsPullbackVia (algebraMap S T') A A'' (hA ≫ gA))
          (ψ : E''.A ⟶ A''.A) (ψ' : A''.A ⟶ E''.A) (hψ : ψ ≫ A''.f = E''.f)
          (hq : FakeEllipticCurve.IsIsogenyPair (r ^ d) E'' A'' ψ ψ'),
          ψ ≫ hA = hE ≫ φ → ψ' ≫ hE = hA ≫ φ' →
            (ptZ T' E'' A'' (hE ≫ gE) hgE'' (hA ≫ gA) hgA'' ψ ψ' hψ hq).1 =
              Spec.map (CommRingCat.ofHom (f : T →+* T')) ≫ (ptZ T E' A' gE hgE gA hgA φ φ' hφ hp).1) ∧

      (∀ (T : Type) [CommRing T] [Algebra S T]
          (E' A' : FakeEllipticCurve Λ N T) (gE : E'.A ⟶ E.A) (hgE : FakeEllipticCurve.IsPullbackVia (algebraMap S T) E E' gE)
          (gA : A'.A ⟶ A.A) (hgA : FakeEllipticCurve.IsPullbackVia (algebraMap S T) A A' gA)
          (z : SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap S T))) ζ),
          ∃ (φ : E'.A ⟶ A'.A) (φ' : A'.A ⟶ E'.A) (hφ : φ ≫ A'.f = E'.f)
            (hp : FakeEllipticCurve.IsIsogenyPair (r ^ d) E' A' φ φ'),
            ptZ T E' A' gE hgE gA hgA φ φ' hφ hp = z) ∧

      (∀ (T : Type) [CommRing T] [Algebra S T]
          (E' A' : FakeEllipticCurve Λ N T) (gE : E'.A ⟶ E.A) (hgE : FakeEllipticCurve.IsPullbackVia (algebraMap S T) E E' gE)
          (gA : A'.A ⟶ A.A) (hgA : FakeEllipticCurve.IsPullbackVia (algebraMap S T) A A' gA)
          (φ₁ : E'.A ⟶ A'.A) (φ₁' : A'.A ⟶ E'.A) (hφ₁ : φ₁ ≫ A'.f = E'.f)
          (hp₁ : FakeEllipticCurve.IsIsogenyPair (r ^ d) E' A' φ₁ φ₁')
          (φ₂ : E'.A ⟶ A'.A) (φ₂' : A'.A ⟶ E'.A) (hφ₂ : φ₂ ≫ A'.f = E'.f)
          (hp₂ : FakeEllipticCurve.IsIsogenyPair (r ^ d) E' A' φ₂ φ₂'),
          ptZ T E' A' gE hgE gA hgA φ₁ φ₁' hφ₁ hp₁ = ptZ T E' A' gE hgE gA hgA φ₂ φ₂' hφ₂ hp₂ → φ₁ = φ₂ ∧ φ₁' = φ₂') := by
  classical
  obtain ⟨X, πX, pt, hnat, hsurj, hinj, hsep, hlft, hlfp⟩ :=
    CerednikDrinfeld.QM.FakeEllipticCurve.exists_represents_homPair_act_comp_eq_of_closedImmersionBySections β hβ r d S E A 𝓛E hE₁ hE₂ 𝓛A hA₁ hA₂
  have hβ' : ∀ x : ↥Λ, ∃ c : Fin (2 * 2) → ℤ, x = ∑ j, c j • β j := fun x => (hβ x).exists

  have ptcongr : ∀ (S' : Type) [CommRing S'] (s : Spec (CommRingCat.of S') ⟶ Spec (CommRingCat.of S))
      (φ₁ φ₂ : pullback E.f s ⟶ A.A) (h₁ : φ₁ ≫ A.f = pullback.snd E.f s ≫ s) (h₂ : φ₂ ≫ A.f = pullback.snd E.f s ≫ s)
      (ψ₁ ψ₂ : pullback A.f s ⟶ E.A) (k₁ : ψ₁ ≫ E.f = pullback.snd A.f s ≫ s) (k₂ : ψ₂ ≫ E.f = pullback.snd A.f s ≫ s)
      (a₁ : _) (b₁ : _) (c₁ : _) (a₂ : _) (b₂ : _) (c₂ : _),
      φ₁ = φ₂ → ψ₁ = ψ₂ → pt S' s φ₁ h₁ ψ₁ k₁ a₁ b₁ c₁ = pt S' s φ₂ h₂ ψ₂ k₂ a₂ b₂ c₂ := by
    intros S' _ s φ₁ φ₂ h₁ h₂ ψ₁ ψ₂ k₁ k₂ a₁ b₁ c₁ a₂ b₂ c₂ e₁ e₂
    subst e₁; subst e₂; rfl
  refine ⟨X, πX, hlfp, hsep,
    fun T _ _ E' A' gE hgE gA hgA φ φ' hφ hp =>
      pt T (Spec.map (CommRingCat.ofHom (algebraMap S T)))
        ((presIso E E' gE hgE).inv ≫ φ ≫ gA) (trh_over E A E' A' gE hgE gA hgA φ hφ)
        ((presIso A A' gA hgA).inv ≫ φ' ≫ gE) (trh_over A E A' E' gA hgA gE hgE φ' hp.snd.fst)
        (isHom_transport E A E' A' gE hgE gA hgA (presIso E E' gE hgE) (presIso_hom_fst E E' gE hgE) (presIso_hom_snd E E' gE hgE)
          φ hφ hp.snd.snd.1 (trh_over E A E' A' gE hgE gA hgA φ hφ))
        (isHom_transport A E A' E' gA hgA gE hgE (presIso A A' gA hgA) (presIso_hom_fst A A' gA hgA) (presIso_hom_snd A A' gA hgA)
          φ' hp.snd.fst hp.snd.snd.2.1 (trh_over A E A' E' gA hgA gE hgE φ' hp.snd.fst))
        ⟨fun i => lin_transport E A E' A' gE hgE gA hgA (presIso E E' gE hgE) (presIso_hom_fst E E' gE hgE) (presIso_hom_snd E E' gE hgE)
            φ (β i) (hp.snd.snd.2.2.1 (β i)),
         fun i => lin_transport A E A' E' gA hgA gE hgE (presIso A A' gA hgA) (presIso_hom_fst A A' gA hgA) (presIso_hom_snd A A' gA hgA)
            φ' (β i) (hp.snd.snd.2.2.2.1 (β i)),
         fun hd => ⟨deg_transport E A E' A' gE hgE gA hgA (presIso E E' gE hgE) (presIso_hom_fst E E' gE hgE) (presIso_hom_snd E E' gE hgE)
              (presIso A A' gA hgA) (presIso_hom_fst A A' gA hgA) (presIso_hom_snd A A' gA hgA)
              φ hφ φ' ⟨_, hd⟩ (hp.snd.snd.2.2.2.2 hd).1 (trh_over E A E' A' gE hgE gA hgA φ hφ),
            deg_transport A E A' E' gA hgA gE hgE (presIso A A' gA hgA) (presIso_hom_fst A A' gA hgA) (presIso_hom_snd A A' gA hgA)
              (presIso E E' gE hgE) (presIso_hom_fst E E' gE hgE) (presIso_hom_snd E E' gE hgE)
              φ' hp.snd.fst φ ⟨_, hd⟩ (hp.snd.snd.2.2.2.2 hd).2 (trh_over A E A' E' gA hgA gE hgE φ' hp.snd.fst)⟩⟩,
    ?_, ?_, ?_, ?_⟩
  ·
    intro T _ _ E' A' gE hgE gA hgA φ φ' hφ hp E'' A'' gE'' hgE'' gA'' hgA'' ψ ψ' hψ hq iE hiE iA hiA hviaE hviaA hgiE hgiA hcomm hcomm'
    apply ptcongr
    · rw [← presIso_inv_comp_iso E E' E'' gE hgE gE'' hgE'' iE hiE hgiE, Category.assoc, ← Category.assoc iE.hom, hcomm,
        Category.assoc, hgiA]
    · rw [← presIso_inv_comp_iso A A' A'' gA hgA gA'' hgA'' iA hiA hgiA, Category.assoc, ← Category.assoc iA.hom, hcomm',
        Category.assoc, hgiE]
  ·
    intro T T' _ _ _ _ f E' A' gE hgE gA hgA φ φ' hφ hp E'' A'' hE hhE hA hhA hgE'' hgA'' ψ ψ' hψ hq hψA hψE
    have hs : Spec.map (CommRingCat.ofHom (f : T →+* T')) ≫ Spec.map (CommRingCat.ofHom (algebraMap S T)) =
        Spec.map (CommRingCat.ofHom (algebraMap S T')) := by
      rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, f.comp_algebraMap]
    refine hnat T T' (f : T →+* T') _ _ hs _ _ _ _ _ _ _ _ _ _ _ _ _ _ ?_ ?_
    · simp only [← Category.assoc]
      rw [← presIso_baseChange E f E' gE hgE E'' hE hhE hgE'' hs]
      simp only [Category.assoc]
      rw [← Category.assoc ψ hA gA, hψA, Category.assoc]
    · simp only [← Category.assoc]
      rw [← presIso_baseChange A f A' gA hgA A'' hA hhA hgA'' hs]
      simp only [Category.assoc]
      rw [← Category.assoc ψ' hE gE, hψE, Category.assoc]
  ·
    intro T _ _ E' A' gE hgE gA hgA z
    obtain ⟨φh, hφh, φh', hφh', k₁, k₂, k₃, hz⟩ := hsurj T (Spec.map (CommRingCat.ofHom (algebraMap S T))) z
    obtain ⟨φ, φ', hφ, hp, hφgA, hφ'gE⟩ := exists_isIsogenyPair_of_hom β hβ' r d E A E' A' gE hgE gA hgA
      (presIso E E' gE hgE) (presIso_hom_fst E E' gE hgE) (presIso_hom_snd E E' gE hgE)
      (presIso A A' gA hgA) (presIso_hom_fst A A' gA hgA) (presIso_hom_snd A A' gA hgA)
      φh hφh φh' hφh' k₁ k₂ k₃.1 k₃.2.1 k₃.2.2
    refine ⟨φ, φ', hφ, hp, ?_⟩
    rw [← hz]
    apply ptcongr
    · rw [hφgA, Iso.inv_hom_id_assoc]
    · rw [hφ'gE, Iso.inv_hom_id_assoc]
  ·
    intro T _ _ E' A' gE hgE gA hgA φ₁ φ₁' hφ₁ hp₁ φ₂ φ₂' hφ₂ hp₂ heq
    obtain ⟨h1, h2⟩ := hinj T (Spec.map (CommRingCat.ofHom (algebraMap S T))) _ _ _ _ _ _ _ _ _ _ _ _ _ _ heq
    constructor
    · apply hgA.fst.hom_ext
      · rw [← cancel_epi (presIso E E' gE hgE).inv]; simpa only [Category.assoc] using h1
      · rw [hφ₁, hφ₂]
    · apply hgE.fst.hom_ext
      · rw [← cancel_epi (presIso A A' gA hgA).inv]; simpa only [Category.assoc] using h2
      · rw [hp₁.snd.fst, hp₂.snd.fst]

end S_CerednikDrinfeld_QM_FakeEllipticCurve_exists_locallyOfFinitePresentation_isSeparated_represents_isIsogenyPair_of_closedImmersionBySections
end P2MW
export P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_exists_locallyOfFinitePresentation_isSeparated_represents_isIsogenyPair_of_closedImmersionBySections (solution)
