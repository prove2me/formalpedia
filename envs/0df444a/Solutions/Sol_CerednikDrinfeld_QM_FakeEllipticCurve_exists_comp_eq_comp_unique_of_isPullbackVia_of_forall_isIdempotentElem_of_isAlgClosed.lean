-- Prove2me | solution 1 for CerednikDrinfeld.QM.FakeEllipticCurve.exists_comp_eq_comp_unique_of_isPullbackVia_of_forall_isIdempotentElem_of_isAlgClosed
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.837917+00:00
-- url     : https://prove2.me/submissions/3da2b5c0-fb96-56f4-bb72-60e3f7296d48

import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_ModulesProjPresentation
import Definitions.Def_CerednikDrinfeld_QMFormalModuleOf
import Definitions.Def_CerednikDrinfeld_QMIsogeny

import Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_exists_homScheme_represents_of_closedImmersionBySections_lfp
import Theorems.Thm_AlgebraicGeometry_exists_eq_specMap_comp_of_formallyUnramified_of_forall_isIdempotentElem_of_isAlgClosed
import Theorems.Thm_AlgebraicGeometry_FormallyUnramified_eq_of_comp_eq_of_surjective_of_locallyOfFiniteType
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_exists_comp_eq_comp_unique_of_isPullbackVia_of_forall_isIdempotentElem_of_isAlgClosed
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

open CategoryTheory AlgebraicGeometry NeronModelInfra GoodReductionJacobian QuaternionAlgebra CerednikDrinfeld CerednikDrinfeld.QM
open scoped Quaternion

open CategoryTheory.Limits

theorem solution
    {N : ℕ} {a b : ℚ} (Λ : Submodule ℤ ℍ[ℚ, a, b])
    (k₀ : Type) [Field k₀] [IsAlgClosed k₀] (A₀ : FakeEllipticCurve Λ N k₀)

    (𝓛 : A₀.A.Modules) (h𝓛₁ : Scheme.Modules.IsInvertible 𝓛) (h𝓛₂ : Scheme.Modules.ClosedImmersionBySections 𝓛 A₀.f)
    (Bb : Type) [CommRing Bb] [Nontrivial Bb] (ψb : k₀ →+* Bb) (hBb : ∀ x : Bb, IsIdempotentElem x → x = 0 ∨ x = 1)
    (Ab : FakeEllipticCurve Λ N Bb) (gA : Ab.A ⟶ A₀.A) (hAb : FakeEllipticCurve.IsPullbackVia ψb A₀ Ab gA)
    (φ : Ab.A ⟶ Ab.A) (hφ : φ ≫ Ab.f = Ab.f)
    (hφhom : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of Bb)) (P Q : SchemeHomOver t Ab.f),
      mapPt φ hφ (Ab.L.mul t P Q) = Ab.L.mul t (mapPt φ hφ P) (mapPt φ hφ Q)) :
    ∃ (φ₀ : A₀.A ⟶ A₀.A) (hφ₀ : φ₀ ≫ A₀.f = A₀.f),
      (∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of k₀)) (P Q : SchemeHomOver t A₀.f),
        mapPt φ₀ hφ₀ (A₀.L.mul t P Q) = A₀.L.mul t (mapPt φ₀ hφ₀ P) (mapPt φ₀ hφ₀ Q)) ∧
      φ ≫ gA = gA ≫ φ₀ ∧
      ∀ (φ₀' : A₀.A ⟶ A₀.A) (hφ₀' : φ₀' ≫ A₀.f = A₀.f),
        (∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of k₀)) (P Q : SchemeHomOver t A₀.f),
          mapPt φ₀' hφ₀' (A₀.L.mul t P Q) = A₀.L.mul t (mapPt φ₀' hφ₀' P) (mapPt φ₀' hφ₀' Q)) →
        φ ≫ gA = gA ≫ φ₀' → φ₀' = φ₀ := by
  classical

  obtain ⟨H, πH, pt, hnat, hsurj, hinj, -, hlft, -, hunr⟩ :=
    GoodReductionJacobian.RelativeGroupLaw.exists_homScheme_represents_of_closedImmersionBySections_lfp k₀ A₀.f A₀.f
      A₀.L A₀.L A₀.comm A₀.comm A₀.bundle A₀.bundle 𝓛 h𝓛₁ h𝓛₂ 𝓛 h𝓛₁ h𝓛₂
  haveI := hlft
  haveI := hunr

  obtain ⟨hsq, hmul, -, -⟩ := hAb
  let κ : Ab.A ≅ pullback A₀.f (Spec.map (CommRingCat.ofHom ψb)) := hsq.isoPullback
  have hκ₁ : κ.hom ≫ pullback.fst A₀.f (Spec.map (CommRingCat.ofHom ψb)) = gA := hsq.isoPullback_hom_fst
  have hκ₂ : κ.hom ≫ pullback.snd A₀.f (Spec.map (CommRingCat.ofHom ψb)) = Ab.f := hsq.isoPullback_hom_snd
  have hκ₁' : κ.inv ≫ gA = pullback.fst A₀.f (Spec.map (CommRingCat.ofHom ψb)) := by rw [← hκ₁, Iso.inv_hom_id_assoc]
  have hκ₂' : κ.inv ≫ Ab.f = pullback.snd A₀.f (Spec.map (CommRingCat.ofHom ψb)) := by rw [← hκ₂, Iso.inv_hom_id_assoc]

  have castPt : ∀ {T : Scheme.{0}} {t₁ t₂ : T ⟶ Spec (CommRingCat.of k₀)} (e : t₁ = t₂) (P Q : SchemeHomOver t₁ A₀.f),
      (A₀.L.mul t₁ P Q).1 = (A₀.L.mul t₂ ⟨P.1, P.2.trans e⟩ ⟨Q.1, Q.2.trans e⟩).1 := by
    intro T t₁ t₂ e P Q; subst e; rfl

  let Φ : pullback A₀.f (Spec.map (CommRingCat.ofHom ψb)) ⟶ A₀.A := κ.inv ≫ φ ≫ gA
  have hΦ : Φ ≫ A₀.f = pullback.snd A₀.f (Spec.map (CommRingCat.ofHom ψb)) ≫ (Spec.map (CommRingCat.ofHom ψb)) := by
    simp only [Φ, Category.assoc]
    rw [hsq.w, ← Category.assoc φ, hφ, ← Category.assoc, hκ₂']

  have ptAb : ∀ {T : Scheme.{0}} (t' : T ⟶ Spec (CommRingCat.of Bb)) (P : SchemeHomOver (t' ≫ (Spec.map (CommRingCat.ofHom ψb))) A₀.f),
      (pullback.lift P.1 t' P.2 ≫ κ.inv) ≫ Ab.f = t' := by
    intro T t' P; rw [Category.assoc, hκ₂', pullback.lift_snd]
  have hΦhom : ∀ (T : Scheme.{0}) (t' : T ⟶ Spec (CommRingCat.of Bb)) (P Q : SchemeHomOver (t' ≫ (Spec.map (CommRingCat.ofHom ψb))) A₀.f),
      pullback.lift (A₀.L.mul (t' ≫ (Spec.map (CommRingCat.ofHom ψb))) P Q).1 t' (A₀.L.mul (t' ≫ (Spec.map (CommRingCat.ofHom ψb))) P Q).2 ≫ Φ =
        (A₀.L.mul (t' ≫ (Spec.map (CommRingCat.ofHom ψb)))
          ⟨pullback.lift P.1 t' P.2 ≫ Φ, by rw [Category.assoc, hΦ, ← Category.assoc, pullback.lift_snd]⟩
          ⟨pullback.lift Q.1 t' Q.2 ≫ Φ, by rw [Category.assoc, hΦ, ← Category.assoc, pullback.lift_snd]⟩).1 := by
    intro T t' P Q
    let P' : SchemeHomOver t' Ab.f := ⟨pullback.lift P.1 t' P.2 ≫ κ.inv, ptAb t' P⟩
    let Q' : SchemeHomOver t' Ab.f := ⟨pullback.lift Q.1 t' Q.2 ≫ κ.inv, ptAb t' Q⟩

    have hPg : P'.1 ≫ gA = P.1 := by show (pullback.lift P.1 t' P.2 ≫ κ.inv) ≫ gA = P.1; rw [Category.assoc, hκ₁', pullback.lift_fst]
    have hQg : Q'.1 ≫ gA = Q.1 := by show (pullback.lift Q.1 t' Q.2 ≫ κ.inv) ≫ gA = Q.1; rw [Category.assoc, hκ₁', pullback.lift_fst]
    have hm := hmul t' P' Q'
    have hPQ : (A₀.L.mul (t' ≫ Spec.map (CommRingCat.ofHom ψb))
        ⟨P'.1 ≫ gA, by rw [Category.assoc, hsq.w, ← Category.assoc, P'.2]⟩
        ⟨Q'.1 ≫ gA, by rw [Category.assoc, hsq.w, ← Category.assoc, Q'.2]⟩).1 = (A₀.L.mul (t' ≫ (Spec.map (CommRingCat.ofHom ψb))) P Q).1 := by
      congr 2 <;> apply Subtype.ext <;> assumption
    rw [hPQ] at hm
    have hprod : pullback.lift (A₀.L.mul (t' ≫ (Spec.map (CommRingCat.ofHom ψb))) P Q).1 t' (A₀.L.mul (t' ≫ (Spec.map (CommRingCat.ofHom ψb))) P Q).2 ≫ κ.inv = (Ab.L.mul t' P' Q').1 := by
      rw [← cancel_mono κ.hom, Category.assoc, Iso.inv_hom_id, Category.comp_id]
      apply pullback.hom_ext
      · rw [pullback.lift_fst, Category.assoc, hκ₁, hm]
      · rw [pullback.lift_snd, Category.assoc, hκ₂, (Ab.L.mul t' P' Q').2]

    have lhs : pullback.lift (A₀.L.mul (t' ≫ (Spec.map (CommRingCat.ofHom ψb))) P Q).1 t' (A₀.L.mul (t' ≫ (Spec.map (CommRingCat.ofHom ψb))) P Q).2 ≫ Φ =
        (mapPt φ hφ (Ab.L.mul t' P' Q')).1 ≫ gA := by
      show _ ≫ (κ.inv ≫ φ ≫ gA) = _
      rw [← Category.assoc, ← Category.assoc, hprod, mapPt_coe, Category.assoc]
    rw [lhs, hφhom t' P' Q', hmul t']
    congr 2

  let x := pt Bb (Spec.map (CommRingCat.ofHom ψb)) Φ hΦ
  obtain ⟨h, hh₁, hh₂⟩ :=
    AlgebraicGeometry.exists_eq_specMap_comp_of_formallyUnramified_of_forall_isIdempotentElem_of_isAlgClosed
      πH Bb ψb hBb x.1 (by rw [x.2])

  obtain ⟨Φ₀, hΦ₀, hΦ₀hom, hpt₀⟩ := hsurj k₀ (𝟙 _) ⟨h, hh₁⟩

  let bc : pullback A₀.f (Spec.map (CommRingCat.ofHom ψb)) ⟶ pullback A₀.f (𝟙 (Spec (CommRingCat.of k₀))) :=
    pullback.lift (pullback.fst A₀.f (Spec.map (CommRingCat.ofHom ψb))) (pullback.snd A₀.f (Spec.map (CommRingCat.ofHom ψb)) ≫ Spec.map (CommRingCat.ofHom ψb))
      (by rw [Category.assoc, Category.comp_id]; exact pullback.condition)
  have hnat₀ := hnat k₀ Bb ψb (𝟙 _) (Spec.map (CommRingCat.ofHom ψb)) (Category.comp_id _) Φ₀ hΦ₀
  have hΦ' : (bc ≫ Φ₀) ≫ A₀.f = pullback.snd A₀.f (Spec.map (CommRingCat.ofHom ψb)) ≫ (Spec.map (CommRingCat.ofHom ψb)) := by
    rw [Category.assoc, hΦ₀, ← Category.assoc, pullback.lift_snd, Category.comp_id]

  have hbcP : ∀ {T : Scheme.{0}} (t' : T ⟶ Spec (CommRingCat.of Bb)) (P : SchemeHomOver (t' ≫ (Spec.map (CommRingCat.ofHom ψb))) A₀.f),
      pullback.lift P.1 t' P.2 ≫ bc = pullback.lift P.1 (t' ≫ (Spec.map (CommRingCat.ofHom ψb)))
        (by rw [Category.assoc, Category.comp_id]; exact P.2) := by
    intro T t' P
    apply pullback.hom_ext
    · rw [Category.assoc, pullback.lift_fst, pullback.lift_fst, pullback.lift_fst]
    · rw [Category.assoc, pullback.lift_snd, pullback.lift_snd, ← Category.assoc, pullback.lift_snd]
  have hΦ'hom : ∀ (T : Scheme.{0}) (t' : T ⟶ Spec (CommRingCat.of Bb)) (P Q : SchemeHomOver (t' ≫ (Spec.map (CommRingCat.ofHom ψb))) A₀.f),
      pullback.lift (A₀.L.mul (t' ≫ (Spec.map (CommRingCat.ofHom ψb))) P Q).1 t' (A₀.L.mul (t' ≫ (Spec.map (CommRingCat.ofHom ψb))) P Q).2 ≫ (bc ≫ Φ₀) =
        (A₀.L.mul (t' ≫ (Spec.map (CommRingCat.ofHom ψb)))
          ⟨pullback.lift P.1 t' P.2 ≫ (bc ≫ Φ₀), by rw [Category.assoc, hΦ', ← Category.assoc, pullback.lift_snd]⟩
          ⟨pullback.lift Q.1 t' Q.2 ≫ (bc ≫ Φ₀), by rw [Category.assoc, hΦ', ← Category.assoc, pullback.lift_snd]⟩).1 := by
    intro T t' P Q
    have e : t' ≫ (Spec.map (CommRingCat.ofHom ψb)) = (t' ≫ (Spec.map (CommRingCat.ofHom ψb))) ≫ 𝟙 _ := (Category.comp_id _).symm
    let P₁ : SchemeHomOver ((t' ≫ (Spec.map (CommRingCat.ofHom ψb))) ≫ 𝟙 _) A₀.f := ⟨P.1, P.2.trans e⟩
    let Q₁ : SchemeHomOver ((t' ≫ (Spec.map (CommRingCat.ofHom ψb))) ≫ 𝟙 _) A₀.f := ⟨Q.1, Q.2.trans e⟩
    have h0 := hΦ₀hom T (t' ≫ (Spec.map (CommRingCat.ofHom ψb))) P₁ Q₁
    have m1 : (A₀.L.mul (t' ≫ (Spec.map (CommRingCat.ofHom ψb))) P Q).1 = (A₀.L.mul ((t' ≫ (Spec.map (CommRingCat.ofHom ψb))) ≫ 𝟙 _) P₁ Q₁).1 := castPt e P Q
    rw [← Category.assoc, show pullback.lift (A₀.L.mul (t' ≫ (Spec.map (CommRingCat.ofHom ψb))) P Q).1 t' (A₀.L.mul (t' ≫ (Spec.map (CommRingCat.ofHom ψb))) P Q).2 ≫ bc =
        pullback.lift (A₀.L.mul ((t' ≫ (Spec.map (CommRingCat.ofHom ψb))) ≫ 𝟙 _) P₁ Q₁).1 (t' ≫ (Spec.map (CommRingCat.ofHom ψb))) (A₀.L.mul ((t' ≫ (Spec.map (CommRingCat.ofHom ψb))) ≫ 𝟙 _) P₁ Q₁).2 from by
          apply pullback.hom_ext
          · rw [Category.assoc, pullback.lift_fst, pullback.lift_fst, pullback.lift_fst, m1]
          · rw [Category.assoc, pullback.lift_snd, pullback.lift_snd, ← Category.assoc, pullback.lift_snd],
      h0, castPt e]
    congr 2 <;> apply Subtype.ext
    · show pullback.lift P₁.1 (t' ≫ (Spec.map (CommRingCat.ofHom ψb))) P₁.2 ≫ Φ₀ = pullback.lift P.1 t' P.2 ≫ bc ≫ Φ₀
      rw [← Category.assoc, hbcP]
    · show pullback.lift Q₁.1 (t' ≫ (Spec.map (CommRingCat.ofHom ψb))) Q₁.2 ≫ Φ₀ = pullback.lift Q.1 t' Q.2 ≫ bc ≫ Φ₀
      rw [← Category.assoc, hbcP]
  have hpteq : pt Bb (Spec.map (CommRingCat.ofHom ψb)) (bc ≫ Φ₀) hΦ' = pt Bb (Spec.map (CommRingCat.ofHom ψb)) Φ hΦ := by
    apply Subtype.ext
    have := hnat₀
    rw [hpt₀] at this
    change (pt Bb (Spec.map (CommRingCat.ofHom ψb)) (bc ≫ Φ₀) _).1 = Spec.map (CommRingCat.ofHom ψb) ≫ h at this
    rw [this, ← hh₂]
  have hΦeq : bc ≫ Φ₀ = Φ := hinj Bb (Spec.map (CommRingCat.ofHom ψb)) (bc ≫ Φ₀) Φ hΦ' hΦ hΦ'hom hΦhom hpteq

  let j : A₀.A ⟶ pullback A₀.f (𝟙 (Spec (CommRingCat.of k₀))) := pullback.lift (𝟙 _) A₀.f (by simp)
  have hj₁ : j ≫ pullback.fst A₀.f (𝟙 _) = 𝟙 _ := pullback.lift_fst _ _ _
  have hj₂ : j ≫ pullback.snd A₀.f (𝟙 _) = A₀.f := pullback.lift_snd _ _ _
  have hfst_j : pullback.fst A₀.f (𝟙 (Spec (CommRingCat.of k₀))) ≫ j = 𝟙 _ := by
    apply pullback.hom_ext
    · rw [Category.assoc, hj₁, Category.comp_id, Category.id_comp]
    · rw [Category.assoc, hj₂, Category.id_comp, pullback.condition, Category.comp_id]
  let φ₀ : A₀.A ⟶ A₀.A := j ≫ Φ₀
  have hφ₀ : φ₀ ≫ A₀.f = A₀.f := by
    show (j ≫ Φ₀) ≫ A₀.f = A₀.f
    rw [Category.assoc, hΦ₀, ← Category.assoc, hj₂, Category.comp_id]
  have hbc_j : κ.hom ≫ bc = gA ≫ j := by
    apply pullback.hom_ext
    · rw [Category.assoc, pullback.lift_fst, hκ₁, Category.assoc, hj₁, Category.comp_id]
    · rw [Category.assoc, pullback.lift_snd, ← Category.assoc, hκ₂, Category.assoc, hj₂, hsq.w]
  have hcomm : φ ≫ gA = gA ≫ φ₀ := by
    have := congrArg (fun m => κ.hom ≫ m) hΦeq
    simp only [Φ, Iso.hom_inv_id_assoc] at this
    rw [← this, ← Category.assoc, hbc_j, Category.assoc]

  have hφ₀hom : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of k₀)) (P Q : SchemeHomOver t A₀.f),
      mapPt φ₀ hφ₀ (A₀.L.mul t P Q) = A₀.L.mul t (mapPt φ₀ hφ₀ P) (mapPt φ₀ hφ₀ Q) := by
    intro T t P Q
    have e : t = t ≫ 𝟙 _ := (Category.comp_id _).symm
    let P₁ : SchemeHomOver (t ≫ 𝟙 _) A₀.f := ⟨P.1, P.2.trans e⟩
    let Q₁ : SchemeHomOver (t ≫ 𝟙 _) A₀.f := ⟨Q.1, Q.2.trans e⟩
    have h0 := hΦ₀hom T t P₁ Q₁
    have hl : ∀ (R : SchemeHomOver (t ≫ 𝟙 _) A₀.f), pullback.lift R.1 t R.2 = R.1 ≫ j := by
      intro R; apply pullback.hom_ext
      · rw [pullback.lift_fst, Category.assoc, hj₁]; exact (Category.comp_id _).symm
      · rw [pullback.lift_snd, Category.assoc, hj₂]; exact (R.2.trans (Category.comp_id _)).symm
    apply Subtype.ext
    rw [mapPt_coe, castPt e, castPt e]
    show (A₀.L.mul (t ≫ 𝟙 _) P₁ Q₁).1 ≫ j ≫ Φ₀ = _
    rw [← Category.assoc, ← hl, h0]
    congr 2 <;> apply Subtype.ext
    · show pullback.lift P₁.1 t P₁.2 ≫ Φ₀ = P.1 ≫ j ≫ Φ₀; rw [hl, Category.assoc]
    · show pullback.lift Q₁.1 t Q₁.2 ≫ Φ₀ = Q.1 ≫ j ≫ Φ₀; rw [hl, Category.assoc]
  refine ⟨φ₀, hφ₀, hφ₀hom, hcomm, ?_⟩

  intro φ₀' hφ₀' hφ₀'hom hcomm'
  let Φ₀' : pullback A₀.f (𝟙 (Spec (CommRingCat.of k₀))) ⟶ A₀.A := pullback.fst A₀.f (𝟙 _) ≫ φ₀'
  have hΦ₀' : Φ₀' ≫ A₀.f = pullback.snd A₀.f (𝟙 _) ≫ 𝟙 _ := by
    show (pullback.fst A₀.f (𝟙 _) ≫ φ₀') ≫ A₀.f = _
    rw [Category.assoc, hφ₀', pullback.condition]
  have hΦ₀'hom : ∀ (T : Scheme.{0}) (t' : T ⟶ Spec (CommRingCat.of k₀)) (P Q : SchemeHomOver (t' ≫ 𝟙 _) A₀.f),
      pullback.lift (A₀.L.mul (t' ≫ 𝟙 _) P Q).1 t' (A₀.L.mul (t' ≫ 𝟙 _) P Q).2 ≫ Φ₀' =
        (A₀.L.mul (t' ≫ 𝟙 _)
          ⟨pullback.lift P.1 t' P.2 ≫ Φ₀', by rw [Category.assoc, hΦ₀', ← Category.assoc, pullback.lift_snd]⟩
          ⟨pullback.lift Q.1 t' Q.2 ≫ Φ₀', by rw [Category.assoc, hΦ₀', ← Category.assoc, pullback.lift_snd]⟩).1 := by
    intro T t' P Q
    have e : t' ≫ 𝟙 _ = t' := Category.comp_id _
    let P₁ : SchemeHomOver t' A₀.f := ⟨P.1, P.2.trans e⟩
    let Q₁ : SchemeHomOver t' A₀.f := ⟨Q.1, Q.2.trans e⟩
    have h0 := congrArg Subtype.val (hφ₀'hom t' P₁ Q₁)
    rw [mapPt_coe] at h0
    show pullback.lift _ t' _ ≫ pullback.fst A₀.f (𝟙 _) ≫ φ₀' = _
    rw [← Category.assoc, pullback.lift_fst, castPt e, h0, castPt e.symm]
    congr 2 <;> apply Subtype.ext
    · show (P₁.1 ≫ φ₀') = pullback.lift P.1 t' P.2 ≫ pullback.fst A₀.f (𝟙 _) ≫ φ₀'
      rw [← Category.assoc, pullback.lift_fst]
    · show (Q₁.1 ≫ φ₀') = pullback.lift Q.1 t' Q.2 ≫ pullback.fst A₀.f (𝟙 _) ≫ φ₀'
      rw [← Category.assoc, pullback.lift_fst]
  let h' := pt k₀ (𝟙 _) Φ₀' hΦ₀'
  have hnat' := hnat k₀ Bb ψb (𝟙 _) (Spec.map (CommRingCat.ofHom ψb)) (Category.comp_id _) Φ₀' hΦ₀'

  have hbcΦ' : bc ≫ Φ₀' = Φ := by
    show bc ≫ pullback.fst A₀.f (𝟙 _) ≫ φ₀' = κ.inv ≫ φ ≫ gA
    rw [← Category.assoc, pullback.lift_fst, hcomm', ← Category.assoc, hκ₁']
  have hx' : (pt Bb (Spec.map (CommRingCat.ofHom ψb)) Φ hΦ).1 = (Spec.map (CommRingCat.ofHom ψb)) ≫ h'.1 := by
    have := hnat'
    have ee : ∀ (a b : pullback A₀.f (Spec.map (CommRingCat.ofHom ψb)) ⟶ A₀.A) (ha : a ≫ A₀.f = pullback.snd A₀.f (Spec.map (CommRingCat.ofHom ψb)) ≫ (Spec.map (CommRingCat.ofHom ψb)))
        (hb : b ≫ A₀.f = pullback.snd A₀.f (Spec.map (CommRingCat.ofHom ψb)) ≫ (Spec.map (CommRingCat.ofHom ψb))), a = b → (pt Bb (Spec.map (CommRingCat.ofHom ψb)) a ha).1 = (pt Bb (Spec.map (CommRingCat.ofHom ψb)) b hb).1 := by
      intro a b ha hb hab; subst hab; rfl
    rw [ee _ Φ _ hΦ hbcΦ'] at this
    rw [this]

  haveI : AlgebraicGeometry.Surjective (Spec.map (CommRingCat.ofHom ψb)) := by
    refine ⟨fun y => ?_⟩
    obtain ⟨m, hm⟩ := Ideal.exists_maximal Bb
    refine ⟨⟨m, hm.isPrime⟩, ?_⟩
    haveI := PrimeSpectrum.instUnique (R := k₀)
    exact Subsingleton.elim _ _
  have hhh : h'.1 = h :=
    AlgebraicGeometry.FormallyUnramified.eq_of_comp_eq_of_surjective_of_locallyOfFiniteType πH (Spec.map (CommRingCat.ofHom ψb)) h'.1 h
      (by rw [h'.2, hh₁]) (by rw [← hx', ← hh₂])
  have hpt' : pt k₀ (𝟙 _) Φ₀' hΦ₀' = pt k₀ (𝟙 _) Φ₀ hΦ₀ := by
    rw [hpt₀]; apply Subtype.ext; exact hhh
  have hΦ₀eq : Φ₀' = Φ₀ := hinj k₀ (𝟙 _) Φ₀' Φ₀ hΦ₀' hΦ₀ hΦ₀'hom hΦ₀hom hpt'
  show φ₀' = j ≫ Φ₀
  rw [← hΦ₀eq, show j ≫ Φ₀' = (j ≫ pullback.fst A₀.f (𝟙 _)) ≫ φ₀' from (Category.assoc _ _ _).symm, hj₁, Category.id_comp]

end S_CerednikDrinfeld_QM_FakeEllipticCurve_exists_comp_eq_comp_unique_of_isPullbackVia_of_forall_isIdempotentElem_of_isAlgClosed
end P2MW
export P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_exists_comp_eq_comp_unique_of_isPullbackVia_of_forall_isIdempotentElem_of_isAlgClosed (solution)
