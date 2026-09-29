-- Prove2me | solution 1 for CerednikDrinfeld.QM.FakeEllipticCurve.exists_comp_act_comp_eq_of_isPullbackVia_of_forall_isIdempotentElem_of_closedImmersionBySections_of_isAlgClosed
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.837917+00:00
-- url     : https://prove2.me/submissions/35eed7b6-a536-5024-8790-3df358813112

import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_ModulesProjPresentation
import Definitions.Def_CerednikDrinfeld_QMFormalModuleOf
import Definitions.Def_CerednikDrinfeld_QMIsogeny
import Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_exists_comp_eq_comp_unique_of_isPullbackVia_of_forall_isIdempotentElem_of_isAlgClosed
import Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_isIsogenyPair_of_isIsogenyPair_of_comp_eq_comp_of_isPullbackVia
import Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_preservesLevel_of_preservesLevel_of_comp_eq_comp_of_isPullbackVia
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_exists_comp_act_comp_eq_of_isPullbackVia_of_forall_isIdempotentElem_of_closedImmersionBySections_of_isAlgClosed
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

namespace BRAsm

open CerednikDrinfeld.QM.FakeEllipticCurve

variable {N : ℕ} {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} {k₀ : Type} [Field k₀] {Bb : Type} [CommRing Bb]

theorem exists_bc (A₀ : FakeEllipticCurve Λ N k₀) (ψb : k₀ →+* Bb) (Ab : FakeEllipticCurve Λ N Bb) (gA : Ab.A ⟶ A₀.A)
    (hAb : FakeEllipticCurve.IsPullbackVia ψb A₀ Ab gA)
    (χ : A₀.A ⟶ A₀.A) (hχ : χ ≫ A₀.f = A₀.f)
    (hχhom : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of k₀)) (P Q : SchemeHomOver t A₀.f),
      mapPt χ hχ (A₀.L.mul t P Q) = A₀.L.mul t (mapPt χ hχ P) (mapPt χ hχ Q)) :
    ∃ (χb : Ab.A ⟶ Ab.A) (hχb : χb ≫ Ab.f = Ab.f),
      (∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of Bb)) (P Q : SchemeHomOver t Ab.f),
        mapPt χb hχb (Ab.L.mul t P Q) = Ab.L.mul t (mapPt χb hχb P) (mapPt χb hχb Q)) ∧
      χb ≫ gA = gA ≫ χ := by
  obtain ⟨hg, hmul, -, -⟩ := hAb
  have w : (gA ≫ χ) ≫ A₀.f = Ab.f ≫ Spec.map (CommRingCat.ofHom ψb) := by
    rw [Category.assoc, hχ]; exact hg.w
  refine ⟨hg.lift (gA ≫ χ) Ab.f w, hg.lift_snd _ _ w, ?_, hg.lift_fst _ _ w⟩
  intro T t P Q
  apply Subtype.ext
  apply hg.hom_ext
  ·
    rw [mapPt_coe, Category.assoc, hg.lift_fst, hmul, ← Category.assoc, hmul]
    have h1 := congrArg Subtype.val (hχhom (t ≫ Spec.map (CommRingCat.ofHom ψb))
      ⟨P.1 ≫ gA, by rw [Category.assoc, hg.w, ← Category.assoc, P.2]⟩
      ⟨Q.1 ≫ gA, by rw [Category.assoc, hg.w, ← Category.assoc, Q.2]⟩)
    rw [mapPt_coe] at h1
    rw [h1]
    congr 2 <;> apply Subtype.ext <;> simp only [mapPt_coe, Category.assoc, hg.lift_fst]
  · rw [mapPt_coe, Category.assoc, hg.lift_snd, (Ab.L.mul t P Q).2, (Ab.L.mul t _ _).2]

end BRAsm

open BRAsm in
theorem solution
    {r N : ℕ} {a b : ℚ} (Λ : Submodule ℤ ℍ[ℚ, a, b]) (hΛℤ : ∀ m : ℤ, ((m : ℚ) : ℍ[ℚ, a, b]) ∈ Λ)
    (k₀ : Type) [Field k₀] [IsAlgClosed k₀] (A₀ : FakeEllipticCurve Λ N k₀)

    (𝓛 : A₀.A.Modules) (h𝓛₁ : Scheme.Modules.IsInvertible 𝓛) (h𝓛₂ : Scheme.Modules.ClosedImmersionBySections 𝓛 A₀.f)

    {a₁ b₁ : ℚ} (Γt : Subgroup (ℍ[ℚ, a₁, b₁])ˣ)
    (e e' : ↥Γt → (A₀.A ⟶ A₀.A)) (he : ∀ γ, e γ ≫ A₀.f = A₀.f) (deg : ↥Γt → ℕ)
    (hE1 : ∀ γ : ↥Γt, FakeEllipticCurve.IsIsogenyPair (r ^ deg γ) A₀ A₀ (e γ) (e' γ) ∧ FakeEllipticCurve.PreservesLevel A₀ A₀ (e γ) (he γ))

    (hE4₀ : ∀ (φ ψ : A₀.A ⟶ A₀.A) (d : ℕ) (hφ : φ ≫ A₀.f = A₀.f),
        FakeEllipticCurve.IsIsogenyPair (r ^ d) A₀ A₀ φ ψ → FakeEllipticCurve.PreservesLevel A₀ A₀ φ hφ →
        ∃ (γ : ↥Γt) (i j : ℕ), φ ≫ A₀.act ⟨(((r ^ i : ℕ) : ℤ) : ℚ), hΛℤ _⟩ = e γ ≫ A₀.act ⟨(((r ^ j : ℕ) : ℤ) : ℚ), hΛℤ _⟩) :
    ∀ (Bb : Type) [CommRing Bb] (ψb : k₀ →+* Bb)
      (Ab : FakeEllipticCurve Λ N Bb) (gA : Ab.A ⟶ A₀.A) (hAb : FakeEllipticCurve.IsPullbackVia ψb A₀ Ab gA),
      ∀ (φ ψ : Ab.A ⟶ Ab.A) (d : ℕ) (hφ : φ ≫ Ab.f = Ab.f),
        FakeEllipticCurve.IsIsogenyPair (r ^ d) Ab Ab φ ψ → FakeEllipticCurve.PreservesLevel Ab Ab φ hφ →
        (∀ x : Bb, IsIdempotentElem x → x = 0 ∨ x = 1) →
        ∃ (γ : ↥Γt) (i j : ℕ), φ ≫ Ab.act ⟨(((r ^ i : ℕ) : ℤ) : ℚ), hΛℤ _⟩ ≫ gA = gA ≫ e γ ≫ A₀.act ⟨(((r ^ j : ℕ) : ℤ) : ℚ), hΛℤ _⟩ := by
  intro Bb _ ψb Ab gA hAb φ ψ d hφ hpair hlev hBb
  classical
  by_cases hnt : Nontrivial Bb
  swap
  ·
    rw [not_nontrivial_iff_subsingleton] at hnt
    haveI := hnt
    haveI : IsEmpty ↥(Spec (CommRingCat.of Bb)) := (inferInstance : IsEmpty (PrimeSpectrum Bb))
    haveI : IsEmpty ↥Ab.A := Function.isEmpty Ab.f.base
    exact ⟨1, 0, 0, (isInitialOfIsEmpty (X := Ab.A)).hom_ext _ _⟩

  obtain ⟨hφ', hψ', φhom, ψhom, φact, ψact, hcomp⟩ := hpair

  obtain ⟨φ₀, hφ₀, φ₀hom, hφg, huφ⟩ :=
    FakeEllipticCurve.exists_comp_eq_comp_unique_of_isPullbackVia_of_forall_isIdempotentElem_of_isAlgClosed
      Λ k₀ A₀ 𝓛 h𝓛₁ h𝓛₂ Bb ψb hBb Ab gA hAb φ hφ' φhom
  obtain ⟨ψ₀, hψ₀, ψ₀hom, hψg, -⟩ :=
    FakeEllipticCurve.exists_comp_eq_comp_unique_of_isPullbackVia_of_forall_isIdempotentElem_of_isAlgClosed
      Λ k₀ A₀ 𝓛 h𝓛₁ h𝓛₂ Bb ψb hBb Ab gA hAb ψ hψ' ψhom

  have huniq : ∀ (χ χ' : A₀.A ⟶ A₀.A) (hχ : χ ≫ A₀.f = A₀.f) (hχ' : χ' ≫ A₀.f = A₀.f),
      (∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of k₀)) (P Q : SchemeHomOver t A₀.f),
        mapPt χ hχ (A₀.L.mul t P Q) = A₀.L.mul t (mapPt χ hχ P) (mapPt χ hχ Q)) →
      (∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of k₀)) (P Q : SchemeHomOver t A₀.f),
        mapPt χ' hχ' (A₀.L.mul t P Q) = A₀.L.mul t (mapPt χ' hχ' P) (mapPt χ' hχ' Q)) →
      gA ≫ χ = gA ≫ χ' → χ = χ' := by
    intro χ χ' hχ hχ' hχhom hχ'hom hgg
    obtain ⟨χb, hχb, χbhom, hχbg⟩ := exists_bc A₀ ψb Ab gA hAb χ hχ hχhom
    obtain ⟨χ₀, hχ₀, -, -, hu⟩ :=
      FakeEllipticCurve.exists_comp_eq_comp_unique_of_isPullbackVia_of_forall_isIdempotentElem_of_isAlgClosed
        Λ k₀ A₀ 𝓛 h𝓛₁ h𝓛₂ Bb ψb hBb Ab gA hAb χb hχb χbhom
    have e1 : χ = χ₀ := hu χ hχ hχhom hχbg
    have e2 : χ' = χ₀ := hu χ' hχ' hχ'hom (hχbg.trans hgg)
    rw [e1, e2]

  have hpair₀ : FakeEllipticCurve.IsIsogenyPair (r ^ d) A₀ A₀ φ₀ ψ₀ :=
    FakeEllipticCurve.isIsogenyPair_of_isIsogenyPair_of_comp_eq_comp_of_isPullbackVia A₀ ψb Ab gA hAb huniq (r ^ d) φ ψ
      ⟨hφ', hψ', φhom, ψhom, φact, ψact, hcomp⟩ φ₀ ψ₀ hφ₀ hψ₀ φ₀hom ψ₀hom hφg hψg
  have hlev₀ : FakeEllipticCurve.PreservesLevel A₀ A₀ φ₀ hφ₀ :=
    FakeEllipticCurve.preservesLevel_of_preservesLevel_of_comp_eq_comp_of_isPullbackVia A₀ ψb Ab gA hAb φ hφ φ₀ hφ₀ hφg hlev

  obtain ⟨γ, i, j, hγ⟩ := hE4₀ φ₀ ψ₀ d hφ₀ hpair₀ hlev₀
  obtain ⟨-, -, hact, -⟩ := hAb
  refine ⟨γ, i, j, ?_⟩
  rw [hact, ← Category.assoc, hφg, Category.assoc, hγ]

end S_CerednikDrinfeld_QM_FakeEllipticCurve_exists_comp_act_comp_eq_of_isPullbackVia_of_forall_isIdempotentElem_of_closedImmersionBySections_of_isAlgClosed
end P2MW
export P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_exists_comp_act_comp_eq_of_isPullbackVia_of_forall_isIdempotentElem_of_closedImmersionBySections_of_isAlgClosed (solution)
