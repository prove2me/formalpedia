-- Prove2me | solution 1 for CerednikDrinfeld.QM.exists_transition_isPullback_of_represents_qmStructure_affineOpens_satisfying
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.141142+00:00
-- url     : https://prove2.me/submissions/7db1b8af-efc3-5438-a08c-22358e91f3b1

import Definitions.Def_CerednikDrinfeld_QMFineModuli
import Definitions.Def_CerednikDrinfeld_QMStructureOnPolarised
import Definitions.Def_AlgebraicGeometry_PolarisedAbelianSchemeOfType
import Theorems.Thm_AlgebraicGeometry_Scheme_exists_iso_over_of_forall_schemeHomOver_equiv
import Theorems.Thm_AlgebraicGeometry_PolarisedAbelianScheme_exists_isPullback
import Theorems.Thm_AlgebraicGeometry_PolarisedAbelianScheme_Iso_baseChange
import Theorems.Thm_AlgebraicGeometry_PolarisedAbelianScheme_IsPullback_trans
import Theorems.Thm_AlgebraicGeometry_PolarisedAbelianScheme_QMStructure_exists_iso_of_polarisedAbelianScheme_iso
import Theorems.Thm_AlgebraicGeometry_PolarisedAbelianScheme_QMStructure_ptZ_eq_of_iso_of_isPullback_of_isPullback
import Theorems.Thm_AlgebraicGeometry_PolarisedAbelianScheme_Iso_refl_symm_trans
import Theorems.Thm_AlgebraicGeometry_PolarisedAbelianScheme_QMStructure_Iso_refl_symm_trans
import Theorems.Thm_AlgebraicGeometry_PolarisedAbelianScheme_QMStructure_exists_isPullback
import Theorems.Thm_AlgebraicGeometry_PolarisedAbelianScheme_QMStructure_Iso_of_isPullback_of_isPullback__5e6a0e
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_QM_exists_transition_isPullback_of_represents_qmStructure_affineOpens_satisfying
p2m_attr_erase "instance" "PresheafOfModules.PullbackMonoidal.pullback_monoidal PresheafOfModules.PullbackMonoidal.isIso_δ PresheafOfModules.pushforward_laxMonoidal PresheafOfModules.PullbackMonoidal.isIso_η PresheafOfModules.free_monoidal PresheafOfModules.restrictScalars_laxMonoidal PresheafOfModules.PullbackMonoidal.isIso_δ_gS PresheafOfModules.pullback_oplaxMonoidal PresheafOfModules.PullbackMonoidal.instPreservesColimitsOfSizeCompOppositeCommRingCatRingCatForget₂RingHomCarrierCarrierPb PresheafOfModules.pullback_monoidal' AlgebraicGeometry.Scheme.Modules.preservesBinaryProducts_opensMap AlgebraicGeometry.Scheme.Modules.pullback_monoidal AlgebraicGeometry.Scheme.Modules.sheafify_isLocalization' AlgebraicGeometry.Scheme.Modules.preservesTerminal_opensMap AlgebraicGeometry.Scheme.Modules.pullback₀_monoidal AlgebraicGeometry.Scheme.Modules.preservesFiniteProducts_opensMap AlgebraicGeometry.Scheme.Modules.instLiftingPresheafOfModulesSheafifyPresheafWOpensCarrierCarrierCommRingCatGrothendieckTopologyObjFunctorOppositeIsSheafSheafCompPullback₀Pullback GoodReductionJacobian.RelativeGroupLaw.isIso_endKerStr_schemeHomOverId AlgebraicGeometry.OModulePresheaf.isScalarTower AlgebraicGeometry.Scheme.OrderedAffineCover.instLinearOrder AlgebraicGeometry.OModulePresheaf.module AlgebraicGeometry.Scheme.OrderedAffineCover.instFintype AlgebraicGeometry.Scheme.OrderedAffineCover.instFintypeIdx AlgebraicGeometry.OModulePresheaf.addCommGroup AlgebraicGeometry.Scheme.OrderedAffineCover.instDecidableEqIdx AlgebraicGeometry.OModulePresheaf.moduleSections TwoChartCech.Sections.M0_moduleA TwoChartCech.Sections.M1_module TwoChartCech.Cover.A01_algebra TwoChartCech.Cover.A0_algebra TwoChartCech.Cover.A1_commRing TwoChartCech.Cover.A1_algebra TwoChartCech.Sections.M01_module TwoChartCech.Sections.M0_addCommGroup TwoChartCech.Sections.M0_tower TwoChartCech.Sections.M01_addCommGroup TwoChartCech.Cover.A0_commRing TwoChartCech.Sections.M1_tower TwoChartCech.Sections.M01_moduleA TwoChartCech.Sections.M0_module"
p2m_attr_erase "instance" "TwoChartCech.Sections.M1_moduleA TwoChartCech.Sections.M1_addCommGroup TwoChartCech.Cover.A01_commRing TwoChartCech.Sections.M01_tower CoherentBaseChange.TwoTermComplex.C0_module CoherentBaseChange.TwoTermComplex.C0_addCommGroup CoherentBaseChange.TwoTermComplex.C1_module CoherentBaseChange.TwoTermComplex.C1_addCommGroup CoherentBaseChange.TwoTermComplex.C0_free CoherentBaseChange.TwoTermComplex.C1_finite CoherentBaseChange.TwoTermComplex.C0_finite CoherentBaseChange.TwoTermComplex.C1_free AlgebraicGeometry.OModulePresheaf.instSubsingletonObjZero AlgebraicGeometry.SmoothOfRelativeDimension.fiberToSpecResidueField AlgebraicGeometry.SmoothOfRelativeDimension.pullback_snd AlgebraicGeometry.SmoothOfRelativeDimension.pullback_fst AlgebraicGeometry.SmoothOfRelativeDimension.smooth_one AlgebraicGeometry.SmoothProperCurve.isIntegral_pullback_Spec_field AlgebraicGeometry.IsProper.fiberToSpecResidueField AlgebraicCurve.CurveModel.isProper AlgebraicCurve.CurveModel.isIntegral AlgebraicCurve.CurveModel.smooth AlgebraicGeometry.Scheme.LocalRepresentabilityULift.instIsLocallyInjectiveFunUliftYonedaGluedToSheaf AlgebraicGeometry.Scheme.LocalRepresentabilityULift.instIsLocallySurjectiveFunUliftYonedaGluedToSheafOfIsLocallySurjectiveZariskiTopologyDescFunctorOppositeType AlgebraicGeometry.Scheme.LocalRepresentabilityULift.instIsOpenImmersionToGlued AlgebraicGeometry.Scheme.LocalRepresentabilityULift.instIsIsoSheafZariskiTopologyTypeUliftYonedaGluedToSheaf AlgebraicGeometry.RelPicard.instIsOpenImmersionToGlued AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.instFundamentalIdentityOfSumRamificationInertia AlgebraicCurve.Place.instIsScalarTowerResidueFieldRestrictPushforward AlgebraicCurve.Place.instAlgebraResidueFieldRestrictPushforward AlgebraicCurve.Place.instIsLocalHomRestrictInclusion AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions PresheafOfModules.ExteriorPower.instModulePresheafAb"
p2m_attr_erase "instance" "AlgebraicGeometry.RelEffCartierDiv.subsingleton_of_degree_zero AlgebraicGeometry.RelEffCartierDiv.isIso_subschemeIota_snd_of_degree_one AlgebraicGeometry.isIso_ker_graphOver_subschemeIota_snd AlgebraicGeometry.isClosedImmersion_graphOver AlgebraicGeometry.FGSubalgebra.instIsDirectedLe AlgebraicGeometry.FGSubalgebra.instQuasiSeparatedSpaceCarrierCarrierCommRingCatObjOppositeSchemeSpecDiagram AlgebraicGeometry.FGSubalgebra.instIsCofilteredOpposite AlgebraicGeometry.FGSubalgebra.instIsAffineObjOppositeSchemeSpecDiagram AlgebraicGeometry.FGSubalgebra.instNonempty AlgebraicGeometry.FGSubalgebra.instNonemptySubtypeLeSubalgebraValFG AlgebraicGeometry.FGSubalgebra.instCompactSpaceCarrierCarrierCommRingCatObjOppositeSchemeSpecDiagram AlgebraicGeometry.FGSubalgebra.instIsDirectedSubtypeLeSubalgebraValFG AlgebraicGeometry.FGSubalgebra.instIsAffineHomMapOppositeSchemeSpecDiagram AlgebraicGeometry.FGSubalgebra.instIsFiltered AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instNeg AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instSMulInt AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instAddCommGroup AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instAdd AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instSub AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instModuleCarrierObjOppositeOpensCarrierCarrierCommRingCatPresheafOpOpensTop AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instSMulCarrierObjOppositeOpensCarrierCarrierCommRingCatPresheafOpOpensTop AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instSMulNat AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instZero AlgebraicCurve.instHasLocalResidue_of_hasCanonicalLocalResidueK AlgebraicCurve.instHasCanonicalLocalResidueK_of_hasCanonicalLocalResidueKStar AlgebraicCurve.Place.kw_ffgc_finiteDimensional_adicCompletion instAlgebraSubtypeMemValuationSubring_definitions AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersIntegersCompletion ModularCurve.KwF4gRRTate.instAlgebraKAdicCompletionIntegers AlgebraicCurve.Place.kw_ffgc_continuousSMul_adicCompletionComap AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersCompletionCompletion IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions AlgebraicCurve.instHasCanonicalLocalResidueK AlgebraicCurve.Place.instAlgebra_restrictResidueField AlgebraicCurve.Place.instIsScalarTower_restrictResidueField"
p2m_attr_erase "instance" "AlgebraicCurve.instHasLocalResidue AlgebraicCurve.HasSeparableResidue.of_perfectField_of_isCurveOver AlgebraicCurve.HasSeparableResidue.of_perfectField AlgebraicCurve.Place.instIsLocalHom_restrictSubringHom AlgebraicCurve.instHasCanonicalLocalResidueKStar ModularCurve.KwNo6Pin.isLocalRing_completion SheafOfModules.isIso_ihomModelToIhom AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instDecidableEqIdx AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instFintype AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instLinearOrder AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instFintypeIdx AlgebraicGeometry.OModulePresheaf.Leray.relAltC_scalarTower AlgebraicGeometry.OModulePresheaf.Leray.ker_relAltd_modΓ AlgebraicGeometry.OModulePresheaf.Leray.relAltC_modΓ AlgebraicGeometry.OModulePresheaf.Leray.biC_abGrp AlgebraicGeometry.OModulePresheaf.Leray.relAltH_modΓ AlgebraicGeometry.OModulePresheaf.Leray.ker_relAltd_smul AlgebraicGeometry.OModulePresheaf.Leray.relAltH_scalarTower AlgebraicGeometry.OModulePresheaf.Leray.relAltH_smul AlgebraicGeometry.OModulePresheaf.Leray.biC_module DoubleComplex.instModuleE₂I DoubleComplex.Bounded.modR DoubleComplex.instModuleE₂II DoubleComplex.instAddCommGroupE₂II DoubleComplex.Bounded.abGrp DoubleComplex.instAddCommGroupE₂I ProjSpaceCech.GradedModule.H.module ProjSpaceCech.GradedModule.H.addCommGroup ProjSpaceCech.GradedModule.sec.instAdd ProjSpaceCech.GradedModule.sec.instNeg ProjSpaceCech.GradedModule.acg ProjSpaceCech.GradedModule.Frac.setoid ProjSpaceCech.GradedModule.modR ProjSpaceCech.GradedModule.sec.instModule ProjSpaceCech.GradedModule.sec.instAddCommGroup ProjSpaceCech.GradedModule.sec.instZero ProjSpaceCech.GradedModule.Presentation.fJ ProjSpaceCech.GradedModule.sec.instSMul ProjSpaceCech.Twist.H.module ProjSpaceCech.Idx.instFintype"
p2m_attr_erase "instance" "ProjSpaceCech.Twist.H.addCommGroup ProjSpaceCech.Idx.instDecidableEq ProjSpaceCech.Twist.Mon.instDecidableEq ProjSpaceCech.Twist.cochain.instAddCommGroup ProjSpaceCech.Twist.cochain.instModule AlgebraicGeometry.FGSubalgebra.tensorStage_directedSystem AlgebraicGeometry.RelEffCartierDiv.isClosedImmersion_subschemeι_resProdMap AlgebraicGeometry.RelEffCartierDiv.isOpenImmersion_resProdMap AlgebraicCurve.CurveModel.locallyOfFiniteType_gluedToBase AlgebraicCurve.CurveModel.isFractionRing_overlap AlgebraicCurve.CurveModel.isLocallyNoetherian_glued AlgebraicCurve.CurveModel.jacobsonSpace_glued AlgebraicCurve.CurveModel.isOpenImmersion_ι₀ AlgebraicCurve.CurveModel.isIntegral_glued AlgebraicCurve.CurveModel.quasiSeparated_gluedToBase AlgebraicCurve.CurveModel.compactSpace_glued AlgebraicCurve.CurveModel.isIntegral_adjoin_chartRing AlgebraicCurve.CurveModel.isFractionRing_overlap_functionField AlgebraicCurve.CurveModel.isProper_gluedToBase AlgebraicCurve.CurveModel.isOpenImmersion_ιU AlgebraicCurve.CurveModel.isOpenImmersion_f₀ AlgebraicCurve.CurveModel.isOpenImmersion_fInf AlgebraicCurve.CurveModel.isOpenImmersion_ιInf AlgebraicCurve.CurveModel.algebra_overlap_functionField AlgebraicCurve.CurveModel.quasiCompact_gluedToBase AlgebraicCurve.CurveModel.algebraAdjoin AlgebraicCurve.CurveModel.isDedekindDomain_chartRing AlgebraicCurve.CurveModel.isIntegralClosure AlgebraicCurve.CurveModel.finite_chartRing AlgebraicCurve.CurveModel.centre_isPrime AlgebraicCurve.CurveModel.isFractionRing_chartRing AlgebraicCurve.CurveModel.finiteType_chartRing AlgebraicCurve.CurveModel.isNoetherianRing_chartRing AlgebraicCurve.CurveModel.isScalarTower_base_adjoin AlgebraicCurve.CurveModel.isScalarTower_adjoin AlgebraicCurve.CurveModel.chartRing_finitePresentation instTopologicallyFGOfFiniteType AlgebraicGeometry.ProjSpace.twistObj.addCommGroup AlgebraicGeometry.ProjSpace.twistFam.module AlgebraicGeometry.ProjSpace.twistObj.module"
p2m_attr_erase "instance" "AlgebraicGeometry.ProjSpace.twistObj.moduleSections AlgebraicGeometry.ProjSpace.twistFam.addCommGroup kmfloorsGlue_int_three_isPrime kmfloorsGlue_int_bot_isPrime AlgebraicGeometry.SubalgebraStages.compactSpace_pullback AlgebraicGeometry.SubalgebraStages.quasiSeparatedSpace_pullback AlgebraicGeometry.SubalgebraStages.compactSpace_obj AlgebraicGeometry.SubalgebraStages.quasiSeparatedSpace_obj AlgebraicGeometry.SubalgebraStages.quasiCompact_snd AlgebraicGeometry.SubalgebraStages.isAffineHom_leg AlgebraicGeometry.SubalgebraStages.isAffineHom_trans AlgebraicGeometry.SubalgebraStages.isAffineHom_diagram_map AlgebraicGeometry.SubalgebraStages.quasiSeparated_snd AlgebraicGeometry.SubalgebraStages.isCofiltered_op IsDirectLimit.Module.instDirectLimitCoeLinearMapIdOfOfNonempty AdicCompletion.instIsLocalRingMaximalIdeal AlgebraicGeometry.Scheme.Modules.GlueOfCocycle.instSMulCarrierObjOppositeOpensCarrierCarrierCommRingCatPresheafOpOpensSubtypeForallMinMemAddSubgroupFamilies AlgebraicGeometry.Scheme.Modules.GlueOfCocycle.instModulePreGlue AlgebraicGeometry.Scheme.Modules.GlueOfCocycle.instModuleCarrierObjOppositeOpensCarrierCarrierCommRingCatPresheafOpOpensSubtypeForallMinMemAddSubgroupFamilies"
p2m_attr_erase "simp" "GoodReductionJacobian.RelativeGroupLaw.baseChangePointToBase_ofBase GoodReductionJacobian.RelativeGroupLaw.baseChangePointToBase_coe GoodReductionJacobian.RelativeGroupLaw.baseChangePointOfBase_coe GoodReductionJacobian.RelativeGroupLaw.baseChange_inv GoodReductionJacobian.RelativeGroupLaw.baseChangePointOfBase_toBase GoodReductionJacobian.RelativeGroupLaw.baseChange_mul GoodReductionJacobian.RelativeGroupLaw.baseChange_one NeronModelInfra.NeronModelPropertyBundle.endExtensionEquiv_symm_restrict NeronModelInfra.schemeHomOverComp_id_left NeronModelInfra.schemeHomOverComp_id_right NeronModelInfra.schemeHomOverId_coe NeronModelInfra.NeronModelPropertyBundle.endExtensionEquiv_apply NeronModelInfra.NeronModelPropertyBundle.restrict_endExtensionEquiv_symm NeronModelInfra.schemeHomOverComp_coe NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_fst NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_snd NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_fst NeronSpecialFibreInfra.neronEndRestrictEquiv_apply NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_fst_assoc NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_snd NeronSpecialFibreInfra.neronEndExtension_genericFibreRestrict NeronSpecialFibreInfra.specClosedFibreInclusion_eq NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_fst_assoc NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_snd_assoc NeronSpecialFibreInfra.genericFibreRestrict_neronEndExtension NeronSpecialFibreInfra.homOverId_coe NeronSpecialFibreInfra.homOverComp_coe NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_snd_assoc GoodReductionJacobian.RelativeGroupLaw.fibre_inv GoodReductionJacobian.RelativeGroupLaw.fibrePointToBase_coe GoodReductionJacobian.RelativeGroupLaw.fibrePointOfBase_toBase GoodReductionJacobian.RelativeGroupLaw.fibre_mul GoodReductionJacobian.RelativeGroupLaw.fibrePointToBase_ofBase GoodReductionJacobian.RelativeGroupLaw.fibre_one GoodReductionJacobian.RelativeGroupLaw.fibrePointOfBase_coe AlgebraicGeometry.schemeFibreEndo_snd AlgebraicGeometry.schemeFibreEndo_fst RegularLocalRingQuotientAscent.dualNumberFst_apply PresheafOfModules.freeεIso_hom_app PresheafOfModules.freeμIso_hom_app"
p2m_attr_erase "simp" "NeronModelInfra.schemeHomOverNpow_succ NeronModelInfra.schemeHomOverNpow_zero GoodReductionJacobian.relativeGroupLawOfGrpObj_inv GoodReductionJacobian.relativeGroupLawOfGrpObj_mul GoodReductionJacobian.overHomEquivSchemeHomOver_apply_coe GoodReductionJacobian.relativeGroupLawOfGrpObj_one GoodReductionJacobian.overHomEquivSchemeHomOver_symm_apply_left AlgebraicGeometry.Scheme.Modules.tensorPow_zero AlgebraicGeometry.Scheme.Modules.tensorPow_succ AlgebraicGeometry.Scheme.OrderedAffineCover.mk.injEq AlgebraicGeometry.OModulePresheaf.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCover.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.mk.injEq AlgebraicGeometry.Scheme.TwoAffineOpenCover.mk.injEq AlgebraicGeometry.Scheme.TwoAffineOpenCover.mk.sizeOf_spec AlgebraicGeometry.Scheme.TwoAffineOpenCover.pullback_U1 AlgebraicGeometry.Scheme.TwoAffineOpenCover.pullback_U0 TwoChartCech.Sections.mk.injEq TwoChartCech.Cover.mk.injEq TwoChartCech.GrothendieckComplex.mk.injEq TwoChartCech.Sections.mk.sizeOf_spec TwoChartCech.Cover.mk.sizeOf_spec TwoChartCech.Cover.lineBundle_r0_apply TwoChartCech.GrothendieckComplex.mk.sizeOf_spec TwoChartCech.Cover.lineBundle_r1_apply CoherentBaseChange.TwoTermComplex.mk.sizeOf_spec CoherentBaseChange.TwoTermComplex.mk.injEq AlgebraicGeometry.OModulePresheaf.prod_obj AlgebraicGeometry.OModulePresheaf.restrOpen_obj AlgebraicGeometry.OModulePresheaf.DevissageStep.mk.injEq AlgebraicGeometry.OModulePresheaf.pushforward_obj AlgebraicGeometry.OModulePresheaf.im_obj AlgebraicGeometry.OModulePresheaf.pow_obj AlgebraicGeometry.OModulePresheaf.fstHom_app AlgebraicGeometry.OModulePresheaf.ker_obj AlgebraicGeometry.OModulePresheaf.coker_obj AlgebraicGeometry.OModulePresheaf.DevissageStep.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCover.preimage_U AlgebraicGeometry.OModulePresheaf.sndHom_app AlgebraicGeometry.OModulePresheaf.Hom.mk.injEq"
p2m_attr_erase "simp" "AlgebraicGeometry.OModulePresheaf.Hom.id_app AlgebraicGeometry.OModulePresheaf.AffHom.appSections_apply AlgebraicGeometry.OModulePresheaf.AffHom.comp_app AlgebraicGeometry.OModulePresheaf.AffSES.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.AffHom.kerMap_coe AlgebraicGeometry.OModulePresheaf.AffHom.id_app AlgebraicGeometry.OModulePresheaf.Hom.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.Hom.toAffHom_app AlgebraicGeometry.OModulePresheaf.SES.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.AffHom.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.Hom.comp_app AlgebraicGeometry.OModulePresheaf.SES.mk.injEq AlgebraicGeometry.OModulePresheaf.AffHom.mk.injEq AlgebraicGeometry.OModulePresheaf.Hom.appSections_apply AlgebraicGeometry.OModulePresheaf.AffSES.mk.injEq AlgebraicGeometry.RelPicard.RepresentsRelSubPic.mk.injEq AlgebraicGeometry.RelPicard.SubPicCondition.mk.injEq AlgebraicGeometry.RelPicard.SubPicCondition.mk.sizeOf_spec AlgebraicGeometry.RelPicard.RepresentsRelSubPic.mk.sizeOf_spec AlgebraicGeometry.SmoothProperCurve.sectionBaseChange_coe_snd AlgebraicGeometry.SmoothProperCurve.sectionBaseChange_coe_fst AlgebraicCurve.CurveModel.mk.injEq AlgebraicCurve.CurveModel.mk.sizeOf_spec AlgebraicCurve.mulAdele_apply AlgebraicCurve.residuePairing_apply_coe AlgebraicCurve.mem_adeleBdd AlgebraicCurve.weilSmul_one AlgebraicCurve.diagonalHom_apply AlgebraicCurve.weilSmul_apply AlgebraicCurve.adeleSpaceMul_coe AlgebraicCurve.mulAdele_one AlgebraicGeometry.SmoothProperCurve.FiniteMapData.twoAffineOpenCover_U1 AlgebraicGeometry.SmoothProperCurve.FiniteMapData.mk.injEq AlgebraicGeometry.SmoothProperCurve.FiniteMapData.mk.sizeOf_spec AlgebraicGeometry.SmoothProperCurve.FiniteMapData.twoAffineOpenCover_U0 AlgebraicGeometry.RelPicard.SubPicCondition.onClasses_mk AlgebraicGeometry.RelPicard.relSubPicPresheaf_map_coe CategoryTheory.Functor.OverTotal.ofFibre_fst CategoryTheory.Functor.overTotal_map_fst AlgebraicGeometry.Scheme.LocalRepresentabilityULift.glueData_J"
p2m_attr_erase "simp" "AlgebraicGeometry.Scheme.LocalRepresentabilityULift.uliftYoneda_toGlued_uliftYonedaGluedToSheaf AlgebraicGeometry.Scheme.LocalRepresentabilityULift.glueData_t' AlgebraicGeometry.Scheme.LocalRepresentabilityULift.uliftYoneda_toGlued_uliftYonedaGluedToSheaf_assoc AlgebraicGeometry.Scheme.LocalRepresentabilityULift.uliftYonedaGluedToSheaf_app_toGlued AlgebraicGeometry.Scheme.LocalRepresentabilityULift.glueData_openCover_map AlgebraicGeometry.Scheme.LocalRepresentabilityULift.uliftYonedaGluedToSheaf_app_comp AlgebraicGeometry.Scheme.LocalRepresentabilityULift.glueData_V AlgebraicGeometry.Scheme.LocalRepresentabilityULift.glueData_t AlgebraicGeometry.Scheme.LocalRepresentabilityULift.glueData_U AlgebraicGeometry.Scheme.LocalRepresentabilityULift.glueData_f AlgebraicGeometry.RelPicard.designationOfRepresentableBy_P AlgebraicGeometry.RelPicard.designationOfRepresentableBy_toBase AlgebraicGeometry.RelPicard.rigSection_snd AlgebraicGeometry.RelPicard.RigidifiedLineBundle.ofInvertible_L AlgebraicGeometry.RelPicard.rigSection_snd_assoc AlgebraicGeometry.RelPicard.SubPicGroupCondition.mk.injEq AlgebraicGeometry.RelPicard.SubPicGroupCondition.mk.sizeOf_spec AlgebraicCurve.coe_cechH0Equiv_apply AlgebraicCurve.cechH1ToH1_mk AlgebraicCurve.lSpaceOn_univ AlgebraicCurve.lSpaceOn_empty AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.Divisor.mapRestrict_single AlgebraicCurve.Divisor.pushforward_single AlgebraicCurve.Place.coe_restrictInclusion AlgebraicCurve.Place.mem_fiber AlgebraicCurve.Place.restrict_toValuationSubring AlgebraicCurve.Divisor.degree_pushforward AlgebraicCurve.Place.restrictResidueMap_residue AlgebraicCurve.Pic0.coe_pushforwardDegZeroHom AlgebraicCurve.Pic0.coe_pullbackDegZeroHom AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply"
p2m_attr_erase "simp" "AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Divisor.degree_pushforwardAlong AlgebraicCurve.Pic0.coe_degZeroCorrespondence AlgebraicCurve.Place.mem_fiberAlong AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.jqNModC_one ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one AlgebraicCurve.Place.differentialCoeff_zero AlgebraicCurve.Place.differentialCoeff_dCoord AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.injEq"
p2m_attr_erase "simp" "AlgebraicCurve.TranscendenceTower.mk.injEq AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec AlgebraicCurve.PoleDivisorPackage.mk.injEq AlgebraicGeometry.RelPicard.thetaBundle_def AlgebraicGeometry.RelPicard.picardBundle_def AlgebraicGeometry.RelEffCartierDiv.toRelEffDivisor_ofRelEffDivisor AlgebraicGeometry.RelEffCartierDiv.toRelEffDivisor_I AlgebraicGeometry.mapOnProdOver_fst_assoc AlgebraicGeometry.RelEffCartierDiv.mk.sizeOf_spec AlgebraicGeometry.RelEffCartierDiv.mk.injEq AlgebraicGeometry.mapOnProdOver_snd AlgebraicGeometry.mapOnProdOver_fst AlgebraicGeometry.mapOnProdOver_snd_assoc AlgebraicGeometry.mapOnProdOver_id AlgebraicCurve.RelEffDivisor.mk.sizeOf_spec AlgebraicCurve.mapOnProd_fst AlgebraicCurve.mapOnProd_fst_assoc AlgebraicCurve.mapOnProd_snd AlgebraicCurve.UnivDivisorPack.mk.injEq AlgebraicCurve.RelEffDivisor.mk.injEq AlgebraicCurve.UnivDivisorPack.mk.sizeOf_spec AlgebraicCurve.mapOnProd_snd_assoc AlgebraicGeometry.Scheme.Modules.exteriorPower_obj PresheafOfModules.exteriorPower_map_ιMulti PresheafOfModules.ExteriorPower.appₗ_apply AlgebraicGeometry.prodKerGraph_one AlgebraicGeometry.fibrePowOver.proj_comp AlgebraicGeometry.prodKerGraph_zero AlgebraicGeometry.RelEffCartierDiv.empty_I AlgebraicGeometry.fibrePowOver.proj_comp_assoc AlgebraicGeometry.graphOver_fst_assoc AlgebraicGeometry.RelEffCartierDiv.toPoint_comp AlgebraicGeometry.RelEffCartierDiv.toPoint_comp_assoc AlgebraicGeometry.graphOver_fst AlgebraicGeometry.RelEffCartierDiv.ofPoint_I AlgebraicGeometry.graphOver_snd AlgebraicGeometry.graphOver_snd_assoc AlgebraicCurve.SymmetricPowerPackage.mk.sizeOf_spec AlgebraicCurve.SymmetricPowerPackage.mk.injEq"
p2m_attr_erase "simp" "AlgebraicGeometry.FGSubalgebra.cocone_ι_app_apply AlgebraicGeometry.RelPicard.fst_toProdSpec AlgebraicGeometry.RelPicard.toProdSpec_fst_assoc AlgebraicGeometry.RelPicard.pointsSubBasepointModule_cons AlgebraicGeometry.RelPicard.pointsSubBasepointModule_nil AlgebraicGeometry.RelPicard.fst_toProdSpec_assoc AlgebraicGeometry.RelPicard.toProdSpec_fst AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.sub_app AlgebraicGeometry.Scheme.IdealSheafData.sres_sresTop AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.add_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.mk.sizeOf_spec AlgebraicGeometry.Scheme.IdealSheafData.coe_resLE AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.smul_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.coe_ofLE_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.ideal_range AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.zero_app AlgebraicGeometry.Scheme.IdealSheafData.sres_sres AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.comp_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.neg_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.id_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.coe_mulRight_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.nsmul_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.mk.injEq AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.zsmul_app AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.sizeOf_spec AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.injEq AlgebraicCurve.adeleSingle_coe AlgebraicCurve.kaehlerResidueTermKFam_apply AlgebraicCurve.Place.LocalResidueData.mk.injEq AlgebraicCurve.Place.LocalResidueData.mk.sizeOf_spec AlgebraicCurve.Place.kw_ffgc_adicCompletionComapIntegers_coe AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.sizeOf_spec AlgebraicCurve.Place.mem_simplePoleSubmodule AlgebraicCurve.Place.coe_uniformizerSubring ModularCurve.Lg37.Lg37CompletionSection.mk.injEq AlgebraicCurve.Place.CoefficientFieldSection.mk.injEq AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.injEq ModularCurve.Lg37.Lg37CompletionSection.mk.sizeOf_spec AlgebraicCurve.Place.CoefficientFieldSection.mk.sizeOf_spec AlgebraicCurve.Place.poleSubmodule_one"
p2m_attr_erase "simp" "AlgebraicCurve.Place.mem_poleSubmodule AlgebraicGeometry.Scheme.Modules.toUnitSection_ofUnitSection AlgebraicGeometry.Scheme.Modules.pullbackSection_def AlgebraicGeometry.Scheme.Modules.ofUnitSection_toUnitSection PresheafOfModules.InternalHom.IsSheafAux.appAt_toPresheafHom SheafOfModules.ihomSectionsEquivFamily_unit AlgebraicGeometry.Scheme.Modules.restrictHomEquivFamily_apply SheafOfModules.ihomEval_unit_app AlgebraicGeometry.Scheme.Modules.ihomEval_zero_right AlgebraicGeometry.Scheme.Modules.ihomEval_zero_left AlgebraicGeometry.Scheme.Modules.homOfFamily_app_apply SheafOfModules.unit_ihomSectionsEquivFamily AlgebraicGeometry.Scheme.Modules.familyOfHom_app AlgebraicGeometry.Scheme.Modules.restrictUnitIso_hom_app_apply AlgebraicGeometry.Scheme.Modules.restrictUnitIso_inv_app_apply AlgebraicGeometry.Scheme.Modules.restrictHomOfFamily_app_apply AlgebraicGeometry.Scheme.Modules.restrictHomEquivFamily_symm_apply AlgebraicGeometry.Scheme.Modules.tensorSections_zero_right AlgebraicGeometry.Scheme.Modules.map_unitSection AlgebraicGeometry.Scheme.Modules.tensorSectionsBilin_apply AlgebraicGeometry.Scheme.Modules.tensorPowSection_zero AlgebraicGeometry.Scheme.Modules.tensorSections_zero_left AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_neg AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_zero AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_sub AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_add AlgebraicGeometry.Scheme.OrderedAffineCover.toCoverOf_U AlgebraicGeometry.Scheme.OrderedAffineCoverOf.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCoverOf.mk.injEq AlgebraicGeometry.Scheme.OrderedAffineCover.restrict_U AlgebraicGeometry.OModulePresheaf.Leray.restrictToPreimage_U DoubleComplex.Bounded.mk.injEq DoubleComplex.Bounded.mk.sizeOf_spec DoubleComplex.Convergence.mk.injEq DoubleComplex.Convergence.mk.sizeOf_spec DoubleComplex.SubQuot.mk.sizeOf_spec DoubleComplex.SubQuot.mk.injEq ProjSpaceCech.GradedModule.mk.injEq ProjSpaceCech.GradedModule.mk.sizeOf_spec ProjSpaceCech.GradedModule.Frac.mk.sizeOf_spec"
p2m_attr_erase "simp" "ProjSpaceCech.GradedModule.Presentation.mk.injEq ProjSpaceCech.GradedModule.Frac.mk.injEq ProjSpaceCech.GradedModule.Presentation.mk.sizeOf_spec ProjSpaceCech.GradedModule.Hom.shift_toLinearMap ProjSpaceCech.GradedModule.Hom.mk.sizeOf_spec ProjSpaceCech.GradedModule.Hom.mk.injEq TwoChartCech.Mumford.dK_apply TwoChartCech.Mumford.ι0_apply TwoChartCech.Mumford.ι1_apply TwoChartCech.KerCoprod.dK_apply TwoChartCech.KerCoprod.ι1_apply TwoChartCech.KerCoprod.ι0_apply AlgebraicGeometry.tilde.functorCompPullbackSpecIso_app AlgebraicGeometry.RelPicard.algEquivZeroGroupCut_toSubPicCondition AlgebraicGeometry.RelPicard.LFP.stageHom_val AlgebraicGeometry.RelPicard.BaseChange.relSubPicPresheafRestrictIso_hom_app_coe AlgebraicGeometry.RelPicard.BaseChange.relSubPicPresheafRestrictIso_inv_app_coe AlgebraicGeometry.RelPicard.BaseChange.restrict_P AlgebraicGeometry.RelEffCartierDiv.IsUniversal.lift_comp AlgebraicGeometry.RelEffCartierDiv.functor_map_fst AlgebraicGeometry.RelEffCartierDiv.IsUniversal.homEquiv_apply AlgebraicGeometry.RelEffCartierDiv.IsUniversal.lift_pullbackAlong AlgebraicGeometry.RelEffCartierDiv.IsUniversal.homEquiv_symm_apply AlgebraicGeometry.RelEffCartierDiv.IsUniversal.lift_comp_assoc AlgebraicGeometry.RelEffCartierDiv.supportedIn_top AlgebraicGeometry.RelEffCartierDiv.mem_supportedIn_iff AlgebraicGeometry.RelEffCartierDiv.supportedIn_top_eq AlgebraicGeometry.RelEffCartierDiv.restrictAlong_extendAlong AlgebraicGeometry.RelEffCartierDiv.extendAlong_I AlgebraicGeometry.RelEffCartierDiv.resProdMap_snd AlgebraicGeometry.RelEffCartierDiv.restrictAlong_I AlgebraicGeometry.RelEffCartierDiv.extendAlong_restrictAlong AlgebraicGeometry.RelEffCartierDiv.resProdMap_fst_assoc AlgebraicGeometry.RelEffCartierDiv.resProdMap_snd_assoc AlgebraicGeometry.RelEffCartierDiv.resProdMap_fst CoherentBaseChange.FibreH0Family.mk.sizeOf_spec CoherentBaseChange.FibreH0Family.mk.injEq AlgebraicCurve.CurveModel.coe_gInf AlgebraicCurve.CurveModel.coe_tInvChart AlgebraicCurve.CurveModel.ιInf_gluedToBase_assoc"
p2m_attr_erase "simp" "AlgebraicCurve.CurveModel.ιInf_gluedToBase AlgebraicCurve.CurveModel.primeOfι₀_asIdeal AlgebraicCurve.CurveModel.coe_tChart AlgebraicCurve.CurveModel.ι₀_gluedToBase_assoc AlgebraicCurve.CurveModel.primeOfιInf_asIdeal AlgebraicCurve.CurveModel.ι₀_gluedToBase AlgebraicCurve.CurveModel.coe_tma AlgebraicCurve.CurveModel.coe_primeEquivChartPlaces AlgebraicGeometry.ProjSpace.twistObj.mk.injEq AlgebraicGeometry.ProjSpace.twistObj.zero_val AlgebraicGeometry.ProjSpace.twistObj.add_val AlgebraicGeometry.ProjSpace.twist_res_val AlgebraicGeometry.ProjSpace.twist_smul_val AlgebraicGeometry.ProjSpace.twistGradeToObj_val AlgebraicGeometry.ProjSpace.twistObj.smul_val AlgebraicGeometry.ProjSpace.twistGradeEquiv_apply_val AlgebraicGeometry.ProjSpace.twistObj.mk.sizeOf_spec AlgebraicGeometry.SubalgebraStages.specCone_π_app AlgebraicGeometry.SubalgebraStages.specLeg_specHom AlgebraicGeometry.SubalgebraStages.specLeg_specTrans AlgebraicGeometry.SubalgebraStages.cone_pt AlgebraicGeometry.SubalgebraStages.trans_fst AlgebraicGeometry.SubalgebraStages.diagram_obj AlgebraicGeometry.SubalgebraStages.leg_snd AlgebraicGeometry.SubalgebraStages.diagram_map AlgebraicGeometry.SubalgebraStages.specTrans_refl AlgebraicGeometry.SubalgebraStages.trans_snd AlgebraicGeometry.SubalgebraStages.specTrans_specHom AlgebraicGeometry.SubalgebraStages.specCone_pt AlgebraicGeometry.SubalgebraStages.cone_π_app AlgebraicGeometry.SubalgebraStages.specDiagram_map AlgebraicGeometry.SubalgebraStages.specDiagram_obj AlgebraicGeometry.SubalgebraStages.leg_fst AlgebraicGeometry.SubalgebraStages.leg_trans IsDirectLimit.Module.linearEquiv_symm_apply IsDirectLimit.linearEquiv_symm_apply IsDirectLimit.lift_of IsDirectLimit.Module.linearEquiv_apply IsDirectLimit.Module.lift_of IsDirectLimit.Equiv_apply"
p2m_attr_erase "simp" "AlgebraicGeometry.Scheme.Modules.glueComponent_glueMk AlgebraicGeometry.Scheme.Modules.UnitCocycle.mk.injEq AlgebraicGeometry.Scheme.Modules.UnitCocycle.mk.sizeOf_spec GoodReductionJacobian.RelativeGroupLaw.sndPoint_coe GoodReductionJacobian.RelativeGroupLaw.fstPoint_coe"

set_option autoImplicit false

open scoped TensorProduct Quaternion NumberField
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry QuaternionAlgebra CerednikDrinfeld CerednikDrinfeld.QM NeronModelInfra GoodReductionJacobian AlgebraicGeometry.Polarisation AlgebraicGeometry.PolarisedAbelianScheme

theorem PQH9.exists_isPullback_map_homOfLE_and_pt_eq_fromSpec_satisfying
    {g d n : ℕ} {B : Type} [CommRing B] {M : Scheme.{0}} {πM : M ⟶ Spec (CommRingCat.of B)}
    {Q : ∀ (S : Type) [CommRing S], PolarisedAbelianScheme g d n S → Prop}
    {pt : ∀ (S : Type) [CommRing S] (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of B)),
      PolarisedAbelianScheme.Satisfying g d n Q S → SchemeHomOver s πM}
    (hM : PolarisedAbelianScheme.Satisfying.IsFineModuli g d n Q M πM pt)
    (hQbc : ∀ (S S' : Type) [CommRing S] [CommRing S'] (φ : S →+* S')
      (X : PolarisedAbelianScheme g d n S) (X' : PolarisedAbelianScheme g d n S'),
      PolarisedAbelianScheme.IsPullback φ X X' → Q S X → Q S' X')
    {U U' : M.Opens} (hU : IsAffineOpen U) (hU' : IsAffineOpen U') (hle : U' ≤ U)
    (X : PolarisedAbelianScheme g d n Γ(M, U)) (hXQ : Q Γ(M, U) X)
    (hX : (pt Γ(M, U) (hU.fromSpec ≫ πM) ⟨X, hXQ⟩).1 = hU.fromSpec) :
    ∃ (X' : PolarisedAbelianScheme g d n Γ(M, U')) (hX'Q : Q Γ(M, U') X'),
      PolarisedAbelianScheme.IsPullback (M.presheaf.map (homOfLE hle).op).hom X X' ∧
      (pt Γ(M, U') (hU'.fromSpec ≫ πM) ⟨X', hX'Q⟩).1 = hU'.fromSpec ∧
      ∀ (Y : PolarisedAbelianScheme g d n Γ(M, U')) (hYQ : Q Γ(M, U') Y),
        (pt Γ(M, U') (hU'.fromSpec ≫ πM) ⟨Y, hYQ⟩).1 = hU'.fromSpec → PolarisedAbelianScheme.Iso X' Y := by
  obtain ⟨X', hX'⟩ := AlgebraicGeometry.PolarisedAbelianScheme.exists_isPullback (M.presheaf.map (homOfLE hle).op).hom X
  have hX'Q : Q _ X' := hQbc _ _ _ X X' hX' hXQ
  have hs : Spec.map (CommRingCat.ofHom (M.presheaf.map (homOfLE hle).op).hom) ≫ (hU.fromSpec ≫ πM) =
      hU'.fromSpec ≫ πM := by
    rw [CommRingCat.ofHom_hom, ← Category.assoc, hU.map_fromSpec hU' (homOfLE hle).op]
  have h := hM.pt_pullback Γ(M, U) Γ(M, U') (M.presheaf.map (homOfLE hle).op).hom (hU.fromSpec ≫ πM)
    (hU'.fromSpec ≫ πM) hs ⟨X, hXQ⟩ ⟨X', hX'Q⟩ hX'
  have hpt : (pt Γ(M, U') (hU'.fromSpec ≫ πM) ⟨X', hX'Q⟩).1 = hU'.fromSpec := by
    rw [h, hX, CommRingCat.ofHom_hom]
    exact hU.map_fromSpec hU' (homOfLE hle).op
  refine ⟨X', hX'Q, hX', hpt, fun Y hYQ hY => ?_⟩
  exact hM.pt_injective Γ(M, U') (hU'.fromSpec ≫ πM) ⟨X', hX'Q⟩ ⟨Y, hYQ⟩ (Subtype.ext (hpt.trans hY.symm))

theorem solution
    {q q' : ℕ} [Fact q.Prime] [Fact q'.Prime]
    {a b : ℚ} (Λ : Submodule ℤ ℍ[ℚ, a, b]) (m : ℕ) (hm : 3 ≤ m)
    (𝒪 : Type) [CommRing 𝒪] (hm' : IsUnit ((m : ℕ) : 𝒪))
    (star : ↥Λ → ↥Λ) (β : Fin (2 * 2) → ↥Λ)
    (Q : ∀ (S : Type) [CommRing S], PolarisedAbelianScheme 2 36 m S → Prop)
    (hQ : ∀ (S : Type) [CommRing S] (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of 𝒪))
      (X : PolarisedAbelianScheme 2 36 m S), QMStructure Λ star β X → Q S X)
    (hQbc : ∀ (S S' : Type) [CommRing S] [CommRing S'] (φ : S →+* S')
      (X : PolarisedAbelianScheme 2 36 m S) (X' : PolarisedAbelianScheme 2 36 m S'),
      PolarisedAbelianScheme.IsPullback φ X X' → Q S X → Q S' X')

    (M : Scheme.{0}) (πM : M ⟶ Spec (CommRingCat.of 𝒪))
    (pt : ∀ (S : Type) [CommRing S] (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of 𝒪)),
      PolarisedAbelianScheme.Satisfying 2 36 m Q S → SchemeHomOver s πM)
    (hM : PolarisedAbelianScheme.Satisfying.IsFineModuli 2 36 m Q M πM pt)

    (XU : ∀ U : M.affineOpens, PolarisedAbelianScheme 2 36 m Γ(M, U))
    (hQU : ∀ U : M.affineOpens, Q Γ(M, U) (XU U))
    (hXU : ∀ U : M.affineOpens, (pt Γ(M, U) (U.2.fromSpec ≫ πM) ⟨XU U, hQU U⟩).1 = U.2.fromSpec)

    (Z : M.affineOpens → Scheme.{0})
    (ζ : ∀ U : M.affineOpens, Z U ⟶ Spec (CommRingCat.of Γ(M, U)))
    (ptZ : ∀ (U : M.affineOpens) (T : Type) [CommRing T] (φ : Γ(M, U) →+* T) (X' : PolarisedAbelianScheme 2 36 m T),
      PolarisedAbelianScheme.IsPullback φ (XU U) X' → QMStructure Λ star β X' →
      SchemeHomOver (Spec.map (CommRingCat.ofHom φ)) (ζ U))
    (hζ : ∀ U, IsFinite (ζ U) ∧ LocallyOfFinitePresentation (ζ U))
    (hnat : ∀ (U : M.affineOpens) (T T' : Type) [CommRing T] [CommRing T'] (φ : Γ(M, U) →+* T) (φ' : Γ(M, U) →+* T')
      (ψ : T →+* T') (hψ : ψ.comp φ = φ')
      (X' : PolarisedAbelianScheme 2 36 m T) (X'' : PolarisedAbelianScheme 2 36 m T')
      (hX' : PolarisedAbelianScheme.IsPullback φ (XU U) X') (hX'' : PolarisedAbelianScheme.IsPullback φ' (XU U) X'')
      (s' : QMStructure Λ star β X') (s'' : QMStructure Λ star β X''),
      QMStructure.IsPullback ψ s' s'' →
      (ptZ U T' φ' X'' hX'' s'').1 = Spec.map (CommRingCat.ofHom ψ) ≫ (ptZ U T φ X' hX' s').1)
    (hsurjZ : ∀ (U : M.affineOpens) (T : Type) [CommRing T] (φ : Γ(M, U) →+* T) (X' : PolarisedAbelianScheme 2 36 m T)
      (hX' : PolarisedAbelianScheme.IsPullback φ (XU U) X') (z : SchemeHomOver (Spec.map (CommRingCat.ofHom φ)) (ζ U)),
      ∃ s' : QMStructure Λ star β X', ptZ U T φ X' hX' s' = z)
    (hinjZ : ∀ (U : M.affineOpens) (T : Type) [CommRing T] (φ : Γ(M, U) →+* T) (X' : PolarisedAbelianScheme 2 36 m T)
      (hX' : PolarisedAbelianScheme.IsPullback φ (XU U) X') (s' s'' : QMStructure Λ star β X'),
      ptZ U T φ X' hX' s' = ptZ U T φ X' hX' s'' → s' = s'') :
    ∃ (ρ : ∀ {U V : M.affineOpens}, U ≤ V → (Z U ⟶ Z V)),
      (∀ U : M.affineOpens, ρ (le_refl U) = 𝟙 (Z U)) ∧
      (∀ {U V W : M.affineOpens} (h₁ : U ≤ V) (h₂ : V ≤ W), ρ h₁ ≫ ρ h₂ = ρ (h₁.trans h₂)) ∧
      (∀ {U V : M.affineOpens} (h : U ≤ V),
        IsPullback (ρ h) (ζ U ≫ U.2.isoSpec.inv) (ζ V ≫ V.2.isoSpec.inv) (M.homOfLE h)) ∧
      (∀ {U V : M.affineOpens} (h : U ≤ V) (T : Type) [CommRing T] (φ : Γ(M, U) →+* T)
        (X' X'' : PolarisedAbelianScheme 2 36 m T)
        (hX' : PolarisedAbelianScheme.IsPullback φ (XU U) X')
        (hX'' : PolarisedAbelianScheme.IsPullback (φ.comp (M.presheaf.map (homOfLE (show (U.1 : M.Opens) ≤ V.1 from h)).op).hom) (XU V) X'')
        (s' : QMStructure Λ star β X') (s'' : QMStructure Λ star β X''), QMStructure.Iso s' s'' →
        (ptZ U T φ X' hX' s').1 ≫ ρ h = (ptZ V T (φ.comp (M.presheaf.map (homOfLE (show (U.1 : M.Opens) ≤ V.1 from h)).op).hom) X'' hX'' s'').1) := by
  classical

  let PT : ∀ {U V : M.affineOpens}, U ≤ V → (Z U ⟶ Z V) → Prop := fun {U V} h r =>
    ∀ (T : Type) [CommRing T] (φ : Γ(M, U) →+* T) (X' X'' : PolarisedAbelianScheme 2 36 m T)
      (hX' : PolarisedAbelianScheme.IsPullback φ (XU U) X')
      (hX'' : PolarisedAbelianScheme.IsPullback (φ.comp (M.presheaf.map (homOfLE (show (U.1 : M.Opens) ≤ V.1 from h)).op).hom) (XU V) X'')
      (s' : QMStructure Λ star β X') (s'' : QMStructure Λ star β X''), QMStructure.Iso s' s'' →
      (ptZ U T φ X' hX' s').1 ≫ r = (ptZ V T (φ.comp (M.presheaf.map (homOfLE (show (U.1 : M.Opens) ≤ V.1 from h)).op).hom) X'' hX'' s'').1

  let SQ : ∀ {U V : M.affineOpens}, U ≤ V → (Z U ⟶ Z V) → Prop := fun {U V} h r =>
    IsPullback r (ζ U ≫ U.2.isoSpec.inv) (ζ V ≫ V.2.isoSpec.inv) (M.homOfLE h)

  have hmU : ∀ U : M.affineOpens, IsUnit ((m : ℕ) : Γ(M, U)) := fun U => by
    have := hm'.map ((Scheme.ΓSpecIso (CommRingCat.of 𝒪)).inv ≫ πM.appLE ⊤ U.1 le_top).hom
    rwa [map_natCast] at this

  have PT_id : ∀ U : M.affineOpens, PT (le_refl U) (𝟙 (Z U)) := by
    intro U T _ φ X' X'' hX' hX'' s' s'' hiso
    rw [Category.comp_id]

    have hres : (M.presheaf.map (homOfLE (show (U.1 : M.Opens) ≤ U.1 from (le_refl U))).op).hom = RingHom.id _ := by
      have : (homOfLE (show (U.1 : M.Opens) ≤ U.1 from le_refl U)) = 𝟙 _ := Subsingleton.elim _ _
      rw [this, op_id, M.presheaf.map_id]; rfl
    have hφ : φ.comp (M.presheaf.map (homOfLE (show (U.1 : M.Opens) ≤ U.1 from (le_refl U))).op).hom = φ := by rw [hres, RingHom.comp_id]

    have hgen : ∀ (φ₁ φ₂ : Γ(M, U) →+* T) (e : φ₁ = φ₂) (h₁ : PolarisedAbelianScheme.IsPullback φ₁ (XU U) X''),
        (ptZ U T φ₁ X'' h₁ s'').1 = (ptZ U T φ₂ X'' (e ▸ h₁) s'').1 := by
      intro φ₁ φ₂ e h₁; subst e; rfl
    rw [hgen _ _ hφ hX'']
    congr 1
    exact AlgebraicGeometry.PolarisedAbelianScheme.QMStructure.ptZ_eq_of_iso_of_isPullback_of_isPullback hm
      (hmU U) (XU U) (ζ U) (ptZ U) (hnat U)
      T φ X' X'' hX' (hφ ▸ hX'') s' s'' hiso

  have PAS_iso_symm : ∀ {S : Type} [CommRing S] {u v : PolarisedAbelianScheme 2 36 m S},
      PolarisedAbelianScheme.Iso u v → PolarisedAbelianScheme.Iso v u :=
    fun {S} _ {u v} h => (AlgebraicGeometry.PolarisedAbelianScheme.Iso.refl_symm_trans (S := S)).2.1 u v h
  have QM_iso_symm : ∀ {S : Type} [CommRing S] {X Y : PolarisedAbelianScheme 2 36 m S}
      {s : QMStructure Λ star β X} {t : QMStructure Λ star β Y}, QMStructure.Iso s t → QMStructure.Iso t s :=
    fun {S} _ {X Y} {s t} h =>
      (AlgebraicGeometry.PolarisedAbelianScheme.QMStructure.Iso.refl_symm_trans (Λ := Λ) (star := star) (β := β) (S := S)).2.1 X Y s t h
  have QM_iso_trans : ∀ {S : Type} [CommRing S] {X Y W : PolarisedAbelianScheme 2 36 m S}
      {s : QMStructure Λ star β X} {t : QMStructure Λ star β Y} {w : QMStructure Λ star β W},
      QMStructure.Iso s t → QMStructure.Iso t w → QMStructure.Iso s w :=
    fun {S} _ {X Y W} {s t w} h₁ h₂ =>
      (AlgebraicGeometry.PolarisedAbelianScheme.QMStructure.Iso.refl_symm_trans (Λ := Λ) (star := star) (β := β) (S := S)).2.2 X Y W s t w h₁ h₂

  have ptZ_congr : ∀ (U : M.affineOpens) (T : Type) [CommRing T] (φ₁ φ₂ : Γ(M, U) →+* T) (e : φ₁ = φ₂)
      (X'' : PolarisedAbelianScheme 2 36 m T) (h₁ : PolarisedAbelianScheme.IsPullback φ₁ (XU U) X'')
      (h₂ : PolarisedAbelianScheme.IsPullback φ₂ (XU U) X'') (s'' : QMStructure Λ star β X''),
      (ptZ U T φ₁ X'' h₁ s'').1 = (ptZ U T φ₂ X'' h₂ s'').1 := by
    intro U T _ φ₁ φ₂ e X'' h₁ h₂ s''; subst e; rfl

  have res_comp : ∀ {U V W : M.affineOpens} (h₁ : U ≤ V) (h₂ : V ≤ W),
      ((M.presheaf.map (homOfLE (show (U.1 : M.Opens) ≤ V.1 from h₁)).op).hom).comp (M.presheaf.map (homOfLE (show (V.1 : M.Opens) ≤ W.1 from h₂)).op).hom = (M.presheaf.map (homOfLE (show (U.1 : M.Opens) ≤ W.1 from (h₁.trans h₂))).op).hom := by
    intro U V W h₁ h₂
    rw [← CommRingCat.hom_comp, ← M.presheaf.map_comp, ← op_comp]
    rfl
  have PAS_iso_refl : ∀ {S : Type} [CommRing S] (u : PolarisedAbelianScheme 2 36 m S), PolarisedAbelianScheme.Iso u u :=
    fun {S} _ u => (AlgebraicGeometry.PolarisedAbelianScheme.Iso.refl_symm_trans (S := S)).1 u

  have samePt_iso : ∀ (U : M.affineOpens) (T : Type) [CommRing T] (φ : Γ(M, U) →+* T)
      (X₁' X₂' : PolarisedAbelianScheme 2 36 m T)
      (h₁ : PolarisedAbelianScheme.IsPullback φ (XU U) X₁') (h₂ : PolarisedAbelianScheme.IsPullback φ (XU U) X₂')
      (s₁ : QMStructure Λ star β X₁') (s₂ : QMStructure Λ star β X₂'),
      (ptZ U T φ X₁' h₁ s₁).1 = (ptZ U T φ X₂' h₂ s₂).1 → QMStructure.Iso s₁ s₂ := by
    intro U T _ φ X₁' X₂' h₁ h₂ s₁ s₂ heq
    have hIso : PolarisedAbelianScheme.Iso X₁' X₂' :=
      AlgebraicGeometry.PolarisedAbelianScheme.Iso.baseChange φ (XU U) (XU U) X₁' X₂' (PAS_iso_refl (XU U)) h₁ h₂
    obtain ⟨s₁', hs₁'⟩ := AlgebraicGeometry.PolarisedAbelianScheme.QMStructure.exists_iso_of_polarisedAbelianScheme_iso hIso s₁
    have hpt : ptZ U T φ X₁' h₁ s₁ = ptZ U T φ X₂' h₂ s₁' :=
      AlgebraicGeometry.PolarisedAbelianScheme.QMStructure.ptZ_eq_of_iso_of_isPullback_of_isPullback hm (hmU U) (XU U) (ζ U) (ptZ U) (hnat U) T φ X₁' X₂' h₁ h₂ s₁ s₁' hs₁'
    have : s₁' = s₂ := hinjZ U T φ X₂' h₂ s₁' s₂ (Subtype.ext (by rw [← hpt]; exact heq))
    subst this
    exact hs₁'

  have partner : ∀ {U V : M.affineOpens} (h : U ≤ V) (T : Type) [CommRing T] (φ : Γ(M, U) →+* T)
      (X' : PolarisedAbelianScheme 2 36 m T) (hX' : PolarisedAbelianScheme.IsPullback φ (XU U) X')
      (s' : QMStructure Λ star β X'),
      ∃ (X'' : PolarisedAbelianScheme 2 36 m T)
        (hX'' : PolarisedAbelianScheme.IsPullback (φ.comp (M.presheaf.map (homOfLE (show (U.1 : M.Opens) ≤ V.1 from h)).op).hom) (XU V) X'')
        (s'' : QMStructure Λ star β X''), QMStructure.Iso s' s'' := by
    intro U V h T _ φ X' hX' s'
    obtain ⟨X₁, -, hX₁pb, -, hX₁iso⟩ := PQH9.exists_isPullback_map_homOfLE_and_pt_eq_fromSpec_satisfying hM hQbc V.2 U.2 h (XU V) (hQU V) (hXU V)
    have hIso₁ : PolarisedAbelianScheme.Iso X₁ (XU U) := hX₁iso (XU U) (hQU U) (hXU U)
    obtain ⟨X'', hX''⟩ := AlgebraicGeometry.PolarisedAbelianScheme.exists_isPullback φ X₁
    have hX''V : PolarisedAbelianScheme.IsPullback (φ.comp (M.presheaf.map (homOfLE (show (U.1 : M.Opens) ≤ V.1 from h)).op).hom) (XU V) X'' :=
      AlgebraicGeometry.PolarisedAbelianScheme.IsPullback.trans _ _ (XU V) X₁ X'' hX₁pb hX''
    have hIso' : PolarisedAbelianScheme.Iso X' X'' :=
      PAS_iso_symm (AlgebraicGeometry.PolarisedAbelianScheme.Iso.baseChange φ X₁ (XU U) X'' X' hIso₁ hX'' hX')
    obtain ⟨s'', hs''⟩ := AlgebraicGeometry.PolarisedAbelianScheme.QMStructure.exists_iso_of_polarisedAbelianScheme_iso hIso' s'
    exact ⟨X'', hX''V, s'', hs''⟩

  have K1 : ∀ {U V : M.affineOpens} (h : U ≤ V) (r₁ r₂ : Z U ⟶ Z V), PT h r₁ → PT h r₂ → r₁ = r₂ := by
    intro U V h r₁ r₂ H₁ H₂
    apply (Z U).affineOpenCover.openCover.hom_ext
    intro i

    let Rᵢ : CommRingCat := (Z U).affineOpenCover.X i
    let x : Spec Rᵢ ⟶ Z U := (Z U).affineOpenCover.f i

    let φ' : CommRingCat.of Γ(M, U) ⟶ Rᵢ := Spec.preimage (x ≫ ζ U)
    have hφ' : Spec.map φ' = x ≫ ζ U := Spec.map_preimage _
    let φ : Γ(M, U) →+* Rᵢ := φ'.hom
    have hxφ : x ≫ ζ U = Spec.map (CommRingCat.ofHom φ) := by rw [CommRingCat.ofHom_hom, hφ']
    obtain ⟨X', hX'⟩ := AlgebraicGeometry.PolarisedAbelianScheme.exists_isPullback φ (XU U)
    obtain ⟨s', hs'⟩ := hsurjZ U Rᵢ φ X' hX' ⟨x, hxφ⟩
    obtain ⟨X'', hX'', s'', hiso⟩ := partner h Rᵢ φ X' hX' s'
    have e1 := H₁ Rᵢ φ X' X'' hX' hX'' s' s'' hiso
    have e2 := H₂ Rᵢ φ X' X'' hX' hX'' s' s'' hiso
    have hx : (ptZ U Rᵢ φ X' hX' s').1 = x := congrArg Subtype.val hs'
    show x ≫ r₁ = x ≫ r₂
    rw [← hx, e1, ← e2]
  have PT_comp : ∀ {U V W : M.affineOpens} (h₁ : U ≤ V) (h₂ : V ≤ W) (r₁ : Z U ⟶ Z V) (r₂ : Z V ⟶ Z W),
      PT h₁ r₁ → PT h₂ r₂ → PT (h₁.trans h₂) (r₁ ≫ r₂) := by
    intro U V W h₁ h₂ r₁ r₂ H₁ H₂ T _ φ X' X''' hX' hX''' s' s''' hiso

    obtain ⟨X₁, -, hX₁pb, -, hX₁iso⟩ := PQH9.exists_isPullback_map_homOfLE_and_pt_eq_fromSpec_satisfying hM hQbc V.2 U.2 h₁ (XU V) (hQU V) (hXU V)
    have hIso₁ : PolarisedAbelianScheme.Iso X₁ (XU U) := hX₁iso (XU U) (hQU U) (hXU U)
    obtain ⟨X'', hX''⟩ := AlgebraicGeometry.PolarisedAbelianScheme.exists_isPullback φ X₁
    have hX''V : PolarisedAbelianScheme.IsPullback (φ.comp (M.presheaf.map (homOfLE (show (U.1 : M.Opens) ≤ V.1 from h₁)).op).hom) (XU V) X'' :=
      AlgebraicGeometry.PolarisedAbelianScheme.IsPullback.trans _ _ (XU V) X₁ X'' hX₁pb hX''
    have hIso' : PolarisedAbelianScheme.Iso X' X'' :=
      PAS_iso_symm (AlgebraicGeometry.PolarisedAbelianScheme.Iso.baseChange φ X₁ (XU U) X'' X' hIso₁ hX'' hX')
    obtain ⟨s'', hs''⟩ := AlgebraicGeometry.PolarisedAbelianScheme.QMStructure.exists_iso_of_polarisedAbelianScheme_iso hIso' s'

    have e1 := H₁ T φ X' X'' hX' hX''V s' s'' hs''
    have hcast : PolarisedAbelianScheme.IsPullback ((φ.comp (M.presheaf.map (homOfLE (show (U.1 : M.Opens) ≤ V.1 from h₁)).op).hom).comp (M.presheaf.map (homOfLE (show (V.1 : M.Opens) ≤ W.1 from h₂)).op).hom) (XU W) X''' := by
      rw [RingHom.comp_assoc, res_comp h₁ h₂]; exact hX'''
    have e2 := H₂ T (φ.comp (M.presheaf.map (homOfLE (show (U.1 : M.Opens) ≤ V.1 from h₁)).op).hom) X'' X''' hX''V hcast s'' s''' (QM_iso_trans (QM_iso_symm hs'') hiso)
    rw [← Category.assoc, e1, e2]
    exact ptZ_congr W T _ _ (by rw [RingHom.comp_assoc, res_comp h₁ h₂]) X''' hcast hX''' s'''

  have QM_iso_bc : ∀ {S S' : Type} [CommRing S] [CommRing S'] (ψ : S →+* S')
      {X Y : PolarisedAbelianScheme 2 36 m S} {X' Y' : PolarisedAbelianScheme 2 36 m S'}
      {s : QMStructure Λ star β X} {t : QMStructure Λ star β Y} {s' : QMStructure Λ star β X'} {t' : QMStructure Λ star β Y'},
      QMStructure.Iso s t → QMStructure.IsPullback ψ s s' → QMStructure.IsPullback ψ t t' → QMStructure.Iso s' t' :=
    fun {S S'} _ _ ψ {X Y X' Y'} {s t s' t'} h h₁ h₂ =>
      AlgebraicGeometry.PolarisedAbelianScheme.QMStructure.Iso.of_isPullback_of_isPullback ψ h h₁ h₂
  have PAS_iso_trans : ∀ {S : Type} [CommRing S] {u v w : PolarisedAbelianScheme 2 36 m S},
      PolarisedAbelianScheme.Iso u v → PolarisedAbelianScheme.Iso v w → PolarisedAbelianScheme.Iso u w :=
    fun {S} _ {u v w} h₁ h₂ => (AlgebraicGeometry.PolarisedAbelianScheme.Iso.refl_symm_trans (S := S)).2.2 u v w h₁ h₂

  have K2 : ∀ {U V : M.affineOpens} (h : U ≤ V), ∃ r : Z U ⟶ Z V, SQ h r ∧ PT h r := by
    intro U V h

    let bV : Spec (CommRingCat.of Γ(M, U)) ⟶ Spec (CommRingCat.of Γ(M, V)) := Spec.map (CommRingCat.ofHom (M.presheaf.map (homOfLE (show (U.1 : M.Opens) ≤ V.1 from h)).op).hom)
    let ζ₂ : pullback (ζ V) bV ⟶ Spec (CommRingCat.of Γ(M, U)) := pullback.snd (ζ V) bV
    have hb : ∀ (T : Type) [CommRing T] (φ : Γ(M, U) →+* T),
        Spec.map (CommRingCat.ofHom φ) ≫ bV = Spec.map (CommRingCat.ofHom (φ.comp (M.presheaf.map (homOfLE (show (U.1 : M.Opens) ≤ V.1 from h)).op).hom)) := by
      intro T _ φ; show _ ≫ Spec.map _ = _; rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]

    choose Xc hXc using fun (T : Type) (_i : CommRing T) (φ : Γ(M, U) →+* T) => AlgebraicGeometry.PolarisedAbelianScheme.exists_isPullback φ (XU U)
    choose Yc hYc using fun (T : Type) (_i : CommRing T) (φ : Γ(M, U) →+* T) => AlgebraicGeometry.PolarisedAbelianScheme.exists_isPullback (φ.comp (M.presheaf.map (homOfLE (show (U.1 : M.Opens) ≤ V.1 from h)).op).hom) (XU V)
    have IsoXY : ∀ (T : Type) (_i : CommRing T) (φ : Γ(M, U) →+* T), PolarisedAbelianScheme.Iso (Xc T _i φ) (Yc T _i φ) := by
      intro T _ φ
      obtain ⟨X₁, -, hX₁pb, -, hX₁iso⟩ := PQH9.exists_isPullback_map_homOfLE_and_pt_eq_fromSpec_satisfying hM hQbc V.2 U.2 h (XU V) (hQU V) (hXU V)
      obtain ⟨X₃, hX₃⟩ := AlgebraicGeometry.PolarisedAbelianScheme.exists_isPullback φ X₁
      exact PAS_iso_trans
        (PAS_iso_symm (AlgebraicGeometry.PolarisedAbelianScheme.Iso.baseChange φ X₁ (XU U) X₃ (Xc T _ φ) (hX₁iso (XU U) (hQU U) (hXU U)) hX₃ (hXc T _ φ)))
        (AlgebraicGeometry.PolarisedAbelianScheme.Iso.baseChange _ (XU V) (XU V) X₃ (Yc T _ φ) (PAS_iso_refl (XU V))
          (AlgebraicGeometry.PolarisedAbelianScheme.IsPullback.trans _ _ (XU V) X₁ X₃ hX₁pb hX₃) (hYc T _ φ))
    choose sOf hsOf using fun (T : Type) (_i : CommRing T) (φ : Γ(M, U) →+* T)
      (x : SchemeHomOver (Spec.map (CommRingCat.ofHom φ)) (ζ U)) => hsurjZ U T φ (Xc T _i φ) (hXc T _i φ) x
    choose tOf htOf using fun (T : Type) (_i : CommRing T) (φ : Γ(M, U) →+* T)
      (y : SchemeHomOver (Spec.map (CommRingCat.ofHom (φ.comp (M.presheaf.map (homOfLE (show (U.1 : M.Opens) ≤ V.1 from h)).op).hom))) (ζ V)) =>
        hsurjZ V T (φ.comp (M.presheaf.map (homOfLE (show (U.1 : M.Opens) ≤ V.1 from h)).op).hom) (Yc T _i φ) (hYc T _i φ) y
    choose fwd hfwd using fun (T : Type) (_i : CommRing T) (φ : Γ(M, U) →+* T) (s' : QMStructure Λ star β (Xc T _i φ)) =>
      AlgebraicGeometry.PolarisedAbelianScheme.QMStructure.exists_iso_of_polarisedAbelianScheme_iso (IsoXY T _i φ) s'
    choose bwd hbwd using fun (T : Type) (_i : CommRing T) (φ : Γ(M, U) →+* T) (t : QMStructure Λ star β (Yc T _i φ)) =>
      AlgebraicGeometry.PolarisedAbelianScheme.QMStructure.exists_iso_of_polarisedAbelianScheme_iso (PAS_iso_symm (IsoXY T _i φ)) t

    let F : ∀ (T : Type) [CommRing T] (φ : Γ(M, U) →+* T),
        SchemeHomOver (Spec.map (CommRingCat.ofHom φ)) (ζ U) → SchemeHomOver (Spec.map (CommRingCat.ofHom φ)) ζ₂ :=
      fun T _ φ x => ⟨pullback.lift (ptZ V T (φ.comp (M.presheaf.map (homOfLE (show (U.1 : M.Opens) ≤ V.1 from h)).op).hom) (Yc T _ φ) (hYc T _ φ) (fwd T _ φ (sOf T _ φ x))).1
          (Spec.map (CommRingCat.ofHom φ))
          (by rw [(ptZ V T (φ.comp (M.presheaf.map (homOfLE (show (U.1 : M.Opens) ≤ V.1 from h)).op).hom) (Yc T _ φ) (hYc T _ φ) (fwd T _ φ (sOf T _ φ x))).2, hb]),
        pullback.lift_snd _ _ _⟩
    let G : ∀ (T : Type) [CommRing T] (φ : Γ(M, U) →+* T),
        SchemeHomOver (Spec.map (CommRingCat.ofHom φ)) ζ₂ → SchemeHomOver (Spec.map (CommRingCat.ofHom φ)) (ζ U) :=
      fun T _ φ z => ptZ U T φ (Xc T _ φ) (hXc T _ φ)
        (bwd T _ φ (tOf T _ φ ⟨z.1 ≫ pullback.fst (ζ V) bV, by rw [Category.assoc, pullback.condition, ← Category.assoc, z.2, hb]⟩))

    have hFG : ∀ (T : Type) [CommRing T] (φ : Γ(M, U) →+* T) (x : SchemeHomOver (Spec.map (CommRingCat.ofHom φ)) (ζ U)),
        G T φ (F T φ x) = x := by
      intro T _ φ x

      have hy : (⟨(F T φ x).1 ≫ pullback.fst (ζ V) bV, by
            rw [Category.assoc, pullback.condition, ← Category.assoc, (F T φ x).2, hb]⟩ :
            SchemeHomOver (Spec.map (CommRingCat.ofHom (φ.comp (M.presheaf.map (homOfLE (show (U.1 : M.Opens) ≤ V.1 from h)).op).hom))) (ζ V)) =
          ptZ V T (φ.comp (M.presheaf.map (homOfLE (show (U.1 : M.Opens) ≤ V.1 from h)).op).hom) (Yc T _ φ) (hYc T _ φ) (fwd T _ φ (sOf T _ φ x)) :=
        Subtype.ext (pullback.lift_fst _ _ _)
      have ht : tOf T _ φ ⟨(F T φ x).1 ≫ pullback.fst (ζ V) bV, by
            rw [Category.assoc, pullback.condition, ← Category.assoc, (F T φ x).2, hb]⟩ =
          fwd T _ φ (sOf T _ φ x) :=
        hinjZ V T _ (Yc T _ φ) (hYc T _ φ) _ _ ((htOf T _ φ _).trans hy)
      show ptZ U T φ (Xc T _ φ) (hXc T _ φ) (bwd T _ φ (tOf T _ φ ⟨(F T φ x).1 ≫ pullback.fst (ζ V) bV, _⟩)) = x
      rw [ht]
      exact (AlgebraicGeometry.PolarisedAbelianScheme.QMStructure.ptZ_eq_of_iso_of_isPullback_of_isPullback hm (hmU U) (XU U) (ζ U) (ptZ U) (hnat U) T φ _ _ (hXc T _ φ) (hXc T _ φ)
        (sOf T _ φ x) _ (QM_iso_trans (hfwd T _ φ _) (hbwd T _ φ _))).symm.trans (hsOf T _ φ x)
    have hGF : ∀ (T : Type) [CommRing T] (φ : Γ(M, U) →+* T) (z : SchemeHomOver (Spec.map (CommRingCat.ofHom φ)) ζ₂),
        F T φ (G T φ z) = z := by
      intro T _ φ z
      apply Subtype.ext
      show pullback.lift (ptZ V T (φ.comp (M.presheaf.map (homOfLE (show (U.1 : M.Opens) ≤ V.1 from h)).op).hom) (Yc T _ φ) (hYc T _ φ) (fwd T _ φ (sOf T _ φ (G T φ z)))).1
          (Spec.map (CommRingCat.ofHom φ)) _ = z.1

      have hs : sOf T _ φ (G T φ z) = bwd T _ φ (tOf T _ φ ⟨z.1 ≫ pullback.fst (ζ V) bV, by
            rw [Category.assoc, pullback.condition, ← Category.assoc, z.2, hb]⟩) :=
        hinjZ U T φ (Xc T _ φ) (hXc T _ φ) _ _ (hsOf T _ φ (G T φ z))
      have hpt : ptZ V T (φ.comp (M.presheaf.map (homOfLE (show (U.1 : M.Opens) ≤ V.1 from h)).op).hom) (Yc T _ φ) (hYc T _ φ) (fwd T _ φ (sOf T _ φ (G T φ z))) =
          ptZ V T (φ.comp (M.presheaf.map (homOfLE (show (U.1 : M.Opens) ≤ V.1 from h)).op).hom) (Yc T _ φ) (hYc T _ φ) (tOf T _ φ ⟨z.1 ≫ pullback.fst (ζ V) bV, by
            rw [Category.assoc, pullback.condition, ← Category.assoc, z.2, hb]⟩) := by
        rw [hs]
        exact (AlgebraicGeometry.PolarisedAbelianScheme.QMStructure.ptZ_eq_of_iso_of_isPullback_of_isPullback hm (hmU V) (XU V) (ζ V) (ptZ V) (hnat V) T _ _ _ (hYc T _ φ) (hYc T _ φ) _ _
          (QM_iso_trans (hbwd T _ φ _) (hfwd T _ φ _))).symm
      apply pullback.hom_ext
      · rw [pullback.lift_fst, hpt, htOf]
      · rw [pullback.lift_snd, z.2]

    let e : ∀ (T : Type) [CommRing T] (φ : Γ(M, U) →+* T),
        SchemeHomOver (Spec.map (CommRingCat.ofHom φ)) (ζ U) ≃ SchemeHomOver (Spec.map (CommRingCat.ofHom φ)) ζ₂ :=
      fun T _ φ => ⟨F T φ, G T φ, hFG T φ, hGF T φ⟩
    have he : ∀ (T T' : Type) [CommRing T] [CommRing T'] (φ : Γ(M, U) →+* T) (ψ : T →+* T')
        (x : SchemeHomOver (Spec.map (CommRingCat.ofHom φ)) (ζ U)),
        (e T' (ψ.comp φ) ⟨Spec.map (CommRingCat.ofHom ψ) ≫ x.1, by
            rw [Category.assoc, x.2, ← Spec.map_comp, ← CommRingCat.ofHom_comp]⟩).1 =
          Spec.map (CommRingCat.ofHom ψ) ≫ (e T φ x).1 := by
      intro T T' _ _ φ ψ x

      let x' : SchemeHomOver (Spec.map (CommRingCat.ofHom (ψ.comp φ))) (ζ U) :=
        ⟨Spec.map (CommRingCat.ofHom ψ) ≫ x.1, by rw [Category.assoc, x.2, ← Spec.map_comp, ← CommRingCat.ofHom_comp]⟩
      let s₀ := sOf T _ φ x
      let t₀ := fwd T _ φ s₀
      let s'c := sOf T' _ (ψ.comp φ) x'
      let t' := fwd T' _ (ψ.comp φ) s'c
      show pullback.lift (ptZ V T' ((ψ.comp φ).comp (M.presheaf.map (homOfLE (show (U.1 : M.Opens) ≤ V.1 from h)).op).hom) (Yc T' _ (ψ.comp φ)) (hYc T' _ (ψ.comp φ)) t').1 _ _ =
        Spec.map (CommRingCat.ofHom ψ) ≫ pullback.lift (ptZ V T (φ.comp (M.presheaf.map (homOfLE (show (U.1 : M.Opens) ≤ V.1 from h)).op).hom) (Yc T _ φ) (hYc T _ φ) t₀).1 _ _

      obtain ⟨Xcψ, hXcψ⟩ := AlgebraicGeometry.PolarisedAbelianScheme.exists_isPullback ψ (Xc T _ φ)
      have hXcψU : PolarisedAbelianScheme.IsPullback (ψ.comp φ) (XU U) Xcψ := AlgebraicGeometry.PolarisedAbelianScheme.IsPullback.trans _ _ (XU U) (Xc T _ φ) Xcψ (hXc T _ φ) hXcψ
      obtain ⟨sψ, hsψ⟩ := AlgebraicGeometry.PolarisedAbelianScheme.QMStructure.exists_isPullback ψ hXcψ s₀
      obtain ⟨Ycψ, hYcψ⟩ := AlgebraicGeometry.PolarisedAbelianScheme.exists_isPullback ψ (Yc T _ φ)
      have hYcψV : PolarisedAbelianScheme.IsPullback (ψ.comp (φ.comp (M.presheaf.map (homOfLE (show (U.1 : M.Opens) ≤ V.1 from h)).op).hom)) (XU V) Ycψ :=
        AlgebraicGeometry.PolarisedAbelianScheme.IsPullback.trans _ _ (XU V) (Yc T _ φ) Ycψ (hYc T _ φ) hYcψ
      obtain ⟨tψ, htψ⟩ := AlgebraicGeometry.PolarisedAbelianScheme.QMStructure.exists_isPullback ψ hYcψ t₀

      have nU := hnat U T T' φ (ψ.comp φ) ψ rfl (Xc T _ φ) Xcψ (hXc T _ φ) hXcψU s₀ sψ hsψ
      have nV := hnat V T T' (φ.comp (M.presheaf.map (homOfLE (show (U.1 : M.Opens) ≤ V.1 from h)).op).hom) (ψ.comp (φ.comp (M.presheaf.map (homOfLE (show (U.1 : M.Opens) ≤ V.1 from h)).op).hom)) ψ rfl (Yc T _ φ) Ycψ (hYc T _ φ) hYcψV t₀ tψ htψ

      have a1 : (ptZ U T' (ψ.comp φ) (Xc T' _ (ψ.comp φ)) (hXc T' _ (ψ.comp φ)) s'c).1 = Spec.map (CommRingCat.ofHom ψ) ≫ x.1 :=
        congrArg Subtype.val (hsOf T' _ (ψ.comp φ) x')
      have a2 : (ptZ U T φ (Xc T _ φ) (hXc T _ φ) s₀).1 = x.1 := congrArg Subtype.val (hsOf T _ φ x)
      have i1 : QMStructure.Iso s'c sψ :=
        samePt_iso U T' (ψ.comp φ) _ _ (hXc T' _ (ψ.comp φ)) hXcψU s'c sψ (by rw [a1, nU, a2])
      have i2 : QMStructure.Iso sψ tψ := QM_iso_bc ψ (hfwd T _ φ s₀) hsψ htψ
      have i3 : QMStructure.Iso t' tψ := QM_iso_trans (QM_iso_trans (QM_iso_symm (hfwd T' _ (ψ.comp φ) s'c)) i1) i2

      apply pullback.hom_ext
      · rw [pullback.lift_fst, Category.assoc, pullback.lift_fst, ← nV]
        have hcast : PolarisedAbelianScheme.IsPullback (ψ.comp (φ.comp (M.presheaf.map (homOfLE (show (U.1 : M.Opens) ≤ V.1 from h)).op).hom)) (XU V) (Yc T' _ (ψ.comp φ)) := by
          rw [← RingHom.comp_assoc]; exact hYc T' _ (ψ.comp φ)
        rw [ptZ_congr V T' ((ψ.comp φ).comp (M.presheaf.map (homOfLE (show (U.1 : M.Opens) ≤ V.1 from h)).op).hom) (ψ.comp (φ.comp (M.presheaf.map (homOfLE (show (U.1 : M.Opens) ≤ V.1 from h)).op).hom)) (RingHom.comp_assoc _ _ _).symm
          (Yc T' _ (ψ.comp φ)) (hYc T' _ (ψ.comp φ)) hcast t']
        exact congrArg Subtype.val
          (AlgebraicGeometry.PolarisedAbelianScheme.QMStructure.ptZ_eq_of_iso_of_isPullback_of_isPullback hm (hmU V) (XU V) (ζ V) (ptZ V) (hnat V) T' _ _ _ hcast hYcψV t' tψ i3)
      · rw [pullback.lift_snd, Category.assoc, pullback.lift_snd, ← Spec.map_comp, ← CommRingCat.ofHom_comp]

    obtain ⟨ε, hε₁, hε₂, -⟩ := AlgebraicGeometry.Scheme.exists_iso_over_of_forall_schemeHomOver_equiv (ζ U) ζ₂ e he
    refine ⟨ε.hom ≫ pullback.fst (ζ V) bV, ?_, ?_⟩
    ·
      have sq1 : IsPullback ε.hom (ζ U) ζ₂ (𝟙 _) := IsPullback.of_horiz_isIso ⟨by rw [hε₁, Category.comp_id]⟩
      have sq2 : IsPullback (pullback.fst (ζ V) bV) ζ₂ (ζ V) bV := IsPullback.of_hasPullback _ _
      have sq12 : IsPullback (ε.hom ≫ pullback.fst (ζ V) bV) (ζ U) (ζ V) bV := by
        simpa using sq1.paste_horiz sq2
      have hbot : bV ≫ V.2.isoSpec.inv = U.2.isoSpec.inv ≫ M.homOfLE h := by
        rw [← cancel_mono V.1.ι, Category.assoc, Category.assoc, ← IsAffineOpen.fromSpec,
          Scheme.homOfLE_ι, ← IsAffineOpen.fromSpec]
        exact IsAffineOpen.map_fromSpec V.2 U.2 (homOfLE (show (U.1 : M.Opens) ≤ V.1 from h)).op
      have sq3 : IsPullback bV U.2.isoSpec.inv V.2.isoSpec.inv (M.homOfLE h) := IsPullback.of_vert_isIso ⟨hbot⟩
      exact sq12.paste_vert sq3
    ·
      intro T _ φ X' X'' hX' hX'' s' s'' hiso
      rw [← Category.assoc, hε₂ T φ (ptZ U T φ X' hX' s')]
      show (pullback.lift (ptZ V T (φ.comp (M.presheaf.map (homOfLE (show (U.1 : M.Opens) ≤ V.1 from h)).op).hom) (Yc T _ φ) (hYc T _ φ)
          (fwd T _ φ (sOf T _ φ (ptZ U T φ X' hX' s')))).1 _ _) ≫ pullback.fst (ζ V) bV = _
      rw [pullback.lift_fst]
      have i1 : QMStructure.Iso (sOf T _ φ (ptZ U T φ X' hX' s')) s' :=
        samePt_iso U T φ _ _ (hXc T _ φ) hX' _ _ (congrArg Subtype.val (hsOf T _ φ (ptZ U T φ X' hX' s')))
      have i2 : QMStructure.Iso (fwd T _ φ (sOf T _ φ (ptZ U T φ X' hX' s'))) s'' :=
        QM_iso_trans (QM_iso_trans (QM_iso_symm (hfwd T _ φ _)) i1) hiso
      exact congrArg Subtype.val
        (AlgebraicGeometry.PolarisedAbelianScheme.QMStructure.ptZ_eq_of_iso_of_isPullback_of_isPullback hm (hmU V) (XU V) (ζ V) (ptZ V) (hnat V) T _ _ _ (hYc T _ φ) hX'' _ _ i2)

  have key : ∀ {U V : M.affineOpens} (h : U ≤ V), ∃ r : Z U ⟶ Z V, SQ h r ∧ PT h r ∧ ∀ r' : Z U ⟶ Z V, PT h r' → r' = r := by
    intro U V h
    obtain ⟨r, hSQ, hPT⟩ := K2 h
    exact ⟨r, hSQ, hPT, fun r' h' => K1 h r' r h' hPT⟩
  refine ⟨fun h => (key h).choose, fun U => ?_, fun h₁ h₂ => ?_, fun h => (key h).choose_spec.1, fun h => ?_⟩
  · exact ((key (le_refl U)).choose_spec.2.2 _ (PT_id U)).symm
  · exact (key (h₁.trans h₂)).choose_spec.2.2 _
      (PT_comp h₁ h₂ _ _ (key h₁).choose_spec.2.1 (key h₂).choose_spec.2.1)
  · exact (key h).choose_spec.2.1

end S_CerednikDrinfeld_QM_exists_transition_isPullback_of_represents_qmStructure_affineOpens_satisfying
end P2MW
export P2MW.S_CerednikDrinfeld_QM_exists_transition_isPullback_of_represents_qmStructure_affineOpens_satisfying (solution)
