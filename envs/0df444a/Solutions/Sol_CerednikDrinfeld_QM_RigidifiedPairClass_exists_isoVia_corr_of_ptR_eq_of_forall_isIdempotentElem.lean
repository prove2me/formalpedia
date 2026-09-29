-- Prove2me | solution 1 for CerednikDrinfeld.QM.RigidifiedPairClass.exists_isoVia_corr_of_ptR_eq_of_forall_isIdempotentElem
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.141142+00:00
-- url     : https://prove2.me/submissions/2b2cea60-2e5d-52ba-aac5-9c5f09921b0b

import Definitions.Def_CerednikDrinfeld_QMRigidification
import Definitions.Def_CerednikDrinfeld_QMFineModuli
import Definitions.Def_CerednikDrinfeld_QMFineModuliT
import Definitions.Def_CerednikDrinfeld_FormalUpperHalfPlaneCharts
import Definitions.Def_CerednikDrinfeld_RigidifiedPairClassModel
import Theorems.Thm_CerednikDrinfeld_QM_RigidifiedPairClass_rel_equivalence
import Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_Rigidification_exists_forall_corr_mul_pow_eq_of_forall_isIdempotentElem
import Theorems.Thm_CerednikDrinfeld_QM_RigidifiedPairClass_exists_pullback_ptX_eq_specMap_comp
import Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_Rigidification_exists_isPullbackVia_of_isPullbackVia
import Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_exists_isPullbackVia_id_comp_eq_of_isPullbackVia_of_isPullbackVia_of_isUnit
import Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_Rigidification_exists_corr_of_isoVia
import Theorems.Thm_CerednikDrinfeld_QM_RigidifiedPairClass_ptR_eq_of_isoVia_of_corr
import Theorems.Thm_CerednikDrinfeld_QM_RigidifiedPairClass_map_ptR_eq_ptR_of_isPullbackVia
import Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_WithFullLevel_eq_refl_of_mapPt_eq_of_three_le
import Theorems.Thm_AlgebraicGeometry_Scheme_section_ext_and_exists_section_of_isLocalizationAway_of_span_eq_top
import Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_IsPullbackVia_comp
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_QM_RigidifiedPairClass_exists_isoVia_corr_of_ptR_eq_of_forall_isIdempotentElem
p2m_attr_erase "instance" "instTopologicallyFGOfFiniteType GoodReductionJacobian.RelativeGroupLaw.isIso_endKerStr_schemeHomOverId AlgebraicGeometry.OModulePresheaf.isScalarTower AlgebraicGeometry.Scheme.OrderedAffineCover.instLinearOrder AlgebraicGeometry.OModulePresheaf.module AlgebraicGeometry.Scheme.OrderedAffineCover.instFintype AlgebraicGeometry.Scheme.OrderedAffineCover.instFintypeIdx AlgebraicGeometry.OModulePresheaf.addCommGroup AlgebraicGeometry.Scheme.OrderedAffineCover.instDecidableEqIdx AlgebraicGeometry.OModulePresheaf.moduleSections TwoChartCech.Sections.M0_moduleA TwoChartCech.Sections.M1_module TwoChartCech.Cover.A01_algebra TwoChartCech.Cover.A0_algebra TwoChartCech.Cover.A1_commRing TwoChartCech.Cover.A1_algebra TwoChartCech.Sections.M01_module TwoChartCech.Sections.M0_addCommGroup TwoChartCech.Sections.M0_tower TwoChartCech.Sections.M01_addCommGroup TwoChartCech.Cover.A0_commRing TwoChartCech.Sections.M1_tower TwoChartCech.Sections.M01_moduleA TwoChartCech.Sections.M0_module TwoChartCech.Sections.M1_moduleA TwoChartCech.Sections.M1_addCommGroup TwoChartCech.Cover.A01_commRing TwoChartCech.Sections.M01_tower CoherentBaseChange.TwoTermComplex.C0_module CoherentBaseChange.TwoTermComplex.C0_addCommGroup CoherentBaseChange.TwoTermComplex.C1_module CoherentBaseChange.TwoTermComplex.C1_addCommGroup CoherentBaseChange.TwoTermComplex.C0_free CoherentBaseChange.TwoTermComplex.C1_finite CoherentBaseChange.TwoTermComplex.C0_finite CoherentBaseChange.TwoTermComplex.C1_free AlgebraicGeometry.OModulePresheaf.instSubsingletonObjZero AlgebraicGeometry.Scheme.Modules.preservesBinaryProducts_opensMap AlgebraicGeometry.Scheme.Modules.pullback_monoidal AlgebraicGeometry.Scheme.Modules.sheafify_isLocalization'"
p2m_attr_erase "instance" "AlgebraicGeometry.Scheme.Modules.preservesTerminal_opensMap AlgebraicGeometry.Scheme.Modules.pullback₀_monoidal AlgebraicGeometry.Scheme.Modules.preservesFiniteProducts_opensMap AlgebraicGeometry.Scheme.Modules.instLiftingPresheafOfModulesSheafifyPresheafWOpensCarrierCarrierCommRingCatGrothendieckTopologyObjFunctorOppositeIsSheafSheafCompPullback₀Pullback PresheafOfModules.PullbackMonoidal.pullback_monoidal PresheafOfModules.PullbackMonoidal.isIso_δ PresheafOfModules.pushforward_laxMonoidal PresheafOfModules.PullbackMonoidal.isIso_η PresheafOfModules.free_monoidal PresheafOfModules.restrictScalars_laxMonoidal PresheafOfModules.PullbackMonoidal.isIso_δ_gS PresheafOfModules.pullback_oplaxMonoidal PresheafOfModules.PullbackMonoidal.instPreservesColimitsOfSizeCompOppositeCommRingCatRingCatForget₂RingHomCarrierCarrierPb PresheafOfModules.pullback_monoidal' AlgebraicGeometry.SmoothOfRelativeDimension.fiberToSpecResidueField AlgebraicGeometry.SmoothOfRelativeDimension.pullback_snd AlgebraicGeometry.SmoothOfRelativeDimension.pullback_fst AlgebraicGeometry.SmoothOfRelativeDimension.smooth_one AlgebraicGeometry.SmoothProperCurve.isIntegral_pullback_Spec_field AlgebraicGeometry.IsProper.fiberToSpecResidueField AlgebraicCurve.CurveModel.isProper AlgebraicCurve.CurveModel.isIntegral AlgebraicCurve.CurveModel.smooth AlgebraicGeometry.Scheme.LocalRepresentabilityULift.instIsLocallyInjectiveFunUliftYonedaGluedToSheaf AlgebraicGeometry.Scheme.LocalRepresentabilityULift.instIsLocallySurjectiveFunUliftYonedaGluedToSheafOfIsLocallySurjectiveZariskiTopologyDescFunctorOppositeType AlgebraicGeometry.Scheme.LocalRepresentabilityULift.instIsOpenImmersionToGlued AlgebraicGeometry.Scheme.LocalRepresentabilityULift.instIsIsoSheafZariskiTopologyTypeUliftYonedaGluedToSheaf AlgebraicGeometry.RelPicard.instIsOpenImmersionToGlued AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.instFundamentalIdentityOfSumRamificationInertia AlgebraicCurve.Place.instIsScalarTowerResidueFieldRestrictPushforward AlgebraicCurve.Place.instAlgebraResidueFieldRestrictPushforward AlgebraicCurve.Place.instIsLocalHomRestrictInclusion AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions"
p2m_attr_erase "instance" "PresheafOfModules.ExteriorPower.instModulePresheafAb AlgebraicGeometry.RelEffCartierDiv.subsingleton_of_degree_zero AlgebraicGeometry.RelEffCartierDiv.isIso_subschemeIota_snd_of_degree_one AlgebraicGeometry.isIso_ker_graphOver_subschemeIota_snd AlgebraicGeometry.isClosedImmersion_graphOver AlgebraicGeometry.FGSubalgebra.instIsDirectedLe AlgebraicGeometry.FGSubalgebra.instQuasiSeparatedSpaceCarrierCarrierCommRingCatObjOppositeSchemeSpecDiagram AlgebraicGeometry.FGSubalgebra.instIsCofilteredOpposite AlgebraicGeometry.FGSubalgebra.instIsAffineObjOppositeSchemeSpecDiagram AlgebraicGeometry.FGSubalgebra.instNonempty AlgebraicGeometry.FGSubalgebra.instNonemptySubtypeLeSubalgebraValFG AlgebraicGeometry.FGSubalgebra.instCompactSpaceCarrierCarrierCommRingCatObjOppositeSchemeSpecDiagram AlgebraicGeometry.FGSubalgebra.instIsDirectedSubtypeLeSubalgebraValFG AlgebraicGeometry.FGSubalgebra.instIsAffineHomMapOppositeSchemeSpecDiagram AlgebraicGeometry.FGSubalgebra.instIsFiltered AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instNeg AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instSMulInt AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instAddCommGroup AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instAdd AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instSub AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instModuleCarrierObjOppositeOpensCarrierCarrierCommRingCatPresheafOpOpensTop AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instSMulCarrierObjOppositeOpensCarrierCarrierCommRingCatPresheafOpOpensTop AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instSMulNat AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instZero AlgebraicCurve.instHasLocalResidue_of_hasCanonicalLocalResidueK AlgebraicCurve.instHasCanonicalLocalResidueK_of_hasCanonicalLocalResidueKStar AlgebraicCurve.Place.kw_ffgc_finiteDimensional_adicCompletion instAlgebraSubtypeMemValuationSubring_definitions AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersIntegersCompletion ModularCurve.KwF4gRRTate.instAlgebraKAdicCompletionIntegers AlgebraicCurve.Place.kw_ffgc_continuousSMul_adicCompletionComap AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersCompletionCompletion IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions AlgebraicCurve.instHasCanonicalLocalResidueK AlgebraicCurve.Place.instAlgebra_restrictResidueField"
p2m_attr_erase "instance" "AlgebraicCurve.Place.instIsScalarTower_restrictResidueField AlgebraicCurve.instHasLocalResidue AlgebraicCurve.HasSeparableResidue.of_perfectField_of_isCurveOver AlgebraicCurve.HasSeparableResidue.of_perfectField AlgebraicCurve.Place.instIsLocalHom_restrictSubringHom AlgebraicCurve.instHasCanonicalLocalResidueKStar ModularCurve.KwNo6Pin.isLocalRing_completion SheafOfModules.isIso_ihomModelToIhom AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instDecidableEqIdx AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instFintype AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instLinearOrder AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instFintypeIdx AlgebraicGeometry.OModulePresheaf.Leray.relAltC_scalarTower AlgebraicGeometry.OModulePresheaf.Leray.ker_relAltd_modΓ AlgebraicGeometry.OModulePresheaf.Leray.relAltC_modΓ AlgebraicGeometry.OModulePresheaf.Leray.biC_abGrp AlgebraicGeometry.OModulePresheaf.Leray.relAltH_modΓ AlgebraicGeometry.OModulePresheaf.Leray.ker_relAltd_smul AlgebraicGeometry.OModulePresheaf.Leray.relAltH_scalarTower AlgebraicGeometry.OModulePresheaf.Leray.relAltH_smul AlgebraicGeometry.OModulePresheaf.Leray.biC_module DoubleComplex.instModuleE₂I DoubleComplex.Bounded.modR DoubleComplex.instModuleE₂II DoubleComplex.instAddCommGroupE₂II DoubleComplex.Bounded.abGrp DoubleComplex.instAddCommGroupE₂I ProjSpaceCech.GradedModule.H.module ProjSpaceCech.GradedModule.H.addCommGroup ProjSpaceCech.GradedModule.sec.instAdd ProjSpaceCech.GradedModule.sec.instNeg ProjSpaceCech.GradedModule.acg ProjSpaceCech.GradedModule.Frac.setoid ProjSpaceCech.GradedModule.modR ProjSpaceCech.GradedModule.sec.instModule ProjSpaceCech.GradedModule.sec.instAddCommGroup ProjSpaceCech.GradedModule.sec.instZero ProjSpaceCech.GradedModule.Presentation.fJ ProjSpaceCech.GradedModule.sec.instSMul ProjSpaceCech.Twist.H.module"
p2m_attr_erase "instance" "ProjSpaceCech.Idx.instFintype ProjSpaceCech.Twist.H.addCommGroup ProjSpaceCech.Idx.instDecidableEq ProjSpaceCech.Twist.Mon.instDecidableEq ProjSpaceCech.Twist.cochain.instAddCommGroup ProjSpaceCech.Twist.cochain.instModule AlgebraicGeometry.FGSubalgebra.tensorStage_directedSystem AlgebraicGeometry.RelEffCartierDiv.isClosedImmersion_subschemeι_resProdMap AlgebraicGeometry.RelEffCartierDiv.isOpenImmersion_resProdMap AlgebraicCurve.CurveModel.locallyOfFiniteType_gluedToBase AlgebraicCurve.CurveModel.isFractionRing_overlap AlgebraicCurve.CurveModel.isLocallyNoetherian_glued AlgebraicCurve.CurveModel.jacobsonSpace_glued AlgebraicCurve.CurveModel.isOpenImmersion_ι₀ AlgebraicCurve.CurveModel.isIntegral_glued AlgebraicCurve.CurveModel.quasiSeparated_gluedToBase AlgebraicCurve.CurveModel.compactSpace_glued AlgebraicCurve.CurveModel.isIntegral_adjoin_chartRing AlgebraicCurve.CurveModel.isFractionRing_overlap_functionField AlgebraicCurve.CurveModel.isProper_gluedToBase AlgebraicCurve.CurveModel.isOpenImmersion_ιU AlgebraicCurve.CurveModel.isOpenImmersion_f₀ AlgebraicCurve.CurveModel.isOpenImmersion_fInf AlgebraicCurve.CurveModel.isOpenImmersion_ιInf AlgebraicCurve.CurveModel.algebra_overlap_functionField AlgebraicCurve.CurveModel.quasiCompact_gluedToBase AlgebraicCurve.CurveModel.algebraAdjoin AlgebraicCurve.CurveModel.isDedekindDomain_chartRing AlgebraicCurve.CurveModel.isIntegralClosure AlgebraicCurve.CurveModel.finite_chartRing AlgebraicCurve.CurveModel.centre_isPrime AlgebraicCurve.CurveModel.isFractionRing_chartRing AlgebraicCurve.CurveModel.finiteType_chartRing AlgebraicCurve.CurveModel.isNoetherianRing_chartRing AlgebraicCurve.CurveModel.isScalarTower_base_adjoin AlgebraicCurve.CurveModel.isScalarTower_adjoin AlgebraicCurve.CurveModel.chartRing_finitePresentation AlgebraicGeometry.ProjSpace.twistObj.addCommGroup AlgebraicGeometry.ProjSpace.twistFam.module AlgebraicGeometry.ProjSpace.twistObj.module"
p2m_attr_erase "instance" "AlgebraicGeometry.ProjSpace.twistObj.moduleSections AlgebraicGeometry.ProjSpace.twistFam.addCommGroup kmfloorsGlue_int_three_isPrime kmfloorsGlue_int_bot_isPrime AlgebraicGeometry.SubalgebraStages.compactSpace_pullback AlgebraicGeometry.SubalgebraStages.quasiSeparatedSpace_pullback AlgebraicGeometry.SubalgebraStages.compactSpace_obj AlgebraicGeometry.SubalgebraStages.quasiSeparatedSpace_obj AlgebraicGeometry.SubalgebraStages.quasiCompact_snd AlgebraicGeometry.SubalgebraStages.isAffineHom_leg AlgebraicGeometry.SubalgebraStages.isAffineHom_trans AlgebraicGeometry.SubalgebraStages.isAffineHom_diagram_map AlgebraicGeometry.SubalgebraStages.quasiSeparated_snd AlgebraicGeometry.SubalgebraStages.isCofiltered_op IsDirectLimit.Module.instDirectLimitCoeLinearMapIdOfOfNonempty AdicCompletion.instIsLocalRingMaximalIdeal"
p2m_attr_erase "simp" "GoodReductionJacobian.RelativeGroupLaw.baseChangePointToBase_ofBase GoodReductionJacobian.RelativeGroupLaw.baseChangePointToBase_coe GoodReductionJacobian.RelativeGroupLaw.baseChangePointOfBase_coe GoodReductionJacobian.RelativeGroupLaw.baseChange_inv GoodReductionJacobian.RelativeGroupLaw.baseChangePointOfBase_toBase GoodReductionJacobian.RelativeGroupLaw.baseChange_mul GoodReductionJacobian.RelativeGroupLaw.baseChange_one NeronModelInfra.NeronModelPropertyBundle.endExtensionEquiv_symm_restrict NeronModelInfra.schemeHomOverComp_id_left NeronModelInfra.schemeHomOverComp_id_right NeronModelInfra.schemeHomOverId_coe NeronModelInfra.NeronModelPropertyBundle.endExtensionEquiv_apply NeronModelInfra.NeronModelPropertyBundle.restrict_endExtensionEquiv_symm NeronModelInfra.schemeHomOverComp_coe NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_fst NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_snd NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_fst NeronSpecialFibreInfra.neronEndRestrictEquiv_apply NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_fst_assoc NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_snd NeronSpecialFibreInfra.neronEndExtension_genericFibreRestrict NeronSpecialFibreInfra.specClosedFibreInclusion_eq NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_fst_assoc NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_snd_assoc NeronSpecialFibreInfra.genericFibreRestrict_neronEndExtension NeronSpecialFibreInfra.homOverId_coe NeronSpecialFibreInfra.homOverComp_coe NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_snd_assoc GoodReductionJacobian.RelativeGroupLaw.fibre_inv GoodReductionJacobian.RelativeGroupLaw.fibrePointToBase_coe GoodReductionJacobian.RelativeGroupLaw.fibrePointOfBase_toBase GoodReductionJacobian.RelativeGroupLaw.fibre_mul GoodReductionJacobian.RelativeGroupLaw.fibrePointToBase_ofBase GoodReductionJacobian.RelativeGroupLaw.fibre_one GoodReductionJacobian.RelativeGroupLaw.fibrePointOfBase_coe AlgebraicGeometry.schemeFibreEndo_snd AlgebraicGeometry.schemeFibreEndo_fst RegularLocalRingQuotientAscent.dualNumberFst_apply NeronModelInfra.schemeHomOverNpow_succ NeronModelInfra.schemeHomOverNpow_zero"
p2m_attr_erase "simp" "GoodReductionJacobian.relativeGroupLawOfGrpObj_inv GoodReductionJacobian.relativeGroupLawOfGrpObj_mul GoodReductionJacobian.overHomEquivSchemeHomOver_apply_coe GoodReductionJacobian.relativeGroupLawOfGrpObj_one GoodReductionJacobian.overHomEquivSchemeHomOver_symm_apply_left AlgebraicGeometry.Scheme.Modules.tensorPow_zero AlgebraicGeometry.Scheme.Modules.tensorPow_succ AlgebraicGeometry.Scheme.OrderedAffineCover.mk.injEq AlgebraicGeometry.OModulePresheaf.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCover.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.mk.injEq AlgebraicGeometry.Scheme.TwoAffineOpenCover.mk.injEq AlgebraicGeometry.Scheme.TwoAffineOpenCover.mk.sizeOf_spec AlgebraicGeometry.Scheme.TwoAffineOpenCover.pullback_U1 AlgebraicGeometry.Scheme.TwoAffineOpenCover.pullback_U0 TwoChartCech.Sections.mk.injEq TwoChartCech.Cover.mk.injEq TwoChartCech.GrothendieckComplex.mk.injEq TwoChartCech.Sections.mk.sizeOf_spec TwoChartCech.Cover.mk.sizeOf_spec TwoChartCech.Cover.lineBundle_r0_apply TwoChartCech.GrothendieckComplex.mk.sizeOf_spec TwoChartCech.Cover.lineBundle_r1_apply CoherentBaseChange.TwoTermComplex.mk.sizeOf_spec CoherentBaseChange.TwoTermComplex.mk.injEq AlgebraicGeometry.OModulePresheaf.prod_obj AlgebraicGeometry.OModulePresheaf.restrOpen_obj AlgebraicGeometry.OModulePresheaf.DevissageStep.mk.injEq AlgebraicGeometry.OModulePresheaf.pushforward_obj AlgebraicGeometry.OModulePresheaf.im_obj AlgebraicGeometry.OModulePresheaf.pow_obj AlgebraicGeometry.OModulePresheaf.fstHom_app AlgebraicGeometry.OModulePresheaf.ker_obj AlgebraicGeometry.OModulePresheaf.coker_obj AlgebraicGeometry.OModulePresheaf.DevissageStep.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCover.preimage_U AlgebraicGeometry.OModulePresheaf.sndHom_app AlgebraicGeometry.OModulePresheaf.Hom.mk.injEq AlgebraicGeometry.OModulePresheaf.Hom.id_app AlgebraicGeometry.OModulePresheaf.AffHom.appSections_apply"
p2m_attr_erase "simp" "AlgebraicGeometry.OModulePresheaf.AffHom.comp_app AlgebraicGeometry.OModulePresheaf.AffSES.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.AffHom.kerMap_coe AlgebraicGeometry.OModulePresheaf.AffHom.id_app AlgebraicGeometry.OModulePresheaf.Hom.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.Hom.toAffHom_app AlgebraicGeometry.OModulePresheaf.SES.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.AffHom.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.Hom.comp_app AlgebraicGeometry.OModulePresheaf.SES.mk.injEq AlgebraicGeometry.OModulePresheaf.AffHom.mk.injEq AlgebraicGeometry.OModulePresheaf.Hom.appSections_apply AlgebraicGeometry.OModulePresheaf.AffSES.mk.injEq PresheafOfModules.freeεIso_hom_app PresheafOfModules.freeμIso_hom_app AlgebraicGeometry.RelPicard.RepresentsRelSubPic.mk.injEq AlgebraicGeometry.RelPicard.SubPicCondition.mk.injEq AlgebraicGeometry.RelPicard.SubPicCondition.mk.sizeOf_spec AlgebraicGeometry.RelPicard.RepresentsRelSubPic.mk.sizeOf_spec AlgebraicGeometry.SmoothProperCurve.sectionBaseChange_coe_snd AlgebraicGeometry.SmoothProperCurve.sectionBaseChange_coe_fst AlgebraicCurve.CurveModel.mk.injEq AlgebraicCurve.CurveModel.mk.sizeOf_spec AlgebraicCurve.mulAdele_apply AlgebraicCurve.residuePairing_apply_coe AlgebraicCurve.mem_adeleBdd AlgebraicCurve.weilSmul_one AlgebraicCurve.diagonalHom_apply AlgebraicCurve.weilSmul_apply AlgebraicCurve.adeleSpaceMul_coe AlgebraicCurve.mulAdele_one AlgebraicGeometry.SmoothProperCurve.FiniteMapData.twoAffineOpenCover_U1 AlgebraicGeometry.SmoothProperCurve.FiniteMapData.mk.injEq AlgebraicGeometry.SmoothProperCurve.FiniteMapData.mk.sizeOf_spec AlgebraicGeometry.SmoothProperCurve.FiniteMapData.twoAffineOpenCover_U0 AlgebraicGeometry.RelPicard.SubPicCondition.onClasses_mk AlgebraicGeometry.RelPicard.relSubPicPresheaf_map_coe CategoryTheory.Functor.OverTotal.ofFibre_fst CategoryTheory.Functor.overTotal_map_fst AlgebraicGeometry.Scheme.LocalRepresentabilityULift.glueData_J"
p2m_attr_erase "simp" "AlgebraicGeometry.Scheme.LocalRepresentabilityULift.uliftYoneda_toGlued_uliftYonedaGluedToSheaf AlgebraicGeometry.Scheme.LocalRepresentabilityULift.glueData_t' AlgebraicGeometry.Scheme.LocalRepresentabilityULift.uliftYoneda_toGlued_uliftYonedaGluedToSheaf_assoc AlgebraicGeometry.Scheme.LocalRepresentabilityULift.uliftYonedaGluedToSheaf_app_toGlued AlgebraicGeometry.Scheme.LocalRepresentabilityULift.glueData_openCover_map AlgebraicGeometry.Scheme.LocalRepresentabilityULift.uliftYonedaGluedToSheaf_app_comp AlgebraicGeometry.Scheme.LocalRepresentabilityULift.glueData_V AlgebraicGeometry.Scheme.LocalRepresentabilityULift.glueData_t AlgebraicGeometry.Scheme.LocalRepresentabilityULift.glueData_U AlgebraicGeometry.Scheme.LocalRepresentabilityULift.glueData_f AlgebraicGeometry.RelPicard.designationOfRepresentableBy_P AlgebraicGeometry.RelPicard.designationOfRepresentableBy_toBase AlgebraicGeometry.RelPicard.rigSection_snd AlgebraicGeometry.RelPicard.RigidifiedLineBundle.ofInvertible_L AlgebraicGeometry.RelPicard.rigSection_snd_assoc AlgebraicGeometry.RelPicard.SubPicGroupCondition.mk.injEq AlgebraicGeometry.RelPicard.SubPicGroupCondition.mk.sizeOf_spec AlgebraicCurve.coe_cechH0Equiv_apply AlgebraicCurve.cechH1ToH1_mk AlgebraicCurve.lSpaceOn_univ AlgebraicCurve.lSpaceOn_empty AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.Divisor.mapRestrict_single AlgebraicCurve.Divisor.pushforward_single AlgebraicCurve.Place.coe_restrictInclusion AlgebraicCurve.Place.mem_fiber AlgebraicCurve.Place.restrict_toValuationSubring AlgebraicCurve.Divisor.degree_pushforward AlgebraicCurve.Place.restrictResidueMap_residue AlgebraicCurve.Pic0.coe_pushforwardDegZeroHom AlgebraicCurve.Pic0.coe_pullbackDegZeroHom AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply"
p2m_attr_erase "simp" "AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Divisor.degree_pushforwardAlong AlgebraicCurve.Pic0.coe_degZeroCorrespondence AlgebraicCurve.Place.mem_fiberAlong AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.jqNModC_one ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one AlgebraicCurve.Place.differentialCoeff_zero AlgebraicCurve.Place.differentialCoeff_dCoord AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.injEq"
p2m_attr_erase "simp" "AlgebraicCurve.TranscendenceTower.mk.injEq AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec AlgebraicCurve.PoleDivisorPackage.mk.injEq AlgebraicGeometry.RelPicard.thetaBundle_def AlgebraicGeometry.RelPicard.picardBundle_def AlgebraicGeometry.RelEffCartierDiv.toRelEffDivisor_ofRelEffDivisor AlgebraicGeometry.RelEffCartierDiv.toRelEffDivisor_I AlgebraicGeometry.mapOnProdOver_fst_assoc AlgebraicGeometry.RelEffCartierDiv.mk.sizeOf_spec AlgebraicGeometry.RelEffCartierDiv.mk.injEq AlgebraicGeometry.mapOnProdOver_snd AlgebraicGeometry.mapOnProdOver_fst AlgebraicGeometry.mapOnProdOver_snd_assoc AlgebraicGeometry.mapOnProdOver_id AlgebraicCurve.RelEffDivisor.mk.sizeOf_spec AlgebraicCurve.mapOnProd_fst AlgebraicCurve.mapOnProd_fst_assoc AlgebraicCurve.mapOnProd_snd AlgebraicCurve.UnivDivisorPack.mk.injEq AlgebraicCurve.RelEffDivisor.mk.injEq AlgebraicCurve.UnivDivisorPack.mk.sizeOf_spec AlgebraicCurve.mapOnProd_snd_assoc AlgebraicGeometry.Scheme.Modules.exteriorPower_obj PresheafOfModules.exteriorPower_map_ιMulti PresheafOfModules.ExteriorPower.appₗ_apply AlgebraicGeometry.prodKerGraph_one AlgebraicGeometry.fibrePowOver.proj_comp AlgebraicGeometry.prodKerGraph_zero AlgebraicGeometry.RelEffCartierDiv.empty_I AlgebraicGeometry.fibrePowOver.proj_comp_assoc AlgebraicGeometry.graphOver_fst_assoc AlgebraicGeometry.RelEffCartierDiv.toPoint_comp AlgebraicGeometry.RelEffCartierDiv.toPoint_comp_assoc AlgebraicGeometry.graphOver_fst AlgebraicGeometry.RelEffCartierDiv.ofPoint_I AlgebraicGeometry.graphOver_snd AlgebraicGeometry.graphOver_snd_assoc AlgebraicCurve.SymmetricPowerPackage.mk.sizeOf_spec AlgebraicCurve.SymmetricPowerPackage.mk.injEq"
p2m_attr_erase "simp" "AlgebraicGeometry.FGSubalgebra.cocone_ι_app_apply AlgebraicGeometry.RelPicard.fst_toProdSpec AlgebraicGeometry.RelPicard.toProdSpec_fst_assoc AlgebraicGeometry.RelPicard.pointsSubBasepointModule_cons AlgebraicGeometry.RelPicard.pointsSubBasepointModule_nil AlgebraicGeometry.RelPicard.fst_toProdSpec_assoc AlgebraicGeometry.RelPicard.toProdSpec_fst AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.sub_app AlgebraicGeometry.Scheme.IdealSheafData.sres_sresTop AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.add_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.mk.sizeOf_spec AlgebraicGeometry.Scheme.IdealSheafData.coe_resLE AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.smul_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.coe_ofLE_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.ideal_range AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.zero_app AlgebraicGeometry.Scheme.IdealSheafData.sres_sres AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.comp_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.neg_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.id_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.coe_mulRight_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.nsmul_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.mk.injEq AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.zsmul_app AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.sizeOf_spec AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.injEq AlgebraicCurve.adeleSingle_coe AlgebraicCurve.kaehlerResidueTermKFam_apply AlgebraicCurve.Place.LocalResidueData.mk.injEq AlgebraicCurve.Place.LocalResidueData.mk.sizeOf_spec AlgebraicCurve.Place.kw_ffgc_adicCompletionComapIntegers_coe AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.sizeOf_spec AlgebraicCurve.Place.mem_simplePoleSubmodule AlgebraicCurve.Place.coe_uniformizerSubring ModularCurve.Lg37.Lg37CompletionSection.mk.injEq AlgebraicCurve.Place.CoefficientFieldSection.mk.injEq AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.injEq ModularCurve.Lg37.Lg37CompletionSection.mk.sizeOf_spec AlgebraicCurve.Place.CoefficientFieldSection.mk.sizeOf_spec AlgebraicCurve.Place.poleSubmodule_one"
p2m_attr_erase "simp" "AlgebraicCurve.Place.mem_poleSubmodule AlgebraicGeometry.Scheme.Modules.toUnitSection_ofUnitSection AlgebraicGeometry.Scheme.Modules.pullbackSection_def AlgebraicGeometry.Scheme.Modules.ofUnitSection_toUnitSection PresheafOfModules.InternalHom.IsSheafAux.appAt_toPresheafHom SheafOfModules.ihomSectionsEquivFamily_unit AlgebraicGeometry.Scheme.Modules.restrictHomEquivFamily_apply SheafOfModules.ihomEval_unit_app AlgebraicGeometry.Scheme.Modules.ihomEval_zero_right AlgebraicGeometry.Scheme.Modules.ihomEval_zero_left AlgebraicGeometry.Scheme.Modules.homOfFamily_app_apply SheafOfModules.unit_ihomSectionsEquivFamily AlgebraicGeometry.Scheme.Modules.familyOfHom_app AlgebraicGeometry.Scheme.Modules.restrictUnitIso_hom_app_apply AlgebraicGeometry.Scheme.Modules.restrictUnitIso_inv_app_apply AlgebraicGeometry.Scheme.Modules.restrictHomOfFamily_app_apply AlgebraicGeometry.Scheme.Modules.restrictHomEquivFamily_symm_apply AlgebraicGeometry.Scheme.Modules.tensorSections_zero_right AlgebraicGeometry.Scheme.Modules.map_unitSection AlgebraicGeometry.Scheme.Modules.tensorSectionsBilin_apply AlgebraicGeometry.Scheme.Modules.tensorPowSection_zero AlgebraicGeometry.Scheme.Modules.tensorSections_zero_left AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_neg AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_zero AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_sub AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_add AlgebraicGeometry.Scheme.OrderedAffineCover.toCoverOf_U AlgebraicGeometry.Scheme.OrderedAffineCoverOf.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCoverOf.mk.injEq AlgebraicGeometry.Scheme.OrderedAffineCover.restrict_U AlgebraicGeometry.OModulePresheaf.Leray.restrictToPreimage_U DoubleComplex.Bounded.mk.injEq DoubleComplex.Bounded.mk.sizeOf_spec DoubleComplex.Convergence.mk.injEq DoubleComplex.Convergence.mk.sizeOf_spec DoubleComplex.SubQuot.mk.sizeOf_spec DoubleComplex.SubQuot.mk.injEq ProjSpaceCech.GradedModule.mk.injEq ProjSpaceCech.GradedModule.mk.sizeOf_spec ProjSpaceCech.GradedModule.Frac.mk.sizeOf_spec"
p2m_attr_erase "simp" "ProjSpaceCech.GradedModule.Presentation.mk.injEq ProjSpaceCech.GradedModule.Frac.mk.injEq ProjSpaceCech.GradedModule.Presentation.mk.sizeOf_spec ProjSpaceCech.GradedModule.Hom.shift_toLinearMap ProjSpaceCech.GradedModule.Hom.mk.sizeOf_spec ProjSpaceCech.GradedModule.Hom.mk.injEq TwoChartCech.Mumford.dK_apply TwoChartCech.Mumford.ι0_apply TwoChartCech.Mumford.ι1_apply TwoChartCech.KerCoprod.dK_apply TwoChartCech.KerCoprod.ι1_apply TwoChartCech.KerCoprod.ι0_apply AlgebraicGeometry.tilde.functorCompPullbackSpecIso_app AlgebraicGeometry.RelPicard.algEquivZeroGroupCut_toSubPicCondition AlgebraicGeometry.RelPicard.LFP.stageHom_val AlgebraicGeometry.RelPicard.BaseChange.relSubPicPresheafRestrictIso_hom_app_coe AlgebraicGeometry.RelPicard.BaseChange.relSubPicPresheafRestrictIso_inv_app_coe AlgebraicGeometry.RelPicard.BaseChange.restrict_P AlgebraicGeometry.RelEffCartierDiv.IsUniversal.lift_comp AlgebraicGeometry.RelEffCartierDiv.functor_map_fst AlgebraicGeometry.RelEffCartierDiv.IsUniversal.homEquiv_apply AlgebraicGeometry.RelEffCartierDiv.IsUniversal.lift_pullbackAlong AlgebraicGeometry.RelEffCartierDiv.IsUniversal.homEquiv_symm_apply AlgebraicGeometry.RelEffCartierDiv.IsUniversal.lift_comp_assoc AlgebraicGeometry.RelEffCartierDiv.supportedIn_top AlgebraicGeometry.RelEffCartierDiv.mem_supportedIn_iff AlgebraicGeometry.RelEffCartierDiv.supportedIn_top_eq AlgebraicGeometry.RelEffCartierDiv.restrictAlong_extendAlong AlgebraicGeometry.RelEffCartierDiv.extendAlong_I AlgebraicGeometry.RelEffCartierDiv.resProdMap_snd AlgebraicGeometry.RelEffCartierDiv.restrictAlong_I AlgebraicGeometry.RelEffCartierDiv.extendAlong_restrictAlong AlgebraicGeometry.RelEffCartierDiv.resProdMap_fst_assoc AlgebraicGeometry.RelEffCartierDiv.resProdMap_snd_assoc AlgebraicGeometry.RelEffCartierDiv.resProdMap_fst CoherentBaseChange.FibreH0Family.mk.sizeOf_spec CoherentBaseChange.FibreH0Family.mk.injEq AlgebraicCurve.CurveModel.coe_gInf AlgebraicCurve.CurveModel.coe_tInvChart AlgebraicCurve.CurveModel.ιInf_gluedToBase_assoc"
p2m_attr_erase "simp" "AlgebraicCurve.CurveModel.ιInf_gluedToBase AlgebraicCurve.CurveModel.primeOfι₀_asIdeal AlgebraicCurve.CurveModel.coe_tChart AlgebraicCurve.CurveModel.ι₀_gluedToBase_assoc AlgebraicCurve.CurveModel.primeOfιInf_asIdeal AlgebraicCurve.CurveModel.ι₀_gluedToBase AlgebraicCurve.CurveModel.coe_tma AlgebraicCurve.CurveModel.coe_primeEquivChartPlaces AlgebraicGeometry.ProjSpace.twistObj.mk.injEq AlgebraicGeometry.ProjSpace.twistObj.zero_val AlgebraicGeometry.ProjSpace.twistObj.add_val AlgebraicGeometry.ProjSpace.twist_res_val AlgebraicGeometry.ProjSpace.twist_smul_val AlgebraicGeometry.ProjSpace.twistGradeToObj_val AlgebraicGeometry.ProjSpace.twistObj.smul_val AlgebraicGeometry.ProjSpace.twistGradeEquiv_apply_val AlgebraicGeometry.ProjSpace.twistObj.mk.sizeOf_spec QuaternionAlgebra.baseChangeRight_tmul QuaternionAlgebra.mapOfAlgebraMapEq_apply QuaternionAlgebra.baseChange_tmul AlgebraicGeometry.SubalgebraStages.specCone_π_app AlgebraicGeometry.SubalgebraStages.specLeg_specHom AlgebraicGeometry.SubalgebraStages.specLeg_specTrans AlgebraicGeometry.SubalgebraStages.cone_pt AlgebraicGeometry.SubalgebraStages.trans_fst AlgebraicGeometry.SubalgebraStages.diagram_obj AlgebraicGeometry.SubalgebraStages.leg_snd AlgebraicGeometry.SubalgebraStages.diagram_map AlgebraicGeometry.SubalgebraStages.specTrans_refl AlgebraicGeometry.SubalgebraStages.trans_snd AlgebraicGeometry.SubalgebraStages.specTrans_specHom AlgebraicGeometry.SubalgebraStages.specCone_pt AlgebraicGeometry.SubalgebraStages.cone_π_app AlgebraicGeometry.SubalgebraStages.specDiagram_map AlgebraicGeometry.SubalgebraStages.specDiagram_obj AlgebraicGeometry.SubalgebraStages.leg_fst AlgebraicGeometry.SubalgebraStages.leg_trans IsDirectLimit.Module.linearEquiv_symm_apply IsDirectLimit.linearEquiv_symm_apply IsDirectLimit.lift_of"
p2m_attr_erase "simp" "IsDirectLimit.Module.linearEquiv_apply IsDirectLimit.Module.lift_of IsDirectLimit.Equiv_apply"

set_option autoImplicit false

open scoped TensorProduct Quaternion NumberField
open CategoryTheory AlgebraicGeometry QuaternionAlgebra CerednikDrinfeld CerednikDrinfeld.QM NeronModelInfra GoodReductionJacobian

namespace Ws47RL

open CerednikDrinfeld.QM.FakeEllipticCurve in
theorem mapPt_hom_inv {R : Type} [CommRing R] {A A' : Scheme.{0}} {f : A ⟶ Spec (CommRingCat.of R)} {f' : A' ⟶ Spec (CommRingCat.of R)}
    (i : A ≅ A') (hi : i.hom ≫ f' = f) (hi' : i.inv ≫ f = f') {T : Scheme.{0}} {t : T ⟶ Spec (CommRingCat.of R)}
    (P : SchemeHomOver t f) : mapPt i.inv hi' (mapPt i.hom hi P) = P :=
  Subtype.ext (by simp [mapPt])

theorem mapPt_inv_hom {R : Type} [CommRing R] {A A' : Scheme.{0}} {f : A ⟶ Spec (CommRingCat.of R)} {f' : A' ⟶ Spec (CommRingCat.of R)}
    (i : A ≅ A') (hi : i.hom ≫ f' = f) (hi' : i.inv ≫ f = f') {T : Scheme.{0}} {t : T ⟶ Spec (CommRingCat.of R)}
    (P : SchemeHomOver t f') : mapPt i.hom hi (mapPt i.inv hi' P) = P :=
  Subtype.ext (by simp [mapPt])

open CerednikDrinfeld.QM.FakeEllipticCurve in

theorem isoVia_symm {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} {N n : ℕ} {S : Type} [CommRing S]
    (u u' : WithFullLevel Λ N n S) (i : u.1.A ≅ u'.1.A) (hi : i.hom ≫ u'.1.f = u.1.f)
    (h : WithFullLevel.IsoVia u u' i hi) :
    ∃ hi' : i.symm.hom ≫ u.1.f = u'.1.f, WithFullLevel.IsoVia u' u i.symm hi' := by
  have hi' : i.inv ≫ u.1.f = u'.1.f := by rw [← hi, Iso.inv_hom_id_assoc]
  obtain ⟨hm, ha, hl, hP⟩ := h
  refine ⟨hi', ?_, ?_, ?_, ?_⟩
  · intro T t P Q
    have := hm t (mapPt i.inv hi' P) (mapPt i.inv hi' Q)
    rw [mapPt_inv_hom, mapPt_inv_hom] at this
    show mapPt i.inv hi' (u'.1.L.mul t P Q) = u.1.L.mul t (mapPt i.inv hi' P) (mapPt i.inv hi' Q)
    rw [← this, mapPt_hom_inv]
  · intro x
    show u'.1.act x ≫ i.inv = i.inv ≫ u.1.act x
    rw [Iso.eq_inv_comp, ← Category.assoc, ← ha, Category.assoc, Iso.hom_inv_id, Category.comp_id]
  · intro T t P
    have := hl t (mapPt i.inv hi' P)
    rw [mapPt_inv_hom] at this
    exact this.symm
  · show mapPt i.inv hi' u'.2.P = u.2.P
    rw [← hP, mapPt_hom_inv]

theorem isUnit_natCast_of_not_dvd {r N : ℕ} [Fact r.Prime] (hrN : ¬ r ∣ N)
    {𝒪 : Type} [CommRing 𝒪] {π : 𝒪} (hunr : Ideal.span {((r : ℕ) : 𝒪)} = Ideal.span {π})
    {L : Type} [CommRing L] [Algebra 𝒪 L] (hπ : algebraMap 𝒪 L π = 0) :
    IsUnit ((N : ℕ) : L) := by
  have hr : ((r : ℕ) : 𝒪) ∈ Ideal.span {π} := hunr ▸ Ideal.mem_span_singleton_self _
  obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.mp hr
  have hrL : ((r : ℕ) : L) = 0 := by
    rw [← map_natCast (algebraMap 𝒪 L), ← hc, map_mul, hπ, mul_zero]
  have hcop : IsCoprime ((r : ℕ) : ℤ) ((N : ℕ) : ℤ) :=
    Nat.isCoprime_iff_coprime.mpr (((Fact.out : r.Prime).coprime_iff_not_dvd).mpr hrN)
  have h2 := hcop.map (Int.castRingHom L)
  simp only [eq_intCast, Int.cast_natCast, hrL] at h2
  exact isCoprime_zero_left.mp h2

theorem isUnit_natCast_quot_of_not_dvd {r N : ℕ} [Fact r.Prime] (hrN : ¬ r ∣ N)
    {𝒪 : Type} [CommRing 𝒪] {π : 𝒪} (hunr : Ideal.span {((r : ℕ) : 𝒪)} = Ideal.span {π})
    {L : Type} [CommRing L] [Algebra 𝒪 L] (hπ : algebraMap 𝒪 L π = 0) :
    IsUnit ((N : ℕ) : L ⧸ Ideal.span {algebraMap 𝒪 L π}) := by
  have := (isUnit_natCast_of_not_dvd hrN hunr hπ).map (Ideal.Quotient.mk (Ideal.span {algebraMap 𝒪 L π}))
  simpa using this

theorem Spec_map_id (S : Type) [CommRing S] : Spec.map (CommRingCat.ofHom (RingHom.id S)) = 𝟙 _ := by
  rw [CommRingCat.ofHom_id, Spec.map_id]

open CerednikDrinfeld.QM.FakeEllipticCurve in

theorem exists_corr_symm
    {r N : ℕ} {𝒪 : Type} [CommRing 𝒪] {π : 𝒪} {Onr : Type} [CommRing Onr] [Algebra 𝒪 Onr]
    {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} (hΛℤ : ∀ m : ℤ, ((m : ℚ) : ℍ[ℚ, a, b]) ∈ Λ)
    {A₀ : FakeEllipticCurve Λ N (Onr ⧸ Ideal.span {algebraMap 𝒪 Onr π})}
    {B : Type} [CommRing B] [Algebra 𝒪 B] {ψ : Onr →ₐ[𝒪] B}
    (hNB : IsUnit ((N : ℕ) : B ⧸ Ideal.span {algebraMap 𝒪 B π}))
    {E E' : FakeEllipticCurve Λ N B} (i : E.A ≅ E'.A) (hi : i.hom ≫ E'.f = E.f)
    (ρ : Rigidification r π A₀ ψ E) (ρ' : Rigidification r π A₀ ψ E')
    (ib : ρ.Eb.A ⟶ ρ'.Eb.A) (hib : ib ≫ ρ'.gb = ρ.gb ≫ i.hom) (hibf : ib ≫ ρ'.Eb.f = ρ.Eb.f)
    (uA : ρ'.Ab.A ⟶ ρ.Ab.A) (huA : IsPullbackVia (RingHom.id _) ρ.Ab ρ'.Ab uA) (huAg : uA ≫ ρ.gA = ρ'.gA)
    (i₁ j₁ : ℕ)
    (hcorr : ib ≫ ρ'.φ ≫ uA ≫ ρ.Ab.act ⟨(((r ^ i₁ : ℕ) : ℤ) : ℚ), hΛℤ _⟩ = ρ.φ ≫ ρ.Ab.act ⟨(((r ^ j₁ : ℕ) : ℤ) : ℚ), hΛℤ _⟩) :
    ∃ (ib' : ρ'.Eb.A ⟶ ρ.Eb.A) (_ : ib' ≫ ρ.gb = ρ'.gb ≫ i.symm.hom) (_ : ib' ≫ ρ.Eb.f = ρ'.Eb.f)
      (uA' : ρ.Ab.A ⟶ ρ'.Ab.A) (_ : IsPullbackVia (RingHom.id _) ρ'.Ab ρ.Ab uA') (_ : uA' ≫ ρ'.gA = ρ.gA)
      (i₂ j₂ : ℕ),
      ib' ≫ ρ.φ ≫ uA' ≫ ρ'.Ab.act ⟨(((r ^ i₂ : ℕ) : ℤ) : ℚ), hΛℤ _⟩ = ρ'.φ ≫ ρ'.Ab.act ⟨(((r ^ j₂ : ℕ) : ℤ) : ℚ), hΛℤ _⟩ := by
  have hid := Spec_map_id (B ⧸ Ideal.span {algebraMap 𝒪 B π})

  obtain ⟨hpb, -, -, -⟩ := ρ.isPullback_Eb
  obtain ⟨hpb', -, -, -⟩ := ρ'.isPullback_Eb
  have hi' : i.inv ≫ E.f = E'.f := by rw [← hi, Iso.inv_hom_id_assoc]

  have w : (ρ'.gb ≫ i.inv) ≫ E.f = ρ'.Eb.f ≫ Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (Ideal.span {algebraMap 𝒪 B π}))) := by
    rw [Category.assoc, hi', hpb'.w]
  let ib' : ρ'.Eb.A ⟶ ρ.Eb.A := hpb.lift (ρ'.gb ≫ i.inv) ρ'.Eb.f w
  have hib'1 : ib' ≫ ρ.gb = ρ'.gb ≫ i.inv := hpb.lift_fst _ _ _
  have hib'2 : ib' ≫ ρ.Eb.f = ρ'.Eb.f := hpb.lift_snd _ _ _
  have hinv : ib' ≫ ib = 𝟙 _ := by
    apply hpb'.hom_ext
    · rw [Category.assoc, hib, ← Category.assoc, hib'1, Category.assoc, Iso.inv_hom_id, Category.comp_id, Category.id_comp]
    · rw [Category.assoc, hibf, hib'2, Category.id_comp]

  obtain ⟨uA', huA'g, huA'f, huA'v⟩ :=
    CerednikDrinfeld.QM.FakeEllipticCurve.exists_isPullbackVia_id_comp_eq_of_isPullbackVia_of_isPullbackVia_of_isUnit
      _ hNB A₀ ρ'.Ab ρ'.gA ρ'.isPullback_Ab ρ.Ab ρ.gA ρ.isPullback_Ab
  obtain ⟨hpbA', -, -, -⟩ := ρ'.isPullback_Ab
  obtain ⟨huAw, -, -, -⟩ := id huA
  obtain ⟨huA'w, -, huA'act, -⟩ := id huA'v
  have hinvA : uA ≫ uA' = 𝟙 _ := by
    apply hpbA'.hom_ext
    · rw [Category.assoc, huA'g, huAg, Category.id_comp]
    · have h1 := huAw.w; have h2 := huA'w.w
      simp only [hid, Category.comp_id] at h1 h2
      rw [Category.assoc, h2, h1, Category.id_comp]
  refine ⟨ib', hib'1, hib'2, uA', huA'v, huA'g, j₁, i₁, ?_⟩

  have h := congrArg (fun z => ib' ≫ z ≫ uA') hcorr
  simp only [Category.assoc] at h
  rw [← Category.assoc ib' ib, hinv, Category.id_comp, huA'act, huA'act, ← Category.assoc uA uA', hinvA,
    Category.id_comp] at h
  exact h.symm

end Ws47RL

namespace We81Corr

variable {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} {N : ℕ} {S : Type} [CommRing S]

theorem powCast_mem (hΛℤ : ∀ m : ℤ, ((m : ℚ) : ℍ[ℚ, a, b]) ∈ Λ) (r k : ℕ) :
    ((((r ^ k : ℕ) : ℤ) : ℚ) : ℍ[ℚ, a, b]) ∈ Λ := hΛℤ _

theorem act_pow_comp_act_pow (hΛℤ : ∀ m : ℤ, ((m : ℚ) : ℍ[ℚ, a, b]) ∈ Λ) (E : FakeEllipticCurve Λ N S) (r m n : ℕ) :
    E.act ⟨(((r ^ m : ℕ) : ℤ) : ℚ), hΛℤ _⟩ ≫ E.act ⟨(((r ^ n : ℕ) : ℤ) : ℚ), hΛℤ _⟩ =
      E.act ⟨(((r ^ (m + n) : ℕ) : ℤ) : ℚ), hΛℤ _⟩ := by
  have hprod : ((((r ^ n : ℕ) : ℤ) : ℚ) : ℍ[ℚ, a, b]) * ((((r ^ m : ℕ) : ℤ) : ℚ) : ℍ[ℚ, a, b]) =
      ((((r ^ (m + n) : ℕ) : ℤ) : ℚ) : ℍ[ℚ, a, b]) := by
    push_cast
    rw [← pow_add, add_comm]
  have hmem : ((((r ^ n : ℕ) : ℤ) : ℚ) : ℍ[ℚ, a, b]) * ((((r ^ m : ℕ) : ℤ) : ℚ) : ℍ[ℚ, a, b]) ∈ Λ := by
    rw [hprod]; exact hΛℤ _
  have h := E.act_mul ⟨(((r ^ n : ℕ) : ℤ) : ℚ), hΛℤ _⟩ ⟨(((r ^ m : ℕ) : ℤ) : ℚ), hΛℤ _⟩ hmem

  rw [← h]
  congr 1
  exact Subtype.ext hprod

theorem act_pow_comm (hΛℤ : ∀ m : ℤ, ((m : ℚ) : ℍ[ℚ, a, b]) ∈ Λ) (E : FakeEllipticCurve Λ N S) (r m n : ℕ) :
    E.act ⟨(((r ^ m : ℕ) : ℤ) : ℚ), hΛℤ _⟩ ≫ E.act ⟨(((r ^ n : ℕ) : ℤ) : ℚ), hΛℤ _⟩ =
      E.act ⟨(((r ^ n : ℕ) : ℤ) : ℚ), hΛℤ _⟩ ≫ E.act ⟨(((r ^ m : ℕ) : ℤ) : ℚ), hΛℤ _⟩ := by
  rw [act_pow_comp_act_pow, act_pow_comp_act_pow, Nat.add_comm]

theorem corr_trans {r : ℕ} {𝒪 : Type} [CommRing 𝒪] {π : 𝒪} {Onr : Type} [CommRing Onr] [Algebra 𝒪 Onr]
    (hΛℤ : ∀ m : ℤ, ((m : ℚ) : ℍ[ℚ, a, b]) ∈ Λ)
    {A₀ : FakeEllipticCurve Λ N (Onr ⧸ Ideal.span {algebraMap 𝒪 Onr π})}
    {B : Type} [CommRing B] [Algebra 𝒪 B] {ψ : Onr →ₐ[𝒪] B} {E E' E'' : FakeEllipticCurve Λ N B}
    (ρ₁ : FakeEllipticCurve.Rigidification r π A₀ ψ E) (ρ₂ : FakeEllipticCurve.Rigidification r π A₀ ψ E') (ρ₃ : FakeEllipticCurve.Rigidification r π A₀ ψ E'')
    (ih : E.A ⟶ E'.A) (ih₂ : E'.A ⟶ E''.A)

    (ib₁ : ρ₁.Eb.A ⟶ ρ₂.Eb.A) (hib₁ : ib₁ ≫ ρ₂.gb = ρ₁.gb ≫ ih) (hib₁f : ib₁ ≫ ρ₂.Eb.f = ρ₁.Eb.f)
    (uA₁ : ρ₂.Ab.A ⟶ ρ₁.Ab.A) (huA₁ : FakeEllipticCurve.IsPullbackVia (RingHom.id _) ρ₁.Ab ρ₂.Ab uA₁)
    (huA₁g : uA₁ ≫ ρ₁.gA = ρ₂.gA) (i₁ j₁ : ℕ)
    (h₁ : ib₁ ≫ ρ₂.φ ≫ uA₁ ≫ ρ₁.Ab.act ⟨(((r ^ i₁ : ℕ) : ℤ) : ℚ), hΛℤ _⟩ = ρ₁.φ ≫ ρ₁.Ab.act ⟨(((r ^ j₁ : ℕ) : ℤ) : ℚ), hΛℤ _⟩)

    (ib₂ : ρ₂.Eb.A ⟶ ρ₃.Eb.A) (hib₂ : ib₂ ≫ ρ₃.gb = ρ₂.gb ≫ ih₂) (hib₂f : ib₂ ≫ ρ₃.Eb.f = ρ₂.Eb.f)
    (uA₂ : ρ₃.Ab.A ⟶ ρ₂.Ab.A) (huA₂ : FakeEllipticCurve.IsPullbackVia (RingHom.id _) ρ₂.Ab ρ₃.Ab uA₂)
    (huA₂g : uA₂ ≫ ρ₂.gA = ρ₃.gA) (i₂ j₂ : ℕ)
    (h₂ : ib₂ ≫ ρ₃.φ ≫ uA₂ ≫ ρ₂.Ab.act ⟨(((r ^ i₂ : ℕ) : ℤ) : ℚ), hΛℤ _⟩ = ρ₂.φ ≫ ρ₂.Ab.act ⟨(((r ^ j₂ : ℕ) : ℤ) : ℚ), hΛℤ _⟩) :
    ∃ (ib : ρ₁.Eb.A ⟶ ρ₃.Eb.A) (_ : ib ≫ ρ₃.gb = ρ₁.gb ≫ (ih ≫ ih₂)) (_ : ib ≫ ρ₃.Eb.f = ρ₁.Eb.f)
      (uA : ρ₃.Ab.A ⟶ ρ₁.Ab.A) (_ : FakeEllipticCurve.IsPullbackVia (RingHom.id _) ρ₁.Ab ρ₃.Ab uA) (_ : uA ≫ ρ₁.gA = ρ₃.gA)
      (i' j' : ℕ),
      ib ≫ ρ₃.φ ≫ uA ≫ ρ₁.Ab.act ⟨(((r ^ i' : ℕ) : ℤ) : ℚ), hΛℤ _⟩ = ρ₁.φ ≫ ρ₁.Ab.act ⟨(((r ^ j' : ℕ) : ℤ) : ℚ), hΛℤ _⟩ := by

  have hcomp := FakeEllipticCurve.IsPullbackVia.comp (RingHom.id _) (RingHom.id _) ρ₁.Ab ρ₂.Ab ρ₃.Ab uA₁ uA₂ huA₁ huA₂
  have hid : (RingHom.id (B ⧸ Ideal.span {algebraMap 𝒪 B π})).comp (RingHom.id _) = RingHom.id _ := RingHom.id_comp _
  rw [hid] at hcomp

  obtain ⟨-, -, hact₁, -⟩ := huA₁
  refine ⟨ib₁ ≫ ib₂, ?_, ?_, uA₂ ≫ uA₁, hcomp, ?_, i₂ + i₁, j₁ + j₂, ?_⟩
  · rw [Category.assoc, hib₂, ← Category.assoc, hib₁, Category.assoc]
  · rw [Category.assoc, hib₂f, hib₁f]
  · rw [Category.assoc, huA₁g, huA₂g]
  ·
    rw [← act_pow_comp_act_pow hΛℤ ρ₁.Ab r i₂ i₁]
    calc (ib₁ ≫ ib₂) ≫ ρ₃.φ ≫ (uA₂ ≫ uA₁) ≫
          (ρ₁.Ab.act ⟨(((r ^ i₂ : ℕ) : ℤ) : ℚ), hΛℤ _⟩ ≫ ρ₁.Ab.act ⟨(((r ^ i₁ : ℕ) : ℤ) : ℚ), hΛℤ _⟩)
        = ib₁ ≫ (ib₂ ≫ ρ₃.φ ≫ uA₂ ≫ (uA₁ ≫ ρ₁.Ab.act ⟨(((r ^ i₂ : ℕ) : ℤ) : ℚ), hΛℤ _⟩)) ≫
            ρ₁.Ab.act ⟨(((r ^ i₁ : ℕ) : ℤ) : ℚ), hΛℤ _⟩ := by simp only [Category.assoc]
      _ = ib₁ ≫ (ib₂ ≫ ρ₃.φ ≫ uA₂ ≫ (ρ₂.Ab.act ⟨(((r ^ i₂ : ℕ) : ℤ) : ℚ), hΛℤ _⟩ ≫ uA₁)) ≫
            ρ₁.Ab.act ⟨(((r ^ i₁ : ℕ) : ℤ) : ℚ), hΛℤ _⟩ := by rw [hact₁]
      _ = ib₁ ≫ ((ib₂ ≫ ρ₃.φ ≫ uA₂ ≫ ρ₂.Ab.act ⟨(((r ^ i₂ : ℕ) : ℤ) : ℚ), hΛℤ _⟩) ≫ uA₁) ≫
            ρ₁.Ab.act ⟨(((r ^ i₁ : ℕ) : ℤ) : ℚ), hΛℤ _⟩ := by simp only [Category.assoc]
      _ = ib₁ ≫ ((ρ₂.φ ≫ ρ₂.Ab.act ⟨(((r ^ j₂ : ℕ) : ℤ) : ℚ), hΛℤ _⟩) ≫ uA₁) ≫
            ρ₁.Ab.act ⟨(((r ^ i₁ : ℕ) : ℤ) : ℚ), hΛℤ _⟩ := by rw [h₂]
      _ = ib₁ ≫ ρ₂.φ ≫ (ρ₂.Ab.act ⟨(((r ^ j₂ : ℕ) : ℤ) : ℚ), hΛℤ _⟩ ≫ uA₁) ≫
            ρ₁.Ab.act ⟨(((r ^ i₁ : ℕ) : ℤ) : ℚ), hΛℤ _⟩ := by simp only [Category.assoc]
      _ = ib₁ ≫ ρ₂.φ ≫ (uA₁ ≫ ρ₁.Ab.act ⟨(((r ^ j₂ : ℕ) : ℤ) : ℚ), hΛℤ _⟩) ≫
            ρ₁.Ab.act ⟨(((r ^ i₁ : ℕ) : ℤ) : ℚ), hΛℤ _⟩ := by rw [hact₁]
      _ = ib₁ ≫ ρ₂.φ ≫ uA₁ ≫ (ρ₁.Ab.act ⟨(((r ^ j₂ : ℕ) : ℤ) : ℚ), hΛℤ _⟩ ≫
            ρ₁.Ab.act ⟨(((r ^ i₁ : ℕ) : ℤ) : ℚ), hΛℤ _⟩) := by simp only [Category.assoc]
      _ = ib₁ ≫ ρ₂.φ ≫ uA₁ ≫ (ρ₁.Ab.act ⟨(((r ^ i₁ : ℕ) : ℤ) : ℚ), hΛℤ _⟩ ≫
            ρ₁.Ab.act ⟨(((r ^ j₂ : ℕ) : ℤ) : ℚ), hΛℤ _⟩) := by rw [act_pow_comm]
      _ = (ib₁ ≫ ρ₂.φ ≫ uA₁ ≫ ρ₁.Ab.act ⟨(((r ^ i₁ : ℕ) : ℤ) : ℚ), hΛℤ _⟩) ≫
            ρ₁.Ab.act ⟨(((r ^ j₂ : ℕ) : ℤ) : ℚ), hΛℤ _⟩ := by simp only [Category.assoc]
      _ = (ρ₁.φ ≫ ρ₁.Ab.act ⟨(((r ^ j₁ : ℕ) : ℤ) : ℚ), hΛℤ _⟩) ≫
            ρ₁.Ab.act ⟨(((r ^ j₂ : ℕ) : ℤ) : ℚ), hΛℤ _⟩ := by rw [h₁]
      _ = ρ₁.φ ≫ ρ₁.Ab.act ⟨(((r ^ (j₁ + j₂) : ℕ) : ℤ) : ℚ), hΛℤ _⟩ := by
            rw [Category.assoc, act_pow_comp_act_pow]

end We81Corr

namespace We88Hsc

theorem hSc_quotient_of_isNilpotent (S : Type) [CommRing S] (I : Ideal S) (hI : ∀ x ∈ I, IsNilpotent x)
    (hS : ∀ e : S, IsIdempotentElem e → e = 0 ∨ e = 1) (e : S ⧸ I) (he : IsIdempotentElem e) : e = 0 ∨ e = 1 := by
  have hker : ∀ x ∈ RingHom.ker (Ideal.Quotient.mk I), IsNilpotent x := fun x hx => by
    rw [Ideal.mk_ker] at hx; exact hI x hx
  obtain ⟨e', he', rfl⟩ := exists_isIdempotentElem_eq_of_ker_isNilpotent (Ideal.Quotient.mk I) hker e
    (by obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective e; exact ⟨x, rfl⟩) he
  rcases hS e' he' with h | h
  · left; rw [h, map_zero]
  · right; rw [h, map_one]

theorem hSc_quotient_of_eq_bot (S : Type) [CommRing S] (I : Ideal S) (hI : I = ⊥)
    (hS : ∀ e : S, IsIdempotentElem e → e = 0 ∨ e = 1) (e : S ⧸ I) (he : IsIdempotentElem e) : e = 0 ∨ e = 1 :=
  hSc_quotient_of_isNilpotent S I (fun x hx => by rw [hI, Ideal.mem_bot] at hx; rw [hx]; exact IsNilpotent.zero) hS e he

theorem forall_mem_span_singleton_isNilpotent (S : Type) [CommRing S] (π : S) (hπ : IsNilpotent π) :
    ∀ x ∈ Ideal.span ({π} : Set S), IsNilpotent x := fun x hx => by
  obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.1 hx
  exact (Commute.all c π).isNilpotent_mul_left hπ

end We88Hsc

namespace We89Transfer

theorem corr_refl_of_corr_refl_pullback
    {r N : ℕ} {𝒪 : Type} [CommRing 𝒪] {π : 𝒪} {Onr : Type} [CommRing Onr] [Algebra 𝒪 Onr]
    {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} (hΛℤ : ∀ m : ℤ, ((m : ℚ) : ℍ[ℚ, a, b]) ∈ Λ)
    {A₀ : FakeEllipticCurve Λ N (Onr ⧸ Ideal.span {algebraMap 𝒪 Onr π})}

    {S S' : Type} [CommRing S] [Algebra 𝒪 S] [CommRing S'] [Algebra 𝒪 S'] (φ : S →ₐ[𝒪] S')
    (hφ : Function.Bijective (Ideal.quotientMap (Ideal.span {algebraMap 𝒪 S' π}) (φ : S →+* S')
      (Ideal.span_le.mpr (Set.singleton_subset_iff.mpr (Ideal.mem_comap.mpr
        (by rw [show (φ : S →+* S') (algebraMap 𝒪 S π) = algebraMap 𝒪 S' π from φ.commutes π]; exact Ideal.subset_span rfl))))))

    (hN : IsUnit ((N : ℕ) : S ⧸ Ideal.span {algebraMap 𝒪 S π}))
    {ψ : Onr →ₐ[𝒪] S} {E : FakeEllipticCurve Λ N S} {E' : FakeEllipticCurve Λ N S'}
    (g : E'.A ⟶ E.A) (hg : FakeEllipticCurve.IsPullbackVia (φ : S →+* S') E E' g)

    (ρ₁ ρ₂ : FakeEllipticCurve.Rigidification r π A₀ ψ E)
    (ρ₁' ρ₂' : FakeEllipticCurve.Rigidification r π A₀ (φ.comp ψ) E')
    (h₁ : FakeEllipticCurve.Rigidification.IsPullbackVia φ g hg ρ₁ ρ₁')
    (h₂ : FakeEllipticCurve.Rigidification.IsPullbackVia φ g hg ρ₂ ρ₂')

    (ib' : ρ₁'.Eb.A ⟶ ρ₂'.Eb.A) (hib' : ib' ≫ ρ₂'.gb = ρ₁'.gb) (hibf' : ib' ≫ ρ₂'.Eb.f = ρ₁'.Eb.f)
    (uA' : ρ₂'.Ab.A ⟶ ρ₁'.Ab.A) (huA' : FakeEllipticCurve.IsPullbackVia (RingHom.id _) ρ₁'.Ab ρ₂'.Ab uA') (huAg' : uA' ≫ ρ₁'.gA = ρ₂'.gA)
    (A B : ℕ)
    (h : ib' ≫ ρ₂'.φ ≫ uA' ≫ ρ₁'.Ab.act ⟨(((r ^ A : ℕ) : ℤ) : ℚ), hΛℤ _⟩ = ρ₁'.φ ≫ ρ₁'.Ab.act ⟨(((r ^ B : ℕ) : ℤ) : ℚ), hΛℤ _⟩) :
    ∃ (ib : ρ₁.Eb.A ⟶ ρ₂.Eb.A) (_ : ib ≫ ρ₂.gb = ρ₁.gb ≫ (Iso.refl E.A).hom) (_ : ib ≫ ρ₂.Eb.f = ρ₁.Eb.f)
      (uA : ρ₂.Ab.A ⟶ ρ₁.Ab.A) (_ : FakeEllipticCurve.IsPullbackVia (RingHom.id _) ρ₁.Ab ρ₂.Ab uA) (_ : uA ≫ ρ₁.gA = ρ₂.gA),
      ib ≫ ρ₂.φ ≫ uA ≫ ρ₁.Ab.act ⟨(((r ^ A : ℕ) : ℤ) : ℚ), hΛℤ _⟩ = ρ₁.φ ≫ ρ₁.Ab.act ⟨(((r ^ B : ℕ) : ℤ) : ℚ), hΛℤ _⟩ := by
  obtain ⟨hsq₁E, -, -, -⟩ := ρ₁.isPullback_Eb
  obtain ⟨hsq₂E, -, -, -⟩ := ρ₂.isPullback_Eb

  have wE : ρ₁.gb ≫ E.f = ρ₁.Eb.f ≫ Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (Ideal.span {algebraMap 𝒪 S π}))) :=
    hsq₁E.w
  let ib : ρ₁.Eb.A ⟶ ρ₂.Eb.A := hsq₂E.lift ρ₁.gb ρ₁.Eb.f wE
  have hib : ib ≫ ρ₂.gb = ρ₁.gb := hsq₂E.lift_fst _ _ _
  have hibf : ib ≫ ρ₂.Eb.f = ρ₁.Eb.f := hsq₂E.lift_snd _ _ _

  obtain ⟨uA, huAg, huAf, huA⟩ :=
    CerednikDrinfeld.QM.FakeEllipticCurve.exists_isPullbackVia_id_comp_eq_of_isPullbackVia_of_isPullbackVia_of_isUnit
      _ hN A₀ ρ₁.Ab ρ₁.gA ρ₁.isPullback_Ab ρ₂.Ab ρ₂.gA ρ₂.isPullback_Ab
  refine ⟨ib, by rw [Iso.refl_hom, Category.comp_id]; exact hib, hibf, uA, huA, huAg, ?_⟩

  obtain ⟨ub₁, uA₁, hub₁, hub₁g, huA₁, huA₁g, -, hsq₁⟩ := h₁
  obtain ⟨ub₂, uA₂, hub₂, hub₂g, huA₂, huA₂g, -, hsq₂⟩ := h₂
  obtain ⟨hub₁sq, -, -, -⟩ := hub₁
  obtain ⟨hub₂sq, -, -, -⟩ := hub₂
  obtain ⟨huA₁sq, -, huA₁act, -⟩ := huA₁
  obtain ⟨huA₂sq, -, -, -⟩ := huA₂
  obtain ⟨huAsq, -, -, -⟩ := huA
  obtain ⟨huA'sq, -, -, -⟩ := huA'
  obtain ⟨hsq₁A, -, -, -⟩ := ρ₁.isPullback_Ab

  haveI : IsIso (CommRingCat.ofHom (Ideal.quotientMap (Ideal.span {algebraMap 𝒪 S' π}) (φ : S →+* S')
      (Ideal.span_le.mpr (Set.singleton_subset_iff.mpr (Ideal.mem_comap.mpr
        (by rw [show (φ : S →+* S') (algebraMap 𝒪 S π) = algebraMap 𝒪 S' π from φ.commutes π]; exact Ideal.subset_span rfl)))))) :=
    (RingEquiv.ofBijective _ hφ).toCommRingCatIso.isIso_hom
  haveI : IsIso ub₁ := hub₁sq.isIso_fst_of_isIso

  have hii : ub₁ ≫ ib = ib' ≫ ub₂ := by
    apply hsq₂E.hom_ext
    · simp only [Category.assoc]
      rw [hib, hub₁g, hub₂g, ← Category.assoc, hib']
    · simp only [Category.assoc]
      rw [hibf, hub₁sq.w, hub₂sq.w, ← Category.assoc, hibf']

  have e2 : uA ≫ ρ₁.Ab.f = ρ₂.Ab.f := huAf
  have e3 : uA' ≫ ρ₁'.Ab.f = ρ₂'.Ab.f := by
    have := huA'sq.w
    rw [CommRingCat.ofHom_id] at this
    erw [Spec.map_id] at this
    rw [Category.comp_id] at this
    exact this
  have hiii : uA' ≫ uA₁ = uA₂ ≫ uA := by
    apply hsq₁A.hom_ext
    · simp only [Category.assoc]
      rw [huA₁g, huAg, huAg', huA₂g]
    · simp only [Category.assoc]
      rw [huA₁sq.w, e2, ← Category.assoc, e3, huA₂sq.w]

  rw [← cancel_epi ub₁]
  calc ub₁ ≫ ib ≫ ρ₂.φ ≫ uA ≫ ρ₁.Ab.act ⟨(((r ^ A : ℕ) : ℤ) : ℚ), hΛℤ _⟩
      = (ub₁ ≫ ib) ≫ ρ₂.φ ≫ uA ≫ ρ₁.Ab.act ⟨(((r ^ A : ℕ) : ℤ) : ℚ), hΛℤ _⟩ := by simp only [Category.assoc]
    _ = (ib' ≫ ub₂) ≫ ρ₂.φ ≫ uA ≫ ρ₁.Ab.act ⟨(((r ^ A : ℕ) : ℤ) : ℚ), hΛℤ _⟩ := by rw [hii]
    _ = ib' ≫ (ub₂ ≫ ρ₂.φ) ≫ uA ≫ ρ₁.Ab.act ⟨(((r ^ A : ℕ) : ℤ) : ℚ), hΛℤ _⟩ := by simp only [Category.assoc]
    _ = ib' ≫ (ρ₂'.φ ≫ uA₂) ≫ uA ≫ ρ₁.Ab.act ⟨(((r ^ A : ℕ) : ℤ) : ℚ), hΛℤ _⟩ := by rw [hsq₂]
    _ = ib' ≫ ρ₂'.φ ≫ (uA₂ ≫ uA) ≫ ρ₁.Ab.act ⟨(((r ^ A : ℕ) : ℤ) : ℚ), hΛℤ _⟩ := by simp only [Category.assoc]
    _ = ib' ≫ ρ₂'.φ ≫ (uA' ≫ uA₁) ≫ ρ₁.Ab.act ⟨(((r ^ A : ℕ) : ℤ) : ℚ), hΛℤ _⟩ := by rw [hiii]
    _ = ib' ≫ ρ₂'.φ ≫ uA' ≫ (uA₁ ≫ ρ₁.Ab.act ⟨(((r ^ A : ℕ) : ℤ) : ℚ), hΛℤ _⟩) := by simp only [Category.assoc]
    _ = ib' ≫ ρ₂'.φ ≫ uA' ≫ (ρ₁'.Ab.act ⟨(((r ^ A : ℕ) : ℤ) : ℚ), hΛℤ _⟩ ≫ uA₁) := by rw [huA₁act]
    _ = (ib' ≫ ρ₂'.φ ≫ uA' ≫ ρ₁'.Ab.act ⟨(((r ^ A : ℕ) : ℤ) : ℚ), hΛℤ _⟩) ≫ uA₁ := by simp only [Category.assoc]
    _ = (ρ₁'.φ ≫ ρ₁'.Ab.act ⟨(((r ^ B : ℕ) : ℤ) : ℚ), hΛℤ _⟩) ≫ uA₁ := by rw [h]
    _ = ρ₁'.φ ≫ (ρ₁'.Ab.act ⟨(((r ^ B : ℕ) : ℤ) : ℚ), hΛℤ _⟩ ≫ uA₁) := by simp only [Category.assoc]
    _ = ρ₁'.φ ≫ (uA₁ ≫ ρ₁.Ab.act ⟨(((r ^ B : ℕ) : ℤ) : ℚ), hΛℤ _⟩) := by rw [huA₁act]
    _ = (ρ₁'.φ ≫ uA₁) ≫ ρ₁.Ab.act ⟨(((r ^ B : ℕ) : ℤ) : ℚ), hΛℤ _⟩ := by simp only [Category.assoc]
    _ = (ub₁ ≫ ρ₁.φ) ≫ ρ₁.Ab.act ⟨(((r ^ B : ℕ) : ℤ) : ℚ), hΛℤ _⟩ := by rw [hsq₁]
    _ = ub₁ ≫ ρ₁.φ ≫ ρ₁.Ab.act ⟨(((r ^ B : ℕ) : ℤ) : ℚ), hΛℤ _⟩ := by simp only [Category.assoc]

end We89Transfer

namespace We89Bits

theorem quotientMap_bijective_of_tower
    (𝒪 : Type) [CommRing 𝒪] (π : 𝒪) (C : Type) [CommRing C] [Algebra 𝒪 C]
    (S : Type) [CommRing S] [Algebra C S] [Algebra 𝒪 S] [IsScalarTower 𝒪 C S] :
    Function.Bijective (Ideal.quotientMap
      (Ideal.span {algebraMap 𝒪 (S ⧸ Ideal.span {algebraMap C S (algebraMap 𝒪 C π)}) π})
      (((Ideal.Quotient.mkₐ C (Ideal.span {algebraMap C S (algebraMap 𝒪 C π)})).restrictScalars 𝒪 :
          S →ₐ[𝒪] S ⧸ Ideal.span {algebraMap C S (algebraMap 𝒪 C π)}) :
        S →+* S ⧸ Ideal.span {algebraMap C S (algebraMap 𝒪 C π)})
      (Ideal.span_le.mpr (Set.singleton_subset_iff.mpr (Ideal.mem_comap.mpr
        (by rw [show (((Ideal.Quotient.mkₐ C (Ideal.span {algebraMap C S (algebraMap 𝒪 C π)})).restrictScalars 𝒪 :
                  S →ₐ[𝒪] S ⧸ Ideal.span {algebraMap C S (algebraMap 𝒪 C π)}) :
                    S →+* S ⧸ Ideal.span {algebraMap C S (algebraMap 𝒪 C π)}) (algebraMap 𝒪 S π) =
                  algebraMap 𝒪 (S ⧸ Ideal.span {algebraMap C S (algebraMap 𝒪 C π)}) π from
                ((Ideal.Quotient.mkₐ C (Ideal.span {algebraMap C S (algebraMap 𝒪 C π)})).restrictScalars 𝒪).commutes π]
            exact Ideal.subset_span rfl))))) := by

  have hI : algebraMap C S (algebraMap 𝒪 C π) = algebraMap 𝒪 S π := (IsScalarTower.algebraMap_apply 𝒪 C S π).symm
  have h0 : algebraMap 𝒪 (S ⧸ Ideal.span {algebraMap C S (algebraMap 𝒪 C π)}) π = 0 := by
    show Ideal.Quotient.mk (Ideal.span {algebraMap C S (algebraMap 𝒪 C π)}) (algebraMap 𝒪 S π) = 0
    rw [Ideal.Quotient.eq_zero_iff_mem, ← hI]
    exact Ideal.subset_span rfl
  constructor
  · apply Ideal.quotientMap_injective'
    intro x hx
    rw [Ideal.mem_comap, h0, Ideal.span_singleton_eq_bot.mpr rfl, Ideal.mem_bot] at hx

    have hx' : Ideal.Quotient.mk (Ideal.span {algebraMap C S (algebraMap 𝒪 C π)}) x = 0 := hx
    rw [Ideal.Quotient.eq_zero_iff_mem, hI] at hx'
    exact hx'
  · apply Ideal.quotientMap_surjective
    exact Ideal.Quotient.mk_surjective

theorem tM_natural
    {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} {N : ℕ}
    (𝒪 : Type) [CommRing 𝒪] (n : ℕ) (M : Scheme.{0}) (fM : M ⟶ Spec (CommRingCat.of 𝒪))
    (ptF : ∀ (S : Type) [CommRing S] (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of 𝒪)),
      FakeEllipticCurve.WithFullLevel Λ N n S → SchemeHomOver s fM)
    (hM : IsFineModuli Λ N n M fM ptF)
    (C : Type) [CommRing C] [Algebra 𝒪 C]
    (tM : ∀ (T : Type) [CommRing T] [Algebra C T],
      FakeEllipticCurve.WithFullLevel Λ N n T → SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap C T))) (Limits.pullback.snd fM (Spec.map (CommRingCat.ofHom (algebraMap 𝒪 C)))))
    (htM : ∀ (T : Type) [CommRing T] [Algebra C T] [Algebra 𝒪 T] [IsScalarTower 𝒪 C T]
        (u : FakeEllipticCurve.WithFullLevel Λ N n T),
        (tM T u).1 ≫ Limits.pullback.fst fM (Spec.map (CommRingCat.ofHom (algebraMap 𝒪 C))) = (ptF T (Spec.map (CommRingCat.ofHom (algebraMap 𝒪 T))) u).1) :
    ∀ (S S' : Type) [CommRing S] [Algebra C S] [CommRing S'] [Algebra C S'] (φ : S →ₐ[C] S')
      (u : FakeEllipticCurve.WithFullLevel Λ N n S) (u' : FakeEllipticCurve.WithFullLevel Λ N n S')
      (g' : u'.1.A ⟶ u.1.A), FakeEllipticCurve.IsPullbackVia (φ : S →+* S') u.1 u'.1 g' →
      (u'.2.P).1 ≫ g' = Spec.map (CommRingCat.ofHom (φ : S →+* S')) ≫ (u.2.P).1 →
      (tM S' u').1 = Spec.map (CommRingCat.ofHom (φ : S →+* S')) ≫ (tM S u).1 := by
  intro S S' _ _ _ _ φ u u' g' hg hP
  letI iS : Algebra 𝒪 S := ((algebraMap C S).comp (algebraMap 𝒪 C)).toAlgebra
  haveI : IsScalarTower 𝒪 C S := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  letI iS' : Algebra 𝒪 S' := ((algebraMap C S').comp (algebraMap 𝒪 C)).toAlgebra
  haveI : IsScalarTower 𝒪 C S' := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  obtain ⟨hsq, hmul, hact, hlev⟩ := hg
  have hpb : FakeEllipticCurve.WithFullLevel.IsPullback (φ : S →+* S') u u' := ⟨g', hsq, hmul, hact, hlev, hP⟩
  have hφ𝒪 : (φ : S →+* S').comp (algebraMap 𝒪 S) = algebraMap 𝒪 S' := by
    show (φ : S →+* S').comp ((algebraMap C S).comp (algebraMap 𝒪 C)) = (algebraMap C S').comp (algebraMap 𝒪 C)
    rw [← RingHom.comp_assoc, φ.comp_algebraMap]
  have hs : Spec.map (CommRingCat.ofHom (φ : S →+* S')) ≫ Spec.map (CommRingCat.ofHom (algebraMap 𝒪 S)) =
      Spec.map (CommRingCat.ofHom (algebraMap 𝒪 S')) := by
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, hφ𝒪]
  apply Limits.pullback.hom_ext
  · rw [Category.assoc, htM S u, htM S' u']
    exact hM.ptF_pullback S S' (φ : S →+* S') _ _ hs u u' hpb
  · rw [Category.assoc, (tM S u).2, (tM S' u').2, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
    congr 2
    exact φ.comp_algebraMap.symm

end We89Bits

namespace We88PtxNat

theorem ptX_natural
    {r N : ℕ} [Fact r.Prime] [NeZero N] (hrN : ¬ r ∣ N) {rbar : ℕ} [Fact rbar.Prime] (hrr : rbar ≠ r)

    (𝒪 : Type) [CommRing 𝒪] (π : 𝒪) (hunr : Ideal.span {((r : ℕ) : 𝒪)} = Ideal.span {π}) (Onr : Type) [CommRing Onr] [Algebra 𝒪 Onr]
    {a b : ℚ} (hBq : IsIndefiniteRamifiedExactlyAt a b r rbar)
    (Λ : Submodule ℤ ℍ[ℚ, a, b]) (hΛ : IsMaximalOrder Λ) (hΛℤ : ∀ m : ℤ, ((m : ℚ) : ℍ[ℚ, a, b]) ∈ Λ)

    (coord : ↥Λ → Zp2 r × Zp2 r) (hcoord : IsOrderCoord Λ r coord)
    (A₀ : FakeEllipticCurve Λ N (Onr ⧸ Ideal.span {algebraMap 𝒪 Onr π}))

    (n : ℕ) (hn : 3 ≤ n) (hrn : ¬ r ∣ n) (M : Scheme.{0}) (fM : M ⟶ Spec (CommRingCat.of 𝒪))
    (ptF : ∀ (S : Type) [CommRing S] (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of 𝒪)),
      FakeEllipticCurve.WithFullLevel Λ N n S → SchemeHomOver s fM)
    (hM : IsFineModuli Λ N n M fM ptF)

    (C : Type) [CommRing C] [IsNoetherianRing C] [Algebra 𝒪 C] (hC : IsNilpotent (algebraMap 𝒪 C π)) (ψ : Onr →ₐ[𝒪] C)

    (X : ℕ → Scheme.{0}) (ξ : ∀ d, X d ⟶ Limits.pullback fM (Spec.map (CommRingCat.ofHom (algebraMap 𝒪 C))))
    (tM : ∀ (T : Type) [CommRing T] [Algebra C T],
      FakeEllipticCurve.WithFullLevel Λ N n T → SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap C T))) (Limits.pullback.snd fM (Spec.map (CommRingCat.ofHom (algebraMap 𝒪 C)))))
    (xOf : ∀ (T : Type) [CommRing T] [Algebra C T] [Algebra 𝒪 T] [IsScalarTower 𝒪 C T]
      (ψT : Onr →ₐ[𝒪] T) (_ : ψT = (IsScalarTower.toAlgHom 𝒪 C T).comp ψ)
      (u : FakeEllipticCurve.WithFullLevel Λ N n T) (ρ : FakeEllipticCurve.Rigidification r π A₀ ψT u.1),
      { x : Spec (CommRingCat.of (T ⧸ Ideal.span {algebraMap C T (algebraMap 𝒪 C π)})) ⟶ X ρ.d //
        x ≫ ξ ρ.d = Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (Ideal.span {algebraMap C T (algebraMap 𝒪 C π)}))) ≫ (tM T u).1 })

    (hxOf : ∀ (S S' : Type) [CommRing S] [Algebra C S] [Algebra 𝒪 S] [IsScalarTower 𝒪 C S]
        [CommRing S'] [Algebra C S'] [Algebra 𝒪 S'] [IsScalarTower 𝒪 C S'] (φ : S →ₐ[C] S')
        (ψS : Onr →ₐ[𝒪] S) (hψS : ψS = (IsScalarTower.toAlgHom 𝒪 C S).comp ψ)
        (hψS' : (φ.restrictScalars 𝒪).comp ψS = (IsScalarTower.toAlgHom 𝒪 C S').comp ψ)
        (u : FakeEllipticCurve.WithFullLevel Λ N n S) (u' : FakeEllipticCurve.WithFullLevel Λ N n S')
        (ρ : FakeEllipticCurve.Rigidification r π A₀ ψS u.1)
        (ρ' : FakeEllipticCurve.Rigidification r π A₀ ((φ.restrictScalars 𝒪).comp ψS) u'.1)
        (g : u'.1.A ⟶ u.1.A) (hg : FakeEllipticCurve.IsPullbackVia (φ : S →+* S') u.1 u'.1 g),
        (u'.2.P).1 ≫ g = Spec.map (CommRingCat.ofHom (φ : S →+* S')) ≫ (u.2.P).1 →
        FakeEllipticCurve.Rigidification.IsPullbackVia (φ.restrictScalars 𝒪) g hg ρ ρ' →
          ∃ hd : ρ'.d = ρ.d, (xOf S' ((φ.restrictScalars 𝒪).comp ψS) hψS' u' ρ').1 ≫ eqToHom (congrArg X hd) =
            Spec.map (CommRingCat.ofHom (RigidifiedPairClass.qmap (algebraMap 𝒪 C π) φ)) ≫ (xOf S ψS hψS u ρ).1) :
    (∀ (d : ℕ) (T T' : Type) [CommRing T] [Algebra C T] [Algebra 𝒪 T] [IsScalarTower 𝒪 C T]
                [CommRing T'] [Algebra C T'] [Algebra 𝒪 T'] [IsScalarTower 𝒪 C T'] (φ : T →ₐ[C] T')
                (ψT : Onr →ₐ[𝒪] T) (hψT : ψT = (IsScalarTower.toAlgHom 𝒪 C T).comp ψ)
                (hψT' : (φ.restrictScalars 𝒪).comp ψT = (IsScalarTower.toAlgHom 𝒪 C T').comp ψ)
                (u : FakeEllipticCurve.WithFullLevel Λ N n T) (u' : FakeEllipticCurve.WithFullLevel Λ N n T')
                (ρ : FakeEllipticCurve.Rigidification r π A₀ ψT u.1)
                (ρ' : FakeEllipticCurve.Rigidification r π A₀ ((φ.restrictScalars 𝒪).comp ψT) u'.1)
                (g : u'.1.A ⟶ u.1.A) (hg : FakeEllipticCurve.IsPullbackVia (φ : T →+* T') u.1 u'.1 g)
                (hd : ρ.d = d) (hd' : ρ'.d = d) (h0 : algebraMap C T (algebraMap 𝒪 C π) = 0) (h0' : algebraMap C T' (algebraMap 𝒪 C π) = 0),
                (u'.2.P).1 ≫ g = Spec.map (CommRingCat.ofHom (φ : T →+* T')) ≫ (u.2.P).1 →
                FakeEllipticCurve.Rigidification.IsPullbackVia (φ.restrictScalars 𝒪) g hg ρ ρ' →
                  ((RigidifiedPairClass.ptX 𝒪 π Onr Λ A₀ n C ψ (Limits.pullback.snd fM (Spec.map (CommRingCat.ofHom (algebraMap 𝒪 C)))) X ξ tM xOf) d T' ((φ.restrictScalars 𝒪).comp ψT) hψT' u' ρ' hd' h0').1 =
                    Spec.map (CommRingCat.ofHom (φ : T →+* T')) ≫ ((RigidifiedPairClass.ptX 𝒪 π Onr Λ A₀ n C ψ (Limits.pullback.snd fM (Spec.map (CommRingCat.ofHom (algebraMap 𝒪 C)))) X ξ tM xOf) d T ψT hψT u ρ hd h0).1) := by
  intro d T T' _ _ _ _ _ _ _ _ φ ψT hψT hψT' u u' ρ ρ' g hg hd hd' h0 h0' hP hρ
  obtain ⟨hd₀, hx⟩ := hxOf T T' φ ψT hψT hψT' u u' ρ ρ' g hg hP hρ
  subst hd
  show Spec.map (CommRingCat.ofHom
        (((Ideal.quotEquivOfEq (Ideal.span_singleton_eq_bot.mpr h0')).trans (RingEquiv.quotientBot T')).toRingHom)) ≫
        (xOf T' ((φ.restrictScalars 𝒪).comp ψT) hψT' u' ρ').1 ≫ eqToHom (congrArg X hd₀) =
      Spec.map (CommRingCat.ofHom (φ : T →+* T')) ≫
        (Spec.map (CommRingCat.ofHom
          (((Ideal.quotEquivOfEq (Ideal.span_singleton_eq_bot.mpr h0)).trans (RingEquiv.quotientBot T)).toRingHom)) ≫
          (xOf T ψT hψT u ρ).1 ≫ eqToHom (congrArg X rfl))
  rw [hx, eqToHom_refl, Category.comp_id, ← Category.assoc, ← Category.assoc, ← Spec.map_comp, ← Spec.map_comp,
    ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp]
  have key :
      (((Ideal.quotEquivOfEq (Ideal.span_singleton_eq_bot.mpr h0')).trans (RingEquiv.quotientBot T')).toRingHom).comp
          (RigidifiedPairClass.qmap (algebraMap 𝒪 C π) φ) =
        (φ : T →+* T').comp
          ((Ideal.quotEquivOfEq (Ideal.span_singleton_eq_bot.mpr h0)).trans (RingEquiv.quotientBot T)).toRingHom := by
    apply Ideal.Quotient.ringHom_ext
    rw [RingHom.comp_assoc, RingHom.comp_assoc, RigidifiedPairClass.qmap_comp_mk, ← RingHom.comp_assoc,
      RigidifiedPairClass.quotEquiv_comp_mk (algebraMap 𝒪 C π) T' h0',
      RigidifiedPairClass.quotEquiv_comp_mk (algebraMap 𝒪 C π) T h0]
    ext x
    rfl
  rw [key]

end We88PtxNat

namespace We88Piece

theorem mapPt_trans {R : Type} [CommRing R] {A A' A'' : Scheme.{0}}
    {f : A ⟶ Spec (CommRingCat.of R)} {f' : A' ⟶ Spec (CommRingCat.of R)} {f'' : A'' ⟶ Spec (CommRingCat.of R)}
    (i : A ≅ A') (hi : i.hom ≫ f' = f) (j : A' ≅ A'') (hj : j.hom ≫ f'' = f') (hij : (i ≪≫ j).hom ≫ f'' = f)
    {T : Scheme.{0}} {t : T ⟶ Spec (CommRingCat.of R)} (P : SchemeHomOver t f) :
    mapPt (i ≪≫ j).hom hij P = mapPt j.hom hj (mapPt i.hom hi P) :=
  Subtype.ext (by simp only [mapPt_coe, Iso.trans_hom, Category.assoc])

theorem isoVia_trans {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} {N n : ℕ} {S : Type} [CommRing S]
    (u u' u'' : FakeEllipticCurve.WithFullLevel Λ N n S)
    (i : u.1.A ≅ u'.1.A) (hi : i.hom ≫ u'.1.f = u.1.f) (hI : FakeEllipticCurve.WithFullLevel.IsoVia u u' i hi)
    (j : u'.1.A ≅ u''.1.A) (hj : j.hom ≫ u''.1.f = u'.1.f) (hJ : FakeEllipticCurve.WithFullLevel.IsoVia u' u'' j hj) :
    ∃ hij : (i ≪≫ j).hom ≫ u''.1.f = u.1.f, FakeEllipticCurve.WithFullLevel.IsoVia u u'' (i ≪≫ j) hij := by
  have hij : (i ≪≫ j).hom ≫ u''.1.f = u.1.f := by rw [Iso.trans_hom, Category.assoc, hj, hi]
  obtain ⟨hImul, hIact, hIlev, hIP⟩ := hI
  obtain ⟨hJmul, hJact, hJlev, hJP⟩ := hJ
  refine ⟨hij, ?_, ?_, ?_, ?_⟩
  · intro T t P Q
    rw [mapPt_trans i hi j hj hij, mapPt_trans i hi j hj hij, mapPt_trans i hi j hj hij, hImul, hJmul]
  · intro x
    rw [Iso.trans_hom, ← Category.assoc, hIact, Category.assoc, hJact, Category.assoc]
  · intro T t P
    rw [mapPt_trans i hi j hj hij, hIlev, hJlev]
  · rw [mapPt_trans i hi j hj hij, hIP, hJP]

theorem corr_pullback_of_relLoc_piece
    {r N : ℕ} [Fact r.Prime] [NeZero N] (hrN : ¬ r ∣ N) {rbar : ℕ} [Fact rbar.Prime] (hrr : rbar ≠ r)

    (𝒪 : Type) [CommRing 𝒪] (π : 𝒪) (hunr : Ideal.span {((r : ℕ) : 𝒪)} = Ideal.span {π}) (Onr : Type) [CommRing Onr] [Algebra 𝒪 Onr]
    {a b : ℚ} (hBq : IsIndefiniteRamifiedExactlyAt a b r rbar)
    (Λ : Submodule ℤ ℍ[ℚ, a, b]) (hΛ : IsMaximalOrder Λ) (hΛℤ : ∀ m : ℤ, ((m : ℚ) : ℍ[ℚ, a, b]) ∈ Λ)

    (coord : ↥Λ → Zp2 r × Zp2 r) (hcoord : IsOrderCoord Λ r coord)
    (A₀ : FakeEllipticCurve Λ N (Onr ⧸ Ideal.span {algebraMap 𝒪 Onr π}))

    (n : ℕ) (hn : 3 ≤ n) (hrn : ¬ r ∣ n) (M : Scheme.{0}) (fM : M ⟶ Spec (CommRingCat.of 𝒪))
    (ptF : ∀ (S : Type) [CommRing S] (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of 𝒪)),
      FakeEllipticCurve.WithFullLevel Λ N n S → SchemeHomOver s fM)
    (hM : IsFineModuli Λ N n M fM ptF)

    (C : Type) [CommRing C] [IsNoetherianRing C] [Algebra 𝒪 C] (hC : IsNilpotent (algebraMap 𝒪 C π)) (ψ : Onr →ₐ[𝒪] C)

    (X : ℕ → Scheme.{0}) (ξ : ∀ d, X d ⟶ Limits.pullback fM (Spec.map (CommRingCat.ofHom (algebraMap 𝒪 C))))
    (tM : ∀ (T : Type) [CommRing T] [Algebra C T],
      FakeEllipticCurve.WithFullLevel Λ N n T → SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap C T))) (Limits.pullback.snd fM (Spec.map (CommRingCat.ofHom (algebraMap 𝒪 C)))))
    (xOf : ∀ (T : Type) [CommRing T] [Algebra C T] [Algebra 𝒪 T] [IsScalarTower 𝒪 C T]
      (ψT : Onr →ₐ[𝒪] T) (_ : ψT = (IsScalarTower.toAlgHom 𝒪 C T).comp ψ)
      (u : FakeEllipticCurve.WithFullLevel Λ N n T) (ρ : FakeEllipticCurve.Rigidification r π A₀ ψT u.1),
      { x : Spec (CommRingCat.of (T ⧸ Ideal.span {algebraMap C T (algebraMap 𝒪 C π)})) ⟶ X ρ.d //
        x ≫ ξ ρ.d = Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (Ideal.span {algebraMap C T (algebraMap 𝒪 C π)}))) ≫ (tM T u).1 })

    (hx4 : (∀ (d : ℕ) (T : Type) [CommRing T] [Algebra C T] [Algebra 𝒪 T] [IsScalarTower 𝒪 C T]
                (ψT : Onr →ₐ[𝒪] T) (hψT : ψT = (IsScalarTower.toAlgHom 𝒪 C T).comp ψ)
                (h0 : algebraMap C T (algebraMap 𝒪 C π) = 0)
                (u u' : FakeEllipticCurve.WithFullLevel Λ N n T)
                (ρ : FakeEllipticCurve.Rigidification r π A₀ ψT u.1) (ρ' : FakeEllipticCurve.Rigidification r π A₀ ψT u'.1)
                (hd : ρ.d = d) (hd' : ρ'.d = d),
                ((RigidifiedPairClass.ptX 𝒪 π Onr Λ A₀ n C ψ (Limits.pullback.snd fM (Spec.map (CommRingCat.ofHom (algebraMap 𝒪 C)))) X ξ tM xOf) d T ψT hψT u ρ hd h0 = (RigidifiedPairClass.ptX 𝒪 π Onr Λ A₀ n C ψ (Limits.pullback.snd fM (Spec.map (CommRingCat.ofHom (algebraMap 𝒪 C)))) X ξ tM xOf) d T ψT hψT u' ρ' hd' h0 ↔
                  ∃ (i : u.1.A ≅ u'.1.A) (hi : i.hom ≫ u'.1.f = u.1.f), FakeEllipticCurve.WithFullLevel.IsoVia u u' i hi ∧
                    ∃ (ib : ρ.Eb.A ⟶ ρ'.Eb.A) (_ : ib ≫ ρ'.gb = ρ.gb ≫ i.hom) (_ : ib ≫ ρ'.Eb.f = ρ.Eb.f)
                      (uA : ρ'.Ab.A ⟶ ρ.Ab.A) (_ : FakeEllipticCurve.IsPullbackVia (RingHom.id _) ρ.Ab ρ'.Ab uA) (_ : uA ≫ ρ.gA = ρ'.gA),
                      ib ≫ ρ'.φ ≫ uA = ρ.φ)))

    (hxOf : ∀ (S S' : Type) [CommRing S] [Algebra C S] [Algebra 𝒪 S] [IsScalarTower 𝒪 C S]
        [CommRing S'] [Algebra C S'] [Algebra 𝒪 S'] [IsScalarTower 𝒪 C S'] (φ : S →ₐ[C] S')
        (ψS : Onr →ₐ[𝒪] S) (hψS : ψS = (IsScalarTower.toAlgHom 𝒪 C S).comp ψ)
        (hψS' : (φ.restrictScalars 𝒪).comp ψS = (IsScalarTower.toAlgHom 𝒪 C S').comp ψ)
        (u : FakeEllipticCurve.WithFullLevel Λ N n S) (u' : FakeEllipticCurve.WithFullLevel Λ N n S')
        (ρ : FakeEllipticCurve.Rigidification r π A₀ ψS u.1)
        (ρ' : FakeEllipticCurve.Rigidification r π A₀ ((φ.restrictScalars 𝒪).comp ψS) u'.1)
        (g : u'.1.A ⟶ u.1.A) (hg : FakeEllipticCurve.IsPullbackVia (φ : S →+* S') u.1 u'.1 g),
        (u'.2.P).1 ≫ g = Spec.map (CommRingCat.ofHom (φ : S →+* S')) ≫ (u.2.P).1 →
        FakeEllipticCurve.Rigidification.IsPullbackVia (φ.restrictScalars 𝒪) g hg ρ ρ' →
          ∃ hd : ρ'.d = ρ.d, (xOf S' ((φ.restrictScalars 𝒪).comp ψS) hψS' u' ρ').1 ≫ eqToHom (congrArg X hd) =
            Spec.map (CommRingCat.ofHom (RigidifiedPairClass.qmap (algebraMap 𝒪 C π) φ)) ≫ (xOf S ψS hψS u ρ).1)

    (T : Type) [CommRing T] [Algebra C T] [Algebra 𝒪 T] [IsScalarTower 𝒪 C T]
    (ψT : Onr →ₐ[𝒪] T) (hψT : ψT = (IsScalarTower.toAlgHom 𝒪 C T).comp ψ)
    (h0T : algebraMap C T (algebraMap 𝒪 C π) = 0)
    (u : FakeEllipticCurve.WithFullLevel Λ N n T)
    (ρ ρ' : FakeEllipticCurve.Rigidification r π A₀ ψT u.1)

    (L : Type) [CommRing L] [Algebra (T ⧸ Ideal.span {algebraMap C T (algebraMap 𝒪 C π)}) L] [Algebra C L]
    [IsScalarTower C (T ⧸ Ideal.span {algebraMap C T (algebraMap 𝒪 C π)}) L] [Algebra 𝒪 L] [IsScalarTower 𝒪 C L]
    (h0L : algebraMap C L (algebraMap 𝒪 C π) = 0)

    (hψL : (((IsScalarTower.toAlgHom C (T ⧸ Ideal.span {algebraMap C T (algebraMap 𝒪 C π)}) L).comp (Ideal.Quotient.mkₐ C (Ideal.span {algebraMap C T (algebraMap 𝒪 C π)}))).restrictScalars 𝒪).comp ψT = (IsScalarTower.toAlgHom 𝒪 C L).comp ψ)
    (uL : FakeEllipticCurve.WithFullLevel Λ N n L) (g : uL.1.A ⟶ u.1.A)
    (hg : FakeEllipticCurve.IsPullbackVia (((IsScalarTower.toAlgHom C (T ⧸ Ideal.span {algebraMap C T (algebraMap 𝒪 C π)}) L).comp (Ideal.Quotient.mkₐ C (Ideal.span {algebraMap C T (algebraMap 𝒪 C π)}))) : T →+* L) u.1 uL.1 g)
    (hP : (uL.2.P).1 ≫ g = Spec.map (CommRingCat.ofHom (((IsScalarTower.toAlgHom C (T ⧸ Ideal.span {algebraMap C T (algebraMap 𝒪 C π)}) L).comp (Ideal.Quotient.mkₐ C (Ideal.span {algebraMap C T (algebraMap 𝒪 C π)}))) : T →+* L)) ≫ (u.2.P).1)
    (ρL ρL' : FakeEllipticCurve.Rigidification r π A₀ ((((IsScalarTower.toAlgHom C (T ⧸ Ideal.span {algebraMap C T (algebraMap 𝒪 C π)}) L).comp (Ideal.Quotient.mkₐ C (Ideal.span {algebraMap C T (algebraMap 𝒪 C π)}))).restrictScalars 𝒪).comp ψT) uL.1)
    (hρL : FakeEllipticCurve.Rigidification.IsPullbackVia (((IsScalarTower.toAlgHom C (T ⧸ Ideal.span {algebraMap C T (algebraMap 𝒪 C π)}) L).comp (Ideal.Quotient.mkₐ C (Ideal.span {algebraMap C T (algebraMap 𝒪 C π)}))).restrictScalars 𝒪) g hg ρ ρL)
    (hρL' : FakeEllipticCurve.Rigidification.IsPullbackVia (((IsScalarTower.toAlgHom C (T ⧸ Ideal.span {algebraMap C T (algebraMap 𝒪 C π)}) L).comp (Ideal.Quotient.mkₐ C (Ideal.span {algebraMap C T (algebraMap 𝒪 C π)}))).restrictScalars 𝒪) g hg ρ' ρL')

    (v v' : FakeEllipticCurve.WithFullLevel Λ N n L)
    (ϱ : FakeEllipticCurve.Rigidification r π A₀ ((IsScalarTower.toAlgHom 𝒪 C L).comp ψ) v.1)
    (ϱ' : FakeEllipticCurve.Rigidification r π A₀ ((IsScalarTower.toAlgHom 𝒪 C L).comp ψ) v'.1)
    (hd : ϱ.d = ρ.d) (hd' : ϱ'.d = ρ'.d)
    (i₀ : v.1.A ≅ v'.1.A) (hi : i₀.hom ≫ v'.1.f = v.1.f) (hiso : FakeEllipticCurve.WithFullLevel.IsoVia v v' i₀ hi)
    (hcorr : ∃ (ib : ϱ.Eb.A ⟶ ϱ'.Eb.A) (_ : ib ≫ ϱ'.gb = ϱ.gb ≫ i₀.hom) (_ : ib ≫ ϱ'.Eb.f = ϱ.Eb.f)
        (uA : ϱ'.Ab.A ⟶ ϱ.Ab.A) (_ : FakeEllipticCurve.IsPullbackVia (RingHom.id _) ϱ.Ab ϱ'.Ab uA) (_ : uA ≫ ϱ.gA = ϱ'.gA)
        (i₁ j₁ : ℕ),
        ib ≫ ϱ'.φ ≫ uA ≫ ϱ.Ab.act ⟨(((r ^ i₁ : ℕ) : ℤ) : ℚ), hΛℤ _⟩ = ϱ.φ ≫ ϱ.Ab.act ⟨(((r ^ j₁ : ℕ) : ℤ) : ℚ), hΛℤ _⟩)
    (hx : ((RigidifiedPairClass.ptX 𝒪 π Onr Λ A₀ n C ψ (Limits.pullback.snd fM (Spec.map (CommRingCat.ofHom (algebraMap 𝒪 C)))) X ξ tM xOf) ρ.d L ((IsScalarTower.toAlgHom 𝒪 C L).comp ψ) rfl v ϱ hd h0L).1 =
      Spec.map (CommRingCat.ofHom (algebraMap (T ⧸ Ideal.span {algebraMap C T (algebraMap 𝒪 C π)}) L)) ≫ (xOf T ψT hψT u ρ).1)
    (hx' : ((RigidifiedPairClass.ptX 𝒪 π Onr Λ A₀ n C ψ (Limits.pullback.snd fM (Spec.map (CommRingCat.ofHom (algebraMap 𝒪 C)))) X ξ tM xOf) ρ'.d L ((IsScalarTower.toAlgHom 𝒪 C L).comp ψ) rfl v' ϱ' hd' h0L).1 =
      Spec.map (CommRingCat.ofHom (algebraMap (T ⧸ Ideal.span {algebraMap C T (algebraMap 𝒪 C π)}) L)) ≫ (xOf T ψT hψT u ρ').1) :
    ∃ (σ : uL.1.A ≅ uL.1.A) (hσ : σ.hom ≫ uL.1.f = uL.1.f), FakeEllipticCurve.WithFullLevel.IsoVia uL uL σ hσ ∧
      ∃ (ib : ρL.Eb.A ⟶ ρL'.Eb.A) (_ : ib ≫ ρL'.gb = ρL.gb ≫ σ.hom) (_ : ib ≫ ρL'.Eb.f = ρL.Eb.f)
      (uA : ρL'.Ab.A ⟶ ρL.Ab.A) (_ : FakeEllipticCurve.IsPullbackVia (RingHom.id _) ρL.Ab ρL'.Ab uA) (_ : uA ≫ ρL.gA = ρL'.gA)
      (i₁ j₁ : ℕ),
      ib ≫ ρL'.φ ≫ uA ≫ ρL.Ab.act ⟨(((r ^ i₁ : ℕ) : ℤ) : ℚ), hΛℤ _⟩ = ρL.φ ≫ ρL.Ab.act ⟨(((r ^ j₁ : ℕ) : ℤ) : ℚ), hΛℤ _⟩ := by
  classical

  obtain ⟨hdL, hxL⟩ := hxOf T L ((IsScalarTower.toAlgHom C (T ⧸ Ideal.span {algebraMap C T (algebraMap 𝒪 C π)}) L).comp (Ideal.Quotient.mkₐ C (Ideal.span {algebraMap C T (algebraMap 𝒪 C π)}))) ψT hψT hψL u uL ρ ρL g hg hP hρL
  obtain ⟨hdL', hxL'⟩ := hxOf T L ((IsScalarTower.toAlgHom C (T ⧸ Ideal.span {algebraMap C T (algebraMap 𝒪 C π)}) L).comp (Ideal.Quotient.mkₐ C (Ideal.span {algebraMap C T (algebraMap 𝒪 C π)}))) ψT hψT hψL u uL ρ' ρL' g hg hP hρL'
  clear hρL hρL'
  revert hψL ρL ρL' hdL hdL' hxL hxL'
  generalize hψ₁ : (((((IsScalarTower.toAlgHom C (T ⧸ Ideal.span {algebraMap C T (algebraMap 𝒪 C π)}) L).comp (Ideal.Quotient.mkₐ C (Ideal.span {algebraMap C T (algebraMap 𝒪 C π)})))).restrictScalars 𝒪).comp ψT) = ψ₁
  intro hψL ρL ρL' hdL hxL hdL' hxL'
  subst hψL

  have key : (((Ideal.quotEquivOfEq (Ideal.span_singleton_eq_bot.mpr h0L)).trans (RingEquiv.quotientBot L)).toRingHom).comp (RigidifiedPairClass.qmap (algebraMap 𝒪 C π) ((IsScalarTower.toAlgHom C (T ⧸ Ideal.span {algebraMap C T (algebraMap 𝒪 C π)}) L).comp (Ideal.Quotient.mkₐ C (Ideal.span {algebraMap C T (algebraMap 𝒪 C π)})))) = algebraMap (T ⧸ Ideal.span {algebraMap C T (algebraMap 𝒪 C π)}) L := by
    apply Ideal.Quotient.ringHom_ext
    rw [RingHom.comp_assoc, RigidifiedPairClass.qmap_comp_mk, ← RingHom.comp_assoc,
      RigidifiedPairClass.quotEquiv_comp_mk (algebraMap 𝒪 C π) L h0L]
    ext x
    rfl
  have e1 : (RigidifiedPairClass.ptX 𝒪 π Onr Λ A₀ n C ψ (Limits.pullback.snd fM (Spec.map (CommRingCat.ofHom (algebraMap 𝒪 C)))) X ξ tM xOf) ρ.d L ((IsScalarTower.toAlgHom 𝒪 C L).comp ψ) rfl uL ρL hdL h0L =
      (RigidifiedPairClass.ptX 𝒪 π Onr Λ A₀ n C ψ (Limits.pullback.snd fM (Spec.map (CommRingCat.ofHom (algebraMap 𝒪 C)))) X ξ tM xOf) ρ.d L ((IsScalarTower.toAlgHom 𝒪 C L).comp ψ) rfl v ϱ hd h0L := by
    apply Subtype.ext
    rw [hx]
    show Spec.map (CommRingCat.ofHom (((Ideal.quotEquivOfEq (Ideal.span_singleton_eq_bot.mpr h0L)).trans (RingEquiv.quotientBot L)).toRingHom)) ≫ (xOf L _ _ uL ρL).1 ≫ eqToHom (congrArg X hdL) = _
    rw [hxL, ← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp, key]
  have e2 : (RigidifiedPairClass.ptX 𝒪 π Onr Λ A₀ n C ψ (Limits.pullback.snd fM (Spec.map (CommRingCat.ofHom (algebraMap 𝒪 C)))) X ξ tM xOf) ρ'.d L ((IsScalarTower.toAlgHom 𝒪 C L).comp ψ) rfl v' ϱ' hd' h0L =
      (RigidifiedPairClass.ptX 𝒪 π Onr Λ A₀ n C ψ (Limits.pullback.snd fM (Spec.map (CommRingCat.ofHom (algebraMap 𝒪 C)))) X ξ tM xOf) ρ'.d L ((IsScalarTower.toAlgHom 𝒪 C L).comp ψ) rfl uL ρL' hdL' h0L := by
    apply Subtype.ext
    rw [hx']
    show _ = Spec.map (CommRingCat.ofHom (((Ideal.quotEquivOfEq (Ideal.span_singleton_eq_bot.mpr h0L)).trans (RingEquiv.quotientBot L)).toRingHom)) ≫ (xOf L _ _ uL ρL').1 ≫ eqToHom (congrArg X hdL')
    rw [hxL', ← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp, key]

  obtain ⟨j₁, hj₁, hJ₁, ib₁, hib₁g, hib₁f, uA₁, huA₁, huA₁g, hc₁⟩ :=
    (hx4 ρ.d L ((IsScalarTower.toAlgHom 𝒪 C L).comp ψ) rfl h0L uL v ρL ϱ hdL hd).mp e1
  obtain ⟨j₂, hj₂, hJ₂, ib₂, hib₂g, hib₂f, uA₂, huA₂, huA₂g, hc₂⟩ :=
    (hx4 ρ'.d L ((IsScalarTower.toAlgHom 𝒪 C L).comp ψ) rfl h0L v' uL ϱ' ρL' hd' hdL').mp e2
  obtain ⟨ib, hibg, hibf, uA, huA, huAg, a₁, b₁, hc⟩ := hcorr

  obtain ⟨h12, hI12⟩ := We88Piece.isoVia_trans uL v v' j₁ hj₁ hJ₁ i₀ hi hiso
  obtain ⟨h123, hI123⟩ := We88Piece.isoVia_trans uL v' uL (j₁ ≪≫ i₀) h12 hI12 j₂ hj₂ hJ₂
  have huA₁c := huA₁
  obtain ⟨-, -, huA₁act, -⟩ := huA₁c
  have hUA : FakeEllipticCurve.IsPullbackVia (RingHom.id _) ρL.Ab ρL'.Ab (uA₂ ≫ uA ≫ uA₁) := by
    have k12 := CerednikDrinfeld.QM.FakeEllipticCurve.IsPullbackVia.comp (RingHom.id _) (RingHom.id _)
      ρL.Ab ϱ.Ab ϱ'.Ab uA₁ uA huA₁ huA
    have k123 := CerednikDrinfeld.QM.FakeEllipticCurve.IsPullbackVia.comp _ (RingHom.id _)
      ρL.Ab ϱ'.Ab ρL'.Ab (uA ≫ uA₁) uA₂ k12 huA₂
    simpa only [RingHom.comp_id] using k123
  refine ⟨(j₁ ≪≫ i₀) ≪≫ j₂, h123, hI123, ib₁ ≫ ib ≫ ib₂, ?_, ?_, uA₂ ≫ uA ≫ uA₁, hUA, ?_, a₁, b₁, ?_⟩
  · simp only [Iso.trans_hom, Category.assoc]
    rw [hib₂g, reassoc_of% hibg, reassoc_of% hib₁g]
  · simp only [Category.assoc]
    rw [hib₂f, hibf, hib₁f]
  · simp only [Category.assoc]
    rw [huA₁g, huAg, huA₂g]
  · simp only [Category.assoc]
    rw [reassoc_of% hc₂, ← huA₁act, reassoc_of% hc, huA₁act, reassoc_of% hc₁]

end We88Piece

namespace GPShift
open CerednikDrinfeld.QM.FakeEllipticCurve

variable {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} {N : ℕ}

theorem act_rpow_comp {S : Type} [CommRing S]
    (hΛℤ : ∀ m : ℤ, ((m : ℚ) : ℍ[ℚ, a, b]) ∈ Λ) (E : FakeEllipticCurve Λ N S) (r m n : ℕ) :
    E.act ⟨(((r ^ m : ℕ) : ℤ) : ℚ), hΛℤ _⟩ ≫ E.act ⟨(((r ^ n : ℕ) : ℤ) : ℚ), hΛℤ _⟩ =
      E.act ⟨(((r ^ (m + n) : ℕ) : ℤ) : ℚ), hΛℤ _⟩ := by
  have e : ((((r ^ n : ℕ) : ℤ) : ℚ) : ℍ[ℚ, a, b]) * ((((r ^ m : ℕ) : ℤ) : ℚ) : ℍ[ℚ, a, b]) =
      ((((r ^ (m + n) : ℕ) : ℤ) : ℚ) : ℍ[ℚ, a, b]) := by
    rw [← QuaternionAlgebra.coe_mul]; congr 1; push_cast; ring
  have hmem : ((((r ^ n : ℕ) : ℤ) : ℚ) : ℍ[ℚ, a, b]) * ((((r ^ m : ℕ) : ℤ) : ℚ) : ℍ[ℚ, a, b]) ∈ Λ := e ▸ hΛℤ _
  rw [← E.act_mul ⟨(((r ^ n : ℕ) : ℤ) : ℚ), hΛℤ _⟩ ⟨(((r ^ m : ℕ) : ℤ) : ℚ), hΛℤ _⟩ hmem]
  congr 1
  exact Subtype.ext e

theorem act_comm_intCast {S : Type} [CommRing S]
    (hΛℤ : ∀ m : ℤ, ((m : ℚ) : ℍ[ℚ, a, b]) ∈ Λ) (E : FakeEllipticCurve Λ N S) (m : ℤ) (x : ↥Λ) :
    E.act x ≫ E.act ⟨((m : ℚ) : ℍ[ℚ, a, b]), hΛℤ m⟩ = E.act ⟨((m : ℚ) : ℍ[ℚ, a, b]), hΛℤ m⟩ ≫ E.act x := by
  have e1 : (((m : ℚ)) : ℍ[ℚ, a, b]) * (x : ℍ[ℚ, a, b]) = (x : ℍ[ℚ, a, b]) * (((m : ℚ)) : ℍ[ℚ, a, b]) := by
    rw [QuaternionAlgebra.coe_mul_eq_smul, QuaternionAlgebra.mul_coe_eq_smul]
  have hmem : (x : ℍ[ℚ, a, b]) * (((m : ℚ)) : ℍ[ℚ, a, b]) ∈ Λ := by
    rw [QuaternionAlgebra.mul_coe_eq_smul, Int.cast_smul_eq_zsmul]
    exact Λ.smul_mem _ x.2
  have hmem' : (((m : ℚ)) : ℍ[ℚ, a, b]) * (x : ℍ[ℚ, a, b]) ∈ Λ := e1 ▸ hmem
  rw [← E.act_mul _ x hmem', ← E.act_mul x _ hmem]
  congr 1; exact Subtype.ext e1

theorem act_natCast_eq {S : Type} [CommRing S]
    (hΛℤ : ∀ m : ℤ, ((m : ℚ) : ℍ[ℚ, a, b]) ∈ Λ) (E : FakeEllipticCurve Λ N S) (m : ℕ)
    (h : (((m : ℕ) : ℚ) : ℍ[ℚ, a, b]) ∈ Λ) :
    E.act ⟨(((m : ℕ) : ℚ) : ℍ[ℚ, a, b]), h⟩ = E.act ⟨((((m : ℕ) : ℤ) : ℚ) : ℍ[ℚ, a, b]), hΛℤ m⟩ := by
  exact congrArg E.act (Subtype.ext (by simp))

noncomputable def pad {r : ℕ} {𝒪 : Type} [CommRing 𝒪] {π : 𝒪} {Onr : Type} [CommRing Onr] [Algebra 𝒪 Onr]
    (hΛℤ : ∀ m : ℤ, ((m : ℚ) : ℍ[ℚ, a, b]) ∈ Λ)
    {A₀ : FakeEllipticCurve Λ N (Onr ⧸ Ideal.span {algebraMap 𝒪 Onr π})}
    {B : Type} [CommRing B] [Algebra 𝒪 B] {ψ : Onr →ₐ[𝒪] B} {E : FakeEllipticCurve Λ N B}
    (ρ : Rigidification r π A₀ ψ E) (s t : ℕ) : Rigidification r π A₀ ψ E where
  Eb := ρ.Eb
  gb := ρ.gb
  isPullback_Eb := ρ.isPullback_Eb
  Ab := ρ.Ab
  gA := ρ.gA
  isPullback_Ab := ρ.isPullback_Ab
  d := ρ.d + s + t
  φ := ρ.φ ≫ ρ.Ab.act ⟨(((r ^ s : ℕ) : ℤ) : ℚ), hΛℤ _⟩
  φ' := ρ.φ' ≫ ρ.Eb.act ⟨(((r ^ t : ℕ) : ℤ) : ℚ), hΛℤ _⟩
  φ_over := by rw [Category.assoc, ρ.Ab.act_over]; exact ρ.φ_over
  isIsogenyPair := by
    obtain ⟨hφ, hψ, hm, hm', ha, ha', hc⟩ := ρ.isIsogenyPair
    have hφs : (ρ.φ ≫ ρ.Ab.act ⟨(((r ^ s : ℕ) : ℤ) : ℚ), hΛℤ _⟩) ≫ ρ.Ab.f = ρ.Eb.f := by
      rw [Category.assoc, ρ.Ab.act_over]; exact hφ
    have hψt : (ρ.φ' ≫ ρ.Eb.act ⟨(((r ^ t : ℕ) : ℤ) : ℚ), hΛℤ _⟩) ≫ ρ.Eb.f = ρ.Ab.f := by
      rw [Category.assoc, ρ.Eb.act_over]; exact hψ
    refine ⟨hφs, hψt, ?_, ?_, ?_, ?_, ?_⟩
    · intro T u P Q
      have e : ∀ R : SchemeHomOver u ρ.Eb.f, mapPt (ρ.φ ≫ ρ.Ab.act ⟨(((r ^ s : ℕ) : ℤ) : ℚ), hΛℤ _⟩) hφs R =
          pushPt (ρ.Ab.act ⟨(((r ^ s : ℕ) : ℤ) : ℚ), hΛℤ _⟩) (ρ.Ab.act_over _) (mapPt ρ.φ hφ R) :=
        fun R => Subtype.ext (by simp only [mapPt_coe, Category.assoc])
      rw [e, e, e, hm, ρ.Ab.act_hom]
    · intro T u P Q
      have e : ∀ R : SchemeHomOver u ρ.Ab.f, mapPt (ρ.φ' ≫ ρ.Eb.act ⟨(((r ^ t : ℕ) : ℤ) : ℚ), hΛℤ _⟩) hψt R =
          pushPt (ρ.Eb.act ⟨(((r ^ t : ℕ) : ℤ) : ℚ), hΛℤ _⟩) (ρ.Eb.act_over _) (mapPt ρ.φ' hψ R) :=
        fun R => Subtype.ext (by simp only [mapPt_coe, Category.assoc])
      rw [e, e, e, hm', ρ.Eb.act_hom]
    · intro x
      rw [← Category.assoc, ha, Category.assoc, Category.assoc, act_comm_intCast hΛℤ]
    · intro x
      rw [← Category.assoc, ha', Category.assoc, Category.assoc, act_comm_intCast hΛℤ]
    · intro hd
      have hd₀ : (((r ^ ρ.d : ℕ) : ℚ) : ℍ[ℚ, a, b]) ∈ Λ := by
        have := hΛℤ (r ^ ρ.d : ℕ); push_cast at this ⊢; exact this
      obtain ⟨c, c'⟩ := hc hd₀
      rw [act_natCast_eq hΛℤ] at c c'
      rw [act_natCast_eq hΛℤ, act_natCast_eq hΛℤ]
      constructor
      · rw [Category.assoc, ← Category.assoc (ρ.Ab.act _), ha', Category.assoc, ← Category.assoc ρ.φ, c,
          act_rpow_comp, act_rpow_comp]
        congr 1; apply Subtype.ext; push_cast; ring_nf
      · rw [Category.assoc, ← Category.assoc (ρ.Eb.act _), ha, Category.assoc, ← Category.assoc ρ.φ', c',
          act_rpow_comp, act_rpow_comp]
        congr 1; apply Subtype.ext; push_cast; ring_nf
  preservesLevel := by
    intro T u P hP
    have e : mapPt (ρ.φ ≫ ρ.Ab.act ⟨(((r ^ s : ℕ) : ℤ) : ℚ), hΛℤ _⟩)
        (by rw [Category.assoc, ρ.Ab.act_over]; exact ρ.φ_over) P =
        pushPt (ρ.Ab.act ⟨(((r ^ s : ℕ) : ℤ) : ℚ), hΛℤ _⟩) (ρ.Ab.act_over _) (mapPt ρ.φ ρ.φ_over P) :=
      Subtype.ext (by simp only [mapPt_coe, Category.assoc])
    rw [e]
    exact ρ.Ab.lev_stable _ u _ (ρ.preservesLevel u P hP)

end GPShift

namespace We89C2
open CerednikDrinfeld.QM.FakeEllipticCurve

section Algebra
variable {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} {N : ℕ}
  {r : ℕ} {𝒪 : Type} [CommRing 𝒪] {π : 𝒪} {Onr : Type} [CommRing Onr] [Algebra 𝒪 Onr]
  (hΛℤ : ∀ m : ℤ, ((m : ℚ) : ℍ[ℚ, a, b]) ∈ Λ)
  {A₀ : FakeEllipticCurve Λ N (Onr ⧸ Ideal.span {algebraMap 𝒪 Onr π})}
  {B : Type} [CommRing B] [Algebra 𝒪 B] {ψ : Onr →ₐ[𝒪] B} {E E' : FakeEllipticCurve Λ N B}

@[scoped simp] theorem pad_Eb (ρ : Rigidification r π A₀ ψ E) (s t : ℕ) : (GPShift.pad hΛℤ ρ s t).Eb = ρ.Eb := rfl
@[scoped simp] theorem pad_gb (ρ : Rigidification r π A₀ ψ E) (s t : ℕ) : (GPShift.pad hΛℤ ρ s t).gb = ρ.gb := rfl
@[scoped simp] theorem pad_Ab (ρ : Rigidification r π A₀ ψ E) (s t : ℕ) : (GPShift.pad hΛℤ ρ s t).Ab = ρ.Ab := rfl
@[scoped simp] theorem pad_gA (ρ : Rigidification r π A₀ ψ E) (s t : ℕ) : (GPShift.pad hΛℤ ρ s t).gA = ρ.gA := rfl
@[scoped simp] theorem pad_d (ρ : Rigidification r π A₀ ψ E) (s t : ℕ) : (GPShift.pad hΛℤ ρ s t).d = ρ.d + s + t := rfl
theorem pad_φ (ρ : Rigidification r π A₀ ψ E) (s t : ℕ) :
    (GPShift.pad hΛℤ ρ s t).φ = ρ.φ ≫ ρ.Ab.act ⟨(((r ^ s : ℕ) : ℤ) : ℚ), hΛℤ _⟩ := rfl
theorem pad_φ' (ρ : Rigidification r π A₀ ψ E) (s t : ℕ) :
    (GPShift.pad hΛℤ ρ s t).φ' = ρ.φ' ≫ ρ.Eb.act ⟨(((r ^ t : ℕ) : ℤ) : ℚ), hΛℤ _⟩ := rfl
theorem pad_isPullback_Eb (ρ : Rigidification r π A₀ ψ E) (s t : ℕ) :
    (GPShift.pad hΛℤ ρ s t).isPullback_Eb = ρ.isPullback_Eb := rfl
theorem pad_isPullback_Ab (ρ : Rigidification r π A₀ ψ E) (s t : ℕ) :
    (GPShift.pad hΛℤ ρ s t).isPullback_Ab = ρ.isPullback_Ab := rfl

theorem corr_shift_add
    (ρ : Rigidification r π A₀ ψ E) (ρ' : Rigidification r π A₀ ψ E')
    (ib : ρ.Eb.A ⟶ ρ'.Eb.A) (uA : ρ'.Ab.A ⟶ ρ.Ab.A) (i₁ j₁ t : ℕ)
    (h : ib ≫ ρ'.φ ≫ uA ≫ ρ.Ab.act ⟨(((r ^ i₁ : ℕ) : ℤ) : ℚ), hΛℤ _⟩ = ρ.φ ≫ ρ.Ab.act ⟨(((r ^ j₁ : ℕ) : ℤ) : ℚ), hΛℤ _⟩) :
    ib ≫ ρ'.φ ≫ uA ≫ ρ.Ab.act ⟨(((r ^ (i₁ + t) : ℕ) : ℤ) : ℚ), hΛℤ _⟩ = ρ.φ ≫ ρ.Ab.act ⟨(((r ^ (j₁ + t) : ℕ) : ℤ) : ℚ), hΛℤ _⟩ := by
  have h' := congrArg (· ≫ ρ.Ab.act ⟨(((r ^ t : ℕ) : ℤ) : ℚ), hΛℤ _⟩) h
  simp only [Category.assoc] at h'
  rw [GPShift.act_rpow_comp hΛℤ ρ.Ab r i₁ t, GPShift.act_rpow_comp hΛℤ ρ.Ab r j₁ t] at h'
  exact h'

theorem pad_corr_of_shift_corr'
    (ρ : Rigidification r π A₀ ψ E) (ρ' : Rigidification r π A₀ ψ E')
    (ib : ρ.Eb.A ⟶ ρ'.Eb.A) (uA : ρ'.Ab.A ⟶ ρ.Ab.A)
    (huAact : ∀ x : ↥Λ, ρ'.Ab.act x ≫ uA = uA ≫ ρ.Ab.act x)
    (i₁ j₁ t t' : ℕ)
    (h : ib ≫ ρ'.φ ≫ uA ≫ ρ.Ab.act ⟨(((r ^ i₁ : ℕ) : ℤ) : ℚ), hΛℤ _⟩ = ρ.φ ≫ ρ.Ab.act ⟨(((r ^ j₁ : ℕ) : ℤ) : ℚ), hΛℤ _⟩) :
    ib ≫ (GPShift.pad hΛℤ ρ' i₁ t').φ ≫ uA = (GPShift.pad hΛℤ ρ j₁ t).φ := by
  show ib ≫ (ρ'.φ ≫ ρ'.Ab.act ⟨(((r ^ i₁ : ℕ) : ℤ) : ℚ), hΛℤ _⟩) ≫ uA = ρ.φ ≫ ρ.Ab.act ⟨(((r ^ j₁ : ℕ) : ℤ) : ℚ), hΛℤ _⟩
  rw [Category.assoc, huAact]
  exact h

theorem pad_corr_of_shift_corr
    (ρ : Rigidification r π A₀ ψ E) (ρ' : Rigidification r π A₀ ψ E')
    (ib : ρ.Eb.A ⟶ ρ'.Eb.A) (uA : ρ'.Ab.A ⟶ ρ.Ab.A)
    (huA : FakeEllipticCurve.IsPullbackVia (RingHom.id _) ρ.Ab ρ'.Ab uA)
    (i₁ j₁ t t' : ℕ)
    (h : ib ≫ ρ'.φ ≫ uA ≫ ρ.Ab.act ⟨(((r ^ i₁ : ℕ) : ℤ) : ℚ), hΛℤ _⟩ = ρ.φ ≫ ρ.Ab.act ⟨(((r ^ j₁ : ℕ) : ℤ) : ℚ), hΛℤ _⟩) :
    ib ≫ (GPShift.pad hΛℤ ρ' i₁ t').φ ≫ uA = (GPShift.pad hΛℤ ρ j₁ t).φ := by
  obtain ⟨-, -, hact, -⟩ := huA
  exact pad_corr_of_shift_corr' hΛℤ ρ ρ' ib uA hact i₁ j₁ t t' h

theorem shift_corr_of_pad_corr'
    (ρ : Rigidification r π A₀ ψ E) (ρ' : Rigidification r π A₀ ψ E')
    (ib : ρ.Eb.A ⟶ ρ'.Eb.A) (uA : ρ'.Ab.A ⟶ ρ.Ab.A)
    (huAact : ∀ x : ↥Λ, ρ'.Ab.act x ≫ uA = uA ≫ ρ.Ab.act x)
    (s t s' t' : ℕ)
    (h : ib ≫ (GPShift.pad hΛℤ ρ' s' t').φ ≫ uA = (GPShift.pad hΛℤ ρ s t).φ) :
    ib ≫ ρ'.φ ≫ uA ≫ ρ.Ab.act ⟨(((r ^ s' : ℕ) : ℤ) : ℚ), hΛℤ _⟩ = ρ.φ ≫ ρ.Ab.act ⟨(((r ^ s : ℕ) : ℤ) : ℚ), hΛℤ _⟩ := by
  have h' : ib ≫ (ρ'.φ ≫ ρ'.Ab.act ⟨(((r ^ s' : ℕ) : ℤ) : ℚ), hΛℤ _⟩) ≫ uA = ρ.φ ≫ ρ.Ab.act ⟨(((r ^ s : ℕ) : ℤ) : ℚ), hΛℤ _⟩ := h
  rw [Category.assoc, huAact] at h'
  exact h'

theorem shift_corr_of_pad_corr
    (ρ : Rigidification r π A₀ ψ E) (ρ' : Rigidification r π A₀ ψ E')
    (ib : ρ.Eb.A ⟶ ρ'.Eb.A) (uA : ρ'.Ab.A ⟶ ρ.Ab.A)
    (huA : FakeEllipticCurve.IsPullbackVia (RingHom.id _) ρ.Ab ρ'.Ab uA)
    (s t s' t' : ℕ)
    (h : ib ≫ (GPShift.pad hΛℤ ρ' s' t').φ ≫ uA = (GPShift.pad hΛℤ ρ s t).φ) :
    ib ≫ ρ'.φ ≫ uA ≫ ρ.Ab.act ⟨(((r ^ s' : ℕ) : ℤ) : ℚ), hΛℤ _⟩ = ρ.φ ≫ ρ.Ab.act ⟨(((r ^ s : ℕ) : ℤ) : ℚ), hΛℤ _⟩ := by
  obtain ⟨-, -, hact, -⟩ := huA
  exact shift_corr_of_pad_corr' hΛℤ ρ ρ' ib uA hact s t s' t' h

theorem pad_d_comm (ρ : Rigidification r π A₀ ψ E) (ρ' : Rigidification r π A₀ ψ E') (i₁ j₁ : ℕ) :
    (GPShift.pad hΛℤ ρ' i₁ (ρ.d + j₁)).d = ρ.d + j₁ + (ρ'.d + i₁) := by
  show ρ'.d + i₁ + (ρ.d + j₁) = ρ.d + j₁ + (ρ'.d + i₁)
  omega

theorem pad_isPullbackVia {B' : Type} [CommRing B'] [Algebra 𝒪 B'] (f : B →ₐ[𝒪] B')
    {EL : FakeEllipticCurve Λ N B'} (g : EL.A ⟶ E.A) (hg : FakeEllipticCurve.IsPullbackVia (f : B →+* B') E EL g)
    (ρ : Rigidification r π A₀ ψ E) (ρL : Rigidification r π A₀ (f.comp ψ) EL)
    (h : Rigidification.IsPullbackVia f g hg ρ ρL) (s t : ℕ) :
    Rigidification.IsPullbackVia f g hg (GPShift.pad hΛℤ ρ s t) (GPShift.pad hΛℤ ρL s t) := by
  obtain ⟨ub, uA, hub, hubg, huA, huAg, hd, hφ⟩ := h
  refine ⟨ub, uA, hub, hubg, huA, huAg, ?_, ?_⟩
  · show ρL.d + s + t = ρ.d + s + t
    rw [hd]
  · obtain ⟨-, -, hact, -⟩ := huA
    show ub ≫ (ρ.φ ≫ ρ.Ab.act ⟨(((r ^ s : ℕ) : ℤ) : ℚ), hΛℤ _⟩) = (ρL.φ ≫ ρL.Ab.act ⟨(((r ^ s : ℕ) : ℤ) : ℚ), hΛℤ _⟩) ≫ uA
    rw [Category.assoc, hact, ← Category.assoc, ← Category.assoc, hφ]

end Algebra

section Model

variable {r N : ℕ} (𝒪 : Type) [CommRing 𝒪] (π : 𝒪) (Onr : Type) [CommRing Onr] [Algebra 𝒪 Onr]
  {a b : ℚ} (Λ : Submodule ℤ ℍ[ℚ, a, b]) (hΛℤ : ∀ m : ℤ, ((m : ℚ) : ℍ[ℚ, a, b]) ∈ Λ)
  (A₀ : FakeEllipticCurve Λ N (Onr ⧸ Ideal.span {algebraMap 𝒪 Onr π})) (n : ℕ)
  (C : Type) [CommRing C] [Algebra 𝒪 C] (ψ : Onr →ₐ[𝒪] C)
  {MC : Scheme.{0}} (g : MC ⟶ Spec (CommRingCat.of C)) (X : ℕ → Scheme.{0}) (ξ : ∀ d, X d ⟶ MC)
  (tM : ∀ (T : Type) [CommRing T] [Algebra C T],
    FakeEllipticCurve.WithFullLevel Λ N n T → SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap C T))) g)
  (xOf : ∀ (T : Type) [CommRing T] [Algebra C T] [Algebra 𝒪 T] [IsScalarTower 𝒪 C T]
    (ψT : Onr →ₐ[𝒪] T) (_ : ψT = (IsScalarTower.toAlgHom 𝒪 C T).comp ψ)
    (u : FakeEllipticCurve.WithFullLevel Λ N n T) (ρ : FakeEllipticCurve.Rigidification r π A₀ ψT u.1),
    { x : Spec (CommRingCat.of (T ⧸ Ideal.span {algebraMap C T (algebraMap 𝒪 C π)})) ⟶ X ρ.d //
      x ≫ ξ ρ.d = Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (Ideal.span {algebraMap C T (algebraMap 𝒪 C π)}))) ≫ (tM T u).1 })

  (hx4 : (∀ (d : ℕ) (T : Type) [CommRing T] [Algebra C T] [Algebra 𝒪 T] [IsScalarTower 𝒪 C T]
              (ψT : Onr →ₐ[𝒪] T) (hψT : ψT = (IsScalarTower.toAlgHom 𝒪 C T).comp ψ)
              (h0 : algebraMap C T (algebraMap 𝒪 C π) = 0)
              (u u' : FakeEllipticCurve.WithFullLevel Λ N n T)
              (ρ : FakeEllipticCurve.Rigidification r π A₀ ψT u.1) (ρ' : FakeEllipticCurve.Rigidification r π A₀ ψT u'.1)
              (hd : ρ.d = d) (hd' : ρ'.d = d),
              ((RigidifiedPairClass.ptX 𝒪 π Onr Λ A₀ n C ψ g X ξ tM xOf) d T ψT hψT u ρ hd h0 = (RigidifiedPairClass.ptX 𝒪 π Onr Λ A₀ n C ψ g X ξ tM xOf) d T ψT hψT u' ρ' hd' h0 ↔
                ∃ (i : u.1.A ≅ u'.1.A) (hi : i.hom ≫ u'.1.f = u.1.f), FakeEllipticCurve.WithFullLevel.IsoVia u u' i hi ∧
                  ∃ (ib : ρ.Eb.A ⟶ ρ'.Eb.A) (_ : ib ≫ ρ'.gb = ρ.gb ≫ i.hom) (_ : ib ≫ ρ'.Eb.f = ρ.Eb.f)
                    (uA : ρ'.Ab.A ⟶ ρ.Ab.A) (_ : FakeEllipticCurve.IsPullbackVia (RingHom.id _) ρ.Ab ρ'.Ab uA) (_ : uA ≫ ρ.gA = ρ'.gA),
                    ib ≫ ρ'.φ ≫ uA = ρ.φ)))
  (T : Type) [CommRing T] [Algebra C T] [Algebra 𝒪 T] [IsScalarTower 𝒪 C T]
  (ψT : Onr →ₐ[𝒪] T) (hψT : ψT = (IsScalarTower.toAlgHom 𝒪 C T).comp ψ)
  (h0 : algebraMap C T (algebraMap 𝒪 C π) = 0)
  (u u' : FakeEllipticCurve.WithFullLevel Λ N n T)
  (ρ : FakeEllipticCurve.Rigidification r π A₀ ψT u.1) (ρ' : FakeEllipticCurve.Rigidification r π A₀ ψT u'.1)

include hx4

theorem ptX_pad_eq_of_corr
    (i : u.1.A ≅ u'.1.A) (hi : i.hom ≫ u'.1.f = u.1.f) (hiso : FakeEllipticCurve.WithFullLevel.IsoVia u u' i hi)
    (ib : ρ.Eb.A ⟶ ρ'.Eb.A) (hib : ib ≫ ρ'.gb = ρ.gb ≫ i.hom) (hibf : ib ≫ ρ'.Eb.f = ρ.Eb.f)
    (uA : ρ'.Ab.A ⟶ ρ.Ab.A) (huA : FakeEllipticCurve.IsPullbackVia (RingHom.id _) ρ.Ab ρ'.Ab uA) (huAg : uA ≫ ρ.gA = ρ'.gA)
    (i₁ j₁ : ℕ)
    (h : ib ≫ ρ'.φ ≫ uA ≫ ρ.Ab.act ⟨(((r ^ i₁ : ℕ) : ℤ) : ℚ), hΛℤ _⟩ = ρ.φ ≫ ρ.Ab.act ⟨(((r ^ j₁ : ℕ) : ℤ) : ℚ), hΛℤ _⟩)
    (t t' e : ℕ) (hd : (GPShift.pad hΛℤ ρ j₁ t).d = e) (hd' : (GPShift.pad hΛℤ ρ' i₁ t').d = e) :
    (RigidifiedPairClass.ptX 𝒪 π Onr Λ A₀ n C ψ g X ξ tM xOf) e T ψT hψT u (GPShift.pad hΛℤ ρ j₁ t) hd h0 =
      (RigidifiedPairClass.ptX 𝒪 π Onr Λ A₀ n C ψ g X ξ tM xOf) e T ψT hψT u' (GPShift.pad hΛℤ ρ' i₁ t') hd' h0 :=
  (hx4 e T ψT hψT h0 u u' (GPShift.pad hΛℤ ρ j₁ t) (GPShift.pad hΛℤ ρ' i₁ t') hd hd').mpr
    ⟨i, hi, hiso, ib, hib, hibf, uA, huA, huAg, pad_corr_of_shift_corr hΛℤ ρ ρ' ib uA huA i₁ j₁ t t' h⟩

theorem exists_ptX_pad_eq_of_corr
    (hc : ∃ (i : u.1.A ≅ u'.1.A) (hi : i.hom ≫ u'.1.f = u.1.f), FakeEllipticCurve.WithFullLevel.IsoVia u u' i hi ∧
      ∃ (ib : ρ.Eb.A ⟶ ρ'.Eb.A) (_ : ib ≫ ρ'.gb = ρ.gb ≫ i.hom) (_ : ib ≫ ρ'.Eb.f = ρ.Eb.f)
        (uA : ρ'.Ab.A ⟶ ρ.Ab.A) (_ : FakeEllipticCurve.IsPullbackVia (RingHom.id _) ρ.Ab ρ'.Ab uA) (_ : uA ≫ ρ.gA = ρ'.gA)
        (i₁ j₁ : ℕ),
        ib ≫ ρ'.φ ≫ uA ≫ ρ.Ab.act ⟨(((r ^ i₁ : ℕ) : ℤ) : ℚ), hΛℤ _⟩ = ρ.φ ≫ ρ.Ab.act ⟨(((r ^ j₁ : ℕ) : ℤ) : ℚ), hΛℤ _⟩) :
    ∃ (i₁ j₁ : ℕ) (hd : (GPShift.pad hΛℤ ρ j₁ (ρ'.d + i₁)).d = ρ.d + j₁ + (ρ'.d + i₁))
      (hd' : (GPShift.pad hΛℤ ρ' i₁ (ρ.d + j₁)).d = ρ.d + j₁ + (ρ'.d + i₁)),
      (RigidifiedPairClass.ptX 𝒪 π Onr Λ A₀ n C ψ g X ξ tM xOf) (ρ.d + j₁ + (ρ'.d + i₁)) T ψT hψT u
          (GPShift.pad hΛℤ ρ j₁ (ρ'.d + i₁)) hd h0 =
        (RigidifiedPairClass.ptX 𝒪 π Onr Λ A₀ n C ψ g X ξ tM xOf) (ρ.d + j₁ + (ρ'.d + i₁)) T ψT hψT u'
          (GPShift.pad hΛℤ ρ' i₁ (ρ.d + j₁)) hd' h0 := by
  obtain ⟨i, hi, hiso, ib, hib, hibf, uA, huA, huAg, i₁, j₁, h⟩ := hc
  exact ⟨i₁, j₁, rfl, pad_d_comm hΛℤ ρ ρ' i₁ j₁,
    ptX_pad_eq_of_corr 𝒪 π Onr Λ hΛℤ A₀ n C ψ g X ξ tM xOf hx4 T ψT hψT h0 u u' ρ ρ' i hi hiso ib hib hibf uA huA huAg
      i₁ j₁ h _ _ _ rfl (pad_d_comm hΛℤ ρ ρ' i₁ j₁)⟩

theorem corr_of_ptX_pad_eq
    (s t s' t' e : ℕ) (hd : (GPShift.pad hΛℤ ρ s t).d = e) (hd' : (GPShift.pad hΛℤ ρ' s' t').d = e)
    (h : (RigidifiedPairClass.ptX 𝒪 π Onr Λ A₀ n C ψ g X ξ tM xOf) e T ψT hψT u (GPShift.pad hΛℤ ρ s t) hd h0 =
      (RigidifiedPairClass.ptX 𝒪 π Onr Λ A₀ n C ψ g X ξ tM xOf) e T ψT hψT u' (GPShift.pad hΛℤ ρ' s' t') hd' h0) :
    ∃ (i : u.1.A ≅ u'.1.A) (hi : i.hom ≫ u'.1.f = u.1.f), FakeEllipticCurve.WithFullLevel.IsoVia u u' i hi ∧
      ∃ (ib : ρ.Eb.A ⟶ ρ'.Eb.A) (_ : ib ≫ ρ'.gb = ρ.gb ≫ i.hom) (_ : ib ≫ ρ'.Eb.f = ρ.Eb.f)
        (uA : ρ'.Ab.A ⟶ ρ.Ab.A) (_ : FakeEllipticCurve.IsPullbackVia (RingHom.id _) ρ.Ab ρ'.Ab uA) (_ : uA ≫ ρ.gA = ρ'.gA)
        (i₁ j₁ : ℕ),
        ib ≫ ρ'.φ ≫ uA ≫ ρ.Ab.act ⟨(((r ^ i₁ : ℕ) : ℤ) : ℚ), hΛℤ _⟩ = ρ.φ ≫ ρ.Ab.act ⟨(((r ^ j₁ : ℕ) : ℤ) : ℚ), hΛℤ _⟩ := by
  obtain ⟨i, hi, hiso, ib, hib, hibf, uA, huA, huAg, hc⟩ :=
    (hx4 e T ψT hψT h0 u u' (GPShift.pad hΛℤ ρ s t) (GPShift.pad hΛℤ ρ' s' t') hd hd').mp h
  exact ⟨i, hi, hiso, ib, hib, hibf, uA, huA, huAg, s', s, shift_corr_of_pad_corr hΛℤ ρ ρ' ib uA huA s t s' t' hc⟩

end Model

end We89C2
p2m_reactivate "P2MW.S_CerednikDrinfeld_QM_RigidifiedPairClass_exists_isoVia_corr_of_ptR_eq_of_forall_isIdempotentElem.We89C2"

namespace R3IBlocks

theorem add_eq_add_of_mul_pow_eq {R P P' a b a' b' : ℕ} (hR : 2 ≤ R) (hP : 0 < P) (hP' : 0 < P')
    (h₁ : P' * R ^ a = P * R ^ b) (h₂ : P' * R ^ a' = P * R ^ b') : a + b' = a' + b := by
  have key : P * P' * R ^ (a + b') = P * P' * R ^ (a' + b) := by
    calc P * P' * R ^ (a + b') = (P' * R ^ a) * (P * R ^ b') := by ring
      _ = (P * R ^ b) * (P' * R ^ a') := by rw [h₁, ← h₂]
      _ = P * P' * R ^ (a' + b) := by ring
  exact Nat.pow_right_injective hR (Nat.eq_of_mul_eq_mul_left (Nat.mul_pos hP hP') key)

theorem exists_uniform_shifts {ι : Type} [Fintype ι] (a b : ι → ℕ) (h : ∀ k l, a k + b l = a l + b k) :
    ∃ A B : ℕ, ∀ k, ∃ m : ℕ, a k + m = A ∧ b k + m = B := by
  classical
  rcases isEmpty_or_nonempty ι with hι | ⟨⟨k₀⟩⟩
  · exact ⟨0, 0, fun k => (IsEmpty.false k).elim⟩
  · refine ⟨Finset.univ.sup a, b k₀ + (Finset.univ.sup a - a k₀), fun k => ⟨Finset.univ.sup a - a k, ?_, ?_⟩⟩
    · have := Finset.le_sup (f := a) (Finset.mem_univ k); omega
    · have hk := Finset.le_sup (f := a) (Finset.mem_univ k)
      have hk₀ := Finset.le_sup (f := a) (Finset.mem_univ k₀)
      have := h k k₀
      omega

end R3IBlocks
p2m_reactivate "P2MW.S_CerednikDrinfeld_QM_RigidifiedPairClass_exists_isoVia_corr_of_ptR_eq_of_forall_isIdempotentElem.We89C2"

namespace We89Finish

theorem isUnit_natCast_of_not_dvd' {r N : ℕ} [Fact r.Prime] (hrN : ¬ r ∣ N)
    {𝒪 : Type} [CommRing 𝒪] {π : 𝒪} (hunr : Ideal.span {((r : ℕ) : 𝒪)} = Ideal.span {π})
    {L : Type} [CommRing L] [Algebra 𝒪 L] (hπ : algebraMap 𝒪 L π = 0) :
    IsUnit ((N : ℕ) : L) := by
  have hr : ((r : ℕ) : 𝒪) ∈ Ideal.span {π} := hunr ▸ Ideal.mem_span_singleton_self _
  obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.mp hr
  have hrL : ((r : ℕ) : L) = 0 := by
    rw [← map_natCast (algebraMap 𝒪 L), ← hc, map_mul, hπ, mul_zero]
  have hcop : IsCoprime ((r : ℕ) : ℤ) ((N : ℕ) : ℤ) :=
    Nat.isCoprime_iff_coprime.mpr (((Fact.out : r.Prime).coprime_iff_not_dvd).mpr hrN)
  have h2 := hcop.map (Int.castRingHom L)
  simp only [eq_intCast, Int.cast_natCast, hrL] at h2
  exact isCoprime_zero_left.mp h2

theorem corr_refl_of_ptX_pad_eq
    {r N : ℕ} [Fact r.Prime] [NeZero N] (hrN : ¬ r ∣ N) {rbar : ℕ} [Fact rbar.Prime] (hrr : rbar ≠ r)

    (𝒪 : Type) [CommRing 𝒪] (π : 𝒪) (hunr : Ideal.span {((r : ℕ) : 𝒪)} = Ideal.span {π}) (Onr : Type) [CommRing Onr] [Algebra 𝒪 Onr]
    {a b : ℚ} (hBq : IsIndefiniteRamifiedExactlyAt a b r rbar)
    (Λ : Submodule ℤ ℍ[ℚ, a, b]) (hΛ : IsMaximalOrder Λ) (hΛℤ : ∀ m : ℤ, ((m : ℚ) : ℍ[ℚ, a, b]) ∈ Λ)

    (coord : ↥Λ → Zp2 r × Zp2 r) (hcoord : IsOrderCoord Λ r coord)
    (A₀ : FakeEllipticCurve Λ N (Onr ⧸ Ideal.span {algebraMap 𝒪 Onr π}))
    (n : ℕ) (hn : 3 ≤ n) (hrn : ¬ r ∣ n) (M : Scheme.{0}) (fM : M ⟶ Spec (CommRingCat.of 𝒪))
    (C : Type) [CommRing C] [Algebra 𝒪 C] (ψ : Onr →ₐ[𝒪] C)
    (X : ℕ → Scheme.{0}) (ξ : ∀ d, X d ⟶ Limits.pullback fM (Spec.map (CommRingCat.ofHom (algebraMap 𝒪 C))))
    (tM : ∀ (T : Type) [CommRing T] [Algebra C T],
      FakeEllipticCurve.WithFullLevel Λ N n T → SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap C T))) (Limits.pullback.snd fM (Spec.map (CommRingCat.ofHom (algebraMap 𝒪 C)))))
    (xOf : ∀ (T : Type) [CommRing T] [Algebra C T] [Algebra 𝒪 T] [IsScalarTower 𝒪 C T]
      (ψT : Onr →ₐ[𝒪] T) (_ : ψT = (IsScalarTower.toAlgHom 𝒪 C T).comp ψ)
      (u : FakeEllipticCurve.WithFullLevel Λ N n T) (ρ : FakeEllipticCurve.Rigidification r π A₀ ψT u.1),
      { x : Spec (CommRingCat.of (T ⧸ Ideal.span {algebraMap C T (algebraMap 𝒪 C π)})) ⟶ X ρ.d //
        x ≫ ξ ρ.d = Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (Ideal.span {algebraMap C T (algebraMap 𝒪 C π)}))) ≫ (tM T u).1 })
    (hx4 : (∀ (d : ℕ) (T : Type) [CommRing T] [Algebra C T] [Algebra 𝒪 T] [IsScalarTower 𝒪 C T]
                (ψT : Onr →ₐ[𝒪] T) (hψT : ψT = (IsScalarTower.toAlgHom 𝒪 C T).comp ψ)
                (h0 : algebraMap C T (algebraMap 𝒪 C π) = 0)
                (u u' : FakeEllipticCurve.WithFullLevel Λ N n T)
                (ρ : FakeEllipticCurve.Rigidification r π A₀ ψT u.1) (ρ' : FakeEllipticCurve.Rigidification r π A₀ ψT u'.1)
                (hd : ρ.d = d) (hd' : ρ'.d = d),
                ((RigidifiedPairClass.ptX 𝒪 π Onr Λ A₀ n C ψ (Limits.pullback.snd fM (Spec.map (CommRingCat.ofHom (algebraMap 𝒪 C)))) X ξ tM xOf) d T ψT hψT u ρ hd h0 = (RigidifiedPairClass.ptX 𝒪 π Onr Λ A₀ n C ψ (Limits.pullback.snd fM (Spec.map (CommRingCat.ofHom (algebraMap 𝒪 C)))) X ξ tM xOf) d T ψT hψT u' ρ' hd' h0 ↔
                  ∃ (i : u.1.A ≅ u'.1.A) (hi : i.hom ≫ u'.1.f = u.1.f), FakeEllipticCurve.WithFullLevel.IsoVia u u' i hi ∧
                    ∃ (ib : ρ.Eb.A ⟶ ρ'.Eb.A) (_ : ib ≫ ρ'.gb = ρ.gb ≫ i.hom) (_ : ib ≫ ρ'.Eb.f = ρ.Eb.f)
                      (uA : ρ'.Ab.A ⟶ ρ.Ab.A) (_ : FakeEllipticCurve.IsPullbackVia (RingHom.id _) ρ.Ab ρ'.Ab uA) (_ : uA ≫ ρ.gA = ρ'.gA),
                      ib ≫ ρ'.φ ≫ uA = ρ.φ)))
    (T : Type) [CommRing T] [Algebra C T] [Algebra 𝒪 T] [IsScalarTower 𝒪 C T]
    (ψT : Onr →ₐ[𝒪] T) (hψT : ψT = (IsScalarTower.toAlgHom 𝒪 C T).comp ψ)
    (h0 : algebraMap C T (algebraMap 𝒪 C π) = 0)
    (u : FakeEllipticCurve.WithFullLevel Λ N n T)
    (ρ ρ' : FakeEllipticCurve.Rigidification r π A₀ ψT u.1)
    (A B D : ℕ) (t t' : ℕ) (hd : (GPShift.pad hΛℤ ρ B t).d = D) (hd' : (GPShift.pad hΛℤ ρ' A t').d = D)
    (h : (RigidifiedPairClass.ptX 𝒪 π Onr Λ A₀ n C ψ (Limits.pullback.snd fM (Spec.map (CommRingCat.ofHom (algebraMap 𝒪 C)))) X ξ tM xOf) D T ψT hψT u (GPShift.pad hΛℤ ρ B t) hd h0 =
      (RigidifiedPairClass.ptX 𝒪 π Onr Λ A₀ n C ψ (Limits.pullback.snd fM (Spec.map (CommRingCat.ofHom (algebraMap 𝒪 C)))) X ξ tM xOf) D T ψT hψT u (GPShift.pad hΛℤ ρ' A t') hd' h0) :
    ∃ (ib : ρ.Eb.A ⟶ ρ'.Eb.A) (_ : ib ≫ ρ'.gb = ρ.gb) (_ : ib ≫ ρ'.Eb.f = ρ.Eb.f)
      (uA : ρ'.Ab.A ⟶ ρ.Ab.A) (_ : FakeEllipticCurve.IsPullbackVia (RingHom.id _) ρ.Ab ρ'.Ab uA) (_ : uA ≫ ρ.gA = ρ'.gA),
      ib ≫ ρ'.φ ≫ uA ≫ ρ.Ab.act ⟨(((r ^ A : ℕ) : ℤ) : ℚ), hΛℤ _⟩ = ρ.φ ≫ ρ.Ab.act ⟨(((r ^ B : ℕ) : ℤ) : ℚ), hΛℤ _⟩ := by

  obtain ⟨i, hi, hiso, ib, hib, hibf, uA, huA, huAg, hc⟩ :=
    (hx4 D T ψT hψT h0 u u (GPShift.pad hΛℤ ρ B t) (GPShift.pad hΛℤ ρ' A t') hd hd').mp h

  obtain ⟨hmul, hact, -, hP⟩ := hiso
  have hπT : algebraMap 𝒪 T π = 0 := by
    rw [IsScalarTower.algebraMap_apply 𝒪 C T π]; exact h0
  have hnT : IsUnit ((n : ℕ) : T) := isUnit_natCast_of_not_dvd' hrn hunr hπT
  have hrig : i = Iso.refl u.1.A :=
    CerednikDrinfeld.QM.FakeEllipticCurve.WithFullLevel.eq_refl_of_mapPt_eq_of_three_le hrr hBq Λ hΛ hn hnT u i hi
      hmul hact hP
  rw [hrig, Iso.refl_hom, Category.comp_id] at hib

  exact ⟨ib, hib, hibf, uA, huA, huAg, We89C2.shift_corr_of_pad_corr hΛℤ ρ ρ' ib uA huA B t A t' hc⟩

end We89Finish
p2m_reactivate "P2MW.S_CerednikDrinfeld_QM_RigidifiedPairClass_exists_isoVia_corr_of_ptR_eq_of_forall_isIdempotentElem.We89C2"

namespace We88Glue

theorem pt_ext_of_cover
    (𝒪 : Type) [CommRing 𝒪] (π : 𝒪) (C : Type) [CommRing C] [Algebra 𝒪 C]
    {MC : Scheme.{0}} (g : MC ⟶ Spec (CommRingCat.of C)) (X : ℕ → Scheme.{0}) (ξ : ∀ d, X d ⟶ MC)
    (T : Type) [CommRing T] [Algebra C T] (h0 : algebraMap C T (algebraMap 𝒪 C π) = 0) (D : ℕ)
    (y y' : SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap C T))) (ξ D ≫ g))
    (m : ℕ) (f : Fin m → (T ⧸ Ideal.span {algebraMap C T (algebraMap 𝒪 C π)}))
    (hf : Ideal.span (Set.range f) = ⊤)
    (L : Fin m → Type) [∀ k, CommRing (L k)] [∀ k, Algebra (T ⧸ Ideal.span {algebraMap C T (algebraMap 𝒪 C π)}) (L k)]
    [∀ k, IsLocalization.Away (f k) (L k)]
    (h : ∀ k,
      Spec.map (CommRingCat.ofHom (algebraMap (T ⧸ Ideal.span {algebraMap C T (algebraMap 𝒪 C π)}) (L k))) ≫
          Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (Ideal.span {algebraMap C T (algebraMap 𝒪 C π)}))) ≫ y.1 =
        Spec.map (CommRingCat.ofHom (algebraMap (T ⧸ Ideal.span {algebraMap C T (algebraMap 𝒪 C π)}) (L k))) ≫
          Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (Ideal.span {algebraMap C T (algebraMap 𝒪 C π)}))) ≫ y'.1) :
    y = y' := by
  classical

  have H := AlgebraicGeometry.Scheme.section_ext_and_exists_section_of_isLocalizationAway_of_span_eq_top
    (S := T ⧸ Ideal.span {algebraMap C T (algebraMap 𝒪 C π)})
    (A := Limits.pullback (ξ D ≫ g)
      (Spec.map (CommRingCat.ofHom (algebraMap C (T ⧸ Ideal.span {algebraMap C T (algebraMap 𝒪 C π)})))))
    (Limits.pullback.snd (ξ D ≫ g)
      (Spec.map (CommRingCat.ofHom (algebraMap C (T ⧸ Ideal.span {algebraMap C T (algebraMap 𝒪 C π)})))))
    m f hf L (fun i j => Localization.Away (f i * f j))
    (fun i j => IsLocalization.Away.awayToAwayRight (S := L i) (f i) (f j) (P := Localization.Away (f i * f j)))
    (fun i j => IsLocalization.Away.awayToAwayLeft (S := L j) (f j) (f i) (P := Localization.Away (f i * f j)))
    (fun i j => RingHom.ext fun a => IsLocalization.Away.awayToAwayRight_eq (S := L i) (f i) (f j) (P := Localization.Away (f i * f j)) a)
    (fun i j => RingHom.ext fun a => IsLocalization.Away.awayToAwayLeft_eq (S := L j) (f j) (f i) (P := Localization.Away (f i * f j)) a)
  obtain ⟨huniq, -⟩ := H
  have w : ∀ (z : SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap C T))) (ξ D ≫ g)),
      (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (Ideal.span {algebraMap C T (algebraMap 𝒪 C π)}))) ≫ z.1) ≫ (ξ D ≫ g) =
        𝟙 _ ≫ Spec.map (CommRingCat.ofHom (algebraMap C (T ⧸ Ideal.span {algebraMap C T (algebraMap 𝒪 C π)}))) := fun z => by
    rw [Category.assoc, z.2, Category.id_comp, ← Ideal.Quotient.mk_comp_algebraMap, CommRingCat.ofHom_comp, Spec.map_comp]
  have key := huniq (Limits.pullback.lift _ _ (w y)) (Limits.pullback.lift _ _ (w y'))
    (Limits.pullback.lift_snd _ _ _) (Limits.pullback.lift_snd _ _ _) (by
      intro i
      apply Limits.pullback.hom_ext
      · rw [Category.assoc, Category.assoc, Limits.pullback.lift_fst, Limits.pullback.lift_fst]; exact h i
      · rw [Category.assoc, Category.assoc, Limits.pullback.lift_snd, Limits.pullback.lift_snd])
  have keyA : Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (Ideal.span {algebraMap C T (algebraMap 𝒪 C π)}))) ≫ y.1 =
      Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (Ideal.span {algebraMap C T (algebraMap 𝒪 C π)}))) ≫ y'.1 := by
    rw [← Limits.pullback.lift_fst _ _ (w y), key, Limits.pullback.lift_fst]

  apply Subtype.ext
  have hsec : Spec.map (CommRingCat.ofHom
        (((Ideal.quotEquivOfEq (Ideal.span_singleton_eq_bot.mpr h0)).trans (RingEquiv.quotientBot T)).toRingHom)) ≫
      Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (Ideal.span {algebraMap C T (algebraMap 𝒪 C π)}))) = 𝟙 _ := by
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, RigidifiedPairClass.quotEquiv_comp_mk (algebraMap 𝒪 C π) T h0,
      CommRingCat.ofHom_id]
    erw [Spec.map_id]
  rw [← Category.id_comp y.1, ← Category.id_comp y'.1, ← hsec, Category.assoc, Category.assoc, keyA]

end We88Glue
p2m_reactivate "P2MW.S_CerednikDrinfeld_QM_RigidifiedPairClass_exists_isoVia_corr_of_ptR_eq_of_forall_isIdempotentElem.We89C2"

namespace We89Sub

section Model
variable {r N : ℕ} (𝒪 : Type) [CommRing 𝒪] (π : 𝒪) (Onr : Type) [CommRing Onr] [Algebra 𝒪 Onr]
  {a b : ℚ} (Λ : Submodule ℤ ℍ[ℚ, a, b])
  (A₀ : FakeEllipticCurve Λ N (Onr ⧸ Ideal.span {algebraMap 𝒪 Onr π})) (n : ℕ)
  (C : Type) [CommRing C] [Algebra 𝒪 C] (ψ : Onr →ₐ[𝒪] C)
  {MC : Scheme.{0}} (g : MC ⟶ Spec (CommRingCat.of C)) (X : ℕ → Scheme.{0}) (ξ : ∀ d, X d ⟶ MC)
  (tM : ∀ (T : Type) [CommRing T] [Algebra C T],
    FakeEllipticCurve.WithFullLevel Λ N n T → SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap C T))) g)
  (xOf : ∀ (T : Type) [CommRing T] [Algebra C T] [Algebra 𝒪 T] [IsScalarTower 𝒪 C T]
    (ψT : Onr →ₐ[𝒪] T) (_ : ψT = (IsScalarTower.toAlgHom 𝒪 C T).comp ψ)
    (u : FakeEllipticCurve.WithFullLevel Λ N n T) (ρ : FakeEllipticCurve.Rigidification r π A₀ ψT u.1),
    { x : Spec (CommRingCat.of (T ⧸ Ideal.span {algebraMap C T (algebraMap 𝒪 C π)})) ⟶ X ρ.d //
      x ≫ ξ ρ.d = Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (Ideal.span {algebraMap C T (algebraMap 𝒪 C π)}))) ≫ (tM T u).1 })

theorem isEmpty_spec_of_subsingleton (L : Type) [CommRing L] [Subsingleton L] : IsEmpty ↑(Spec (CommRingCat.of L)) :=
  inferInstanceAs (IsEmpty (PrimeSpectrum L))

theorem ptX_eq_of_subsingleton
    (d : ℕ) (L : Type) [CommRing L] [Algebra C L] [Algebra 𝒪 L] [IsScalarTower 𝒪 C L] [Subsingleton L]
    (ψL : Onr →ₐ[𝒪] L) (hψL : ψL = (IsScalarTower.toAlgHom 𝒪 C L).comp ψ)
    (h0 : algebraMap C L (algebraMap 𝒪 C π) = 0)
    (u u' : FakeEllipticCurve.WithFullLevel Λ N n L)
    (ρ : FakeEllipticCurve.Rigidification r π A₀ ψL u.1) (ρ' : FakeEllipticCurve.Rigidification r π A₀ ψL u'.1)
    (hd : ρ.d = d) (hd' : ρ'.d = d) :
    (RigidifiedPairClass.ptX 𝒪 π Onr Λ A₀ n C ψ g X ξ tM xOf) d L ψL hψL u ρ hd h0 =
      (RigidifiedPairClass.ptX 𝒪 π Onr Λ A₀ n C ψ g X ξ tM xOf) d L ψL hψL u' ρ' hd' h0 := by
  haveI : IsEmpty ↑(Spec (CommRingCat.of L)) := isEmpty_spec_of_subsingleton L
  apply Subtype.ext
  exact isInitialOfIsEmpty.hom_ext _ _

theorem ptX_val_eq_of_subsingleton
    (d : ℕ) (L : Type) [CommRing L] [Algebra C L] [Algebra 𝒪 L] [IsScalarTower 𝒪 C L] [Subsingleton L]
    (ψL : Onr →ₐ[𝒪] L) (hψL : ψL = (IsScalarTower.toAlgHom 𝒪 C L).comp ψ)
    (h0 : algebraMap C L (algebraMap 𝒪 C π) = 0)
    (u u' : FakeEllipticCurve.WithFullLevel Λ N n L)
    (ρ : FakeEllipticCurve.Rigidification r π A₀ ψL u.1) (ρ' : FakeEllipticCurve.Rigidification r π A₀ ψL u'.1)
    (hd : ρ.d = d) (hd' : ρ'.d = d) :
    ((RigidifiedPairClass.ptX 𝒪 π Onr Λ A₀ n C ψ g X ξ tM xOf) d L ψL hψL u ρ hd h0).1 =
      ((RigidifiedPairClass.ptX 𝒪 π Onr Λ A₀ n C ψ g X ξ tM xOf) d L ψL hψL u' ρ' hd' h0).1 := by
  haveI : IsEmpty ↑(Spec (CommRingCat.of L)) := isEmpty_spec_of_subsingleton L
  exact isInitialOfIsEmpty.hom_ext _ _

theorem hom_eq_of_subsingleton (L : Type) [CommRing L] [Subsingleton L] {Y : Scheme.{0}}
    (f₁ f₂ : Spec (CommRingCat.of L) ⟶ Y) : f₁ = f₂ := by
  haveI : IsEmpty ↑(Spec (CommRingCat.of L)) := isEmpty_spec_of_subsingleton L
  exact isInitialOfIsEmpty.hom_ext _ _

end Model
p2m_reactivate "P2MW.S_CerednikDrinfeld_QM_RigidifiedPairClass_exists_isoVia_corr_of_ptR_eq_of_forall_isIdempotentElem.We89C2"

end We89Sub
p2m_reactivate "P2MW.S_CerednikDrinfeld_QM_RigidifiedPairClass_exists_isoVia_corr_of_ptR_eq_of_forall_isIdempotentElem.We89C2"

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace We87R3I

theorem isUnit_natCast_quot {r N : ℕ} [Fact r.Prime] (hrN : ¬ r ∣ N)
    {𝒪 : Type} [CommRing 𝒪] {π : 𝒪} (hunr : Ideal.span {((r : ℕ) : 𝒪)} = Ideal.span {π})
    (S : Type) [CommRing S] [Algebra 𝒪 S] :
    IsUnit ((N : ℕ) : S ⧸ Ideal.span {algebraMap 𝒪 S π}) := by
  apply Ws47RL.isUnit_natCast_of_not_dvd (N := N) hrN hunr (L := S ⧸ Ideal.span {algebraMap 𝒪 S π})
  rw [← Ideal.Quotient.mk_algebraMap, Ideal.Quotient.eq_zero_iff_mem]
  exact Ideal.subset_span rfl

section Frame

variable
    {r N : ℕ} [Fact r.Prime] [NeZero N] (hrN : ¬ r ∣ N) {rbar : ℕ} [Fact rbar.Prime] (hrr : rbar ≠ r)

    (𝒪 : Type) [CommRing 𝒪] (π : 𝒪) (hunr : Ideal.span {((r : ℕ) : 𝒪)} = Ideal.span {π}) (Onr : Type) [CommRing Onr] [Algebra 𝒪 Onr]
    {a b : ℚ} (hBq : IsIndefiniteRamifiedExactlyAt a b r rbar)
    (Λ : Submodule ℤ ℍ[ℚ, a, b]) (hΛ : IsMaximalOrder Λ) (hΛℤ : ∀ m : ℤ, ((m : ℚ) : ℍ[ℚ, a, b]) ∈ Λ)

    (coord : ↥Λ → Zp2 r × Zp2 r) (hcoord : IsOrderCoord Λ r coord)
    (A₀ : FakeEllipticCurve Λ N (Onr ⧸ Ideal.span {algebraMap 𝒪 Onr π}))

    (n : ℕ) (hn : 3 ≤ n) (hrn : ¬ r ∣ n) (M : Scheme.{0}) (fM : M ⟶ Spec (CommRingCat.of 𝒪))
    (ptF : ∀ (S : Type) [CommRing S] (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of 𝒪)),
      FakeEllipticCurve.WithFullLevel Λ N n S → SchemeHomOver s fM)
    (hM : IsFineModuli Λ N n M fM ptF)

    (C : Type) [CommRing C] [IsNoetherianRing C] [Algebra 𝒪 C] (hC : IsNilpotent (algebraMap 𝒪 C π)) (ψ : Onr →ₐ[𝒪] C)

    (X : ℕ → Scheme.{0}) (ξ : ∀ d, X d ⟶ Limits.pullback fM (Spec.map (CommRingCat.ofHom (algebraMap 𝒪 C))))
    (tM : ∀ (T : Type) [CommRing T] [Algebra C T],
      FakeEllipticCurve.WithFullLevel Λ N n T → SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap C T))) (Limits.pullback.snd fM (Spec.map (CommRingCat.ofHom (algebraMap 𝒪 C)))))
    (xOf : ∀ (T : Type) [CommRing T] [Algebra C T] [Algebra 𝒪 T] [IsScalarTower 𝒪 C T]
      (ψT : Onr →ₐ[𝒪] T) (_ : ψT = (IsScalarTower.toAlgHom 𝒪 C T).comp ψ)
      (u : FakeEllipticCurve.WithFullLevel Λ N n T) (ρ : FakeEllipticCurve.Rigidification r π A₀ ψT u.1),
      { x : Spec (CommRingCat.of (T ⧸ Ideal.span {algebraMap C T (algebraMap 𝒪 C π)})) ⟶ X ρ.d //
        x ≫ ξ ρ.d = Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (Ideal.span {algebraMap C T (algebraMap 𝒪 C π)}))) ≫ (tM T u).1 })
    (hmap : RigidifiedPairClass.MapCompat 𝒪 π Onr Λ hΛℤ A₀ n C ψ (Limits.pullback.snd fM (Spec.map (CommRingCat.ofHom (algebraMap 𝒪 C)))) X ξ tM xOf)

    (htM : ∀ (T : Type) [CommRing T] [Algebra C T] [Algebra 𝒪 T] [IsScalarTower 𝒪 C T]
        (u : FakeEllipticCurve.WithFullLevel Λ N n T),
        (tM T u).1 ≫ Limits.pullback.fst fM (Spec.map (CommRingCat.ofHom (algebraMap 𝒪 C))) = (ptF T (Spec.map (CommRingCat.ofHom (algebraMap 𝒪 T))) u).1)

    (hx3 : (∀ (d : ℕ) (T : Type) [CommRing T] [Algebra C T] [Algebra 𝒪 T] [IsScalarTower 𝒪 C T]
                (ψT : Onr →ₐ[𝒪] T) (hψT : ψT = (IsScalarTower.toAlgHom 𝒪 C T).comp ψ)
                (h0 : algebraMap C T (algebraMap 𝒪 C π) = 0) (x : SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap C T))) (ξ d ≫ Limits.pullback.snd fM (Spec.map (CommRingCat.ofHom (algebraMap 𝒪 C))))),
                ∃ (u : FakeEllipticCurve.WithFullLevel Λ N n T) (ρ : FakeEllipticCurve.Rigidification r π A₀ ψT u.1) (hd : ρ.d = d),
                  (RigidifiedPairClass.ptX 𝒪 π Onr Λ A₀ n C ψ (Limits.pullback.snd fM (Spec.map (CommRingCat.ofHom (algebraMap 𝒪 C)))) X ξ tM xOf) d T ψT hψT u ρ hd h0 = x))

    (hx4 : (∀ (d : ℕ) (T : Type) [CommRing T] [Algebra C T] [Algebra 𝒪 T] [IsScalarTower 𝒪 C T]
                (ψT : Onr →ₐ[𝒪] T) (hψT : ψT = (IsScalarTower.toAlgHom 𝒪 C T).comp ψ)
                (h0 : algebraMap C T (algebraMap 𝒪 C π) = 0)
                (u u' : FakeEllipticCurve.WithFullLevel Λ N n T)
                (ρ : FakeEllipticCurve.Rigidification r π A₀ ψT u.1) (ρ' : FakeEllipticCurve.Rigidification r π A₀ ψT u'.1)
                (hd : ρ.d = d) (hd' : ρ'.d = d),
                ((RigidifiedPairClass.ptX 𝒪 π Onr Λ A₀ n C ψ (Limits.pullback.snd fM (Spec.map (CommRingCat.ofHom (algebraMap 𝒪 C)))) X ξ tM xOf) d T ψT hψT u ρ hd h0 = (RigidifiedPairClass.ptX 𝒪 π Onr Λ A₀ n C ψ (Limits.pullback.snd fM (Spec.map (CommRingCat.ofHom (algebraMap 𝒪 C)))) X ξ tM xOf) d T ψT hψT u' ρ' hd' h0 ↔
                  ∃ (i : u.1.A ≅ u'.1.A) (hi : i.hom ≫ u'.1.f = u.1.f), FakeEllipticCurve.WithFullLevel.IsoVia u u' i hi ∧
                    ∃ (ib : ρ.Eb.A ⟶ ρ'.Eb.A) (_ : ib ≫ ρ'.gb = ρ.gb ≫ i.hom) (_ : ib ≫ ρ'.Eb.f = ρ.Eb.f)
                      (uA : ρ'.Ab.A ⟶ ρ.Ab.A) (_ : FakeEllipticCurve.IsPullbackVia (RingHom.id _) ρ.Ab ρ'.Ab uA) (_ : uA ≫ ρ.gA = ρ'.gA),
                      ib ≫ ρ'.φ ≫ uA = ρ.φ)))

    (hxM : ∀ (d : ℕ) (T : Type) [CommRing T] [Algebra C T] [Algebra 𝒪 T] [IsScalarTower 𝒪 C T]
        (ψT : Onr →ₐ[𝒪] T) (hψT : ψT = (IsScalarTower.toAlgHom 𝒪 C T).comp ψ)
        (u : FakeEllipticCurve.WithFullLevel Λ N n T) (ρ : FakeEllipticCurve.Rigidification r π A₀ ψT u.1)
        (hd : ρ.d = d) (h0 : algebraMap C T (algebraMap 𝒪 C π) = 0),
        ((RigidifiedPairClass.ptX 𝒪 π Onr Λ A₀ n C ψ (Limits.pullback.snd fM (Spec.map (CommRingCat.ofHom (algebraMap 𝒪 C)))) X ξ tM xOf) d T ψT hψT u ρ hd h0).1 ≫ ξ d ≫ Limits.pullback.fst fM (Spec.map (CommRingCat.ofHom (algebraMap 𝒪 C))) =
          (ptF T (Spec.map (CommRingCat.ofHom (algebraMap 𝒪 T))) u).1)

    (hxOf : ∀ (S S' : Type) [CommRing S] [Algebra C S] [Algebra 𝒪 S] [IsScalarTower 𝒪 C S]
        [CommRing S'] [Algebra C S'] [Algebra 𝒪 S'] [IsScalarTower 𝒪 C S'] (φ : S →ₐ[C] S')
        (ψS : Onr →ₐ[𝒪] S) (hψS : ψS = (IsScalarTower.toAlgHom 𝒪 C S).comp ψ)
        (hψS' : (φ.restrictScalars 𝒪).comp ψS = (IsScalarTower.toAlgHom 𝒪 C S').comp ψ)
        (u : FakeEllipticCurve.WithFullLevel Λ N n S) (u' : FakeEllipticCurve.WithFullLevel Λ N n S')
        (ρ : FakeEllipticCurve.Rigidification r π A₀ ψS u.1)
        (ρ' : FakeEllipticCurve.Rigidification r π A₀ ((φ.restrictScalars 𝒪).comp ψS) u'.1)
        (g : u'.1.A ⟶ u.1.A) (hg : FakeEllipticCurve.IsPullbackVia (φ : S →+* S') u.1 u'.1 g),
        (u'.2.P).1 ≫ g = Spec.map (CommRingCat.ofHom (φ : S →+* S')) ≫ (u.2.P).1 →
        FakeEllipticCurve.Rigidification.IsPullbackVia (φ.restrictScalars 𝒪) g hg ρ ρ' →
          ∃ hd : ρ'.d = ρ.d, (xOf S' ((φ.restrictScalars 𝒪).comp ψS) hψS' u' ρ').1 ≫ eqToHom (congrArg X hd) =
            Spec.map (CommRingCat.ofHom (RigidifiedPairClass.qmap (algebraMap 𝒪 C π) φ)) ≫ (xOf S ψS hψS u ρ).1)

local notation "gC" => Limits.pullback.snd fM (Spec.map (CommRingCat.ofHom (algebraMap 𝒪 C)))
local notation "PTX" => RigidifiedPairClass.ptX 𝒪 π Onr Λ A₀ n C ψ gC X ξ tM xOf
local notation "PTR" => RigidifiedPairClass.ptR 𝒪 π Onr Λ hΛℤ A₀ n C ψ gC X ξ tM xOf hmap

include hM htM in

theorem tM_eq_of_isoVia
    (S : Type) [CommRing S] [Algebra C S]
    (u u' : FakeEllipticCurve.WithFullLevel Λ N n S)
    (i : u.1.A ≅ u'.1.A) (hi : i.hom ≫ u'.1.f = u.1.f) (hiso : FakeEllipticCurve.WithFullLevel.IsoVia u u' i hi) :
    (tM S u).1 = (tM S u').1 := by
  letI : Algebra 𝒪 S := ((algebraMap C S).comp (algebraMap 𝒪 C)).toAlgebra
  haveI : IsScalarTower 𝒪 C S := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  have hF := hM.ptF_iso S (Spec.map (CommRingCat.ofHom (algebraMap 𝒪 S))) u u' ⟨i, hi, hiso⟩
  apply Limits.pullback.hom_ext
  · rw [htM S u, htM S u', hF]
  · rw [(tM S u).2, (tM S u').2]

include hM htM in

theorem exists_isoVia_of_tM_eq
    (S : Type) [CommRing S] [Algebra C S] [Algebra 𝒪 S] [IsScalarTower 𝒪 C S]
    (u u' : FakeEllipticCurve.WithFullLevel Λ N n S) (h : (tM S u).1 = (tM S u').1) :
    ∃ (i : u.1.A ≅ u'.1.A) (hi : i.hom ≫ u'.1.f = u.1.f), FakeEllipticCurve.WithFullLevel.IsoVia u u' i hi := by
  have hF : ptF S (Spec.map (CommRingCat.ofHom (algebraMap 𝒪 S))) u = ptF S (Spec.map (CommRingCat.ofHom (algebraMap 𝒪 S))) u' := by
    apply Subtype.ext
    rw [← htM S u, ← htM S u', h]
  exact hM.ptF_injective S _ u u' hF

theorem tM_eq_of_ptR_eq
    (S : Type) [CommRing S] [Algebra C S] [Algebra 𝒪 S] [IsScalarTower 𝒪 C S]
    (ψS : Onr →ₐ[𝒪] S) (hψS : ψS = (IsScalarTower.toAlgHom 𝒪 C S).comp ψ)
    (u u' : FakeEllipticCurve.WithFullLevel Λ N n S)
    (ρ : FakeEllipticCurve.Rigidification r π A₀ ψS u.1) (ρ' : FakeEllipticCurve.Rigidification r π A₀ ψS u'.1)
    (h : PTR S ψS hψS u ρ = PTR S ψS hψS u' ρ') :
    (tM S u).1 = (tM S u').1 :=
  congrArg Subtype.val (congrArg (RigidifiedPairClass.toM 𝒪 π Onr Λ hΛℤ A₀ n C ψ gC X ξ tM xOf hmap S) h)

include hrN hrr hunr hBq hΛ coord hcoord hn hrn hM hC htM hx3 hx4 hxM hxOf in

theorem core_bar
    (T : Type) [CommRing T] [Algebra C T] [Algebra 𝒪 T] [IsScalarTower 𝒪 C T]
    (ψT : Onr →ₐ[𝒪] T) (hψT : ψT = (IsScalarTower.toAlgHom 𝒪 C T).comp ψ)
    (h0 : algebraMap C T (algebraMap 𝒪 C π) = 0)
    (hTc : ∀ e : T, IsIdempotentElem e → e = 0 ∨ e = 1)
    (u : FakeEllipticCurve.WithFullLevel Λ N n T)
    (ρ ρ' : FakeEllipticCurve.Rigidification r π A₀ ψT u.1)
    (h : PTR T ψT hψT u ρ = PTR T ψT hψT u ρ') :
    ∃ (ib : ρ.Eb.A ⟶ ρ'.Eb.A) (_ : ib ≫ ρ'.gb = ρ.gb) (_ : ib ≫ ρ'.Eb.f = ρ.Eb.f)
      (uA : ρ'.Ab.A ⟶ ρ.Ab.A) (_ : FakeEllipticCurve.IsPullbackVia (RingHom.id _) ρ.Ab ρ'.Ab uA) (_ : uA ≫ ρ.gA = ρ'.gA)
      (i₁ j₁ : ℕ),
      ib ≫ ρ'.φ ≫ uA ≫ ρ.Ab.act ⟨(((r ^ i₁ : ℕ) : ℤ) : ℚ), hΛℤ _⟩ = ρ.φ ≫ ρ.Ab.act ⟨(((r ^ j₁ : ℕ) : ℤ) : ℚ), hΛℤ _⟩ := by
  classical

  have hx2 := We88PtxNat.ptX_natural hrN hrr 𝒪 π hunr Onr hBq Λ hΛ hΛℤ coord hcoord A₀ n hn hrn M fM ptF hM C hC ψ X ξ tM xOf hxOf
  have hEq := CerednikDrinfeld.QM.RigidifiedPairClass.rel_equivalence hrN hrr 𝒪 π hunr Onr hBq Λ hΛ hΛℤ coord hcoord A₀ n hn hrn
    M fM ptF hM C hC ψ X ξ tM xOf hx2 hx3
    (fun d T _ _ _ _ ψT hψT h0 u u' ρ ρ' hd hd' => (hx4 d T ψT hψT h0 u u' ρ ρ' hd hd').mp) T
  have hrel := hEq.eqvGen_iff.mp (Quot.eqvGen_exact h)
  obtain ⟨-, m, f, hf, hk⟩ := hrel
  choose L iCR iAlg iAway iC iST iO iST2 h0L v v' ϱ ϱ' hdv hdv' i₀ hi₀ hisoV hcorrV hxv hxv' using hk
  letI : ∀ k, CommRing (L k) := iCR
  letI : ∀ k, Algebra (T ⧸ Ideal.span {algebraMap C T (algebraMap 𝒪 C π)}) (L k) := iAlg
  haveI : ∀ k, IsLocalization.Away (f k) (L k) := iAway
  letI : ∀ k, Algebra C (L k) := iC
  haveI : ∀ k, IsScalarTower C (T ⧸ Ideal.span {algebraMap C T (algebraMap 𝒪 C π)}) (L k) := iST
  letI : ∀ k, Algebra 𝒪 (L k) := iO
  haveI : ∀ k, IsScalarTower 𝒪 C (L k) := iST2

  have hpiece : ∀ k, ∃ (hψk : ((((IsScalarTower.toAlgHom C (T ⧸ Ideal.span {algebraMap C T (algebraMap 𝒪 C π)}) (L k)).comp (Ideal.Quotient.mkₐ C (Ideal.span {algebraMap C T (algebraMap 𝒪 C π)}))).restrictScalars 𝒪).comp ψT = (IsScalarTower.toAlgHom 𝒪 C (L k)).comp ψ))
      (uk : FakeEllipticCurve.WithFullLevel Λ N n (L k)) (gk : uk.1.A ⟶ u.1.A)
      (hgk : FakeEllipticCurve.IsPullbackVia (((IsScalarTower.toAlgHom C (T ⧸ Ideal.span {algebraMap C T (algebraMap 𝒪 C π)}) (L k)).comp (Ideal.Quotient.mkₐ C (Ideal.span {algebraMap C T (algebraMap 𝒪 C π)}))) : T →+* L k) u.1 uk.1 gk)
      (hPk : (uk.2.P).1 ≫ gk = Spec.map (CommRingCat.ofHom (((IsScalarTower.toAlgHom C (T ⧸ Ideal.span {algebraMap C T (algebraMap 𝒪 C π)}) (L k)).comp (Ideal.Quotient.mkₐ C (Ideal.span {algebraMap C T (algebraMap 𝒪 C π)}))) : T →+* L k)) ≫ (u.2.P).1)
      (ρk ρk' : FakeEllipticCurve.Rigidification r π A₀ (((((IsScalarTower.toAlgHom C (T ⧸ Ideal.span {algebraMap C T (algebraMap 𝒪 C π)}) (L k)).comp (Ideal.Quotient.mkₐ C (Ideal.span {algebraMap C T (algebraMap 𝒪 C π)}))).restrictScalars 𝒪).comp ψT)) uk.1)
      (hρk : FakeEllipticCurve.Rigidification.IsPullbackVia (((IsScalarTower.toAlgHom C (T ⧸ Ideal.span {algebraMap C T (algebraMap 𝒪 C π)}) (L k)).comp (Ideal.Quotient.mkₐ C (Ideal.span {algebraMap C T (algebraMap 𝒪 C π)}))).restrictScalars 𝒪) gk hgk ρ ρk)
      (hρk' : FakeEllipticCurve.Rigidification.IsPullbackVia (((IsScalarTower.toAlgHom C (T ⧸ Ideal.span {algebraMap C T (algebraMap 𝒪 C π)}) (L k)).comp (Ideal.Quotient.mkₐ C (Ideal.span {algebraMap C T (algebraMap 𝒪 C π)}))).restrictScalars 𝒪) gk hgk ρ' ρk')
      (σ : uk.1.A ≅ uk.1.A) (hσ : σ.hom ≫ uk.1.f = uk.1.f) (_ : FakeEllipticCurve.WithFullLevel.IsoVia uk uk σ hσ),
      ∃ (ib : ρk.Eb.A ⟶ ρk'.Eb.A) (_ : ib ≫ ρk'.gb = ρk.gb ≫ σ.hom) (_ : ib ≫ ρk'.Eb.f = ρk.Eb.f)
      (uA : ρk'.Ab.A ⟶ ρk.Ab.A) (_ : FakeEllipticCurve.IsPullbackVia (RingHom.id _) ρk.Ab ρk'.Ab uA) (_ : uA ≫ ρk.gA = ρk'.gA)
      (i₁ j₁ : ℕ),
      ib ≫ ρk'.φ ≫ uA ≫ ρk.Ab.act ⟨(((r ^ i₁ : ℕ) : ℤ) : ℚ), hΛℤ _⟩ = ρk.φ ≫ ρk.Ab.act ⟨(((r ^ j₁ : ℕ) : ℤ) : ℚ), hΛℤ _⟩ := by
    intro k
    obtain ⟨hψk, uk, ρk, gk, hgk, hPk, hρk, hdk, -⟩ :=
      CerednikDrinfeld.QM.RigidifiedPairClass.exists_pullback_ptX_eq_specMap_comp hrN hrr 𝒪 π hunr Onr hBq Λ hΛ hΛℤ coord hcoord
        A₀ n hn hrn M fM ptF hM C hC ψ X ξ tM xOf hxOf T (L k)
        ((IsScalarTower.toAlgHom C (T ⧸ Ideal.span {algebraMap C T (algebraMap 𝒪 C π)}) (L k)).comp (Ideal.Quotient.mkₐ C (Ideal.span {algebraMap C T (algebraMap 𝒪 C π)}))) ψT hψT u ρ
    obtain ⟨ρk', hρk'⟩ :=
      CerednikDrinfeld.QM.FakeEllipticCurve.Rigidification.exists_isPullbackVia_of_isPullbackVia 𝒪 π Onr Λ A₀ T (L k)
        (((IsScalarTower.toAlgHom C (T ⧸ Ideal.span {algebraMap C T (algebraMap 𝒪 C π)}) (L k)).comp (Ideal.Quotient.mkₐ C (Ideal.span {algebraMap C T (algebraMap 𝒪 C π)}))).restrictScalars 𝒪) ψT u.1 uk.1 gk hgk ρ'
    obtain ⟨σ, hσ, hisoσ, hc⟩ := We88Piece.corr_pullback_of_relLoc_piece hrN hrr 𝒪 π hunr Onr hBq Λ hΛ hΛℤ coord hcoord A₀ n hn hrn
      M fM ptF hM C hC ψ X ξ tM xOf hx4 hxOf T ψT hψT h0 u ρ ρ' (L k) (h0L k) hψk uk gk hgk hPk ρk ρk' hρk hρk'
      (v k) (v' k) (ϱ k) (ϱ' k) (hdv k) (hdv' k) (i₀ k) (hi₀ k) (hisoV k) (hcorrV k) (hxv k) (hxv' k)
    exact ⟨hψk, uk, gk, hgk, hPk, ρk, ρk', hρk, hρk', σ, hσ, hisoσ, hc⟩
  choose hψk uk gk hgk hPk ρk ρk' hρk hρk' σ hσ hisoσ ibk hibk hibkf uAk huAk huAkg ak bk hck using hpiece

  have h0' : algebraMap 𝒪 T π = 0 := by rw [IsScalarTower.algebraMap_apply 𝒪 C T]; exact h0
  obtain ⟨F, F', c, hF, hF', hc, hC1⟩ :=
    CerednikDrinfeld.QM.FakeEllipticCurve.Rigidification.exists_forall_corr_mul_pow_eq_of_forall_isIdempotentElem hrN hrr 𝒪 π hunr
      Onr hBq Λ hΛ hΛℤ coord hcoord A₀ T ψT h0' hTc u.1 u.1 ρ ρ'
  have hdeg : ∀ k, Nontrivial (L k) → F' * c ^ ak k = F * c ^ bk k := by
    intro k hk
    haveI := hk
    exact hC1 (L k) ((((IsScalarTower.toAlgHom C (T ⧸ Ideal.span {algebraMap C T (algebraMap 𝒪 C π)}) (L k)).comp (Ideal.Quotient.mkₐ C (Ideal.span {algebraMap C T (algebraMap 𝒪 C π)})))).restrictScalars 𝒪) (uk k).1 (uk k).1 (gk k) (hgk k) (gk k) (hgk k) (ρk k) (ρk' k)
      (hρk k) (hρk' k) (σ k) (hσ k) (ibk k) (hibk k) (hibkf k) (uAk k) (huAk k) (huAkg k) (ak k) (bk k) (hck k)
  obtain ⟨A, B, hAB⟩ := R3IBlocks.exists_uniform_shifts (ι := {k : Fin m // Nontrivial (L k)}) (fun k => ak k.1) (fun k => bk k.1)
    (fun k l => R3IBlocks.add_eq_add_of_mul_pow_eq hc hF hF' (hdeg k.1 k.2) (hdeg l.1 l.2))

  set t : ℕ := ρ'.d + A with ht
  set t' : ℕ := ρ.d + B with ht'
  set D : ℕ := ρ.d + B + (ρ'.d + A) with hD
  have hdP : (GPShift.pad hΛℤ ρ B t).d = D := by show ρ.d + B + t = D; omega
  have hdP' : (GPShift.pad hΛℤ ρ' A t').d = D := by show ρ'.d + A + t' = D; omega

  have hEk : ∀ k, ∀ (hd₁ : (GPShift.pad hΛℤ (ρk k) B t).d = D) (hd₂ : (GPShift.pad hΛℤ (ρk' k) A t').d = D),
      PTX D (L k) (((((IsScalarTower.toAlgHom C (T ⧸ Ideal.span {algebraMap C T (algebraMap 𝒪 C π)}) (L k)).comp (Ideal.Quotient.mkₐ C (Ideal.span {algebraMap C T (algebraMap 𝒪 C π)})))).restrictScalars 𝒪).comp ψT) (hψk k) (uk k) (GPShift.pad hΛℤ (ρk k) B t) hd₁ (h0L k) =
      PTX D (L k) (((((IsScalarTower.toAlgHom C (T ⧸ Ideal.span {algebraMap C T (algebraMap 𝒪 C π)}) (L k)).comp (Ideal.Quotient.mkₐ C (Ideal.span {algebraMap C T (algebraMap 𝒪 C π)})))).restrictScalars 𝒪).comp ψT) (hψk k) (uk k) (GPShift.pad hΛℤ (ρk' k) A t') hd₂ (h0L k) := by
    intro k hd₁ hd₂
    rcases subsingleton_or_nontrivial (L k) with hLk | hLk
    · haveI := hLk
      exact We89Sub.ptX_eq_of_subsingleton 𝒪 π Onr Λ A₀ n C ψ gC X ξ tM xOf D (L k) _ (hψk k) (h0L k) (uk k) (uk k) _ _ hd₁ hd₂
    · obtain ⟨tk, hak, hbk⟩ := hAB ⟨k, hLk⟩
      have hck' := We89C2.corr_shift_add hΛℤ (ρk k) (ρk' k) (ibk k) (uAk k) (ak k) (bk k) tk (hck k)
      rw [hak, hbk] at hck'
      exact We89C2.ptX_pad_eq_of_corr 𝒪 π Onr Λ hΛℤ A₀ n C ψ gC X ξ tM xOf hx4 (L k) _ (hψk k) (h0L k) (uk k) (uk k) (ρk k) (ρk' k)
        (σ k) (hσ k) (hisoσ k) (ibk k) (hibk k) (hibkf k) (uAk k) (huAk k) (huAkg k) A B hck' t t' D hd₁ hd₂

  have hdk : ∀ k, (ρk k).d = ρ.d := fun k => by
    obtain ⟨-, -, -, -, -, -, hd, -⟩ := hρk k; exact hd
  have hdk' : ∀ k, (ρk' k).d = ρ'.d := fun k => by
    obtain ⟨-, -, -, -, -, -, hd, -⟩ := hρk' k; exact hd
  have hd₁ : ∀ k, (GPShift.pad hΛℤ (ρk k) B t).d = D := fun k => by
    have := hdk k; show (ρk k).d + B + t = D; omega
  have hd₂ : ∀ k, (GPShift.pad hΛℤ (ρk' k) A t').d = D := fun k => by
    have := hdk' k; show (ρk' k).d + A + t' = D; omega

  have hN₁ : ∀ k, (PTX D (L k) (((((IsScalarTower.toAlgHom C (T ⧸ Ideal.span {algebraMap C T (algebraMap 𝒪 C π)}) (L k)).comp (Ideal.Quotient.mkₐ C (Ideal.span {algebraMap C T (algebraMap 𝒪 C π)})))).restrictScalars 𝒪).comp ψT) (hψk k) (uk k) (GPShift.pad hΛℤ (ρk k) B t) (hd₁ k) (h0L k)).1 =
      Spec.map (CommRingCat.ofHom (((IsScalarTower.toAlgHom C (T ⧸ Ideal.span {algebraMap C T (algebraMap 𝒪 C π)}) (L k)).comp (Ideal.Quotient.mkₐ C (Ideal.span {algebraMap C T (algebraMap 𝒪 C π)}))) : T →+* L k)) ≫ (PTX D T ψT hψT u (GPShift.pad hΛℤ ρ B t) hdP h0).1 := fun k =>
    hx2 D T (L k) ((IsScalarTower.toAlgHom C (T ⧸ Ideal.span {algebraMap C T (algebraMap 𝒪 C π)}) (L k)).comp (Ideal.Quotient.mkₐ C (Ideal.span {algebraMap C T (algebraMap 𝒪 C π)}))) ψT hψT (hψk k) u (uk k) (GPShift.pad hΛℤ ρ B t) (GPShift.pad hΛℤ (ρk k) B t) (gk k) (hgk k)
      hdP (hd₁ k) h0 (h0L k) (hPk k) (We89C2.pad_isPullbackVia hΛℤ ((((IsScalarTower.toAlgHom C (T ⧸ Ideal.span {algebraMap C T (algebraMap 𝒪 C π)}) (L k)).comp (Ideal.Quotient.mkₐ C (Ideal.span {algebraMap C T (algebraMap 𝒪 C π)})))).restrictScalars 𝒪) (gk k) (hgk k) ρ (ρk k) (hρk k) B t)
  have hN₂ : ∀ k, (PTX D (L k) (((((IsScalarTower.toAlgHom C (T ⧸ Ideal.span {algebraMap C T (algebraMap 𝒪 C π)}) (L k)).comp (Ideal.Quotient.mkₐ C (Ideal.span {algebraMap C T (algebraMap 𝒪 C π)})))).restrictScalars 𝒪).comp ψT) (hψk k) (uk k) (GPShift.pad hΛℤ (ρk' k) A t') (hd₂ k) (h0L k)).1 =
      Spec.map (CommRingCat.ofHom (((IsScalarTower.toAlgHom C (T ⧸ Ideal.span {algebraMap C T (algebraMap 𝒪 C π)}) (L k)).comp (Ideal.Quotient.mkₐ C (Ideal.span {algebraMap C T (algebraMap 𝒪 C π)}))) : T →+* L k)) ≫ (PTX D T ψT hψT u (GPShift.pad hΛℤ ρ' A t') hdP' h0).1 := fun k =>
    hx2 D T (L k) ((IsScalarTower.toAlgHom C (T ⧸ Ideal.span {algebraMap C T (algebraMap 𝒪 C π)}) (L k)).comp (Ideal.Quotient.mkₐ C (Ideal.span {algebraMap C T (algebraMap 𝒪 C π)}))) ψT hψT (hψk k) u (uk k) (GPShift.pad hΛℤ ρ' A t') (GPShift.pad hΛℤ (ρk' k) A t') (gk k) (hgk k)
      hdP' (hd₂ k) h0 (h0L k) (hPk k) (We89C2.pad_isPullbackVia hΛℤ ((((IsScalarTower.toAlgHom C (T ⧸ Ideal.span {algebraMap C T (algebraMap 𝒪 C π)}) (L k)).comp (Ideal.Quotient.mkₐ C (Ideal.span {algebraMap C T (algebraMap 𝒪 C π)})))).restrictScalars 𝒪) (gk k) (hgk k) ρ' (ρk' k) (hρk' k) A t')
  have hφk : ∀ k, Spec.map (CommRingCat.ofHom (((IsScalarTower.toAlgHom C (T ⧸ Ideal.span {algebraMap C T (algebraMap 𝒪 C π)}) (L k)).comp (Ideal.Quotient.mkₐ C (Ideal.span {algebraMap C T (algebraMap 𝒪 C π)}))) : T →+* L k)) =
      Spec.map (CommRingCat.ofHom (algebraMap (T ⧸ Ideal.span {algebraMap C T (algebraMap 𝒪 C π)}) (L k))) ≫
        Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (Ideal.span {algebraMap C T (algebraMap 𝒪 C π)}))) := fun k => by
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
    rfl

  have hglue : PTX D T ψT hψT u (GPShift.pad hΛℤ ρ B t) hdP h0 = PTX D T ψT hψT u (GPShift.pad hΛℤ ρ' A t') hdP' h0 := by
    apply We88Glue.pt_ext_of_cover 𝒪 π C gC X ξ T h0 D _ _ m f hf L
    intro k
    rw [← Category.assoc, ← Category.assoc, ← hφk k, ← hN₁ k, ← hN₂ k, hEk k (hd₁ k) (hd₂ k)]

  obtain ⟨ib, hib, hibf, uA, huA, huAg, hfin⟩ :=
    We89Finish.corr_refl_of_ptX_pad_eq hrN hrr 𝒪 π hunr Onr hBq Λ hΛ hΛℤ coord hcoord A₀ n hn hrn M fM C ψ X ξ tM xOf hx4
      T ψT hψT h0 u ρ ρ' A B D t t' hdP hdP' hglue
  exact ⟨ib, hib, hibf, uA, huA, huAg, A, B, hfin⟩

include hrN hrr hunr hBq hΛ coord hcoord hn hrn hM hC htM hx3 hx4 hxM hxOf in

theorem core
    (S : Type) [CommRing S] [Algebra C S] [Algebra 𝒪 S] [IsScalarTower 𝒪 C S]
    (ψS : Onr →ₐ[𝒪] S) (hψS : ψS = (IsScalarTower.toAlgHom 𝒪 C S).comp ψ)
    (hSc : ∀ e : S, IsIdempotentElem e → e = 0 ∨ e = 1)
    (u : FakeEllipticCurve.WithFullLevel Λ N n S)
    (ρ ρ' : FakeEllipticCurve.Rigidification r π A₀ ψS u.1)
    (h : PTR S ψS hψS u ρ = PTR S ψS hψS u ρ') :
    ∃ (ib : ρ.Eb.A ⟶ ρ'.Eb.A) (_ : ib ≫ ρ'.gb = ρ.gb ≫ (Iso.refl u.1.A).hom) (_ : ib ≫ ρ'.Eb.f = ρ.Eb.f)
      (uA : ρ'.Ab.A ⟶ ρ.Ab.A) (_ : FakeEllipticCurve.IsPullbackVia (RingHom.id _) ρ.Ab ρ'.Ab uA) (_ : uA ≫ ρ.gA = ρ'.gA)
      (i₁ j₁ : ℕ),
      ib ≫ ρ'.φ ≫ uA ≫ ρ.Ab.act ⟨(((r ^ i₁ : ℕ) : ℤ) : ℚ), hΛℤ _⟩ = ρ.φ ≫ ρ.Ab.act ⟨(((r ^ j₁ : ℕ) : ℤ) : ℚ), hΛℤ _⟩ := by
  classical

  let φ₀ : S →ₐ[C] (S ⧸ Ideal.span {algebraMap C S (algebraMap 𝒪 C π)}) :=
    Ideal.Quotient.mkₐ C (Ideal.span {algebraMap C S (algebraMap 𝒪 C π)})
  have h0b : algebraMap C (S ⧸ Ideal.span {algebraMap C S (algebraMap 𝒪 C π)}) (algebraMap 𝒪 C π) = 0 := by
    rw [← Ideal.Quotient.mk_algebraMap, Ideal.Quotient.eq_zero_iff_mem]
    exact Ideal.subset_span rfl

  obtain ⟨hψb, ub, ρb, g₀, hg₀, hP₀, hρb, hdb, -⟩ :=
    CerednikDrinfeld.QM.RigidifiedPairClass.exists_pullback_ptX_eq_specMap_comp hrN hrr 𝒪 π hunr Onr hBq Λ hΛ hΛℤ coord hcoord
      A₀ n hn hrn M fM ptF hM C hC ψ X ξ tM xOf hxOf S _ φ₀ ψS hψS u ρ
  obtain ⟨ρb', hρb'⟩ :=
    CerednikDrinfeld.QM.FakeEllipticCurve.Rigidification.exists_isPullbackVia_of_isPullbackVia 𝒪 π Onr Λ A₀ S _
      (φ₀.restrictScalars 𝒪) ψS u.1 ub.1 g₀ hg₀ ρ'

  have hTnat := We89Bits.tM_natural 𝒪 n M fM ptF hM C tM htM
  have e₁ := CerednikDrinfeld.QM.RigidifiedPairClass.map_ptR_eq_ptR_of_isPullbackVia 𝒪 π Onr Λ hΛℤ A₀ n C ψ gC X ξ tM xOf hmap
    hTnat hxOf S _ φ₀ ψS hψS hψb u ub ρ ρb g₀ hg₀ hP₀ hρb
  have e₂ := CerednikDrinfeld.QM.RigidifiedPairClass.map_ptR_eq_ptR_of_isPullbackVia 𝒪 π Onr Λ hΛℤ A₀ n C ψ gC X ξ tM xOf hmap
    hTnat hxOf S _ φ₀ ψS hψS hψb u ub ρ' ρb' g₀ hg₀ hP₀ hρb'
  have hb : PTR _ ((φ₀.restrictScalars 𝒪).comp ψS) hψb ub ρb = PTR _ ((φ₀.restrictScalars 𝒪).comp ψS) hψb ub ρb' := by
    rw [← e₁, ← e₂, h]

  have hnil : IsNilpotent (algebraMap C S (algebraMap 𝒪 C π)) := by
    obtain ⟨k, hk⟩ := hC
    exact ⟨k, by rw [← map_pow, hk, map_zero]⟩
  have hSbc : ∀ e : S ⧸ Ideal.span {algebraMap C S (algebraMap 𝒪 C π)}, IsIdempotentElem e → e = 0 ∨ e = 1 :=
    We88Hsc.hSc_quotient_of_isNilpotent S _ (We88Hsc.forall_mem_span_singleton_isNilpotent S _ hnil) hSc

  obtain ⟨ibb, hibb, hibbf, uAb, huAb, huAbg, A, B, hb'⟩ :=
    core_bar hrN hrr 𝒪 π hunr Onr hBq Λ hΛ hΛℤ coord hcoord A₀ n hn hrn M fM ptF hM C hC ψ X ξ tM xOf hmap htM hx3 hx4 hxM hxOf
      _ ((φ₀.restrictScalars 𝒪).comp ψS) hψb h0b hSbc ub ρb ρb' hb

  have hN := isUnit_natCast_quot (N := N) hrN hunr S
  obtain ⟨ib, hib, hibf, uA, huA, huAg, hfin⟩ := We89Transfer.corr_refl_of_corr_refl_pullback hΛℤ (φ₀.restrictScalars 𝒪)
    (We89Bits.quotientMap_bijective_of_tower 𝒪 π C S) hN g₀ hg₀ ρ ρ' ρb ρb' hρb hρb' ibb hibb hibbf uAb huAb huAbg A B hb'
  exact ⟨ib, hib, hibf, uA, huA, huAg, A, B, hfin⟩

end Frame
p2m_reactivate "P2MW.S_CerednikDrinfeld_QM_RigidifiedPairClass_exists_isoVia_corr_of_ptR_eq_of_forall_isIdempotentElem.We89C2"

end We87R3I
p2m_reactivate "P2MW.S_CerednikDrinfeld_QM_RigidifiedPairClass_exists_isoVia_corr_of_ptR_eq_of_forall_isIdempotentElem.We89C2"

theorem solution
    {r N : ℕ} [Fact r.Prime] [NeZero N] (hrN : ¬ r ∣ N) {rbar : ℕ} [Fact rbar.Prime] (hrr : rbar ≠ r)

    (𝒪 : Type) [CommRing 𝒪] (π : 𝒪) (hunr : Ideal.span {((r : ℕ) : 𝒪)} = Ideal.span {π}) (Onr : Type) [CommRing Onr] [Algebra 𝒪 Onr]
    {a b : ℚ} (hBq : IsIndefiniteRamifiedExactlyAt a b r rbar)
    (Λ : Submodule ℤ ℍ[ℚ, a, b]) (hΛ : IsMaximalOrder Λ) (hΛℤ : ∀ m : ℤ, ((m : ℚ) : ℍ[ℚ, a, b]) ∈ Λ)

    (coord : ↥Λ → Zp2 r × Zp2 r) (hcoord : IsOrderCoord Λ r coord)
    (A₀ : FakeEllipticCurve Λ N (Onr ⧸ Ideal.span {algebraMap 𝒪 Onr π}))

    (n : ℕ) (hn : 3 ≤ n) (hrn : ¬ r ∣ n) (M : Scheme.{0}) (fM : M ⟶ Spec (CommRingCat.of 𝒪))
    (ptF : ∀ (S : Type) [CommRing S] (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of 𝒪)),
      FakeEllipticCurve.WithFullLevel Λ N n S → SchemeHomOver s fM)
    (hM : IsFineModuli Λ N n M fM ptF)

    (C : Type) [CommRing C] [IsNoetherianRing C] [Algebra 𝒪 C] (hC : IsNilpotent (algebraMap 𝒪 C π)) (ψ : Onr →ₐ[𝒪] C)

    (X : ℕ → Scheme.{0}) (ξ : ∀ d, X d ⟶ Limits.pullback fM (Spec.map (CommRingCat.ofHom (algebraMap 𝒪 C))))
    (tM : ∀ (T : Type) [CommRing T] [Algebra C T],
      FakeEllipticCurve.WithFullLevel Λ N n T → SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap C T))) (Limits.pullback.snd fM (Spec.map (CommRingCat.ofHom (algebraMap 𝒪 C)))))
    (xOf : ∀ (T : Type) [CommRing T] [Algebra C T] [Algebra 𝒪 T] [IsScalarTower 𝒪 C T]
      (ψT : Onr →ₐ[𝒪] T) (_ : ψT = (IsScalarTower.toAlgHom 𝒪 C T).comp ψ)
      (u : FakeEllipticCurve.WithFullLevel Λ N n T) (ρ : FakeEllipticCurve.Rigidification r π A₀ ψT u.1),
      { x : Spec (CommRingCat.of (T ⧸ Ideal.span {algebraMap C T (algebraMap 𝒪 C π)})) ⟶ X ρ.d //
        x ≫ ξ ρ.d = Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (Ideal.span {algebraMap C T (algebraMap 𝒪 C π)}))) ≫ (tM T u).1 })
    (hmap : RigidifiedPairClass.MapCompat 𝒪 π Onr Λ hΛℤ A₀ n C ψ (Limits.pullback.snd fM (Spec.map (CommRingCat.ofHom (algebraMap 𝒪 C)))) X ξ tM xOf)

    (htM : ∀ (T : Type) [CommRing T] [Algebra C T] [Algebra 𝒪 T] [IsScalarTower 𝒪 C T]
        (u : FakeEllipticCurve.WithFullLevel Λ N n T),
        (tM T u).1 ≫ Limits.pullback.fst fM (Spec.map (CommRingCat.ofHom (algebraMap 𝒪 C))) = (ptF T (Spec.map (CommRingCat.ofHom (algebraMap 𝒪 T))) u).1)

    (hx3 : (∀ (d : ℕ) (T : Type) [CommRing T] [Algebra C T] [Algebra 𝒪 T] [IsScalarTower 𝒪 C T]
                (ψT : Onr →ₐ[𝒪] T) (hψT : ψT = (IsScalarTower.toAlgHom 𝒪 C T).comp ψ)
                (h0 : algebraMap C T (algebraMap 𝒪 C π) = 0) (x : SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap C T))) (ξ d ≫ Limits.pullback.snd fM (Spec.map (CommRingCat.ofHom (algebraMap 𝒪 C))))),
                ∃ (u : FakeEllipticCurve.WithFullLevel Λ N n T) (ρ : FakeEllipticCurve.Rigidification r π A₀ ψT u.1) (hd : ρ.d = d),
                  (RigidifiedPairClass.ptX 𝒪 π Onr Λ A₀ n C ψ (Limits.pullback.snd fM (Spec.map (CommRingCat.ofHom (algebraMap 𝒪 C)))) X ξ tM xOf) d T ψT hψT u ρ hd h0 = x))

    (hx4 : (∀ (d : ℕ) (T : Type) [CommRing T] [Algebra C T] [Algebra 𝒪 T] [IsScalarTower 𝒪 C T]
                (ψT : Onr →ₐ[𝒪] T) (hψT : ψT = (IsScalarTower.toAlgHom 𝒪 C T).comp ψ)
                (h0 : algebraMap C T (algebraMap 𝒪 C π) = 0)
                (u u' : FakeEllipticCurve.WithFullLevel Λ N n T)
                (ρ : FakeEllipticCurve.Rigidification r π A₀ ψT u.1) (ρ' : FakeEllipticCurve.Rigidification r π A₀ ψT u'.1)
                (hd : ρ.d = d) (hd' : ρ'.d = d),
                ((RigidifiedPairClass.ptX 𝒪 π Onr Λ A₀ n C ψ (Limits.pullback.snd fM (Spec.map (CommRingCat.ofHom (algebraMap 𝒪 C)))) X ξ tM xOf) d T ψT hψT u ρ hd h0 = (RigidifiedPairClass.ptX 𝒪 π Onr Λ A₀ n C ψ (Limits.pullback.snd fM (Spec.map (CommRingCat.ofHom (algebraMap 𝒪 C)))) X ξ tM xOf) d T ψT hψT u' ρ' hd' h0 ↔
                  ∃ (i : u.1.A ≅ u'.1.A) (hi : i.hom ≫ u'.1.f = u.1.f), FakeEllipticCurve.WithFullLevel.IsoVia u u' i hi ∧
                    ∃ (ib : ρ.Eb.A ⟶ ρ'.Eb.A) (_ : ib ≫ ρ'.gb = ρ.gb ≫ i.hom) (_ : ib ≫ ρ'.Eb.f = ρ.Eb.f)
                      (uA : ρ'.Ab.A ⟶ ρ.Ab.A) (_ : FakeEllipticCurve.IsPullbackVia (RingHom.id _) ρ.Ab ρ'.Ab uA) (_ : uA ≫ ρ.gA = ρ'.gA),
                      ib ≫ ρ'.φ ≫ uA = ρ.φ)))

    (hxM : ∀ (d : ℕ) (T : Type) [CommRing T] [Algebra C T] [Algebra 𝒪 T] [IsScalarTower 𝒪 C T]
        (ψT : Onr →ₐ[𝒪] T) (hψT : ψT = (IsScalarTower.toAlgHom 𝒪 C T).comp ψ)
        (u : FakeEllipticCurve.WithFullLevel Λ N n T) (ρ : FakeEllipticCurve.Rigidification r π A₀ ψT u.1)
        (hd : ρ.d = d) (h0 : algebraMap C T (algebraMap 𝒪 C π) = 0),
        ((RigidifiedPairClass.ptX 𝒪 π Onr Λ A₀ n C ψ (Limits.pullback.snd fM (Spec.map (CommRingCat.ofHom (algebraMap 𝒪 C)))) X ξ tM xOf) d T ψT hψT u ρ hd h0).1 ≫ ξ d ≫ Limits.pullback.fst fM (Spec.map (CommRingCat.ofHom (algebraMap 𝒪 C))) =
          (ptF T (Spec.map (CommRingCat.ofHom (algebraMap 𝒪 T))) u).1)

    (hxOf : ∀ (S S' : Type) [CommRing S] [Algebra C S] [Algebra 𝒪 S] [IsScalarTower 𝒪 C S]
        [CommRing S'] [Algebra C S'] [Algebra 𝒪 S'] [IsScalarTower 𝒪 C S'] (φ : S →ₐ[C] S')
        (ψS : Onr →ₐ[𝒪] S) (hψS : ψS = (IsScalarTower.toAlgHom 𝒪 C S).comp ψ)
        (hψS' : (φ.restrictScalars 𝒪).comp ψS = (IsScalarTower.toAlgHom 𝒪 C S').comp ψ)
        (u : FakeEllipticCurve.WithFullLevel Λ N n S) (u' : FakeEllipticCurve.WithFullLevel Λ N n S')
        (ρ : FakeEllipticCurve.Rigidification r π A₀ ψS u.1)
        (ρ' : FakeEllipticCurve.Rigidification r π A₀ ((φ.restrictScalars 𝒪).comp ψS) u'.1)
        (g : u'.1.A ⟶ u.1.A) (hg : FakeEllipticCurve.IsPullbackVia (φ : S →+* S') u.1 u'.1 g),
        (u'.2.P).1 ≫ g = Spec.map (CommRingCat.ofHom (φ : S →+* S')) ≫ (u.2.P).1 →
        FakeEllipticCurve.Rigidification.IsPullbackVia (φ.restrictScalars 𝒪) g hg ρ ρ' →
          ∃ hd : ρ'.d = ρ.d, (xOf S' ((φ.restrictScalars 𝒪).comp ψS) hψS' u' ρ').1 ≫ eqToHom (congrArg X hd) =
            Spec.map (CommRingCat.ofHom (RigidifiedPairClass.qmap (algebraMap 𝒪 C π) φ)) ≫ (xOf S ψS hψS u ρ).1) :
    (∀ (S : Type) [CommRing S] [Algebra C S] [Algebra 𝒪 S] [IsScalarTower 𝒪 C S]
          (ψS : Onr →ₐ[𝒪] S) (hψS : ψS = (IsScalarTower.toAlgHom 𝒪 C S).comp ψ)
          (hSc : ∀ e : S, IsIdempotentElem e → e = 0 ∨ e = 1)
          (u u' : FakeEllipticCurve.WithFullLevel Λ N n S)
          (ρ : FakeEllipticCurve.Rigidification r π A₀ ψS u.1) (ρ' : FakeEllipticCurve.Rigidification r π A₀ ψS u'.1),
          (RigidifiedPairClass.ptR 𝒪 π Onr Λ hΛℤ A₀ n C ψ (Limits.pullback.snd fM (Spec.map (CommRingCat.ofHom (algebraMap 𝒪 C)))) X ξ tM xOf hmap) S ψS hψS u ρ = (RigidifiedPairClass.ptR 𝒪 π Onr Λ hΛℤ A₀ n C ψ (Limits.pullback.snd fM (Spec.map (CommRingCat.ofHom (algebraMap 𝒪 C)))) X ξ tM xOf hmap) S ψS hψS u' ρ' →
            ∃ (i : u.1.A ≅ u'.1.A) (hi : i.hom ≫ u'.1.f = u.1.f), FakeEllipticCurve.WithFullLevel.IsoVia u u' i hi ∧
              ∃ (ib : ρ.Eb.A ⟶ ρ'.Eb.A) (_ : ib ≫ ρ'.gb = ρ.gb ≫ i.hom) (_ : ib ≫ ρ'.Eb.f = ρ.Eb.f)
              (uA : ρ'.Ab.A ⟶ ρ.Ab.A) (_ : FakeEllipticCurve.IsPullbackVia (RingHom.id _) ρ.Ab ρ'.Ab uA) (_ : uA ≫ ρ.gA = ρ'.gA)
              (i₁ j₁ : ℕ),
              ib ≫ ρ'.φ ≫ uA ≫ ρ.Ab.act ⟨(((r ^ i₁ : ℕ) : ℤ) : ℚ), hΛℤ _⟩ = ρ.φ ≫ ρ.Ab.act ⟨(((r ^ j₁ : ℕ) : ℤ) : ℚ), hΛℤ _⟩) := by
  intro S _ _ _ _ ψS hψS hSc u u' ρ ρ' hpt

  have htMeq := We87R3I.tM_eq_of_ptR_eq 𝒪 π Onr Λ hΛℤ A₀ n M fM C ψ X ξ tM xOf hmap S ψS hψS u u' ρ ρ' hpt
  obtain ⟨i, hi, hiso⟩ := We87R3I.exists_isoVia_of_tM_eq 𝒪 Λ n M fM ptF hM C tM htM S u u' htMeq

  obtain ⟨hi', hiso'⟩ := Ws47RL.isoVia_symm u u' i hi hiso
  obtain ⟨hm', ha', hl', hP'⟩ := hiso'
  obtain ⟨ρ'', ib₁, hib₁, hib₁f, uA₁, huA₁, huA₁g, a₁, b₁, h₁⟩ :=
    CerednikDrinfeld.QM.FakeEllipticCurve.Rigidification.exists_corr_of_isoVia hΛℤ ρ' i.symm hi' ⟨hm', ha', hl'⟩
  have hTiso := We87R3I.tM_eq_of_isoVia 𝒪 Λ n M fM ptF hM C tM htM
  have hpt' : RigidifiedPairClass.ptR 𝒪 π Onr Λ hΛℤ A₀ n C ψ (Limits.pullback.snd fM (Spec.map (CommRingCat.ofHom (algebraMap 𝒪 C)))) X ξ tM xOf hmap S ψS hψS u' ρ' =
      RigidifiedPairClass.ptR 𝒪 π Onr Λ hΛℤ A₀ n C ψ (Limits.pullback.snd fM (Spec.map (CommRingCat.ofHom (algebraMap 𝒪 C)))) X ξ tM xOf hmap S ψS hψS u ρ'' :=
    CerednikDrinfeld.QM.RigidifiedPairClass.ptR_eq_of_isoVia_of_corr 𝒪 π Onr Λ hΛℤ A₀ n C ψ _ X ξ tM xOf hmap
      hTiso hxOf S ψS hψS u' u ρ' ρ'' i.symm hi' ⟨hm', ha', hl', hP'⟩
      ⟨ib₁, hib₁, hib₁f, uA₁, huA₁, huA₁g, a₁, b₁, h₁⟩

  obtain ⟨ib₀, hib₀, hib₀f, uA₀, huA₀, huA₀g, A, B, h₀⟩ :=
    We87R3I.core hrN hrr 𝒪 π hunr Onr hBq Λ hΛ hΛℤ coord hcoord A₀ n hn hrn M fM ptF hM C hC ψ X ξ tM xOf hmap htM hx3 hx4 hxM hxOf
      S ψS hψS hSc u ρ ρ'' (hpt.trans hpt')

  have hNB := We87R3I.isUnit_natCast_quot (N := N) hrN hunr S
  obtain ⟨ib₂, hib₂, hib₂f, uA₂, huA₂, huA₂g, a₂, b₂, h₂⟩ :=
    Ws47RL.exists_corr_symm hΛℤ hNB i.symm hi' ρ' ρ'' ib₁ hib₁ hib₁f uA₁ huA₁ huA₁g a₁ b₁ h₁
  obtain ⟨ib, hib, hibf, uA, huA, huAg, i', j', h⟩ :=
    We81Corr.corr_trans hΛℤ ρ ρ'' ρ' (Iso.refl u.1.A).hom i.symm.symm.hom
      ib₀ hib₀ hib₀f uA₀ huA₀ huA₀g A B h₀ ib₂ hib₂ hib₂f uA₂ huA₂ huA₂g a₂ b₂ h₂
  refine ⟨i, hi, hiso, ib, ?_, hibf, uA, huA, huAg, i', j', h⟩
  rw [hib, Iso.refl_hom, Category.id_comp, Iso.symm_symm_eq]

end S_CerednikDrinfeld_QM_RigidifiedPairClass_exists_isoVia_corr_of_ptR_eq_of_forall_isIdempotentElem
end P2MW
export P2MW.S_CerednikDrinfeld_QM_RigidifiedPairClass_exists_isoVia_corr_of_ptR_eq_of_forall_isIdempotentElem (solution)
