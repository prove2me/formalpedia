-- Prove2me | solution 1 for CerednikDrinfeld.QM.isFinite_endKerStr_act_and_finrank_eq_natAbs_sq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.141142+00:00
-- url     : https://prove2.me/submissions/a48b76b7-94c9-5573-a504-63503d4e436b

import Mathlib
import Definitions.Def_CerednikDrinfeld_QMStructureOnPolarised
import Definitions.Def_AlgebraicGeometry_RelativeGroupLawEndDegree
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawTranslate
import Theorems.Thm_QuaternionAlgebra_IsIndefiniteRamifiedExactlyAt_isUnit_of_ne_zero
import Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_isFinite_endKerStr_and_endDegree_ne_zero_of_hom_of_schemeHomOverComp_eq_nsmul
import Theorems.Thm_CerednikDrinfeld_QM_act_add_mul_zsmul_neg_pointCommGroup
import Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_endDegree_inv_idPoint_eq_one_and_inv_eq_schemeHomOverComp_inv_idPoint
import Theorems.Thm_Polynomial_eq_sq_of_mul_comp_neg_X_sub_C_eq_pow_four_of_irreducible
import Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_exists_polynomial_eval_eq_endDegree_zpow_mul_of_abelianSchemePropertyBundle
import Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_endDegree_schemeHomOverComp_eq_mul_of_ne_zero
import Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_endDegree_nsmul_idPoint_eq_pow
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_QM_isFinite_endKerStr_act_and_finrank_eq_natAbs_sq
p2m_attr_erase "instance" "AlgebraicGeometry.OModulePresheaf.isScalarTower AlgebraicGeometry.Scheme.OrderedAffineCover.instLinearOrder AlgebraicGeometry.OModulePresheaf.module AlgebraicGeometry.Scheme.OrderedAffineCover.instFintype AlgebraicGeometry.Scheme.OrderedAffineCover.instFintypeIdx AlgebraicGeometry.OModulePresheaf.addCommGroup AlgebraicGeometry.Scheme.OrderedAffineCover.instDecidableEqIdx AlgebraicGeometry.OModulePresheaf.moduleSections TwoChartCech.Sections.M0_moduleA TwoChartCech.Sections.M1_module TwoChartCech.Cover.A01_algebra TwoChartCech.Cover.A0_algebra TwoChartCech.Cover.A1_commRing TwoChartCech.Cover.A1_algebra TwoChartCech.Sections.M01_module TwoChartCech.Sections.M0_addCommGroup TwoChartCech.Sections.M0_tower TwoChartCech.Sections.M01_addCommGroup TwoChartCech.Cover.A0_commRing TwoChartCech.Sections.M1_tower TwoChartCech.Sections.M01_moduleA TwoChartCech.Sections.M0_module TwoChartCech.Sections.M1_moduleA TwoChartCech.Sections.M1_addCommGroup TwoChartCech.Cover.A01_commRing TwoChartCech.Sections.M01_tower CoherentBaseChange.TwoTermComplex.C0_module CoherentBaseChange.TwoTermComplex.C0_addCommGroup CoherentBaseChange.TwoTermComplex.C1_module CoherentBaseChange.TwoTermComplex.C1_addCommGroup CoherentBaseChange.TwoTermComplex.C0_free CoherentBaseChange.TwoTermComplex.C1_finite CoherentBaseChange.TwoTermComplex.C0_finite CoherentBaseChange.TwoTermComplex.C1_free AlgebraicGeometry.OModulePresheaf.instSubsingletonObjZero AlgebraicGeometry.Scheme.Modules.preservesBinaryProducts_opensMap AlgebraicGeometry.Scheme.Modules.pullback_monoidal AlgebraicGeometry.Scheme.Modules.sheafify_isLocalization' AlgebraicGeometry.Scheme.Modules.preservesTerminal_opensMap AlgebraicGeometry.Scheme.Modules.pullback₀_monoidal"
p2m_attr_erase "instance" "AlgebraicGeometry.Scheme.Modules.preservesFiniteProducts_opensMap AlgebraicGeometry.Scheme.Modules.instLiftingPresheafOfModulesSheafifyPresheafWOpensCarrierCarrierCommRingCatGrothendieckTopologyObjFunctorOppositeIsSheafSheafCompPullback₀Pullback PresheafOfModules.PullbackMonoidal.pullback_monoidal PresheafOfModules.PullbackMonoidal.isIso_δ PresheafOfModules.pushforward_laxMonoidal PresheafOfModules.PullbackMonoidal.isIso_η PresheafOfModules.free_monoidal PresheafOfModules.restrictScalars_laxMonoidal PresheafOfModules.PullbackMonoidal.isIso_δ_gS PresheafOfModules.pullback_oplaxMonoidal PresheafOfModules.PullbackMonoidal.instPreservesColimitsOfSizeCompOppositeCommRingCatRingCatForget₂RingHomCarrierCarrierPb PresheafOfModules.pullback_monoidal' AlgebraicGeometry.SmoothOfRelativeDimension.fiberToSpecResidueField AlgebraicGeometry.SmoothOfRelativeDimension.pullback_snd AlgebraicGeometry.SmoothOfRelativeDimension.pullback_fst AlgebraicGeometry.SmoothOfRelativeDimension.smooth_one AlgebraicGeometry.SmoothProperCurve.isIntegral_pullback_Spec_field AlgebraicGeometry.IsProper.fiberToSpecResidueField AlgebraicCurve.CurveModel.isProper AlgebraicCurve.CurveModel.isIntegral AlgebraicCurve.CurveModel.smooth AlgebraicGeometry.Scheme.LocalRepresentabilityULift.instIsLocallyInjectiveFunUliftYonedaGluedToSheaf AlgebraicGeometry.Scheme.LocalRepresentabilityULift.instIsLocallySurjectiveFunUliftYonedaGluedToSheafOfIsLocallySurjectiveZariskiTopologyDescFunctorOppositeType AlgebraicGeometry.Scheme.LocalRepresentabilityULift.instIsOpenImmersionToGlued AlgebraicGeometry.Scheme.LocalRepresentabilityULift.instIsIsoSheafZariskiTopologyTypeUliftYonedaGluedToSheaf AlgebraicGeometry.RelPicard.instIsOpenImmersionToGlued AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.instFundamentalIdentityOfSumRamificationInertia AlgebraicCurve.Place.instIsScalarTowerResidueFieldRestrictPushforward AlgebraicCurve.Place.instAlgebraResidueFieldRestrictPushforward AlgebraicCurve.Place.instIsLocalHomRestrictInclusion AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions PresheafOfModules.ExteriorPower.instModulePresheafAb AlgebraicGeometry.RelEffCartierDiv.subsingleton_of_degree_zero"
p2m_attr_erase "instance" "AlgebraicGeometry.RelEffCartierDiv.isIso_subschemeIota_snd_of_degree_one AlgebraicGeometry.isIso_ker_graphOver_subschemeIota_snd AlgebraicGeometry.isClosedImmersion_graphOver AlgebraicGeometry.FGSubalgebra.instIsDirectedLe AlgebraicGeometry.FGSubalgebra.instQuasiSeparatedSpaceCarrierCarrierCommRingCatObjOppositeSchemeSpecDiagram AlgebraicGeometry.FGSubalgebra.instIsCofilteredOpposite AlgebraicGeometry.FGSubalgebra.instIsAffineObjOppositeSchemeSpecDiagram AlgebraicGeometry.FGSubalgebra.instNonempty AlgebraicGeometry.FGSubalgebra.instNonemptySubtypeLeSubalgebraValFG AlgebraicGeometry.FGSubalgebra.instCompactSpaceCarrierCarrierCommRingCatObjOppositeSchemeSpecDiagram AlgebraicGeometry.FGSubalgebra.instIsDirectedSubtypeLeSubalgebraValFG AlgebraicGeometry.FGSubalgebra.instIsAffineHomMapOppositeSchemeSpecDiagram AlgebraicGeometry.FGSubalgebra.instIsFiltered AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instNeg AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instSMulInt AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instAddCommGroup AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instAdd AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instSub AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instModuleCarrierObjOppositeOpensCarrierCarrierCommRingCatPresheafOpOpensTop AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instSMulCarrierObjOppositeOpensCarrierCarrierCommRingCatPresheafOpOpensTop AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instSMulNat AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instZero AlgebraicCurve.instHasLocalResidue_of_hasCanonicalLocalResidueK AlgebraicCurve.instHasCanonicalLocalResidueK_of_hasCanonicalLocalResidueKStar AlgebraicCurve.Place.kw_ffgc_finiteDimensional_adicCompletion instAlgebraSubtypeMemValuationSubring_definitions AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersIntegersCompletion ModularCurve.KwF4gRRTate.instAlgebraKAdicCompletionIntegers AlgebraicCurve.Place.kw_ffgc_continuousSMul_adicCompletionComap AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersCompletionCompletion IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions AlgebraicCurve.instHasCanonicalLocalResidueK AlgebraicCurve.Place.instAlgebra_restrictResidueField AlgebraicCurve.Place.instIsScalarTower_restrictResidueField AlgebraicCurve.instHasLocalResidue"
p2m_attr_erase "instance" "AlgebraicCurve.HasSeparableResidue.of_perfectField_of_isCurveOver AlgebraicCurve.HasSeparableResidue.of_perfectField AlgebraicCurve.Place.instIsLocalHom_restrictSubringHom AlgebraicCurve.instHasCanonicalLocalResidueKStar ModularCurve.KwNo6Pin.isLocalRing_completion SheafOfModules.isIso_ihomModelToIhom AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instDecidableEqIdx AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instFintype AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instLinearOrder AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instFintypeIdx AlgebraicGeometry.OModulePresheaf.Leray.relAltC_scalarTower AlgebraicGeometry.OModulePresheaf.Leray.ker_relAltd_modΓ AlgebraicGeometry.OModulePresheaf.Leray.relAltC_modΓ AlgebraicGeometry.OModulePresheaf.Leray.biC_abGrp AlgebraicGeometry.OModulePresheaf.Leray.relAltH_modΓ AlgebraicGeometry.OModulePresheaf.Leray.ker_relAltd_smul AlgebraicGeometry.OModulePresheaf.Leray.relAltH_scalarTower AlgebraicGeometry.OModulePresheaf.Leray.relAltH_smul AlgebraicGeometry.OModulePresheaf.Leray.biC_module DoubleComplex.instModuleE₂I DoubleComplex.Bounded.modR DoubleComplex.instModuleE₂II DoubleComplex.instAddCommGroupE₂II DoubleComplex.Bounded.abGrp DoubleComplex.instAddCommGroupE₂I ProjSpaceCech.GradedModule.H.module ProjSpaceCech.GradedModule.H.addCommGroup ProjSpaceCech.GradedModule.sec.instAdd ProjSpaceCech.GradedModule.sec.instNeg ProjSpaceCech.GradedModule.acg ProjSpaceCech.GradedModule.Frac.setoid ProjSpaceCech.GradedModule.modR ProjSpaceCech.GradedModule.sec.instModule ProjSpaceCech.GradedModule.sec.instAddCommGroup ProjSpaceCech.GradedModule.sec.instZero ProjSpaceCech.GradedModule.Presentation.fJ ProjSpaceCech.GradedModule.sec.instSMul ProjSpaceCech.Twist.H.module ProjSpaceCech.Idx.instFintype ProjSpaceCech.Twist.H.addCommGroup"
p2m_attr_erase "instance" "ProjSpaceCech.Idx.instDecidableEq ProjSpaceCech.Twist.Mon.instDecidableEq ProjSpaceCech.Twist.cochain.instAddCommGroup ProjSpaceCech.Twist.cochain.instModule AlgebraicGeometry.FGSubalgebra.tensorStage_directedSystem AlgebraicGeometry.RelEffCartierDiv.isClosedImmersion_subschemeι_resProdMap AlgebraicGeometry.RelEffCartierDiv.isOpenImmersion_resProdMap AlgebraicCurve.CurveModel.locallyOfFiniteType_gluedToBase AlgebraicCurve.CurveModel.isFractionRing_overlap AlgebraicCurve.CurveModel.isLocallyNoetherian_glued AlgebraicCurve.CurveModel.jacobsonSpace_glued AlgebraicCurve.CurveModel.isOpenImmersion_ι₀ AlgebraicCurve.CurveModel.isIntegral_glued AlgebraicCurve.CurveModel.quasiSeparated_gluedToBase AlgebraicCurve.CurveModel.compactSpace_glued AlgebraicCurve.CurveModel.isIntegral_adjoin_chartRing AlgebraicCurve.CurveModel.isFractionRing_overlap_functionField AlgebraicCurve.CurveModel.isProper_gluedToBase AlgebraicCurve.CurveModel.isOpenImmersion_ιU AlgebraicCurve.CurveModel.isOpenImmersion_f₀ AlgebraicCurve.CurveModel.isOpenImmersion_fInf AlgebraicCurve.CurveModel.isOpenImmersion_ιInf AlgebraicCurve.CurveModel.algebra_overlap_functionField AlgebraicCurve.CurveModel.quasiCompact_gluedToBase AlgebraicCurve.CurveModel.algebraAdjoin AlgebraicCurve.CurveModel.isDedekindDomain_chartRing AlgebraicCurve.CurveModel.isIntegralClosure AlgebraicCurve.CurveModel.finite_chartRing AlgebraicCurve.CurveModel.centre_isPrime AlgebraicCurve.CurveModel.isFractionRing_chartRing AlgebraicCurve.CurveModel.finiteType_chartRing AlgebraicCurve.CurveModel.isNoetherianRing_chartRing AlgebraicCurve.CurveModel.isScalarTower_base_adjoin AlgebraicCurve.CurveModel.isScalarTower_adjoin AlgebraicCurve.CurveModel.chartRing_finitePresentation instTopologicallyFGOfFiniteType AlgebraicGeometry.ProjSpace.twistObj.addCommGroup AlgebraicGeometry.ProjSpace.twistFam.module AlgebraicGeometry.ProjSpace.twistObj.module AlgebraicGeometry.ProjSpace.twistObj.moduleSections"
p2m_attr_erase "instance" "AlgebraicGeometry.ProjSpace.twistFam.addCommGroup"
p2m_attr_erase "simp" "GoodReductionJacobian.relativeGroupLawOfGrpObj_inv GoodReductionJacobian.relativeGroupLawOfGrpObj_mul GoodReductionJacobian.overHomEquivSchemeHomOver_apply_coe GoodReductionJacobian.relativeGroupLawOfGrpObj_one GoodReductionJacobian.overHomEquivSchemeHomOver_symm_apply_left AlgebraicGeometry.Scheme.Modules.tensorPow_zero AlgebraicGeometry.Scheme.Modules.tensorPow_succ AlgebraicGeometry.Scheme.OrderedAffineCover.mk.injEq AlgebraicGeometry.OModulePresheaf.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCover.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.mk.injEq AlgebraicGeometry.Scheme.TwoAffineOpenCover.mk.injEq AlgebraicGeometry.Scheme.TwoAffineOpenCover.mk.sizeOf_spec AlgebraicGeometry.Scheme.TwoAffineOpenCover.pullback_U1 AlgebraicGeometry.Scheme.TwoAffineOpenCover.pullback_U0 TwoChartCech.Sections.mk.injEq TwoChartCech.Cover.mk.injEq TwoChartCech.GrothendieckComplex.mk.injEq TwoChartCech.Sections.mk.sizeOf_spec TwoChartCech.Cover.mk.sizeOf_spec TwoChartCech.Cover.lineBundle_r0_apply TwoChartCech.GrothendieckComplex.mk.sizeOf_spec TwoChartCech.Cover.lineBundle_r1_apply CoherentBaseChange.TwoTermComplex.mk.sizeOf_spec CoherentBaseChange.TwoTermComplex.mk.injEq AlgebraicGeometry.OModulePresheaf.prod_obj AlgebraicGeometry.OModulePresheaf.restrOpen_obj AlgebraicGeometry.OModulePresheaf.DevissageStep.mk.injEq AlgebraicGeometry.OModulePresheaf.pushforward_obj AlgebraicGeometry.OModulePresheaf.im_obj AlgebraicGeometry.OModulePresheaf.pow_obj AlgebraicGeometry.OModulePresheaf.fstHom_app AlgebraicGeometry.OModulePresheaf.ker_obj AlgebraicGeometry.OModulePresheaf.coker_obj AlgebraicGeometry.OModulePresheaf.DevissageStep.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCover.preimage_U AlgebraicGeometry.OModulePresheaf.sndHom_app AlgebraicGeometry.OModulePresheaf.Hom.mk.injEq AlgebraicGeometry.OModulePresheaf.Hom.id_app AlgebraicGeometry.OModulePresheaf.AffHom.appSections_apply"
p2m_attr_erase "simp" "AlgebraicGeometry.OModulePresheaf.AffHom.comp_app AlgebraicGeometry.OModulePresheaf.AffSES.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.AffHom.kerMap_coe AlgebraicGeometry.OModulePresheaf.AffHom.id_app AlgebraicGeometry.OModulePresheaf.Hom.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.Hom.toAffHom_app AlgebraicGeometry.OModulePresheaf.SES.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.AffHom.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.Hom.comp_app AlgebraicGeometry.OModulePresheaf.SES.mk.injEq AlgebraicGeometry.OModulePresheaf.AffHom.mk.injEq AlgebraicGeometry.OModulePresheaf.Hom.appSections_apply AlgebraicGeometry.OModulePresheaf.AffSES.mk.injEq PresheafOfModules.freeεIso_hom_app PresheafOfModules.freeμIso_hom_app AlgebraicGeometry.RelPicard.RepresentsRelSubPic.mk.injEq AlgebraicGeometry.RelPicard.SubPicCondition.mk.injEq AlgebraicGeometry.RelPicard.SubPicCondition.mk.sizeOf_spec AlgebraicGeometry.RelPicard.RepresentsRelSubPic.mk.sizeOf_spec AlgebraicGeometry.SmoothProperCurve.sectionBaseChange_coe_snd AlgebraicGeometry.SmoothProperCurve.sectionBaseChange_coe_fst AlgebraicCurve.CurveModel.mk.injEq AlgebraicCurve.CurveModel.mk.sizeOf_spec AlgebraicCurve.mulAdele_apply AlgebraicCurve.residuePairing_apply_coe AlgebraicCurve.mem_adeleBdd AlgebraicCurve.weilSmul_one AlgebraicCurve.diagonalHom_apply AlgebraicCurve.weilSmul_apply AlgebraicCurve.adeleSpaceMul_coe AlgebraicCurve.mulAdele_one AlgebraicGeometry.SmoothProperCurve.FiniteMapData.twoAffineOpenCover_U1 AlgebraicGeometry.SmoothProperCurve.FiniteMapData.mk.injEq AlgebraicGeometry.SmoothProperCurve.FiniteMapData.mk.sizeOf_spec AlgebraicGeometry.SmoothProperCurve.FiniteMapData.twoAffineOpenCover_U0 AlgebraicGeometry.RelPicard.SubPicCondition.onClasses_mk AlgebraicGeometry.RelPicard.relSubPicPresheaf_map_coe CategoryTheory.Functor.OverTotal.ofFibre_fst CategoryTheory.Functor.overTotal_map_fst AlgebraicGeometry.Scheme.LocalRepresentabilityULift.glueData_J"
p2m_attr_erase "simp" "AlgebraicGeometry.Scheme.LocalRepresentabilityULift.uliftYoneda_toGlued_uliftYonedaGluedToSheaf AlgebraicGeometry.Scheme.LocalRepresentabilityULift.glueData_t' AlgebraicGeometry.Scheme.LocalRepresentabilityULift.uliftYoneda_toGlued_uliftYonedaGluedToSheaf_assoc AlgebraicGeometry.Scheme.LocalRepresentabilityULift.uliftYonedaGluedToSheaf_app_toGlued AlgebraicGeometry.Scheme.LocalRepresentabilityULift.glueData_openCover_map AlgebraicGeometry.Scheme.LocalRepresentabilityULift.uliftYonedaGluedToSheaf_app_comp AlgebraicGeometry.Scheme.LocalRepresentabilityULift.glueData_V AlgebraicGeometry.Scheme.LocalRepresentabilityULift.glueData_t AlgebraicGeometry.Scheme.LocalRepresentabilityULift.glueData_U AlgebraicGeometry.Scheme.LocalRepresentabilityULift.glueData_f AlgebraicGeometry.RelPicard.designationOfRepresentableBy_P AlgebraicGeometry.RelPicard.designationOfRepresentableBy_toBase AlgebraicGeometry.RelPicard.rigSection_snd AlgebraicGeometry.RelPicard.RigidifiedLineBundle.ofInvertible_L AlgebraicGeometry.RelPicard.rigSection_snd_assoc AlgebraicGeometry.RelPicard.SubPicGroupCondition.mk.injEq AlgebraicGeometry.RelPicard.SubPicGroupCondition.mk.sizeOf_spec AlgebraicCurve.coe_cechH0Equiv_apply AlgebraicCurve.cechH1ToH1_mk AlgebraicCurve.lSpaceOn_univ AlgebraicCurve.lSpaceOn_empty AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.Divisor.mapRestrict_single AlgebraicCurve.Divisor.pushforward_single AlgebraicCurve.Place.coe_restrictInclusion AlgebraicCurve.Place.mem_fiber AlgebraicCurve.Place.restrict_toValuationSubring AlgebraicCurve.Divisor.degree_pushforward AlgebraicCurve.Place.restrictResidueMap_residue AlgebraicCurve.Pic0.coe_pushforwardDegZeroHom AlgebraicCurve.Pic0.coe_pullbackDegZeroHom AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply"
p2m_attr_erase "simp" "AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Divisor.degree_pushforwardAlong AlgebraicCurve.Pic0.coe_degZeroCorrespondence AlgebraicCurve.Place.mem_fiberAlong AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.jqNModC_one ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one AlgebraicCurve.Place.differentialCoeff_zero AlgebraicCurve.Place.differentialCoeff_dCoord AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.injEq"
p2m_attr_erase "simp" "AlgebraicCurve.TranscendenceTower.mk.injEq AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec AlgebraicCurve.PoleDivisorPackage.mk.injEq AlgebraicGeometry.RelPicard.thetaBundle_def AlgebraicGeometry.RelPicard.picardBundle_def AlgebraicGeometry.RelEffCartierDiv.toRelEffDivisor_ofRelEffDivisor AlgebraicGeometry.RelEffCartierDiv.toRelEffDivisor_I AlgebraicGeometry.mapOnProdOver_fst_assoc AlgebraicGeometry.RelEffCartierDiv.mk.sizeOf_spec AlgebraicGeometry.RelEffCartierDiv.mk.injEq AlgebraicGeometry.mapOnProdOver_snd AlgebraicGeometry.mapOnProdOver_fst AlgebraicGeometry.mapOnProdOver_snd_assoc AlgebraicGeometry.mapOnProdOver_id AlgebraicCurve.RelEffDivisor.mk.sizeOf_spec AlgebraicCurve.mapOnProd_fst AlgebraicCurve.mapOnProd_fst_assoc AlgebraicCurve.mapOnProd_snd AlgebraicCurve.UnivDivisorPack.mk.injEq AlgebraicCurve.RelEffDivisor.mk.injEq AlgebraicCurve.UnivDivisorPack.mk.sizeOf_spec AlgebraicCurve.mapOnProd_snd_assoc AlgebraicGeometry.Scheme.Modules.exteriorPower_obj PresheafOfModules.exteriorPower_map_ιMulti PresheafOfModules.ExteriorPower.appₗ_apply AlgebraicGeometry.prodKerGraph_one AlgebraicGeometry.fibrePowOver.proj_comp AlgebraicGeometry.prodKerGraph_zero AlgebraicGeometry.RelEffCartierDiv.empty_I AlgebraicGeometry.fibrePowOver.proj_comp_assoc AlgebraicGeometry.graphOver_fst_assoc AlgebraicGeometry.RelEffCartierDiv.toPoint_comp AlgebraicGeometry.RelEffCartierDiv.toPoint_comp_assoc AlgebraicGeometry.graphOver_fst AlgebraicGeometry.RelEffCartierDiv.ofPoint_I AlgebraicGeometry.graphOver_snd AlgebraicGeometry.graphOver_snd_assoc AlgebraicCurve.SymmetricPowerPackage.mk.sizeOf_spec AlgebraicCurve.SymmetricPowerPackage.mk.injEq"
p2m_attr_erase "simp" "AlgebraicGeometry.FGSubalgebra.cocone_ι_app_apply AlgebraicGeometry.RelPicard.fst_toProdSpec AlgebraicGeometry.RelPicard.toProdSpec_fst_assoc AlgebraicGeometry.RelPicard.pointsSubBasepointModule_cons AlgebraicGeometry.RelPicard.pointsSubBasepointModule_nil AlgebraicGeometry.RelPicard.fst_toProdSpec_assoc AlgebraicGeometry.RelPicard.toProdSpec_fst AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.sub_app AlgebraicGeometry.Scheme.IdealSheafData.sres_sresTop AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.add_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.mk.sizeOf_spec AlgebraicGeometry.Scheme.IdealSheafData.coe_resLE AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.smul_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.coe_ofLE_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.ideal_range AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.zero_app AlgebraicGeometry.Scheme.IdealSheafData.sres_sres AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.comp_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.neg_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.id_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.coe_mulRight_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.nsmul_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.mk.injEq AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.zsmul_app AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.sizeOf_spec AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.injEq AlgebraicCurve.adeleSingle_coe AlgebraicCurve.kaehlerResidueTermKFam_apply AlgebraicCurve.Place.LocalResidueData.mk.injEq AlgebraicCurve.Place.LocalResidueData.mk.sizeOf_spec AlgebraicCurve.Place.kw_ffgc_adicCompletionComapIntegers_coe AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.sizeOf_spec AlgebraicCurve.Place.mem_simplePoleSubmodule AlgebraicCurve.Place.coe_uniformizerSubring ModularCurve.Lg37.Lg37CompletionSection.mk.injEq AlgebraicCurve.Place.CoefficientFieldSection.mk.injEq AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.injEq ModularCurve.Lg37.Lg37CompletionSection.mk.sizeOf_spec AlgebraicCurve.Place.CoefficientFieldSection.mk.sizeOf_spec AlgebraicCurve.Place.poleSubmodule_one"
p2m_attr_erase "simp" "AlgebraicCurve.Place.mem_poleSubmodule AlgebraicGeometry.Scheme.Modules.toUnitSection_ofUnitSection AlgebraicGeometry.Scheme.Modules.pullbackSection_def AlgebraicGeometry.Scheme.Modules.ofUnitSection_toUnitSection PresheafOfModules.InternalHom.IsSheafAux.appAt_toPresheafHom SheafOfModules.ihomSectionsEquivFamily_unit AlgebraicGeometry.Scheme.Modules.restrictHomEquivFamily_apply SheafOfModules.ihomEval_unit_app AlgebraicGeometry.Scheme.Modules.ihomEval_zero_right AlgebraicGeometry.Scheme.Modules.ihomEval_zero_left AlgebraicGeometry.Scheme.Modules.homOfFamily_app_apply SheafOfModules.unit_ihomSectionsEquivFamily AlgebraicGeometry.Scheme.Modules.familyOfHom_app AlgebraicGeometry.Scheme.Modules.restrictUnitIso_hom_app_apply AlgebraicGeometry.Scheme.Modules.restrictUnitIso_inv_app_apply AlgebraicGeometry.Scheme.Modules.restrictHomOfFamily_app_apply AlgebraicGeometry.Scheme.Modules.restrictHomEquivFamily_symm_apply AlgebraicGeometry.Scheme.Modules.tensorSections_zero_right AlgebraicGeometry.Scheme.Modules.map_unitSection AlgebraicGeometry.Scheme.Modules.tensorSectionsBilin_apply AlgebraicGeometry.Scheme.Modules.tensorPowSection_zero AlgebraicGeometry.Scheme.Modules.tensorSections_zero_left AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_neg AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_zero AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_sub AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_add AlgebraicGeometry.Scheme.OrderedAffineCover.toCoverOf_U AlgebraicGeometry.Scheme.OrderedAffineCoverOf.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCoverOf.mk.injEq AlgebraicGeometry.Scheme.OrderedAffineCover.restrict_U AlgebraicGeometry.OModulePresheaf.Leray.restrictToPreimage_U DoubleComplex.Bounded.mk.injEq DoubleComplex.Bounded.mk.sizeOf_spec DoubleComplex.Convergence.mk.injEq DoubleComplex.Convergence.mk.sizeOf_spec DoubleComplex.SubQuot.mk.sizeOf_spec DoubleComplex.SubQuot.mk.injEq ProjSpaceCech.GradedModule.mk.injEq ProjSpaceCech.GradedModule.mk.sizeOf_spec ProjSpaceCech.GradedModule.Frac.mk.sizeOf_spec"
p2m_attr_erase "simp" "ProjSpaceCech.GradedModule.Presentation.mk.injEq ProjSpaceCech.GradedModule.Frac.mk.injEq ProjSpaceCech.GradedModule.Presentation.mk.sizeOf_spec ProjSpaceCech.GradedModule.Hom.shift_toLinearMap ProjSpaceCech.GradedModule.Hom.mk.sizeOf_spec ProjSpaceCech.GradedModule.Hom.mk.injEq TwoChartCech.Mumford.dK_apply TwoChartCech.Mumford.ι0_apply TwoChartCech.Mumford.ι1_apply TwoChartCech.KerCoprod.dK_apply TwoChartCech.KerCoprod.ι1_apply TwoChartCech.KerCoprod.ι0_apply AlgebraicGeometry.tilde.functorCompPullbackSpecIso_app AlgebraicGeometry.RelPicard.algEquivZeroGroupCut_toSubPicCondition AlgebraicGeometry.RelPicard.LFP.stageHom_val AlgebraicGeometry.RelPicard.BaseChange.relSubPicPresheafRestrictIso_hom_app_coe AlgebraicGeometry.RelPicard.BaseChange.relSubPicPresheafRestrictIso_inv_app_coe AlgebraicGeometry.RelPicard.BaseChange.restrict_P AlgebraicGeometry.RelEffCartierDiv.IsUniversal.lift_comp AlgebraicGeometry.RelEffCartierDiv.functor_map_fst AlgebraicGeometry.RelEffCartierDiv.IsUniversal.homEquiv_apply AlgebraicGeometry.RelEffCartierDiv.IsUniversal.lift_pullbackAlong AlgebraicGeometry.RelEffCartierDiv.IsUniversal.homEquiv_symm_apply AlgebraicGeometry.RelEffCartierDiv.IsUniversal.lift_comp_assoc AlgebraicGeometry.RelEffCartierDiv.supportedIn_top AlgebraicGeometry.RelEffCartierDiv.mem_supportedIn_iff AlgebraicGeometry.RelEffCartierDiv.supportedIn_top_eq AlgebraicGeometry.RelEffCartierDiv.restrictAlong_extendAlong AlgebraicGeometry.RelEffCartierDiv.extendAlong_I AlgebraicGeometry.RelEffCartierDiv.resProdMap_snd AlgebraicGeometry.RelEffCartierDiv.restrictAlong_I AlgebraicGeometry.RelEffCartierDiv.extendAlong_restrictAlong AlgebraicGeometry.RelEffCartierDiv.resProdMap_fst_assoc AlgebraicGeometry.RelEffCartierDiv.resProdMap_snd_assoc AlgebraicGeometry.RelEffCartierDiv.resProdMap_fst CoherentBaseChange.FibreH0Family.mk.sizeOf_spec CoherentBaseChange.FibreH0Family.mk.injEq AlgebraicCurve.CurveModel.coe_gInf AlgebraicCurve.CurveModel.coe_tInvChart AlgebraicCurve.CurveModel.ιInf_gluedToBase_assoc"
p2m_attr_erase "simp" "AlgebraicCurve.CurveModel.ιInf_gluedToBase AlgebraicCurve.CurveModel.primeOfι₀_asIdeal AlgebraicCurve.CurveModel.coe_tChart AlgebraicCurve.CurveModel.ι₀_gluedToBase_assoc AlgebraicCurve.CurveModel.primeOfιInf_asIdeal AlgebraicCurve.CurveModel.ι₀_gluedToBase AlgebraicCurve.CurveModel.coe_tma AlgebraicCurve.CurveModel.coe_primeEquivChartPlaces RegularLocalRingQuotientAscent.dualNumberFst_apply AlgebraicGeometry.ProjSpace.twistObj.mk.injEq AlgebraicGeometry.ProjSpace.twistObj.zero_val AlgebraicGeometry.ProjSpace.twistObj.add_val AlgebraicGeometry.ProjSpace.twist_res_val AlgebraicGeometry.ProjSpace.twist_smul_val AlgebraicGeometry.ProjSpace.twistGradeToObj_val AlgebraicGeometry.ProjSpace.twistObj.smul_val AlgebraicGeometry.ProjSpace.twistGradeEquiv_apply_val AlgebraicGeometry.ProjSpace.twistObj.mk.sizeOf_spec"

set_option autoImplicit false
set_option linter.unusedSectionVars false

open scoped Quaternion
p2m_open "CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry QuaternionAlgebra NeronModelInfra GoodReductionJacobian AlgebraicGeometry.Polarisation AlgebraicGeometry.PolarisedAbelianScheme CerednikDrinfeld CerednikDrinfeld.QM"

namespace RKCRed

section Quat

variable {a b : ℚ}

theorem star_eq_of_add_star (c : ℍ[ℚ, a, b]) (t : ℤ) (ht : c + star c = ((t : ℚ) : ℍ[ℚ, a, b])) :
    star c = ((t : ℚ) : ℍ[ℚ, a, b]) - c := by
  rw [← ht]; abel

theorem star_mul_self_eq_self_mul_star (c : ℍ[ℚ, a, b]) (t : ℤ) (ht : c + star c = ((t : ℚ) : ℍ[ℚ, a, b])) :
    star c * c = c * star c := by
  rw [star_eq_of_add_star c t ht, sub_mul, mul_sub, QuaternionAlgebra.coe_commutes]

theorem key (c : ℍ[ℚ, a, b]) (t n : ℤ) (ht : c + star c = ((t : ℚ) : ℍ[ℚ, a, b]))
    (hn : c * star c = ((n : ℚ) : ℍ[ℚ, a, b])) (r : ℚ) :
    (star c + (r : ℍ[ℚ, a, b])) * (c + (r : ℍ[ℚ, a, b])) = ((r ^ 2 + t * r + n : ℚ) : ℍ[ℚ, a, b]) := by
  have h1 : star c * c = ((n : ℚ) : ℍ[ℚ, a, b]) := by rw [star_mul_self_eq_self_mul_star c t ht, hn]
  have h2 : star c * (r : ℍ[ℚ, a, b]) + (r : ℍ[ℚ, a, b]) * c = (r : ℍ[ℚ, a, b]) * ((t : ℚ) : ℍ[ℚ, a, b]) := by
    rw [← QuaternionAlgebra.coe_commutes r (star c), ← mul_add, add_comm (star c) c, ht]
  calc (star c + (r : ℍ[ℚ, a, b])) * (c + (r : ℍ[ℚ, a, b]))
      = star c * c + (star c * (r : ℍ[ℚ, a, b]) + (r : ℍ[ℚ, a, b]) * c) + (r : ℍ[ℚ, a, b]) * (r : ℍ[ℚ, a, b]) := by
        simp only [add_mul, mul_add]; abel
    _ = ((n : ℚ) : ℍ[ℚ, a, b]) + (r : ℍ[ℚ, a, b]) * ((t : ℚ) : ℍ[ℚ, a, b]) + (r : ℍ[ℚ, a, b]) * (r : ℍ[ℚ, a, b]) := by
        rw [h1, h2]
    _ = ((r ^ 2 + t * r + n : ℚ) : ℍ[ℚ, a, b]) := by
        rw [← QuaternionAlgebra.coe_mul, ← QuaternionAlgebra.coe_mul, ← QuaternionAlgebra.coe_add, ← QuaternionAlgebra.coe_add]
        congr 1; ring

theorem star_add_coe (c : ℍ[ℚ, a, b]) (r : ℚ) : star (c + (r : ℍ[ℚ, a, b])) = star c + (r : ℍ[ℚ, a, b]) := by
  rw [star_add, QuaternionAlgebra.star_coe]

theorem mul_ne_zero_of_hB {q q' : ℕ} [Fact q.Prime] [Fact q'.Prime] (hB : IsIndefiniteRamifiedExactlyAt a b q q')
    {x y : ℍ[ℚ, a, b]} (hx : x ≠ 0) (hy : y ≠ 0) : x * y ≠ 0 := by
  intro h
  obtain ⟨u, rfl⟩ := QuaternionAlgebra.IsIndefiniteRamifiedExactlyAt.isUnit_of_ne_zero hB x hx
  apply hy
  have := congrArg (fun z => (↑u⁻¹ : ℍ[ℚ, a, b]) * z) h
  simpa using this

theorem star_ne_zero {x : ℍ[ℚ, a, b]} (hx : x ≠ 0) : star x ≠ 0 :=
  fun h => hx (by rw [← star_star x, h, star_zero])

theorem cast_natAbs_eq_abs (z : ℤ) : ((z.natAbs : ℕ) : ℚ) = |((z : ℤ) : ℚ)| := by
  rw [← Int.cast_natCast, Nat.cast_natAbs]
  exact Int.cast_abs

end Quat

section Pow

universe u
variable {K : Type u} [Field K] {A : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of K)}

theorem pow_idPoint_eq_nsmul (L : RelativeGroupLaw K f) (hc : L.IsCommutative) (M : ℕ) :
    (letI := L.pointCommGroup hc f; (RelativeGroupLaw.idPoint : SchemeHomOver f f) ^ M) =
      L.nsmul f M RelativeGroupLaw.idPoint := by
  letI := L.pointCommGroup hc f
  induction M with
  | zero => rw [pow_zero, RelativeGroupLaw.nsmul_zero]; rfl
  | succ M ih => rw [pow_succ, RelativeGroupLaw.nsmul_succ, ← ih]; rfl

theorem idPoint_hom (L : RelativeGroupLaw K f) {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of K)) (x y : SchemeHomOver t f) :
    NeronModelInfra.schemeHomOverComp (L.mul t x y) (RelativeGroupLaw.idPoint : SchemeHomOver f f) =
      L.mul t (NeronModelInfra.schemeHomOverComp x RelativeGroupLaw.idPoint)
        (NeronModelInfra.schemeHomOverComp y RelativeGroupLaw.idPoint) := by
  have h : ∀ z : SchemeHomOver t f, NeronModelInfra.schemeHomOverComp z (RelativeGroupLaw.idPoint : SchemeHomOver f f) = z :=
    fun z => Subtype.ext (Category.comp_id _)
  rw [h, h, h]

end Pow

end RKCRed

namespace RKCRed

section Frame

variable (K : Type) [Field K] [IsAlgClosed K] {A : Scheme.{0}} (f : A ⟶ Spec (CommRingCat.of K))
  (L : RelativeGroupLaw K f) (hc : L.IsCommutative) (hA : AbelianSchemePropertyBundle K f)
  [SmoothOfRelativeDimension 2 f]
  {q q' : ℕ} [Fact q.Prime] [Fact q'.Prime]
  {a b : ℚ} (hB : IsIndefiniteRamifiedExactlyAt a b q q')
  (Λ : Submodule ℤ ℍ[ℚ, a, b]) (hΛ : IsMaximalOrder Λ)
  (act : ↥Λ → (A ⟶ A)) (act_over : ∀ x : ↥Λ, act x ≫ f = f)
  (act_hom : ∀ (x : ↥Λ) {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of K)) (P Q : SchemeHomOver t f),
    pushPt (act x) (act_over x) (L.mul t P Q) = L.mul t (pushPt (act x) (act_over x) P) (pushPt (act x) (act_over x) Q))
  (act_one : ∀ h : (1 : ℍ[ℚ, a, b]) ∈ Λ, act ⟨1, h⟩ = 𝟙 A)
  (act_mul : ∀ (x y : ↥Λ) (h : (x : ℍ[ℚ, a, b]) * (y : ℍ[ℚ, a, b]) ∈ Λ),
    act ⟨(x : ℍ[ℚ, a, b]) * (y : ℍ[ℚ, a, b]), h⟩ = act y ≫ act x)
  (act_add : ∀ (x y : ↥Λ) {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of K)) (P : SchemeHomOver t f),
    pushPt (act (x + y)) (act_over (x + y)) P =
      L.mul t (pushPt (act x) (act_over x) P) (pushPt (act y) (act_over y) P))
  (c : ↥Λ) (t n : ℤ) (ht : (c : ℍ[ℚ, a, b]) + Star.star (c : ℍ[ℚ, a, b]) = ((t : ℚ) : ℍ[ℚ, a, b]))
  (hn : (c : ℍ[ℚ, a, b]) * Star.star (c : ℍ[ℚ, a, b]) = ((n : ℚ) : ℍ[ℚ, a, b]))

abbrev I (x : ↥Λ) : SchemeHomOver f f := ⟨act x, act_over x⟩

abbrev one : ↥Λ := ⟨1, hΛ.isOrder.one_mem⟩

theorem coe_add_zsmul_one (x : ↥Λ) (m : ℤ) :
    ((x + m • one Λ hΛ : ↥Λ) : ℍ[ℚ, a, b]) = (x : ℍ[ℚ, a, b]) + ((m : ℚ) : ℍ[ℚ, a, b]) := by
  rw [Submodule.coe_add, Submodule.coe_smul, zsmul_eq_mul, mul_one, QuaternionAlgebra.coe_intCast]

abbrev cbar : ↥Λ := t • one Λ hΛ - c

include ht in
theorem coe_cbar : ((cbar Λ hΛ c t : ↥Λ) : ℍ[ℚ, a, b]) = star (c : ℍ[ℚ, a, b]) := by
  rw [star_eq_of_add_star _ t ht, Submodule.coe_sub, Submodule.coe_smul, zsmul_eq_mul, mul_one, QuaternionAlgebra.coe_intCast]

include ht in
theorem coe_cbar_add (m : ℤ) :
    ((cbar Λ hΛ c t + m • one Λ hΛ : ↥Λ) : ℍ[ℚ, a, b]) = star ((c : ℍ[ℚ, a, b]) + ((m : ℚ) : ℍ[ℚ, a, b])) := by
  rw [coe_add_zsmul_one, coe_cbar (ht := ht), star_add_coe]

theorem cbar_add_eq_neg (m : ℤ) : cbar Λ hΛ c t + m • one Λ hΛ = -(c + (-t - m) • one Λ hΛ) := by
  show t • one Λ hΛ - c + m • one Λ hΛ = -(c + (-t - m) • one Λ hΛ)
  rw [sub_smul, neg_smul]
  abel

abbrev Nq (m : ℤ) : ℤ := m ^ 2 + t * m + n

include ht hn in
theorem star_mul_eq_N (m : ℤ) :
    star ((c : ℍ[ℚ, a, b]) + ((m : ℚ) : ℍ[ℚ, a, b])) * ((c : ℍ[ℚ, a, b]) + ((m : ℚ) : ℍ[ℚ, a, b])) =
      (((Nq t n m : ℤ) : ℚ) : ℍ[ℚ, a, b]) := by
  rw [star_add_coe, key _ t n ht hn]
  push_cast
  ring_nf

end Frame

end RKCRed

namespace RKCRed
section Core

variable (K : Type) [Field K] [IsAlgClosed K] {A : Scheme.{0}} (f : A ⟶ Spec (CommRingCat.of K))
  (L : RelativeGroupLaw K f) (hc : L.IsCommutative) (hA : AbelianSchemePropertyBundle K f)
  [SmoothOfRelativeDimension 2 f]
  {q q' : ℕ} [Fact q.Prime] [Fact q'.Prime]
  {a b : ℚ} (hB : IsIndefiniteRamifiedExactlyAt a b q q')
  (Λ : Submodule ℤ ℍ[ℚ, a, b]) (hΛ : IsMaximalOrder Λ)
  (act : ↥Λ → (A ⟶ A)) (act_over : ∀ x : ↥Λ, act x ≫ f = f)
  (act_hom : ∀ (x : ↥Λ) {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of K)) (P Q : SchemeHomOver t f),
    pushPt (act x) (act_over x) (L.mul t P Q) = L.mul t (pushPt (act x) (act_over x) P) (pushPt (act x) (act_over x) Q))
  (act_one : ∀ h : (1 : ℍ[ℚ, a, b]) ∈ Λ, act ⟨1, h⟩ = 𝟙 A)
  (act_mul : ∀ (x y : ↥Λ) (h : (x : ℍ[ℚ, a, b]) * (y : ℍ[ℚ, a, b]) ∈ Λ),
    act ⟨(x : ℍ[ℚ, a, b]) * (y : ℍ[ℚ, a, b]), h⟩ = act y ≫ act x)
  (act_add : ∀ (x y : ↥Λ) {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of K)) (P : SchemeHomOver t f),
    pushPt (act (x + y)) (act_over (x + y)) P =
      L.mul t (pushPt (act x) (act_over x) P) (pushPt (act y) (act_over y) P))
  (c : ↥Λ) (t n : ℤ) (ht : (c : ℍ[ℚ, a, b]) + Star.star (c : ℍ[ℚ, a, b]) = ((t : ℚ) : ℍ[ℚ, a, b]))
  (hn : (c : ℍ[ℚ, a, b]) * Star.star (c : ℍ[ℚ, a, b]) = ((n : ℚ) : ℍ[ℚ, a, b]))

include act_hom act_one act_mul act_add in

theorem dict :
    letI := L.pointCommGroup hc f
    (∀ x y : ↥Λ, I K f Λ act act_over (x + y) = I K f Λ act act_over x * I K f Λ act act_over y) ∧
    (∀ (x y : ↥Λ) (h : (x : ℍ[ℚ, a, b]) * (y : ℍ[ℚ, a, b]) ∈ Λ),
      I K f Λ act act_over ⟨(x : ℍ[ℚ, a, b]) * (y : ℍ[ℚ, a, b]), h⟩ =
        NeronModelInfra.schemeHomOverComp (I K f Λ act act_over y) (I K f Λ act act_over x)) ∧
    (∀ k : ℤ, I K f Λ act act_over (k • one Λ hΛ) = (RelativeGroupLaw.idPoint : SchemeHomOver f f) ^ k) ∧
    (∀ x : ↥Λ, I K f Λ act act_over (-x) = (I K f Λ act act_over x)⁻¹) ∧
    (∀ (x : ↥Λ) {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of K)) (P Q : SchemeHomOver t f),
      NeronModelInfra.schemeHomOverComp (L.mul t P Q) (I K f Λ act act_over x) =
        L.mul t (NeronModelInfra.schemeHomOverComp P (I K f Λ act act_over x))
          (NeronModelInfra.schemeHomOverComp Q (I K f Λ act act_over x))) :=
  CerednikDrinfeld.QM.act_add_mul_zsmul_neg_pointCommGroup K f L hc Λ hΛ act act_over act_hom act_one act_mul act_add

include hc hA hB act_hom act_one act_mul act_add ht hn in

theorem nonvanish (hns : ∀ r : ℚ, (c : ℍ[ℚ, a, b]) ≠ (r : ℍ[ℚ, a, b])) (m : ℤ) :
    IsFinite (L.endKerStr (I K f Λ act act_over (c + m • one Λ hΛ))) ∧
      L.endDegree (I K f Λ act act_over (c + m • one Λ hΛ)) ≠ 0 := by
  classical
  letI := L.pointCommGroup hc f
  obtain ⟨-, hmul, hzs, -, hhom⟩ := dict K f L hc Λ hΛ act act_over act_hom act_one act_mul act_add
  have hxc : ((c + m • one Λ hΛ : ↥Λ) : ℍ[ℚ, a, b]) = (c : ℍ[ℚ, a, b]) + ((m : ℚ) : ℍ[ℚ, a, b]) :=
    coe_add_zsmul_one Λ hΛ c m
  have hx0 : (c : ℍ[ℚ, a, b]) + ((m : ℚ) : ℍ[ℚ, a, b]) ≠ 0 := by
    intro h
    apply hns (-(m : ℚ))
    rw [QuaternionAlgebra.coe_neg, eq_neg_iff_add_eq_zero, h]
  have hN := star_mul_eq_N Λ c t n ht hn m
  have hN0 : Nq t n m ≠ 0 := by
    intro h0
    have hprod := mul_ne_zero_of_hB hB (star_ne_zero hx0) hx0
    rw [hN, h0] at hprod
    exact hprod (by push_cast; rfl)

  have hzx : (((Nq t n m) • (cbar Λ hΛ c t + m • one Λ hΛ) : ↥Λ) : ℍ[ℚ, a, b]) * ((c + m • one Λ hΛ : ↥Λ) : ℍ[ℚ, a, b]) =
      ((((Nq t n m) ^ 2 • one Λ hΛ) : ↥Λ) : ℍ[ℚ, a, b]) := by
    rw [Submodule.coe_smul, coe_cbar_add Λ hΛ c t ht m, hxc, smul_mul_assoc, hN, Submodule.coe_smul]
    show (Nq t n m) • ((((Nq t n m : ℤ) : ℚ)) : ℍ[ℚ, a, b]) = (Nq t n m ^ 2) • (1 : ℍ[ℚ, a, b])
    rw [zsmul_eq_mul, zsmul_eq_mul, mul_one, ← QuaternionAlgebra.coe_intCast, ← QuaternionAlgebra.coe_intCast,
      ← QuaternionAlgebra.coe_mul]
    congr 1
    push_cast
    ring
  have hmem : (((Nq t n m) • (cbar Λ hΛ c t + m • one Λ hΛ) : ↥Λ) : ℍ[ℚ, a, b]) *
      ((c + m • one Λ hΛ : ↥Λ) : ℍ[ℚ, a, b]) ∈ Λ := by
    rw [hzx]; exact ((Nq t n m) ^ 2 • one Λ hΛ).2
  have heq : (⟨_, hmem⟩ : ↥Λ) = (Nq t n m) ^ 2 • one Λ hΛ := Subtype.ext hzx
  have hcomp : NeronModelInfra.schemeHomOverComp (I K f Λ act act_over (c + m • one Λ hΛ))
      (I K f Λ act act_over ((Nq t n m) • (cbar Λ hΛ c t + m • one Λ hΛ))) =
        L.nsmul f ((Nq t n m).natAbs ^ 2) RelativeGroupLaw.idPoint := by
    rw [← hmul _ _ hmem, heq, hzs, show ((Nq t n m) ^ 2 : ℤ) = (((Nq t n m).natAbs ^ 2 : ℕ) : ℤ) by
      push_cast; exact (sq_abs _).symm, zpow_natCast]
    exact pow_idPoint_eq_nsmul L hc _
  exact GoodReductionJacobian.RelativeGroupLaw.isFinite_endKerStr_and_endDegree_ne_zero_of_hom_of_schemeHomOverComp_eq_nsmul
    K f L hc hA 2 _ _ (hhom _) (hhom _) _ (pow_ne_zero 2 (Int.natAbs_ne_zero.mpr hN0)) hcomp

end Core
end RKCRed

namespace RKCRed
section Core2

variable (K : Type) [Field K] [IsAlgClosed K] {A : Scheme.{0}} (f : A ⟶ Spec (CommRingCat.of K))
  (L : RelativeGroupLaw K f) (hc : L.IsCommutative) (hA : AbelianSchemePropertyBundle K f)
  [SmoothOfRelativeDimension 2 f]
  {q q' : ℕ} [Fact q.Prime] [Fact q'.Prime]
  {a b : ℚ} (hB : IsIndefiniteRamifiedExactlyAt a b q q')
  (Λ : Submodule ℤ ℍ[ℚ, a, b]) (hΛ : IsMaximalOrder Λ)
  (act : ↥Λ → (A ⟶ A)) (act_over : ∀ x : ↥Λ, act x ≫ f = f)
  (act_hom : ∀ (x : ↥Λ) {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of K)) (P Q : SchemeHomOver t f),
    pushPt (act x) (act_over x) (L.mul t P Q) = L.mul t (pushPt (act x) (act_over x) P) (pushPt (act x) (act_over x) Q))
  (act_one : ∀ h : (1 : ℍ[ℚ, a, b]) ∈ Λ, act ⟨1, h⟩ = 𝟙 A)
  (act_mul : ∀ (x y : ↥Λ) (h : (x : ℍ[ℚ, a, b]) * (y : ℍ[ℚ, a, b]) ∈ Λ),
    act ⟨(x : ℍ[ℚ, a, b]) * (y : ℍ[ℚ, a, b]), h⟩ = act y ≫ act x)
  (act_add : ∀ (x y : ↥Λ) {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of K)) (P : SchemeHomOver t f),
    pushPt (act (x + y)) (act_over (x + y)) P =
      L.mul t (pushPt (act x) (act_over x) P) (pushPt (act y) (act_over y) P))
  (c : ↥Λ) (t n : ℤ) (ht : (c : ℍ[ℚ, a, b]) + Star.star (c : ℍ[ℚ, a, b]) = ((t : ℚ) : ℍ[ℚ, a, b]))
  (hn : (c : ℍ[ℚ, a, b]) * Star.star (c : ℍ[ℚ, a, b]) = ((n : ℚ) : ℍ[ℚ, a, b]))

include act_hom act_one act_mul act_add in

theorem I_add_zsmul (k : ℤ) :
    letI := L.pointCommGroup hc f
    I K f Λ act act_over (c + k • one Λ hΛ) = (RelativeGroupLaw.idPoint : SchemeHomOver f f) ^ k * I K f Λ act act_over c := by
  letI := L.pointCommGroup hc f
  obtain ⟨hadd, -, hzs, -, -⟩ := dict K f L hc Λ hΛ act act_over act_hom act_one act_mul act_add
  rw [hadd, hzs, mul_comm]

include hc hA hB act_hom act_one act_mul act_add ht hn in

theorem deg_bar (hns : ∀ r : ℚ, (c : ℍ[ℚ, a, b]) ≠ (r : ℍ[ℚ, a, b])) (m : ℤ) :
    L.endDegree (I K f Λ act act_over (cbar Λ hΛ c t + m • one Λ hΛ)) =
      L.endDegree (I K f Λ act act_over (c + (-t - m) • one Λ hΛ)) ∧
    L.endDegree (I K f Λ act act_over (cbar Λ hΛ c t + m • one Λ hΛ)) ≠ 0 := by
  classical
  letI := L.pointCommGroup hc f
  obtain ⟨-, -, -, hneg, hhom⟩ := dict K f L hc Λ hΛ act act_over act_hom act_one act_mul act_add
  obtain ⟨-, hinv, hdeg⟩ :=
    GoodReductionJacobian.RelativeGroupLaw.endDegree_inv_idPoint_eq_one_and_inv_eq_schemeHomOverComp_inv_idPoint K f L hc hA 2
  have h0 := (nonvanish K f L hc hA hB Λ hΛ act act_over act_hom act_one act_mul act_add c t n ht hn hns (-t - m)).2
  have e : L.endDegree (I K f Λ act act_over (cbar Λ hΛ c t + m • one Λ hΛ)) =
      L.endDegree (I K f Λ act act_over (c + (-t - m) • one Λ hΛ)) := by
    rw [cbar_add_eq_neg, hneg, hinv, hdeg _ (hhom _) h0]
  exact ⟨e, e ▸ h0⟩

include hc hA hB act_hom act_one act_mul act_add ht hn in

theorem deg_prod (hns : ∀ r : ℚ, (c : ℍ[ℚ, a, b]) ≠ (r : ℍ[ℚ, a, b])) (m : ℤ) (hpos : 0 < Nq t n m) :
    L.endDegree (I K f Λ act act_over (c + m • one Λ hΛ)) * L.endDegree (I K f Λ act act_over (cbar Λ hΛ c t + m • one Λ hΛ)) =
      (Nq t n m).natAbs ^ (2 * 2) := by
  classical
  letI := L.pointCommGroup hc f
  obtain ⟨-, hmul, hzs, -, hhom⟩ := dict K f L hc Λ hΛ act act_over act_hom act_one act_mul act_add
  have hβ0 := (nonvanish K f L hc hA hB Λ hΛ act act_over act_hom act_one act_mul act_add c t n ht hn hns m).2
  have hγ0 := (deg_bar K f L hc hA hB Λ hΛ act act_over act_hom act_one act_mul act_add c t n ht hn hns m).2
  rw [← GoodReductionJacobian.RelativeGroupLaw.endDegree_schemeHomOverComp_eq_mul_of_ne_zero K f L hc hA 2 _ _ (hhom _) (hhom _) hβ0 hγ0]

  have hprod : ((cbar Λ hΛ c t + m • one Λ hΛ : ↥Λ) : ℍ[ℚ, a, b]) * ((c + m • one Λ hΛ : ↥Λ) : ℍ[ℚ, a, b]) =
      ((((Nq t n m) • one Λ hΛ) : ↥Λ) : ℍ[ℚ, a, b]) := by
    rw [coe_cbar_add Λ hΛ c t ht m, coe_add_zsmul_one, star_mul_eq_N Λ c t n ht hn m, Submodule.coe_smul]
    show ((((Nq t n m : ℤ) : ℚ)) : ℍ[ℚ, a, b]) = (Nq t n m) • (1 : ℍ[ℚ, a, b])
    rw [zsmul_eq_mul, mul_one, QuaternionAlgebra.coe_intCast]
  have hmem : ((cbar Λ hΛ c t + m • one Λ hΛ : ↥Λ) : ℍ[ℚ, a, b]) * ((c + m • one Λ hΛ : ↥Λ) : ℍ[ℚ, a, b]) ∈ Λ := by
    rw [hprod]; exact ((Nq t n m) • one Λ hΛ).2
  have heq : (⟨_, hmem⟩ : ↥Λ) = (Nq t n m) • one Λ hΛ := Subtype.ext hprod
  rw [← hmul _ _ hmem, heq, hzs, ← Int.natAbs_of_nonneg hpos.le, zpow_natCast, pow_idPoint_eq_nsmul L hc]
  exact GoodReductionJacobian.RelativeGroupLaw.endDegree_nsmul_idPoint_eq_pow K f L hc hA 2 _
    (Int.natAbs_pos.mpr hpos.ne')

end Core2
end RKCRed

open RKCRed _root_.Polynomial _root_.AlgebraicGeometry.Polynomial in
set_option maxHeartbeats 3200000 in
theorem solution
    (K : Type) [Field K] [IsAlgClosed K] {A : Scheme.{0}} (f : A ⟶ Spec (CommRingCat.of K))
    (L : RelativeGroupLaw K f) (hc : L.IsCommutative) (hA : AbelianSchemePropertyBundle K f)
    [SmoothOfRelativeDimension 2 f]
    {q q' : ℕ} [Fact q.Prime] [Fact q'.Prime] (hqq' : q' ≠ q)
    {a b : ℚ} (hB : IsIndefiniteRamifiedExactlyAt a b q q')
    (Λ : Submodule ℤ ℍ[ℚ, a, b]) (hΛ : IsMaximalOrder Λ)
    (act : ↥Λ → (A ⟶ A)) (act_over : ∀ x : ↥Λ, act x ≫ f = f)
    (act_hom : ∀ (x : ↥Λ) {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of K)) (P Q : SchemeHomOver t f),
      pushPt (act x) (act_over x) (L.mul t P Q) = L.mul t (pushPt (act x) (act_over x) P) (pushPt (act x) (act_over x) Q))
    (act_one : ∀ h : (1 : ℍ[ℚ, a, b]) ∈ Λ, act ⟨1, h⟩ = 𝟙 A)
    (act_mul : ∀ (x y : ↥Λ) (h : (x : ℍ[ℚ, a, b]) * (y : ℍ[ℚ, a, b]) ∈ Λ),
      act ⟨(x : ℍ[ℚ, a, b]) * (y : ℍ[ℚ, a, b]), h⟩ = act y ≫ act x)
    (act_add : ∀ (x y : ↥Λ) {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of K)) (P : SchemeHomOver t f),
      pushPt (act (x + y)) (act_over (x + y)) P =
        L.mul t (pushPt (act x) (act_over x) P) (pushPt (act y) (act_over y) P))
    (c : ↥Λ) (hc0 : (c : ℍ[ℚ, a, b]) ≠ 0)
    (t n : ℤ) (ht : (c : ℍ[ℚ, a, b]) + Star.star (c : ℍ[ℚ, a, b]) = ((t : ℚ) : ℍ[ℚ, a, b]))
    (hn : (c : ℍ[ℚ, a, b]) * Star.star (c : ℍ[ℚ, a, b]) = ((n : ℚ) : ℍ[ℚ, a, b])) :
    IsFinite (L.endKerStr ⟨act c, act_over c⟩) ∧
      (L.endKerStr ⟨act c, act_over c⟩).finrank (IsLocalRing.closedPoint K) = n.natAbs ^ 2 := by
  classical
  letI := L.pointCommGroup hc f
  suffices h : IsFinite (L.endKerStr (I K f Λ act act_over c)) ∧ L.endDegree (I K f Λ act act_over c) = n.natAbs ^ 2 by
    refine ⟨h.1, ?_⟩
    haveI := h.1
    rw [← RelativeGroupLaw.endDegree_of_isFinite]
    exact h.2
  obtain ⟨hadd, hmul, hzs, hneg, hhom⟩ := dict K f L hc Λ hΛ act act_over act_hom act_one act_mul act_add
  obtain ⟨-, hinv, hdeg⟩ :=
    GoodReductionJacobian.RelativeGroupLaw.endDegree_inv_idPoint_eq_one_and_inv_eq_schemeHomOverComp_inv_idPoint K f L hc hA 2
  by_cases hsc : ∃ r : ℚ, (c : ℍ[ℚ, a, b]) = (r : ℍ[ℚ, a, b])
  ·
    obtain ⟨r, hr⟩ := hsc
    have h2r : r + r = t := by
      have h := ht
      rw [hr, QuaternionAlgebra.star_coe, ← QuaternionAlgebra.coe_add] at h
      exact_mod_cast QuaternionAlgebra.coe_injective h
    have hrr : r * r = n := by
      have h := hn
      rw [hr, QuaternionAlgebra.star_coe, ← QuaternionAlgebra.coe_mul] at h
      exact_mod_cast QuaternionAlgebra.coe_injective h
    have ht2 : t ^ 2 = 4 * n := by
      have h : ((t : ℚ)) ^ 2 = 4 * n := by rw [← h2r, ← hrr]; ring
      exact_mod_cast h
    obtain ⟨k, hk⟩ : Even t := by
      have he : Even (t ^ 2) := ⟨2 * n, by rw [ht2]; ring⟩
      exact (Int.even_pow.mp he).1
    have hrk : r = k := by
      have : (2 : ℚ) * r = 2 * k := by rw [two_mul, h2r, hk]; push_cast; ring
      linarith
    have hck : c = k • one Λ hΛ := Subtype.ext (by
      rw [hr, hrk, Submodule.coe_smul]
      show (((k : ℤ) : ℚ) : ℍ[ℚ, a, b]) = k • (1 : ℍ[ℚ, a, b])
      rw [zsmul_eq_mul, mul_one, QuaternionAlgebra.coe_intCast])
    have hk0 : k ≠ 0 := by
      rintro rfl
      apply hc0
      rw [hr, hrk]; simp
    have hnk : n = k ^ 2 := by
      have h : (n : ℚ) = (k : ℚ) ^ 2 := by rw [← hrr, hrk]; ring
      exact_mod_cast h
    have hdegc : L.endDegree (I K f Λ act act_over c) = k.natAbs ^ (2 * 2) := by
      rcases lt_or_gt_of_ne hk0 with hlt | hgt
      · have e1 : I K f Λ act act_over (-c) = L.nsmul f k.natAbs RelativeGroupLaw.idPoint := by
          rw [hck, ← neg_smul, hzs, show (-k : ℤ) = (k.natAbs : ℕ) by omega, zpow_natCast]
          exact pow_idPoint_eq_nsmul L hc _
        have hd1 : L.endDegree (I K f Λ act act_over (-c)) = k.natAbs ^ (2 * 2) := by
          rw [e1]
          exact GoodReductionJacobian.RelativeGroupLaw.endDegree_nsmul_idPoint_eq_pow K f L hc hA 2 _
            (Int.natAbs_pos.mpr hk0)
        have hne : L.endDegree (I K f Λ act act_over (-c)) ≠ 0 := by rw [hd1]; positivity
        calc L.endDegree (I K f Λ act act_over c)
            = L.endDegree (I K f Λ act act_over (-(-c))) := by rw [neg_neg]
          _ = L.endDegree (I K f Λ act act_over (-c)) := by rw [hneg, hinv]; exact hdeg _ (hhom _) hne
          _ = k.natAbs ^ (2 * 2) := hd1
      · have e1 : I K f Λ act act_over c = L.nsmul f k.natAbs RelativeGroupLaw.idPoint := by
          rw [hck, hzs, show (k : ℤ) = (k.natAbs : ℕ) by omega, zpow_natCast]
          exact pow_idPoint_eq_nsmul L hc _
        rw [e1]
        exact GoodReductionJacobian.RelativeGroupLaw.endDegree_nsmul_idPoint_eq_pow K f L hc hA 2 _
          (Int.natAbs_pos.mpr hk0)
    have hne : L.endDegree (I K f Λ act act_over c) ≠ 0 := by rw [hdegc]; positivity
    refine ⟨?_, ?_⟩
    · by_contra hnf
      exact hne (RelativeGroupLaw.endDegree_of_not_isFinite _ _ hnf)
    · rw [hdegc, hnk, Int.natAbs_pow, ← pow_mul]
  ·
    push Not at hsc
    have hnv := nonvanish K f L hc hA hB Λ hΛ act act_over act_hom act_one act_mul act_add c t n ht hn hsc
    obtain ⟨P, hPdeg, hP⟩ :=
      GoodReductionJacobian.RelativeGroupLaw.exists_polynomial_eval_eq_endDegree_zpow_mul_of_abelianSchemePropertyBundle
        K f L hc hA 2 RelativeGroupLaw.idPoint (I K f Λ act act_over c) (idPoint_hom L) (hhom c)
    have hPI : ∀ k : ℤ, ((L.endDegree (I K f Λ act act_over (c + k • one Λ hΛ)) : ℕ) : ℚ) = P.eval (k : ℚ) := fun k => by
      rw [I_add_zsmul K f L hc Λ hΛ act act_over act_hom act_one act_mul act_add c k]
      exact hP k

    have hNpos : ∀ m : ℤ, |t| + |n| + 1 ≤ m → 0 < Nq t n m := by
      intro m hm
      have hm0 : 0 ≤ m := by linarith [abs_nonneg t, abs_nonneg n]
      have hm1 : 1 ≤ m := by linarith [abs_nonneg t, abs_nonneg n]
      have h1 : -|t| * m ≤ t * m := mul_le_mul_of_nonneg_right (neg_abs_le t) hm0
      have h2 : -|n| ≤ n := neg_abs_le n
      have h3 : (|n| + 1) * m ≤ (m - |t|) * m := mul_le_mul_of_nonneg_right (by linarith) hm0
      have h4 : (|n| + 1) * 1 ≤ (|n| + 1) * m := mul_le_mul_of_nonneg_left hm1 (by positivity)
      show 0 < m ^ 2 + t * m + n
      nlinarith [h1, h2, h3, h4]

    have hev : ∀ m : ℤ, |t| + |n| + 1 ≤ m →
        (P * P.comp (-X - C (t : ℚ))).eval (m : ℚ) = ((X ^ 2 + C (t : ℚ) * X + C (n : ℚ)) ^ 4 : Polynomial ℚ).eval (m : ℚ) := by
      intro m hm
      have h1 := hPI m
      have h2 := hPI (-t - m)
      have hb := (deg_bar K f L hc hA hB Λ hΛ act act_over act_hom act_one act_mul act_add c t n ht hn hsc m).1
      have hp := deg_prod K f L hc hA hB Λ hΛ act act_over act_hom act_one act_mul act_add c t n ht hn hsc m (hNpos m hm)
      rw [hb] at hp
      have hq : ((L.endDegree (I K f Λ act act_over (c + m • one Λ hΛ)) : ℕ) : ℚ) *
          ((L.endDegree (I K f Λ act act_over (c + (-t - m) • one Λ hΛ)) : ℕ) : ℚ) = ((Nq t n m : ℤ) : ℚ) ^ 4 := by
        have := congrArg (fun z : ℕ => (z : ℚ)) hp
        push_cast at this
        rw [this, cast_natAbs_eq_abs]
        exact Even.pow_abs ⟨2, rfl⟩ _
      rw [eval_mul, eval_comp, eval_sub, eval_neg, eval_X, eval_C,
        show (-(m : ℚ) - (t : ℚ)) = (((-t - m : ℤ)) : ℚ) by push_cast; ring, ← h1, ← h2, hq]
      simp only [eval_pow, eval_add, eval_mul, eval_X, eval_C]
      push_cast
      ring
    have hPQ : P * P.comp (-X - C (t : ℚ)) = (X ^ 2 + C (t : ℚ) * X + C (n : ℚ)) ^ 4 := by
      apply Polynomial.eq_of_infinite_eval_eq
      refine Set.Infinite.mono ?_ ((Set.Ici_infinite (|t| + |n| + 1)).image (Int.cast_injective (α := ℚ)).injOn)
      rintro _ ⟨m, hm, rfl⟩
      exact hev m hm

    have hdegN : (X ^ 2 + C (t : ℚ) * X + C (n : ℚ) : Polynomial ℚ).natDegree = 2 := by
      have hlt : (C (t : ℚ) * X + C (n : ℚ)).degree < (X ^ 2 : Polynomial ℚ).degree := by
        rw [degree_X_pow]
        refine (degree_add_le _ _).trans_lt ?_
        refine max_lt ((degree_C_mul_X_le _).trans_lt (by norm_num)) (degree_C_le.trans_lt (by norm_num))
      rw [add_assoc, natDegree_add_eq_left_of_degree_lt hlt, natDegree_X_pow]
    have hirr : Irreducible (X ^ 2 + C (t : ℚ) * X + C (n : ℚ) : Polynomial ℚ) := by
      apply Polynomial.irreducible_of_degree_le_three_of_not_isRoot
      · rw [hdegN]; decide
      · intro r hr
        rw [IsRoot, eval_add, eval_add, eval_pow, eval_mul, eval_C, eval_X, eval_C] at hr
        have hkey := key (c : ℍ[ℚ, a, b]) t n ht hn r
        rw [show r ^ 2 + (t : ℚ) * r + n = 0 by linear_combination hr, QuaternionAlgebra.coe_zero] at hkey
        by_cases hcr : (c : ℍ[ℚ, a, b]) + (r : ℍ[ℚ, a, b]) = 0
        · exact hsc (-r) (by rw [QuaternionAlgebra.coe_neg, eq_neg_iff_add_eq_zero, hcr])
        · have hsr : star (c : ℍ[ℚ, a, b]) + (r : ℍ[ℚ, a, b]) = 0 := by
            by_contra h; exact mul_ne_zero_of_hB hB h hcr hkey
          apply hsc (-r)
          rw [← star_star (c : ℍ[ℚ, a, b]), eq_neg_iff_add_eq_zero.mpr hsr, star_neg, QuaternionAlgebra.star_coe,
            QuaternionAlgebra.coe_neg]
    have hpos' : ∃ m : ℤ, 0 < P.eval (m : ℚ) := by
      refine ⟨|t| + |n| + 1, ?_⟩
      rw [← hPI]
      exact_mod_cast Nat.pos_of_ne_zero (hnv _).2
    have hPeq := Polynomial.eq_sq_of_mul_comp_neg_X_sub_C_eq_pow_four_of_irreducible t n P hirr hPdeg hPQ hpos'
    have h0 := hPI 0
    rw [zero_smul, add_zero, hPeq] at h0
    simp only [eval_pow, eval_add, eval_mul, eval_X, eval_C, Int.cast_zero, mul_zero, zero_pow two_ne_zero,
      zero_add, add_zero] at h0
    have hdegc : L.endDegree (I K f Λ act act_over c) = n.natAbs ^ 2 := by
      have h : ((L.endDegree (I K f Λ act act_over c) : ℕ) : ℚ) = ((n.natAbs ^ 2 : ℕ) : ℚ) := by
        rw [h0, Nat.cast_pow, cast_natAbs_eq_abs, sq_abs]
      exact_mod_cast h
    refine ⟨?_, hdegc⟩
    have := (hnv 0).1
    rwa [zero_smul, add_zero] at this

end S_CerednikDrinfeld_QM_isFinite_endKerStr_act_and_finrank_eq_natAbs_sq
end P2MW
export P2MW.S_CerednikDrinfeld_QM_isFinite_endKerStr_act_and_finrank_eq_natAbs_sq (solution)
