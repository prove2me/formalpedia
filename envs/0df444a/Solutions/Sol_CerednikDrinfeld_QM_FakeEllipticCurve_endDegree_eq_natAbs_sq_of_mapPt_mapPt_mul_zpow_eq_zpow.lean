-- Prove2me | solution 1 for CerednikDrinfeld.QM.FakeEllipticCurve.endDegree_eq_natAbs_sq_of_mapPt_mapPt_mul_zpow_eq_zpow
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.837917+00:00
-- url     : https://prove2.me/submissions/5fc4a870-a8cb-53b2-8dc6-6c73dc853e6b

import Definitions.Def_CerednikDrinfeld_QMModuli
import Definitions.Def_AlgebraicGeometry_RelativeGroupLawEndDegree
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawKernel
import Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_exists_polynomial_eval_eq_endDegree_zpow_mul_of_abelianSchemePropertyBundle
import Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_endDegree_nsmul_idPoint_eq_pow
import Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_endDegree_schemeHomOverComp_eq_mul_of_ne_zero
import Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_endDegree_ne_zero_of_forall_act_comp_eq_of_ne_one
import Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_natCard_isTorsionPoint_eq_pow_of_natCast_ne_zero
import Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_smoothOfRelativeDimension_two
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_endDegree_eq_natAbs_sq_of_mapPt_mapPt_mul_zpow_eq_zpow
p2m_attr_erase "instance" "AlgebraicGeometry.Scheme.PresheafOfModules.symmetricCategory SheafOfModules.instFaithfulRingSheafPModToPMod SheafOfModules.symmetricCategory AlgebraicGeometry.Scheme.PresheafOfModules.monoidalCategory AlgebraicGeometry.Scheme.PresheafOfModules.monoidalClosed SheafOfModules.instFullRingSheafPModToPMod SheafOfModules.monoidalCategory AlgebraicGeometry.Scheme.Modules.symmetricCategory SheafOfModules.monoidalClosed SheafOfModules.instIsLocalizationPModRingSheafSheafifyFunctorPresheafW SheafOfModules.sheafifyFunctor_monoidal AlgebraicGeometry.Scheme.Modules.monoidalClosed AlgebraicGeometry.instMonoidalPresheafOfModulesModulesSheafify AlgebraicGeometry.Scheme.Modules.monoidalCategory PresheafOfModules.instMonoidalClosed PresheafOfModules.InternalHom.instModuleCarrierObjOppositeCommRingCatSubtypePiFamilyMemAddSubgroupNaturalFamilies PresheafOfModules.InternalHom.instModuleCarrierObjOppositeRingCatCompCommRingCatForget₂RingHomCarrierCarrierAbPresheaf PresheafOfModules.InternalHom.instSMulCarrierObjOppositeCommRingCatSubtypePiFamilyMemAddSubgroupNaturalFamilies AlgebraicGeometry.Scheme.Hom.opensMapFinal AlgebraicGeometry.RelPicard.RigidifiedLineBundle.setoid AlgebraicGeometry.RelPicard.RigidifiedLineBundle.instInhabited AlgebraicGeometry.OModulePresheaf.isScalarTower AlgebraicGeometry.Scheme.OrderedAffineCover.instLinearOrder AlgebraicGeometry.OModulePresheaf.module AlgebraicGeometry.Scheme.OrderedAffineCover.instFintype AlgebraicGeometry.Scheme.OrderedAffineCover.instFintypeIdx AlgebraicGeometry.OModulePresheaf.addCommGroup AlgebraicGeometry.Scheme.OrderedAffineCover.instDecidableEqIdx AlgebraicGeometry.OModulePresheaf.moduleSections TwoChartCech.Sections.M0_moduleA TwoChartCech.Sections.M1_module TwoChartCech.Cover.A01_algebra TwoChartCech.Cover.A0_algebra TwoChartCech.Cover.A1_commRing TwoChartCech.Cover.A1_algebra TwoChartCech.Sections.M01_module TwoChartCech.Sections.M0_addCommGroup TwoChartCech.Sections.M0_tower TwoChartCech.Sections.M01_addCommGroup TwoChartCech.Cover.A0_commRing"
p2m_attr_erase "instance" "TwoChartCech.Sections.M1_tower TwoChartCech.Sections.M01_moduleA TwoChartCech.Sections.M0_module TwoChartCech.Sections.M1_moduleA TwoChartCech.Sections.M1_addCommGroup TwoChartCech.Cover.A01_commRing TwoChartCech.Sections.M01_tower CoherentBaseChange.TwoTermComplex.C0_module CoherentBaseChange.TwoTermComplex.C0_addCommGroup CoherentBaseChange.TwoTermComplex.C1_module CoherentBaseChange.TwoTermComplex.C1_addCommGroup CoherentBaseChange.TwoTermComplex.C0_free CoherentBaseChange.TwoTermComplex.C1_finite CoherentBaseChange.TwoTermComplex.C0_finite CoherentBaseChange.TwoTermComplex.C1_free AlgebraicGeometry.Scheme.Modules.preservesBinaryProducts_opensMap AlgebraicGeometry.Scheme.Modules.pullback_monoidal AlgebraicGeometry.Scheme.Modules.sheafify_isLocalization' AlgebraicGeometry.Scheme.Modules.preservesTerminal_opensMap AlgebraicGeometry.Scheme.Modules.pullback₀_monoidal AlgebraicGeometry.Scheme.Modules.preservesFiniteProducts_opensMap AlgebraicGeometry.Scheme.Modules.instLiftingPresheafOfModulesSheafifyPresheafWOpensCarrierCarrierCommRingCatGrothendieckTopologyObjFunctorOppositeIsSheafSheafCompPullback₀Pullback PresheafOfModules.PullbackMonoidal.pullback_monoidal PresheafOfModules.PullbackMonoidal.isIso_δ PresheafOfModules.pushforward_laxMonoidal PresheafOfModules.PullbackMonoidal.isIso_η PresheafOfModules.free_monoidal PresheafOfModules.restrictScalars_laxMonoidal PresheafOfModules.PullbackMonoidal.isIso_δ_gS PresheafOfModules.pullback_oplaxMonoidal PresheafOfModules.PullbackMonoidal.instPreservesColimitsOfSizeCompOppositeCommRingCatRingCatForget₂RingHomCarrierCarrierPb PresheafOfModules.pullback_monoidal' AlgebraicGeometry.SmoothOfRelativeDimension.fiberToSpecResidueField AlgebraicGeometry.SmoothOfRelativeDimension.pullback_snd AlgebraicGeometry.SmoothOfRelativeDimension.pullback_fst AlgebraicGeometry.SmoothOfRelativeDimension.smooth_one AlgebraicGeometry.SmoothProperCurve.isIntegral_pullback_Spec_field AlgebraicGeometry.IsProper.fiberToSpecResidueField AlgebraicCurve.CurveModel.isProper AlgebraicCurve.CurveModel.isIntegral"
p2m_attr_erase "instance" "AlgebraicCurve.CurveModel.smooth AlgebraicGeometry.Scheme.LocalRepresentabilityULift.instIsLocallyInjectiveFunUliftYonedaGluedToSheaf AlgebraicGeometry.Scheme.LocalRepresentabilityULift.instIsLocallySurjectiveFunUliftYonedaGluedToSheafOfIsLocallySurjectiveZariskiTopologyDescFunctorOppositeType AlgebraicGeometry.Scheme.LocalRepresentabilityULift.instIsOpenImmersionToGlued AlgebraicGeometry.Scheme.LocalRepresentabilityULift.instIsIsoSheafZariskiTopologyTypeUliftYonedaGluedToSheaf AlgebraicGeometry.RelPicard.instIsOpenImmersionToGlued AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.instFundamentalIdentityOfSumRamificationInertia AlgebraicCurve.Place.instIsScalarTowerResidueFieldRestrictPushforward AlgebraicCurve.Place.instAlgebraResidueFieldRestrictPushforward AlgebraicCurve.Place.instIsLocalHomRestrictInclusion AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions PresheafOfModules.ExteriorPower.instModulePresheafAb AlgebraicGeometry.RelEffCartierDiv.subsingleton_of_degree_zero AlgebraicGeometry.RelEffCartierDiv.isIso_subschemeIota_snd_of_degree_one AlgebraicGeometry.isIso_ker_graphOver_subschemeIota_snd AlgebraicGeometry.isClosedImmersion_graphOver AlgebraicGeometry.FGSubalgebra.instIsDirectedLe AlgebraicGeometry.FGSubalgebra.instQuasiSeparatedSpaceCarrierCarrierCommRingCatObjOppositeSchemeSpecDiagram AlgebraicGeometry.FGSubalgebra.instIsCofilteredOpposite AlgebraicGeometry.FGSubalgebra.instIsAffineObjOppositeSchemeSpecDiagram AlgebraicGeometry.FGSubalgebra.instNonempty AlgebraicGeometry.FGSubalgebra.instNonemptySubtypeLeSubalgebraValFG AlgebraicGeometry.FGSubalgebra.instCompactSpaceCarrierCarrierCommRingCatObjOppositeSchemeSpecDiagram AlgebraicGeometry.FGSubalgebra.instIsDirectedSubtypeLeSubalgebraValFG AlgebraicGeometry.FGSubalgebra.instIsAffineHomMapOppositeSchemeSpecDiagram AlgebraicGeometry.FGSubalgebra.instIsFiltered AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instNeg AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instSMulInt AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instAddCommGroup AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instAdd AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instSub AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instModuleCarrierObjOppositeOpensCarrierCarrierCommRingCatPresheafOpOpensTop AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instSMulCarrierObjOppositeOpensCarrierCarrierCommRingCatPresheafOpOpensTop"
p2m_attr_erase "instance" "AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instSMulNat AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instZero AlgebraicCurve.instHasLocalResidue_of_hasCanonicalLocalResidueK AlgebraicCurve.instHasCanonicalLocalResidueK_of_hasCanonicalLocalResidueKStar AlgebraicCurve.Place.kw_ffgc_finiteDimensional_adicCompletion instAlgebraSubtypeMemValuationSubring_definitions AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersIntegersCompletion ModularCurve.KwF4gRRTate.instAlgebraKAdicCompletionIntegers AlgebraicCurve.Place.kw_ffgc_continuousSMul_adicCompletionComap AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersCompletionCompletion IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions AlgebraicCurve.instHasCanonicalLocalResidueK AlgebraicCurve.Place.instAlgebra_restrictResidueField AlgebraicCurve.Place.instIsScalarTower_restrictResidueField AlgebraicCurve.instHasLocalResidue AlgebraicCurve.HasSeparableResidue.of_perfectField_of_isCurveOver AlgebraicCurve.HasSeparableResidue.of_perfectField AlgebraicCurve.Place.instIsLocalHom_restrictSubringHom AlgebraicCurve.instHasCanonicalLocalResidueKStar ModularCurve.KwNo6Pin.isLocalRing_completion SheafOfModules.isIso_ihomModelToIhom AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instDecidableEqIdx AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instFintype AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instLinearOrder AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instFintypeIdx AlgebraicGeometry.OModulePresheaf.instSubsingletonObjZero AlgebraicGeometry.OModulePresheaf.Leray.relAltC_scalarTower AlgebraicGeometry.OModulePresheaf.Leray.ker_relAltd_modΓ AlgebraicGeometry.OModulePresheaf.Leray.relAltC_modΓ AlgebraicGeometry.OModulePresheaf.Leray.biC_abGrp AlgebraicGeometry.OModulePresheaf.Leray.relAltH_modΓ AlgebraicGeometry.OModulePresheaf.Leray.ker_relAltd_smul AlgebraicGeometry.OModulePresheaf.Leray.relAltH_scalarTower AlgebraicGeometry.OModulePresheaf.Leray.relAltH_smul AlgebraicGeometry.OModulePresheaf.Leray.biC_module"
p2m_attr_erase "instance" "DoubleComplex.instModuleE₂I DoubleComplex.Bounded.modR DoubleComplex.instModuleE₂II DoubleComplex.instAddCommGroupE₂II DoubleComplex.Bounded.abGrp DoubleComplex.instAddCommGroupE₂I AlgebraicGeometry.ChowDatum.hι_closed AlgebraicGeometry.ChowDatumProj.hιN_closed AlgebraicGeometry.ChowDatumProj.hp_proper AlgebraicGeometry.ChowDatum.hp_isoU AlgebraicGeometry.ChowDatum.hp_proper AlgebraicGeometry.ProjSpace.algebraAway AlgebraicGeometry.ProjSpace.instIsProperProdOverπ AlgebraicGeometry.ChowDatumProj.hp_isoU AlgebraicGeometry.ProjSpace.isProper_π AlgebraicGeometry.ProjSpace.finiteType_mvPolynomial ProjSpaceCech.GradedModule.H.module ProjSpaceCech.GradedModule.H.addCommGroup ProjSpaceCech.GradedModule.sec.instAdd ProjSpaceCech.GradedModule.sec.instNeg ProjSpaceCech.GradedModule.acg ProjSpaceCech.GradedModule.Frac.setoid ProjSpaceCech.GradedModule.modR ProjSpaceCech.GradedModule.sec.instModule ProjSpaceCech.GradedModule.sec.instAddCommGroup ProjSpaceCech.GradedModule.sec.instZero ProjSpaceCech.GradedModule.Presentation.fJ ProjSpaceCech.GradedModule.sec.instSMul ProjSpaceCech.Twist.H.module ProjSpaceCech.Idx.instFintype ProjSpaceCech.Twist.H.addCommGroup ProjSpaceCech.Idx.instDecidableEq ProjSpaceCech.Twist.Mon.instDecidableEq ProjSpaceCech.Twist.cochain.instAddCommGroup ProjSpaceCech.Twist.cochain.instModule AlgebraicGeometry.FGSubalgebra.tensorStage_directedSystem AlgebraicGeometry.RelEffCartierDiv.isClosedImmersion_subschemeι_resProdMap AlgebraicGeometry.RelEffCartierDiv.isOpenImmersion_resProdMap AlgebraicCurve.CurveModel.locallyOfFiniteType_gluedToBase AlgebraicCurve.CurveModel.isFractionRing_overlap"
p2m_attr_erase "instance" "AlgebraicCurve.CurveModel.isLocallyNoetherian_glued AlgebraicCurve.CurveModel.jacobsonSpace_glued AlgebraicCurve.CurveModel.isOpenImmersion_ι₀ AlgebraicCurve.CurveModel.isIntegral_glued AlgebraicCurve.CurveModel.quasiSeparated_gluedToBase AlgebraicCurve.CurveModel.compactSpace_glued AlgebraicCurve.CurveModel.isIntegral_adjoin_chartRing AlgebraicCurve.CurveModel.isFractionRing_overlap_functionField AlgebraicCurve.CurveModel.isProper_gluedToBase AlgebraicCurve.CurveModel.isOpenImmersion_ιU AlgebraicCurve.CurveModel.isOpenImmersion_f₀ AlgebraicCurve.CurveModel.isOpenImmersion_fInf AlgebraicCurve.CurveModel.isOpenImmersion_ιInf AlgebraicCurve.CurveModel.algebra_overlap_functionField AlgebraicCurve.CurveModel.quasiCompact_gluedToBase AlgebraicCurve.CurveModel.algebraAdjoin AlgebraicCurve.CurveModel.isDedekindDomain_chartRing AlgebraicCurve.CurveModel.isIntegralClosure AlgebraicCurve.CurveModel.finite_chartRing AlgebraicCurve.CurveModel.centre_isPrime AlgebraicCurve.CurveModel.isFractionRing_chartRing AlgebraicCurve.CurveModel.finiteType_chartRing AlgebraicCurve.CurveModel.isNoetherianRing_chartRing AlgebraicCurve.CurveModel.isScalarTower_base_adjoin AlgebraicCurve.CurveModel.isScalarTower_adjoin AlgebraicCurve.CurveModel.chartRing_finitePresentation instTopologicallyFGOfFiniteType AlgebraicGeometry.ProjSpace.twistObj.addCommGroup AlgebraicGeometry.ProjSpace.twistFam.module AlgebraicGeometry.ProjSpace.twistObj.module AlgebraicGeometry.ProjSpace.twistObj.moduleSections AlgebraicGeometry.ProjSpace.twistFam.addCommGroup kmfloorsGlue_int_three_isPrime kmfloorsGlue_int_bot_isPrime"
p2m_attr_erase "simp" "GoodReductionJacobian.relativeGroupLawOfGrpObj_inv GoodReductionJacobian.relativeGroupLawOfGrpObj_mul GoodReductionJacobian.overHomEquivSchemeHomOver_apply_coe GoodReductionJacobian.relativeGroupLawOfGrpObj_one GoodReductionJacobian.overHomEquivSchemeHomOver_symm_apply_left SheafOfModules.tensorUnit_eq AlgebraicGeometry.Scheme.Modules.tensorUnit_eq PresheafOfModules.InternalHom.presheaf_map_apply PresheafOfModules.InternalHom.curryFamily_app PresheafOfModules.InternalHom.add_app PresheafOfModules.InternalHom.smul_app PresheafOfModules.InternalHom.zero_app PresheafOfModules.ihomObj_map_val PresheafOfModules.ihomFunctor_map PresheafOfModules.InternalHom.restrict_app PresheafOfModules.InternalHom.postcomp_app PresheafOfModules.InternalHom.neg_app PresheafOfModules.curry'_app_val PresheafOfModules.InternalHom.presheaf_obj PresheafOfModules.ihomFunctor_obj PresheafOfModules.ihomObj_obj PresheafOfModules.InternalHom.sub_app PresheafOfModules.ihomMap_app_val AlgebraicGeometry.Scheme.Modules.tensorPow_zero AlgebraicGeometry.Scheme.Modules.tensorPow_succ AlgebraicGeometry.RelPicard.RigidifiedLineBundle.mk.sizeOf_spec AlgebraicGeometry.RelPicard.RigidifiedLineBundle.mk.injEq AlgebraicGeometry.Scheme.OrderedAffineCover.mk.injEq AlgebraicGeometry.OModulePresheaf.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCover.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.mk.injEq AlgebraicGeometry.Scheme.TwoAffineOpenCover.mk.injEq AlgebraicGeometry.Scheme.TwoAffineOpenCover.mk.sizeOf_spec AlgebraicGeometry.Scheme.TwoAffineOpenCover.pullback_U1 AlgebraicGeometry.Scheme.TwoAffineOpenCover.pullback_U0 TwoChartCech.Sections.mk.injEq TwoChartCech.Cover.mk.injEq TwoChartCech.GrothendieckComplex.mk.injEq TwoChartCech.Sections.mk.sizeOf_spec TwoChartCech.Cover.mk.sizeOf_spec"
p2m_attr_erase "simp" "TwoChartCech.Cover.lineBundle_r0_apply TwoChartCech.GrothendieckComplex.mk.sizeOf_spec TwoChartCech.Cover.lineBundle_r1_apply CoherentBaseChange.TwoTermComplex.mk.sizeOf_spec CoherentBaseChange.TwoTermComplex.mk.injEq PresheafOfModules.freeεIso_hom_app PresheafOfModules.freeμIso_hom_app AlgebraicGeometry.RelPicard.RepresentsRelSubPic.mk.injEq AlgebraicGeometry.RelPicard.SubPicCondition.mk.injEq AlgebraicGeometry.RelPicard.SubPicCondition.mk.sizeOf_spec AlgebraicGeometry.RelPicard.RepresentsRelSubPic.mk.sizeOf_spec AlgebraicGeometry.SmoothProperCurve.sectionBaseChange_coe_snd AlgebraicGeometry.SmoothProperCurve.sectionBaseChange_coe_fst AlgebraicCurve.CurveModel.mk.injEq AlgebraicCurve.CurveModel.mk.sizeOf_spec AlgebraicCurve.mulAdele_apply AlgebraicCurve.residuePairing_apply_coe AlgebraicCurve.mem_adeleBdd AlgebraicCurve.weilSmul_one AlgebraicCurve.diagonalHom_apply AlgebraicCurve.weilSmul_apply AlgebraicCurve.adeleSpaceMul_coe AlgebraicCurve.mulAdele_one AlgebraicGeometry.SmoothProperCurve.FiniteMapData.twoAffineOpenCover_U1 AlgebraicGeometry.SmoothProperCurve.FiniteMapData.mk.injEq AlgebraicGeometry.SmoothProperCurve.FiniteMapData.mk.sizeOf_spec AlgebraicGeometry.SmoothProperCurve.FiniteMapData.twoAffineOpenCover_U0 AlgebraicGeometry.RelPicard.SubPicCondition.onClasses_mk AlgebraicGeometry.RelPicard.relSubPicPresheaf_map_coe CategoryTheory.Functor.OverTotal.ofFibre_fst CategoryTheory.Functor.overTotal_map_fst AlgebraicGeometry.Scheme.LocalRepresentabilityULift.glueData_J AlgebraicGeometry.Scheme.LocalRepresentabilityULift.uliftYoneda_toGlued_uliftYonedaGluedToSheaf AlgebraicGeometry.Scheme.LocalRepresentabilityULift.glueData_t' AlgebraicGeometry.Scheme.LocalRepresentabilityULift.uliftYoneda_toGlued_uliftYonedaGluedToSheaf_assoc AlgebraicGeometry.Scheme.LocalRepresentabilityULift.uliftYonedaGluedToSheaf_app_toGlued AlgebraicGeometry.Scheme.LocalRepresentabilityULift.glueData_openCover_map AlgebraicGeometry.Scheme.LocalRepresentabilityULift.uliftYonedaGluedToSheaf_app_comp AlgebraicGeometry.Scheme.LocalRepresentabilityULift.glueData_V AlgebraicGeometry.Scheme.LocalRepresentabilityULift.glueData_t"
p2m_attr_erase "simp" "AlgebraicGeometry.Scheme.LocalRepresentabilityULift.glueData_U AlgebraicGeometry.Scheme.LocalRepresentabilityULift.glueData_f AlgebraicGeometry.RelPicard.designationOfRepresentableBy_P AlgebraicGeometry.RelPicard.designationOfRepresentableBy_toBase AlgebraicGeometry.RelPicard.rigSection_snd AlgebraicGeometry.RelPicard.RigidifiedLineBundle.ofInvertible_L AlgebraicGeometry.RelPicard.rigSection_snd_assoc AlgebraicGeometry.RelPicard.SubPicGroupCondition.mk.injEq AlgebraicGeometry.RelPicard.SubPicGroupCondition.mk.sizeOf_spec AlgebraicCurve.coe_cechH0Equiv_apply AlgebraicCurve.cechH1ToH1_mk AlgebraicCurve.lSpaceOn_univ AlgebraicCurve.lSpaceOn_empty AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.Divisor.mapRestrict_single AlgebraicCurve.Divisor.pushforward_single AlgebraicCurve.Place.coe_restrictInclusion AlgebraicCurve.Place.mem_fiber AlgebraicCurve.Place.restrict_toValuationSubring AlgebraicCurve.Divisor.degree_pushforward AlgebraicCurve.Place.restrictResidueMap_residue AlgebraicCurve.Pic0.coe_pushforwardDegZeroHom AlgebraicCurve.Pic0.coe_pullbackDegZeroHom AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk"
p2m_attr_erase "simp" "ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Divisor.degree_pushforwardAlong AlgebraicCurve.Pic0.coe_degZeroCorrespondence AlgebraicCurve.Place.mem_fiberAlong AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.jqNModC_one ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one AlgebraicCurve.Place.differentialCoeff_zero AlgebraicCurve.Place.differentialCoeff_dCoord AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.injEq AlgebraicCurve.TranscendenceTower.mk.injEq AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec AlgebraicCurve.PoleDivisorPackage.mk.injEq AlgebraicGeometry.RelPicard.thetaBundle_def AlgebraicGeometry.RelPicard.picardBundle_def AlgebraicGeometry.RelEffCartierDiv.toRelEffDivisor_ofRelEffDivisor AlgebraicGeometry.RelEffCartierDiv.toRelEffDivisor_I"
p2m_attr_erase "simp" "AlgebraicGeometry.mapOnProdOver_fst_assoc AlgebraicGeometry.RelEffCartierDiv.mk.sizeOf_spec AlgebraicGeometry.RelEffCartierDiv.mk.injEq AlgebraicGeometry.mapOnProdOver_snd AlgebraicGeometry.mapOnProdOver_fst AlgebraicGeometry.mapOnProdOver_snd_assoc AlgebraicGeometry.mapOnProdOver_id AlgebraicCurve.RelEffDivisor.mk.sizeOf_spec AlgebraicCurve.mapOnProd_fst AlgebraicCurve.mapOnProd_fst_assoc AlgebraicCurve.mapOnProd_snd AlgebraicCurve.UnivDivisorPack.mk.injEq AlgebraicCurve.RelEffDivisor.mk.injEq AlgebraicCurve.UnivDivisorPack.mk.sizeOf_spec AlgebraicCurve.mapOnProd_snd_assoc AlgebraicGeometry.Scheme.Modules.exteriorPower_obj PresheafOfModules.exteriorPower_map_ιMulti PresheafOfModules.ExteriorPower.appₗ_apply AlgebraicGeometry.prodKerGraph_one AlgebraicGeometry.fibrePowOver.proj_comp AlgebraicGeometry.prodKerGraph_zero AlgebraicGeometry.RelEffCartierDiv.empty_I AlgebraicGeometry.fibrePowOver.proj_comp_assoc AlgebraicGeometry.graphOver_fst_assoc AlgebraicGeometry.RelEffCartierDiv.toPoint_comp AlgebraicGeometry.RelEffCartierDiv.toPoint_comp_assoc AlgebraicGeometry.graphOver_fst AlgebraicGeometry.RelEffCartierDiv.ofPoint_I AlgebraicGeometry.graphOver_snd AlgebraicGeometry.graphOver_snd_assoc AlgebraicCurve.SymmetricPowerPackage.mk.sizeOf_spec AlgebraicCurve.SymmetricPowerPackage.mk.injEq AlgebraicGeometry.FGSubalgebra.cocone_ι_app_apply AlgebraicGeometry.RelPicard.fst_toProdSpec AlgebraicGeometry.RelPicard.toProdSpec_fst_assoc AlgebraicGeometry.RelPicard.pointsSubBasepointModule_cons AlgebraicGeometry.RelPicard.pointsSubBasepointModule_nil AlgebraicGeometry.RelPicard.fst_toProdSpec_assoc AlgebraicGeometry.RelPicard.toProdSpec_fst AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.sub_app"
p2m_attr_erase "simp" "AlgebraicGeometry.Scheme.IdealSheafData.sres_sresTop AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.add_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.mk.sizeOf_spec AlgebraicGeometry.Scheme.IdealSheafData.coe_resLE AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.smul_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.coe_ofLE_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.ideal_range AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.zero_app AlgebraicGeometry.Scheme.IdealSheafData.sres_sres AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.comp_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.neg_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.id_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.coe_mulRight_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.nsmul_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.mk.injEq AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.zsmul_app AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.sizeOf_spec AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.injEq AlgebraicCurve.adeleSingle_coe AlgebraicCurve.kaehlerResidueTermKFam_apply AlgebraicCurve.Place.LocalResidueData.mk.injEq AlgebraicCurve.Place.LocalResidueData.mk.sizeOf_spec AlgebraicCurve.Place.kw_ffgc_adicCompletionComapIntegers_coe AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.sizeOf_spec AlgebraicCurve.Place.mem_simplePoleSubmodule AlgebraicCurve.Place.coe_uniformizerSubring ModularCurve.Lg37.Lg37CompletionSection.mk.injEq AlgebraicCurve.Place.CoefficientFieldSection.mk.injEq AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.injEq ModularCurve.Lg37.Lg37CompletionSection.mk.sizeOf_spec AlgebraicCurve.Place.CoefficientFieldSection.mk.sizeOf_spec AlgebraicCurve.Place.poleSubmodule_one AlgebraicCurve.Place.mem_poleSubmodule AlgebraicGeometry.Scheme.Modules.toUnitSection_ofUnitSection AlgebraicGeometry.Scheme.Modules.pullbackSection_def AlgebraicGeometry.Scheme.Modules.ofUnitSection_toUnitSection PresheafOfModules.InternalHom.IsSheafAux.appAt_toPresheafHom SheafOfModules.ihomSectionsEquivFamily_unit AlgebraicGeometry.Scheme.Modules.restrictHomEquivFamily_apply SheafOfModules.ihomEval_unit_app"
p2m_attr_erase "simp" "AlgebraicGeometry.Scheme.Modules.ihomEval_zero_right AlgebraicGeometry.Scheme.Modules.ihomEval_zero_left AlgebraicGeometry.Scheme.Modules.homOfFamily_app_apply SheafOfModules.unit_ihomSectionsEquivFamily AlgebraicGeometry.Scheme.Modules.familyOfHom_app AlgebraicGeometry.Scheme.Modules.restrictUnitIso_hom_app_apply AlgebraicGeometry.Scheme.Modules.restrictUnitIso_inv_app_apply AlgebraicGeometry.Scheme.Modules.restrictHomOfFamily_app_apply AlgebraicGeometry.Scheme.Modules.restrictHomEquivFamily_symm_apply AlgebraicGeometry.Scheme.Modules.tensorSections_zero_right AlgebraicGeometry.Scheme.Modules.map_unitSection AlgebraicGeometry.Scheme.Modules.tensorSectionsBilin_apply AlgebraicGeometry.Scheme.Modules.tensorPowSection_zero AlgebraicGeometry.Scheme.Modules.tensorSections_zero_left AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_neg AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_zero AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_sub AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_add AlgebraicGeometry.Scheme.OrderedAffineCover.toCoverOf_U AlgebraicGeometry.Scheme.OrderedAffineCoverOf.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCoverOf.mk.injEq AlgebraicGeometry.Scheme.OrderedAffineCover.restrict_U AlgebraicGeometry.OModulePresheaf.Hom.mk.injEq AlgebraicGeometry.OModulePresheaf.Hom.id_app AlgebraicGeometry.OModulePresheaf.AffHom.appSections_apply AlgebraicGeometry.OModulePresheaf.AffHom.comp_app AlgebraicGeometry.OModulePresheaf.AffSES.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.AffHom.kerMap_coe AlgebraicGeometry.OModulePresheaf.AffHom.id_app AlgebraicGeometry.OModulePresheaf.Hom.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.Hom.toAffHom_app AlgebraicGeometry.OModulePresheaf.SES.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.AffHom.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.Hom.comp_app AlgebraicGeometry.OModulePresheaf.SES.mk.injEq AlgebraicGeometry.OModulePresheaf.AffHom.mk.injEq AlgebraicGeometry.OModulePresheaf.Hom.appSections_apply AlgebraicGeometry.OModulePresheaf.AffSES.mk.injEq AlgebraicGeometry.OModulePresheaf.prod_obj AlgebraicGeometry.OModulePresheaf.restrOpen_obj"
p2m_attr_erase "simp" "AlgebraicGeometry.OModulePresheaf.DevissageStep.mk.injEq AlgebraicGeometry.OModulePresheaf.pushforward_obj AlgebraicGeometry.OModulePresheaf.im_obj AlgebraicGeometry.OModulePresheaf.pow_obj AlgebraicGeometry.OModulePresheaf.fstHom_app AlgebraicGeometry.OModulePresheaf.ker_obj AlgebraicGeometry.OModulePresheaf.coker_obj AlgebraicGeometry.OModulePresheaf.DevissageStep.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCover.preimage_U AlgebraicGeometry.OModulePresheaf.sndHom_app AlgebraicGeometry.OModulePresheaf.Leray.restrictToPreimage_U DoubleComplex.Bounded.mk.injEq DoubleComplex.Bounded.mk.sizeOf_spec DoubleComplex.Convergence.mk.injEq DoubleComplex.Convergence.mk.sizeOf_spec DoubleComplex.SubQuot.mk.sizeOf_spec DoubleComplex.SubQuot.mk.injEq AlgebraicGeometry.ChowDatumProj.mk.sizeOf_spec AlgebraicGeometry.ChowDatum.mk.sizeOf_spec AlgebraicGeometry.ChowDatumProj.mk.injEq AlgebraicGeometry.ChowDatum.mk.injEq ProjSpaceCech.GradedModule.mk.injEq ProjSpaceCech.GradedModule.mk.sizeOf_spec ProjSpaceCech.GradedModule.Frac.mk.sizeOf_spec ProjSpaceCech.GradedModule.Presentation.mk.injEq ProjSpaceCech.GradedModule.Frac.mk.injEq ProjSpaceCech.GradedModule.Presentation.mk.sizeOf_spec ProjSpaceCech.GradedModule.Hom.shift_toLinearMap ProjSpaceCech.GradedModule.Hom.mk.sizeOf_spec ProjSpaceCech.GradedModule.Hom.mk.injEq TwoChartCech.Mumford.dK_apply TwoChartCech.Mumford.ι0_apply TwoChartCech.Mumford.ι1_apply TwoChartCech.KerCoprod.dK_apply TwoChartCech.KerCoprod.ι1_apply TwoChartCech.KerCoprod.ι0_apply AlgebraicGeometry.tilde.functorCompPullbackSpecIso_app AlgebraicGeometry.RelPicard.algEquivZeroGroupCut_toSubPicCondition AlgebraicGeometry.RelPicard.LFP.stageHom_val AlgebraicGeometry.RelPicard.BaseChange.relSubPicPresheafRestrictIso_hom_app_coe"
p2m_attr_erase "simp" "AlgebraicGeometry.RelPicard.BaseChange.relSubPicPresheafRestrictIso_inv_app_coe AlgebraicGeometry.RelPicard.BaseChange.restrict_P AlgebraicGeometry.RelEffCartierDiv.IsUniversal.lift_comp AlgebraicGeometry.RelEffCartierDiv.functor_map_fst AlgebraicGeometry.RelEffCartierDiv.IsUniversal.homEquiv_apply AlgebraicGeometry.RelEffCartierDiv.IsUniversal.lift_pullbackAlong AlgebraicGeometry.RelEffCartierDiv.IsUniversal.homEquiv_symm_apply AlgebraicGeometry.RelEffCartierDiv.IsUniversal.lift_comp_assoc AlgebraicGeometry.RelEffCartierDiv.supportedIn_top AlgebraicGeometry.RelEffCartierDiv.mem_supportedIn_iff AlgebraicGeometry.RelEffCartierDiv.supportedIn_top_eq AlgebraicGeometry.RelEffCartierDiv.restrictAlong_extendAlong AlgebraicGeometry.RelEffCartierDiv.extendAlong_I AlgebraicGeometry.RelEffCartierDiv.resProdMap_snd AlgebraicGeometry.RelEffCartierDiv.restrictAlong_I AlgebraicGeometry.RelEffCartierDiv.extendAlong_restrictAlong AlgebraicGeometry.RelEffCartierDiv.resProdMap_fst_assoc AlgebraicGeometry.RelEffCartierDiv.resProdMap_snd_assoc AlgebraicGeometry.RelEffCartierDiv.resProdMap_fst CoherentBaseChange.FibreH0Family.mk.sizeOf_spec CoherentBaseChange.FibreH0Family.mk.injEq AlgebraicGeometry.Scheme.Modules.ProjPresentation.mk.injEq AlgebraicGeometry.Scheme.Modules.ProjPresentation.mk.sizeOf_spec AlgebraicCurve.CurveModel.coe_gInf AlgebraicCurve.CurveModel.coe_tInvChart AlgebraicCurve.CurveModel.ιInf_gluedToBase_assoc AlgebraicCurve.CurveModel.ιInf_gluedToBase AlgebraicCurve.CurveModel.primeOfι₀_asIdeal AlgebraicCurve.CurveModel.coe_tChart AlgebraicCurve.CurveModel.ι₀_gluedToBase_assoc AlgebraicCurve.CurveModel.primeOfιInf_asIdeal AlgebraicCurve.CurveModel.ι₀_gluedToBase AlgebraicCurve.CurveModel.coe_tma AlgebraicCurve.CurveModel.coe_primeEquivChartPlaces RegularLocalRingQuotientAscent.dualNumberFst_apply AlgebraicGeometry.ProjSpace.twistObj.mk.injEq AlgebraicGeometry.ProjSpace.twistObj.zero_val AlgebraicGeometry.ProjSpace.twistObj.add_val AlgebraicGeometry.ProjSpace.twist_res_val AlgebraicGeometry.ProjSpace.twist_smul_val"
p2m_attr_erase "simp" "AlgebraicGeometry.ProjSpace.twistGradeToObj_val AlgebraicGeometry.ProjSpace.twistObj.smul_val AlgebraicGeometry.ProjSpace.twistGradeEquiv_apply_val AlgebraicGeometry.ProjSpace.twistObj.mk.sizeOf_spec GoodReductionJacobian.RelativeGroupLaw.fibre_inv GoodReductionJacobian.RelativeGroupLaw.fibrePointToBase_coe GoodReductionJacobian.RelativeGroupLaw.fibrePointOfBase_toBase GoodReductionJacobian.RelativeGroupLaw.fibre_mul GoodReductionJacobian.RelativeGroupLaw.fibrePointToBase_ofBase GoodReductionJacobian.RelativeGroupLaw.fibre_one GoodReductionJacobian.RelativeGroupLaw.fibrePointOfBase_coe AlgebraicGeometry.schemeFibreEndo_snd AlgebraicGeometry.schemeFibreEndo_fst"

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry NeronModelInfra GoodReductionJacobian IsDedekindDomain AlgebraicCurve QuaternionAlgebra CerednikDrinfeld CerednikDrinfeld.QM
open scoped Quaternion TensorProduct NumberField

universe u

noncomputable section

namespace DegCM

variable {K : Type u} [Field K] {A : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of K)}

local infixl:80 " ⊚ " => NeronModelInfra.schemeHomOverComp

def IsHom (L : RelativeGroupLaw K f) (β : SchemeHomOver f f) : Prop :=
  ∀ (T : Scheme.{u}) (t : T ⟶ Spec (CommRingCat.of K)) (x y : SchemeHomOver t f),
    (L.mul t x y) ⊚ β = L.mul t (x ⊚ β) (y ⊚ β)

section Points

variable (L : RelativeGroupLaw K f)

theorem comp_assoc {T : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of K)} (z : SchemeHomOver t f) (β δ : SchemeHomOver f f) :
    (z ⊚ β) ⊚ δ = z ⊚ (β ⊚ δ) := Subtype.ext (Category.assoc _ _ _)

theorem comp_idPoint {T : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of K)} (z : SchemeHomOver t f) :
    z ⊚ (RelativeGroupLaw.idPoint : SchemeHomOver f f) = z := Subtype.ext (Category.comp_id _)

theorem idPoint_comp (β : SchemeHomOver f f) : (RelativeGroupLaw.idPoint : SchemeHomOver f f) ⊚ β = β :=
  Subtype.ext (Category.id_comp _)

theorem compT_mul {T : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of K)} (z : SchemeHomOver t f)
    (β δ : SchemeHomOver f f) :
    z ⊚ (L.mul f β δ) = L.mul t (z ⊚ β) (z ⊚ δ) := by
  have h := L.mul_natural f t z.1 z.2 β δ
  have e : ∀ δ : SchemeHomOver f f, GoodReductionJacobian.schemeHomOverComp z.1 z.2 δ = z ⊚ δ :=
    fun δ => Subtype.ext rfl
  rw [e, e, e] at h
  exact h

theorem compT_one {T : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of K)} (z : SchemeHomOver t f) :
    z ⊚ (L.one f) = L.one t := by
  have h := L.one_natural f t z.1 z.2
  have e : GoodReductionJacobian.schemeHomOverComp z.1 z.2 (L.one f) = z ⊚ (L.one f) := Subtype.ext rfl
  rw [e] at h
  exact h

def evalHom (hc : L.IsCommutative) {T : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of K)} (z : SchemeHomOver t f) :
    letI := L.pointCommGroup hc f; letI := L.pointCommGroup hc t; SchemeHomOver f f →* SchemeHomOver t f :=
  letI := L.pointCommGroup hc f; letI := L.pointCommGroup hc t
  { toFun := fun δ => z ⊚ δ
    map_one' := compT_one L z
    map_mul' := fun β δ => compT_mul L z β δ }

theorem compT_zpow (hc : L.IsCommutative) {T : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of K)} (z : SchemeHomOver t f)
    (β : SchemeHomOver f f) (n : ℤ) :
    letI := L.pointCommGroup hc f; letI := L.pointCommGroup hc t; z ⊚ (β ^ n) = (z ⊚ β) ^ n := by
  letI := L.pointCommGroup hc f; letI := L.pointCommGroup hc t
  exact map_zpow (evalHom L hc z) β n

def postHom (hc : L.IsCommutative) {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of K)) (β : SchemeHomOver f f)
    (hβ : IsHom L β) :
    letI := L.pointCommGroup hc t; SchemeHomOver t f →* SchemeHomOver t f :=
  letI := L.pointCommGroup hc t
  MonoidHom.mk' (fun x => x ⊚ β) (fun x y => hβ T t x y)

theorem zpow_postcomp (hc : L.IsCommutative) {T : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of K)} (x : SchemeHomOver t f)
    (β : SchemeHomOver f f) (hβ : IsHom L β) (n : ℤ) :
    letI := L.pointCommGroup hc t; (x ^ n) ⊚ β = (x ⊚ β) ^ n := by
  letI := L.pointCommGroup hc t
  exact map_zpow (postHom L hc t β hβ) x n

theorem mul_postcomp (hc : L.IsCommutative) {T : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of K)} (x y : SchemeHomOver t f)
    (β : SchemeHomOver f f) (hβ : IsHom L β) :
    letI := L.pointCommGroup hc t; (x * y) ⊚ β = (x ⊚ β) * (y ⊚ β) := hβ T t x y

theorem isHom_idPoint : IsHom L (RelativeGroupLaw.idPoint : SchemeHomOver f f) := by
  intro T t x y
  rw [comp_idPoint, comp_idPoint, comp_idPoint]

theorem key (hc : L.IsCommutative) (Φ : SchemeHomOver f f) (hΦ : IsHom L Φ) (t n : ℤ)
    (hrel : letI := L.pointCommGroup hc f;
      ((RelativeGroupLaw.idPoint : SchemeHomOver f f) ⊚ Φ) ⊚ Φ * (RelativeGroupLaw.idPoint : SchemeHomOver f f) ^ n =
        ((RelativeGroupLaw.idPoint : SchemeHomOver f f) ⊚ Φ) ^ t)
    (m : ℤ) :
    letI := L.pointCommGroup hc f;
    ((RelativeGroupLaw.idPoint : SchemeHomOver f f) ^ m * Φ) ⊚ ((RelativeGroupLaw.idPoint : SchemeHomOver f f) ^ (-m - t) * Φ) =
      (RelativeGroupLaw.idPoint : SchemeHomOver f f) ^ (-(m ^ 2 + t * m + n)) := by
  letI := L.pointCommGroup hc f
  set u : SchemeHomOver f f := RelativeGroupLaw.idPoint with hu
  rw [idPoint_comp] at hrel

  have hΦΦ : Φ ⊚ Φ = Φ ^ t * u ^ (-n) := by
    rw [← hrel, mul_assoc, ← zpow_add, add_neg_cancel, zpow_zero, mul_one]
  have e1 : (u ^ m * Φ) ⊚ (u ^ (-m - t) * Φ) = ((u ^ m * Φ) ⊚ (u ^ (-m - t))) * ((u ^ m * Φ) ⊚ Φ) :=
    compT_mul L _ _ _
  have e2 : (u ^ m * Φ) ⊚ (u ^ (-m - t)) = (u ^ m * Φ) ^ (-m - t) := by
    rw [compT_zpow L hc, hu, comp_idPoint]
  have e3 : (u ^ m * Φ) ⊚ Φ = Φ ^ m * (Φ ^ t * u ^ (-n)) := by
    rw [mul_postcomp L hc _ _ Φ hΦ, zpow_postcomp L hc _ Φ hΦ, hu, idPoint_comp, ← hu, hΦΦ]
  rw [e1, e2, e3, mul_zpow, ← zpow_mul]

  have : u ^ (m * (-m - t)) * Φ ^ (-m - t) * (Φ ^ m * (Φ ^ t * u ^ (-n))) =
      u ^ (m * (-m - t) + (-n)) * Φ ^ ((-m - t) + m + t) := by
    rw [zpow_add, zpow_add, zpow_add]; simp only [mul_assoc, mul_comm, mul_left_comm]
  rw [this, show (-m - t) + m + t = 0 by ring, zpow_zero, mul_one]
  congr 1; ring

theorem compT_inv' (hc : L.IsCommutative) {T : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of K)} (z : SchemeHomOver t f)
    (β : SchemeHomOver f f) :
    z ⊚ (L.inv f β) = L.inv t (z ⊚ β) := by
  letI := L.pointCommGroup hc f; letI := L.pointCommGroup hc t
  exact map_inv (evalHom L hc z) β

theorem compT_mul' (hc : L.IsCommutative) {T : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of K)} (z : SchemeHomOver t f)
    (β δ : SchemeHomOver f f) :
    letI := L.pointCommGroup hc f; letI := L.pointCommGroup hc t; z ⊚ (β * δ) = (z ⊚ β) * (z ⊚ δ) :=
  compT_mul L z β δ

theorem compT_one' (hc : L.IsCommutative) {T : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of K)} (z : SchemeHomOver t f) :
    letI := L.pointCommGroup hc f; letI := L.pointCommGroup hc t; z ⊚ (1 : SchemeHomOver f f) = 1 :=
  compT_one L z

def homSubgroup (hc : L.IsCommutative) : letI := L.pointCommGroup hc f; Subgroup (SchemeHomOver f f) :=
  letI := L.pointCommGroup hc f
  { carrier := {β | IsHom L β}
    mul_mem' := by
      intro β δ hβ hδ T t x y
      change (L.mul t x y) ⊚ (L.mul f β δ) = L.mul t (x ⊚ L.mul f β δ) (y ⊚ L.mul f β δ)
      rw [compT_mul, compT_mul, compT_mul, hβ, hδ]
      letI := L.pointCommGroup hc t
      change (x ⊚ β * (y ⊚ β)) * (x ⊚ δ * (y ⊚ δ)) = (x ⊚ β * (x ⊚ δ)) * (y ⊚ β * (y ⊚ δ))
      exact mul_mul_mul_comm _ _ _ _
    one_mem' := by
      intro T t x y
      change (L.mul t x y) ⊚ (L.one f) = L.mul t (x ⊚ L.one f) (y ⊚ L.one f)
      rw [compT_one, compT_one, compT_one, L.one_mul]
    inv_mem' := by
      intro β hβ T t x y
      change (L.mul t x y) ⊚ (L.inv f β) = L.mul t (x ⊚ L.inv f β) (y ⊚ L.inv f β)
      letI := L.pointCommGroup hc t
      rw [compT_inv' L hc, compT_inv' L hc, compT_inv' L hc, hβ]
      change (x ⊚ β * (y ⊚ β))⁻¹ = (x ⊚ β)⁻¹ * (y ⊚ β)⁻¹
      rw [mul_inv] }

theorem isHom_zpow_mul (hc : L.IsCommutative) {α β : SchemeHomOver f f} (hα : IsHom L α) (hβ : IsHom L β) (n : ℤ) :
    letI := L.pointCommGroup hc f; IsHom L (α ^ n * β) := by
  letI := L.pointCommGroup hc f
  exact (homSubgroup L hc).mul_mem ((homSubgroup L hc).zpow_mem (show α ∈ homSubgroup L hc from hα) n) hβ

theorem nsmul_eq_pow (hc : L.IsCommutative) {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of K)) (n : ℕ) (x : SchemeHomOver t f) :
    letI := L.pointCommGroup hc t; L.nsmul t n x = x ^ n := by
  letI := L.pointCommGroup hc t
  induction n with
  | zero => rw [RelativeGroupLaw.nsmul_zero, pow_zero]; rfl
  | succ n ih => rw [RelativeGroupLaw.nsmul_succ, pow_succ, ih]; rfl

end Points

section Alg

p2m_open "Polynomial AlgebraicGeometry.Polynomial"

theorem eval_zero_eq_of_mul_comp_eq (t n : ℤ) (htn : t ^ 2 < 4 * n) (P : ℚ[X])
    (hP : P * P.comp (-X - C (t : ℚ)) = (X ^ 2 + C (t : ℚ) * X + C (n : ℚ)) ^ 4)
    (hpos : 0 < P.eval 0) : P.eval 0 = (n : ℚ) ^ 2 := by
  classical
  set q : ℚ[X] := X ^ 2 + C (t : ℚ) * X + C (n : ℚ) with hq
  have hqmonic : q.Monic := by rw [hq]; monicity!
  have hqdeg : q.natDegree = 2 := by rw [hq]; compute_degree!
  have hqeval : ∀ x : ℚ, q.eval x = x ^ 2 + t * x + n := by intro x; simp [hq]
  have hqirr : Irreducible q := by
    rw [hqmonic.irreducible_iff_roots_eq_zero_of_degree_le_three (by rw [hqdeg]) (by rw [hqdeg]; norm_num),
      Multiset.eq_zero_iff_forall_notMem]
    intro x hx
    rw [mem_roots hqmonic.ne_zero, IsRoot, hqeval] at hx
    have h4 : ((t : ℚ)) ^ 2 < 4 * n := by exact_mod_cast htn
    nlinarith [sq_nonneg (2 * x + t)]
  have hqprime : Prime q := hqirr.prime
  have hq0 : q ≠ 0 := hqmonic.ne_zero

  have hqcomp : q.comp (-X - C (t : ℚ)) = q := by
    rw [hq, Polynomial.add_comp, Polynomial.add_comp, Polynomial.pow_comp, Polynomial.X_comp, Polynomial.mul_comp,
      Polynomial.C_comp, Polynomial.X_comp, Polynomial.C_comp]
    ring

  have hdvd : P ∣ q ^ 4 := ⟨_, hP.symm⟩
  obtain ⟨i, hi, u, hu⟩ := (dvd_prime_pow hqprime 4).mp hdvd

  obtain ⟨c, hcunit, hc⟩ := Polynomial.isUnit_iff.mp u.isUnit
  have hc0 : c ≠ 0 := hcunit.ne_zero
  have hPq : P = C c⁻¹ * q ^ i := by
    have : P * C c = q ^ i := by rw [hc]; exact hu
    calc P = P * C c * C c⁻¹ := by rw [mul_assoc, ← C_mul, mul_inv_cancel₀ hc0, C_1, mul_one]
      _ = C c⁻¹ * q ^ i := by rw [this, mul_comm]
  set d : ℚ := c⁻¹ with hd
  have hd0 : d ≠ 0 := inv_ne_zero hc0

  have hcompP : P.comp (-X - C (t : ℚ)) = C d * q ^ i := by
    rw [hPq, Polynomial.mul_comp, Polynomial.C_comp, Polynomial.pow_comp, hqcomp]
  have hprod : C (d * d) * q ^ (2 * i) = q ^ 4 := by
    rw [← hP, hcompP, hPq]; rw [C_mul]; ring
  have hi2 : i = 2 := by
    have := congrArg natDegree hprod
    rw [natDegree_C_mul (mul_ne_zero hd0 hd0), natDegree_pow, natDegree_pow, hqdeg] at this
    omega
  have hdd : d * d = 1 := by
    rw [hi2, show 2 * 2 = 4 from rfl] at hprod
    have : C (d * d) = (1 : ℚ[X]) := by
      have h := mul_right_cancel₀ (pow_ne_zero 4 hq0) (hprod.trans (one_mul _).symm)
      exact h
    have := congrArg (fun p : ℚ[X] => p.eval 0) this
    simpa using this
  have hP0 : P.eval 0 = d * (n : ℚ) ^ 2 := by
    rw [hPq, hi2, eval_mul, eval_C, eval_pow, hqeval]; ring
  rcases mul_self_eq_one_iff.mp hdd with h1 | h1
  · rw [hP0, h1, one_mul]
  · exfalso
    rw [hP0, h1] at hpos
    nlinarith [sq_nonneg (n : ℚ)]

end Alg

end DegCM

end

open _root_.Polynomial _root_.AlgebraicGeometry.Polynomial DegCM in
theorem solution
    {q q' : ℕ} [Fact q.Prime] [Fact q'.Prime] (hqq' : q' ≠ q)
    {a b : ℚ} (hB : IsIndefiniteRamifiedExactlyAt a b q q')
    (Λ : Submodule ℤ ℍ[ℚ, a, b]) (hΛ : IsMaximalOrder Λ) {N : ℕ}
    (k : Type u) [Field k] [IsAlgClosed k] [CharZero k] (E : FakeEllipticCurve Λ N k)
    (t n : ℤ) (htn : t ^ 2 < 4 * n)
    (φ : E.A ⟶ E.A) (hφ : φ ≫ E.f = E.f)
    (hadd : ∀ {T : Scheme.{u}} (s : T ⟶ Spec (CommRingCat.of k)) (P Q : SchemeHomOver s E.f),
      mapPt φ hφ (E.L.mul s P Q) = E.L.mul s (mapPt φ hφ P) (mapPt φ hφ Q))
    (hlin : ∀ x : ↥Λ, E.act x ≫ φ = φ ≫ E.act x)
    (hrel : ∀ {T : Scheme.{u}} (s : T ⟶ Spec (CommRingCat.of k)) (P : SchemeHomOver s E.f),
      letI := E.L.pointCommGroup E.comm s
      mapPt φ hφ (mapPt φ hφ P) * P ^ n = mapPt φ hφ P ^ t) :
    E.L.endDegree ⟨φ, hφ⟩ = n.natAbs ^ 2 := by
  classical
  letI instG := E.L.pointCommGroup E.comm E.f
  haveI : SmoothOfRelativeDimension 2 E.f := CerednikDrinfeld.QM.FakeEllipticCurve.smoothOfRelativeDimension_two k E
  set Φ : SchemeHomOver E.f E.f := ⟨φ, hφ⟩ with hΦdef
  set u : SchemeHomOver E.f E.f := RelativeGroupLaw.idPoint with hu

  have hmapPt : ∀ {T : Scheme.{u}} {s : T ⟶ Spec (CommRingCat.of k)} (P : SchemeHomOver s E.f),
      mapPt φ hφ P = NeronModelInfra.schemeHomOverComp P Φ := fun P => rfl
  have hΦ : IsHom E.L Φ := fun T s x y => by rw [← hmapPt, ← hmapPt, ← hmapPt]; exact hadd s x y
  have hu' : IsHom E.L u := isHom_idPoint E.L

  have hrelU : NeronModelInfra.schemeHomOverComp (NeronModelInfra.schemeHomOverComp u Φ) Φ * u ^ n =
      (NeronModelInfra.schemeHomOverComp u Φ) ^ t := by
    have := hrel E.f u
    rw [hmapPt, hmapPt] at this
    exact this

  have hn0 : n ≠ 0 := by rintro rfl; nlinarith [sq_nonneg t]

  obtain ⟨P, hPdeg, hP⟩ := GoodReductionJacobian.RelativeGroupLaw.exists_polynomial_eval_eq_endDegree_zpow_mul_of_abelianSchemePropertyBundle
    k E.f E.L E.comm E.bundle 2 u Φ (fun s x y => hu' _ s x y) (fun s x y => hΦ _ s x y)
  obtain ⟨P₀, hP₀deg, hP₀⟩ := GoodReductionJacobian.RelativeGroupLaw.exists_polynomial_eval_eq_endDegree_zpow_mul_of_abelianSchemePropertyBundle
    k E.f E.L E.comm E.bundle 2 u 1 (fun s x y => hu' _ s x y) (fun s x y => (homSubgroup E.L E.comm).one_mem _ s x y)

  have hP₀X : P₀ = Polynomial.X ^ 4 := by
    apply Polynomial.eq_of_degree_sub_lt_of_eval_finset_eq (Finset.image (fun j : ℕ => ((j : ℚ))) (Finset.Icc 1 5))
    · have hcard : (Finset.image (fun j : ℕ => ((j : ℚ))) (Finset.Icc 1 5)).card = 5 := by
        rw [Finset.card_image_of_injective _ Nat.cast_injective]; rfl
      rw [hcard]
      refine lt_of_le_of_lt (Polynomial.degree_sub_le _ _) ?_
      refine max_lt ?_ (by rw [Polynomial.degree_X_pow]; exact_mod_cast Nat.lt_succ_self 4)
      exact lt_of_le_of_lt (Polynomial.degree_le_natDegree) (by exact_mod_cast Nat.lt_succ_of_le hP₀deg)
    · intro x hx
      obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hx
      have hjpos : 0 < j := by rw [Finset.mem_Icc] at hj; omega
      rw [Polynomial.eval_pow, Polynomial.eval_X, show ((j : ℕ) : ℚ) = ((j : ℤ) : ℚ) by simp, ← hP₀ j]
      have e1 : u ^ (j : ℤ) * 1 = E.L.nsmul E.f j u := by rw [mul_one, zpow_natCast, nsmul_eq_pow E.L E.comm]
      rw [e1, GoodReductionJacobian.RelativeGroupLaw.endDegree_nsmul_idPoint_eq_pow k E.f E.L E.comm E.bundle 2 j hjpos]
      push_cast; ring
  have hdegU : ∀ z : ℤ, ((E.L.endDegree (u ^ z) : ℕ) : ℚ) = (z : ℚ) ^ 4 := by
    intro z; have := hP₀ z; rw [mul_one, hP₀X, Polynomial.eval_pow, Polynomial.eval_X] at this; exact this

  have hne : ∀ m : ℤ, E.L.endDegree (u ^ m * Φ) ≠ 0 := by
    intro m
    set w : SchemeHomOver E.f E.f := u ^ m * Φ with hw
    have hwhom : IsHom E.L w := isHom_zpow_mul E.L E.comm hu' hΦ m
    have hw' : (⟨w.1, w.2⟩ : SchemeHomOver E.f E.f) = w := rfl
    rw [← hw']
    refine CerednikDrinfeld.QM.FakeEllipticCurve.endDegree_ne_zero_of_forall_act_comp_eq_of_ne_one hqq' hB Λ hΛ k E w.1 w.2
      (fun s P Q => hwhom _ s P Q) ?_ ?_
    ·
      intro x
      let ax : SchemeHomOver E.f E.f := ⟨E.act x, E.act_over x⟩
      have hax : IsHom E.L ax := fun T s P Q => E.act_hom x s P Q
      have hcomm : NeronModelInfra.schemeHomOverComp ax Φ = NeronModelInfra.schemeHomOverComp Φ ax := Subtype.ext (hlin x)
      have : NeronModelInfra.schemeHomOverComp ax w = NeronModelInfra.schemeHomOverComp w ax := by
        rw [hw, compT_mul' E.L E.comm, compT_zpow E.L E.comm, comp_idPoint, mul_postcomp E.L E.comm _ _ ax hax, zpow_postcomp E.L E.comm _ ax hax,
          idPoint_comp, hcomm]
      exact congrArg Subtype.val this
    ·
      intro hw1
      have hw1' : w = E.L.one E.f := hw1
      set N₀ : ℤ := m ^ 2 + t * m + n with hN₀
      have hN₀pos : 0 < N₀ := by rw [hN₀]; nlinarith [sq_nonneg (2 * m + t), sq_nonneg t]

      letI inst1 := E.L.pointCommGroup E.comm (𝟙 (Spec (CommRingCat.of k)))
      have htors : ∀ P : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) E.f, P ^ N₀ = 1 := by
        intro P
        have h1 : NeronModelInfra.schemeHomOverComp P w = 1 := by rw [hw1']; exact compT_one' E.L E.comm P
        rw [hw, compT_mul' E.L E.comm, compT_zpow E.L E.comm, comp_idPoint] at h1

        have hPΦ : NeronModelInfra.schemeHomOverComp P Φ = P ^ (-m) := by
          rw [zpow_neg]; exact eq_inv_of_mul_eq_one_right h1
        have h2 := hrel (𝟙 _) P
        rw [hmapPt, hmapPt, hPΦ, zpow_postcomp E.L E.comm _ Φ hΦ, hPΦ, ← zpow_mul, ← zpow_add, ← zpow_mul] at h2
        have : P ^ (-m * -m + n - (-m * t)) = 1 := by rw [zpow_sub, h2, mul_inv_cancel]
        rw [hN₀, show m ^ 2 + t * m + n = -m * -m + n - (-m * t) by ring]
        exact this

      obtain ⟨ℓ, hℓN, hℓp⟩ := Nat.exists_infinite_primes (N₀.toNat + 1)
      haveI : Fact ℓ.Prime := ⟨hℓp⟩
      have hℓk : ((ℓ : ℕ) : k) ≠ 0 := by exact_mod_cast hℓp.ne_zero
      have hcount := GoodReductionJacobian.RelativeGroupLaw.natCard_isTorsionPoint_eq_pow_of_natCast_ne_zero k E.f E.L E.comm E.bundle 2 ℓ hℓk
      have hall : ∀ P : {x : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) E.f // E.L.IsTorsionPoint (𝟙 (Spec (CommRingCat.of k))) ℓ x},
          P = ⟨1, by rw [GoodReductionJacobian.RelativeGroupLaw.isTorsionPoint_def, nsmul_eq_pow E.L E.comm, one_pow]; rfl⟩ := by
        intro P
        apply Subtype.ext
        have hPℓ : (P.1) ^ (ℓ : ℕ) = 1 := by
          have := P.2; rw [GoodReductionJacobian.RelativeGroupLaw.isTorsionPoint_def, nsmul_eq_pow E.L E.comm] at this; exact this
        have hPN : (P.1) ^ N₀.toNat = 1 := by
          have := htors P.1; rwa [← Int.toNat_of_nonneg hN₀pos.le, zpow_natCast] at this
        have hcop : Nat.Coprime ℓ N₀.toNat := by
          rw [Nat.Prime.coprime_iff_not_dvd hℓp]
          intro hdvd
          have := Nat.le_of_dvd (by omega) hdvd
          omega
        have h1 := orderOf_dvd_of_pow_eq_one hPℓ
        have h2 := orderOf_dvd_of_pow_eq_one hPN
        have : orderOf P.1 ∣ 1 := by rw [← hcop.gcd_eq_one]; exact Nat.dvd_gcd h1 h2
        exact orderOf_eq_one_iff.mp (Nat.dvd_one.mp this)
      have hsub : Subsingleton {x : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) E.f // E.L.IsTorsionPoint (𝟙 (Spec (CommRingCat.of k))) ℓ x} :=
        ⟨fun a b => by rw [hall a, hall b]⟩
      have hle : Nat.card {x : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) E.f // E.L.IsTorsionPoint (𝟙 (Spec (CommRingCat.of k))) ℓ x} ≤ 1 := by
        haveI := hsub
        haveI : Finite {x : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) E.f // E.L.IsTorsionPoint (𝟙 (Spec (CommRingCat.of k))) ℓ x} :=
          Finite.of_subsingleton
        exact Finite.card_le_one_iff_subsingleton.mpr hsub
      rw [hcount] at hle
      have : 2 ^ (2 * 2) ≤ ℓ ^ (2 * 2) := Nat.pow_le_pow_left hℓp.two_le _
      omega

  have hprodZ : ∀ m : ℤ, P.eval (m : ℚ) * P.eval ((-m - t : ℤ) : ℚ) = ((m : ℚ) ^ 2 + t * m + n) ^ 4 := by
    intro m
    rw [← hP m, ← hP (-m - t), ← Nat.cast_mul,
      ← GoodReductionJacobian.RelativeGroupLaw.endDegree_schemeHomOverComp_eq_mul_of_ne_zero k E.f E.L E.comm E.bundle 2 _ _
        (fun s x y => isHom_zpow_mul E.L E.comm hu' hΦ m _ s x y) (fun s x y => isHom_zpow_mul E.L E.comm hu' hΦ (-m - t) _ s x y)
        (hne m) (hne (-m - t)),
      key E.L E.comm Φ hΦ t n hrelU m, hdegU]
    push_cast; ring

  have hpoly : P * P.comp (-Polynomial.X - Polynomial.C (t : ℚ)) =
      (Polynomial.X ^ 2 + Polynomial.C (t : ℚ) * Polynomial.X + Polynomial.C (n : ℚ)) ^ 4 := by
    apply Polynomial.eq_of_infinite_eval_eq
    apply Set.Infinite.mono (s := Set.range (fun m : ℤ => (m : ℚ)))
    · rintro x ⟨m, rfl⟩
      show Polynomial.eval (m : ℚ) (P * P.comp (-Polynomial.X - Polynomial.C (t : ℚ))) =
        Polynomial.eval (m : ℚ) ((Polynomial.X ^ 2 + Polynomial.C (t : ℚ) * Polynomial.X + Polynomial.C (n : ℚ)) ^ 4)
      rw [Polynomial.eval_mul, Polynomial.eval_comp, Polynomial.eval_sub, Polynomial.eval_neg, Polynomial.eval_X, Polynomial.eval_C,
        show (-(m : ℚ) - t) = ((-m - t : ℤ) : ℚ) by push_cast; ring, hprodZ m]
      simp
    · exact Set.infinite_range_of_injective Int.cast_injective
  have hpos : 0 < P.eval 0 := by
    have := hP 0
    rw [zpow_zero, one_mul, Int.cast_zero] at this
    rw [← this]
    exact_mod_cast Nat.pos_of_ne_zero (by have := hne 0; rwa [zpow_zero, one_mul] at this)
  have h0 := eval_zero_eq_of_mul_comp_eq t n htn P hpoly hpos

  have hfin : ((E.L.endDegree Φ : ℕ) : ℚ) = (n : ℚ) ^ 2 := by
    have := hP 0; rw [zpow_zero, one_mul, Int.cast_zero] at this; rw [this, h0]
  have : ((E.L.endDegree Φ : ℕ) : ℚ) = ((n.natAbs ^ 2 : ℕ) : ℚ) := by
    rw [hfin]; push_cast; rw [Nat.cast_natAbs, Int.cast_abs, sq_abs]
  exact_mod_cast this

end S_CerednikDrinfeld_QM_FakeEllipticCurve_endDegree_eq_natAbs_sq_of_mapPt_mapPt_mul_zpow_eq_zpow
end P2MW
export P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_endDegree_eq_natAbs_sq_of_mapPt_mapPt_mul_zpow_eq_zpow (solution)
