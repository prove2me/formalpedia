-- Prove2me | solution 1 for CerednikDrinfeld.QM.FakeEllipticCurve.iso_of_quotient_ker_of_mapPt_mapPt_mul_zpow_eq_zpow
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.141142+00:00
-- url     : https://prove2.me/submissions/71e77403-a70d-5b7f-8fc6-47d01dbb171f

import Definitions.Def_CerednikDrinfeld_QMModuliProps
import Definitions.Def_AlgebraicGeometry_RelativeGroupLawEndDegree
import Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_existsUnique_comp_eq_of_forall_mapPt_eq_one_of_flat_of_surjective
import Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_isIso_of_forall_mapPt_eq_one_imp_eq_one
import Theorems.Thm_CerednikDrinfeld_QM_exists_comp_eq_of_forall_factorsThrough_of_isReduced
import Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_pushPt_act_natCast_eq_nsmulPt
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_iso_of_quotient_ker_of_mapPt_mapPt_mul_zpow_eq_zpow
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

open scoped Quaternion
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry CerednikDrinfeld CerednikDrinfeld.QM QuaternionAlgebra NeronModelInfra GoodReductionJacobian

namespace LASTISO

variable {R : Type} [CommRing R]

theorem mapPt_comp {A A' A'' : Scheme.{0}} {f : A ⟶ Spec (CommRingCat.of R)} {f' : A' ⟶ Spec (CommRingCat.of R)}
    {f'' : A'' ⟶ Spec (CommRingCat.of R)} (φ : A ⟶ A') (hφ : φ ≫ f' = f) (ψ : A' ⟶ A'') (hψ : ψ ≫ f'' = f')
    {h : (φ ≫ ψ) ≫ f'' = f} {T : Scheme.{0}} {t : T ⟶ Spec (CommRingCat.of R)} (P : SchemeHomOver t f) :
    mapPt (φ ≫ ψ) h P = mapPt ψ hψ (mapPt φ hφ P) := by
  apply Subtype.ext; simp [mapPt, Category.assoc]

theorem mapPt_id {A : Scheme.{0}} {f : A ⟶ Spec (CommRingCat.of R)} {h : 𝟙 A ≫ f = f}
    {T : Scheme.{0}} {t : T ⟶ Spec (CommRingCat.of R)} (P : SchemeHomOver t f) : mapPt (𝟙 A) h P = P := by
  apply Subtype.ext; simp [mapPt]

theorem eq_of_mapPt_id_eq {A A' : Scheme.{0}} {f : A ⟶ Spec (CommRingCat.of R)} {f' : A' ⟶ Spec (CommRingCat.of R)}
    {φ ψ : A ⟶ A'} {hφ : φ ≫ f' = f} {hψ : ψ ≫ f' = f}
    (h : mapPt φ hφ (⟨𝟙 A, Category.id_comp f⟩ : SchemeHomOver f f) = mapPt ψ hψ ⟨𝟙 A, Category.id_comp f⟩) : φ = ψ := by
  have := congrArg Subtype.val h
  simpa [mapPt] using this

def IsHom {X Y : Scheme.{0}} {gX : X ⟶ Spec (CommRingCat.of R)} {gY : Y ⟶ Spec (CommRingCat.of R)}
    (LX : RelativeGroupLaw R gX) (LY : RelativeGroupLaw R gY) (α : X ⟶ Y) (hα : α ≫ gY = gX) : Prop :=
  ∀ ⦃T : Scheme.{0}⦄ (t : T ⟶ Spec (CommRingCat.of R)) (u v : SchemeHomOver t gX),
    mapPt α hα (LX.mul t u v) = LY.mul t (mapPt α hα u) (mapPt α hα v)

theorem IsHom.comp {X Y Z : Scheme.{0}} {gX : X ⟶ Spec (CommRingCat.of R)} {gY : Y ⟶ Spec (CommRingCat.of R)}
    {gZ : Z ⟶ Spec (CommRingCat.of R)} {LX : RelativeGroupLaw R gX} {LY : RelativeGroupLaw R gY} {LZ : RelativeGroupLaw R gZ}
    {α : X ⟶ Y} {hα : α ≫ gY = gX} {β : Y ⟶ Z} {hβ : β ≫ gZ = gY} (h₁ : IsHom LX LY α hα) (h₂ : IsHom LY LZ β hβ)
    {h : (α ≫ β) ≫ gZ = gX} : IsHom LX LZ (α ≫ β) h := by
  intro T t u v
  rw [mapPt_comp α hα β hβ, h₁, h₂, ← mapPt_comp α hα β hβ, ← mapPt_comp α hα β hβ]

theorem IsHom.map_one {X Y : Scheme.{0}} {gX : X ⟶ Spec (CommRingCat.of R)} {gY : Y ⟶ Spec (CommRingCat.of R)}
    {LX : RelativeGroupLaw R gX} {LY : RelativeGroupLaw R gY} {α : X ⟶ Y} {hα : α ≫ gY = gX} (h : IsHom LX LY α hα)
    {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of R)) : mapPt α hα (LX.one t) = LY.one t := by
  have h' := h t (LX.one t) (LX.one t)
  rw [LX.one_mul] at h'
  have := congrArg (LY.mul t (LY.inv t (mapPt α hα (LX.one t)))) h'
  rw [← LY.mul_assoc, LY.inv_mul_cancel, LY.one_mul] at this
  exact this.symm

theorem IsHom.map_inv {X Y : Scheme.{0}} {gX : X ⟶ Spec (CommRingCat.of R)} {gY : Y ⟶ Spec (CommRingCat.of R)}
    {LX : RelativeGroupLaw R gX} {LY : RelativeGroupLaw R gY} {α : X ⟶ Y} {hα : α ≫ gY = gX} (h : IsHom LX LY α hα)
    {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of R)) (P : SchemeHomOver t gX) :
    mapPt α hα (LX.inv t P) = LY.inv t (mapPt α hα P) := by
  letI := LY.pointGroup t
  have h' := h t (LX.inv t P) P
  rw [LX.inv_mul_cancel, h.map_one] at h'
  exact (inv_eq_of_mul_eq_one_left h'.symm).symm

theorem IsHom.map_nsmulPt {X Y : Scheme.{0}} {gX : X ⟶ Spec (CommRingCat.of R)} {gY : Y ⟶ Spec (CommRingCat.of R)}
    {LX : RelativeGroupLaw R gX} {LY : RelativeGroupLaw R gY} {α : X ⟶ Y} {hα : α ≫ gY = gX} (h : IsHom LX LY α hα)
    {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of R)) (n : ℕ) (P : SchemeHomOver t gX) :
    mapPt α hα (nsmulPt LX t n P) = nsmulPt LY t n (mapPt α hα P) := by
  induction n with
  | zero => exact h.map_one t
  | succ n ih => simp only [nsmulPt]; rw [h, ih]

theorem mapPt_iso_eq_iff {X Y : Scheme.{0}} {gX : X ⟶ Spec (CommRingCat.of R)} {gY : Y ⟶ Spec (CommRingCat.of R)}
    (e : X ≅ Y) (he : e.hom ≫ gY = gX) {T : Scheme.{0}} {t : T ⟶ Spec (CommRingCat.of R)} (P Q : SchemeHomOver t gX) :
    mapPt e.hom he P = mapPt e.hom he Q ↔ P = Q := by
  constructor
  · intro h
    have := congrArg (fun S : SchemeHomOver t gY => S.1 ≫ e.inv) h
    simp only [mapPt, Category.assoc, e.hom_inv_id, Category.comp_id] at this
    exact Subtype.ext this
  · rintro rfl; rfl

theorem inv_unique {A : Scheme.{0}} {f : A ⟶ Spec (CommRingCat.of R)} (L : RelativeGroupLaw R f)
    {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of R)) (x y : SchemeHomOver t f) (h : L.mul t y x = L.one t) :
    y = L.inv t x := by
  have := congrArg (fun z => L.mul t z (L.inv t x)) h
  rw [L.mul_assoc, L.mul_inv_cancel, L.mul_one, L.one_mul] at this
  exact this

theorem mapPt_invHom {A : Scheme.{0}} {f : A ⟶ Spec (CommRingCat.of R)} (L : RelativeGroupLaw R f)
    {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of R)) (P : SchemeHomOver t f) :
    mapPt (L.inv f ⟨𝟙 A, Category.id_comp f⟩).1 (L.inv f ⟨𝟙 A, Category.id_comp f⟩).2 P = L.inv t P := by
  apply inv_unique
  have hn := L.mul_natural f t P.1 P.2 (L.inv f ⟨𝟙 A, Category.id_comp f⟩) ⟨𝟙 A, Category.id_comp f⟩
  rw [L.inv_mul_cancel, L.one_natural] at hn
  have e1 : GoodReductionJacobian.schemeHomOverComp P.1 P.2 (L.inv f ⟨𝟙 A, Category.id_comp f⟩) =
      mapPt (L.inv f ⟨𝟙 A, Category.id_comp f⟩).1 (L.inv f ⟨𝟙 A, Category.id_comp f⟩).2 P := by
    apply Subtype.ext; rfl
  have e2 : GoodReductionJacobian.schemeHomOverComp P.1 P.2 (⟨𝟙 A, Category.id_comp f⟩ : SchemeHomOver f f) = P := by
    apply Subtype.ext; show P.1 ≫ 𝟙 A = P.1; exact Category.comp_id _
  rw [e1, e2] at hn
  exact hn.symm

theorem factorsThrough_lev_iff_eq_one {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} {S : Type} [CommRing S]
    (X : FakeEllipticCurve Λ 1 S) {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of S)) (Q : SchemeHomOver t X.f) :
    FactorsThrough X.lev Q ↔ Q = X.L.one t := by
  haveI := X.lev_finite; haveI := X.lev_flat; haveI := X.lev_finitePresentation
  haveI : IsIso (X.lev ≫ X.f) := by
    rw [Scheme.Hom.isIso_iff_finrank_eq]
    funext s; rw [X.lev_rank s]; simp
  constructor
  · rintro ⟨c, hc⟩
    obtain ⟨c₁, hc₁⟩ := X.lev_one t
    have hcg : ∀ (d : T ⟶ X.C), d ≫ X.lev ≫ X.f = t → d = t ≫ inv (X.lev ≫ X.f) := by
      intro d hd; rw [← hd, Category.assoc, IsIso.hom_inv_id, Category.comp_id]
    have h1 : c = t ≫ inv (X.lev ≫ X.f) := hcg c (by rw [← Category.assoc, hc]; exact Q.2)
    have h2 : c₁ = t ≫ inv (X.lev ≫ X.f) := hcg c₁ (by rw [← Category.assoc, hc₁]; exact (X.L.one t).2)
    apply Subtype.ext
    rw [← hc, ← hc₁, h1, h2]
  · rintro rfl; exact X.lev_one t

end LASTISO

theorem solution
    {q q' : ℕ} [Fact q.Prime] [Fact q'.Prime] (hqq' : q' ≠ q)
    {a b : ℚ} (hB : IsIndefiniteRamifiedExactlyAt a b q q')
    (Λ : Submodule ℤ ℍ[ℚ, a, b]) (hΛ : IsMaximalOrder Λ)
    (E : FakeEllipticCurve Λ 1 (AlgebraicClosure ℚ))
    (t n : ℤ) (htn : t ^ 2 < 4 * n)
    (φ : E.A ⟶ E.A) (hφ : φ ≫ E.f = E.f)
    (hadd : ∀ {T : Scheme.{0}} (s : T ⟶ Spec (CommRingCat.of (AlgebraicClosure ℚ))) (P Q : SchemeHomOver s E.f),
      mapPt φ hφ (E.L.mul s P Q) = E.L.mul s (mapPt φ hφ P) (mapPt φ hφ Q))
    (hlin : ∀ x : ↥Λ, E.act x ≫ φ = φ ≫ E.act x)
    (hrel : ∀ {T : Scheme.{0}} (s : T ⟶ Spec (CommRingCat.of (AlgebraicClosure ℚ))) (P : SchemeHomOver s E.f),
      letI := E.L.pointCommGroup E.comm s
      mapPt φ hφ (mapPt φ hφ P) * P ^ n = mapPt φ hφ P ^ t)
    (H : Set (SchemeHomOver (𝟙 (Spec (CommRingCat.of (AlgebraicClosure ℚ)))) E.f)) (hHfin : H.Finite)
    (hHone : E.L.one (𝟙 (Spec (CommRingCat.of (AlgebraicClosure ℚ)))) ∈ H)
    (hHmul : ∀ P Q, P ∈ H → Q ∈ H → E.L.mul (𝟙 (Spec (CommRingCat.of (AlgebraicClosure ℚ)))) P Q ∈ H)
    (hHinv : ∀ P, P ∈ H → E.L.inv (𝟙 (Spec (CommRingCat.of (AlgebraicClosure ℚ)))) P ∈ H)
    (hHstab : ∀ (x : ↥Λ) P, P ∈ H → pushPt (E.act x) (E.act_over x) P ∈ H)
    (hHφ : ∀ P, P ∈ H ↔ mapPt φ hφ P = E.L.one (𝟙 (Spec (CommRingCat.of (AlgebraicClosure ℚ)))))
    (C : FakeEllipticCurve Λ 1 (AlgebraicClosure ℚ)) (p : E.A ⟶ C.A) (hp : p ≫ C.f = E.f) (K : Scheme.{0}) (κ : K ⟶ E.A)
    (hC :
      (∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of (AlgebraicClosure ℚ))) (P Q : SchemeHomOver t E.f),
        mapPt p hp (E.L.mul t P Q) = C.L.mul t (mapPt p hp P) (mapPt p hp Q)) ∧
      (∀ x : ↥Λ, E.act x ≫ p = p ≫ C.act x) ∧
      IsFinite p ∧ Flat p ∧ Surjective p ∧
      (∀ R : SchemeHomOver (𝟙 (Spec (CommRingCat.of (AlgebraicClosure ℚ)))) C.f, ∃ P : SchemeHomOver (𝟙 (Spec (CommRingCat.of (AlgebraicClosure ℚ)))) E.f, mapPt p hp P = R) ∧
      IsClosedImmersion κ ∧ IsReduced K ∧ IsFinite (κ ≫ E.f) ∧
      (∀ P : SchemeHomOver (𝟙 (Spec (CommRingCat.of (AlgebraicClosure ℚ)))) E.f, FactorsThrough κ P ↔ P ∈ H) ∧
      (∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of (AlgebraicClosure ℚ))) (Q : SchemeHomOver t E.f),
        mapPt p hp Q = C.L.one t ↔ FactorsThrough κ Q))
    :
    FakeEllipticCurve.Iso C E := by
  classical
  obtain ⟨p_hom, p_act, hpfin, hpflat, hpsurj, hponto, hκci, hKred, hκfin, hκpts, hkerp⟩ := hC
  haveI := hpfin; haveI := hpflat; haveI := hpsurj; haveI := hκci; haveI := hKred; haveI := hκfin
  have hO : IsOrder Λ := hΛ.1
  have hn0 : 0 < n := by nlinarith [sq_nonneg t]
  obtain ⟨m, hm⟩ : ∃ m : ℕ, (m : ℤ) = n := ⟨n.toNat, Int.toNat_of_nonneg hn0.le⟩
  have hmpos : 0 < m := by exact_mod_cast (hm ▸ hn0 : (0 : ℤ) < m)
  have hmk : (m : AlgebraicClosure ℚ) ≠ 0 := by exact_mod_cast hmpos.ne'
  have hmΛ : ((m : ℚ) : ℍ[ℚ, a, b]) ∈ Λ := by
    have : ((m : ℚ) : ℍ[ℚ, a, b]) = (m : ℤ) • (1 : ℍ[ℚ, a, b]) := by rw [zsmul_eq_mul, mul_one]; norm_cast
    rw [this]; exact Λ.smul_mem _ hO.one_mem
  have hφhom : LASTISO.IsHom E.L E.L φ hφ := fun _ s P Q => hadd s P Q
  have hphom : LASTISO.IsHom E.L C.L p hp := fun _ s P Q => p_hom s P Q

  set e₀ : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ E.A := (E.L.one (𝟙 _)).1 with he₀
  have he₀f : e₀ ≫ E.f = 𝟙 _ := (E.L.one (𝟙 _)).2
  haveI : IsProper E.f := E.bundle.proper
  haveI : IsClosedImmersion (e₀ ≫ E.f) := by rw [he₀f]; infer_instance
  haveI : IsClosedImmersion e₀ := IsClosedImmersion.of_comp e₀ E.f
  have hone_t : ∀ {T : Scheme.{0}} (s : T ⟶ Spec (CommRingCat.of (AlgebraicClosure ℚ))), (E.L.one s).1 = s ≫ e₀ := by
    intro T s
    have hn := GoodReductionJacobian.RelativeGroupLaw.one_natural E.L (𝟙 _) s s (Category.comp_id _)
    rw [← hn]; rfl
  obtain ⟨g₁, hg₁⟩ := CerednikDrinfeld.QM.exists_comp_eq_of_forall_factorsThrough_of_isReduced (AlgebraicClosure ℚ)
    (κ ≫ E.f) E.f e₀ (κ ≫ φ) (by rw [Category.assoc, hφ]) (by
      intro y
      let P : SchemeHomOver (𝟙 (Spec (CommRingCat.of (AlgebraicClosure ℚ)))) E.f := ⟨y.1 ≫ κ, by rw [Category.assoc]; exact y.2⟩
      have hP : P ∈ H := (hκpts P).1 ⟨y.1, rfl⟩
      have h0 := congrArg Subtype.val ((hHφ P).1 hP)
      refine ⟨𝟙 _, ?_⟩
      rw [Category.id_comp]
      show e₀ = y.1 ≫ (κ ≫ φ)
      rw [← Category.assoc]; exact h0.symm)
  have hkill : ∀ {T : Scheme.{0}} (s : T ⟶ Spec (CommRingCat.of (AlgebraicClosure ℚ))) (Q : SchemeHomOver s E.f),
      mapPt p hp Q = C.L.one s → mapPt φ hφ Q = E.L.one s := by
    intro T s Q hQ
    obtain ⟨c, hc⟩ := (hkerp s Q).1 hQ
    apply Subtype.ext
    rw [hone_t]
    show Q.1 ≫ φ = s ≫ e₀
    have hcg : c ≫ g₁ = s := by
      rw [← Category.comp_id (c ≫ g₁), ← he₀f, Category.assoc, ← Category.assoc g₁, hg₁, Category.assoc, hφ,
        ← Category.assoc, hc]
      exact Q.2
    rw [← hc, Category.assoc, ← hg₁, ← Category.assoc, hcg]

  obtain ⟨φb, hφb, hφbhom, hφbuniq⟩ :=
    GoodReductionJacobian.RelativeGroupLaw.existsUnique_comp_eq_of_forall_mapPt_eq_one_of_flat_of_surjective
      (AlgebraicClosure ℚ) E.L C.L E.L p hp p_hom φ hφ hadd hkill
  have hφbhom' : LASTISO.IsHom C.L E.L φb.1 φb.2 := fun _ s P Q => hφbhom s P Q
  have hφbact : ∀ x : ↥Λ, C.act x ≫ φb.1 = φb.1 ≫ E.act x := by
    intro x
    have hacthom : LASTISO.IsHom E.L E.L (E.act x) (E.act_over x) := fun _ s P Q => E.act_hom x s P Q
    have hCacthom : LASTISO.IsHom C.L C.L (C.act x) (C.act_over x) := fun _ s P Q => C.act_hom x s P Q
    obtain ⟨χ, -, -, hχu⟩ :=
      GoodReductionJacobian.RelativeGroupLaw.existsUnique_comp_eq_of_forall_mapPt_eq_one_of_flat_of_surjective
        (AlgebraicClosure ℚ) E.L C.L E.L p hp p_hom (E.act x ≫ φ) (by rw [Category.assoc, hφ, E.act_over])
        (fun s P Q => (hacthom.comp hφhom) s P Q)
        (fun s P hP => by
          rw [LASTISO.mapPt_comp (E.act x) (E.act_over x) φ hφ]
          apply hkill
          rw [show mapPt p hp (mapPt (E.act x) (E.act_over x) P) = mapPt (C.act x) (C.act_over x) (mapPt p hp P) from by
            rw [← LASTISO.mapPt_comp (E.act x) (E.act_over x) p hp (h := by rw [Category.assoc, hp, E.act_over]),
              ← LASTISO.mapPt_comp p hp (C.act x) (C.act_over x) (h := by rw [Category.assoc, C.act_over, hp])]
            apply Subtype.ext; simp only [mapPt, p_act x], hP]
          exact hCacthom.map_one s)
    have hA := hχu ⟨C.act x ≫ φb.1, by rw [Category.assoc, φb.2, C.act_over]⟩
      (by show p ≫ C.act x ≫ φb.1 = E.act x ≫ φ; rw [← Category.assoc, ← p_act x, Category.assoc, hφb])
    have hB := hχu ⟨φb.1 ≫ E.act x, by rw [Category.assoc, E.act_over, φb.2]⟩
      (by show p ≫ φb.1 ≫ E.act x = E.act x ≫ φ; rw [← Category.assoc, hφb, hlin x])
    exact congrArg Subtype.val (hA.trans hB.symm)

  letI iG : CommGroup (SchemeHomOver E.f E.f) := E.L.pointCommGroup E.comm E.f
  let ι : SchemeHomOver E.f E.f := ⟨𝟙 E.A, Category.id_comp _⟩
  let φP : SchemeHomOver E.f E.f := ⟨φ, hφ⟩
  let τ : SchemeHomOver E.f E.f := ι ^ t * φP⁻¹

  have ev : ∀ {T : Scheme.{0}} {s : T ⟶ Spec (CommRingCat.of (AlgebraicClosure ℚ))} (P : SchemeHomOver s E.f) (X : SchemeHomOver E.f E.f),
      mapPt X.1 X.2 P = GoodReductionJacobian.schemeHomOverComp P.1 P.2 X := fun P X => rfl
  have ev_mul : ∀ {T : Scheme.{0}} {s : T ⟶ Spec (CommRingCat.of (AlgebraicClosure ℚ))} (P : SchemeHomOver s E.f) (X Y : SchemeHomOver E.f E.f),
      letI := E.L.pointCommGroup E.comm s
      mapPt (X * Y).1 (X * Y).2 P = mapPt X.1 X.2 P * mapPt Y.1 Y.2 P := by
    intro T s P X Y; rw [ev, ev, ev]; exact E.L.mul_natural E.f s P.1 P.2 X Y
  have ev_one : ∀ {T : Scheme.{0}} {s : T ⟶ Spec (CommRingCat.of (AlgebraicClosure ℚ))} (P : SchemeHomOver s E.f),
      letI := E.L.pointCommGroup E.comm s
      mapPt (1 : SchemeHomOver E.f E.f).1 (1 : SchemeHomOver E.f E.f).2 P = 1 := by
    intro T s P; rw [ev]; exact E.L.one_natural E.f s P.1 P.2
  have evHom : ∀ {T : Scheme.{0}} {s : T ⟶ Spec (CommRingCat.of (AlgebraicClosure ℚ))} (P : SchemeHomOver s E.f),
      letI := E.L.pointCommGroup E.comm s
      ∃ h : SchemeHomOver E.f E.f →* SchemeHomOver s E.f, ∀ X, h X = mapPt X.1 X.2 P := by
    intro T s P
    letI := E.L.pointCommGroup E.comm s
    exact ⟨{ toFun := fun X => mapPt X.1 X.2 P, map_one' := ev_one P, map_mul' := fun X Y => ev_mul P X Y }, fun X => rfl⟩
  have ev_ι : ∀ {T : Scheme.{0}} {s : T ⟶ Spec (CommRingCat.of (AlgebraicClosure ℚ))} (P : SchemeHomOver s E.f),
      mapPt ι.1 ι.2 P = P := fun P => Subtype.ext (by show P.1 ≫ 𝟙 E.A = P.1; simp)
  have hτ : ∀ {T : Scheme.{0}} {s : T ⟶ Spec (CommRingCat.of (AlgebraicClosure ℚ))} (P : SchemeHomOver s E.f),
      letI := E.L.pointCommGroup E.comm s
      mapPt τ.1 τ.2 P = P ^ t * (mapPt φ hφ P)⁻¹ := by
    intro T s P
    letI := E.L.pointCommGroup E.comm s
    obtain ⟨h, hh⟩ := evHom P
    rw [← hh, show τ = ι ^ t * φP⁻¹ from rfl, map_mul, map_zpow, map_inv, hh, hh, ev_ι]
  have key : ∀ {T : Scheme.{0}} {s : T ⟶ Spec (CommRingCat.of (AlgebraicClosure ℚ))} (P : SchemeHomOver s E.f),
      letI := E.L.pointCommGroup E.comm s
      mapPt φ hφ (mapPt τ.1 τ.2 P) = P ^ n ∧ mapPt τ.1 τ.2 (mapPt φ hφ P) = P ^ n := by
    intro T s P
    letI := E.L.pointCommGroup E.comm s
    have hr := hrel s P
    have hφmul : ∀ X Y : SchemeHomOver s E.f, mapPt φ hφ (X * Y) = mapPt φ hφ X * mapPt φ hφ Y := fun X Y => hadd s X Y
    let φh : SchemeHomOver s E.f →* SchemeHomOver s E.f := MonoidHom.mk' (fun X => mapPt φ hφ X) hφmul
    have hφh : ∀ X, φh X = mapPt φ hφ X := fun X => rfl
    constructor
    · rw [hτ, ← hφh, map_mul, map_zpow, map_inv, hφh, hφh, ← hr, mul_comm (mapPt φ hφ (mapPt φ hφ P)) (P ^ n),
        mul_inv_cancel_right]
    · rw [hτ, ← hr, mul_comm (mapPt φ hφ (mapPt φ hφ P)) (P ^ n), mul_inv_cancel_right]

  have hpow' : ∀ (k : ℕ) {T : Scheme.{0}} (s : T ⟶ Spec (CommRingCat.of (AlgebraicClosure ℚ))) (P : SchemeHomOver s E.f),
      (letI := E.L.pointCommGroup E.comm s; P ^ k) = nsmulPt E.L s k P := by
    intro k
    induction k with
    | zero => intro T s P; rfl
    | succ j ih =>
      intro T s P
      letI := E.L.pointCommGroup E.comm s
      show P ^ (j + 1) = E.L.mul s (nsmulPt E.L s j P) P
      rw [pow_succ, ih]; rfl
  have hpow : ∀ {T : Scheme.{0}} (s : T ⟶ Spec (CommRingCat.of (AlgebraicClosure ℚ))) (P : SchemeHomOver s E.f),
      (letI := E.L.pointCommGroup E.comm s; P ^ n) = nsmulPt E.L s m P := by
    intro T s P
    letI := E.L.pointCommGroup E.comm s
    show P ^ n = _
    rw [← hm, zpow_natCast]; exact hpow' m s P

  have hφτ : φ ≫ τ.1 = E.act ⟨_, hmΛ⟩ := by
    apply LASTISO.eq_of_mapPt_id_eq (hφ := by rw [Category.assoc, τ.2, hφ]) (hψ := E.act_over _)
    rw [LASTISO.mapPt_comp φ hφ τ.1 τ.2, (key _).2, hpow,
      show mapPt (E.act ⟨_, hmΛ⟩) (E.act_over _) (⟨𝟙 E.A, Category.id_comp E.f⟩ : SchemeHomOver E.f E.f) =
        pushPt (E.act ⟨_, hmΛ⟩) (E.act_over _) ⟨𝟙 E.A, Category.id_comp E.f⟩ from rfl,
      CerednikDrinfeld.QM.FakeEllipticCurve.pushPt_act_natCast_eq_nsmulPt E hO.one_mem m hmΛ]
  have hτp : (τ.1 ≫ p) ≫ C.f = E.f := by rw [Category.assoc, hp, τ.2]

  have hφψ' : ∀ {T : Scheme.{0}} (s : T ⟶ Spec (CommRingCat.of (AlgebraicClosure ℚ))) (P : SchemeHomOver s E.f),
      mapPt φb.1 φb.2 (mapPt (τ.1 ≫ p) hτp P) = nsmulPt E.L s m P := by
    intro T s P
    rw [LASTISO.mapPt_comp τ.1 τ.2 p hp, ← LASTISO.mapPt_comp p hp φb.1 φb.2 (h := by rw [Category.assoc, φb.2, hp]),
      show mapPt (p ≫ φb.1) _ (mapPt τ.1 τ.2 P) = mapPt φ hφ (mapPt τ.1 τ.2 P) from by apply Subtype.ext; simp only [mapPt, hφb],
      (key P).1, hpow]
  have hacthomE : LASTISO.IsHom E.L E.L (E.act ⟨_, hmΛ⟩) (E.act_over _) := fun _ s P Q => E.act_hom _ s P Q
  have hacthomC : LASTISO.IsHom C.L C.L (C.act ⟨_, hmΛ⟩) (C.act_over _) := fun _ s P Q => C.act_hom _ s P Q
  have hm1 : φb.1 ≫ τ.1 ≫ p = C.act ⟨_, hmΛ⟩ := by
    obtain ⟨χ, -, -, hχu⟩ :=
      GoodReductionJacobian.RelativeGroupLaw.existsUnique_comp_eq_of_forall_mapPt_eq_one_of_flat_of_surjective
        (AlgebraicClosure ℚ) E.L C.L C.L p hp p_hom (E.act ⟨_, hmΛ⟩ ≫ p) (by rw [Category.assoc, hp, E.act_over])
        (fun s P Q => (hacthomE.comp hphom) s P Q)
        (fun s P hP => by
          rw [show mapPt (E.act ⟨_, hmΛ⟩ ≫ p) _ P = mapPt (C.act ⟨_, hmΛ⟩) (C.act_over _) (mapPt p hp P) from by
            rw [← LASTISO.mapPt_comp p hp (C.act ⟨_, hmΛ⟩) (C.act_over _) (h := by rw [Category.assoc, C.act_over, hp])]
            apply Subtype.ext; simp only [mapPt, p_act], hP]
          exact hacthomC.map_one s)
    have hA := hχu ⟨φb.1 ≫ τ.1 ≫ p, by rw [Category.assoc, hτp, φb.2]⟩
      (by show p ≫ φb.1 ≫ τ.1 ≫ p = E.act ⟨_, hmΛ⟩ ≫ p; rw [← Category.assoc, hφb, ← Category.assoc, hφτ])
    have hB := hχu ⟨C.act ⟨_, hmΛ⟩, C.act_over _⟩ (by show p ≫ C.act ⟨_, hmΛ⟩ = E.act ⟨_, hmΛ⟩ ≫ p; rw [p_act])
    exact congrArg Subtype.val (hA.trans hB.symm)
  have hψφ' : ∀ {T : Scheme.{0}} (s : T ⟶ Spec (CommRingCat.of (AlgebraicClosure ℚ))) (R : SchemeHomOver s C.f),
      mapPt (τ.1 ≫ p) hτp (mapPt φb.1 φb.2 R) = nsmulPt C.L s m R := by
    intro T s R
    rw [← LASTISO.mapPt_comp φb.1 φb.2 (τ.1 ≫ p) hτp (h := by rw [Category.assoc, hτp, φb.2]),
      show mapPt (φb.1 ≫ τ.1 ≫ p) _ R = pushPt (C.act ⟨_, hmΛ⟩) (C.act_over _) R from by apply Subtype.ext; simp only [mapPt, pushPt, hm1],
      CerednikDrinfeld.QM.FakeEllipticCurve.pushPt_act_natCast_eq_nsmulPt C hO.one_mem m hmΛ]

  have htriv : ∀ R : SchemeHomOver (𝟙 (Spec (CommRingCat.of (AlgebraicClosure ℚ)))) C.f,
      mapPt φb.1 φb.2 R = E.L.one _ → R = C.L.one _ := by
    intro R hR
    obtain ⟨P, rfl⟩ := hponto R
    have hφP : mapPt φ hφ P = E.L.one _ := by
      rw [← hR, ← LASTISO.mapPt_comp p hp φb.1 φb.2 (h := by rw [Category.assoc, φb.2, hp])]
      apply Subtype.ext; simp only [mapPt, hφb]
    exact (hkerp _ P).2 ((hκpts P).2 ((hHφ P).2 hφP))
  haveI : IsIso φb.1 := CerednikDrinfeld.QM.FakeEllipticCurve.isIso_of_forall_mapPt_eq_one_imp_eq_one (AlgebraicClosure ℚ)
    C E φb.1 φb.2 hφbhom hφbact (τ.1 ≫ p) hτp m hmpos hmk hψφ' hφψ' htriv

  refine ⟨asIso φb.1, φb.2, hφbhom, hφbact, ?_⟩
  intro T s R
  rw [LASTISO.factorsThrough_lev_iff_eq_one C, LASTISO.factorsThrough_lev_iff_eq_one E]
  constructor
  · rintro rfl; exact hφbhom'.map_one s
  · intro h
    rw [← LASTISO.mapPt_iso_eq_iff (asIso φb.1) φb.2 R (C.L.one s)]
    exact h.trans (hφbhom'.map_one s).symm

end S_CerednikDrinfeld_QM_FakeEllipticCurve_iso_of_quotient_ker_of_mapPt_mapPt_mul_zpow_eq_zpow
end P2MW
export P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_iso_of_quotient_ker_of_mapPt_mapPt_mul_zpow_eq_zpow (solution)
