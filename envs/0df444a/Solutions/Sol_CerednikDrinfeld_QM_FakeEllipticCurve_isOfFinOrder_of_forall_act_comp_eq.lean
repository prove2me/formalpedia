-- Prove2me | solution 1 for CerednikDrinfeld.QM.FakeEllipticCurve.isOfFinOrder_of_forall_act_comp_eq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.141142+00:00
-- url     : https://prove2.me/submissions/d19c28fc-0abb-50ae-ab8b-9dd6c8ac7d85

import Definitions.Def_CerednikDrinfeld_QMModuli
import Definitions.Def_AlgebraicGeometry_RelativeGroupLawEndDegree
import Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_exists_forall_mapPt_mapPt_mul_zpow_eq_zpow_of_forall_act_comp_eq
import Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_exists_forall_mapPt_eq_zpow_of_forall_act_comp_eq_of_four_mul_le_sq
import Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_natCard_isTorsionPoint_eq_pow_of_natCast_ne_zero
import Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_smoothOfRelativeDimension_two
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_isOfFinOrder_of_forall_act_comp_eq
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
p2m_attr_erase "simp" "AlgebraicGeometry.ProjSpace.twistGradeToObj_val AlgebraicGeometry.ProjSpace.twistObj.smul_val AlgebraicGeometry.ProjSpace.twistGradeEquiv_apply_val AlgebraicGeometry.ProjSpace.twistObj.mk.sizeOf_spec GoodReductionJacobian.RelativeGroupLaw.fibre_inv GoodReductionJacobian.RelativeGroupLaw.fibrePointToBase_coe GoodReductionJacobian.RelativeGroupLaw.fibrePointOfBase_toBase GoodReductionJacobian.RelativeGroupLaw.fibre_mul GoodReductionJacobian.RelativeGroupLaw.fibrePointToBase_ofBase GoodReductionJacobian.RelativeGroupLaw.fibre_one GoodReductionJacobian.RelativeGroupLaw.fibrePointOfBase_coe AlgebraicGeometry.schemeFibreEndo_snd AlgebraicGeometry.schemeFibreEndo_fst QuaternionAlgebra.baseChangeRight_tmul QuaternionAlgebra.mapOfAlgebraMapEq_apply QuaternionAlgebra.baseChange_tmul"

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry NeronModelInfra GoodReductionJacobian IsDedekindDomain AlgebraicCurve QuaternionAlgebra CerednikDrinfeld CerednikDrinfeld.QM
open scoped Quaternion TensorProduct NumberField

universe u

namespace P2mKcFinOrdAutQM

section Alg

variable {G : Type*} [CommGroup G]

theorem key_alg (σ τ : G →* G) (hτσ : ∀ P, τ (σ P) = P) (t n t' n' : ℤ)
    (h1 : ∀ P, σ (σ P) * P ^ n = σ P ^ t) (h2 : ∀ P, τ (τ P) * P ^ n' = τ P ^ t') (P : G) :
    σ P ^ (t' - t * n') = P ^ (1 - n * n') := by
  have a : MonoidHom.toAdditive σ (MonoidHom.toAdditive σ (Additive.ofMul P)) + n • Additive.ofMul P = t • MonoidHom.toAdditive σ (Additive.ofMul P) := by
    have := congrArg Additive.ofMul (h1 P)
    simpa [ofMul_mul, ofMul_zpow] using this
  have b : Additive.ofMul P + n' • MonoidHom.toAdditive σ (MonoidHom.toAdditive σ (Additive.ofMul P)) =
      t' • MonoidHom.toAdditive σ (Additive.ofMul P) := by
    have := congrArg Additive.ofMul (h2 (σ (σ P)))
    rw [hτσ, hτσ] at this
    simpa [ofMul_mul, ofMul_zpow] using this
  have c : (t' - t * n') • MonoidHom.toAdditive σ (Additive.ofMul P) = (1 - n * n') • Additive.ofMul P := by
    linear_combination (norm := module) (-1 : ℤ) • b + n' • a
  have := congrArg Additive.toMul c
  simpa [toMul_zsmul] using this

theorem disc_alg (σ : G →* G) (t n s M : ℤ)
    (h1 : ∀ P, σ (σ P) * P ^ n = σ P ^ t) (hK : ∀ P, σ P ^ s = P ^ M) (P : G) :
    P ^ (M ^ 2 - M * t * s + n * s ^ 2) = 1 := by
  have a : MonoidHom.toAdditive σ (MonoidHom.toAdditive σ (Additive.ofMul P)) + n • Additive.ofMul P = t • MonoidHom.toAdditive σ (Additive.ofMul P) := by
    have := congrArg Additive.ofMul (h1 P)
    simpa [ofMul_mul, ofMul_zpow] using this
  have b : s • MonoidHom.toAdditive σ (Additive.ofMul P) = M • Additive.ofMul P := by
    have := congrArg Additive.ofMul (hK P)
    simpa [ofMul_zpow] using this
  have c : s • MonoidHom.toAdditive σ (MonoidHom.toAdditive σ (Additive.ofMul P)) = M • MonoidHom.toAdditive σ (Additive.ofMul P) := by
    have := congrArg Additive.ofMul (hK (σ P))
    simpa [ofMul_zpow] using this
  have d : (M ^ 2 - M * t * s + n * s ^ 2) • Additive.ofMul P = 0 := by
    linear_combination (norm := module) (s ^ 2) • a + (t * s - M) • b - s • c
  have := congrArg Additive.toMul d
  simpa [toMul_zsmul] using this

theorem twelve_alg (σ : G →* G) (t : ℤ) (ht : t = -1 ∨ t = 0 ∨ t = 1)
    (h1 : ∀ P, σ (σ P) * P ^ (1 : ℤ) = σ P ^ t) (P : G) : σ^[12] P = P := by
  rcases ht with rfl | rfl | rfl
  ·
    have h2 : ∀ P, σ (σ P) = (σ P)⁻¹ * P⁻¹ := fun P => by
      have := h1 P
      rw [zpow_one, zpow_neg_one] at this
      exact eq_mul_inv_of_mul_eq this
    have h3 : ∀ P, σ^[3] P = P := fun P => by
      show σ (σ (σ P)) = P
      rw [h2 (σ P), h2 P, mul_inv_rev, inv_inv, inv_inv, mul_assoc, mul_inv_cancel, mul_one]
    rw [show 12 = 3 + 3 + 3 + 3 from rfl, Function.iterate_add_apply, Function.iterate_add_apply,
      Function.iterate_add_apply, h3, h3, h3, h3]
  ·
    have h2 : ∀ P, σ (σ P) = P⁻¹ := fun P => by
      have := h1 P
      rw [zpow_one, zpow_zero] at this
      exact eq_inv_of_mul_eq_one_left this
    have h4 : ∀ P, σ^[4] P = P := fun P => by
      show σ (σ (σ (σ P))) = P
      rw [h2, h2, inv_inv]
    rw [show 12 = 4 + 4 + 4 from rfl, Function.iterate_add_apply, Function.iterate_add_apply, h4, h4, h4]
  ·
    have h2 : ∀ P, σ (σ P) = σ P * P⁻¹ := fun P => by
      have := h1 P
      rw [zpow_one, zpow_one] at this
      exact eq_mul_inv_of_mul_eq this
    have h3 : ∀ P, σ^[3] P = P⁻¹ := fun P => by
      show σ (σ (σ P)) = P⁻¹
      rw [h2 (σ P), h2 P, mul_comm (σ P) P⁻¹, mul_assoc, mul_inv_cancel, mul_one]
    have h6 : ∀ P, σ^[6] P = P := fun P => by
      rw [show 6 = 3 + 3 from rfl, Function.iterate_add_apply, h3, h3, inv_inv]
    rw [show 12 = 6 + 6 from rfl, Function.iterate_add_apply, h6, h6]

theorem scalar_alg (σ τ : G →* G) (hτσ : ∀ P, τ (σ P) = P) (c c' : ℤ)
    (hσ : ∀ P, σ P = P ^ c) (hτ : ∀ P, τ P = P ^ c') (P : G) : P ^ (c' * c - 1) = 1 := by
  have h : P ^ (c' * c) = P := by
    conv_rhs => rw [← hτσ P, hσ, map_zpow, hτ, ← zpow_mul]
  rw [zpow_sub_one, h, mul_inv_cancel]

theorem four_mul_le_sq_of (M t s n : ℤ) (hs : s ≠ 0) (h : M ^ 2 - M * t * s + n * s ^ 2 = 0) : 4 * n ≤ t ^ 2 := by
  have h1 : 4 * n * s ^ 2 ≤ t ^ 2 * s ^ 2 := by nlinarith [sq_nonneg (t * s - 2 * M), sq_nonneg s]
  have hs2 : 0 < s ^ 2 := by positivity
  exact le_of_mul_le_mul_right h1 hs2

end Alg

section MapPt

variable {k : Type u} [CommRing k] {A : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of k)}

theorem inv_over (e : A ≅ A) (he : e.hom ≫ f = f) : e.inv ≫ f = f := by
  have h : e.inv ≫ f = e.inv ≫ (e.hom ≫ f) := by rw [he]
  rw [h, Iso.inv_hom_id_assoc]

theorem mapPt_inv_hom (e : A ≅ A) (he : e.hom ≫ f = f) (he' : e.inv ≫ f = f)
    {T : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of k)} (P : SchemeHomOver t f) :
    mapPt e.inv he' (mapPt e.hom he P) = P := by
  apply Subtype.ext
  simp

theorem mapPt_hom_inv (e : A ≅ A) (he : e.hom ≫ f = f) (he' : e.inv ≫ f = f)
    {T : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of k)} (P : SchemeHomOver t f) :
    mapPt e.hom he (mapPt e.inv he' P) = P := by
  apply Subtype.ext
  simp

theorem hmul_inv (L : RelativeGroupLaw k f) (e : A ≅ A) (he : e.hom ≫ f = f) (he' : e.inv ≫ f = f)
    (hmul : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of k)) (P Q : SchemeHomOver t f),
      mapPt e.hom he (L.mul t P Q) = L.mul t (mapPt e.hom he P) (mapPt e.hom he Q))
    {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of k)) (P Q : SchemeHomOver t f) :
    mapPt e.inv he' (L.mul t P Q) = L.mul t (mapPt e.inv he' P) (mapPt e.inv he' Q) := by
  have hinj : Function.Injective (fun R : SchemeHomOver t f => mapPt e.hom he R) :=
    Function.LeftInverse.injective (g := fun R => mapPt e.inv he' R) (fun R => mapPt_inv_hom e he he' R)
  apply hinj
  show mapPt e.hom he (mapPt e.inv he' (L.mul t P Q)) =
    mapPt e.hom he (L.mul t (mapPt e.inv he' P) (mapPt e.inv he' Q))
  rw [hmul, mapPt_hom_inv, mapPt_hom_inv, mapPt_hom_inv]

theorem comm_inv (e : A ≅ A) (g : A ⟶ A) (hg : g ≫ e.hom = e.hom ≫ g) : g ≫ e.inv = e.inv ≫ g := by
  rw [Iso.comp_inv_eq, Category.assoc, Iso.eq_inv_comp]
  exact hg.symm

theorem pow_hom_over (e : Aut A) (he : e.hom ≫ f = f) (m : ℕ) : (e ^ m).hom ≫ f = f := by
  induction m with
  | zero => exact Category.id_comp f
  | succ m ih => rw [pow_succ', Aut.Aut_mul_def, Iso.trans_hom, Category.assoc, he, ih]

theorem mapPt_pow_hom (e : Aut A) (he : e.hom ≫ f = f) (m : ℕ)
    {T : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of k)} (P : SchemeHomOver t f) :
    mapPt (e ^ m).hom (pow_hom_over e he m) P = (fun R : SchemeHomOver t f => mapPt e.hom he R)^[m] P := by
  induction m generalizing P with
  | zero =>
      apply Subtype.ext
      rw [mapPt_coe, Function.iterate_zero, id_eq, pow_zero]
      exact Category.comp_id _
  | succ m ih =>
      have h1 : (fun R : SchemeHomOver t f => mapPt e.hom he R)^[m + 1] P =
          mapPt e.hom he (mapPt (e ^ m).hom (pow_hom_over e he m) P) := by
        rw [Function.iterate_succ_apply', ← ih]
      rw [h1]
      apply Subtype.ext
      rw [mapPt_coe, mapPt_coe, mapPt_coe, pow_succ', Aut.Aut_mul_def, Iso.trans_hom, Category.assoc]

theorem pow_eq_one_of_iterate (e : Aut A) (he : e.hom ≫ f = f) (m : ℕ)
    (h : (fun R : SchemeHomOver f f => mapPt e.hom he R)^[m] (⟨𝟙 A, Category.id_comp f⟩ : SchemeHomOver f f) =
      ⟨𝟙 A, Category.id_comp f⟩) : e ^ m = 1 := by
  have h' := congrArg Subtype.val ((mapPt_pow_hom e he m (⟨𝟙 A, Category.id_comp f⟩ : SchemeHomOver f f)).trans h)
  rw [mapPt_coe, Category.id_comp] at h'
  exact Iso.ext h'

end MapPt

section Torsion

variable {K : Type u} [Field K] {A : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of K)}

theorem nsmul_eq_pow (L : RelativeGroupLaw K f) (hc : L.IsCommutative) {T : Scheme.{u}}
    (t : T ⟶ Spec (CommRingCat.of K)) (m : ℕ) (x : SchemeHomOver t f) :
    L.nsmul t m x = (letI := L.pointCommGroup hc t; x ^ m) := by
  letI := L.pointCommGroup hc t
  induction m with
  | zero => rfl
  | succ m ih => rw [L.nsmul_succ, ih, pow_succ]; rfl

theorem natCast_ne_zero_of_ringChar_lt (ℓ : ℕ) (hℓ : ℓ.Prime) (h : ringChar K < ℓ) : (ℓ : K) ≠ 0 := by
  intro h0
  rw [ringChar.spec] at h0
  rcases CharP.char_is_prime_or_zero K (ringChar K) with hp | hp
  · rcases (Nat.dvd_prime hℓ).mp h0 with h1 | h1
    · exact hp.one_lt.ne' h1
    · omega
  · rw [hp, zero_dvd_iff] at h0
    omega

theorem eq_zero_of_forall_zpow_eq_one [IsAlgClosed K] (L : RelativeGroupLaw K f) (hc : L.IsCommutative)
    (hA : AbelianSchemePropertyBundle K f) [SmoothOfRelativeDimension 2 f] (M : ℤ)
    (h : ∀ P : SchemeHomOver (𝟙 (Spec (CommRingCat.of K))) f,
      letI := L.pointCommGroup hc (𝟙 (Spec (CommRingCat.of K))); P ^ M = 1) : M = 0 := by
  by_contra hM
  letI := L.pointCommGroup hc (𝟙 (Spec (CommRingCat.of K)))
  obtain ⟨ℓ, hle, hℓ⟩ := Nat.exists_infinite_primes (M.natAbs + ringChar K + 1)
  have hℓK : (ℓ : K) ≠ 0 := natCast_ne_zero_of_ringChar_lt ℓ hℓ (by omega)
  have hcard := GoodReductionJacobian.RelativeGroupLaw.natCard_isTorsionPoint_eq_pow_of_natCast_ne_zero
    K f L hc hA 2 ℓ hℓK
  haveI : Finite {x : SchemeHomOver (𝟙 (Spec (CommRingCat.of K))) f //
      L.IsTorsionPoint (𝟙 (Spec (CommRingCat.of K))) ℓ x} := by
    apply Nat.finite_of_card_ne_zero
    rw [hcard]
    exact pow_ne_zero _ hℓ.ne_zero
  haveI : Nontrivial {x : SchemeHomOver (𝟙 (Spec (CommRingCat.of K))) f //
      L.IsTorsionPoint (𝟙 (Spec (CommRingCat.of K))) ℓ x} := by
    rw [← Finite.one_lt_card_iff_nontrivial, hcard]
    exact Nat.one_lt_pow (by norm_num) hℓ.one_lt
  obtain ⟨b, hb⟩ := exists_ne
    (⟨L.one _, L.isTorsionPoint_unit _ ℓ⟩ : {x : SchemeHomOver (𝟙 (Spec (CommRingCat.of K))) f //
      L.IsTorsionPoint (𝟙 (Spec (CommRingCat.of K))) ℓ x})
  have hbℓ : b.1 ^ ℓ = 1 := by
    have := b.2
    rw [RelativeGroupLaw.isTorsionPoint_def, nsmul_eq_pow L hc] at this
    exact this
  have hb1 : b.1 ≠ 1 := fun h1 => hb (Subtype.ext h1)
  have hord : orderOf b.1 = ℓ := by
    rcases (Nat.dvd_prime hℓ).mp (orderOf_dvd_of_pow_eq_one hbℓ) with h1 | h1
    · exact absurd (orderOf_eq_one_iff.mp h1) hb1
    · exact h1
  have hdvd : (orderOf b.1 : ℤ) ∣ M := orderOf_dvd_iff_zpow_eq_one.mpr (h b.1)
  rw [hord, Int.natCast_dvd] at hdvd
  have := Nat.le_of_dvd (Int.natAbs_pos.mpr hM) hdvd
  omega

end Torsion

theorem main
    {q q' : ℕ} [Fact q.Prime] [Fact q'.Prime] (hqq' : q' ≠ q)
    {a b : ℚ} (hB : IsIndefiniteRamifiedExactlyAt a b q q')
    (Λ : Submodule ℤ ℍ[ℚ, a, b]) (hΛ : IsMaximalOrder Λ) {N : ℕ}
    (k : Type u) [Field k] [IsAlgClosed k] (E : FakeEllipticCurve Λ N k)
    (e : Aut E.A) (he : e.hom ≫ E.f = E.f)
    (hmul : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of k)) (P Q : SchemeHomOver t E.f),
      mapPt e.hom he (E.L.mul t P Q) = E.L.mul t (mapPt e.hom he P) (mapPt e.hom he Q))
    (hact : ∀ x : ↥Λ, E.act x ≫ e.hom = e.hom ≫ E.act x) :
    IsOfFinOrder e ∨ ∃ c : ℤ, ∀ {T : Scheme.{u}} (s : T ⟶ Spec (CommRingCat.of k)) (P : SchemeHomOver s E.f),
      letI := E.L.pointCommGroup E.comm s
      mapPt e.hom he P = P ^ c := by
  haveI := CerednikDrinfeld.QM.FakeEllipticCurve.smoothOfRelativeDimension_two k E
  have he' : e.inv ≫ E.f = E.f := inv_over e he
  have hmul' : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of k)) (P Q : SchemeHomOver t E.f),
      mapPt e.inv he' (E.L.mul t P Q) = E.L.mul t (mapPt e.inv he' P) (mapPt e.inv he' Q) :=
    fun t P Q => hmul_inv E.L e he he' hmul t P Q
  have hact' : ∀ x : ↥Λ, E.act x ≫ e.inv = e.inv ≫ E.act x := fun x => comm_inv e (E.act x) (hact x)

  obtain ⟨t, n, hA1⟩ :=
    CerednikDrinfeld.QM.FakeEllipticCurve.exists_forall_mapPt_mapPt_mul_zpow_eq_zpow_of_forall_act_comp_eq
      hqq' hB Λ hΛ k E e.hom he hmul hact
  obtain ⟨t', n', hA2⟩ :=
    CerednikDrinfeld.QM.FakeEllipticCurve.exists_forall_mapPt_mapPt_mul_zpow_eq_zpow_of_forall_act_comp_eq
      hqq' hB Λ hΛ k E e.inv he' hmul' hact'

  have hK : ∀ {T : Scheme.{u}} (s : T ⟶ Spec (CommRingCat.of k)) (P : SchemeHomOver s E.f),
      letI := E.L.pointCommGroup E.comm s
      mapPt e.hom he P ^ (t' - t * n') = P ^ (1 - n * n') := by
    intro T s P
    letI := E.L.pointCommGroup E.comm s
    exact key_alg (MonoidHom.mk' (fun R => mapPt e.hom he R) (fun R S => hmul s R S))
      (MonoidHom.mk' (fun R => mapPt e.inv he' R) (fun R S => hmul' s R S))
      (fun R => mapPt_inv_hom e he he' R) t n t' n' (fun R => hA1 s R) (fun R => hA2 s R) P
  by_cases hM : 1 - n * n' = 0
  ·
    have hn : n = 1 ∨ n = -1 := Int.eq_one_or_neg_one_of_mul_eq_one (u := n) (v := n') (by linarith)
    rcases hn with rfl | rfl
    · by_cases ht : 4 * (1 : ℤ) ≤ t ^ 2
      · right
        exact CerednikDrinfeld.QM.FakeEllipticCurve.exists_forall_mapPt_eq_zpow_of_forall_act_comp_eq_of_four_mul_le_sq
          hqq' hB Λ hΛ k E e.hom he hmul hact t 1 hA1 ht
      · left
        have ht' : t = -1 ∨ t = 0 ∨ t = 1 := by
          have h4 : t ^ 2 < 4 := by linarith
          have h5 : -2 < t := by nlinarith
          have h6 : t < 2 := by nlinarith
          omega
        refine isOfFinOrder_iff_pow_eq_one.mpr ⟨12, by norm_num, ?_⟩
        apply pow_eq_one_of_iterate e he 12
        letI := E.L.pointCommGroup E.comm E.f
        exact twelve_alg (MonoidHom.mk' (fun R => mapPt e.hom he R) (fun R S => hmul E.f R S)) t ht'
          (fun R => hA1 E.f R) _
    · right
      exact CerednikDrinfeld.QM.FakeEllipticCurve.exists_forall_mapPt_eq_zpow_of_forall_act_comp_eq_of_four_mul_le_sq
        hqq' hB Λ hΛ k E e.hom he hmul hact t (-1) hA1 (by nlinarith [sq_nonneg t])
  ·
    by_cases hs : t' - t * n' = 0
    · exfalso
      apply hM
      apply eq_zero_of_forall_zpow_eq_one E.L E.comm E.bundle (1 - n * n')
      intro P
      letI := E.L.pointCommGroup E.comm (𝟙 (Spec (CommRingCat.of k)))
      have := hK (𝟙 _) P
      rw [hs, zpow_zero] at this
      exact this.symm
    · right
      have hdisc : 4 * n ≤ t ^ 2 := by
        have h0 : (1 - n * n') ^ 2 - (1 - n * n') * t * (t' - t * n') + n * (t' - t * n') ^ 2 = 0 := by
          apply eq_zero_of_forall_zpow_eq_one E.L E.comm E.bundle
          intro P
          letI := E.L.pointCommGroup E.comm (𝟙 (Spec (CommRingCat.of k)))
          exact disc_alg (MonoidHom.mk' (fun R => mapPt e.hom he R) (fun R S => hmul _ R S))
            t n (t' - t * n') (1 - n * n') (fun R => hA1 _ R) (fun R => hK _ R) P
        exact four_mul_le_sq_of _ t _ n hs h0
      exact CerednikDrinfeld.QM.FakeEllipticCurve.exists_forall_mapPt_eq_zpow_of_forall_act_comp_eq_of_four_mul_le_sq
        hqq' hB Λ hΛ k E e.hom he hmul hact t n hA1 hdisc

end P2mKcFinOrdAutQM

open P2mKcFinOrdAutQM

theorem solution
    {q q' : ℕ} [Fact q.Prime] [Fact q'.Prime] (hqq' : q' ≠ q)
    {a b : ℚ} (hB : IsIndefiniteRamifiedExactlyAt a b q q')
    (Λ : Submodule ℤ ℍ[ℚ, a, b]) (hΛ : IsMaximalOrder Λ) {N : ℕ}
    (k : Type u) [Field k] [IsAlgClosed k] (E : FakeEllipticCurve Λ N k)
    (e : Aut E.A) (he : e.hom ≫ E.f = E.f)
    (hmul : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of k)) (P Q : SchemeHomOver t E.f),
      mapPt e.hom he (E.L.mul t P Q) = E.L.mul t (mapPt e.hom he P) (mapPt e.hom he Q))
    (hact : ∀ x : ↥Λ, E.act x ≫ e.hom = e.hom ≫ E.act x) :
    IsOfFinOrder e := by
  haveI := CerednikDrinfeld.QM.FakeEllipticCurve.smoothOfRelativeDimension_two k E
  have he' : e.inv ≫ E.f = E.f := inv_over e he
  have hmul' : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of k)) (P Q : SchemeHomOver t E.f),
      mapPt e.inv he' (E.L.mul t P Q) = E.L.mul t (mapPt e.inv he' P) (mapPt e.inv he' Q) :=
    fun t P Q => hmul_inv E.L e he he' hmul t P Q
  have hact' : ∀ x : ↥Λ, E.act x ≫ e.inv = e.inv ≫ E.act x := fun x => comm_inv e (E.act x) (hact x)
  rcases main hqq' hB Λ hΛ k E e he hmul hact with h | ⟨c, hc⟩
  · exact h
  rcases main hqq' hB Λ hΛ k E e⁻¹ he' hmul' hact' with h | ⟨c', hc'⟩
  · exact isOfFinOrder_inv_iff.mp h

  have hcc : c' * c - 1 = 0 := by
    apply eq_zero_of_forall_zpow_eq_one E.L E.comm E.bundle
    intro P
    letI := E.L.pointCommGroup E.comm (𝟙 (Spec (CommRingCat.of k)))
    exact scalar_alg (MonoidHom.mk' (fun R => mapPt e.hom he R) (fun R S => hmul _ R S))
      (MonoidHom.mk' (fun R => mapPt e.inv he' R) (fun R S => hmul' _ R S))
      (fun R => mapPt_inv_hom e he he' R) c c' (fun R => hc _ R) (fun R => hc' _ R) P
  have hc1 : c = 1 ∨ c = -1 := Int.eq_one_or_neg_one_of_mul_eq_one (u := c) (v := c') (by linarith)
  refine isOfFinOrder_iff_pow_eq_one.mpr ⟨2, by norm_num, ?_⟩
  apply pow_eq_one_of_iterate e he 2
  letI := E.L.pointCommGroup E.comm E.f
  show mapPt e.hom he (mapPt e.hom he _) = _
  rw [hc E.f, hc E.f, ← zpow_mul]
  rcases hc1 with rfl | rfl <;> simp

end S_CerednikDrinfeld_QM_FakeEllipticCurve_isOfFinOrder_of_forall_act_comp_eq
end P2MW
export P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_isOfFinOrder_of_forall_act_comp_eq (solution)
