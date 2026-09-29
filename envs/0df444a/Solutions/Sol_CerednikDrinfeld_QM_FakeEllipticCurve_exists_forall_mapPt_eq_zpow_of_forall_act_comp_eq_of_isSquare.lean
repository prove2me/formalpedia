-- Prove2me | solution 1 for CerednikDrinfeld.QM.FakeEllipticCurve.exists_forall_mapPt_eq_zpow_of_forall_act_comp_eq_of_isSquare
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.837917+00:00
-- url     : https://prove2.me/submissions/4e6ae1e6-cfd7-5357-afb3-ae47b0ac1a91

import Definitions.Def_CerednikDrinfeld_QMModuli
import Definitions.Def_AlgebraicGeometry_RelativeGroupLawEndDegree
import Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_endDegree_ne_zero_of_forall_act_comp_eq_of_ne_one
import Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_exists_forall_nsmul_eq_one_of_isFinite_pullback_snd
import Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_natCard_isTorsionPoint_eq_pow_of_natCast_ne_zero
import Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_smoothOfRelativeDimension_two
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_exists_forall_mapPt_eq_zpow_of_forall_act_comp_eq_of_isSquare
p2m_attr_erase "instance" "AlgebraicGeometry.Scheme.PresheafOfModules.symmetricCategory SheafOfModules.instFaithfulRingSheafPModToPMod SheafOfModules.symmetricCategory AlgebraicGeometry.Scheme.PresheafOfModules.monoidalCategory AlgebraicGeometry.Scheme.PresheafOfModules.monoidalClosed SheafOfModules.instFullRingSheafPModToPMod SheafOfModules.monoidalCategory AlgebraicGeometry.Scheme.Modules.symmetricCategory SheafOfModules.monoidalClosed SheafOfModules.instIsLocalizationPModRingSheafSheafifyFunctorPresheafW SheafOfModules.sheafifyFunctor_monoidal AlgebraicGeometry.Scheme.Modules.monoidalClosed AlgebraicGeometry.instMonoidalPresheafOfModulesModulesSheafify AlgebraicGeometry.Scheme.Modules.monoidalCategory PresheafOfModules.instMonoidalClosed PresheafOfModules.InternalHom.instModuleCarrierObjOppositeCommRingCatSubtypePiFamilyMemAddSubgroupNaturalFamilies PresheafOfModules.InternalHom.instModuleCarrierObjOppositeRingCatCompCommRingCatForget₂RingHomCarrierCarrierAbPresheaf PresheafOfModules.InternalHom.instSMulCarrierObjOppositeCommRingCatSubtypePiFamilyMemAddSubgroupNaturalFamilies AlgebraicGeometry.Scheme.Hom.opensMapFinal AlgebraicGeometry.RelPicard.RigidifiedLineBundle.setoid AlgebraicGeometry.RelPicard.RigidifiedLineBundle.instInhabited AlgebraicGeometry.OModulePresheaf.isScalarTower AlgebraicGeometry.Scheme.OrderedAffineCover.instLinearOrder AlgebraicGeometry.OModulePresheaf.module AlgebraicGeometry.Scheme.OrderedAffineCover.instFintype AlgebraicGeometry.Scheme.OrderedAffineCover.instFintypeIdx AlgebraicGeometry.OModulePresheaf.addCommGroup AlgebraicGeometry.Scheme.OrderedAffineCover.instDecidableEqIdx AlgebraicGeometry.OModulePresheaf.moduleSections TwoChartCech.Sections.M0_moduleA TwoChartCech.Sections.M1_module TwoChartCech.Cover.A01_algebra TwoChartCech.Cover.A0_algebra TwoChartCech.Cover.A1_commRing TwoChartCech.Cover.A1_algebra TwoChartCech.Sections.M01_module TwoChartCech.Sections.M0_addCommGroup TwoChartCech.Sections.M0_tower TwoChartCech.Sections.M01_addCommGroup TwoChartCech.Cover.A0_commRing"
p2m_attr_erase "instance" "TwoChartCech.Sections.M1_tower TwoChartCech.Sections.M01_moduleA TwoChartCech.Sections.M0_module TwoChartCech.Sections.M1_moduleA TwoChartCech.Sections.M1_addCommGroup TwoChartCech.Cover.A01_commRing TwoChartCech.Sections.M01_tower CoherentBaseChange.TwoTermComplex.C0_module CoherentBaseChange.TwoTermComplex.C0_addCommGroup CoherentBaseChange.TwoTermComplex.C1_module CoherentBaseChange.TwoTermComplex.C1_addCommGroup CoherentBaseChange.TwoTermComplex.C0_free CoherentBaseChange.TwoTermComplex.C1_finite CoherentBaseChange.TwoTermComplex.C0_finite CoherentBaseChange.TwoTermComplex.C1_free AlgebraicGeometry.Scheme.Modules.preservesBinaryProducts_opensMap AlgebraicGeometry.Scheme.Modules.pullback_monoidal AlgebraicGeometry.Scheme.Modules.sheafify_isLocalization' AlgebraicGeometry.Scheme.Modules.preservesTerminal_opensMap AlgebraicGeometry.Scheme.Modules.pullback₀_monoidal AlgebraicGeometry.Scheme.Modules.preservesFiniteProducts_opensMap AlgebraicGeometry.Scheme.Modules.instLiftingPresheafOfModulesSheafifyPresheafWOpensCarrierCarrierCommRingCatGrothendieckTopologyObjFunctorOppositeIsSheafSheafCompPullback₀Pullback PresheafOfModules.PullbackMonoidal.pullback_monoidal PresheafOfModules.PullbackMonoidal.isIso_δ PresheafOfModules.pushforward_laxMonoidal PresheafOfModules.PullbackMonoidal.isIso_η PresheafOfModules.free_monoidal PresheafOfModules.restrictScalars_laxMonoidal PresheafOfModules.PullbackMonoidal.isIso_δ_gS PresheafOfModules.pullback_oplaxMonoidal PresheafOfModules.PullbackMonoidal.instPreservesColimitsOfSizeCompOppositeCommRingCatRingCatForget₂RingHomCarrierCarrierPb PresheafOfModules.pullback_monoidal' AlgebraicGeometry.SmoothOfRelativeDimension.fiberToSpecResidueField AlgebraicGeometry.SmoothOfRelativeDimension.pullback_snd AlgebraicGeometry.SmoothOfRelativeDimension.pullback_fst AlgebraicGeometry.SmoothOfRelativeDimension.smooth_one AlgebraicGeometry.SmoothProperCurve.isIntegral_pullback_Spec_field AlgebraicGeometry.IsProper.fiberToSpecResidueField AlgebraicCurve.CurveModel.isProper AlgebraicCurve.CurveModel.isIntegral"
p2m_attr_erase "instance" "AlgebraicCurve.CurveModel.smooth AlgebraicGeometry.Scheme.LocalRepresentabilityULift.instIsLocallyInjectiveFunUliftYonedaGluedToSheaf AlgebraicGeometry.Scheme.LocalRepresentabilityULift.instIsLocallySurjectiveFunUliftYonedaGluedToSheafOfIsLocallySurjectiveZariskiTopologyDescFunctorOppositeType AlgebraicGeometry.Scheme.LocalRepresentabilityULift.instIsOpenImmersionToGlued AlgebraicGeometry.Scheme.LocalRepresentabilityULift.instIsIsoSheafZariskiTopologyTypeUliftYonedaGluedToSheaf AlgebraicGeometry.RelPicard.instIsOpenImmersionToGlued AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.instFundamentalIdentityOfSumRamificationInertia AlgebraicCurve.Place.instIsScalarTowerResidueFieldRestrictPushforward AlgebraicCurve.Place.instAlgebraResidueFieldRestrictPushforward AlgebraicCurve.Place.instIsLocalHomRestrictInclusion AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions PresheafOfModules.ExteriorPower.instModulePresheafAb AlgebraicGeometry.RelEffCartierDiv.subsingleton_of_degree_zero AlgebraicGeometry.RelEffCartierDiv.isIso_subschemeIota_snd_of_degree_one AlgebraicGeometry.isIso_ker_graphOver_subschemeIota_snd AlgebraicGeometry.isClosedImmersion_graphOver AlgebraicGeometry.FGSubalgebra.instIsDirectedLe AlgebraicGeometry.FGSubalgebra.instQuasiSeparatedSpaceCarrierCarrierCommRingCatObjOppositeSchemeSpecDiagram AlgebraicGeometry.FGSubalgebra.instIsCofilteredOpposite AlgebraicGeometry.FGSubalgebra.instIsAffineObjOppositeSchemeSpecDiagram AlgebraicGeometry.FGSubalgebra.instNonempty AlgebraicGeometry.FGSubalgebra.instNonemptySubtypeLeSubalgebraValFG AlgebraicGeometry.FGSubalgebra.instCompactSpaceCarrierCarrierCommRingCatObjOppositeSchemeSpecDiagram AlgebraicGeometry.FGSubalgebra.instIsDirectedSubtypeLeSubalgebraValFG AlgebraicGeometry.FGSubalgebra.instIsAffineHomMapOppositeSchemeSpecDiagram AlgebraicGeometry.FGSubalgebra.instIsFiltered AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instNeg AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instSMulInt AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instAddCommGroup AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instAdd AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instSub AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instModuleCarrierObjOppositeOpensCarrierCarrierCommRingCatPresheafOpOpensTop AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instSMulCarrierObjOppositeOpensCarrierCarrierCommRingCatPresheafOpOpensTop"
p2m_attr_erase "instance" "AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instSMulNat AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instZero AlgebraicCurve.instHasLocalResidue_of_hasCanonicalLocalResidueK AlgebraicCurve.instHasCanonicalLocalResidueK_of_hasCanonicalLocalResidueKStar AlgebraicCurve.Place.kw_ffgc_finiteDimensional_adicCompletion instAlgebraSubtypeMemValuationSubring_definitions AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersIntegersCompletion ModularCurve.KwF4gRRTate.instAlgebraKAdicCompletionIntegers AlgebraicCurve.Place.kw_ffgc_continuousSMul_adicCompletionComap AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersCompletionCompletion IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions AlgebraicCurve.instHasCanonicalLocalResidueK AlgebraicCurve.Place.instAlgebra_restrictResidueField AlgebraicCurve.Place.instIsScalarTower_restrictResidueField AlgebraicCurve.instHasLocalResidue AlgebraicCurve.HasSeparableResidue.of_perfectField_of_isCurveOver AlgebraicCurve.HasSeparableResidue.of_perfectField AlgebraicCurve.Place.instIsLocalHom_restrictSubringHom AlgebraicCurve.instHasCanonicalLocalResidueKStar ModularCurve.KwNo6Pin.isLocalRing_completion SheafOfModules.isIso_ihomModelToIhom AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instDecidableEqIdx AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instFintype AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instLinearOrder AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instFintypeIdx AlgebraicGeometry.OModulePresheaf.instSubsingletonObjZero AlgebraicGeometry.OModulePresheaf.Leray.relAltC_scalarTower AlgebraicGeometry.OModulePresheaf.Leray.ker_relAltd_modΓ AlgebraicGeometry.OModulePresheaf.Leray.relAltC_modΓ AlgebraicGeometry.OModulePresheaf.Leray.biC_abGrp AlgebraicGeometry.OModulePresheaf.Leray.relAltH_modΓ AlgebraicGeometry.OModulePresheaf.Leray.ker_relAltd_smul AlgebraicGeometry.OModulePresheaf.Leray.relAltH_scalarTower AlgebraicGeometry.OModulePresheaf.Leray.relAltH_smul AlgebraicGeometry.OModulePresheaf.Leray.biC_module"
p2m_attr_erase "instance" "DoubleComplex.instModuleE₂I DoubleComplex.Bounded.modR DoubleComplex.instModuleE₂II DoubleComplex.instAddCommGroupE₂II DoubleComplex.Bounded.abGrp DoubleComplex.instAddCommGroupE₂I AlgebraicGeometry.ChowDatum.hι_closed AlgebraicGeometry.ChowDatumProj.hιN_closed AlgebraicGeometry.ChowDatumProj.hp_proper AlgebraicGeometry.ChowDatum.hp_isoU AlgebraicGeometry.ChowDatum.hp_proper AlgebraicGeometry.ProjSpace.algebraAway AlgebraicGeometry.ProjSpace.instIsProperProdOverπ AlgebraicGeometry.ChowDatumProj.hp_isoU AlgebraicGeometry.ProjSpace.isProper_π AlgebraicGeometry.ProjSpace.finiteType_mvPolynomial ProjSpaceCech.GradedModule.H.module ProjSpaceCech.GradedModule.H.addCommGroup ProjSpaceCech.GradedModule.sec.instAdd ProjSpaceCech.GradedModule.sec.instNeg ProjSpaceCech.GradedModule.acg ProjSpaceCech.GradedModule.Frac.setoid ProjSpaceCech.GradedModule.modR ProjSpaceCech.GradedModule.sec.instModule ProjSpaceCech.GradedModule.sec.instAddCommGroup ProjSpaceCech.GradedModule.sec.instZero ProjSpaceCech.GradedModule.Presentation.fJ ProjSpaceCech.GradedModule.sec.instSMul ProjSpaceCech.Twist.H.module ProjSpaceCech.Idx.instFintype ProjSpaceCech.Twist.H.addCommGroup ProjSpaceCech.Idx.instDecidableEq ProjSpaceCech.Twist.Mon.instDecidableEq ProjSpaceCech.Twist.cochain.instAddCommGroup ProjSpaceCech.Twist.cochain.instModule AlgebraicGeometry.FGSubalgebra.tensorStage_directedSystem AlgebraicGeometry.RelEffCartierDiv.isClosedImmersion_subschemeι_resProdMap AlgebraicGeometry.RelEffCartierDiv.isOpenImmersion_resProdMap AlgebraicCurve.CurveModel.locallyOfFiniteType_gluedToBase AlgebraicCurve.CurveModel.isFractionRing_overlap"
p2m_attr_erase "instance" "AlgebraicCurve.CurveModel.isLocallyNoetherian_glued AlgebraicCurve.CurveModel.jacobsonSpace_glued AlgebraicCurve.CurveModel.isOpenImmersion_ι₀ AlgebraicCurve.CurveModel.isIntegral_glued AlgebraicCurve.CurveModel.quasiSeparated_gluedToBase AlgebraicCurve.CurveModel.compactSpace_glued AlgebraicCurve.CurveModel.isIntegral_adjoin_chartRing AlgebraicCurve.CurveModel.isFractionRing_overlap_functionField AlgebraicCurve.CurveModel.isProper_gluedToBase AlgebraicCurve.CurveModel.isOpenImmersion_ιU AlgebraicCurve.CurveModel.isOpenImmersion_f₀ AlgebraicCurve.CurveModel.isOpenImmersion_fInf AlgebraicCurve.CurveModel.isOpenImmersion_ιInf AlgebraicCurve.CurveModel.algebra_overlap_functionField AlgebraicCurve.CurveModel.quasiCompact_gluedToBase AlgebraicCurve.CurveModel.algebraAdjoin AlgebraicCurve.CurveModel.isDedekindDomain_chartRing AlgebraicCurve.CurveModel.isIntegralClosure AlgebraicCurve.CurveModel.finite_chartRing AlgebraicCurve.CurveModel.centre_isPrime AlgebraicCurve.CurveModel.isFractionRing_chartRing AlgebraicCurve.CurveModel.finiteType_chartRing AlgebraicCurve.CurveModel.isNoetherianRing_chartRing AlgebraicCurve.CurveModel.isScalarTower_base_adjoin AlgebraicCurve.CurveModel.isScalarTower_adjoin AlgebraicCurve.CurveModel.chartRing_finitePresentation instTopologicallyFGOfFiniteType AlgebraicGeometry.ProjSpace.twistObj.addCommGroup AlgebraicGeometry.ProjSpace.twistFam.module AlgebraicGeometry.ProjSpace.twistObj.module AlgebraicGeometry.ProjSpace.twistObj.moduleSections AlgebraicGeometry.ProjSpace.twistFam.addCommGroup kmfloorsGlue_int_three_isPrime kmfloorsGlue_int_bot_isPrime"
p2m_attr_erase "simp" "GoodReductionJacobian.relativeGroupLawOfGrpObj_inv GoodReductionJacobian.relativeGroupLawOfGrpObj_mul GoodReductionJacobian.overHomEquivSchemeHomOver_apply_coe GoodReductionJacobian.relativeGroupLawOfGrpObj_one GoodReductionJacobian.overHomEquivSchemeHomOver_symm_apply_left RegularLocalRingQuotientAscent.dualNumberFst_apply SheafOfModules.tensorUnit_eq AlgebraicGeometry.Scheme.Modules.tensorUnit_eq PresheafOfModules.InternalHom.presheaf_map_apply PresheafOfModules.InternalHom.curryFamily_app PresheafOfModules.InternalHom.add_app PresheafOfModules.InternalHom.smul_app PresheafOfModules.InternalHom.zero_app PresheafOfModules.ihomObj_map_val PresheafOfModules.ihomFunctor_map PresheafOfModules.InternalHom.restrict_app PresheafOfModules.InternalHom.postcomp_app PresheafOfModules.InternalHom.neg_app PresheafOfModules.curry'_app_val PresheafOfModules.InternalHom.presheaf_obj PresheafOfModules.ihomFunctor_obj PresheafOfModules.ihomObj_obj PresheafOfModules.InternalHom.sub_app PresheafOfModules.ihomMap_app_val AlgebraicGeometry.Scheme.Modules.tensorPow_zero AlgebraicGeometry.Scheme.Modules.tensorPow_succ AlgebraicGeometry.RelPicard.RigidifiedLineBundle.mk.sizeOf_spec AlgebraicGeometry.RelPicard.RigidifiedLineBundle.mk.injEq AlgebraicGeometry.Scheme.OrderedAffineCover.mk.injEq AlgebraicGeometry.OModulePresheaf.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCover.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.mk.injEq AlgebraicGeometry.Scheme.TwoAffineOpenCover.mk.injEq AlgebraicGeometry.Scheme.TwoAffineOpenCover.mk.sizeOf_spec AlgebraicGeometry.Scheme.TwoAffineOpenCover.pullback_U1 AlgebraicGeometry.Scheme.TwoAffineOpenCover.pullback_U0 TwoChartCech.Sections.mk.injEq TwoChartCech.Cover.mk.injEq TwoChartCech.GrothendieckComplex.mk.injEq TwoChartCech.Sections.mk.sizeOf_spec"
p2m_attr_erase "simp" "TwoChartCech.Cover.mk.sizeOf_spec TwoChartCech.Cover.lineBundle_r0_apply TwoChartCech.GrothendieckComplex.mk.sizeOf_spec TwoChartCech.Cover.lineBundle_r1_apply CoherentBaseChange.TwoTermComplex.mk.sizeOf_spec CoherentBaseChange.TwoTermComplex.mk.injEq PresheafOfModules.freeεIso_hom_app PresheafOfModules.freeμIso_hom_app AlgebraicGeometry.RelPicard.RepresentsRelSubPic.mk.injEq AlgebraicGeometry.RelPicard.SubPicCondition.mk.injEq AlgebraicGeometry.RelPicard.SubPicCondition.mk.sizeOf_spec AlgebraicGeometry.RelPicard.RepresentsRelSubPic.mk.sizeOf_spec AlgebraicGeometry.SmoothProperCurve.sectionBaseChange_coe_snd AlgebraicGeometry.SmoothProperCurve.sectionBaseChange_coe_fst AlgebraicCurve.CurveModel.mk.injEq AlgebraicCurve.CurveModel.mk.sizeOf_spec AlgebraicCurve.mulAdele_apply AlgebraicCurve.residuePairing_apply_coe AlgebraicCurve.mem_adeleBdd AlgebraicCurve.weilSmul_one AlgebraicCurve.diagonalHom_apply AlgebraicCurve.weilSmul_apply AlgebraicCurve.adeleSpaceMul_coe AlgebraicCurve.mulAdele_one AlgebraicGeometry.SmoothProperCurve.FiniteMapData.twoAffineOpenCover_U1 AlgebraicGeometry.SmoothProperCurve.FiniteMapData.mk.injEq AlgebraicGeometry.SmoothProperCurve.FiniteMapData.mk.sizeOf_spec AlgebraicGeometry.SmoothProperCurve.FiniteMapData.twoAffineOpenCover_U0 AlgebraicGeometry.RelPicard.SubPicCondition.onClasses_mk AlgebraicGeometry.RelPicard.relSubPicPresheaf_map_coe CategoryTheory.Functor.OverTotal.ofFibre_fst CategoryTheory.Functor.overTotal_map_fst AlgebraicGeometry.Scheme.LocalRepresentabilityULift.glueData_J AlgebraicGeometry.Scheme.LocalRepresentabilityULift.uliftYoneda_toGlued_uliftYonedaGluedToSheaf AlgebraicGeometry.Scheme.LocalRepresentabilityULift.glueData_t' AlgebraicGeometry.Scheme.LocalRepresentabilityULift.uliftYoneda_toGlued_uliftYonedaGluedToSheaf_assoc AlgebraicGeometry.Scheme.LocalRepresentabilityULift.uliftYonedaGluedToSheaf_app_toGlued AlgebraicGeometry.Scheme.LocalRepresentabilityULift.glueData_openCover_map AlgebraicGeometry.Scheme.LocalRepresentabilityULift.uliftYonedaGluedToSheaf_app_comp AlgebraicGeometry.Scheme.LocalRepresentabilityULift.glueData_V"
p2m_attr_erase "simp" "AlgebraicGeometry.Scheme.LocalRepresentabilityULift.glueData_t AlgebraicGeometry.Scheme.LocalRepresentabilityULift.glueData_U AlgebraicGeometry.Scheme.LocalRepresentabilityULift.glueData_f AlgebraicGeometry.RelPicard.designationOfRepresentableBy_P AlgebraicGeometry.RelPicard.designationOfRepresentableBy_toBase AlgebraicGeometry.RelPicard.rigSection_snd AlgebraicGeometry.RelPicard.RigidifiedLineBundle.ofInvertible_L AlgebraicGeometry.RelPicard.rigSection_snd_assoc AlgebraicGeometry.RelPicard.SubPicGroupCondition.mk.injEq AlgebraicGeometry.RelPicard.SubPicGroupCondition.mk.sizeOf_spec AlgebraicCurve.coe_cechH0Equiv_apply AlgebraicCurve.cechH1ToH1_mk AlgebraicCurve.lSpaceOn_univ AlgebraicCurve.lSpaceOn_empty AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.Divisor.mapRestrict_single AlgebraicCurve.Divisor.pushforward_single AlgebraicCurve.Place.coe_restrictInclusion AlgebraicCurve.Place.mem_fiber AlgebraicCurve.Place.restrict_toValuationSubring AlgebraicCurve.Divisor.degree_pushforward AlgebraicCurve.Place.restrictResidueMap_residue AlgebraicCurve.Pic0.coe_pushforwardDegZeroHom AlgebraicCurve.Pic0.coe_pullbackDegZeroHom AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe"
p2m_attr_erase "simp" "ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Divisor.degree_pushforwardAlong AlgebraicCurve.Pic0.coe_degZeroCorrespondence AlgebraicCurve.Place.mem_fiberAlong AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.jqNModC_one ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one AlgebraicCurve.Place.differentialCoeff_zero AlgebraicCurve.Place.differentialCoeff_dCoord AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.injEq AlgebraicCurve.TranscendenceTower.mk.injEq AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec AlgebraicCurve.PoleDivisorPackage.mk.injEq AlgebraicGeometry.RelPicard.thetaBundle_def AlgebraicGeometry.RelPicard.picardBundle_def AlgebraicGeometry.RelEffCartierDiv.toRelEffDivisor_ofRelEffDivisor"
p2m_attr_erase "simp" "AlgebraicGeometry.RelEffCartierDiv.toRelEffDivisor_I AlgebraicGeometry.mapOnProdOver_fst_assoc AlgebraicGeometry.RelEffCartierDiv.mk.sizeOf_spec AlgebraicGeometry.RelEffCartierDiv.mk.injEq AlgebraicGeometry.mapOnProdOver_snd AlgebraicGeometry.mapOnProdOver_fst AlgebraicGeometry.mapOnProdOver_snd_assoc AlgebraicGeometry.mapOnProdOver_id AlgebraicCurve.RelEffDivisor.mk.sizeOf_spec AlgebraicCurve.mapOnProd_fst AlgebraicCurve.mapOnProd_fst_assoc AlgebraicCurve.mapOnProd_snd AlgebraicCurve.UnivDivisorPack.mk.injEq AlgebraicCurve.RelEffDivisor.mk.injEq AlgebraicCurve.UnivDivisorPack.mk.sizeOf_spec AlgebraicCurve.mapOnProd_snd_assoc AlgebraicGeometry.Scheme.Modules.exteriorPower_obj PresheafOfModules.exteriorPower_map_ιMulti PresheafOfModules.ExteriorPower.appₗ_apply AlgebraicGeometry.prodKerGraph_one AlgebraicGeometry.fibrePowOver.proj_comp AlgebraicGeometry.prodKerGraph_zero AlgebraicGeometry.RelEffCartierDiv.empty_I AlgebraicGeometry.fibrePowOver.proj_comp_assoc AlgebraicGeometry.graphOver_fst_assoc AlgebraicGeometry.RelEffCartierDiv.toPoint_comp AlgebraicGeometry.RelEffCartierDiv.toPoint_comp_assoc AlgebraicGeometry.graphOver_fst AlgebraicGeometry.RelEffCartierDiv.ofPoint_I AlgebraicGeometry.graphOver_snd AlgebraicGeometry.graphOver_snd_assoc AlgebraicCurve.SymmetricPowerPackage.mk.sizeOf_spec AlgebraicCurve.SymmetricPowerPackage.mk.injEq AlgebraicGeometry.FGSubalgebra.cocone_ι_app_apply AlgebraicGeometry.RelPicard.fst_toProdSpec AlgebraicGeometry.RelPicard.toProdSpec_fst_assoc AlgebraicGeometry.RelPicard.pointsSubBasepointModule_cons AlgebraicGeometry.RelPicard.pointsSubBasepointModule_nil AlgebraicGeometry.RelPicard.fst_toProdSpec_assoc AlgebraicGeometry.RelPicard.toProdSpec_fst"
p2m_attr_erase "simp" "AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.sub_app AlgebraicGeometry.Scheme.IdealSheafData.sres_sresTop AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.add_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.mk.sizeOf_spec AlgebraicGeometry.Scheme.IdealSheafData.coe_resLE AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.smul_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.coe_ofLE_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.ideal_range AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.zero_app AlgebraicGeometry.Scheme.IdealSheafData.sres_sres AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.comp_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.neg_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.id_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.coe_mulRight_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.nsmul_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.mk.injEq AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.zsmul_app AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.sizeOf_spec AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.injEq AlgebraicCurve.adeleSingle_coe AlgebraicCurve.kaehlerResidueTermKFam_apply AlgebraicCurve.Place.LocalResidueData.mk.injEq AlgebraicCurve.Place.LocalResidueData.mk.sizeOf_spec AlgebraicCurve.Place.kw_ffgc_adicCompletionComapIntegers_coe AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.sizeOf_spec AlgebraicCurve.Place.mem_simplePoleSubmodule AlgebraicCurve.Place.coe_uniformizerSubring ModularCurve.Lg37.Lg37CompletionSection.mk.injEq AlgebraicCurve.Place.CoefficientFieldSection.mk.injEq AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.injEq ModularCurve.Lg37.Lg37CompletionSection.mk.sizeOf_spec AlgebraicCurve.Place.CoefficientFieldSection.mk.sizeOf_spec AlgebraicCurve.Place.poleSubmodule_one AlgebraicCurve.Place.mem_poleSubmodule AlgebraicGeometry.Scheme.Modules.toUnitSection_ofUnitSection AlgebraicGeometry.Scheme.Modules.pullbackSection_def AlgebraicGeometry.Scheme.Modules.ofUnitSection_toUnitSection PresheafOfModules.InternalHom.IsSheafAux.appAt_toPresheafHom SheafOfModules.ihomSectionsEquivFamily_unit AlgebraicGeometry.Scheme.Modules.restrictHomEquivFamily_apply"
p2m_attr_erase "simp" "SheafOfModules.ihomEval_unit_app AlgebraicGeometry.Scheme.Modules.ihomEval_zero_right AlgebraicGeometry.Scheme.Modules.ihomEval_zero_left AlgebraicGeometry.Scheme.Modules.homOfFamily_app_apply SheafOfModules.unit_ihomSectionsEquivFamily AlgebraicGeometry.Scheme.Modules.familyOfHom_app AlgebraicGeometry.Scheme.Modules.restrictUnitIso_hom_app_apply AlgebraicGeometry.Scheme.Modules.restrictUnitIso_inv_app_apply AlgebraicGeometry.Scheme.Modules.restrictHomOfFamily_app_apply AlgebraicGeometry.Scheme.Modules.restrictHomEquivFamily_symm_apply AlgebraicGeometry.Scheme.Modules.tensorSections_zero_right AlgebraicGeometry.Scheme.Modules.map_unitSection AlgebraicGeometry.Scheme.Modules.tensorSectionsBilin_apply AlgebraicGeometry.Scheme.Modules.tensorPowSection_zero AlgebraicGeometry.Scheme.Modules.tensorSections_zero_left AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_neg AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_zero AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_sub AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_add AlgebraicGeometry.Scheme.OrderedAffineCover.toCoverOf_U AlgebraicGeometry.Scheme.OrderedAffineCoverOf.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCoverOf.mk.injEq AlgebraicGeometry.Scheme.OrderedAffineCover.restrict_U AlgebraicGeometry.OModulePresheaf.Hom.mk.injEq AlgebraicGeometry.OModulePresheaf.Hom.id_app AlgebraicGeometry.OModulePresheaf.AffHom.appSections_apply AlgebraicGeometry.OModulePresheaf.AffHom.comp_app AlgebraicGeometry.OModulePresheaf.AffSES.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.AffHom.kerMap_coe AlgebraicGeometry.OModulePresheaf.AffHom.id_app AlgebraicGeometry.OModulePresheaf.Hom.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.Hom.toAffHom_app AlgebraicGeometry.OModulePresheaf.SES.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.AffHom.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.Hom.comp_app AlgebraicGeometry.OModulePresheaf.SES.mk.injEq AlgebraicGeometry.OModulePresheaf.AffHom.mk.injEq AlgebraicGeometry.OModulePresheaf.Hom.appSections_apply AlgebraicGeometry.OModulePresheaf.AffSES.mk.injEq AlgebraicGeometry.OModulePresheaf.prod_obj"
p2m_attr_erase "simp" "AlgebraicGeometry.OModulePresheaf.restrOpen_obj AlgebraicGeometry.OModulePresheaf.DevissageStep.mk.injEq AlgebraicGeometry.OModulePresheaf.pushforward_obj AlgebraicGeometry.OModulePresheaf.im_obj AlgebraicGeometry.OModulePresheaf.pow_obj AlgebraicGeometry.OModulePresheaf.fstHom_app AlgebraicGeometry.OModulePresheaf.ker_obj AlgebraicGeometry.OModulePresheaf.coker_obj AlgebraicGeometry.OModulePresheaf.DevissageStep.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCover.preimage_U AlgebraicGeometry.OModulePresheaf.sndHom_app AlgebraicGeometry.OModulePresheaf.Leray.restrictToPreimage_U DoubleComplex.Bounded.mk.injEq DoubleComplex.Bounded.mk.sizeOf_spec DoubleComplex.Convergence.mk.injEq DoubleComplex.Convergence.mk.sizeOf_spec DoubleComplex.SubQuot.mk.sizeOf_spec DoubleComplex.SubQuot.mk.injEq AlgebraicGeometry.ChowDatumProj.mk.sizeOf_spec AlgebraicGeometry.ChowDatum.mk.sizeOf_spec AlgebraicGeometry.ChowDatumProj.mk.injEq AlgebraicGeometry.ChowDatum.mk.injEq ProjSpaceCech.GradedModule.mk.injEq ProjSpaceCech.GradedModule.mk.sizeOf_spec ProjSpaceCech.GradedModule.Frac.mk.sizeOf_spec ProjSpaceCech.GradedModule.Presentation.mk.injEq ProjSpaceCech.GradedModule.Frac.mk.injEq ProjSpaceCech.GradedModule.Presentation.mk.sizeOf_spec ProjSpaceCech.GradedModule.Hom.shift_toLinearMap ProjSpaceCech.GradedModule.Hom.mk.sizeOf_spec ProjSpaceCech.GradedModule.Hom.mk.injEq TwoChartCech.Mumford.dK_apply TwoChartCech.Mumford.ι0_apply TwoChartCech.Mumford.ι1_apply TwoChartCech.KerCoprod.dK_apply TwoChartCech.KerCoprod.ι1_apply TwoChartCech.KerCoprod.ι0_apply AlgebraicGeometry.tilde.functorCompPullbackSpecIso_app AlgebraicGeometry.RelPicard.algEquivZeroGroupCut_toSubPicCondition AlgebraicGeometry.RelPicard.LFP.stageHom_val"
p2m_attr_erase "simp" "AlgebraicGeometry.RelPicard.BaseChange.relSubPicPresheafRestrictIso_hom_app_coe AlgebraicGeometry.RelPicard.BaseChange.relSubPicPresheafRestrictIso_inv_app_coe AlgebraicGeometry.RelPicard.BaseChange.restrict_P AlgebraicGeometry.RelEffCartierDiv.IsUniversal.lift_comp AlgebraicGeometry.RelEffCartierDiv.functor_map_fst AlgebraicGeometry.RelEffCartierDiv.IsUniversal.homEquiv_apply AlgebraicGeometry.RelEffCartierDiv.IsUniversal.lift_pullbackAlong AlgebraicGeometry.RelEffCartierDiv.IsUniversal.homEquiv_symm_apply AlgebraicGeometry.RelEffCartierDiv.IsUniversal.lift_comp_assoc AlgebraicGeometry.RelEffCartierDiv.supportedIn_top AlgebraicGeometry.RelEffCartierDiv.mem_supportedIn_iff AlgebraicGeometry.RelEffCartierDiv.supportedIn_top_eq AlgebraicGeometry.RelEffCartierDiv.restrictAlong_extendAlong AlgebraicGeometry.RelEffCartierDiv.extendAlong_I AlgebraicGeometry.RelEffCartierDiv.resProdMap_snd AlgebraicGeometry.RelEffCartierDiv.restrictAlong_I AlgebraicGeometry.RelEffCartierDiv.extendAlong_restrictAlong AlgebraicGeometry.RelEffCartierDiv.resProdMap_fst_assoc AlgebraicGeometry.RelEffCartierDiv.resProdMap_snd_assoc AlgebraicGeometry.RelEffCartierDiv.resProdMap_fst CoherentBaseChange.FibreH0Family.mk.sizeOf_spec CoherentBaseChange.FibreH0Family.mk.injEq AlgebraicGeometry.Scheme.Modules.ProjPresentation.mk.injEq AlgebraicGeometry.Scheme.Modules.ProjPresentation.mk.sizeOf_spec AlgebraicCurve.CurveModel.coe_gInf AlgebraicCurve.CurveModel.coe_tInvChart AlgebraicCurve.CurveModel.ιInf_gluedToBase_assoc AlgebraicCurve.CurveModel.ιInf_gluedToBase AlgebraicCurve.CurveModel.primeOfι₀_asIdeal AlgebraicCurve.CurveModel.coe_tChart AlgebraicCurve.CurveModel.ι₀_gluedToBase_assoc AlgebraicCurve.CurveModel.primeOfιInf_asIdeal AlgebraicCurve.CurveModel.ι₀_gluedToBase AlgebraicCurve.CurveModel.coe_tma AlgebraicCurve.CurveModel.coe_primeEquivChartPlaces AlgebraicGeometry.ProjSpace.twistObj.mk.injEq AlgebraicGeometry.ProjSpace.twistObj.zero_val AlgebraicGeometry.ProjSpace.twistObj.add_val AlgebraicGeometry.ProjSpace.twist_res_val AlgebraicGeometry.ProjSpace.twist_smul_val"
p2m_attr_erase "simp" "AlgebraicGeometry.ProjSpace.twistGradeToObj_val AlgebraicGeometry.ProjSpace.twistObj.smul_val AlgebraicGeometry.ProjSpace.twistGradeEquiv_apply_val AlgebraicGeometry.ProjSpace.twistObj.mk.sizeOf_spec GoodReductionJacobian.RelativeGroupLaw.fibre_inv GoodReductionJacobian.RelativeGroupLaw.fibrePointToBase_coe GoodReductionJacobian.RelativeGroupLaw.fibrePointOfBase_toBase GoodReductionJacobian.RelativeGroupLaw.fibre_mul GoodReductionJacobian.RelativeGroupLaw.fibrePointToBase_ofBase GoodReductionJacobian.RelativeGroupLaw.fibre_one GoodReductionJacobian.RelativeGroupLaw.fibrePointOfBase_coe AlgebraicGeometry.schemeFibreEndo_snd AlgebraicGeometry.schemeFibreEndo_fst"

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian IsDedekindDomain AlgebraicCurve QuaternionAlgebra CerednikDrinfeld CerednikDrinfeld.QM

open scoped Quaternion TensorProduct NumberField

universe u

namespace P2mKcDefOrScalarSq

section Alg

variable {G : Type*} [CommGroup G]

theorem comp_alg (σ : G →* G) (t n s : ℤ) (hs : (t + s) * (t - s) = 4 * n)
    (h1 : ∀ P, σ (σ P) * P ^ n = σ P ^ t) (P : G) :
    σ (σ P ^ (2 : ℤ) * P ^ (-(t - s))) ^ (2 : ℤ) * (σ P ^ (2 : ℤ) * P ^ (-(t - s))) ^ (-(t + s)) = 1 := by
  have a : Additive.ofMul (σ (σ P)) + n • Additive.ofMul P = t • Additive.ofMul (σ P) := by
    have := congrArg Additive.ofMul (h1 P)
    simpa [ofMul_mul, ofMul_zpow] using this
  have a4 : (4 : ℤ) • Additive.ofMul (σ (σ P)) + ((t + s) * (t - s)) • Additive.ofMul P =
      (4 * t) • Additive.ofMul (σ P) := by
    rw [hs, mul_smul, mul_smul, ← smul_add, a]
  rw [← ofMul_eq_zero]
  simp only [map_mul, map_zpow, ofMul_mul, ofMul_zpow]
  linear_combination (norm := module) a4

theorem even_alg (σ : G →* G) (t n u : ℤ)
    (h1 : ∀ P, σ (σ P) * P ^ n = σ P ^ t) (hu : ∀ P, σ P ^ (2 : ℤ) = P ^ u) (P : G) :
    P ^ (u ^ 2 - 2 * t * u + 4 * n) = 1 := by
  have a : Additive.ofMul (σ (σ P)) + n • Additive.ofMul P = t • Additive.ofMul (σ P) := by
    have := congrArg Additive.ofMul (h1 P)
    simpa [ofMul_mul, ofMul_zpow] using this
  have b : (2 : ℤ) • Additive.ofMul (σ P) = u • Additive.ofMul P := by
    have := congrArg Additive.ofMul (hu P)
    first | simpa [ofMul_zpow] using this | (have h_1 := this; simp [ofMul_zpow] at h_1; exact h_1) | (have h_1 := this; simp [ofMul_zpow] at h_1 ⊢; exact h_1) | exact (this)
  have c : (2 : ℤ) • Additive.ofMul (σ (σ P)) = u • Additive.ofMul (σ P) := by
    have := congrArg Additive.ofMul (hu (σ P))
    first | (rwa [ofMul_zpow, ofMul_zpow] at this) | (rw [← map_zpow] at this; simpa [ofMul_zpow, map_zpow] using this)
  rw [← ofMul_eq_zero]
  simp only [ofMul_zpow]
  linear_combination (norm := module) (4 : ℤ) • a - (2 : ℤ) • c - (u - 2 * t) • b

theorem chi_alg (σ : G →* G) (u c : ℤ) (hc : u = c + c) (hu : ∀ P, σ P ^ (2 : ℤ) = P ^ u) (P : G) :
    σ (σ P ^ (0 : ℤ) * P ^ (2 : ℤ)) ^ (1 : ℤ) * (σ P ^ (0 : ℤ) * P ^ (2 : ℤ)) ^ (-c) = 1 := by
  have b : (2 : ℤ) • Additive.ofMul (σ P) = u • Additive.ofMul P := by
    have := congrArg Additive.ofMul (hu P)
    first | simpa [ofMul_zpow] using this | (have h_1 := this; simp [ofMul_zpow] at h_1; exact h_1) | (have h_1 := this; simp [ofMul_zpow] at h_1 ⊢; exact h_1) | exact (this)
  rw [← ofMul_eq_zero]
  simp only [map_mul, map_zpow, ofMul_mul, ofMul_zpow, hc] at b ⊢
  linear_combination (norm := module) b

end Alg

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

section Endo

variable {K : Type u} [CommRing K] {A : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of K)}

theorem mapPt_mul_pt (L : RelativeGroupLaw K f) {T : Scheme.{u}} {s : T ⟶ Spec (CommRingCat.of K)}
    (P : SchemeHomOver s f) (β γ : SchemeHomOver f f) :
    mapPt (L.mul f β γ).1 (L.mul f β γ).2 P = L.mul s (mapPt β.1 β.2 P) (mapPt γ.1 γ.2 P) :=
  L.mul_natural f s P.1 P.2 β γ

theorem mapPt_one_pt (L : RelativeGroupLaw K f) {T : Scheme.{u}} {s : T ⟶ Spec (CommRingCat.of K)}
    (P : SchemeHomOver s f) :
    mapPt (L.one f).1 (L.one f).2 P = L.one s :=
  L.one_natural f s P.1 P.2

theorem mapPt_idPoint (β : SchemeHomOver f f) :
    mapPt β.1 β.2 (RelativeGroupLaw.idPoint : SchemeHomOver f f) = β := by
  apply Subtype.ext
  simp [mapPt]

theorem mapPt_id {T : Scheme.{u}} {s : T ⟶ Spec (CommRingCat.of K)} (Q : SchemeHomOver s f) :
    mapPt (RelativeGroupLaw.idPoint : SchemeHomOver f f).1 (RelativeGroupLaw.idPoint : SchemeHomOver f f).2 Q = Q := by
  apply Subtype.ext
  simp [mapPt]

theorem mapPt_mapPt (φ : A ⟶ A) (hφ : φ ≫ f = f) (ψ : A ⟶ A) (hψ : ψ ≫ f = f)
    {T : Scheme.{u}} {s : T ⟶ Spec (CommRingCat.of K)} (P : SchemeHomOver s f) :
    mapPt ψ hψ (mapPt φ hφ P) = mapPt (φ ≫ ψ) (by rw [Category.assoc, hψ, hφ]) P := by
  apply Subtype.ext
  simp [mapPt]

end Endo

section Frame

variable {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} {N : ℕ} {k : Type u} [Field k]

noncomputable def lin (E : FakeEllipticCurve Λ N k) (φ : E.A ⟶ E.A) (hφ : φ ≫ E.f = E.f) (α β : ℤ) :
    SchemeHomOver E.f E.f :=
  letI := E.L.pointCommGroup E.comm E.f
  (⟨φ, hφ⟩ : SchemeHomOver E.f E.f) ^ α * (RelativeGroupLaw.idPoint : SchemeHomOver E.f E.f) ^ β

theorem mapPt_lin (E : FakeEllipticCurve Λ N k) (φ : E.A ⟶ E.A) (hφ : φ ≫ E.f = E.f) (α β : ℤ)
    {T : Scheme.{u}} (s : T ⟶ Spec (CommRingCat.of k)) (P : SchemeHomOver s E.f) :
    letI := E.L.pointCommGroup E.comm s
    mapPt (lin E φ hφ α β).1 (lin E φ hφ α β).2 P = mapPt φ hφ P ^ α * P ^ β := by
  letI := E.L.pointCommGroup E.comm s
  letI := E.L.pointCommGroup E.comm E.f
  let ev : SchemeHomOver E.f E.f →* SchemeHomOver s E.f :=
    MonoidHom.mk' (fun β => mapPt β.1 β.2 P) (fun β γ => mapPt_mul_pt E.L P β γ)
  have hev : ∀ β : SchemeHomOver E.f E.f, mapPt β.1 β.2 P = ev β := fun _ => rfl
  rw [hev, lin, map_mul, map_zpow, map_zpow]
  show mapPt φ hφ P ^ α * mapPt (RelativeGroupLaw.idPoint : SchemeHomOver E.f E.f).1
    (RelativeGroupLaw.idPoint : SchemeHomOver E.f E.f).2 P ^ β = _
  rw [mapPt_id]

theorem lin_hom (E : FakeEllipticCurve Λ N k) (φ : E.A ⟶ E.A) (hφ : φ ≫ E.f = E.f)
    (hmul : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of k)) (P Q : SchemeHomOver t E.f),
      mapPt φ hφ (E.L.mul t P Q) = E.L.mul t (mapPt φ hφ P) (mapPt φ hφ Q))
    (α β : ℤ) {T : Scheme.{u}} (s : T ⟶ Spec (CommRingCat.of k)) (P Q : SchemeHomOver s E.f) :
    mapPt (lin E φ hφ α β).1 (lin E φ hφ α β).2 (E.L.mul s P Q) =
      E.L.mul s (mapPt (lin E φ hφ α β).1 (lin E φ hφ α β).2 P) (mapPt (lin E φ hφ α β).1 (lin E φ hφ α β).2 Q) := by
  letI := E.L.pointCommGroup E.comm s
  let σ : SchemeHomOver s E.f →* SchemeHomOver s E.f := MonoidHom.mk' (fun R => mapPt φ hφ R) (fun R S => hmul s R S)
  have hσ : ∀ R : SchemeHomOver s E.f, mapPt φ hφ R = σ R := fun _ => rfl
  show mapPt (lin E φ hφ α β).1 (lin E φ hφ α β).2 (P * Q) =
    mapPt (lin E φ hφ α β).1 (lin E φ hφ α β).2 P * mapPt (lin E φ hφ α β).1 (lin E φ hφ α β).2 Q
  rw [mapPt_lin, mapPt_lin, mapPt_lin, hσ, hσ, hσ, map_mul, mul_zpow, mul_zpow]
  simp only [mul_assoc, mul_left_comm]

theorem lin_act (E : FakeEllipticCurve Λ N k) (φ : E.A ⟶ E.A) (hφ : φ ≫ E.f = E.f)
    (hact : ∀ x : ↥Λ, E.act x ≫ φ = φ ≫ E.act x) (α β : ℤ) (x : ↥Λ) :
    E.act x ≫ (lin E φ hφ α β).1 = (lin E φ hφ α β).1 ≫ E.act x := by
  letI := E.L.pointCommGroup E.comm E.f

  let aP : SchemeHomOver E.f E.f := ⟨E.act x, E.act_over x⟩

  let ρ : SchemeHomOver E.f E.f →* SchemeHomOver E.f E.f :=
    MonoidHom.mk' (fun R => pushPt (E.act x) (E.act_over x) R) (fun R S => E.act_hom x E.f R S)

  let ev : SchemeHomOver E.f E.f →* SchemeHomOver E.f E.f :=
    MonoidHom.mk' (fun β => mapPt β.1 β.2 aP) (fun β γ => mapPt_mul_pt E.L aP β γ)
  have h1 : ev ⟨φ, hφ⟩ = ρ ⟨φ, hφ⟩ := by
    apply Subtype.ext
    show E.act x ≫ φ = φ ≫ E.act x
    exact hact x
  have h2 : ev RelativeGroupLaw.idPoint = ρ RelativeGroupLaw.idPoint := by
    apply Subtype.ext
    show E.act x ≫ 𝟙 E.A = 𝟙 E.A ≫ E.act x
    simp
  have h : ev (lin E φ hφ α β) = ρ (lin E φ hφ α β) := by
    simp only [lin, map_mul, map_zpow, h1, h2]
  exact congrArg Subtype.val h

theorem eq_one_of_forall_mapPt (E : FakeEllipticCurve Λ N k) (β : SchemeHomOver E.f E.f)
    (h : ∀ {T : Scheme.{u}} (s : T ⟶ Spec (CommRingCat.of k)) (P : SchemeHomOver s E.f),
      mapPt β.1 β.2 P = E.L.one s) : β = E.L.one E.f := by
  rw [← mapPt_idPoint β]
  exact h E.f _

end Frame

theorem cancel
    {q q' : ℕ} [Fact q.Prime] [Fact q'.Prime] (hqq' : q' ≠ q)
    {a b : ℚ} (hB : IsIndefiniteRamifiedExactlyAt a b q q')
    (Λ : Submodule ℤ ℍ[ℚ, a, b]) (hΛ : IsMaximalOrder Λ) {N : ℕ}
    (k : Type u) [Field k] [IsAlgClosed k] (E : FakeEllipticCurve Λ N k)
    (β γ : SchemeHomOver E.f E.f)
    (hβmul : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of k)) (P Q : SchemeHomOver t E.f),
      mapPt β.1 β.2 (E.L.mul t P Q) = E.L.mul t (mapPt β.1 β.2 P) (mapPt β.1 β.2 Q))
    (hβact : ∀ x : ↥Λ, E.act x ≫ β.1 = β.1 ≫ E.act x)
    (hγmul : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of k)) (P Q : SchemeHomOver t E.f),
      mapPt γ.1 γ.2 (E.L.mul t P Q) = E.L.mul t (mapPt γ.1 γ.2 P) (mapPt γ.1 γ.2 Q))
    (hγact : ∀ x : ↥Λ, E.act x ≫ γ.1 = γ.1 ≫ E.act x)
    (h : ∀ {T : Scheme.{u}} (s : T ⟶ Spec (CommRingCat.of k)) (P : SchemeHomOver s E.f),
      mapPt β.1 β.2 (mapPt γ.1 γ.2 P) = E.L.one s) :
    β = E.L.one E.f ∨ γ = E.L.one E.f := by
  haveI := CerednikDrinfeld.QM.FakeEllipticCurve.smoothOfRelativeDimension_two k E
  by_contra hne
  obtain ⟨hβne, hγne⟩ := not_or.mp hne

  have hβdeg := CerednikDrinfeld.QM.FakeEllipticCurve.endDegree_ne_zero_of_forall_act_comp_eq_of_ne_one
    hqq' hB Λ hΛ k E β.1 β.2 hβmul hβact hβne
  have hγdeg := CerednikDrinfeld.QM.FakeEllipticCurve.endDegree_ne_zero_of_forall_act_comp_eq_of_ne_one
    hqq' hB Λ hΛ k E γ.1 γ.2 hγmul hγact hγne
  have hβfin : IsFinite (E.L.endKerStr β) := by
    by_contra hf
    exact hβdeg (E.L.endDegree_of_not_isFinite β hf)
  have hγfin : IsFinite (E.L.endKerStr γ) := by
    by_contra hf
    exact hγdeg (E.L.endDegree_of_not_isFinite γ hf)

  obtain ⟨M, hM, hkβ⟩ :=
    GoodReductionJacobian.RelativeGroupLaw.exists_forall_nsmul_eq_one_of_isFinite_pullback_snd
      E.L E.comm E.L β (fun t x y => hβmul t x y) hβfin
  obtain ⟨M', hM', hkγ⟩ :=
    GoodReductionJacobian.RelativeGroupLaw.exists_forall_nsmul_eq_one_of_isFinite_pullback_snd
      E.L E.comm E.L γ (fun t x y => hγmul t x y) hγfin

  have hkill : ((M * M' : ℕ) : ℤ) = 0 := by
    apply eq_zero_of_forall_zpow_eq_one E.L E.comm E.bundle
    intro P
    letI := E.L.pointCommGroup E.comm (𝟙 (Spec (CommRingCat.of k)))
    let σ : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) E.f →* SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) E.f :=
      MonoidHom.mk' (fun R => mapPt γ.1 γ.2 R) (fun R S => hγmul _ R S)
    have h1 : mapPt γ.1 γ.2 P ^ M = 1 := by
      rw [← nsmul_eq_pow E.L E.comm]
      exact hkβ _ (mapPt γ.1 γ.2 P) (h _ P)
    have h2 : mapPt γ.1 γ.2 (P ^ M) = 1 := by
      show σ (P ^ M) = 1
      rw [map_pow]
      exact h1
    have h3 : (P ^ M) ^ M' = 1 := by
      rw [← nsmul_eq_pow E.L E.comm]
      exact hkγ _ (P ^ M) h2
    rw [zpow_natCast, pow_mul, h3]
  have : M * M' = 0 := by exact_mod_cast hkill
  rcases Nat.mul_eq_zero.mp this with h0 | h0 <;> omega

theorem main
    {q q' : ℕ} [Fact q.Prime] [Fact q'.Prime] (hqq' : q' ≠ q)
    {a b : ℚ} (hB : IsIndefiniteRamifiedExactlyAt a b q q')
    (Λ : Submodule ℤ ℍ[ℚ, a, b]) (hΛ : IsMaximalOrder Λ) {N : ℕ}
    (k : Type u) [Field k] [IsAlgClosed k] (E : FakeEllipticCurve Λ N k)
    (φ : E.A ⟶ E.A) (hφ : φ ≫ E.f = E.f)
    (hmul : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of k)) (P Q : SchemeHomOver t E.f),
      mapPt φ hφ (E.L.mul t P Q) = E.L.mul t (mapPt φ hφ P) (mapPt φ hφ Q))
    (hact : ∀ x : ↥Λ, E.act x ≫ φ = φ ≫ E.act x)
    (t n : ℤ)
    (hquad : ∀ {T : Scheme.{u}} (s : T ⟶ Spec (CommRingCat.of k)) (P : SchemeHomOver s E.f),
      letI := E.L.pointCommGroup E.comm s
      mapPt φ hφ (mapPt φ hφ P) * P ^ n = mapPt φ hφ P ^ t)
    (hsq : IsSquare (t ^ 2 - 4 * n)) :
    ∃ c : ℤ, ∀ {T : Scheme.{u}} (s : T ⟶ Spec (CommRingCat.of k)) (P : SchemeHomOver s E.f),
      letI := E.L.pointCommGroup E.comm s
      mapPt φ hφ P = P ^ c := by
  haveI := CerednikDrinfeld.QM.FakeEllipticCurve.smoothOfRelativeDimension_two k E
  obtain ⟨r, hr⟩ := hsq
  have hrs : (t + r) * (t - r) = 4 * n := by linear_combination hr

  have hσ : ∀ {T : Scheme.{u}} (s : T ⟶ Spec (CommRingCat.of k)),
      ∃ σ : (letI := E.L.pointCommGroup E.comm s; SchemeHomOver s E.f →* SchemeHomOver s E.f),
        ∀ R, σ R = mapPt φ hφ R := by
    intro T s
    letI := E.L.pointCommGroup E.comm s
    exact ⟨MonoidHom.mk' (fun R => mapPt φ hφ R) (fun R S => hmul s R S), fun _ => rfl⟩

  have hcomp : ∀ {T : Scheme.{u}} (s : T ⟶ Spec (CommRingCat.of k)) (P : SchemeHomOver s E.f),
      mapPt (lin E φ hφ 2 (-(t + r))).1 (lin E φ hφ 2 (-(t + r))).2
        (mapPt (lin E φ hφ 2 (-(t - r))).1 (lin E φ hφ 2 (-(t - r))).2 P) = E.L.one s := by
    intro T s P
    letI := E.L.pointCommGroup E.comm s
    obtain ⟨σ, hσ⟩ := hσ s
    rw [mapPt_lin, mapPt_lin, ← hσ, ← hσ]
    exact comp_alg σ t n r hrs (fun R => by rw [hσ, hσ]; exact hquad s R) P

  have hu : ∃ u : ℤ, ∀ {T : Scheme.{u}} (s : T ⟶ Spec (CommRingCat.of k)) (P : SchemeHomOver s E.f),
      letI := E.L.pointCommGroup E.comm s
      mapPt φ hφ P ^ (2 : ℤ) = P ^ u := by
    rcases cancel hqq' hB Λ hΛ k E (lin E φ hφ 2 (-(t + r))) (lin E φ hφ 2 (-(t - r)))
        (lin_hom E φ hφ hmul 2 _) (lin_act E φ hφ hact 2 _)
        (lin_hom E φ hφ hmul 2 _) (lin_act E φ hφ hact 2 _) hcomp with h0 | h0
    · refine ⟨t + r, fun s P => ?_⟩
      letI := E.L.pointCommGroup E.comm s
      have h1 : mapPt (lin E φ hφ 2 (-(t + r))).1 (lin E φ hφ 2 (-(t + r))).2 P = 1 := by
        rw [h0]; exact mapPt_one_pt E.L P
      rw [mapPt_lin] at h1
      rw [← mul_inv_eq_one, ← zpow_neg]
      exact h1
    · refine ⟨t - r, fun s P => ?_⟩
      letI := E.L.pointCommGroup E.comm s
      have h1 : mapPt (lin E φ hφ 2 (-(t - r))).1 (lin E φ hφ 2 (-(t - r))).2 P = 1 := by
        rw [h0]; exact mapPt_one_pt E.L P
      rw [mapPt_lin] at h1
      rw [← mul_inv_eq_one, ← zpow_neg]
      exact h1
  obtain ⟨u, hu⟩ := hu

  have hpoly : u ^ 2 - 2 * t * u + 4 * n = 0 := by
    apply eq_zero_of_forall_zpow_eq_one E.L E.comm E.bundle
    intro P
    letI := E.L.pointCommGroup E.comm (𝟙 (Spec (CommRingCat.of k)))
    obtain ⟨σ, hσ⟩ := hσ (𝟙 (Spec (CommRingCat.of k)))
    exact even_alg σ t n u (fun R => by rw [hσ, hσ]; exact hquad _ R) (fun R => by rw [hσ]; exact hu _ R) P
  have heven : Even u := by
    have h2 : Even (u ^ 2) := ⟨t * u - 2 * n, by linear_combination hpoly⟩
    exact (Int.even_pow.mp h2).1
  obtain ⟨c, hc⟩ := heven

  refine ⟨c, ?_⟩
  have hcomp2 : ∀ {T : Scheme.{u}} (s : T ⟶ Spec (CommRingCat.of k)) (P : SchemeHomOver s E.f),
      mapPt (lin E φ hφ 1 (-c)).1 (lin E φ hφ 1 (-c)).2
        (mapPt (lin E φ hφ 0 2).1 (lin E φ hφ 0 2).2 P) = E.L.one s := by
    intro T s P
    letI := E.L.pointCommGroup E.comm s
    obtain ⟨σ, hσ⟩ := hσ s
    rw [mapPt_lin, mapPt_lin, ← hσ, ← hσ]
    exact chi_alg σ u c hc (fun R => by rw [hσ]; exact hu s R) P
  rcases cancel hqq' hB Λ hΛ k E (lin E φ hφ 1 (-c)) (lin E φ hφ 0 2)
      (lin_hom E φ hφ hmul 1 _) (lin_act E φ hφ hact 1 _)
      (lin_hom E φ hφ hmul 0 _) (lin_act E φ hφ hact 0 _) hcomp2 with h0 | h0
  · intro T s P
    letI := E.L.pointCommGroup E.comm s
    have h1 : mapPt (lin E φ hφ 1 (-c)).1 (lin E φ hφ 1 (-c)).2 P = 1 := by
      rw [h0]; exact mapPt_one_pt E.L P
    rw [mapPt_lin, zpow_one, zpow_neg, mul_inv_eq_one] at h1
    exact h1
  · exfalso
    have h2 : (2 : ℤ) = 0 := by
      apply eq_zero_of_forall_zpow_eq_one E.L E.comm E.bundle
      intro P
      letI := E.L.pointCommGroup E.comm (𝟙 (Spec (CommRingCat.of k)))
      have h1 : mapPt (lin E φ hφ 0 2).1 (lin E φ hφ 0 2).2 P = 1 := by
        rw [h0]; exact mapPt_one_pt E.L P
      rw [mapPt_lin, zpow_zero, one_mul] at h1
      exact h1
    omega

end P2mKcDefOrScalarSq

open P2mKcDefOrScalarSq

theorem solution
    {q q' : ℕ} [Fact q.Prime] [Fact q'.Prime] (hqq' : q' ≠ q)
    {a b : ℚ} (hB : IsIndefiniteRamifiedExactlyAt a b q q')
    (Λ : Submodule ℤ ℍ[ℚ, a, b]) (hΛ : IsMaximalOrder Λ) {N : ℕ}
    (k : Type u) [Field k] [IsAlgClosed k] (E : FakeEllipticCurve Λ N k)
    (φ : E.A ⟶ E.A) (hφ : φ ≫ E.f = E.f)
    (hmul : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of k)) (P Q : SchemeHomOver t E.f),
      mapPt φ hφ (E.L.mul t P Q) = E.L.mul t (mapPt φ hφ P) (mapPt φ hφ Q))
    (hact : ∀ x : ↥Λ, E.act x ≫ φ = φ ≫ E.act x)
    (t n : ℤ)
    (hquad : ∀ {T : Scheme.{u}} (s : T ⟶ Spec (CommRingCat.of k)) (P : SchemeHomOver s E.f),
      letI := E.L.pointCommGroup E.comm s
      mapPt φ hφ (mapPt φ hφ P) * P ^ n = mapPt φ hφ P ^ t)
    (hsq : IsSquare (t ^ 2 - 4 * n)) :
    ∃ c : ℤ, ∀ {T : Scheme.{u}} (s : T ⟶ Spec (CommRingCat.of k)) (P : SchemeHomOver s E.f),
      letI := E.L.pointCommGroup E.comm s
      mapPt φ hφ P = P ^ c :=
  main hqq' hB Λ hΛ k E φ hφ hmul hact t n hquad hsq

end S_CerednikDrinfeld_QM_FakeEllipticCurve_exists_forall_mapPt_eq_zpow_of_forall_act_comp_eq_of_isSquare
end P2MW
export P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_exists_forall_mapPt_eq_zpow_of_forall_act_comp_eq_of_isSquare (solution)
