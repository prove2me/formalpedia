-- Prove2me | solution 1 for CerednikDrinfeld.QM.FakeEllipticCurve.exists_forall_mapPt_mapPt_mul_zpow_eq_zpow_of_forall_act_comp_eq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.837917+00:00
-- url     : https://prove2.me/submissions/9a491e56-4d25-5a63-b495-882fb6aa3815

import Definitions.Def_CerednikDrinfeld_QMModuli
import Definitions.Def_AlgebraicGeometry_RelativeGroupLawEndDegree
import Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_exists_existsUnique_eq_prod_zpow_of_forall_comm_of_forall_endDegree_ne_zero
import Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_endDegree_ne_zero_of_forall_act_comp_eq_of_ne_one
import Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_exists_eq_pow_of_forall_isTorsionPoint_schemeHomOverComp_eq_one
import Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_natCard_isTorsionPoint_eq_pow_of_natCast_ne_zero
import Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_smoothOfRelativeDimension_two
import Theorems.Thm_QuaternionAlgebra_exists_linearMap_matrix_zmod_of_isMaximalOrder_of_ne
import Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_nsmul_surjective_of_isAlgClosed_of_connectedSpace
import Theorems.Thm_AlgebraicGeometry_SchemeHomOver_ext_of_forall_point_of_isReduced_of_locallyOfFiniteType
import Theorems.Thm_AlgebraicGeometry_Smooth_isReduced_of_isReduced_of_isLocallyNoetherian
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_exists_forall_mapPt_mapPt_mul_zpow_eq_zpow_of_forall_act_comp_eq
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

noncomputable section

universe u

namespace P2mKcQuadIntV2

open Module Polynomial

section RankBound

theorem finrank_le_of_ker_le_smul {S W : Type*} [AddCommGroup S] [Module.Free ℤ S] [Module.Finite ℤ S]
    [AddCommGroup W] [Finite W] {ℓ d : ℕ} (hℓ : 1 < ℓ) (hW : Nat.card W ≤ ℓ ^ d) (ev : S →+ W)
    (hker : ∀ x, ev x = 0 → ∃ y : S, x = (ℓ : ℤ) • y) : finrank ℤ S ≤ d := by
  classical
  haveI := Fintype.ofFinite W
  set s := finrank ℤ S
  let B := Module.finBasis ℤ S
  let F : (Fin s → Fin ℓ) → W := fun x => ev (∑ i, ((x i : ℕ) : ℤ) • B i)
  have hF : Function.Injective F := by
    intro x x' hxx'
    have h0 : ev (∑ i, (((x i : ℕ) : ℤ) - ((x' i : ℕ) : ℤ)) • B i) = 0 := by
      simp only [sub_smul, Finset.sum_sub_distrib, map_sub]
      exact sub_eq_zero.mpr hxx'
    obtain ⟨y, hy⟩ := hker _ h0
    have hcoord : ∀ i, (((x i : ℕ) : ℤ) - ((x' i : ℕ) : ℤ)) = (ℓ : ℤ) * B.equivFun y i := fun i => by
      have h1 : B.equivFun (∑ i, (((x i : ℕ) : ℤ) - ((x' i : ℕ) : ℤ)) • B i) =
          fun i => (((x i : ℕ) : ℤ) - ((x' i : ℕ) : ℤ)) := by
        rw [← B.equivFun_symm_apply, LinearEquiv.apply_symm_apply]
      have h2 := congrFun h1 i
      rw [hy, map_smul] at h2
      simpa [eq_comm] using h2
    funext i
    have hdvd : (ℓ : ℤ) ∣ (((x i : ℕ) : ℤ) - ((x' i : ℕ) : ℤ)) := ⟨_, hcoord i⟩
    have hlt : |(((x i : ℕ) : ℤ) - ((x' i : ℕ) : ℤ))| < (ℓ : ℤ) := by
      have h1 := (x i).2
      have h2 := (x' i).2
      rw [abs_sub_lt_iff]; constructor <;> omega
    have := Int.eq_zero_of_abs_lt_dvd hdvd hlt
    exact Fin.ext (by omega)
  have hcard := Fintype.card_le_of_injective F hF
  rw [Fintype.card_fun, Fintype.card_fin, Fintype.card_fin, Fintype.card_eq_nat_card] at hcard
  exact (Nat.pow_le_pow_iff_right hℓ).mp (hcard.trans hW)

end RankBound

section CyclicVector

variable {F W : Type*} [Field F] [AddCommGroup W] [Module F W] [FiniteDimensional F W]

theorem exists_eq_smul_one_of_forall (h2 : finrank F W = 2) (x : Module.End F W)
    (hx : ∀ v : W, ¬ LinearIndependent F ![v, x v]) : ∃ a : F, x = a • 1 := by
  have hev : ∀ v : W, v ≠ 0 → ∃ a : F, x v = a • v := by
    intro v hv
    have := hx v
    rw [LinearIndependent.pair_iff] at this
    push Not at this
    obtain ⟨s, t, hst, hne⟩ := this
    by_cases ht : t = 0
    · subst ht
      simp only [zero_smul, add_zero, smul_eq_zero] at hst
      rcases hst with hs | hs
      · exact absurd hs (fun hs => hne hs rfl)
      · exact absurd hs hv
    · refine ⟨-(s / t), ?_⟩
      have : t • x v = -(s • v) := eq_neg_of_add_eq_zero_right hst
      calc x v = t⁻¹ • (t • x v) := by rw [smul_smul, inv_mul_cancel₀ ht, one_smul]
        _ = -(s / t) • v := by rw [this, smul_neg, smul_smul, neg_smul, div_eq_inv_mul]
  have h1 : 1 < finrank F W := by omega
  obtain ⟨u, hu⟩ : ∃ u : W, u ≠ 0 := (Module.finrank_pos_iff_exists_ne_zero (R := F)).mp (by omega)
  obtain ⟨u', huu'⟩ := exists_linearIndependent_pair_of_one_lt_finrank h1 hu
  have hu' : u' ≠ 0 := by
    have := huu'.ne_zero 1
    simpa using this
  have hsum : u + u' ≠ 0 := by
    intro h0
    have := (LinearIndependent.pair_iff.mp huu') 1 1 (by simpa using h0)
    exact one_ne_zero this.1
  obtain ⟨a₁, ha₁⟩ := hev u hu
  obtain ⟨a₂, ha₂⟩ := hev u' hu'
  obtain ⟨a₃, ha₃⟩ := hev (u + u') hsum
  have hrel : (a₁ - a₃) • u + (a₂ - a₃) • u' = 0 := by
    have : x (u + u') = x u + x u' := map_add x u u'
    rw [ha₁, ha₂, ha₃, smul_add] at this
    calc (a₁ - a₃) • u + (a₂ - a₃) • u' = (a₁ • u + a₂ • u') - (a₃ • u + a₃ • u') := by
          rw [sub_smul, sub_smul]; abel
      _ = 0 := by rw [this, sub_self]
  obtain ⟨h13, h23⟩ := (LinearIndependent.pair_iff.mp huu') _ _ hrel
  have e1 : a₁ = a₃ := sub_eq_zero.mp h13
  have e2 : a₂ = a₃ := sub_eq_zero.mp h23
  refine ⟨a₃, ?_⟩
  haveI : Nonempty (Fin 2) := ⟨0⟩
  let B := basisOfLinearIndependentOfCardEqFinrank huu' (by simp [h2])
  refine B.ext fun i => ?_
  fin_cases i
  · show x (B 0) = (a₃ • (1 : Module.End F W)) (B 0)
    simp [B, ha₁, e1]
  · show x (B 1) = (a₃ • (1 : Module.End F W)) (B 1)
    simp [B, ha₂, e2]

theorem exists_apply_eq_imp_eq (h2 : finrank F W = 2) {ι : Type*} (c : ι → Module.End F W)
    (hc : ∀ i j, Commute (c i) (c j)) : ∃ v : W, ∀ i j, c i v = c j v → c i = c j := by
  by_cases hs : ∃ i, ∀ a : F, c i ≠ a • 1
  · obtain ⟨i₀, hi₀⟩ := hs
    obtain ⟨v, hv⟩ : ∃ v : W, LinearIndependent F ![v, c i₀ v] := by
      by_contra h
      push Not at h
      obtain ⟨a, ha⟩ := exists_eq_smul_one_of_forall h2 (c i₀) h
      exact hi₀ a ha
    refine ⟨v, fun i j hij => ?_⟩
    haveI : Nonempty (Fin 2) := ⟨0⟩
    let B := basisOfLinearIndependentOfCardEqFinrank hv (by simp [h2])
    refine B.ext fun r => ?_
    fin_cases r
    · simpa [B] using hij
    · show c i (B 1) = c j (B 1)
      have h1 : c i (c i₀ v) = c i₀ (c i v) := congrArg (fun f : Module.End F W => f v) (hc i i₀).eq
      have h2' : c j (c i₀ v) = c i₀ (c j v) := congrArg (fun f : Module.End F W => f v) (hc j i₀).eq
      simp [B, h1, h2', hij]
  · push Not at hs
    obtain ⟨v, hv⟩ : ∃ v : W, v ≠ 0 := (Module.finrank_pos_iff_exists_ne_zero (R := F)).mp (by omega)
    refine ⟨v, fun i j hij => ?_⟩
    obtain ⟨a, ha⟩ := hs i
    obtain ⟨b, hb⟩ := hs j
    rw [ha, hb] at hij ⊢
    have : a = b := smul_left_injective F hv (by simpa using hij)
    rw [this]

end CyclicVector

section Quadratic

theorem exists_mul_self_add_zsmul_one_eq {M : Type*} [Ring M] [Module.Free ℤ M] [Module.Finite ℤ M]
    (h : finrank ℤ M ≤ 2) (α : M) : ∃ t n : ℤ, α * α + n • (1 : M) = t • α := by
  set p := (Algebra.lmul ℤ M α).charpoly with hp
  have hmon : p.Monic := LinearMap.charpoly_monic _
  have hdeg : p.natDegree ≤ 2 := by rw [hp, LinearMap.charpoly_natDegree]; exact h
  have hev : aeval α p = 0 := Algebra.aeval_self_charpoly_lmul α
  have hsum := hmon.as_sum
  interval_cases hd : p.natDegree
  ·
    rw [hsum] at hev
    simp at hev
    refine ⟨0, 0, ?_⟩
    have h10 : (1 : M) = 0 := hev
    calc α * α + (0 : ℤ) • (1 : M) = (α * α + (0 : ℤ) • (1 : M)) * 1 := (mul_one _).symm
      _ = (0 : ℤ) • α := by rw [h10, mul_zero, zero_smul]
  ·
    rw [hsum] at hev
    simp at hev
    refine ⟨-p.coeff 0, 0, ?_⟩
    have hα : α = -((p.coeff 0 : ℤ) • (1 : M)) := by
      rw [eq_neg_iff_add_eq_zero, ← hev, zsmul_one]
    rw [zero_smul, add_zero, neg_smul]
    conv_lhs => rw [hα]
    rw [neg_mul, smul_mul_assoc, one_mul, hα, smul_neg, neg_neg]
  ·
    rw [hsum] at hev
    simp [Finset.sum_range_succ] at hev
    refine ⟨-p.coeff 1, p.coeff 0, ?_⟩
    rw [← zsmul_one (p.coeff 0), ← zsmul_one (p.coeff 1), smul_mul_assoc, one_mul] at hev
    rw [neg_smul, eq_neg_iff_add_eq_zero, ← hev, pow_two]
    abel

end Quadratic

end P2mKcQuadIntV2

namespace P2mKcQuadIntV2

open CategoryTheory AlgebraicGeometry NeronModelInfra GoodReductionJacobian

section EndRing

variable {R₀ : Type u} [CommRing R₀] {A : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of R₀)}

def IsHom (L : RelativeGroupLaw R₀ f) (β : SchemeHomOver f f) : Prop :=
  ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R₀)) (x y : SchemeHomOver t f),
    NeronModelInfra.schemeHomOverComp (L.mul t x y) β =
      L.mul t (NeronModelInfra.schemeHomOverComp x β) (NeronModelInfra.schemeHomOverComp y β)

def Pts (_L : RelativeGroupLaw R₀ f) {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R₀)) : Type u :=
  SchemeHomOver t f

theorem hcomm (L : RelativeGroupLaw R₀ f) [hc : Fact L.IsCommutative] : L.IsCommutative := hc.out

scoped instance instCommGroupPts (L : RelativeGroupLaw R₀ f) [Fact L.IsCommutative] {T : Scheme.{u}}
    (t : T ⟶ Spec (CommRingCat.of R₀)) : CommGroup (Pts L t) :=
  L.pointCommGroup (hcomm L) t

def EndR (L : RelativeGroupLaw R₀ f) : Type u := {β : SchemeHomOver f f // IsHom L β}

variable {L : RelativeGroupLaw R₀ f}

theorem comp_mul {T : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of R₀)} (x : SchemeHomOver t f)
    (β γ : SchemeHomOver f f) :
    NeronModelInfra.schemeHomOverComp x (L.mul f β γ) =
      L.mul t (NeronModelInfra.schemeHomOverComp x β) (NeronModelInfra.schemeHomOverComp x γ) :=
  L.mul_natural f t x.1 x.2 β γ

theorem comp_one {T : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of R₀)} (x : SchemeHomOver t f) :
    NeronModelInfra.schemeHomOverComp x (L.one f) = L.one t :=
  L.one_natural f t x.1 x.2

variable [Fact L.IsCommutative]

def evPt {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R₀)) (β : SchemeHomOver f f) (hβ : IsHom L β) :
    Pts L t →* Pts L t :=
  MonoidHom.mk' (fun x => NeronModelInfra.schemeHomOverComp x β) (fun x y => hβ t x y)

@[scoped simp] theorem evPt_apply {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R₀)) (β : SchemeHomOver f f)
    (hβ : IsHom L β) (x : Pts L t) : evPt t β hβ x = NeronModelInfra.schemeHomOverComp x β := rfl

theorem hom_one {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R₀)) (β : SchemeHomOver f f) (hβ : IsHom L β) :
    NeronModelInfra.schemeHomOverComp (L.one t) β = L.one t :=
  (evPt t β hβ).map_one

theorem hom_inv {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R₀)) (β : SchemeHomOver f f) (hβ : IsHom L β)
    (x : SchemeHomOver t f) :
    NeronModelInfra.schemeHomOverComp (L.inv t x) β = L.inv t (NeronModelInfra.schemeHomOverComp x β) :=
  (evPt t β hβ).map_inv x

omit [Fact L.IsCommutative] in
theorem isHom_id : IsHom L (schemeHomOverId f) := fun t x y => by
  simp only [schemeHomOverComp_id_right]

omit [Fact L.IsCommutative] in
theorem isHom_one : IsHom L (L.one f) := fun t x y => by
  rw [comp_one, comp_one, comp_one, L.one_mul]

theorem isHom_mul {β γ : SchemeHomOver f f} (hβ : IsHom L β) (hγ : IsHom L γ) : IsHom L (L.mul f β γ) :=
  fun t x y => by
    rw [comp_mul, comp_mul, comp_mul, hβ, hγ]
    exact mul_mul_mul_comm (G := Pts L t) _ _ _ _

theorem isHom_inv {β : SchemeHomOver f f} (hβ : IsHom L β) : IsHom L (L.inv f β) := fun t x y => by
  have h : ∀ z : SchemeHomOver t f, NeronModelInfra.schemeHomOverComp z (L.inv f β) =
      L.inv t (NeronModelInfra.schemeHomOverComp z β) := fun z => by
    have := comp_mul (L := L) z (L.inv f β) β
    rw [L.inv_mul_cancel, comp_one] at this
    exact (eq_inv_of_mul_eq_one_left (G := Pts L t) this.symm)
  rw [h, h, h, hβ]
  exact mul_inv (α := Pts L t) _ _

omit [Fact L.IsCommutative] in
theorem isHom_comp {β γ : SchemeHomOver f f} (hβ : IsHom L β) (hγ : IsHom L γ) :
    IsHom L (NeronModelInfra.schemeHomOverComp γ β) := fun t x y => by
  rw [← schemeHomOverComp_assoc, ← schemeHomOverComp_assoc, ← schemeHomOverComp_assoc, hγ, hβ]

namespace EndR

scoped instance instZero : Zero (EndR L) := ⟨⟨L.one f, isHom_one⟩⟩
scoped instance instAdd : Add (EndR L) := ⟨fun β γ => ⟨L.mul f β.1 γ.1, isHom_mul β.2 γ.2⟩⟩
scoped instance instNeg : Neg (EndR L) := ⟨fun β => ⟨L.inv f β.1, isHom_inv β.2⟩⟩
scoped instance instOne : One (EndR L) := ⟨⟨schemeHomOverId f, isHom_id⟩⟩
scoped instance instMul : Mul (EndR L) := ⟨fun β γ => ⟨NeronModelInfra.schemeHomOverComp γ.1 β.1, isHom_comp β.2 γ.2⟩⟩

scoped instance instAddCommGroup : AddCommGroup (EndR L) where
  add_assoc β γ δ := Subtype.ext (L.mul_assoc f _ _ _)
  zero_add β := Subtype.ext (L.one_mul f _)
  add_zero β := Subtype.ext (L.mul_one f _)
  add_comm β γ := Subtype.ext (hcomm L f β.1 γ.1)
  neg_add_cancel β := Subtype.ext (L.inv_mul_cancel f _)
  nsmul := nsmulRec
  zsmul := zsmulRec

scoped instance instRing : Ring (EndR L) where
  __ := (inferInstance : AddCommGroup (EndR L))
  mul_assoc β γ δ := Subtype.ext (schemeHomOverComp_assoc δ.1 γ.1 β.1).symm
  one_mul β := Subtype.ext (schemeHomOverComp_id_right β.1)
  mul_one β := Subtype.ext (schemeHomOverComp_id_left β.1)
  left_distrib β γ δ := Subtype.ext (β.2 f γ.1 δ.1)
  right_distrib β γ δ := Subtype.ext (comp_mul δ.1 β.1 γ.1)
  zero_mul β := Subtype.ext (comp_one β.1)
  mul_zero β := Subtype.ext (hom_one f β.1 β.2)
  npow := npowRec

def pt (β : EndR L) : Pts L f := β.1

omit [Fact L.IsCommutative] in
theorem pt_injective : Function.Injective (pt (L := L)) := fun _ _ h => Subtype.ext h

@[scoped simp] theorem pt_add (β γ : EndR L) : (β + γ).pt = β.pt * γ.pt := rfl
@[scoped simp] theorem pt_zero : (0 : EndR L).pt = 1 := rfl
@[scoped simp] theorem pt_neg (β : EndR L) : (-β).pt = β.pt⁻¹ := rfl
omit [Fact L.IsCommutative] in
@[scoped simp] theorem val_mul (β γ : EndR L) : (β * γ).1 = NeronModelInfra.schemeHomOverComp γ.1 β.1 := rfl
omit [Fact L.IsCommutative] in
@[scoped simp] theorem val_one : (1 : EndR L).1 = schemeHomOverId f := rfl

def ptHom : EndR L →+ Additive (Pts L f) where
  toFun β := Additive.ofMul β.pt
  map_zero' := rfl
  map_add' _ _ := rfl

@[scoped simp] theorem ptHom_apply (β : EndR L) : ptHom β = Additive.ofMul β.pt := rfl

theorem pt_zsmul (n : ℤ) (β : EndR L) : (n • β).pt = β.pt ^ n := by
  have := map_zsmul (ptHom (L := L)) n β
  simpa using congrArg Additive.toMul this

theorem pt_nsmul (n : ℕ) (β : EndR L) : (n • β).pt = β.pt ^ n := by
  have := pt_zsmul (n : ℤ) β
  rwa [natCast_zsmul, zpow_natCast] at this

theorem pt_sum {ι : Type*} (s : Finset ι) (c : ι → ℤ) (β : ι → EndR L) :
    (∑ i ∈ s, c i • β i).pt = ∏ i ∈ s, (β i).pt ^ c i := by
  have := map_sum (ptHom (L := L)) (fun i => c i • β i) s
  simp only [map_zsmul, ptHom_apply] at this
  have := congrArg Additive.toMul this
  simpa [toMul_sum, toMul_zsmul] using this

def evalAt {T : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of R₀)} (x : Pts L t) : EndR L →+ Additive (Pts L t) where
  toFun β := Additive.ofMul (show Pts L t from NeronModelInfra.schemeHomOverComp x β.1)
  map_zero' := by first | exact congrArg Additive.ofMul (comp_one (L := L) x) | simpa using comp_one (L := L) x
  map_add' β γ := by first | exact congrArg Additive.ofMul (comp_mul (L := L) x β.1 γ.1) | simpa using comp_mul (L := L) x β.1 γ.1

theorem evalAt_apply {T : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of R₀)} (x : Pts L t) (β : EndR L) :
    Additive.toMul (evalAt x β) = (show Pts L t from NeronModelInfra.schemeHomOverComp x β.1) := rfl

theorem comp_zsmul {T : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of R₀)} (x : Pts L t) (n : ℤ) (β : EndR L) :
    (show Pts L t from NeronModelInfra.schemeHomOverComp x (n • β).1) =
      (show Pts L t from NeronModelInfra.schemeHomOverComp x β.1) ^ n := by
  have := map_zsmul (evalAt (L := L) x) n β
  have := congrArg Additive.toMul this
  rwa [toMul_zsmul] at this

end EndR
p2m_reactivate "P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_exists_forall_mapPt_mapPt_mul_zpow_eq_zpow_of_forall_act_comp_eq.P2mKcQuadIntV2.EndR"

end EndRing
p2m_reactivate "P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_exists_forall_mapPt_mapPt_mul_zpow_eq_zpow_of_forall_act_comp_eq.P2mKcQuadIntV2.EndR"

section Sat

variable {M : Type*} [Ring M]

def sat (Φ : M) : Subalgebra ℤ M where
  carrier := {β | ∃ m : ℤ, m ≠ 0 ∧ ∃ p : Polynomial ℤ, m • β = Polynomial.aeval Φ p}
  mul_mem' := by
    rintro β γ ⟨m, hm, p, hp⟩ ⟨m', hm', p', hp'⟩
    refine ⟨m * m', mul_ne_zero hm hm', p * p', ?_⟩
    rw [map_mul, ← hp, ← hp', smul_mul_smul_comm, mul_comm m m']
  one_mem' := ⟨1, one_ne_zero, 1, by simp⟩
  add_mem' := by
    rintro β γ ⟨m, hm, p, hp⟩ ⟨m', hm', p', hp'⟩
    refine ⟨m * m', mul_ne_zero hm hm', Polynomial.C m' * p + Polynomial.C m * p', ?_⟩
    rw [map_add, map_mul, map_mul, Polynomial.aeval_C, Polynomial.aeval_C, ← hp, ← hp', smul_add,
      Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one, smul_mul_assoc, smul_mul_assoc, one_mul,
      one_mul, smul_smul, smul_smul, mul_comm m m']
  zero_mem' := ⟨1, one_ne_zero, 0, by simp⟩
  algebraMap_mem' r := ⟨1, one_ne_zero, Polynomial.C r, by simp⟩

theorem self_mem_sat (Φ : M) : Φ ∈ sat Φ := ⟨1, one_ne_zero, Polynomial.X, by simp⟩

theorem mem_sat_of_smul_mem {Φ : M} {n : ℤ} (hn : n ≠ 0) {γ : M} (h : n • γ ∈ sat Φ) : γ ∈ sat Φ := by
  obtain ⟨m, hm, p, hp⟩ := h
  exact ⟨m * n, mul_ne_zero hm hn, p, by rw [mul_smul, hp]⟩

variable [Module.Free ℤ M]

theorem commute_of_mem_sat {Φ a : M} (ha : Commute Φ a) {β : M} (hβ : β ∈ sat Φ) : Commute β a := by
  obtain ⟨m, hm, p, hp⟩ := hβ
  have hc : Commute (Polynomial.aeval Φ p) a := by
    have hmem : Polynomial.aeval Φ p ∈ Subalgebra.centralizer ℤ {a} := by
      have hΦ : Φ ∈ Subalgebra.centralizer ℤ ({a} : Set M) := by
        rw [Subalgebra.mem_centralizer_iff]
        rintro g rfl
        exact ha.eq.symm
      have : Algebra.adjoin ℤ {Φ} ≤ Subalgebra.centralizer ℤ ({a} : Set M) :=
        Algebra.adjoin_le (Set.singleton_subset_iff.mpr hΦ)
      exact this (Polynomial.aeval_mem_adjoin_singleton ℤ Φ)
    rw [Subalgebra.mem_centralizer_iff] at hmem
    exact (hmem a rfl).symm
  have h : m • (β * a - a * β) = 0 := by
    rw [smul_sub, ← smul_mul_assoc, ← mul_smul_comm, hp, hc.eq, sub_self]
  have h' : β * a - a * β = 0 := (smul_eq_zero_iff_right hm).mp h
  exact sub_eq_zero.mp h'

theorem commute_of_mem_sat_of_mem_sat {Φ β γ : M} (hβ : β ∈ sat Φ) (hγ : γ ∈ sat Φ) : Commute β γ :=
  commute_of_mem_sat (commute_of_mem_sat (Commute.refl Φ) hγ).symm hβ

scoped instance instFiniteSat [Module.Finite ℤ M] (Φ : M) : Module.Finite ℤ ↥(sat Φ) :=
  Module.Finite.of_injective (sat Φ).val.toLinearMap Subtype.val_injective

scoped instance instIsTorsionFreeSat (Φ : M) : Module.IsTorsionFree ℤ ↥(sat Φ) :=
  Function.Injective.moduleIsTorsionFree (fun β : ↥(sat Φ) => (β : M)) Subtype.val_injective (fun _ _ => rfl)

scoped instance instFreeSat [Module.Finite ℤ M] (Φ : M) : Module.Free ℤ ↥(sat Φ) :=
  Module.free_of_finite_type_torsion_free'

end Sat
p2m_reactivate "P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_exists_forall_mapPt_mapPt_mul_zpow_eq_zpow_of_forall_act_comp_eq.P2mKcQuadIntV2.EndR"

end P2mKcQuadIntV2
p2m_reactivate "P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_exists_forall_mapPt_mapPt_mul_zpow_eq_zpow_of_forall_act_comp_eq.P2mKcQuadIntV2.EndR P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_exists_forall_mapPt_mapPt_mul_zpow_eq_zpow_of_forall_act_comp_eq.P2mKcQuadIntV2"

namespace P2mKcQuadIntV2

open CategoryTheory AlgebraicGeometry NeronModelInfra GoodReductionJacobian

section Torsion

variable {K : Type u} [Field K] {A : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of K)} {L : RelativeGroupLaw K f}
  [Fact L.IsCommutative]

theorem nsmul_eq_pow {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of K)) (m : ℕ) (x : Pts L t) :
    L.nsmul t m x = x ^ m := by
  induction m with
  | zero => rfl
  | succ m ih => rw [L.nsmul_succ, ih, pow_succ]; rfl

variable (L) in

def tors (ℓ : ℕ) : Subgroup (Pts L (𝟙 (Spec (CommRingCat.of K)))) := (powMonoidHom ℓ).ker

theorem mem_tors {ℓ : ℕ} {x : Pts L (𝟙 (Spec (CommRingCat.of K)))} : x ∈ tors L ℓ ↔ x ^ ℓ = 1 := by
  rw [tors, MonoidHom.mem_ker, powMonoidHom_apply]

theorem mem_tors_iff_isTorsionPoint {ℓ : ℕ} {x : Pts L (𝟙 (Spec (CommRingCat.of K)))} :
    x ∈ tors L ℓ ↔ L.IsTorsionPoint (𝟙 (Spec (CommRingCat.of K))) ℓ x := by
  rw [mem_tors, RelativeGroupLaw.isTorsionPoint_def, nsmul_eq_pow]
  exact Iff.rfl

variable (L) in

def V (ℓ : ℕ) : Type u := Additive ↥(tors L ℓ)

scoped instance instAddCommGroupV (ℓ : ℕ) : AddCommGroup (V L ℓ) := Additive.addCommGroup

theorem nsmul_V_eq_zero {ℓ : ℕ} (v : V L ℓ) : ℓ • v = 0 := by
  have h : (Additive.toMul v : ↥(tors L ℓ)) ^ ℓ = 1 := Subtype.ext (by
    rw [Subgroup.coe_pow, Subgroup.coe_one]; exact mem_tors.mp (Additive.toMul v).2)
  have := congrArg Additive.ofMul h
  rwa [ofMul_pow] at this

scoped instance instModuleV (ℓ : ℕ) : Module (ZMod ℓ) (V L ℓ) := AddCommGroup.zmodModule nsmul_V_eq_zero

def ιV {ℓ : ℕ} (v : V L ℓ) : Pts L (𝟙 (Spec (CommRingCat.of K))) := (Additive.toMul v).1

theorem ιV_injective {ℓ : ℕ} : Function.Injective (ιV (L := L) (ℓ := ℓ)) := fun _ _ h =>
  Additive.toMul.injective (Subtype.ext h)

@[scoped simp] theorem ιV_add {ℓ : ℕ} (v w : V L ℓ) : ιV (v + w) = ιV v * ιV w := rfl
@[scoped simp] theorem ιV_zero {ℓ : ℕ} : ιV (0 : V L ℓ) = 1 := rfl
theorem ιV_mem {ℓ : ℕ} (v : V L ℓ) : ιV v ∈ tors L ℓ := (Additive.toMul v).2

def mkV {ℓ : ℕ} (x : Pts L (𝟙 (Spec (CommRingCat.of K)))) (hx : x ∈ tors L ℓ) : V L ℓ := Additive.ofMul ⟨x, hx⟩

@[scoped simp] theorem ιV_mkV {ℓ : ℕ} (x : Pts L (𝟙 (Spec (CommRingCat.of K)))) (hx : x ∈ tors L ℓ) :
    ιV (mkV x hx) = x := rfl

def actTors (ℓ : ℕ) (β : EndR L) : ↥(tors L ℓ) →* ↥(tors L ℓ) :=
  ((evPt _ β.1 β.2).domRestrict (tors L ℓ)).codRestrict (tors L ℓ) fun x => by
    rw [mem_tors, MonoidHom.domRestrict_apply, ← map_pow, mem_tors.mp x.2, map_one]

variable (L) in

def ρ (ℓ : ℕ) : EndR L →+* Module.End (ZMod ℓ) (V L ℓ) where
  toFun β := AddMonoidHom.toZModLinearMap ℓ (MonoidHom.toAdditive (actTors ℓ β))
  map_one' := by
    refine LinearMap.ext fun v => ιV_injective ?_
    show NeronModelInfra.schemeHomOverComp (ιV v) (schemeHomOverId f) = ιV v
    rw [schemeHomOverComp_id_right]
  map_mul' β γ := by
    refine LinearMap.ext fun v => ιV_injective ?_
    show NeronModelInfra.schemeHomOverComp (ιV v) (NeronModelInfra.schemeHomOverComp γ.1 β.1) =
      NeronModelInfra.schemeHomOverComp (NeronModelInfra.schemeHomOverComp (ιV v) γ.1) β.1
    rw [schemeHomOverComp_assoc]
  map_zero' := by
    refine LinearMap.ext fun v => ιV_injective ?_
    show NeronModelInfra.schemeHomOverComp (ιV v) (L.one f) = (1 : Pts L _)
    exact comp_one _
  map_add' β γ := by
    refine LinearMap.ext fun v => ιV_injective ?_
    show NeronModelInfra.schemeHomOverComp (ιV v) (L.mul f β.1 γ.1) =
      (show Pts L _ from NeronModelInfra.schemeHomOverComp (ιV v) β.1) *
        (show Pts L _ from NeronModelInfra.schemeHomOverComp (ιV v) γ.1)
    exact comp_mul _ _ _

theorem ιV_ρ {ℓ : ℕ} (β : EndR L) (v : V L ℓ) : ιV (ρ L ℓ β v) = NeronModelInfra.schemeHomOverComp (ιV v) β.1 :=
  rfl

theorem zsmul_natCast_End_eq_zero {ℓ : ℕ} (T : Module.End (ZMod ℓ) (V L ℓ)) : (ℓ : ℤ) • T = 0 := by
  ext v
  rw [LinearMap.smul_apply, natCast_zsmul, LinearMap.zero_apply]
  exact nsmul_V_eq_zero _

theorem ρ_eq_zero_of_eq_smul {ℓ : ℕ} {β γ : EndR L} (h : β = (ℓ : ℤ) • γ) : ρ L ℓ β = 0 := by
  rw [h, map_zsmul, zsmul_natCast_End_eq_zero]

variable [IsAlgClosed K]

theorem natCard_V (hA : AbelianSchemePropertyBundle K f) (g : ℕ) [SmoothOfRelativeDimension g f] {ℓ : ℕ}
    (hℓK : (ℓ : K) ≠ 0) : Nat.card (V L ℓ) = ℓ ^ (2 * g) := by
  rw [← GoodReductionJacobian.RelativeGroupLaw.natCard_isTorsionPoint_eq_pow_of_natCast_ne_zero K f L (hcomm L)
    hA g ℓ hℓK]
  refine Nat.card_congr (Additive.toMul.trans (Equiv.subtypeEquivRight fun x => ?_))
  exact mem_tors_iff_isTorsionPoint

theorem exists_eq_smul_of_ρ_eq_zero (hA : AbelianSchemePropertyBundle K f) {ℓ : ℕ} (hℓK : (ℓ : K) ≠ 0)
    {β : EndR L} (h : ρ L ℓ β = 0) : ∃ γ : EndR L, β = (ℓ : ℤ) • γ := by
  have hker : ∀ x : SchemeHomOver (𝟙 (Spec (CommRingCat.of K))) f,
      L.IsTorsionPoint (𝟙 (Spec (CommRingCat.of K))) ℓ x →
        NeronModelInfra.schemeHomOverComp x β.1 = L.one (𝟙 (Spec (CommRingCat.of K))) := by
    intro x hx
    have hx' : (x : Pts L _) ∈ tors L ℓ := mem_tors_iff_isTorsionPoint.mpr hx
    have := LinearMap.congr_fun h (mkV x hx')
    have := congrArg ιV this
    rwa [ιV_ρ, ιV_mkV] at this
  obtain ⟨γ, hγ, hβγ⟩ :=
    GoodReductionJacobian.RelativeGroupLaw.exists_eq_pow_of_forall_isTorsionPoint_schemeHomOverComp_eq_one
      K f L (hcomm L) hA ℓ hℓK β.1 β.2 hker
  refine ⟨⟨γ, hγ⟩, EndR.pt_injective ?_⟩
  rw [natCast_zsmul, EndR.pt_nsmul]
  exact hβγ

end Torsion
p2m_reactivate "P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_exists_forall_mapPt_mapPt_mul_zpow_eq_zpow_of_forall_act_comp_eq.P2mKcQuadIntV2.EndR P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_exists_forall_mapPt_mapPt_mul_zpow_eq_zpow_of_forall_act_comp_eq.P2mKcQuadIntV2"

section NoTorsion

variable {K : Type u} [Field K] {A : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of K)} {L : RelativeGroupLaw K f}
  [Fact L.IsCommutative]

omit [Fact L.IsCommutative] in

theorem connectedSpace_of_bundle (hA : AbelianSchemePropertyBundle K f) : ConnectedSpace A := by
  rw [connectedSpace_iff_univ]
  have h := hA.connectedFibres (IsLocalRing.closedPoint K)
  convert h using 1
  exact (Set.eq_univ_of_forall fun a => Subsingleton.elim _ _).symm

theorem eq_zero_of_natCast_smul_eq_zero [IsAlgClosed K] (hA : AbelianSchemePropertyBundle K f) {ℓ : ℕ}
    (hℓK : (ℓ : K) ≠ 0) {δ : EndR L} (h : (ℓ : ℤ) • δ = 0) : δ = 0 := by
  haveI : Smooth f := hA.smooth
  haveI : ConnectedSpace A := connectedSpace_of_bundle hA
  haveI : IsReduced A := AlgebraicGeometry.Smooth.isReduced_of_isReduced_of_isLocallyNoetherian f
  have hcomm' : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of K)) (x y : SchemeHomOver t f),
      L.mul t x y = L.mul t y x := fun t x y => hcomm L t x y
  have hsurj := GoodReductionJacobian.RelativeGroupLaw.nsmul_surjective_of_isAlgClosed_of_connectedSpace L hcomm' ℓ
    (isUnit_iff_ne_zero.mpr hℓK)
  refine EndR.pt_injective (?_ : δ.1 = L.one f)
  refine AlgebraicGeometry.SchemeHomOver.ext_of_forall_point_of_isReduced_of_locallyOfFiniteType K δ.1 (L.one f)
    fun P => ?_
  obtain ⟨Q, hQ⟩ := hsurj P
  have e2 : (show Pts L _ from NeronModelInfra.schemeHomOverComp P δ.1) =
      (show Pts L _ from NeronModelInfra.schemeHomOverComp Q δ.1) ^ ℓ := by
    rw [← hQ, nsmul_eq_pow]
    exact map_pow (evPt _ δ.1 δ.2) (show Pts L _ from Q) ℓ
  have e3 : (show Pts L _ from NeronModelInfra.schemeHomOverComp Q δ.1) ^ ℓ = 1 := by
    rw [← zpow_natCast, ← EndR.comp_zsmul Q (ℓ : ℤ) δ, h]
    exact comp_one Q
  have h1 : NeronModelInfra.schemeHomOverComp P δ.1 = L.one _ := e2.trans e3
  have h2 : NeronModelInfra.schemeHomOverComp P (L.one f) = L.one _ := comp_one P
  exact (congrArg Subtype.val h1).trans (congrArg Subtype.val h2).symm

end NoTorsion
p2m_reactivate "P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_exists_forall_mapPt_mapPt_mul_zpow_eq_zpow_of_forall_act_comp_eq.P2mKcQuadIntV2.EndR P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_exists_forall_mapPt_mapPt_mul_zpow_eq_zpow_of_forall_act_comp_eq.P2mKcQuadIntV2"

section QM

open QuaternionAlgebra CerednikDrinfeld CerednikDrinfeld.QM
open scoped Quaternion

variable {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} {N : ℕ} {k : Type u} [Field k]

scoped instance instFactComm (E : FakeEllipticCurve Λ N k) : Fact E.L.IsCommutative := ⟨E.comm⟩

variable (E : FakeEllipticCurve Λ N k)

theorem isHom_act (x : ↥Λ) : IsHom E.L ⟨E.act x, E.act_over x⟩ := fun t P Q => E.act_hom x t P Q

def ACT₀ (x : ↥Λ) : EndR E.L := ⟨⟨E.act x, E.act_over x⟩, isHom_act E x⟩

theorem ACT₀_val (x : ↥Λ) : (ACT₀ E x).1 = pushPt (E.act x) (E.act_over x) (⟨𝟙 E.A, Category.id_comp _⟩ : SchemeHomOver E.f E.f) :=
  Subtype.ext (by simp [ACT₀])

def ACT : ↥Λ →+ EndR E.L :=
  AddMonoidHom.mk' (ACT₀ E) fun x y => Subtype.ext (by
    rw [ACT₀_val]
    show pushPt (E.act (x + y)) (E.act_over (x + y)) _ = E.L.mul E.f (ACT₀ E x).1 (ACT₀ E y).1
    rw [ACT₀_val, ACT₀_val]
    exact E.act_add x y E.f _)

@[scoped simp] theorem ACT_apply (x : ↥Λ) : ACT E x = ACT₀ E x := rfl

theorem ACT_one (h1 : (1 : ℍ[ℚ, a, b]) ∈ Λ) : ACT E ⟨1, h1⟩ = 1 :=
  Subtype.ext (Subtype.ext (by simp [ACT₀, E.act_one h1]))

theorem ACT_mul (x y : ↥Λ) (h : (x : ℍ[ℚ, a, b]) * (y : ℍ[ℚ, a, b]) ∈ Λ) :
    ACT E ⟨(x : ℍ[ℚ, a, b]) * y, h⟩ = ACT E x * ACT E y :=
  Subtype.ext (Subtype.ext (by simp [ACT₀, E.act_mul x y h]))

variable {E}

theorem exists_ACT_eq_smul {ℓ : ℕ} {z : ↥Λ} (hz : ∃ y : ↥Λ, (z : ℍ[ℚ, a, b]) = (ℓ : ℚ) • (y : ℍ[ℚ, a, b])) :
    ∃ γ : EndR E.L, ACT E z = (ℓ : ℤ) • γ := by
  obtain ⟨y, hy⟩ := hz
  refine ⟨ACT E y, ?_⟩
  rw [← map_zsmul]
  congr 1
  apply Subtype.ext
  rw [hy, Submodule.coe_smul_of_tower, Nat.cast_smul_eq_nsmul, natCast_zsmul]

section Idempotent

variable {V₀ : Type*} [AddCommGroup V₀] {R : Type*} [Ring R]

theorem idem_aux {e w : R} (he : e * e = e) (hw : w * w = 1) (hwe : w * e * w + e = 1) :
    e * w * e = 0 ∧ e * w * w = e ∧ e + w * (e * w) = 1 := by
  have h1 : w * e * w = 1 - e := eq_sub_of_add_eq hwe
  have h2 : e * w = w - w * e := by
    have := congrArg (fun x => w * x) h1
    simp only [mul_sub, mul_one, ← mul_assoc, hw, one_mul] at this
    exact this
  refine ⟨?_, ?_, ?_⟩
  · rw [h2, sub_mul, mul_assoc, he, sub_self]
  · rw [mul_assoc, hw, mul_one]
  · rw [h2, mul_sub, ← mul_assoc, hw, one_mul]; abel

end Idempotent
p2m_reactivate "P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_exists_forall_mapPt_mapPt_mul_zpow_eq_zpow_of_forall_act_comp_eq.P2mKcQuadIntV2.EndR P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_exists_forall_mapPt_mapPt_mul_zpow_eq_zpow_of_forall_act_comp_eq.P2mKcQuadIntV2"

variable {q q' : ℕ} [Fact q.Prime] [Fact q'.Prime] [IsAlgClosed k]

variable (E) in
omit [Fact q.Prime] [Fact q'.Prime] [IsAlgClosed k] in

def Cring : Subring (EndR E.L) := Subring.centralizer (Set.range (ACT E))

omit [Fact q.Prime] [Fact q'.Prime] [IsAlgClosed k] in
theorem mem_Cring_iff {β : EndR E.L} : β ∈ Cring E ↔ ∀ x : ↥Λ, Commute β (ACT E x) := by
  rw [Cring, Subring.mem_centralizer_iff]
  constructor
  · intro h x
    exact (h _ ⟨x, rfl⟩).symm
  · rintro h _ ⟨x, rfl⟩
    exact (h x).eq.symm

omit [Fact q.Prime] [Fact q'.Prime] [IsAlgClosed k] in

theorem comm_of_mem_Cring {β : EndR E.L} (h : β ∈ Cring E) (x : ↥Λ) :
    NeronModelInfra.schemeHomOverComp (ACT₀ E x).1 β.1 = NeronModelInfra.schemeHomOverComp β.1 (ACT₀ E x).1 :=
  congrArg Subtype.val ((mem_Cring_iff.mp h x).eq)

theorem mem_Cring_of_smul_mem {E : FakeEllipticCurve Λ N k} {ℓ : ℕ} (hℓk : (ℓ : k) ≠ 0) {γ : EndR E.L}
    (h : (ℓ : ℤ) • γ ∈ Cring E) : γ ∈ Cring E := by
  rw [mem_Cring_iff] at h ⊢
  intro x
  have h0 : (ℓ : ℤ) • (γ * ACT E x - ACT E x * γ) = 0 := by
    rw [smul_sub, ← smul_mul_assoc, ← mul_smul_comm, (h x).eq, sub_self]
  exact sub_eq_zero.mp (eq_zero_of_natCast_smul_eq_zero E.bundle hℓk h0)

theorem free_and_finite_C (hqq' : q' ≠ q) (hB : IsIndefiniteRamifiedExactlyAt a b q q') (hΛ : IsMaximalOrder Λ)
    (E : FakeEllipticCurve Λ N k) : Module.Free ℤ ↥(Cring E) ∧ Module.Finite ℤ ↥(Cring E) := by
  haveI : SmoothOfRelativeDimension 2 E.f := CerednikDrinfeld.QM.FakeEllipticCurve.smoothOfRelativeDimension_two k E
  have hsep : ∀ β : SchemeHomOver E.f E.f,
      (∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of k)) (x y : SchemeHomOver t E.f),
        NeronModelInfra.schemeHomOverComp (E.L.mul t x y) β =
          E.L.mul t (NeronModelInfra.schemeHomOverComp x β) (NeronModelInfra.schemeHomOverComp y β)) →
      (∀ x : ↥Λ, NeronModelInfra.schemeHomOverComp (ACT₀ E x).1 β = NeronModelInfra.schemeHomOverComp β (ACT₀ E x).1) →
      β ≠ E.L.one E.f → E.L.endDegree β ≠ 0 := by
    rintro ⟨φ, hφ⟩ hβ hcomm hne
    refine CerednikDrinfeld.QM.FakeEllipticCurve.endDegree_ne_zero_of_forall_act_comp_eq_of_ne_one hqq' hB Λ hΛ k E φ hφ
      (fun t P Q => hβ t P Q) (fun x => ?_) hne
    exact congrArg Subtype.val (hcomm x)
  obtain ⟨r, bb, hbb, huniq⟩ :=
    GoodReductionJacobian.RelativeGroupLaw.exists_existsUnique_eq_prod_zpow_of_forall_comm_of_forall_endDegree_ne_zero
      k E.f E.L (hcomm E.L) E.bundle 2 two_pos (fun x : ↥Λ => (ACT₀ E x).1)
      (fun x {T} t P Q => isHom_act E x t P Q) hsep
  have hbC : ∀ i, (⟨bb i, fun t P Q => (hbb i).1 t P Q⟩ : EndR E.L) ∈ Cring E := fun i =>
    mem_Cring_iff.mpr fun x => Subtype.ext ((hbb i).2 x)
  let Bv : Fin r → ↥(Cring E) := fun i => ⟨⟨bb i, fun t P Q => (hbb i).1 t P Q⟩, hbC i⟩
  let g : (Fin r → ℤ) →ₗ[ℤ] ↥(Cring E) := Fintype.linearCombination ℤ Bv
  have hg : ∀ c : Fin r → ℤ, ((g c : ↥(Cring E)) : EndR E.L).pt =
      (letI := E.L.pointCommGroup (hcomm E.L) E.f; ∏ i, bb i ^ c i) := fun c => by
    have h1 : ((g c : ↥(Cring E)) : EndR E.L) = ∑ i, c i • ((Bv i : ↥(Cring E)) : EndR E.L) := by
      show (Cring E).subtype (Fintype.linearCombination ℤ Bv c) = _
      rw [Fintype.linearCombination_apply, map_sum]
      simp only [map_zsmul]
      rfl
    rw [h1, EndR.pt_sum]
    rfl
  have hinj : Function.Injective g := by
    intro c c' hcc'
    obtain ⟨c₀, -, hc₀⟩ := huniq ((g c : ↥(Cring E)) : EndR E.L).1 ((g c : ↥(Cring E)) : EndR E.L).2
      (comm_of_mem_Cring (g c).2)
    have h1 : c = c₀ := hc₀ c (hg c)
    have h2 : c' = c₀ := hc₀ c' (by rw [hcc']; exact hg c')
    rw [h1, h2]
  have hsurj : Function.Surjective g := by
    intro β
    obtain ⟨c, hc, -⟩ := huniq (β : EndR E.L).1 (β : EndR E.L).2 (comm_of_mem_Cring β.2)
    exact ⟨c, Subtype.ext (EndR.pt_injective ((hg c).trans hc.symm))⟩
  let e : (Fin r → ℤ) ≃ₗ[ℤ] ↥(Cring E) := LinearEquiv.ofBijective g ⟨hinj, hsurj⟩
  exact ⟨Module.Free.of_equiv e, Module.Finite.equiv e⟩

theorem finrank_sat_le_two (hB : IsIndefiniteRamifiedExactlyAt a b q q') (hΛ : IsMaximalOrder Λ)
    (E : FakeEllipticCurve Λ N k) [Module.Free ℤ ↥(Cring E)] [Module.Finite ℤ ↥(Cring E)]
    (Φ : ↥(Cring E)) : Module.finrank ℤ ↥(sat Φ) ≤ 2 := by
  classical

  obtain ⟨ℓ, hℓge, hℓ⟩ := Nat.exists_infinite_primes (q + q' + ringChar k + 1)
  haveI : Fact ℓ.Prime := ⟨hℓ⟩
  have hℓq : ℓ ≠ q := by omega
  have hℓq' : ℓ ≠ q' := by omega
  have hℓk : (ℓ : k) ≠ 0 := by
    intro h0
    rw [ringChar.spec] at h0
    rcases CharP.char_is_prime_or_zero k (ringChar k) with hp | hp
    · rcases (Nat.dvd_prime hℓ).mp h0 with h1 | h1
      · exact hp.one_lt.ne' h1
      · omega
    · rw [hp, zero_dvd_iff] at h0; omega
  haveI : SmoothOfRelativeDimension 2 E.f := CerednikDrinfeld.QM.FakeEllipticCurve.smoothOfRelativeDimension_two k E
  have hA : AbelianSchemePropertyBundle k E.f := E.bundle
  have h1Λ : (1 : ℍ[ℚ, a, b]) ∈ Λ := hΛ.1.one_mem

  obtain ⟨θ, hθ1, hθmul, hθsurj, hθker⟩ :=
    QuaternionAlgebra.exists_linearMap_matrix_zmod_of_isMaximalOrder_of_ne hB Λ hΛ ℓ hℓq hℓq'
  obtain ⟨et, het⟩ := hθsurj !![1, 0; 0, 0]
  obtain ⟨wt, hwt⟩ := hθsurj !![0, 1; 1, 0]
  have hee : (et : ℍ[ℚ, a, b]) * et ∈ Λ := hΛ.1.mul_mem et.2 et.2
  have hww : (wt : ℍ[ℚ, a, b]) * wt ∈ Λ := hΛ.1.mul_mem wt.2 wt.2
  have hwe : (wt : ℍ[ℚ, a, b]) * et ∈ Λ := hΛ.1.mul_mem wt.2 et.2
  have hwew : (wt : ℍ[ℚ, a, b]) * et * wt ∈ Λ := hΛ.1.mul_mem hwe wt.2

  have r1 : θ (⟨(et : ℍ[ℚ, a, b]) * et, hee⟩ - et) = 0 := by
    rw [map_sub, hθmul, het]
    ext i j; fin_cases i <;> fin_cases j <;> simp
  have r2 : θ (⟨(wt : ℍ[ℚ, a, b]) * wt, hww⟩ - ⟨1, h1Λ⟩) = 0 := by
    rw [map_sub, hθmul, hwt, hθ1]
    ext i j; fin_cases i <;> fin_cases j <;> simp
  have r3 : θ (⟨(wt : ℍ[ℚ, a, b]) * et * wt, hwew⟩ + et - ⟨1, h1Λ⟩) = 0 := by
    rw [map_sub, map_add, hθmul ⟨(wt : ℍ[ℚ, a, b]) * et, hwe⟩ wt hwew, hθmul, hwt, het, hθ1]
    ext i j; fin_cases i <;> fin_cases j <;> simp

  set e : Module.End (ZMod ℓ) (V E.L ℓ) := ρ E.L ℓ (ACT E et) with he_def
  set w : Module.End (ZMod ℓ) (V E.L ℓ) := ρ E.L ℓ (ACT E wt) with hw_def
  have he : e * e = e := by
    obtain ⟨γ, hγ⟩ := exists_ACT_eq_smul (E := E) ((hθker _).mp r1)
    rw [map_sub, ACT_mul, sub_eq_iff_eq_add] at hγ
    rw [he_def, ← map_mul, hγ, map_add, ρ_eq_zero_of_eq_smul rfl, zero_add]
  have hw : w * w = 1 := by
    obtain ⟨γ, hγ⟩ := exists_ACT_eq_smul (E := E) ((hθker _).mp r2)
    rw [map_sub, ACT_mul, ACT_one, sub_eq_iff_eq_add] at hγ
    rw [hw_def, ← map_mul, hγ, map_add, ρ_eq_zero_of_eq_smul rfl, zero_add, map_one]
  have hwew' : w * e * w + e = 1 := by
    obtain ⟨γ, hγ⟩ := exists_ACT_eq_smul (E := E) ((hθker _).mp r3)
    rw [map_sub, map_add, ACT_mul E ⟨(wt : ℍ[ℚ, a, b]) * et, hwe⟩ wt hwew, ACT_mul, ACT_one,
      sub_eq_iff_eq_add] at hγ
    rw [hw_def, he_def, ← map_mul, ← map_mul, ← map_add, hγ, map_add, ρ_eq_zero_of_eq_smul rfl, zero_add, map_one]
  obtain ⟨hewe, heww, hdec⟩ := idem_aux he hw hwew'

  have hce : ∀ β : ↥(sat Φ), Commute (ρ E.L ℓ ((β : ↥(Cring E)) : EndR E.L)) e := fun β =>
    (mem_Cring_iff.mp (β : ↥(Cring E)).2 et).map (ρ E.L ℓ)
  have hcw : ∀ β : ↥(sat Φ), Commute (ρ E.L ℓ ((β : ↥(Cring E)) : EndR E.L)) w := fun β =>
    (mem_Cring_iff.mp (β : ↥(Cring E)).2 wt).map (ρ E.L ℓ)

  let W : Submodule (ZMod ℓ) (V E.L ℓ) := LinearMap.eqLocus e 1
  have hWmem : ∀ v, v ∈ W ↔ e v = v := fun v => LinearMap.mem_eqLocus
  have heW : ∀ v, e v ∈ W := fun v => (hWmem _).mpr (by rw [← Module.End.mul_apply, he])

  have hcardV : Nat.card (V E.L ℓ) = ℓ ^ 4 := natCard_V hA 2 hℓk
  haveI : Finite (V E.L ℓ) := Nat.finite_of_card_ne_zero (by rw [hcardV]; exact pow_ne_zero _ hℓ.ne_zero)
  let split : V E.L ℓ ≃ ↥W × ↥W :=
    { toFun := fun v => (⟨e v, heW v⟩, ⟨e (w v), heW _⟩)
      invFun := fun p => p.1 + w p.2
      left_inv := fun v => by
        show e v + w (e (w v)) = v
        have := LinearMap.congr_fun hdec v
        simpa using this
      right_inv := fun p => by
        obtain ⟨⟨x, hx⟩, ⟨y, hy⟩⟩ := p
        rw [hWmem] at hx hy
        have h3 : e (w y) = 0 := by
          rw [← hy]; show (e * w * e) y = 0; rw [hewe]; rfl
        have h4 : e (w x) = 0 := by
          rw [← hx]; show (e * w * e) x = 0; rw [hewe]; rfl
        have h5 : e (w (w y)) = y := by
          show (e * w * w) y = y; rw [heww, hy]
        have h1 : e (x + w y) = x := by rw [map_add, hx, h3, add_zero]
        have h2 : e (w (x + w y)) = y := by rw [map_add, map_add, h4, h5, zero_add]
        exact Prod.ext (Subtype.ext h1) (Subtype.ext h2) }
  have hcardW : Nat.card ↥W = ℓ ^ 2 := by
    have h := Nat.card_congr split
    rw [Nat.card_prod, hcardV, ← pow_two] at h
    have : (ℓ ^ 2) ^ 2 = Nat.card ↥W ^ 2 := by rw [← h]; ring
    exact (Nat.pow_left_injective two_ne_zero this).symm
  have hfinW : Module.finrank (ZMod ℓ) ↥W = 2 := by
    have h := Module.natCard_eq_pow_finrank (K := ZMod ℓ) (V := ↥W)
    rw [hcardW, Nat.card_zmod] at h
    exact (Nat.pow_right_injective hℓ.two_le h).symm

  have hres : ∀ β : ↥(sat Φ), ∀ v ∈ W, ρ E.L ℓ ((β : ↥(Cring E)) : EndR E.L) v ∈ W := fun β v hv => by
    rw [hWmem] at hv ⊢
    rw [← Module.End.mul_apply, ← (hce β).eq, Module.End.mul_apply, hv]
  let c : ↥(sat Φ) → Module.End (ZMod ℓ) ↥W := fun β => (ρ E.L ℓ ((β : ↥(Cring E)) : EndR E.L)).restrict (hres β)
  have hcc : ∀ β γ, Commute (c β) (c γ) := fun β γ => by
    refine LinearMap.ext fun v => Subtype.ext ?_
    show ρ E.L ℓ ((β : ↥(Cring E)) : EndR E.L) (ρ E.L ℓ ((γ : ↥(Cring E)) : EndR E.L) v) =
      ρ E.L ℓ ((γ : ↥(Cring E)) : EndR E.L) (ρ E.L ℓ ((β : ↥(Cring E)) : EndR E.L) v)
    have hC : Commute ((β : ↥(Cring E)) : EndR E.L) ((γ : ↥(Cring E)) : EndR E.L) :=
      (commute_of_mem_sat_of_mem_sat β.2 γ.2).map (Cring E).subtype
    rw [← Module.End.mul_apply, ← map_mul, hC.eq, map_mul, Module.End.mul_apply]
  obtain ⟨v₀, hv₀⟩ := exists_apply_eq_imp_eq hfinW c hcc

  let ev : ↥(sat Φ) →+ ↥W :=
    { toFun := fun β => c β v₀
      map_zero' := Subtype.ext (by simp [c])
      map_add' := fun β γ => Subtype.ext (by simp [c]) }
  refine finrank_le_of_ker_le_smul hℓ.one_lt hcardW.le ev fun β hβ => ?_

  have hc0 : c β = c 0 := hv₀ β 0 (by
    have : c 0 v₀ = 0 := Subtype.ext (by simp [c])
    rw [this]; exact hβ)
  have hW0 : ∀ v ∈ W, ρ E.L ℓ ((β : ↥(Cring E)) : EndR E.L) v = 0 := fun v hv => by
    have := congrArg Subtype.val (LinearMap.congr_fun hc0 ⟨v, hv⟩)
    simpa [c, LinearMap.restrict_apply] using this
  have hV0 : ρ E.L ℓ ((β : ↥(Cring E)) : EndR E.L) = 0 := by
    refine LinearMap.ext fun v => ?_
    have hv : v = e v + w (e (w v)) := by
      have := LinearMap.congr_fun hdec v
      simpa using this.symm
    rw [hv, map_add, hW0 _ (heW v), ← Module.End.mul_apply, (hcw β).eq, Module.End.mul_apply,
      hW0 _ (heW _), map_zero, LinearMap.zero_apply, add_zero]
  obtain ⟨γ, hγ⟩ := exists_eq_smul_of_ρ_eq_zero hA hℓk hV0
  have hγC : γ ∈ Cring E := mem_Cring_of_smul_mem hℓk (hγ ▸ (β : ↥(Cring E)).2)
  have hγ' : (β : ↥(Cring E)) = (ℓ : ℤ) • (⟨γ, hγC⟩ : ↥(Cring E)) := Subtype.ext hγ
  have hγmem : (⟨γ, hγC⟩ : ↥(Cring E)) ∈ sat Φ :=
    mem_sat_of_smul_mem (by exact_mod_cast hℓ.ne_zero) (hγ' ▸ β.2)
  exact ⟨⟨⟨γ, hγC⟩, hγmem⟩, Subtype.ext hγ'⟩

theorem exists_quadratic (hqq' : q' ≠ q) (hB : IsIndefiniteRamifiedExactlyAt a b q q') (hΛ : IsMaximalOrder Λ)
    (E : FakeEllipticCurve Λ N k) (Φ : EndR E.L) (hΦ : ∀ x : ↥Λ, Commute Φ (ACT E x)) :
    ∃ t n : ℤ, Φ * Φ + n • (1 : EndR E.L) = t • Φ := by
  obtain ⟨hfree, hfin⟩ := free_and_finite_C hqq' hB hΛ E
  let Φc : ↥(Cring E) := ⟨Φ, mem_Cring_iff.mpr hΦ⟩
  have hrank := finrank_sat_le_two hB hΛ E Φc
  obtain ⟨t, n, h⟩ := exists_mul_self_add_zsmul_one_eq hrank ⟨Φc, self_mem_sat Φc⟩
  refine ⟨t, n, ?_⟩
  have h1 := congrArg (fun x : ↥(sat Φc) => (Cring E).subtype (x : ↥(Cring E))) h
  simpa [Φc] using h1

end QM
p2m_reactivate "P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_exists_forall_mapPt_mapPt_mul_zpow_eq_zpow_of_forall_act_comp_eq.P2mKcQuadIntV2.EndR P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_exists_forall_mapPt_mapPt_mul_zpow_eq_zpow_of_forall_act_comp_eq.P2mKcQuadIntV2"

end P2mKcQuadIntV2
p2m_reactivate "P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_exists_forall_mapPt_mapPt_mul_zpow_eq_zpow_of_forall_act_comp_eq.P2mKcQuadIntV2.EndR P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_exists_forall_mapPt_mapPt_mul_zpow_eq_zpow_of_forall_act_comp_eq.P2mKcQuadIntV2"

open CategoryTheory AlgebraicGeometry NeronModelInfra GoodReductionJacobian IsDedekindDomain AlgebraicCurve QuaternionAlgebra CerednikDrinfeld CerednikDrinfeld.QM
open scoped Quaternion TensorProduct NumberField

theorem solution
    {q q' : ℕ} [Fact q.Prime] [Fact q'.Prime] (hqq' : q' ≠ q)
    {a b : ℚ} (hB : IsIndefiniteRamifiedExactlyAt a b q q')
    (Λ : Submodule ℤ ℍ[ℚ, a, b]) (hΛ : IsMaximalOrder Λ) {N : ℕ}
    (k : Type u) [Field k] [IsAlgClosed k] (E : FakeEllipticCurve Λ N k)
    (φ : E.A ⟶ E.A) (hφ : φ ≫ E.f = E.f)
    (hmul : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of k)) (P Q : SchemeHomOver t E.f),
      mapPt φ hφ (E.L.mul t P Q) = E.L.mul t (mapPt φ hφ P) (mapPt φ hφ Q))
    (hact : ∀ x : ↥Λ, E.act x ≫ φ = φ ≫ E.act x) :
    ∃ t n : ℤ, ∀ {T : Scheme.{u}} (s : T ⟶ Spec (CommRingCat.of k)) (P : SchemeHomOver s E.f),
      letI := E.L.pointCommGroup E.comm s
      mapPt φ hφ (mapPt φ hφ P) * P ^ n = mapPt φ hφ P ^ t := by
  let Φ : P2mKcQuadIntV2.EndR E.L := ⟨⟨φ, hφ⟩, fun t P Q => hmul t P Q⟩
  have hΦ : ∀ x : ↥Λ, Commute Φ (P2mKcQuadIntV2.ACT E x) := fun x =>
    Subtype.ext (Subtype.ext (by simp [Φ, P2mKcQuadIntV2.ACT₀, hact x]))
  obtain ⟨t, n, h⟩ := P2mKcQuadIntV2.exists_quadratic hqq' hB hΛ E Φ hΦ
  refine ⟨t, n, fun s P => ?_⟩
  have h1 := congrArg (fun β => Additive.toMul
    (P2mKcQuadIntV2.EndR.evalAt (L := E.L) (show P2mKcQuadIntV2.Pts E.L s from P) β)) h
  simp only [map_add, map_zsmul, toMul_add, toMul_zsmul, P2mKcQuadIntV2.EndR.evalAt_apply] at h1
  exact h1

end
p2m_reactivate "P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_exists_forall_mapPt_mapPt_mul_zpow_eq_zpow_of_forall_act_comp_eq.P2mKcQuadIntV2.EndR P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_exists_forall_mapPt_mapPt_mul_zpow_eq_zpow_of_forall_act_comp_eq.P2mKcQuadIntV2"

end S_CerednikDrinfeld_QM_FakeEllipticCurve_exists_forall_mapPt_mapPt_mul_zpow_eq_zpow_of_forall_act_comp_eq
end P2MW
export P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_exists_forall_mapPt_mapPt_mul_zpow_eq_zpow_of_forall_act_comp_eq (solution)
