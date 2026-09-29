-- Prove2me | solution 1 for CerednikDrinfeld.QM.FakeEllipticCurve.forall_mapPt_eq_one_of_isLevelIsogeny_of_exists_factorsThrough_ne_one
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.141142+00:00
-- url     : https://prove2.me/submissions/fa7a30cf-6515-54d7-857b-996e3a3f8de5

import Definitions.Def_CerednikDrinfeld_FakeEllipticFrobenius
import Theorems.Thm_QuaternionAlgebra_exists_linearMap_matrix_zmod_of_isMaximalOrder_of_ne
import Theorems.Thm_CerednikDrinfeld_QM_surjective_and_isFinite_and_flat_of_mapPt_mapPt_eq_nsmulPt
import Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_finite_and_natCard_torsionPoints_le_sq_of_charP_of_not_dvd
import Theorems.Thm_QuaternionAlgebra_exists_module_matrix_zmod_of_smul_eq_zero_of_linearMap
import Theorems.Thm_Matrix_exists_natCard_eq_pow_two_mul_of_module_zmod
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_forall_mapPt_eq_one_of_isLevelIsogeny_of_exists_factorsThrough_ne_one
p2m_attr_erase "instance" "GoodReductionJacobian.RelativeGroupLaw.isIso_endKerStr_schemeHomOverId AlgebraicGeometry.Scheme.PresheafOfModules.symmetricCategory SheafOfModules.instFaithfulRingSheafPModToPMod SheafOfModules.symmetricCategory AlgebraicGeometry.Scheme.PresheafOfModules.monoidalCategory AlgebraicGeometry.Scheme.PresheafOfModules.monoidalClosed SheafOfModules.instFullRingSheafPModToPMod SheafOfModules.monoidalCategory AlgebraicGeometry.Scheme.Modules.symmetricCategory SheafOfModules.monoidalClosed SheafOfModules.instIsLocalizationPModRingSheafSheafifyFunctorPresheafW SheafOfModules.sheafifyFunctor_monoidal AlgebraicGeometry.Scheme.Modules.monoidalClosed AlgebraicGeometry.instMonoidalPresheafOfModulesModulesSheafify AlgebraicGeometry.Scheme.Modules.monoidalCategory PresheafOfModules.instMonoidalClosed PresheafOfModules.InternalHom.instModuleCarrierObjOppositeCommRingCatSubtypePiFamilyMemAddSubgroupNaturalFamilies PresheafOfModules.InternalHom.instModuleCarrierObjOppositeRingCatCompCommRingCatForget₂RingHomCarrierCarrierAbPresheaf PresheafOfModules.InternalHom.instSMulCarrierObjOppositeCommRingCatSubtypePiFamilyMemAddSubgroupNaturalFamilies AlgebraicGeometry.Scheme.Hom.opensMapFinal AlgebraicGeometry.RelPicard.RigidifiedLineBundle.setoid AlgebraicGeometry.RelPicard.RigidifiedLineBundle.instInhabited AlgebraicGeometry.OModulePresheaf.isScalarTower AlgebraicGeometry.Scheme.OrderedAffineCover.instLinearOrder AlgebraicGeometry.OModulePresheaf.module AlgebraicGeometry.Scheme.OrderedAffineCover.instFintype AlgebraicGeometry.Scheme.OrderedAffineCover.instFintypeIdx AlgebraicGeometry.OModulePresheaf.addCommGroup AlgebraicGeometry.Scheme.OrderedAffineCover.instDecidableEqIdx AlgebraicGeometry.OModulePresheaf.moduleSections TwoChartCech.Sections.M0_moduleA TwoChartCech.Sections.M1_module TwoChartCech.Cover.A01_algebra TwoChartCech.Cover.A0_algebra TwoChartCech.Cover.A1_commRing TwoChartCech.Cover.A1_algebra TwoChartCech.Sections.M01_module TwoChartCech.Sections.M0_addCommGroup TwoChartCech.Sections.M0_tower TwoChartCech.Sections.M01_addCommGroup"
p2m_attr_erase "instance" "TwoChartCech.Cover.A0_commRing TwoChartCech.Sections.M1_tower TwoChartCech.Sections.M01_moduleA TwoChartCech.Sections.M0_module TwoChartCech.Sections.M1_moduleA TwoChartCech.Sections.M1_addCommGroup TwoChartCech.Cover.A01_commRing TwoChartCech.Sections.M01_tower CoherentBaseChange.TwoTermComplex.C0_module CoherentBaseChange.TwoTermComplex.C0_addCommGroup CoherentBaseChange.TwoTermComplex.C1_module CoherentBaseChange.TwoTermComplex.C1_addCommGroup CoherentBaseChange.TwoTermComplex.C0_free CoherentBaseChange.TwoTermComplex.C1_finite CoherentBaseChange.TwoTermComplex.C0_finite CoherentBaseChange.TwoTermComplex.C1_free AlgebraicGeometry.Scheme.Modules.preservesBinaryProducts_opensMap AlgebraicGeometry.Scheme.Modules.pullback_monoidal AlgebraicGeometry.Scheme.Modules.sheafify_isLocalization' AlgebraicGeometry.Scheme.Modules.preservesTerminal_opensMap AlgebraicGeometry.Scheme.Modules.pullback₀_monoidal AlgebraicGeometry.Scheme.Modules.preservesFiniteProducts_opensMap AlgebraicGeometry.Scheme.Modules.instLiftingPresheafOfModulesSheafifyPresheafWOpensCarrierCarrierCommRingCatGrothendieckTopologyObjFunctorOppositeIsSheafSheafCompPullback₀Pullback PresheafOfModules.PullbackMonoidal.pullback_monoidal PresheafOfModules.PullbackMonoidal.isIso_δ PresheafOfModules.pushforward_laxMonoidal PresheafOfModules.PullbackMonoidal.isIso_η PresheafOfModules.free_monoidal PresheafOfModules.restrictScalars_laxMonoidal PresheafOfModules.PullbackMonoidal.isIso_δ_gS PresheafOfModules.pullback_oplaxMonoidal PresheafOfModules.PullbackMonoidal.instPreservesColimitsOfSizeCompOppositeCommRingCatRingCatForget₂RingHomCarrierCarrierPb PresheafOfModules.pullback_monoidal' AlgebraicGeometry.SmoothOfRelativeDimension.fiberToSpecResidueField AlgebraicGeometry.SmoothOfRelativeDimension.pullback_snd AlgebraicGeometry.SmoothOfRelativeDimension.pullback_fst AlgebraicGeometry.SmoothOfRelativeDimension.smooth_one AlgebraicGeometry.SmoothProperCurve.isIntegral_pullback_Spec_field AlgebraicGeometry.IsProper.fiberToSpecResidueField AlgebraicCurve.CurveModel.isProper"
p2m_attr_erase "instance" "AlgebraicCurve.CurveModel.isIntegral AlgebraicCurve.CurveModel.smooth AlgebraicGeometry.Scheme.LocalRepresentabilityULift.instIsLocallyInjectiveFunUliftYonedaGluedToSheaf AlgebraicGeometry.Scheme.LocalRepresentabilityULift.instIsLocallySurjectiveFunUliftYonedaGluedToSheafOfIsLocallySurjectiveZariskiTopologyDescFunctorOppositeType AlgebraicGeometry.Scheme.LocalRepresentabilityULift.instIsOpenImmersionToGlued AlgebraicGeometry.Scheme.LocalRepresentabilityULift.instIsIsoSheafZariskiTopologyTypeUliftYonedaGluedToSheaf AlgebraicGeometry.RelPicard.instIsOpenImmersionToGlued AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.instFundamentalIdentityOfSumRamificationInertia AlgebraicCurve.Place.instIsScalarTowerResidueFieldRestrictPushforward AlgebraicCurve.Place.instAlgebraResidueFieldRestrictPushforward AlgebraicCurve.Place.instIsLocalHomRestrictInclusion AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions PresheafOfModules.ExteriorPower.instModulePresheafAb AlgebraicGeometry.RelEffCartierDiv.subsingleton_of_degree_zero AlgebraicGeometry.RelEffCartierDiv.isIso_subschemeIota_snd_of_degree_one AlgebraicGeometry.isIso_ker_graphOver_subschemeIota_snd AlgebraicGeometry.isClosedImmersion_graphOver AlgebraicGeometry.FGSubalgebra.instIsDirectedLe AlgebraicGeometry.FGSubalgebra.instQuasiSeparatedSpaceCarrierCarrierCommRingCatObjOppositeSchemeSpecDiagram AlgebraicGeometry.FGSubalgebra.instIsCofilteredOpposite AlgebraicGeometry.FGSubalgebra.instIsAffineObjOppositeSchemeSpecDiagram AlgebraicGeometry.FGSubalgebra.instNonempty AlgebraicGeometry.FGSubalgebra.instNonemptySubtypeLeSubalgebraValFG AlgebraicGeometry.FGSubalgebra.instCompactSpaceCarrierCarrierCommRingCatObjOppositeSchemeSpecDiagram AlgebraicGeometry.FGSubalgebra.instIsDirectedSubtypeLeSubalgebraValFG AlgebraicGeometry.FGSubalgebra.instIsAffineHomMapOppositeSchemeSpecDiagram AlgebraicGeometry.FGSubalgebra.instIsFiltered AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instNeg AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instSMulInt AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instAddCommGroup AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instAdd AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instSub AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instModuleCarrierObjOppositeOpensCarrierCarrierCommRingCatPresheafOpOpensTop"
p2m_attr_erase "instance" "AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instSMulCarrierObjOppositeOpensCarrierCarrierCommRingCatPresheafOpOpensTop AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instSMulNat AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instZero AlgebraicCurve.instHasLocalResidue_of_hasCanonicalLocalResidueK AlgebraicCurve.instHasCanonicalLocalResidueK_of_hasCanonicalLocalResidueKStar AlgebraicCurve.Place.kw_ffgc_finiteDimensional_adicCompletion instAlgebraSubtypeMemValuationSubring_definitions AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersIntegersCompletion ModularCurve.KwF4gRRTate.instAlgebraKAdicCompletionIntegers AlgebraicCurve.Place.kw_ffgc_continuousSMul_adicCompletionComap AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersCompletionCompletion IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions AlgebraicCurve.instHasCanonicalLocalResidueK AlgebraicCurve.Place.instAlgebra_restrictResidueField AlgebraicCurve.Place.instIsScalarTower_restrictResidueField AlgebraicCurve.instHasLocalResidue AlgebraicCurve.HasSeparableResidue.of_perfectField_of_isCurveOver AlgebraicCurve.HasSeparableResidue.of_perfectField AlgebraicCurve.Place.instIsLocalHom_restrictSubringHom AlgebraicCurve.instHasCanonicalLocalResidueKStar ModularCurve.KwNo6Pin.isLocalRing_completion SheafOfModules.isIso_ihomModelToIhom AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instDecidableEqIdx AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instFintype AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instLinearOrder AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instFintypeIdx AlgebraicGeometry.OModulePresheaf.instSubsingletonObjZero AlgebraicGeometry.OModulePresheaf.Leray.relAltC_scalarTower AlgebraicGeometry.OModulePresheaf.Leray.ker_relAltd_modΓ AlgebraicGeometry.OModulePresheaf.Leray.relAltC_modΓ AlgebraicGeometry.OModulePresheaf.Leray.biC_abGrp AlgebraicGeometry.OModulePresheaf.Leray.relAltH_modΓ AlgebraicGeometry.OModulePresheaf.Leray.ker_relAltd_smul AlgebraicGeometry.OModulePresheaf.Leray.relAltH_scalarTower AlgebraicGeometry.OModulePresheaf.Leray.relAltH_smul"
p2m_attr_erase "instance" "AlgebraicGeometry.OModulePresheaf.Leray.biC_module DoubleComplex.instModuleE₂I DoubleComplex.Bounded.modR DoubleComplex.instModuleE₂II DoubleComplex.instAddCommGroupE₂II DoubleComplex.Bounded.abGrp DoubleComplex.instAddCommGroupE₂I AlgebraicGeometry.ChowDatum.hι_closed AlgebraicGeometry.ChowDatumProj.hιN_closed AlgebraicGeometry.ChowDatumProj.hp_proper AlgebraicGeometry.ChowDatum.hp_isoU AlgebraicGeometry.ChowDatum.hp_proper AlgebraicGeometry.ProjSpace.algebraAway AlgebraicGeometry.ProjSpace.instIsProperProdOverπ AlgebraicGeometry.ChowDatumProj.hp_isoU AlgebraicGeometry.ProjSpace.isProper_π AlgebraicGeometry.ProjSpace.finiteType_mvPolynomial ProjSpaceCech.GradedModule.H.module ProjSpaceCech.GradedModule.H.addCommGroup ProjSpaceCech.GradedModule.sec.instAdd ProjSpaceCech.GradedModule.sec.instNeg ProjSpaceCech.GradedModule.acg ProjSpaceCech.GradedModule.Frac.setoid ProjSpaceCech.GradedModule.modR ProjSpaceCech.GradedModule.sec.instModule ProjSpaceCech.GradedModule.sec.instAddCommGroup ProjSpaceCech.GradedModule.sec.instZero ProjSpaceCech.GradedModule.Presentation.fJ ProjSpaceCech.GradedModule.sec.instSMul ProjSpaceCech.Twist.H.module ProjSpaceCech.Idx.instFintype ProjSpaceCech.Twist.H.addCommGroup ProjSpaceCech.Idx.instDecidableEq ProjSpaceCech.Twist.Mon.instDecidableEq ProjSpaceCech.Twist.cochain.instAddCommGroup ProjSpaceCech.Twist.cochain.instModule AlgebraicGeometry.FGSubalgebra.tensorStage_directedSystem AlgebraicGeometry.RelEffCartierDiv.isClosedImmersion_subschemeι_resProdMap AlgebraicGeometry.RelEffCartierDiv.isOpenImmersion_resProdMap AlgebraicCurve.CurveModel.locallyOfFiniteType_gluedToBase"
p2m_attr_erase "instance" "AlgebraicCurve.CurveModel.isFractionRing_overlap AlgebraicCurve.CurveModel.isLocallyNoetherian_glued AlgebraicCurve.CurveModel.jacobsonSpace_glued AlgebraicCurve.CurveModel.isOpenImmersion_ι₀ AlgebraicCurve.CurveModel.isIntegral_glued AlgebraicCurve.CurveModel.quasiSeparated_gluedToBase AlgebraicCurve.CurveModel.compactSpace_glued AlgebraicCurve.CurveModel.isIntegral_adjoin_chartRing AlgebraicCurve.CurveModel.isFractionRing_overlap_functionField AlgebraicCurve.CurveModel.isProper_gluedToBase AlgebraicCurve.CurveModel.isOpenImmersion_ιU AlgebraicCurve.CurveModel.isOpenImmersion_f₀ AlgebraicCurve.CurveModel.isOpenImmersion_fInf AlgebraicCurve.CurveModel.isOpenImmersion_ιInf AlgebraicCurve.CurveModel.algebra_overlap_functionField AlgebraicCurve.CurveModel.quasiCompact_gluedToBase AlgebraicCurve.CurveModel.algebraAdjoin AlgebraicCurve.CurveModel.isDedekindDomain_chartRing AlgebraicCurve.CurveModel.isIntegralClosure AlgebraicCurve.CurveModel.finite_chartRing AlgebraicCurve.CurveModel.centre_isPrime AlgebraicCurve.CurveModel.isFractionRing_chartRing AlgebraicCurve.CurveModel.finiteType_chartRing AlgebraicCurve.CurveModel.isNoetherianRing_chartRing AlgebraicCurve.CurveModel.isScalarTower_base_adjoin AlgebraicCurve.CurveModel.isScalarTower_adjoin AlgebraicCurve.CurveModel.chartRing_finitePresentation instTopologicallyFGOfFiniteType AlgebraicGeometry.ProjSpace.twistObj.addCommGroup AlgebraicGeometry.ProjSpace.twistFam.module AlgebraicGeometry.ProjSpace.twistObj.module AlgebraicGeometry.ProjSpace.twistObj.moduleSections AlgebraicGeometry.ProjSpace.twistFam.addCommGroup kmfloorsGlue_int_three_isPrime kmfloorsGlue_int_bot_isPrime"
p2m_attr_erase "simp" "QuaternionAlgebra.baseChangeRight_tmul QuaternionAlgebra.mapOfAlgebraMapEq_apply QuaternionAlgebra.baseChange_tmul NeronModelInfra.schemeHomOverNpow_succ NeronModelInfra.schemeHomOverNpow_zero GoodReductionJacobian.RelativeGroupLaw.nsmul_zero GoodReductionJacobian.RelativeGroupLaw.mem_torsionSubset GoodReductionJacobian.RelativeGroupLaw.nsmul_succ NeronModelInfra.NeronModelPropertyBundle.endExtensionEquiv_symm_restrict NeronModelInfra.schemeHomOverComp_id_left NeronModelInfra.schemeHomOverComp_id_right NeronModelInfra.schemeHomOverId_coe NeronModelInfra.NeronModelPropertyBundle.endExtensionEquiv_apply NeronModelInfra.NeronModelPropertyBundle.restrict_endExtensionEquiv_symm NeronModelInfra.schemeHomOverComp_coe GoodReductionJacobian.relativeGroupLawOfGrpObj_inv GoodReductionJacobian.relativeGroupLawOfGrpObj_mul GoodReductionJacobian.overHomEquivSchemeHomOver_apply_coe GoodReductionJacobian.relativeGroupLawOfGrpObj_one GoodReductionJacobian.overHomEquivSchemeHomOver_symm_apply_left SheafOfModules.tensorUnit_eq AlgebraicGeometry.Scheme.Modules.tensorUnit_eq PresheafOfModules.InternalHom.presheaf_map_apply PresheafOfModules.InternalHom.curryFamily_app PresheafOfModules.InternalHom.add_app PresheafOfModules.InternalHom.smul_app PresheafOfModules.InternalHom.zero_app PresheafOfModules.ihomObj_map_val PresheafOfModules.ihomFunctor_map PresheafOfModules.InternalHom.restrict_app PresheafOfModules.InternalHom.postcomp_app PresheafOfModules.InternalHom.neg_app PresheafOfModules.curry'_app_val PresheafOfModules.InternalHom.presheaf_obj PresheafOfModules.ihomFunctor_obj PresheafOfModules.ihomObj_obj PresheafOfModules.InternalHom.sub_app PresheafOfModules.ihomMap_app_val AlgebraicGeometry.Scheme.Modules.tensorPow_zero AlgebraicGeometry.Scheme.Modules.tensorPow_succ"
p2m_attr_erase "simp" "AlgebraicGeometry.RelPicard.RigidifiedLineBundle.mk.sizeOf_spec AlgebraicGeometry.RelPicard.RigidifiedLineBundle.mk.injEq AlgebraicGeometry.Scheme.OrderedAffineCover.mk.injEq AlgebraicGeometry.OModulePresheaf.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCover.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.mk.injEq AlgebraicGeometry.Scheme.TwoAffineOpenCover.mk.injEq AlgebraicGeometry.Scheme.TwoAffineOpenCover.mk.sizeOf_spec AlgebraicGeometry.Scheme.TwoAffineOpenCover.pullback_U1 AlgebraicGeometry.Scheme.TwoAffineOpenCover.pullback_U0 TwoChartCech.Sections.mk.injEq TwoChartCech.Cover.mk.injEq TwoChartCech.GrothendieckComplex.mk.injEq TwoChartCech.Sections.mk.sizeOf_spec TwoChartCech.Cover.mk.sizeOf_spec TwoChartCech.Cover.lineBundle_r0_apply TwoChartCech.GrothendieckComplex.mk.sizeOf_spec TwoChartCech.Cover.lineBundle_r1_apply CoherentBaseChange.TwoTermComplex.mk.sizeOf_spec CoherentBaseChange.TwoTermComplex.mk.injEq PresheafOfModules.freeεIso_hom_app PresheafOfModules.freeμIso_hom_app AlgebraicGeometry.RelPicard.RepresentsRelSubPic.mk.injEq AlgebraicGeometry.RelPicard.SubPicCondition.mk.injEq AlgebraicGeometry.RelPicard.SubPicCondition.mk.sizeOf_spec AlgebraicGeometry.RelPicard.RepresentsRelSubPic.mk.sizeOf_spec AlgebraicGeometry.SmoothProperCurve.sectionBaseChange_coe_snd AlgebraicGeometry.SmoothProperCurve.sectionBaseChange_coe_fst AlgebraicCurve.CurveModel.mk.injEq AlgebraicCurve.CurveModel.mk.sizeOf_spec AlgebraicCurve.mulAdele_apply AlgebraicCurve.residuePairing_apply_coe AlgebraicCurve.mem_adeleBdd AlgebraicCurve.weilSmul_one AlgebraicCurve.diagonalHom_apply AlgebraicCurve.weilSmul_apply AlgebraicCurve.adeleSpaceMul_coe AlgebraicCurve.mulAdele_one AlgebraicGeometry.SmoothProperCurve.FiniteMapData.twoAffineOpenCover_U1 AlgebraicGeometry.SmoothProperCurve.FiniteMapData.mk.injEq"
p2m_attr_erase "simp" "AlgebraicGeometry.SmoothProperCurve.FiniteMapData.mk.sizeOf_spec AlgebraicGeometry.SmoothProperCurve.FiniteMapData.twoAffineOpenCover_U0 AlgebraicGeometry.RelPicard.SubPicCondition.onClasses_mk AlgebraicGeometry.RelPicard.relSubPicPresheaf_map_coe CategoryTheory.Functor.OverTotal.ofFibre_fst CategoryTheory.Functor.overTotal_map_fst AlgebraicGeometry.Scheme.LocalRepresentabilityULift.glueData_J AlgebraicGeometry.Scheme.LocalRepresentabilityULift.uliftYoneda_toGlued_uliftYonedaGluedToSheaf AlgebraicGeometry.Scheme.LocalRepresentabilityULift.glueData_t' AlgebraicGeometry.Scheme.LocalRepresentabilityULift.uliftYoneda_toGlued_uliftYonedaGluedToSheaf_assoc AlgebraicGeometry.Scheme.LocalRepresentabilityULift.uliftYonedaGluedToSheaf_app_toGlued AlgebraicGeometry.Scheme.LocalRepresentabilityULift.glueData_openCover_map AlgebraicGeometry.Scheme.LocalRepresentabilityULift.uliftYonedaGluedToSheaf_app_comp AlgebraicGeometry.Scheme.LocalRepresentabilityULift.glueData_V AlgebraicGeometry.Scheme.LocalRepresentabilityULift.glueData_t AlgebraicGeometry.Scheme.LocalRepresentabilityULift.glueData_U AlgebraicGeometry.Scheme.LocalRepresentabilityULift.glueData_f AlgebraicGeometry.RelPicard.designationOfRepresentableBy_P AlgebraicGeometry.RelPicard.designationOfRepresentableBy_toBase AlgebraicGeometry.RelPicard.rigSection_snd AlgebraicGeometry.RelPicard.RigidifiedLineBundle.ofInvertible_L AlgebraicGeometry.RelPicard.rigSection_snd_assoc AlgebraicGeometry.RelPicard.SubPicGroupCondition.mk.injEq AlgebraicGeometry.RelPicard.SubPicGroupCondition.mk.sizeOf_spec AlgebraicCurve.coe_cechH0Equiv_apply AlgebraicCurve.cechH1ToH1_mk AlgebraicCurve.lSpaceOn_univ AlgebraicCurve.lSpaceOn_empty AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.Divisor.mapRestrict_single AlgebraicCurve.Divisor.pushforward_single AlgebraicCurve.Place.coe_restrictInclusion AlgebraicCurve.Place.mem_fiber AlgebraicCurve.Place.restrict_toValuationSubring AlgebraicCurve.Divisor.degree_pushforward"
p2m_attr_erase "simp" "AlgebraicCurve.Place.restrictResidueMap_residue AlgebraicCurve.Pic0.coe_pushforwardDegZeroHom AlgebraicCurve.Pic0.coe_pullbackDegZeroHom AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Divisor.degree_pushforwardAlong AlgebraicCurve.Pic0.coe_degZeroCorrespondence AlgebraicCurve.Place.mem_fiberAlong AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.jqNModC_one ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint"
p2m_attr_erase "simp" "AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one AlgebraicCurve.Place.differentialCoeff_zero AlgebraicCurve.Place.differentialCoeff_dCoord AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.injEq AlgebraicCurve.TranscendenceTower.mk.injEq AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec AlgebraicCurve.PoleDivisorPackage.mk.injEq AlgebraicGeometry.RelPicard.thetaBundle_def AlgebraicGeometry.RelPicard.picardBundle_def AlgebraicGeometry.RelEffCartierDiv.toRelEffDivisor_ofRelEffDivisor AlgebraicGeometry.RelEffCartierDiv.toRelEffDivisor_I AlgebraicGeometry.mapOnProdOver_fst_assoc AlgebraicGeometry.RelEffCartierDiv.mk.sizeOf_spec AlgebraicGeometry.RelEffCartierDiv.mk.injEq AlgebraicGeometry.mapOnProdOver_snd AlgebraicGeometry.mapOnProdOver_fst AlgebraicGeometry.mapOnProdOver_snd_assoc AlgebraicGeometry.mapOnProdOver_id AlgebraicCurve.RelEffDivisor.mk.sizeOf_spec AlgebraicCurve.mapOnProd_fst AlgebraicCurve.mapOnProd_fst_assoc AlgebraicCurve.mapOnProd_snd AlgebraicCurve.UnivDivisorPack.mk.injEq AlgebraicCurve.RelEffDivisor.mk.injEq AlgebraicCurve.UnivDivisorPack.mk.sizeOf_spec AlgebraicCurve.mapOnProd_snd_assoc AlgebraicGeometry.Scheme.Modules.exteriorPower_obj PresheafOfModules.exteriorPower_map_ιMulti PresheafOfModules.ExteriorPower.appₗ_apply AlgebraicGeometry.prodKerGraph_one AlgebraicGeometry.fibrePowOver.proj_comp AlgebraicGeometry.prodKerGraph_zero AlgebraicGeometry.RelEffCartierDiv.empty_I AlgebraicGeometry.fibrePowOver.proj_comp_assoc AlgebraicGeometry.graphOver_fst_assoc AlgebraicGeometry.RelEffCartierDiv.toPoint_comp"
p2m_attr_erase "simp" "AlgebraicGeometry.RelEffCartierDiv.toPoint_comp_assoc AlgebraicGeometry.graphOver_fst AlgebraicGeometry.RelEffCartierDiv.ofPoint_I AlgebraicGeometry.graphOver_snd AlgebraicGeometry.graphOver_snd_assoc AlgebraicCurve.SymmetricPowerPackage.mk.sizeOf_spec AlgebraicCurve.SymmetricPowerPackage.mk.injEq AlgebraicGeometry.FGSubalgebra.cocone_ι_app_apply AlgebraicGeometry.RelPicard.fst_toProdSpec AlgebraicGeometry.RelPicard.toProdSpec_fst_assoc AlgebraicGeometry.RelPicard.pointsSubBasepointModule_cons AlgebraicGeometry.RelPicard.pointsSubBasepointModule_nil AlgebraicGeometry.RelPicard.fst_toProdSpec_assoc AlgebraicGeometry.RelPicard.toProdSpec_fst AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.sub_app AlgebraicGeometry.Scheme.IdealSheafData.sres_sresTop AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.add_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.mk.sizeOf_spec AlgebraicGeometry.Scheme.IdealSheafData.coe_resLE AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.smul_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.coe_ofLE_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.ideal_range AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.zero_app AlgebraicGeometry.Scheme.IdealSheafData.sres_sres AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.comp_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.neg_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.id_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.coe_mulRight_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.nsmul_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.mk.injEq AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.zsmul_app AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.sizeOf_spec AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.injEq AlgebraicCurve.adeleSingle_coe AlgebraicCurve.kaehlerResidueTermKFam_apply AlgebraicCurve.Place.LocalResidueData.mk.injEq AlgebraicCurve.Place.LocalResidueData.mk.sizeOf_spec AlgebraicCurve.Place.kw_ffgc_adicCompletionComapIntegers_coe AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.sizeOf_spec AlgebraicCurve.Place.mem_simplePoleSubmodule"
p2m_attr_erase "simp" "AlgebraicCurve.Place.coe_uniformizerSubring ModularCurve.Lg37.Lg37CompletionSection.mk.injEq AlgebraicCurve.Place.CoefficientFieldSection.mk.injEq AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.injEq ModularCurve.Lg37.Lg37CompletionSection.mk.sizeOf_spec AlgebraicCurve.Place.CoefficientFieldSection.mk.sizeOf_spec AlgebraicCurve.Place.poleSubmodule_one AlgebraicCurve.Place.mem_poleSubmodule AlgebraicGeometry.Scheme.Modules.toUnitSection_ofUnitSection AlgebraicGeometry.Scheme.Modules.pullbackSection_def AlgebraicGeometry.Scheme.Modules.ofUnitSection_toUnitSection PresheafOfModules.InternalHom.IsSheafAux.appAt_toPresheafHom SheafOfModules.ihomSectionsEquivFamily_unit AlgebraicGeometry.Scheme.Modules.restrictHomEquivFamily_apply SheafOfModules.ihomEval_unit_app AlgebraicGeometry.Scheme.Modules.ihomEval_zero_right AlgebraicGeometry.Scheme.Modules.ihomEval_zero_left AlgebraicGeometry.Scheme.Modules.homOfFamily_app_apply SheafOfModules.unit_ihomSectionsEquivFamily AlgebraicGeometry.Scheme.Modules.familyOfHom_app AlgebraicGeometry.Scheme.Modules.restrictUnitIso_hom_app_apply AlgebraicGeometry.Scheme.Modules.restrictUnitIso_inv_app_apply AlgebraicGeometry.Scheme.Modules.restrictHomOfFamily_app_apply AlgebraicGeometry.Scheme.Modules.restrictHomEquivFamily_symm_apply AlgebraicGeometry.Scheme.Modules.tensorSections_zero_right AlgebraicGeometry.Scheme.Modules.map_unitSection AlgebraicGeometry.Scheme.Modules.tensorSectionsBilin_apply AlgebraicGeometry.Scheme.Modules.tensorPowSection_zero AlgebraicGeometry.Scheme.Modules.tensorSections_zero_left AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_neg AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_zero AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_sub AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_add AlgebraicGeometry.Scheme.OrderedAffineCover.toCoverOf_U AlgebraicGeometry.Scheme.OrderedAffineCoverOf.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCoverOf.mk.injEq AlgebraicGeometry.Scheme.OrderedAffineCover.restrict_U AlgebraicGeometry.OModulePresheaf.Hom.mk.injEq AlgebraicGeometry.OModulePresheaf.Hom.id_app AlgebraicGeometry.OModulePresheaf.AffHom.appSections_apply"
p2m_attr_erase "simp" "AlgebraicGeometry.OModulePresheaf.AffHom.comp_app AlgebraicGeometry.OModulePresheaf.AffSES.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.AffHom.kerMap_coe AlgebraicGeometry.OModulePresheaf.AffHom.id_app AlgebraicGeometry.OModulePresheaf.Hom.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.Hom.toAffHom_app AlgebraicGeometry.OModulePresheaf.SES.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.AffHom.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.Hom.comp_app AlgebraicGeometry.OModulePresheaf.SES.mk.injEq AlgebraicGeometry.OModulePresheaf.AffHom.mk.injEq AlgebraicGeometry.OModulePresheaf.Hom.appSections_apply AlgebraicGeometry.OModulePresheaf.AffSES.mk.injEq AlgebraicGeometry.OModulePresheaf.prod_obj AlgebraicGeometry.OModulePresheaf.restrOpen_obj AlgebraicGeometry.OModulePresheaf.DevissageStep.mk.injEq AlgebraicGeometry.OModulePresheaf.pushforward_obj AlgebraicGeometry.OModulePresheaf.im_obj AlgebraicGeometry.OModulePresheaf.pow_obj AlgebraicGeometry.OModulePresheaf.fstHom_app AlgebraicGeometry.OModulePresheaf.ker_obj AlgebraicGeometry.OModulePresheaf.coker_obj AlgebraicGeometry.OModulePresheaf.DevissageStep.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCover.preimage_U AlgebraicGeometry.OModulePresheaf.sndHom_app AlgebraicGeometry.OModulePresheaf.Leray.restrictToPreimage_U DoubleComplex.Bounded.mk.injEq DoubleComplex.Bounded.mk.sizeOf_spec DoubleComplex.Convergence.mk.injEq DoubleComplex.Convergence.mk.sizeOf_spec DoubleComplex.SubQuot.mk.sizeOf_spec DoubleComplex.SubQuot.mk.injEq AlgebraicGeometry.ChowDatumProj.mk.sizeOf_spec AlgebraicGeometry.ChowDatum.mk.sizeOf_spec AlgebraicGeometry.ChowDatumProj.mk.injEq AlgebraicGeometry.ChowDatum.mk.injEq ProjSpaceCech.GradedModule.mk.injEq ProjSpaceCech.GradedModule.mk.sizeOf_spec ProjSpaceCech.GradedModule.Frac.mk.sizeOf_spec ProjSpaceCech.GradedModule.Presentation.mk.injEq"
p2m_attr_erase "simp" "ProjSpaceCech.GradedModule.Frac.mk.injEq ProjSpaceCech.GradedModule.Presentation.mk.sizeOf_spec ProjSpaceCech.GradedModule.Hom.shift_toLinearMap ProjSpaceCech.GradedModule.Hom.mk.sizeOf_spec ProjSpaceCech.GradedModule.Hom.mk.injEq TwoChartCech.Mumford.dK_apply TwoChartCech.Mumford.ι0_apply TwoChartCech.Mumford.ι1_apply TwoChartCech.KerCoprod.dK_apply TwoChartCech.KerCoprod.ι1_apply TwoChartCech.KerCoprod.ι0_apply AlgebraicGeometry.tilde.functorCompPullbackSpecIso_app AlgebraicGeometry.RelPicard.algEquivZeroGroupCut_toSubPicCondition AlgebraicGeometry.RelPicard.LFP.stageHom_val AlgebraicGeometry.RelPicard.BaseChange.relSubPicPresheafRestrictIso_hom_app_coe AlgebraicGeometry.RelPicard.BaseChange.relSubPicPresheafRestrictIso_inv_app_coe AlgebraicGeometry.RelPicard.BaseChange.restrict_P AlgebraicGeometry.RelEffCartierDiv.IsUniversal.lift_comp AlgebraicGeometry.RelEffCartierDiv.functor_map_fst AlgebraicGeometry.RelEffCartierDiv.IsUniversal.homEquiv_apply AlgebraicGeometry.RelEffCartierDiv.IsUniversal.lift_pullbackAlong AlgebraicGeometry.RelEffCartierDiv.IsUniversal.homEquiv_symm_apply AlgebraicGeometry.RelEffCartierDiv.IsUniversal.lift_comp_assoc AlgebraicGeometry.RelEffCartierDiv.supportedIn_top AlgebraicGeometry.RelEffCartierDiv.mem_supportedIn_iff AlgebraicGeometry.RelEffCartierDiv.supportedIn_top_eq AlgebraicGeometry.RelEffCartierDiv.restrictAlong_extendAlong AlgebraicGeometry.RelEffCartierDiv.extendAlong_I AlgebraicGeometry.RelEffCartierDiv.resProdMap_snd AlgebraicGeometry.RelEffCartierDiv.restrictAlong_I AlgebraicGeometry.RelEffCartierDiv.extendAlong_restrictAlong AlgebraicGeometry.RelEffCartierDiv.resProdMap_fst_assoc AlgebraicGeometry.RelEffCartierDiv.resProdMap_snd_assoc AlgebraicGeometry.RelEffCartierDiv.resProdMap_fst CoherentBaseChange.FibreH0Family.mk.sizeOf_spec CoherentBaseChange.FibreH0Family.mk.injEq AlgebraicGeometry.Scheme.Modules.ProjPresentation.mk.injEq AlgebraicGeometry.Scheme.Modules.ProjPresentation.mk.sizeOf_spec AlgebraicCurve.CurveModel.coe_gInf AlgebraicCurve.CurveModel.coe_tInvChart"
p2m_attr_erase "simp" "AlgebraicCurve.CurveModel.ιInf_gluedToBase_assoc AlgebraicCurve.CurveModel.ιInf_gluedToBase AlgebraicCurve.CurveModel.primeOfι₀_asIdeal AlgebraicCurve.CurveModel.coe_tChart AlgebraicCurve.CurveModel.ι₀_gluedToBase_assoc AlgebraicCurve.CurveModel.primeOfιInf_asIdeal AlgebraicCurve.CurveModel.ι₀_gluedToBase AlgebraicCurve.CurveModel.coe_tma AlgebraicCurve.CurveModel.coe_primeEquivChartPlaces RegularLocalRingQuotientAscent.dualNumberFst_apply AlgebraicGeometry.ProjSpace.twistObj.mk.injEq AlgebraicGeometry.ProjSpace.twistObj.zero_val AlgebraicGeometry.ProjSpace.twistObj.add_val AlgebraicGeometry.ProjSpace.twist_res_val AlgebraicGeometry.ProjSpace.twist_smul_val AlgebraicGeometry.ProjSpace.twistGradeToObj_val AlgebraicGeometry.ProjSpace.twistObj.smul_val AlgebraicGeometry.ProjSpace.twistGradeEquiv_apply_val AlgebraicGeometry.ProjSpace.twistObj.mk.sizeOf_spec GoodReductionJacobian.RelativeGroupLaw.fibre_inv GoodReductionJacobian.RelativeGroupLaw.fibrePointToBase_coe GoodReductionJacobian.RelativeGroupLaw.fibrePointOfBase_toBase GoodReductionJacobian.RelativeGroupLaw.fibre_mul GoodReductionJacobian.RelativeGroupLaw.fibrePointToBase_ofBase GoodReductionJacobian.RelativeGroupLaw.fibre_one GoodReductionJacobian.RelativeGroupLaw.fibrePointOfBase_coe AlgebraicGeometry.schemeFibreEndo_snd AlgebraicGeometry.schemeFibreEndo_fst AlgebraicGeometry.Scheme.relFrobenius_snd AlgebraicGeometry.Scheme.frobenius_preimage AlgebraicGeometry.Scheme.relFrobenius_fst AlgebraicGeometry.Scheme.relFrobenius_snd_assoc AlgebraicGeometry.Scheme.relFrobenius_fst_assoc AlgebraicGeometry.powCharRingHom_apply AlgebraicGeometry.Scheme.frobenius_base GoodReductionJacobian.RelativeGroupLaw.baseChangePointToBase_ofBase GoodReductionJacobian.RelativeGroupLaw.baseChangePointToBase_coe GoodReductionJacobian.RelativeGroupLaw.baseChangePointOfBase_coe GoodReductionJacobian.RelativeGroupLaw.baseChange_inv GoodReductionJacobian.RelativeGroupLaw.baseChangePointOfBase_toBase"
p2m_attr_erase "simp" "GoodReductionJacobian.RelativeGroupLaw.baseChange_mul GoodReductionJacobian.RelativeGroupLaw.baseChange_one NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_fst NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_snd NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_fst NeronSpecialFibreInfra.neronEndRestrictEquiv_apply NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_fst_assoc NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_snd NeronSpecialFibreInfra.neronEndExtension_genericFibreRestrict NeronSpecialFibreInfra.specClosedFibreInclusion_eq NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_fst_assoc NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_snd_assoc NeronSpecialFibreInfra.genericFibreRestrict_neronEndExtension NeronSpecialFibreInfra.homOverId_coe NeronSpecialFibreInfra.homOverComp_coe NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_snd_assoc"

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian CerednikDrinfeld CerednikDrinfeld.QM CerednikDrinfeld.QM.FakeEllipticCurve
open scoped Quaternion

namespace RoadT
namespace SEP

theorem exists_section_of_isFinite {k : Type u} [Field k] [IsAlgClosed k] {F : Scheme.{u}}
    (g : F ⟶ Spec (CommRingCat.of k)) [IsFinite g] [Nonempty ↥F] :
    ∃ s : Spec (CommRingCat.of k) ⟶ F, s ≫ g = 𝟙 _ := by
  classical
  haveI : IsAffine F := isAffine_of_isAffineHom g
  let A : CommRingCat := Γ(F, ⊤)

  let κ : k →+* A := g.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of k)).inv.hom
  have hfin : g.appTop.hom.Finite := IsFinite.finite_app (f := g) ⊤ (isAffineOpen_top _)
  letI : Algebra k A := κ.toAlgebra
  have hinvsurj : Function.Surjective (Scheme.ΓSpecIso (CommRingCat.of k)).inv.hom := fun a =>
    ⟨(Scheme.ΓSpecIso (CommRingCat.of k)).hom a, Iso.hom_inv_id_apply _ a⟩
  haveI : Module.Finite k A := by
    have : κ.Finite := hfin.comp (RingHom.Finite.of_surjective _ hinvsurj)
    exact this

  haveI : Nontrivial A := by
    obtain ⟨x⟩ := (inferInstance : Nonempty ↥F)
    let p : PrimeSpectrum A := F.isoSpec.hom.base x
    exact ⟨⟨0, 1, fun h => p.2.ne_top (by rw [Ideal.eq_top_iff_one, ← h]; exact p.1.zero_mem)⟩⟩
  obtain ⟨𝔪, h𝔪⟩ := Ideal.exists_maximal A
  letI : Field (A ⧸ 𝔪) := Ideal.Quotient.field 𝔪
  haveI : Module.Finite k (A ⧸ 𝔪) := Module.Finite.of_surjective (Ideal.Quotient.mkₐ k 𝔪).toLinearMap Ideal.Quotient.mk_surjective
  haveI : Algebra.IsIntegral k (A ⧸ 𝔪) := Algebra.IsIntegral.of_finite k _
  have hbij := IsAlgClosed.algebraMap_bijective_of_isIntegral (k := k) (K := A ⧸ 𝔪)
  let e : k ≃+* (A ⧸ 𝔪) := RingEquiv.ofBijective (algebraMap k (A ⧸ 𝔪)) hbij
  let σ : A →+* k := e.symm.toRingHom.comp (Ideal.Quotient.mk 𝔪)
  have hσ : σ.comp κ = RingHom.id k := by
    ext c
    show e.symm (Ideal.Quotient.mk 𝔪 (κ c)) = c
    have : Ideal.Quotient.mk 𝔪 (κ c) = algebraMap k (A ⧸ 𝔪) c := rfl
    rw [this]
    exact e.symm_apply_apply c

  refine ⟨Spec.map (CommRingCat.ofHom σ) ≫ F.isoSpec.inv, ?_⟩

  have hnat : F.isoSpec.inv ≫ g = Spec.map g.appTop ≫ (Spec (CommRingCat.of k)).isoSpec.inv :=
    (Scheme.isoSpec_inv_naturality g).symm
  rw [Category.assoc, hnat, ← Category.assoc, ← Spec.map_comp, Scheme.isoSpec_Spec_inv, ← Spec.map_comp]
  have : (Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫ Scheme.Hom.appTop g ≫ CommRingCat.ofHom σ = 𝟙 _ := by
    ext c
    change σ (κ c) = c
    exact congrArg (fun φ => φ c) hσ
  first
    | rw [this, Spec.map_id]
    | (rw [Category.assoc, this, Spec.map_id])
    | (rw [← Category.assoc] at this; rw [this, Spec.map_id])

theorem exists_comp_eq_of_isFinite_of_surjective {k : Type u} [Field k] [IsAlgClosed k] {X Y : Scheme.{u}}
    (φ : X ⟶ Y) [IsFinite φ] [Surjective φ] (Q : Spec (CommRingCat.of k) ⟶ Y) :
    ∃ P : Spec (CommRingCat.of k) ⟶ X, P ≫ φ = Q := by
  let g := pullback.snd φ Q
  haveI : IsFinite g := inferInstance
  haveI : Surjective g := inferInstance
  haveI : Nonempty ↥(pullback φ Q) := by
    obtain ⟨x, -⟩ := g.surjective ⟨⊥, Ideal.bot_prime⟩
    exact ⟨x⟩
  obtain ⟨s, hs⟩ := exists_section_of_isFinite g
  refine ⟨s ≫ pullback.fst φ Q, ?_⟩
  rw [Category.assoc, pullback.condition, ← Category.assoc, hs, Category.id_comp]

end RoadT.SEP

namespace RoadT
namespace SEP
namespace M2

theorem exists_natCard_eq_pow_two_mul (ℓ : ℕ) [Fact ℓ.Prime] (V : Type u) [AddCommGroup V]
    [Module (Matrix (Fin 2) (Fin 2) (ZMod ℓ)) V] [Finite V] :
    ∃ k : ℕ, Nat.card V = ℓ ^ (2 * k) := by
  classical
  haveI : Small.{0} V := inferInstance
  let e : Shrink.{0} V ≃ₗ[Matrix (Fin 2) (Fin 2) (ZMod ℓ)] V := Shrink.linearEquiv _ V
  haveI : Finite (Shrink.{0} V) := Finite.of_equiv V e.toEquiv.symm
  obtain ⟨k, hk⟩ := Matrix.exists_natCard_eq_pow_two_mul_of_module_zmod ℓ (Shrink.{0} V)
  exact ⟨k, by rw [← hk, Nat.card_congr e.toEquiv]⟩

theorem sq_le_natCard (ℓ : ℕ) [Fact ℓ.Prime] (V : Type u) [AddCommGroup V]
    [Module (Matrix (Fin 2) (Fin 2) (ZMod ℓ)) V] [Finite V] [Nontrivial V] :
    ℓ ^ 2 ≤ Nat.card V := by
  obtain ⟨k, hk⟩ := exists_natCard_eq_pow_two_mul ℓ V
  have h1 : 1 < Nat.card V := Finite.one_lt_card
  have hk0 : k ≠ 0 := by
    rintro rfl
    rw [hk, mul_zero, pow_zero] at h1
    exact lt_irrefl _ h1
  rw [hk]
  exact Nat.pow_le_pow_right (Fact.out : ℓ.Prime).pos (by omega)

end RoadT.SEP.M2

namespace B12Insep

variable {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} {N : ℕ} {S : Type u} [CommRing S]

theorem ratCast_natCast_mem (hΛ : QuaternionAlgebra.IsOrder Λ) (n : ℕ) :
    ((n : ℚ) : ℍ[ℚ, a, b]) ∈ Λ := by
  have h := Submodule.smul_mem Λ (n : ℤ) hΛ.one_mem
  have e : ((n : ℤ) • (1 : ℍ[ℚ, a, b])) = ((n : ℚ) : ℍ[ℚ, a, b]) := by
    rw [zsmul_eq_mul, mul_one]; push_cast; rfl
  rw [e] at h; exact h

def natElt (hΛ : QuaternionAlgebra.IsOrder Λ) (n : ℕ) : ↥Λ := ⟨((n : ℚ) : ℍ[ℚ, a, b]), ratCast_natCast_mem hΛ n⟩

theorem pushPt_act_congr (E : FakeEllipticCurve Λ N S) {x y : ↥Λ} (h : x = y)
    {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of S)) (P : SchemeHomOver t E.f) :
    pushPt (E.act x) (E.act_over x) P = pushPt (E.act y) (E.act_over y) P := by
  subst h; rfl

theorem pushPt_act_zero (E : FakeEllipticCurve Λ N S) (hΛ : QuaternionAlgebra.IsOrder Λ)
    {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of S)) (P : SchemeHomOver t E.f) :
    pushPt (E.act (natElt hΛ 0)) (E.act_over (natElt hΛ 0)) P = E.L.one t := by
  have hsum : natElt hΛ 0 + natElt hΛ 0 = natElt hΛ 0 := by
    apply Subtype.ext; simp [natElt]
  have h := E.act_add (natElt hΛ 0) (natElt hΛ 0) t P
  rw [pushPt_act_congr E hsum t P] at h

  letI : Group (SchemeHomOver t E.f) := E.L.pointGroup t
  have h' : pushPt (E.act (natElt hΛ 0)) (E.act_over (natElt hΛ 0)) P =
      pushPt (E.act (natElt hΛ 0)) (E.act_over (natElt hΛ 0)) P *
        pushPt (E.act (natElt hΛ 0)) (E.act_over (natElt hΛ 0)) P := h
  have := mul_left_cancel (a := pushPt (E.act (natElt hΛ 0)) (E.act_over (natElt hΛ 0)) P)
    (b := 1) (c := pushPt (E.act (natElt hΛ 0)) (E.act_over (natElt hΛ 0)) P) (by rw [mul_one]; exact h')
  exact this.symm

theorem pushPt_act_one (E : FakeEllipticCurve Λ N S) (hΛ : QuaternionAlgebra.IsOrder Λ)
    {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of S)) (P : SchemeHomOver t E.f) :
    pushPt (E.act (natElt hΛ 1)) (E.act_over (natElt hΛ 1)) P = P := by
  have h1 : natElt hΛ 1 = ⟨1, hΛ.one_mem⟩ := by apply Subtype.ext; simp [natElt]
  rw [pushPt_act_congr E h1 t P]
  apply Subtype.ext
  simp [pushPt, mapPt, E.act_one hΛ.one_mem]

theorem pushPt_act_natCast (E : FakeEllipticCurve Λ N S) (hΛ : QuaternionAlgebra.IsOrder Λ) (n : ℕ)
    {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of S)) (P : SchemeHomOver t E.f) :
    pushPt (E.act (natElt hΛ n)) (E.act_over (natElt hΛ n)) P = nsmulPt E.L t n P := by
  induction n with
  | zero => exact pushPt_act_zero E hΛ t P
  | succ n ih =>
    have hsum : natElt hΛ n + natElt hΛ 1 = natElt hΛ (n + 1) := by
      apply Subtype.ext; simp [natElt]
    rw [← pushPt_act_congr E hsum t P, E.act_add, ih, pushPt_act_one]
    rfl

def univPt (E : FakeEllipticCurve Λ N S) : SchemeHomOver E.f E.f := ⟨𝟙 E.A, Category.id_comp _⟩

theorem act_natCast_eq_of_forall_nsmulPt (E : FakeEllipticCurve Λ N S) (hΛ : QuaternionAlgebra.IsOrder Λ) (n : ℕ)
    (g : E.A ⟶ E.A) (hg : g ≫ E.f = E.f)
    (h : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of S)) (P : SchemeHomOver t E.f),
      mapPt g hg P = nsmulPt E.L t n P) :
    g = E.act (natElt hΛ n) := by
  have h1 := h E.f (univPt E)
  rw [← pushPt_act_natCast E hΛ n E.f (univPt E)] at h1
  have h2 := congrArg Subtype.val h1
  simpa [mapPt, pushPt, univPt] using h2

variable {ℓ : ℕ} [Fact ℓ.Prime] [CharP S ℓ]

theorem F_comp_V (hΛ : QuaternionAlgebra.IsOrder Λ) {E Eℓ : FakeEllipticCurve Λ N S}
    (D : FrobeniusVerschiebungData ℓ E Eℓ) : D.F ≫ D.V = E.act (natElt hΛ ℓ) := by
  apply act_natCast_eq_of_forall_nsmulPt E hΛ ℓ (D.F ≫ D.V) (by rw [Category.assoc, D.V_over, D.F_over])
  intro T t P
  have := D.V_F t P
  rw [← this]
  apply Subtype.ext
  simp [mapPt]

theorem V_comp_F (hΛ : QuaternionAlgebra.IsOrder Λ) {E Eℓ : FakeEllipticCurve Λ N S}
    (D : FrobeniusVerschiebungData ℓ E Eℓ) : D.V ≫ D.F = Eℓ.act (natElt hΛ ℓ) := by
  apply act_natCast_eq_of_forall_nsmulPt Eℓ hΛ ℓ (D.V ≫ D.F) (by rw [Category.assoc, D.F_over, D.V_over])
  intro T t Q
  have := D.F_V t Q
  rw [← this]
  apply Subtype.ext
  simp [mapPt]

theorem isLevelIsogeny_of_isFrobeniusKernel (hΛ : QuaternionAlgebra.IsOrder Λ)
    {E Eℓ : FakeEllipticCurve Λ N S} (K : E.ExtraLevel ℓ) (D : FrobeniusVerschiebungData ℓ E Eℓ)
    (hK : IsFrobeniusKernel (⟨E, K⟩ : WithExtraLevel Λ N ℓ S) D) :
    IsLevelIsogeny ℓ (⟨E, K⟩ : WithExtraLevel Λ N ℓ S) Eℓ := by
  refine ⟨D.F, D.F_over, D.V, D.V_over, D.F_hom, D.V_hom, D.F_act, D.V_act, ?_, ?_, D.F_lev⟩
  · intro hℓ
    exact ⟨F_comp_V hΛ D, V_comp_F hΛ D⟩
  · intro T t P
    exact (hK t P).symm

end B12Insep

namespace HeckeBeta

variable {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} {N : ℕ} {S : Type u} [CommRing S]

theorem nsmulPt_eq_pow (E : FakeEllipticCurve Λ N S) {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of S)) (n : ℕ)
    (P : SchemeHomOver t E.f) :
    letI := E.L.pointGroup t
    nsmulPt E.L t n P = P ^ n := by
  letI := E.L.pointGroup t
  induction n with
  | zero => rfl
  | succ n ih => show E.L.mul t (nsmulPt E.L t n P) P = P ^ (n + 1); rw [ih, pow_succ]; rfl

end HeckeBeta

open B12Insep HeckeBeta in
theorem solution
    {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} {N : ℕ}
    (k : Type u) [Field k] [IsAlgClosed k] (ℓ : ℕ) [Fact ℓ.Prime] [CharP k ℓ] (hℓN : ¬ ℓ ∣ N)
    (hΛ : QuaternionAlgebra.IsMaximalOrder Λ)
    {q q' : ℕ} [Fact q.Prime] [Fact q'.Prime] (hB : QuaternionAlgebra.IsIndefiniteRamifiedExactlyAt a b q q')
    (hℓq : ℓ ≠ q) (hℓq' : ℓ ≠ q')
    (E Eℓ : FakeEllipticCurve Λ N k) (D : FrobeniusVerschiebungData ℓ E Eℓ)
    (K : E.ExtraLevel ℓ) (d : FakeEllipticCurve Λ N k)
    (φ : E.A ⟶ d.A) (hφ : φ ≫ d.f = E.f) (ψ : d.A ⟶ E.A) (hψ : ψ ≫ E.f = d.f)
    (hφmul : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of k)) (P Q : SchemeHomOver t E.f),
      mapPt φ hφ (E.L.mul t P Q) = d.L.mul t (mapPt φ hφ P) (mapPt φ hφ Q))
    (hψmul : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of k)) (P Q : SchemeHomOver t d.f),
      mapPt ψ hψ (d.L.mul t P Q) = E.L.mul t (mapPt ψ hψ P) (mapPt ψ hψ Q))
    (hφact : ∀ x : ↥Λ, E.act x ≫ φ = φ ≫ d.act x) (hψact : ∀ x : ↥Λ, d.act x ≫ ψ = ψ ≫ E.act x)
    (hcomp : ∀ hℓ : ((ℓ : ℚ) : ℍ[ℚ, a, b]) ∈ Λ,
      φ ≫ ψ = E.act ⟨((ℓ : ℚ) : ℍ[ℚ, a, b]), hℓ⟩ ∧ ψ ≫ φ = d.act ⟨((ℓ : ℚ) : ℍ[ℚ, a, b]), hℓ⟩)
    (hker : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of k)) (P : SchemeHomOver t E.f),
      mapPt φ hφ P = d.L.one t ↔ FactorsThrough K.levK P)
    (hlev : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of k)) (P : SchemeHomOver t E.f),
      FactorsThrough E.lev P → FactorsThrough d.lev (mapPt φ hφ P))
    (hK : ∃ P : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) E.f,
      FactorsThrough K.levK P ∧ P ≠ E.L.one (𝟙 (Spec (CommRingCat.of k)))) :
    ∀ Q : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) d.f,
      mapPt ψ hψ Q = E.L.one (𝟙 (Spec (CommRingCat.of k))) → Q = d.L.one (𝟙 (Spec (CommRingCat.of k))) := by
  classical
  intro Q hQ

  let t₁ : Spec (CommRingCat.of k) ⟶ Spec (CommRingCat.of k) := 𝟙 _
  have hℓΛ : ((ℓ : ℚ) : ℍ[ℚ, a, b]) ∈ Λ := ratCast_natCast_mem hΛ.isOrder ℓ

  have hψφ : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of k)) (P : SchemeHomOver t E.f),
      mapPt ψ hψ (mapPt φ hφ P) = nsmulPt E.L t ℓ P := by
    intro T t P
    rw [← pushPt_act_natCast E hΛ.isOrder ℓ t P]
    apply Subtype.ext
    simp only [mapPt_coe, Category.assoc, (hcomp hℓΛ).1]
    rfl
  have hφψ : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of k)) (Q : SchemeHomOver t d.f),
      mapPt φ hφ (mapPt ψ hψ Q) = nsmulPt d.L t ℓ Q := by
    intro T t Q
    rw [← pushPt_act_natCast d hΛ.isOrder ℓ t Q]
    apply Subtype.ext
    simp only [mapPt_coe, Category.assoc, (hcomp hℓΛ).2]
    rfl

  obtain ⟨hsurj, hfinφ, -⟩ := CerednikDrinfeld.QM.surjective_and_isFinite_and_flat_of_mapPt_mapPt_eq_nsmulPt
    E.L E.comm E.bundle d.L d.comm d.bundle φ hφ hφmul ψ hψ ℓ (Fact.out : ℓ.Prime).pos hψφ hφψ
  haveI := hsurj
  haveI := hfinφ
  obtain ⟨P₁, hP₁⟩ := RoadT.SEP.exists_comp_eq_of_isFinite_of_surjective (k := k) φ Q.1
  let P : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) E.f := ⟨P₁, by rw [← hφ, ← Category.assoc, hP₁]; exact Q.2⟩
  have hPQ : mapPt φ hφ P = Q := Subtype.ext hP₁

  have hPtors : nsmulPt E.L (𝟙 _) ℓ P = E.L.one (𝟙 _) := by rw [← hψφ, hPQ, hQ]

  suffices hTK : ∀ R : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) E.f,
      nsmulPt E.L (𝟙 _) ℓ R = E.L.one (𝟙 _) → FactorsThrough K.levK R by
    rw [← hPQ]; exact (hker _ P).mpr (hTK P hPtors)

  obtain ⟨hTfin, hTcard⟩ := CerednikDrinfeld.QM.FakeEllipticCurve.finite_and_natCard_torsionPoints_le_sq_of_charP_of_not_dvd k ℓ hℓN E

  letI grp : CommGroup (SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) E.f) :=
    { E.L.pointGroup (𝟙 _) with mul_comm := E.comm (𝟙 _) }
  let KS : Subgroup (SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) E.f) :=
    { carrier := {R | FactorsThrough K.levK R}
      mul_mem' := fun {x y} hx hy => (K.levK_sub (𝟙 _) x y hx hy).1
      one_mem' := K.levK_one (𝟙 _)
      inv_mem' := fun {x} hx => (K.levK_sub (𝟙 _) x x hx hx).2 }

  let TT := {R : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) E.f // nsmulPt E.L (𝟙 (Spec (CommRingCat.of k))) ℓ R = E.L.one (𝟙 (Spec (CommRingCat.of k)))}
  haveI : Finite TT := hTfin
  let ι : ↥KS → TT := fun R => ⟨R.1, K.levK_torsion (𝟙 _) R.1 R.2⟩
  have hιinj : Function.Injective ι := fun x y h => Subtype.ext (congrArg (fun z : TT => z.1) h)
  haveI hKSfin : Finite ↥KS := Finite.of_injective ι hιinj
  let V := Additive ↥KS
  haveI : Finite V := hKSfin

  have hpow : ∀ R : ↥KS, R ^ ℓ = 1 := by
    intro R
    apply Subtype.ext
    show (R : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) E.f) ^ ℓ = E.L.one (𝟙 _)
    rw [← nsmulPt_eq_pow]; exact K.levK_torsion (𝟙 _) R.1 R.2
  have hV : ∀ v : V, ℓ • v = 0 := by
    intro v
    rw [← ofMul_toMul v, ← ofMul_pow, hpow]; rfl

  have hord := hΛ.isOrder
  have hmulΛ : ∀ x y : ↥Λ, (x : ℍ[ℚ, a, b]) * (y : ℍ[ℚ, a, b]) ∈ Λ := fun x y => hord.mul_mem x.2 y.2
  let actM : ↥Λ → ↥KS →* ↥KS := fun m =>
    { toFun := fun R => ⟨pushPt (E.act m) (E.act_over m) R.1, K.levK_stable m (𝟙 _) R.1 R.2⟩
      map_one' := by
        apply Subtype.ext
        show pushPt (E.act m) (E.act_over m) (E.L.one (𝟙 _)) = E.L.one (𝟙 _)

        have h := E.act_hom m (𝟙 _) (E.L.one (𝟙 _)) (E.L.one (𝟙 _))
        rw [E.L.one_mul] at h
        have h' : pushPt (E.act m) (E.act_over m) (E.L.one (𝟙 _)) =
            pushPt (E.act m) (E.act_over m) (E.L.one (𝟙 _)) * pushPt (E.act m) (E.act_over m) (E.L.one (𝟙 _)) := h
        exact mul_eq_left.mp h'.symm
      map_mul' := fun R R' => Subtype.ext (E.act_hom m (𝟙 _) R.1 R'.1) }
  have hactM : ∀ (m : ↥Λ) (R : ↥KS), ((actM m R : ↥KS) : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) E.f) =
      pushPt (E.act m) (E.act_over m) R.1 := fun _ _ => rfl
  let act : ↥Λ → V →+ V := fun m => MonoidHom.toAdditive (actM m)
  have hact1 : act ⟨1, hord.one_mem⟩ = AddMonoidHom.id V := by
    refine AddMonoidHom.ext fun v => ?_
    change Additive.ofMul (actM ⟨1, hord.one_mem⟩ (Additive.toMul v)) = Additive.ofMul (Additive.toMul v)
    congr 1
    apply Subtype.ext; rw [hactM]; apply Subtype.ext
    show (Additive.toMul v).1.1 ≫ E.act ⟨1, hord.one_mem⟩ = (Additive.toMul v).1.1
    rw [E.act_one hord.one_mem, Category.comp_id]
  have hactmul : ∀ x y : ↥Λ, act ⟨_, hmulΛ x y⟩ = (act x).comp (act y) := by
    intro x y
    refine AddMonoidHom.ext fun v => ?_
    change Additive.ofMul (actM ⟨_, hmulΛ x y⟩ (Additive.toMul v)) = Additive.ofMul (actM x (actM y (Additive.toMul v)))
    congr 1
    apply Subtype.ext; rw [hactM, hactM]; apply Subtype.ext
    show (Additive.toMul v).1.1 ≫ E.act ⟨_, hmulΛ x y⟩ = ((Additive.toMul v).1.1 ≫ E.act y) ≫ E.act x
    rw [E.act_mul x y (hmulΛ x y), Category.assoc]
  have hactadd : ∀ x y : ↥Λ, act (x + y) = act x + act y := by
    intro x y
    refine AddMonoidHom.ext fun v => ?_
    change Additive.ofMul (actM (x + y) (Additive.toMul v)) = Additive.ofMul (actM x (Additive.toMul v) * actM y (Additive.toMul v))
    congr 1
    apply Subtype.ext; rw [hactM]
    exact E.act_add x y (𝟙 _) _

  obtain ⟨φΛ, hφ1, hφmul', hφsurj, hφker⟩ :=
    QuaternionAlgebra.exists_linearMap_matrix_zmod_of_isMaximalOrder_of_ne hB Λ hΛ ℓ hℓq hℓq'
  obtain ⟨inst, -⟩ := QuaternionAlgebra.exists_module_matrix_zmod_of_smul_eq_zero_of_linearMap Λ ℓ φΛ hφ1 hφmul' hφsurj hφker
    hord.one_mem hmulΛ V hV act hact1 hactmul hactadd
  letI := inst

  obtain ⟨P₀, hP₀K, hP₀ne⟩ := hK
  haveI : Nontrivial V := ⟨⟨Additive.ofMul ⟨P₀, hP₀K⟩, 0, fun h => hP₀ne (congrArg (fun z : V => (Additive.toMul z).1) h)⟩⟩
  obtain ⟨kk, hkk⟩ := RoadT.SEP.M2.exists_natCard_eq_pow_two_mul ℓ V
  have hℓ1 : 1 < ℓ := (Fact.out : ℓ.Prime).one_lt
  have hcardV : ℓ ^ 2 ≤ Nat.card V := by
    rw [hkk]
    have : 1 < Nat.card V := Finite.one_lt_card
    rw [hkk] at this
    have hk0 : kk ≠ 0 := by rintro rfl; simp at this
    exact Nat.pow_le_pow_right hℓ1.le (by omega)
  have hcardKS : Nat.card ↥KS = Nat.card V := rfl
  have hle : Nat.card TT ≤ Nat.card ↥KS := by rw [hcardKS]; exact hTcard.trans hcardV
  have hge : Nat.card ↥KS ≤ Nat.card TT := Nat.card_le_card_of_injective ι hιinj

  haveI := Fintype.ofFinite ↥KS
  haveI := Fintype.ofFinite TT
  have hbij : Function.Bijective ι := by
    rw [Fintype.bijective_iff_injective_and_card]
    refine ⟨hιinj, ?_⟩
    rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card]
    exact le_antisymm hge hle
  intro R hR
  obtain ⟨R', hR'⟩ := hbij.2 ⟨R, hR⟩
  have : (R' : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) E.f) = R := congrArg Subtype.val hR'
  rw [← this]; exact R'.2

end S_CerednikDrinfeld_QM_FakeEllipticCurve_forall_mapPt_eq_one_of_isLevelIsogeny_of_exists_factorsThrough_ne_one
end P2MW
export P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_forall_mapPt_eq_one_of_isLevelIsogeny_of_exists_factorsThrough_ne_one (solution)
