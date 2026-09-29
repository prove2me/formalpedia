-- Prove2me | solution 1 for CerednikDrinfeld.QM.FakeEllipticCurve.isSquare_or_sq_lt_four_mul_of_forall_act_comp_eq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.141142+00:00
-- url     : https://prove2.me/submissions/65efa1a5-19b4-5c24-a4ab-4ae877f4f6de

import Definitions.Def_CerednikDrinfeld_QMModuli
import Definitions.Def_AlgebraicGeometry_RelativeGroupLawEndDegree
import Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_exists_isHomogeneous_eval_eq_endDegree_of_abelianSchemePropertyBundle
import Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_endDegree_schemeHomOverComp_of_isFinite_of_flat
import Theorems.Thm_CerednikDrinfeld_QM_surjective_and_isFinite_and_flat_of_mapPt_mapPt_eq_nsmulPt
import Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_exists_forall_nsmul_eq_one_of_isFinite_pullback_snd
import Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_natCard_isTorsionPoint_eq_pow_of_natCast_ne_zero
import Theorems.Thm_QuaternionAlgebra_IsIndefiniteRamifiedExactlyAt_isUnit_of_ne_zero
import Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_smoothOfRelativeDimension_two
import Theorems.Thm_MvPolynomial_isSquare_or_isSquare_of_isHomogeneous_of_forall_eval_mul_eq
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_isSquare_or_sq_lt_four_mul_of_forall_act_comp_eq
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

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian IsDedekindDomain AlgebraicCurve QuaternionAlgebra CerednikDrinfeld CerednikDrinfeld.QM

open scoped Quaternion TensorProduct NumberField

universe u

namespace P2mKcRmExclusion

section Ring

def mulV {R : Type*} [CommRing R] (D c : R) (v w : Fin 4 → R) : Fin 4 → R :=
  ![v 0 * w 0 + D * (v 1 * w 1) + c * (v 2 * w 2) + D * c * (v 3 * w 3),
    v 0 * w 1 + v 1 * w 0 + c * (v 2 * w 3 + v 3 * w 2),
    v 0 * w 2 + v 2 * w 0 + D * (v 1 * w 3 + v 3 * w 1),
    v 0 * w 3 + v 3 * w 0 + v 1 * w 2 + v 2 * w 1]

def e0 : Fin 4 → ℤ := ![1, 0, 0, 0]

theorem mulV_comm (D c : ℤ) (v w : Fin 4 → ℤ) : mulV D c v w = mulV D c w v := by
  ext i; fin_cases i <;> simp [mulV] <;> ring

theorem mulV_e0 (D c : ℤ) (v : Fin 4 → ℤ) : mulV D c v e0 = v := by
  ext i; fin_cases i <;> simp [mulV, e0]

theorem mulV_add_smul_e0_left (D c : ℤ) (v w : Fin 4 → ℤ) (t : ℤ) :
    mulV D c (v + t • e0) w = mulV D c v w + t • w := by
  ext i; fin_cases i <;> simp [mulV, e0] <;> ring

def adjV (D c : ℤ) (v : Fin 4 → ℤ) : Fin 4 → ℤ :=
  mulV D c (mulV D c ![v 0, -v 1, v 2, -v 3] ![v 0, v 1, -v 2, -v 3]) ![v 0, -v 1, -v 2, v 3]

def normV (D c : ℤ) (v : Fin 4 → ℤ) : ℤ :=
  (v 0 ^ 2 + D * v 1 ^ 2 - c * v 2 ^ 2 - D * c * v 3 ^ 2) ^ 2 - D * (2 * (v 0 * v 1 - c * (v 2 * v 3))) ^ 2

theorem mulV_adjV (D c : ℤ) (v : Fin 4 → ℤ) : mulV D c v (adjV D c v) = normV D c v • e0 := by
  ext i; fin_cases i <;> simp [mulV, adjV, normV, e0] <;> ring

theorem normV_e0 (D c : ℤ) : normV D c e0 = 1 := by
  simp [normV, e0]

theorem mulV_neg_right (D c : ℤ) (v w : Fin 4 → ℤ) : mulV D c v (-w) = -mulV D c v w := by
  ext i; fin_cases i <;> simp [mulV] <;> ring

theorem exists_mulV_eq_smul_e0 (D c : ℤ) (v : Fin 4 → ℤ) (hv : normV D c v ≠ 0) :
    ∃ (w : Fin 4 → ℤ) (m : ℕ), 0 < m ∧ mulV D c v w = (m : ℤ) • e0 ∧ mulV D c w v = (m : ℤ) • e0 := by
  rcases lt_or_gt_of_ne hv with h | h
  · refine ⟨-adjV D c v, (normV D c v).natAbs, Int.natAbs_pos.mpr hv, ?_, ?_⟩
    · rw [mulV_neg_right, mulV_adjV, ← neg_smul, Int.ofNat_natAbs_of_nonpos h.le]
    · rw [mulV_comm, mulV_neg_right, mulV_adjV, ← neg_smul, Int.ofNat_natAbs_of_nonpos h.le]
  · refine ⟨adjV D c v, (normV D c v).natAbs, Int.natAbs_pos.mpr hv, ?_, ?_⟩
    · rw [mulV_adjV, Int.natAbs_of_nonneg h.le]
    · rw [mulV_comm, mulV_adjV, Int.natAbs_of_nonneg h.le]

noncomputable def normPoly (D c : ℤ) : MvPolynomial (Fin 4) ℚ :=
  (MvPolynomial.X 0 ^ 2 + MvPolynomial.C (D : ℚ) * MvPolynomial.X 1 ^ 2 - MvPolynomial.C (c : ℚ) * MvPolynomial.X 2 ^ 2 -
      MvPolynomial.C ((D * c : ℤ) : ℚ) * MvPolynomial.X 3 ^ 2) ^ 2 -
    MvPolynomial.C (D : ℚ) * (MvPolynomial.C 2 * (MvPolynomial.X 0 * MvPolynomial.X 1 -
      MvPolynomial.C (c : ℚ) * (MvPolynomial.X 2 * MvPolynomial.X 3))) ^ 2

theorem aeval_normPoly {S : Type*} [CommRing S] [Algebra ℚ S] (D c : ℤ) (x : Fin 4 → S) :
    MvPolynomial.aeval x (normPoly D c) =
      (x 0 ^ 2 + (D : S) * x 1 ^ 2 - (c : S) * x 2 ^ 2 - (D : S) * (c : S) * x 3 ^ 2) ^ 2 -
        (D : S) * (2 * (x 0 * x 1 - (c : S) * (x 2 * x 3))) ^ 2 := by
  simp [normPoly, map_sub, map_add, map_mul, map_pow, map_ofNat]

theorem eval_normPoly_intCast (D c : ℤ) (v : Fin 4 → ℤ) :
    MvPolynomial.eval (fun i => (v i : ℚ)) (normPoly D c) = (normV D c v : ℚ) := by
  simp only [normPoly, map_sub, map_add, map_mul, map_pow, MvPolynomial.eval_X, MvPolynomial.eval_C, normV]
  push_cast
  ring

theorem normPoly_ne_zero (D c : ℤ) : normPoly D c ≠ 0 := by
  intro h
  have := eval_normPoly_intCast D c e0
  rw [h, map_zero, normV_e0] at this
  norm_num at this

theorem map_mulV {R S : Type*} [CommRing R] [CommRing S] (φ : R →+* S) (D c : R) (v w : Fin 4 → R) :
    (fun i => φ (mulV D c v w i)) = mulV (φ D) (φ c) (fun i => φ (v i)) (fun i => φ (w i)) := by
  ext i
  fin_cases i <;> simp [mulV]

noncomputable def mulPoly (D c : ℚ) : Fin 4 → MvPolynomial (Fin 4 ⊕ Fin 4) ℚ :=
  mulV (MvPolynomial.C D) (MvPolynomial.C c) (fun i => MvPolynomial.X (Sum.inl i)) (fun i => MvPolynomial.X (Sum.inr i))

theorem aeval_mulPoly {S : Type*} [CommRing S] [Algebra ℚ S] (D c : ℚ) (x : Fin 4 ⊕ Fin 4 → S) (i : Fin 4) :
    MvPolynomial.aeval x (mulPoly D c i) =
      mulV (algebraMap ℚ S D) (algebraMap ℚ S c) (fun i => x (Sum.inl i)) (fun i => x (Sum.inr i)) i := by
  fin_cases i <;> simp [mulPoly, mulV]

theorem mul_of_generic (D c : ℤ) (F : (Fin 4 → ℤ) → ℕ) (P : MvPolynomial (Fin 4) ℚ)
    (hF : ∀ v : Fin 4 → ℤ, (F v : ℚ) = MvPolynomial.eval (fun i => (v i : ℚ)) P)
    (hgen : ∀ v w : Fin 4 → ℤ, normV D c v ≠ 0 → normV D c w ≠ 0 → F (mulV D c v w) = F v * F w)
    (v w : Fin 4 → ℤ) : F (mulV D c v w) = F v * F w := by
  classical
  set Q : MvPolynomial (Fin 4 ⊕ Fin 4) ℚ :=
    MvPolynomial.bind₁ (mulPoly D c) P -
      MvPolynomial.rename Sum.inl P * MvPolynomial.rename Sum.inr P with hQ

  have hQev : ∀ z : Fin 4 ⊕ Fin 4 → ℤ, MvPolynomial.aeval (fun i => (z i : ℚ)) Q =
      (F (mulV D c (fun i => z (Sum.inl i)) (fun i => z (Sum.inr i))) : ℚ) -
        F (fun i => z (Sum.inl i)) * F (fun i => z (Sum.inr i)) := by
    intro z
    rw [hQ, map_sub, map_mul, MvPolynomial.aeval_bind₁, MvPolynomial.aeval_rename, MvPolynomial.aeval_rename]
    simp only [aeval_mulPoly, MvPolynomial.aeval_eq_eval]
    have h1 : mulV (algebraMap ℚ ℚ (D : ℚ)) (algebraMap ℚ ℚ (c : ℚ)) (fun i => ((z (Sum.inl i)) : ℚ))
        (fun i => ((z (Sum.inr i)) : ℚ)) =
        fun i => ((mulV D c (fun i => z (Sum.inl i)) (fun i => z (Sum.inr i)) i : ℤ) : ℚ) := by
      have := map_mulV (Int.castRingHom ℚ) D c (fun i => z (Sum.inl i)) (fun i => z (Sum.inr i))
      simp only [eq_intCast] at this
      rw [this]
      simp
    rw [h1, ← hF, show ((fun i => (z i : ℚ)) ∘ Sum.inl) = fun i => ((z (Sum.inl i) : ℤ) : ℚ) from rfl,
      show ((fun i => (z i : ℚ)) ∘ Sum.inr) = fun i => ((z (Sum.inr i) : ℤ) : ℚ) from rfl, ← hF, ← hF]

  have hQN : Q * (MvPolynomial.rename Sum.inl (normPoly D c) * MvPolynomial.rename Sum.inr (normPoly D c)) = 0 := by
    apply MvPolynomial.funext_set (fun _ => Set.range (Int.cast : ℤ → ℚ))
      (fun _ => Set.infinite_range_of_injective Int.cast_injective)
    intro x hx
    rw [Set.mem_univ_pi] at hx
    choose z hz using hx
    have hxz : x = fun i => (z i : ℚ) := funext fun i => (hz i).symm
    rw [map_zero]
    change MvPolynomial.aeval x _ = 0
    rw [map_mul, map_mul, MvPolynomial.aeval_rename, MvPolynomial.aeval_rename, hxz, hQev,
      show ((fun i => (z i : ℚ)) ∘ Sum.inl) = fun i => ((z (Sum.inl i) : ℤ) : ℚ) from rfl,
      show ((fun i => (z i : ℚ)) ∘ Sum.inr) = fun i => ((z (Sum.inr i) : ℤ) : ℚ) from rfl,
      MvPolynomial.aeval_eq_eval, MvPolynomial.aeval_eq_eval, eval_normPoly_intCast, eval_normPoly_intCast]
    by_cases h1 : normV D c (fun i => z (Sum.inl i)) = 0
    · rw [h1]; simp
    by_cases h2 : normV D c (fun i => z (Sum.inr i)) = 0
    · rw [h2]; simp
    rw [hgen _ _ h1 h2]
    push_cast
    ring
  have hN : MvPolynomial.rename Sum.inl (normPoly D c) * MvPolynomial.rename Sum.inr (normPoly D c) ≠
      (0 : MvPolynomial (Fin 4 ⊕ Fin 4) ℚ) := by
    refine mul_ne_zero ?_ ?_
    · exact (MvPolynomial.rename_injective _ Sum.inl_injective).ne_iff' (map_zero _) |>.mpr (normPoly_ne_zero D c)
    · exact (MvPolynomial.rename_injective _ Sum.inr_injective).ne_iff' (map_zero _) |>.mpr (normPoly_ne_zero D c)
  have hQ0 : Q = 0 := (mul_eq_zero.mp hQN).resolve_right hN
  have := hQev (Sum.elim v w)
  rw [hQ0, map_zero] at this
  simp only [Sum.elim_inl, Sum.elim_inr] at this
  have h : (F (mulV D c v w) : ℚ) = F v * F w := by linear_combination -this
  exact_mod_cast h

end Ring

section Group

variable {G : Type*} [CommGroup G]

def uHom (σ τ : G →* G) (v : Fin 4 → ℤ) : G →* G :=
  zpowGroupHom (v 0) * (zpowGroupHom (v 1)).comp σ * (zpowGroupHom (v 2)).comp τ *
    (zpowGroupHom (v 3)).comp (σ.comp τ)

theorem uHom_apply (σ τ : G →* G) (v : Fin 4 → ℤ) (P : G) :
    uHom σ τ v P = P ^ v 0 * σ P ^ v 1 * τ P ^ v 2 * σ (τ P) ^ v 3 := rfl

theorem uHom_e0 (σ τ : G →* G) (P : G) : uHom σ τ e0 P = P := by
  simp [uHom_apply, e0]

theorem uHom_smul_e0 (σ τ : G →* G) (m : ℤ) (P : G) : uHom σ τ (m • e0) P = P ^ m := by
  simp [uHom_apply, e0]

theorem uHom_uHom (σ τ : G →* G) (D c : ℤ) (hστ : ∀ P, σ (τ P) = τ (σ P))
    (hσ : ∀ P, σ (σ P) = P ^ D) (hτ : ∀ P, τ (τ P) = P ^ c) (v w : Fin 4 → ℤ) (P : G) :
    uHom σ τ w (uHom σ τ v P) = uHom σ τ (mulV D c v w) P := by

  let s : Additive G →+ Additive G := MonoidHom.toAdditive σ
  let t : Additive G →+ Additive G := MonoidHom.toAdditive τ
  have hs : ∀ m : Additive G, s (s m) = D • m := fun m => by
    change Additive.ofMul (σ (σ (Additive.toMul m))) = _
    rw [hσ]; rfl
  have ht : ∀ m : Additive G, t (t m) = c • m := fun m => by
    change Additive.ofMul (τ (τ (Additive.toMul m))) = _
    rw [hτ]; rfl
  have hts : ∀ m : Additive G, t (s m) = s (t m) := fun m => by
    change Additive.ofMul (τ (σ (Additive.toMul m))) = Additive.ofMul (σ (τ (Additive.toMul m)))
    rw [hστ]
  have key : ∀ (v : Fin 4 → ℤ) (P : G),
      Additive.ofMul (uHom σ τ v P) = v 0 • Additive.ofMul P + v 1 • s (Additive.ofMul P) +
        v 2 • t (Additive.ofMul P) + v 3 • s (t (Additive.ofMul P)) := by
    intro v P
    rw [uHom_apply]
    rfl
  apply Additive.ofMul.injective
  rw [key w (uHom σ τ v P), key v P, key (mulV D c v w) P]
  simp only [map_add, map_zsmul, hts, hs, ht, mulV, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.tail_cons, Matrix.cons_val_three]
  module

end Group

section Torsion

variable {K : Type u} [Field K] {A : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of K)}

theorem nsmul_eq_pow (L : RelativeGroupLaw K f) (hc : L.IsCommutative) {T : Scheme.{u}}
    (t : T ⟶ Spec (CommRingCat.of K)) (m : ℕ) (x : SchemeHomOver t f) :
    L.nsmul t m x = (letI := L.pointCommGroup hc t; x ^ m) := by
  letI := L.pointCommGroup hc t
  induction m with
  | zero => rfl
  | succ m ih => rw [L.nsmul_succ, ih, pow_succ]; rfl

theorem nsmulPt_eq_pow (L : RelativeGroupLaw K f) (hc : L.IsCommutative) {T : Scheme.{u}}
    (t : T ⟶ Spec (CommRingCat.of K)) (m : ℕ) (x : SchemeHomOver t f) :
    nsmulPt L t m x = (letI := L.pointCommGroup hc t; x ^ m) := by
  letI := L.pointCommGroup hc t
  induction m with
  | zero => rfl
  | succ m ih => rw [nsmulPt, ih, pow_succ]; rfl

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
    (hA : AbelianSchemePropertyBundle K f) (g : ℕ) (hg : 0 < g) [SmoothOfRelativeDimension g f] (M : ℤ)
    (h : ∀ P : SchemeHomOver (𝟙 (Spec (CommRingCat.of K))) f,
      letI := L.pointCommGroup hc (𝟙 (Spec (CommRingCat.of K))); P ^ M = 1) : M = 0 := by
  by_contra hM
  letI := L.pointCommGroup hc (𝟙 (Spec (CommRingCat.of K)))
  obtain ⟨ℓ, hle, hℓ⟩ := Nat.exists_infinite_primes (M.natAbs + ringChar K + 1)
  have hℓK : (ℓ : K) ≠ 0 := natCast_ne_zero_of_ringChar_lt ℓ hℓ (by omega)
  have hcard := GoodReductionJacobian.RelativeGroupLaw.natCard_isTorsionPoint_eq_pow_of_natCast_ne_zero
    K f L hc hA g ℓ hℓK
  haveI : Finite {x : SchemeHomOver (𝟙 (Spec (CommRingCat.of K))) f //
      L.IsTorsionPoint (𝟙 (Spec (CommRingCat.of K))) ℓ x} := by
    apply Nat.finite_of_card_ne_zero
    rw [hcard]
    exact pow_ne_zero _ hℓ.ne_zero
  haveI : Nontrivial {x : SchemeHomOver (𝟙 (Spec (CommRingCat.of K))) f //
      L.IsTorsionPoint (𝟙 (Spec (CommRingCat.of K))) ℓ x} := by
    rw [← Finite.one_lt_card_iff_nontrivial, hcard]
    exact Nat.one_lt_pow (by omega) hℓ.one_lt
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

theorem mapPt_id {T : Scheme.{u}} {s : T ⟶ Spec (CommRingCat.of K)} (h : 𝟙 A ≫ f = f) (Q : SchemeHomOver s f) :
    mapPt (𝟙 A) h Q = Q := by
  apply Subtype.ext
  simp [mapPt]

theorem mapPt_mapPt (φ : A ⟶ A) (hφ : φ ≫ f = f) (ψ : A ⟶ A) (hψ : ψ ≫ f = f)
    {T : Scheme.{u}} {s : T ⟶ Spec (CommRingCat.of K)} (P : SchemeHomOver s f) :
    mapPt ψ hψ (mapPt φ hφ P) = mapPt (φ ≫ ψ) (by rw [Category.assoc, hψ, hφ]) P := by
  apply Subtype.ext
  simp [mapPt]

theorem mapPt_schemeHomOverComp (β γ : SchemeHomOver f f)
    {T : Scheme.{u}} {s : T ⟶ Spec (CommRingCat.of K)} (P : SchemeHomOver s f) :
    mapPt (schemeHomOverComp β γ).1 (schemeHomOverComp β γ).2 P = mapPt γ.1 γ.2 (mapPt β.1 β.2 P) := by
  apply Subtype.ext
  simp [mapPt]

noncomputable def evPt (L : RelativeGroupLaw K f) (hc : L.IsCommutative) {T : Scheme.{u}}
    {s : T ⟶ Spec (CommRingCat.of K)} (P : SchemeHomOver s f) :
    letI := L.pointCommGroup hc f
    letI := L.pointCommGroup hc s
    SchemeHomOver f f →* SchemeHomOver s f :=
  letI := L.pointCommGroup hc f
  letI := L.pointCommGroup hc s
  MonoidHom.mk' (fun β => mapPt β.1 β.2 P) (fun β γ => mapPt_mul_pt L P β γ)

theorem evPt_apply (L : RelativeGroupLaw K f) (hc : L.IsCommutative) {T : Scheme.{u}}
    {s : T ⟶ Spec (CommRingCat.of K)} (P : SchemeHomOver s f) (β : SchemeHomOver f f) :
    evPt L hc P β = mapPt β.1 β.2 P := rfl

noncomputable def ptHom (L : RelativeGroupLaw K f) (hc : L.IsCommutative) (β : SchemeHomOver f f)
    (hβ : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of K)) (P Q : SchemeHomOver t f),
      mapPt β.1 β.2 (L.mul t P Q) = L.mul t (mapPt β.1 β.2 P) (mapPt β.1 β.2 Q))
    {T : Scheme.{u}} (s : T ⟶ Spec (CommRingCat.of K)) :
    letI := L.pointCommGroup hc s
    SchemeHomOver s f →* SchemeHomOver s f :=
  letI := L.pointCommGroup hc s
  MonoidHom.mk' (fun P => mapPt β.1 β.2 P) (fun P Q => hβ s P Q)

theorem ptHom_apply (L : RelativeGroupLaw K f) (hc : L.IsCommutative) (β : SchemeHomOver f f)
    (hβ : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of K)) (P Q : SchemeHomOver t f),
      mapPt β.1 β.2 (L.mul t P Q) = L.mul t (mapPt β.1 β.2 P) (mapPt β.1 β.2 Q))
    {T : Scheme.{u}} (s : T ⟶ Spec (CommRingCat.of K)) (P : SchemeHomOver s f) :
    ptHom L hc β hβ s P = mapPt β.1 β.2 P := rfl

end Endo

section Lattice

variable {K : Type u} [Field K] {A : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of K)}
  (L : RelativeGroupLaw K f) (hc : L.IsCommutative) (β γ : SchemeHomOver f f)
  (hβ : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of K)) (P Q : SchemeHomOver t f),
    mapPt β.1 β.2 (L.mul t P Q) = L.mul t (mapPt β.1 β.2 P) (mapPt β.1 β.2 Q))
  (hγ : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of K)) (P Q : SchemeHomOver t f),
    mapPt γ.1 γ.2 (L.mul t P Q) = L.mul t (mapPt γ.1 γ.2 P) (mapPt γ.1 γ.2 Q))

noncomputable def gens : Fin 4 → SchemeHomOver f f :=
  ![RelativeGroupLaw.idPoint, β, γ, schemeHomOverComp γ β]

noncomputable def uEnd (v : Fin 4 → ℤ) : SchemeHomOver f f :=
  letI := L.pointCommGroup hc f
  ∏ i, gens β γ i ^ v i

include hβ hγ in

theorem mapPt_uEnd (v : Fin 4 → ℤ) {T : Scheme.{u}} (s : T ⟶ Spec (CommRingCat.of K)) (P : SchemeHomOver s f) :
    mapPt (uEnd L hc β γ v).1 (uEnd L hc β γ v).2 P =
      (letI := L.pointCommGroup hc s; uHom (ptHom L hc β hβ s) (ptHom L hc γ hγ s) v P) := by
  letI := L.pointCommGroup hc s
  letI := L.pointCommGroup hc f
  rw [← evPt_apply L hc P, uEnd, map_prod, Fin.prod_univ_four, uHom_apply]
  simp only [map_zpow, evPt_apply, gens, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.tail_cons, Matrix.cons_val_three, ptHom_apply, mapPt_id, mapPt_schemeHomOverComp]

include hβ hγ in

theorem uEnd_hom (v : Fin 4 → ℤ) {T : Scheme.{u}} (s : T ⟶ Spec (CommRingCat.of K)) (P Q : SchemeHomOver s f) :
    mapPt (uEnd L hc β γ v).1 (uEnd L hc β γ v).2 (L.mul s P Q) =
      L.mul s (mapPt (uEnd L hc β γ v).1 (uEnd L hc β γ v).2 P) (mapPt (uEnd L hc β γ v).1 (uEnd L hc β γ v).2 Q) := by
  letI := L.pointCommGroup hc s
  rw [mapPt_uEnd L hc β γ hβ hγ, mapPt_uEnd L hc β γ hβ hγ, mapPt_uEnd L hc β γ hβ hγ]
  exact map_mul _ P Q

theorem uEnd_e0 : uEnd L hc β γ e0 = RelativeGroupLaw.idPoint := by
  letI := L.pointCommGroup hc f
  rw [uEnd, Fin.prod_univ_four]
  simp [gens, e0]

variable (D c : ℤ)
  (hβγ : ∀ {T : Scheme.{u}} (s : T ⟶ Spec (CommRingCat.of K)) (P : SchemeHomOver s f),
    mapPt β.1 β.2 (mapPt γ.1 γ.2 P) = mapPt γ.1 γ.2 (mapPt β.1 β.2 P))
  (hββ : ∀ {T : Scheme.{u}} (s : T ⟶ Spec (CommRingCat.of K)) (P : SchemeHomOver s f),
    mapPt β.1 β.2 (mapPt β.1 β.2 P) = (letI := L.pointCommGroup hc s; P ^ D))
  (hγγ : ∀ {T : Scheme.{u}} (s : T ⟶ Spec (CommRingCat.of K)) (P : SchemeHomOver s f),
    mapPt γ.1 γ.2 (mapPt γ.1 γ.2 P) = (letI := L.pointCommGroup hc s; P ^ c))

include hβ hγ hβγ hββ hγγ in

theorem uEnd_mulV (v w : Fin 4 → ℤ) :
    uEnd L hc β γ (mulV D c v w) = schemeHomOverComp (uEnd L hc β γ v) (uEnd L hc β γ w) := by
  letI := L.pointCommGroup hc f
  rw [← mapPt_idPoint (schemeHomOverComp _ _), mapPt_schemeHomOverComp, mapPt_uEnd L hc β γ hβ hγ,
    mapPt_uEnd L hc β γ hβ hγ, ← mapPt_idPoint (uEnd L hc β γ (mulV D c v w)), mapPt_uEnd L hc β γ hβ hγ,
    uHom_uHom _ _ D c (fun P => hβγ f P) (fun P => hββ f P) (fun P => hγγ f P)]

include hβ hγ hβγ hββ hγγ in
theorem mapPt_uEnd_uEnd (v w : Fin 4 → ℤ) {T : Scheme.{u}} (s : T ⟶ Spec (CommRingCat.of K)) (P : SchemeHomOver s f) :
    mapPt (uEnd L hc β γ w).1 (uEnd L hc β γ w).2 (mapPt (uEnd L hc β γ v).1 (uEnd L hc β γ v).2 P) =
      mapPt (uEnd L hc β γ (mulV D c v w)).1 (uEnd L hc β γ (mulV D c v w)).2 P := by
  rw [uEnd_mulV L hc β γ hβ hγ D c hβγ hββ hγγ, mapPt_schemeHomOverComp]

include hβ hγ hβγ hββ hγγ in

theorem isFinite_and_flat_uEnd [IsAlgClosed K] (hA : AbelianSchemePropertyBundle K f) (v : Fin 4 → ℤ)
    (hv : normV D c v ≠ 0) : IsFinite (uEnd L hc β γ v).1 ∧ Flat (uEnd L hc β γ v).1 := by
  obtain ⟨w, m, hm, hvw, hwv⟩ := exists_mulV_eq_smul_e0 D c v hv
  have key : ∀ (v w : Fin 4 → ℤ), mulV D c v w = (m : ℤ) • e0 →
      ∀ {T : Scheme.{u}} (s : T ⟶ Spec (CommRingCat.of K)) (P : SchemeHomOver s f),
        mapPt (uEnd L hc β γ w).1 (uEnd L hc β γ w).2 (mapPt (uEnd L hc β γ v).1 (uEnd L hc β γ v).2 P) =
          nsmulPt L s m P := by
    intro v w h T s P
    letI := L.pointCommGroup hc s
    rw [mapPt_uEnd_uEnd L hc β γ hβ hγ D c hβγ hββ hγγ, h, mapPt_uEnd L hc β γ hβ hγ, uHom_smul_e0,
      nsmulPt_eq_pow L hc, zpow_natCast]
  exact (CerednikDrinfeld.QM.surjective_and_isFinite_and_flat_of_mapPt_mapPt_eq_nsmulPt L hc hA L hc hA
    (uEnd L hc β γ v).1 (uEnd L hc β γ v).2 (fun s P Q => uEnd_hom L hc β γ hβ hγ v s P Q)
    (uEnd L hc β γ w).1 (uEnd L hc β γ w).2 m hm (key v w hvw) (key w v hwv)).2

theorem connectedSpace_of_bundle (hA : AbelianSchemePropertyBundle K f) : ConnectedSpace A := by
  have h := hA.connectedFibres (IsLocalRing.closedPoint K)
  refine connectedSpace_iff_univ.mpr ?_
  convert h using 1
  exact (Set.eq_univ_of_forall fun x => Subsingleton.elim _ _).symm

include hβ hγ hβγ hββ hγγ in

theorem degree_form [IsAlgClosed K] (hA : AbelianSchemePropertyBundle K f) (g : ℕ) [SmoothOfRelativeDimension g f] :
    ∃ P : MvPolynomial (Fin 4) ℚ, P.IsHomogeneous (2 * g) ∧
      (∀ v : Fin 4 → ℤ, ((L.endDegree (uEnd L hc β γ v) : ℕ) : ℚ) = MvPolynomial.eval (fun i => (v i : ℚ)) P) ∧
      L.endDegree (uEnd L hc β γ e0) = 1 ∧
      ∀ v w : Fin 4 → ℤ, L.endDegree (uEnd L hc β γ (mulV D c v w)) =
        L.endDegree (uEnd L hc β γ v) * L.endDegree (uEnd L hc β γ w) := by
  obtain ⟨P, hP, hPev⟩ :=
    GoodReductionJacobian.RelativeGroupLaw.exists_isHomogeneous_eval_eq_endDegree_of_abelianSchemePropertyBundle
      K f L hc hA g (gens β γ) (by
        intro i T t x y
        fin_cases i
        · rfl
        · exact hβ t x y
        · exact hγ t x y
        · show mapPt (schemeHomOverComp γ β).1 (schemeHomOverComp γ β).2 (L.mul t x y) =
            L.mul t (mapPt (schemeHomOverComp γ β).1 (schemeHomOverComp γ β).2 x)
              (mapPt (schemeHomOverComp γ β).1 (schemeHomOverComp γ β).2 y)
          rw [mapPt_schemeHomOverComp, mapPt_schemeHomOverComp, mapPt_schemeHomOverComp, hγ, hβ])
  have hF : ∀ v : Fin 4 → ℤ, ((L.endDegree (uEnd L hc β γ v) : ℕ) : ℚ) = MvPolynomial.eval (fun i => (v i : ℚ)) P :=
    fun v => hPev v
  refine ⟨P, hP, hF, ?_, ?_⟩
  · rw [uEnd_e0]
    exact L.endDegree_schemeHomOverId
  · haveI : IsProper f := hA.proper
    haveI : ConnectedSpace A := connectedSpace_of_bundle hA
    apply mul_of_generic D c (fun v => L.endDegree (uEnd L hc β γ v)) P hF
    intro v w hv hw
    obtain ⟨_, _⟩ := isFinite_and_flat_uEnd L hc β γ hβ hγ D c hβγ hββ hγγ hA v hv
    obtain ⟨_, _⟩ := isFinite_and_flat_uEnd L hc β γ hβ hγ D c hβγ hββ hγγ hA w hw
    change L.endDegree (uEnd L hc β γ (mulV D c v w)) = _
    rw [uEnd_mulV L hc β γ hβ hγ D c hβγ hββ hγγ]
    exact GoodReductionJacobian.RelativeGroupLaw.endDegree_schemeHomOverComp_of_isFinite_of_flat K f L _ _

end Lattice

section AntiComm

theorem hzd_alg {G : Type*} [CommGroup G] (σ τ η : G →* G) (r d : ℤ) (M : ℕ)
    (hησ : ∀ P, η (σ P) = σ (η P)) (hτη : ∀ P, τ (η P) = (η (τ P))⁻¹) (hηη : ∀ P, η (η P) = P ^ d)
    (hstar : ∀ P, (P ^ r * (σ (τ P))⁻¹) ^ M = 1) (P : G) : P ^ (2 * r * M * d) = 1 := by
  have h2 : η P ^ r * (σ (τ (η P)))⁻¹ = η (P ^ r * σ (τ P)) := by
    rw [hτη, map_inv, inv_inv, ← hησ, map_mul, map_zpow]
  have h3 : η ((P ^ r * σ (τ P)) ^ M) = 1 := by rw [map_pow, ← h2]; exact hstar (η P)
  have h4 : (P ^ r * σ (τ P)) ^ M = P ^ (2 * r * M) := by
    have h5 : (P ^ r * σ (τ P)) ^ M * (P ^ r * (σ (τ P))⁻¹) ^ M = P ^ (2 * r * M) := by
      rw [← mul_pow, show P ^ r * σ (τ P) * (P ^ r * (σ (τ P))⁻¹) = P ^ (2 * r) by
        rw [mul_mul_mul_comm, mul_inv_cancel, mul_one, ← zpow_add, two_mul], ← zpow_natCast, ← zpow_mul]
    rw [hstar P, mul_one] at h5
    exact h5
  rw [h4] at h3
  have h6 := congrArg η h3
  rw [hηη, map_one, ← zpow_mul] at h6
  exact h6

variable {K : Type u} [Field K] [IsAlgClosed K] {A : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of K)}
  (L : RelativeGroupLaw K f) (hc : L.IsCommutative) (hA : AbelianSchemePropertyBundle K f)
  (β γ η : SchemeHomOver f f)
  (hβ : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of K)) (P Q : SchemeHomOver t f),
    mapPt β.1 β.2 (L.mul t P Q) = L.mul t (mapPt β.1 β.2 P) (mapPt β.1 β.2 Q))
  (hγ : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of K)) (P Q : SchemeHomOver t f),
    mapPt γ.1 γ.2 (L.mul t P Q) = L.mul t (mapPt γ.1 γ.2 P) (mapPt γ.1 γ.2 Q))
  (hη : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of K)) (P Q : SchemeHomOver t f),
    mapPt η.1 η.2 (L.mul t P Q) = L.mul t (mapPt η.1 η.2 P) (mapPt η.1 η.2 Q))
  (D c d : ℤ)
  (hβγ : ∀ {T : Scheme.{u}} (s : T ⟶ Spec (CommRingCat.of K)) (P : SchemeHomOver s f),
    mapPt β.1 β.2 (mapPt γ.1 γ.2 P) = mapPt γ.1 γ.2 (mapPt β.1 β.2 P))
  (hββ : ∀ {T : Scheme.{u}} (s : T ⟶ Spec (CommRingCat.of K)) (P : SchemeHomOver s f),
    mapPt β.1 β.2 (mapPt β.1 β.2 P) = (letI := L.pointCommGroup hc s; P ^ D))
  (hγγ : ∀ {T : Scheme.{u}} (s : T ⟶ Spec (CommRingCat.of K)) (P : SchemeHomOver s f),
    mapPt γ.1 γ.2 (mapPt γ.1 γ.2 P) = (letI := L.pointCommGroup hc s; P ^ c))
  (hηβ : ∀ {T : Scheme.{u}} (s : T ⟶ Spec (CommRingCat.of K)) (P : SchemeHomOver s f),
    mapPt η.1 η.2 (mapPt β.1 β.2 P) = mapPt β.1 β.2 (mapPt η.1 η.2 P))
  (hγη : ∀ {T : Scheme.{u}} (s : T ⟶ Spec (CommRingCat.of K)) (P : SchemeHomOver s f),
    mapPt γ.1 γ.2 (mapPt η.1 η.2 P) = (letI := L.pointCommGroup hc s; (mapPt η.1 η.2 (mapPt γ.1 γ.2 P))⁻¹))
  (hηη : ∀ {T : Scheme.{u}} (s : T ⟶ Spec (CommRingCat.of K)) (P : SchemeHomOver s f),
    mapPt η.1 η.2 (mapPt η.1 η.2 P) = (letI := L.pointCommGroup hc s; P ^ d))

include hA hβ hγ hη hβγ hββ hγγ hηβ hγη hηη in

theorem endDegree_uEnd_eq_zero_of_sq_eq (g : ℕ) (hg : 0 < g) [SmoothOfRelativeDimension g f] (hd : d ≠ 0)
    (r : ℤ) (hr : r ^ 2 = D * c) (hr0 : r ≠ 0) :
    L.endDegree (uEnd L hc β γ ![r, 0, 0, 1]) = 0 := by
  by_contra hne
  set uu := uEnd L hc β γ ![r, 0, 0, 1] with huu
  have hfin : IsFinite (L.endKerStr uu) := by
    by_contra hf
    exact hne (L.endDegree_of_not_isFinite uu hf)
  obtain ⟨M, hM, hkill⟩ :=
    GoodReductionJacobian.RelativeGroupLaw.exists_forall_nsmul_eq_one_of_isFinite_pullback_snd
      L hc L uu (fun t x y => uEnd_hom L hc β γ hβ hγ _ t x y) hfin

  have hstar : ∀ {T : Scheme.{u}} (s : T ⟶ Spec (CommRingCat.of K)) (P : SchemeHomOver s f),
      letI := L.pointCommGroup hc s
      (P ^ r * (ptHom L hc β hβ s (ptHom L hc γ hγ s P))⁻¹) ^ M = 1 := by
    intro T s P
    letI := L.pointCommGroup hc s
    have h0 : mulV D c ![r, 0, 0, -1] ![r, 0, 0, 1] = 0 := by
      ext i
      fin_cases i <;> simp [mulV]
      linear_combination hr
    have h1 : mapPt uu.1 uu.2 (mapPt (uEnd L hc β γ ![r, 0, 0, -1]).1 (uEnd L hc β γ ![r, 0, 0, -1]).2 P) = L.one s := by
      rw [huu, mapPt_uEnd_uEnd L hc β γ hβ hγ D c hβγ hββ hγγ, h0, mapPt_uEnd L hc β γ hβ hγ]
      show uHom _ _ 0 P = 1
      simp [uHom_apply]
    have h2 := hkill s _ h1
    rw [nsmul_eq_pow L hc, mapPt_uEnd L hc β γ hβ hγ] at h2
    have h3 : uHom (ptHom L hc β hβ s) (ptHom L hc γ hγ s) ![r, 0, 0, -1] P =
        P ^ r * (ptHom L hc β hβ s (ptHom L hc γ hγ s P))⁻¹ := by
      simp [uHom_apply]
    rw [h3] at h2
    exact h2

  have hzero : 2 * r * M * d = 0 := by
    apply eq_zero_of_forall_zpow_eq_one L hc hA g hg
    intro P
    letI := L.pointCommGroup hc (𝟙 (Spec (CommRingCat.of K)))
    exact hzd_alg (ptHom L hc β hβ _) (ptHom L hc γ hγ _) (ptHom L hc η hη _) r d M
      (fun P => hηβ _ P) (fun P => hγη _ P) (fun P => hηη _ P) (fun P => hstar _ P) P
  have hM0 : (M : ℤ) ≠ 0 := by exact_mod_cast hM.ne'
  rcases mul_eq_zero.mp hzero with h | h
  · rcases mul_eq_zero.mp h with h | h
    · rcases mul_eq_zero.mp h with h | h
      · norm_num at h
      · exact hr0 h
    · exact hM0 h
  · exact hd h

end AntiComm

section Quaternion

variable {a b : ℚ}

theorem exists_nsmul_mem_of_mem_span (Λ : Submodule ℤ ℍ[ℚ, a, b]) (v : ℍ[ℚ, a, b])
    (hv : v ∈ Submodule.span ℚ (Λ : Set ℍ[ℚ, a, b])) :
    ∃ n : ℕ, 0 < n ∧ (n • v) ∈ Λ := by
  induction hv using Submodule.span_induction with
  | mem x hx => exact ⟨1, one_pos, by simpa using hx⟩
  | zero => exact ⟨1, one_pos, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨m, hm, hmx⟩ := hx
    obtain ⟨n, hn, hny⟩ := hy
    refine ⟨m * n, Nat.mul_pos hm hn, ?_⟩
    have h1 : (m * n) • (x + y) = n • (m • x) + m • (n • y) := by
      rw [smul_add, mul_comm m n, mul_smul, mul_comm n m, mul_smul]
    rw [h1]
    exact Λ.add_mem (nsmul_mem hmx n) (nsmul_mem hny m)
  | smul c x _ hx =>
    obtain ⟨n, hn, hnx⟩ := hx
    refine ⟨n * c.den, Nat.mul_pos hn c.den_pos, ?_⟩
    have h1 : (n * c.den) • (c • x) = c.num • (n • x) := by
      rw [← Nat.cast_smul_eq_nsmul ℚ, ← Nat.cast_smul_eq_nsmul ℚ n, ← Int.cast_smul_eq_zsmul ℚ,
        smul_smul, smul_smul, Nat.cast_mul, mul_assoc, Rat.den_mul_eq_num, mul_comm]
    rw [h1]
    exact zsmul_mem hnx c.num

theorem exists_nsmul_mem (Λ : Submodule ℤ ℍ[ℚ, a, b])
    (hspan : Submodule.span ℚ (Λ : Set ℍ[ℚ, a, b]) = ⊤) (v : ℍ[ℚ, a, b]) :
    ∃ n : ℕ, 0 < n ∧ (n • v) ∈ Λ :=
  exists_nsmul_mem_of_mem_span Λ v (by rw [hspan]; exact Submodule.mem_top)

theorem ne_zero_of_mul_self_eq {q q' : ℕ} [Fact q.Prime] (hB : IsIndefiniteRamifiedExactlyAt a b q q')
    (z : ℍ[ℚ, a, b]) (hz : z ≠ 0) (e : ℚ) (h : z * z = (e : ℍ[ℚ, a, b])) : e ≠ 0 := by
  rintro rfl
  have hu := (hB.isUnit_of_ne_zero z hz).mul (hB.isUnit_of_ne_zero z hz)
  rw [h, QuaternionAlgebra.coe_zero] at hu
  exact not_isUnit_zero hu

theorem exists_pair_of (Λ : Submodule ℤ ℍ[ℚ, a, b]) (hspan : Submodule.span ℚ (Λ : Set ℍ[ℚ, a, b]) = ⊤)
    (x₀ y₀ : ℍ[ℚ, a, b]) (e e' : ℚ) (he : 0 < e) (he' : e' ≠ 0)
    (hx₀ : x₀ * x₀ = (e : ℍ[ℚ, a, b])) (hy₀ : y₀ * y₀ = (e' : ℍ[ℚ, a, b])) (hxy₀ : x₀ * y₀ = -(y₀ * x₀))
    (hre : x₀.re = 0) (hne : x₀ ≠ 0) :
    ∃ (x y : ↥Λ) (c d : ℤ), 0 < c ∧ d ≠ 0 ∧ (x : ℍ[ℚ, a, b]).re = 0 ∧ (x : ℍ[ℚ, a, b]) ≠ 0 ∧
      (x : ℍ[ℚ, a, b]) * x = ((c : ℚ) : ℍ[ℚ, a, b]) ∧ (y : ℍ[ℚ, a, b]) * y = ((d : ℚ) : ℍ[ℚ, a, b]) ∧
      (x : ℍ[ℚ, a, b]) * y = -((y : ℍ[ℚ, a, b]) * x) := by
  obtain ⟨m, hm, hmx⟩ := exists_nsmul_mem Λ hspan x₀
  obtain ⟨m', hm', hmy⟩ := exists_nsmul_mem Λ hspan y₀
  have hxmem : ((m * e.den : ℕ) : ℚ) • x₀ ∈ Λ := by
    rw [Nat.cast_smul_eq_nsmul, mul_comm, mul_smul]; exact nsmul_mem hmx _
  have hymem : ((m' * e'.den : ℕ) : ℚ) • y₀ ∈ Λ := by
    rw [Nat.cast_smul_eq_nsmul, mul_comm, mul_smul]; exact nsmul_mem hmy _
  refine ⟨⟨_, hxmem⟩, ⟨_, hymem⟩, (m : ℤ) ^ 2 * e.den * e.num, (m' : ℤ) ^ 2 * e'.den * e'.num, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · have := Rat.num_pos.mpr he
    positivity
  · have : e'.num ≠ 0 := Rat.num_ne_zero.mpr he'
    have : (m' : ℤ) ≠ 0 := by exact_mod_cast hm'.ne'
    have : (e'.den : ℤ) ≠ 0 := by exact_mod_cast e'.den_nz
    positivity
  · simp [hre]
  · simp only
    refine smul_ne_zero ?_ hne
    have := e.den_nz
    positivity
  · simp only
    rw [smul_mul_smul_comm, hx₀, ← QuaternionAlgebra.coe_smul, smul_eq_mul]
    congr 1
    push_cast
    have := Rat.den_mul_eq_num e
    linear_combination ((m : ℚ) ^ 2 * e.den) * this
  · simp only
    rw [smul_mul_smul_comm, hy₀, ← QuaternionAlgebra.coe_smul, smul_eq_mul]
    congr 1
    push_cast
    have := Rat.den_mul_eq_num e'
    linear_combination ((m' : ℚ) ^ 2 * e'.den) * this
  · simp only
    rw [smul_mul_smul_comm, smul_mul_smul_comm, hxy₀, smul_neg, mul_comm]

theorem exists_pair {q q' : ℕ} [Fact q.Prime] (hB : IsIndefiniteRamifiedExactlyAt a b q q')
    (Λ : Submodule ℤ ℍ[ℚ, a, b]) (hspan : Submodule.span ℚ (Λ : Set ℍ[ℚ, a, b]) = ⊤) :
    ∃ (x y : ↥Λ) (c d : ℤ), 0 < c ∧ d ≠ 0 ∧ (x : ℍ[ℚ, a, b]).re = 0 ∧ (x : ℍ[ℚ, a, b]) ≠ 0 ∧
      (x : ℍ[ℚ, a, b]) * x = ((c : ℚ) : ℍ[ℚ, a, b]) ∧ (y : ℍ[ℚ, a, b]) * y = ((d : ℚ) : ℍ[ℚ, a, b]) ∧
      (x : ℍ[ℚ, a, b]) * y = -((y : ℍ[ℚ, a, b]) * x) := by
  let qi : ℍ[ℚ, a, b] := ⟨0, 1, 0, 0⟩
  let qj : ℍ[ℚ, a, b] := ⟨0, 0, 1, 0⟩
  have hii : qi * qi = (a : ℍ[ℚ, a, b]) := by ext <;> simp [qi]
  have hjj : qj * qj = (b : ℍ[ℚ, a, b]) := by ext <;> simp [qj]
  have hij : qi * qj = -(qj * qi) := by ext <;> simp [qi, qj]
  have hi0 : qi ≠ 0 := fun h => by simpa [qi] using congrArg QuaternionAlgebra.imI h
  have hj0 : qj ≠ 0 := fun h => by simpa [qj] using congrArg QuaternionAlgebra.imJ h
  have ha0 : a ≠ 0 := ne_zero_of_mul_self_eq hB qi hi0 a hii
  have hb0 : b ≠ 0 := ne_zero_of_mul_self_eq hB qj hj0 b hjj
  rcases hB.1 with ha | hb
  · exact exists_pair_of Λ hspan qi qj a b ha hb0 hii hjj hij rfl hi0
  · refine exists_pair_of Λ hspan qj qi b a hb ha0 hjj hii ?_ rfl hj0
    rw [hij, neg_neg]

theorem not_isSquare_of_mul_self_eq {q q' : ℕ} [Fact q.Prime] (hB : IsIndefiniteRamifiedExactlyAt a b q q')
    (x : ℍ[ℚ, a, b]) (hre : x.re = 0) (c : ℤ) (hc : 0 < c) (hxx : x * x = ((c : ℚ) : ℍ[ℚ, a, b])) :
    ¬ IsSquare c := by
  rintro ⟨s, hs⟩
  set w : ℍ[ℚ, a, b] := ((s : ℚ) : ℍ[ℚ, a, b]) with hw
  have hprod : (x - w) * (x + w) = 0 := by
    have hcomm : x * w = w * x := (QuaternionAlgebra.coe_commutes (s : ℚ) x).symm
    have hww : w * w = ((c : ℚ) : ℍ[ℚ, a, b]) := by
      rw [hw, ← QuaternionAlgebra.coe_mul, hs]; push_cast; rfl
    calc (x - w) * (x + w) = x * x + x * w - w * x - w * w := by noncomm_ring
      _ = 0 := by rw [hcomm, hxx, hww]; abel
  have hxw : x = w ∨ x = -w := by
    by_cases h : x - w = 0
    · exact Or.inl (sub_eq_zero.mp h)
    · right
      have := (hB.isUnit_of_ne_zero _ h).mul_right_eq_zero.mp hprod
      exact eq_neg_of_add_eq_zero_left this
  have hs0 : s = 0 := by
    rcases hxw with h | h
    · have := congrArg QuaternionAlgebra.re h
      rw [hre, hw, QuaternionAlgebra.re_coe] at this
      exact_mod_cast this.symm
    · have := congrArg QuaternionAlgebra.re h
      rw [hre, hw, QuaternionAlgebra.re_neg, QuaternionAlgebra.re_coe] at this
      have : (s : ℚ) = 0 := by linarith
      exact_mod_cast this
  rw [hs0, mul_zero] at hs
  omega

end Quaternion

section Frame

variable {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} {N : ℕ} {k : Type u} [Field k]

theorem sq_alg {G : Type*} [CommGroup G] (σ : G →* G) (t n : ℤ)
    (h1 : ∀ P, σ (σ P) * P ^ n = σ P ^ t) (P : G) :
    σ (σ P ^ (2 : ℤ) * P ^ (-t)) ^ (2 : ℤ) * (σ P ^ (2 : ℤ) * P ^ (-t)) ^ (-t) = P ^ (t ^ 2 - 4 * n) := by
  have ha : Additive.ofMul (σ (σ P)) + n • Additive.ofMul P = t • Additive.ofMul (σ P) := by
    have := congrArg Additive.ofMul (h1 P)
    simpa [ofMul_mul, ofMul_zpow] using this
  apply Additive.ofMul.injective
  simp only [map_mul, map_zpow, ofMul_mul, ofMul_zpow]
  linear_combination (norm := module) (4 : ℤ) • ha

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
  rw [← evPt_apply E.L E.comm P, lin, map_mul, map_zpow, map_zpow, evPt_apply, evPt_apply, mapPt_id]

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
  have h1 : evPt E.L E.comm aP ⟨φ, hφ⟩ = ρ ⟨φ, hφ⟩ := by
    apply Subtype.ext
    show E.act x ≫ φ = φ ≫ E.act x
    exact hact x
  have h2 : evPt E.L E.comm aP RelativeGroupLaw.idPoint = ρ RelativeGroupLaw.idPoint := by
    apply Subtype.ext
    show E.act x ≫ 𝟙 E.A = 𝟙 E.A ≫ E.act x
    simp
  have h : evPt E.L E.comm aP (lin E φ hφ α β) = ρ (lin E φ hφ α β) := by
    simp only [lin, map_mul, map_zpow, h1, h2]
  exact congrArg Subtype.val h

theorem mapPt_lin_act (E : FakeEllipticCurve Λ N k) (φ : E.A ⟶ E.A) (hφ : φ ≫ E.f = E.f)
    (hact : ∀ x : ↥Λ, E.act x ≫ φ = φ ≫ E.act x) (α β : ℤ) (x : ↥Λ)
    {T : Scheme.{u}} (s : T ⟶ Spec (CommRingCat.of k)) (P : SchemeHomOver s E.f) :
    mapPt (lin E φ hφ α β).1 (lin E φ hφ α β).2 (mapPt (E.act x) (E.act_over x) P) =
      mapPt (E.act x) (E.act_over x) (mapPt (lin E φ hφ α β).1 (lin E φ hφ α β).2 P) := by
  rw [mapPt_mapPt, mapPt_mapPt]
  congr 1
  exact lin_act E φ hφ hact α β x

theorem mapPt_act_zero (E : FakeEllipticCurve Λ N k) {T : Scheme.{u}} (s : T ⟶ Spec (CommRingCat.of k))
    (P : SchemeHomOver s E.f) : mapPt (E.act 0) (E.act_over 0) P = E.L.one s := by
  letI := E.L.pointCommGroup E.comm s
  have h := E.act_add 0 0 s P
  rw [add_zero] at h
  change mapPt (E.act 0) (E.act_over 0) P = mapPt (E.act 0) (E.act_over 0) P * mapPt (E.act 0) (E.act_over 0) P at h
  exact left_eq_mul.mp h

theorem mapPt_act_neg (E : FakeEllipticCurve Λ N k) (z : ↥Λ) {T : Scheme.{u}} (s : T ⟶ Spec (CommRingCat.of k))
    (P : SchemeHomOver s E.f) :
    mapPt (E.act (-z)) (E.act_over (-z)) P = (letI := E.L.pointCommGroup E.comm s; (mapPt (E.act z) (E.act_over z) P)⁻¹) := by
  letI := E.L.pointCommGroup E.comm s
  have h := E.act_add z (-z) s P
  rw [add_neg_cancel] at h
  change mapPt (E.act 0) (E.act_over 0) P = mapPt (E.act z) (E.act_over z) P * mapPt (E.act (-z)) (E.act_over (-z)) P at h
  rw [mapPt_act_zero] at h
  exact (eq_inv_of_mul_eq_one_right h.symm)

theorem mapPt_act_natCast (E : FakeEllipticCurve Λ N k) (h1 : (1 : ℍ[ℚ, a, b]) ∈ Λ) :
    ∀ (m : ℕ) (z : ↥Λ), (z : ℍ[ℚ, a, b]) = ((m : ℚ) : ℍ[ℚ, a, b]) →
      ∀ {T : Scheme.{u}} (s : T ⟶ Spec (CommRingCat.of k)) (P : SchemeHomOver s E.f),
        mapPt (E.act z) (E.act_over z) P = (letI := E.L.pointCommGroup E.comm s; P ^ m) := by
  intro m
  induction m with
  | zero =>
    intro z hz T s P
    letI := E.L.pointCommGroup E.comm s
    have hz0 : z = 0 := Subtype.ext (by rw [hz]; simp)
    subst hz0
    rw [mapPt_act_zero, pow_zero]
    rfl
  | succ m ih =>
    intro z hz T s P
    letI := E.L.pointCommGroup E.comm s
    let z' : ↥Λ := z - ⟨1, h1⟩
    have hz' : (z' : ℍ[ℚ, a, b]) = ((m : ℚ) : ℍ[ℚ, a, b]) := by
      show (z : ℍ[ℚ, a, b]) - 1 = _
      rw [hz, ← QuaternionAlgebra.coe_one, ← QuaternionAlgebra.coe_sub]
      congr 1; push_cast; ring
    have hzz : z = z' + ⟨1, h1⟩ := by simp [z']
    rw [hzz]
    have h := E.act_add z' ⟨1, h1⟩ s P
    change mapPt (E.act (z' + ⟨1, h1⟩)) (E.act_over (z' + ⟨1, h1⟩)) P =
      mapPt (E.act z') (E.act_over z') P * mapPt (E.act ⟨1, h1⟩) (E.act_over ⟨1, h1⟩) P at h
    rw [h, ih z' hz', pow_succ]
    congr 1
    have h2 : E.act ⟨1, h1⟩ = 𝟙 E.A := E.act_one h1
    apply Subtype.ext
    simp [mapPt, h2]

theorem mapPt_act_intCast (E : FakeEllipticCurve Λ N k) (h1 : (1 : ℍ[ℚ, a, b]) ∈ Λ)
    (m : ℤ) (z : ↥Λ) (hz : (z : ℍ[ℚ, a, b]) = ((m : ℚ) : ℍ[ℚ, a, b]))
    {T : Scheme.{u}} (s : T ⟶ Spec (CommRingCat.of k)) (P : SchemeHomOver s E.f) :
    mapPt (E.act z) (E.act_over z) P = (letI := E.L.pointCommGroup E.comm s; P ^ m) := by
  letI := E.L.pointCommGroup E.comm s
  obtain ⟨n, rfl | rfl⟩ := Int.eq_nat_or_neg m
  · rw [mapPt_act_natCast E h1 n z (by rw [hz]; norm_cast), zpow_natCast]
  · have hz' : ((-z : ↥Λ) : ℍ[ℚ, a, b]) = ((n : ℚ) : ℍ[ℚ, a, b]) := by
      rw [Submodule.coe_neg, hz, ← QuaternionAlgebra.coe_neg]
      congr 1; push_cast; ring
    have h := mapPt_act_neg E (-z) s P
    rw [neg_neg] at h
    rw [h, mapPt_act_natCast E h1 n (-z) hz', zpow_neg, zpow_natCast]

theorem mapPt_act_act (E : FakeEllipticCurve Λ N k) (x y : ↥Λ) (h : (x : ℍ[ℚ, a, b]) * y ∈ Λ)
    {T : Scheme.{u}} (s : T ⟶ Spec (CommRingCat.of k)) (P : SchemeHomOver s E.f) :
    mapPt (E.act x) (E.act_over x) (mapPt (E.act y) (E.act_over y) P) =
      mapPt (E.act ⟨(x : ℍ[ℚ, a, b]) * y, h⟩) (E.act_over ⟨(x : ℍ[ℚ, a, b]) * y, h⟩) P := by
  rw [mapPt_mapPt]
  congr 1
  exact (E.act_mul x y h).symm

end Frame

theorem main
    {q q' : ℕ} [Fact q.Prime] {a b : ℚ} (hB : IsIndefiniteRamifiedExactlyAt a b q q')
    (Λ : Submodule ℤ ℍ[ℚ, a, b]) (hΛ : IsMaximalOrder Λ) {N : ℕ}
    (k : Type u) [Field k] [IsAlgClosed k] (E : FakeEllipticCurve Λ N k)
    (φ : E.A ⟶ E.A) (hφ : φ ≫ E.f = E.f)
    (hmul : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of k)) (P Q : SchemeHomOver t E.f),
      mapPt φ hφ (E.L.mul t P Q) = E.L.mul t (mapPt φ hφ P) (mapPt φ hφ Q))
    (hact : ∀ x : ↥Λ, E.act x ≫ φ = φ ≫ E.act x)
    (t n : ℤ)
    (hquad : ∀ {T : Scheme.{u}} (s : T ⟶ Spec (CommRingCat.of k)) (P : SchemeHomOver s E.f),
      letI := E.L.pointCommGroup E.comm s
      mapPt φ hφ (mapPt φ hφ P) * P ^ n = mapPt φ hφ P ^ t) :
    IsSquare (t ^ 2 - 4 * n) ∨ t ^ 2 < 4 * n := by
  by_contra hcon
  obtain ⟨hnsq, hle⟩ := not_or.mp hcon
  set D : ℤ := t ^ 2 - 4 * n with hD
  have hD0 : D ≠ 0 := fun h => hnsq ⟨0, by rw [h, mul_zero]⟩
  have hDpos : 0 < D := by omega
  haveI := CerednikDrinfeld.QM.FakeEllipticCurve.smoothOfRelativeDimension_two k E
  have hO : IsOrder Λ := hΛ.1

  obtain ⟨x, y, c, d, hc, hd, hxre, hx0, hxx, hyy, hxy⟩ := exists_pair hB Λ hO.spanTop
  have hcsq : ¬ IsSquare c := not_isSquare_of_mul_self_eq hB x hxre c hc hxx

  let β : SchemeHomOver E.f E.f := lin E φ hφ 2 (-t)
  let γ : SchemeHomOver E.f E.f := ⟨E.act x, E.act_over x⟩
  let η : SchemeHomOver E.f E.f := ⟨E.act y, E.act_over y⟩
  have hβ : ∀ {T : Scheme.{u}} (s : T ⟶ Spec (CommRingCat.of k)) (P Q : SchemeHomOver s E.f),
      mapPt β.1 β.2 (E.L.mul s P Q) = E.L.mul s (mapPt β.1 β.2 P) (mapPt β.1 β.2 Q) :=
    fun s P Q => lin_hom E φ hφ hmul 2 (-t) s P Q
  have hγ : ∀ {T : Scheme.{u}} (s : T ⟶ Spec (CommRingCat.of k)) (P Q : SchemeHomOver s E.f),
      mapPt γ.1 γ.2 (E.L.mul s P Q) = E.L.mul s (mapPt γ.1 γ.2 P) (mapPt γ.1 γ.2 Q) :=
    fun s P Q => E.act_hom x s P Q
  have hη : ∀ {T : Scheme.{u}} (s : T ⟶ Spec (CommRingCat.of k)) (P Q : SchemeHomOver s E.f),
      mapPt η.1 η.2 (E.L.mul s P Q) = E.L.mul s (mapPt η.1 η.2 P) (mapPt η.1 η.2 Q) :=
    fun s P Q => E.act_hom y s P Q

  have hββ : ∀ {T : Scheme.{u}} (s : T ⟶ Spec (CommRingCat.of k)) (P : SchemeHomOver s E.f),
      mapPt β.1 β.2 (mapPt β.1 β.2 P) = (letI := E.L.pointCommGroup E.comm s; P ^ D) := by
    intro T s P
    letI := E.L.pointCommGroup E.comm s
    let σ : SchemeHomOver s E.f →* SchemeHomOver s E.f := MonoidHom.mk' (fun R => mapPt φ hφ R) (fun R S => hmul s R S)
    have hσ : ∀ R : SchemeHomOver s E.f, mapPt φ hφ R = σ R := fun _ => rfl
    show mapPt (lin E φ hφ 2 (-t)).1 (lin E φ hφ 2 (-t)).2 (mapPt (lin E φ hφ 2 (-t)).1 (lin E φ hφ 2 (-t)).2 P) = P ^ D
    rw [mapPt_lin, mapPt_lin, hσ, hσ, hD]
    exact sq_alg σ t n (fun R => by rw [← hσ, ← hσ]; exact hquad s R) P

  have hxxmem : (x : ℍ[ℚ, a, b]) * x ∈ Λ := hO.mul_mem x.2 x.2
  have hyymem : (y : ℍ[ℚ, a, b]) * y ∈ Λ := hO.mul_mem y.2 y.2
  have hγγ : ∀ {T : Scheme.{u}} (s : T ⟶ Spec (CommRingCat.of k)) (P : SchemeHomOver s E.f),
      mapPt γ.1 γ.2 (mapPt γ.1 γ.2 P) = (letI := E.L.pointCommGroup E.comm s; P ^ c) := by
    intro T s P
    show mapPt (E.act x) (E.act_over x) (mapPt (E.act x) (E.act_over x) P) = _
    rw [mapPt_act_act E x x hxxmem]
    exact mapPt_act_intCast E hO.one_mem c _ hxx s P
  have hηη : ∀ {T : Scheme.{u}} (s : T ⟶ Spec (CommRingCat.of k)) (P : SchemeHomOver s E.f),
      mapPt η.1 η.2 (mapPt η.1 η.2 P) = (letI := E.L.pointCommGroup E.comm s; P ^ d) := by
    intro T s P
    show mapPt (E.act y) (E.act_over y) (mapPt (E.act y) (E.act_over y) P) = _
    rw [mapPt_act_act E y y hyymem]
    exact mapPt_act_intCast E hO.one_mem d _ hyy s P

  have hβγ : ∀ {T : Scheme.{u}} (s : T ⟶ Spec (CommRingCat.of k)) (P : SchemeHomOver s E.f),
      mapPt β.1 β.2 (mapPt γ.1 γ.2 P) = mapPt γ.1 γ.2 (mapPt β.1 β.2 P) :=
    fun s P => mapPt_lin_act E φ hφ hact 2 (-t) x s P
  have hηβ : ∀ {T : Scheme.{u}} (s : T ⟶ Spec (CommRingCat.of k)) (P : SchemeHomOver s E.f),
      mapPt η.1 η.2 (mapPt β.1 β.2 P) = mapPt β.1 β.2 (mapPt η.1 η.2 P) :=
    fun s P => (mapPt_lin_act E φ hφ hact 2 (-t) y s P).symm

  have hxymem : (x : ℍ[ℚ, a, b]) * y ∈ Λ := hO.mul_mem x.2 y.2
  have hyxmem : (y : ℍ[ℚ, a, b]) * x ∈ Λ := hO.mul_mem y.2 x.2
  have hγη : ∀ {T : Scheme.{u}} (s : T ⟶ Spec (CommRingCat.of k)) (P : SchemeHomOver s E.f),
      mapPt γ.1 γ.2 (mapPt η.1 η.2 P) =
        (letI := E.L.pointCommGroup E.comm s; (mapPt η.1 η.2 (mapPt γ.1 γ.2 P))⁻¹) := by
    intro T s P
    letI := E.L.pointCommGroup E.comm s
    show mapPt (E.act x) (E.act_over x) (mapPt (E.act y) (E.act_over y) P) =
      (mapPt (E.act y) (E.act_over y) (mapPt (E.act x) (E.act_over x) P))⁻¹
    rw [mapPt_act_act E x y hxymem, mapPt_act_act E y x hyxmem, ← mapPt_act_neg]
    have hneg : (⟨(x : ℍ[ℚ, a, b]) * y, hxymem⟩ : ↥Λ) = -⟨(y : ℍ[ℚ, a, b]) * x, hyxmem⟩ := by
      apply Subtype.ext
      show ((x : ℍ[ℚ, a, b]) * y) = -((y : ℍ[ℚ, a, b]) * x)
      exact hxy
    congr 1
    rw [hneg]

  obtain ⟨P, hP, hF, hone, hFmul⟩ := degree_form E.L E.comm β γ hβ hγ D c hβγ hββ hγγ E.bundle 2
  have hzd : ∀ r : ℤ, r ^ 2 = D * c → E.L.endDegree (uEnd E.L E.comm β γ ![r, 0, 0, 1]) = 0 := by
    intro r hr
    have hr0 : r ≠ 0 := by
      rintro rfl
      have : (0 : ℤ) < D * c := mul_pos hDpos hc
      rw [← hr] at this
      norm_num at this
    exact endDegree_uEnd_eq_zero_of_sq_eq E.L E.comm E.bundle β γ η hβ hγ hη D c d hβγ hββ hγγ hηβ hγη hηη 2
      (by norm_num) hd r hr hr0
  rcases MvPolynomial.isSquare_or_isSquare_of_isHomogeneous_of_forall_eval_mul_eq D c hDpos hc
      (fun v => E.L.endDegree (uEnd E.L E.comm β γ v)) P hP hF hone hFmul hzd with h | h
  · exact hnsq h
  · exact hcsq h

end P2mKcRmExclusion

set_option linter.unusedVariables false in
open P2mKcRmExclusion in
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
      mapPt φ hφ (mapPt φ hφ P) * P ^ n = mapPt φ hφ P ^ t) :
    IsSquare (t ^ 2 - 4 * n) ∨ t ^ 2 < 4 * n :=
  main hB Λ hΛ k E φ hφ hmul hact t n hquad

end S_CerednikDrinfeld_QM_FakeEllipticCurve_isSquare_or_sq_lt_four_mul_of_forall_act_comp_eq
end P2MW
export P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_isSquare_or_sq_lt_four_mul_of_forall_act_comp_eq (solution)
