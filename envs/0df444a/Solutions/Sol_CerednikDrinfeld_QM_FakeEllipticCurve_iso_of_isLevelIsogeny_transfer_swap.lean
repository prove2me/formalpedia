-- Prove2me | solution 1 for CerednikDrinfeld.QM.FakeEllipticCurve.iso_of_isLevelIsogeny_transfer_swap
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.141142+00:00
-- url     : https://prove2.me/submissions/eff910a1-df6f-5b58-ae39-6b6fe2077518

import Definitions.Def_CerednikDrinfeld_QMModuliProps
import Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_exists_unique_comp_eq_of_forall_mapPt_eq_one
import Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_forall_mapPt_eq_one_of_forall_rationalPoint
import Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_pushPt_act_natCast_eq_nsmulPt
import Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_exists_factorsThrough_lev_mapPt_eq_of_forall_eq_one
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_iso_of_isLevelIsogeny_transfer_swap
p2m_attr_erase "instance" "GoodReductionJacobian.RelativeGroupLaw.isIso_endKerStr_schemeHomOverId AlgebraicGeometry.Scheme.PresheafOfModules.symmetricCategory SheafOfModules.instFaithfulRingSheafPModToPMod SheafOfModules.symmetricCategory AlgebraicGeometry.Scheme.PresheafOfModules.monoidalCategory AlgebraicGeometry.Scheme.PresheafOfModules.monoidalClosed SheafOfModules.instFullRingSheafPModToPMod SheafOfModules.monoidalCategory AlgebraicGeometry.Scheme.Modules.symmetricCategory SheafOfModules.monoidalClosed SheafOfModules.instIsLocalizationPModRingSheafSheafifyFunctorPresheafW SheafOfModules.sheafifyFunctor_monoidal AlgebraicGeometry.Scheme.Modules.monoidalClosed AlgebraicGeometry.instMonoidalPresheafOfModulesModulesSheafify AlgebraicGeometry.Scheme.Modules.monoidalCategory PresheafOfModules.instMonoidalClosed PresheafOfModules.InternalHom.instModuleCarrierObjOppositeCommRingCatSubtypePiFamilyMemAddSubgroupNaturalFamilies PresheafOfModules.InternalHom.instModuleCarrierObjOppositeRingCatCompCommRingCatForget₂RingHomCarrierCarrierAbPresheaf PresheafOfModules.InternalHom.instSMulCarrierObjOppositeCommRingCatSubtypePiFamilyMemAddSubgroupNaturalFamilies AlgebraicGeometry.Scheme.Hom.opensMapFinal AlgebraicGeometry.RelPicard.RigidifiedLineBundle.setoid AlgebraicGeometry.RelPicard.RigidifiedLineBundle.instInhabited AlgebraicGeometry.OModulePresheaf.isScalarTower AlgebraicGeometry.Scheme.OrderedAffineCover.instLinearOrder AlgebraicGeometry.OModulePresheaf.module AlgebraicGeometry.Scheme.OrderedAffineCover.instFintype AlgebraicGeometry.Scheme.OrderedAffineCover.instFintypeIdx AlgebraicGeometry.OModulePresheaf.addCommGroup AlgebraicGeometry.Scheme.OrderedAffineCover.instDecidableEqIdx AlgebraicGeometry.OModulePresheaf.moduleSections TwoChartCech.Sections.M0_moduleA TwoChartCech.Sections.M1_module TwoChartCech.Cover.A01_algebra TwoChartCech.Cover.A0_algebra TwoChartCech.Cover.A1_commRing TwoChartCech.Cover.A1_algebra TwoChartCech.Sections.M01_module TwoChartCech.Sections.M0_addCommGroup TwoChartCech.Sections.M0_tower TwoChartCech.Sections.M01_addCommGroup"
p2m_attr_erase "instance" "TwoChartCech.Cover.A0_commRing TwoChartCech.Sections.M1_tower TwoChartCech.Sections.M01_moduleA TwoChartCech.Sections.M0_module TwoChartCech.Sections.M1_moduleA TwoChartCech.Sections.M1_addCommGroup TwoChartCech.Cover.A01_commRing TwoChartCech.Sections.M01_tower CoherentBaseChange.TwoTermComplex.C0_module CoherentBaseChange.TwoTermComplex.C0_addCommGroup CoherentBaseChange.TwoTermComplex.C1_module CoherentBaseChange.TwoTermComplex.C1_addCommGroup CoherentBaseChange.TwoTermComplex.C0_free CoherentBaseChange.TwoTermComplex.C1_finite CoherentBaseChange.TwoTermComplex.C0_finite CoherentBaseChange.TwoTermComplex.C1_free AlgebraicGeometry.Scheme.Modules.preservesBinaryProducts_opensMap AlgebraicGeometry.Scheme.Modules.pullback_monoidal AlgebraicGeometry.Scheme.Modules.sheafify_isLocalization' AlgebraicGeometry.Scheme.Modules.preservesTerminal_opensMap AlgebraicGeometry.Scheme.Modules.pullback₀_monoidal AlgebraicGeometry.Scheme.Modules.preservesFiniteProducts_opensMap AlgebraicGeometry.Scheme.Modules.instLiftingPresheafOfModulesSheafifyPresheafWOpensCarrierCarrierCommRingCatGrothendieckTopologyObjFunctorOppositeIsSheafSheafCompPullback₀Pullback PresheafOfModules.PullbackMonoidal.pullback_monoidal PresheafOfModules.PullbackMonoidal.isIso_δ PresheafOfModules.pushforward_laxMonoidal PresheafOfModules.PullbackMonoidal.isIso_η PresheafOfModules.free_monoidal PresheafOfModules.restrictScalars_laxMonoidal PresheafOfModules.PullbackMonoidal.isIso_δ_gS PresheafOfModules.pullback_oplaxMonoidal PresheafOfModules.PullbackMonoidal.instPreservesColimitsOfSizeCompOppositeCommRingCatRingCatForget₂RingHomCarrierCarrierPb PresheafOfModules.pullback_monoidal' AlgebraicGeometry.SmoothOfRelativeDimension.fiberToSpecResidueField AlgebraicGeometry.SmoothOfRelativeDimension.pullback_snd AlgebraicGeometry.SmoothOfRelativeDimension.pullback_fst AlgebraicGeometry.SmoothOfRelativeDimension.smooth_one AlgebraicGeometry.SmoothProperCurve.isIntegral_pullback_Spec_field AlgebraicGeometry.IsProper.fiberToSpecResidueField AlgebraicCurve.CurveModel.isProper"
p2m_attr_erase "instance" "AlgebraicCurve.CurveModel.isIntegral AlgebraicCurve.CurveModel.smooth AlgebraicGeometry.Scheme.LocalRepresentabilityULift.instIsLocallyInjectiveFunUliftYonedaGluedToSheaf AlgebraicGeometry.Scheme.LocalRepresentabilityULift.instIsLocallySurjectiveFunUliftYonedaGluedToSheafOfIsLocallySurjectiveZariskiTopologyDescFunctorOppositeType AlgebraicGeometry.Scheme.LocalRepresentabilityULift.instIsOpenImmersionToGlued AlgebraicGeometry.Scheme.LocalRepresentabilityULift.instIsIsoSheafZariskiTopologyTypeUliftYonedaGluedToSheaf AlgebraicGeometry.RelPicard.instIsOpenImmersionToGlued AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.instFundamentalIdentityOfSumRamificationInertia AlgebraicCurve.Place.instIsScalarTowerResidueFieldRestrictPushforward AlgebraicCurve.Place.instAlgebraResidueFieldRestrictPushforward AlgebraicCurve.Place.instIsLocalHomRestrictInclusion AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions PresheafOfModules.ExteriorPower.instModulePresheafAb AlgebraicGeometry.RelEffCartierDiv.subsingleton_of_degree_zero AlgebraicGeometry.RelEffCartierDiv.isIso_subschemeIota_snd_of_degree_one AlgebraicGeometry.isIso_ker_graphOver_subschemeIota_snd AlgebraicGeometry.isClosedImmersion_graphOver AlgebraicGeometry.FGSubalgebra.instIsDirectedLe AlgebraicGeometry.FGSubalgebra.instQuasiSeparatedSpaceCarrierCarrierCommRingCatObjOppositeSchemeSpecDiagram AlgebraicGeometry.FGSubalgebra.instIsCofilteredOpposite AlgebraicGeometry.FGSubalgebra.instIsAffineObjOppositeSchemeSpecDiagram AlgebraicGeometry.FGSubalgebra.instNonempty AlgebraicGeometry.FGSubalgebra.instNonemptySubtypeLeSubalgebraValFG AlgebraicGeometry.FGSubalgebra.instCompactSpaceCarrierCarrierCommRingCatObjOppositeSchemeSpecDiagram AlgebraicGeometry.FGSubalgebra.instIsDirectedSubtypeLeSubalgebraValFG AlgebraicGeometry.FGSubalgebra.instIsAffineHomMapOppositeSchemeSpecDiagram AlgebraicGeometry.FGSubalgebra.instIsFiltered AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instNeg AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instSMulInt AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instAddCommGroup AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instAdd AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instSub AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instModuleCarrierObjOppositeOpensCarrierCarrierCommRingCatPresheafOpOpensTop"
p2m_attr_erase "instance" "AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instSMulCarrierObjOppositeOpensCarrierCarrierCommRingCatPresheafOpOpensTop AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instSMulNat AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instZero AlgebraicCurve.instHasLocalResidue_of_hasCanonicalLocalResidueK AlgebraicCurve.instHasCanonicalLocalResidueK_of_hasCanonicalLocalResidueKStar AlgebraicCurve.Place.kw_ffgc_finiteDimensional_adicCompletion instAlgebraSubtypeMemValuationSubring_definitions AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersIntegersCompletion ModularCurve.KwF4gRRTate.instAlgebraKAdicCompletionIntegers AlgebraicCurve.Place.kw_ffgc_continuousSMul_adicCompletionComap AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersCompletionCompletion IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions AlgebraicCurve.instHasCanonicalLocalResidueK AlgebraicCurve.Place.instAlgebra_restrictResidueField AlgebraicCurve.Place.instIsScalarTower_restrictResidueField AlgebraicCurve.instHasLocalResidue AlgebraicCurve.HasSeparableResidue.of_perfectField_of_isCurveOver AlgebraicCurve.HasSeparableResidue.of_perfectField AlgebraicCurve.Place.instIsLocalHom_restrictSubringHom AlgebraicCurve.instHasCanonicalLocalResidueKStar ModularCurve.KwNo6Pin.isLocalRing_completion SheafOfModules.isIso_ihomModelToIhom AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instDecidableEqIdx AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instFintype AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instLinearOrder AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instFintypeIdx AlgebraicGeometry.OModulePresheaf.instSubsingletonObjZero AlgebraicGeometry.OModulePresheaf.Leray.relAltC_scalarTower AlgebraicGeometry.OModulePresheaf.Leray.ker_relAltd_modΓ AlgebraicGeometry.OModulePresheaf.Leray.relAltC_modΓ AlgebraicGeometry.OModulePresheaf.Leray.biC_abGrp AlgebraicGeometry.OModulePresheaf.Leray.relAltH_modΓ AlgebraicGeometry.OModulePresheaf.Leray.ker_relAltd_smul AlgebraicGeometry.OModulePresheaf.Leray.relAltH_scalarTower AlgebraicGeometry.OModulePresheaf.Leray.relAltH_smul"
p2m_attr_erase "instance" "AlgebraicGeometry.OModulePresheaf.Leray.biC_module DoubleComplex.instModuleE₂I DoubleComplex.Bounded.modR DoubleComplex.instModuleE₂II DoubleComplex.instAddCommGroupE₂II DoubleComplex.Bounded.abGrp DoubleComplex.instAddCommGroupE₂I AlgebraicGeometry.ChowDatum.hι_closed AlgebraicGeometry.ChowDatumProj.hιN_closed AlgebraicGeometry.ChowDatumProj.hp_proper AlgebraicGeometry.ChowDatum.hp_isoU AlgebraicGeometry.ChowDatum.hp_proper AlgebraicGeometry.ProjSpace.algebraAway AlgebraicGeometry.ProjSpace.instIsProperProdOverπ AlgebraicGeometry.ChowDatumProj.hp_isoU AlgebraicGeometry.ProjSpace.isProper_π AlgebraicGeometry.ProjSpace.finiteType_mvPolynomial ProjSpaceCech.GradedModule.H.module ProjSpaceCech.GradedModule.H.addCommGroup ProjSpaceCech.GradedModule.sec.instAdd ProjSpaceCech.GradedModule.sec.instNeg ProjSpaceCech.GradedModule.acg ProjSpaceCech.GradedModule.Frac.setoid ProjSpaceCech.GradedModule.modR ProjSpaceCech.GradedModule.sec.instModule ProjSpaceCech.GradedModule.sec.instAddCommGroup ProjSpaceCech.GradedModule.sec.instZero ProjSpaceCech.GradedModule.Presentation.fJ ProjSpaceCech.GradedModule.sec.instSMul ProjSpaceCech.Twist.H.module ProjSpaceCech.Idx.instFintype ProjSpaceCech.Twist.H.addCommGroup ProjSpaceCech.Idx.instDecidableEq ProjSpaceCech.Twist.Mon.instDecidableEq ProjSpaceCech.Twist.cochain.instAddCommGroup ProjSpaceCech.Twist.cochain.instModule AlgebraicGeometry.FGSubalgebra.tensorStage_directedSystem AlgebraicGeometry.RelEffCartierDiv.isClosedImmersion_subschemeι_resProdMap AlgebraicGeometry.RelEffCartierDiv.isOpenImmersion_resProdMap AlgebraicCurve.CurveModel.locallyOfFiniteType_gluedToBase"
p2m_attr_erase "instance" "AlgebraicCurve.CurveModel.isFractionRing_overlap AlgebraicCurve.CurveModel.isLocallyNoetherian_glued AlgebraicCurve.CurveModel.jacobsonSpace_glued AlgebraicCurve.CurveModel.isOpenImmersion_ι₀ AlgebraicCurve.CurveModel.isIntegral_glued AlgebraicCurve.CurveModel.quasiSeparated_gluedToBase AlgebraicCurve.CurveModel.compactSpace_glued AlgebraicCurve.CurveModel.isIntegral_adjoin_chartRing AlgebraicCurve.CurveModel.isFractionRing_overlap_functionField AlgebraicCurve.CurveModel.isProper_gluedToBase AlgebraicCurve.CurveModel.isOpenImmersion_ιU AlgebraicCurve.CurveModel.isOpenImmersion_f₀ AlgebraicCurve.CurveModel.isOpenImmersion_fInf AlgebraicCurve.CurveModel.isOpenImmersion_ιInf AlgebraicCurve.CurveModel.algebra_overlap_functionField AlgebraicCurve.CurveModel.quasiCompact_gluedToBase AlgebraicCurve.CurveModel.algebraAdjoin AlgebraicCurve.CurveModel.isDedekindDomain_chartRing AlgebraicCurve.CurveModel.isIntegralClosure AlgebraicCurve.CurveModel.finite_chartRing AlgebraicCurve.CurveModel.centre_isPrime AlgebraicCurve.CurveModel.isFractionRing_chartRing AlgebraicCurve.CurveModel.finiteType_chartRing AlgebraicCurve.CurveModel.isNoetherianRing_chartRing AlgebraicCurve.CurveModel.isScalarTower_base_adjoin AlgebraicCurve.CurveModel.isScalarTower_adjoin AlgebraicCurve.CurveModel.chartRing_finitePresentation instTopologicallyFGOfFiniteType AlgebraicGeometry.ProjSpace.twistObj.addCommGroup AlgebraicGeometry.ProjSpace.twistFam.module AlgebraicGeometry.ProjSpace.twistObj.module AlgebraicGeometry.ProjSpace.twistObj.moduleSections AlgebraicGeometry.ProjSpace.twistFam.addCommGroup kmfloorsGlue_int_three_isPrime kmfloorsGlue_int_bot_isPrime"
p2m_attr_erase "simp" "GoodReductionJacobian.relativeGroupLawOfGrpObj_inv GoodReductionJacobian.relativeGroupLawOfGrpObj_mul GoodReductionJacobian.overHomEquivSchemeHomOver_apply_coe GoodReductionJacobian.relativeGroupLawOfGrpObj_one GoodReductionJacobian.overHomEquivSchemeHomOver_symm_apply_left NeronModelInfra.schemeHomOverNpow_succ NeronModelInfra.schemeHomOverNpow_zero GoodReductionJacobian.RelativeGroupLaw.nsmul_zero GoodReductionJacobian.RelativeGroupLaw.mem_torsionSubset GoodReductionJacobian.RelativeGroupLaw.nsmul_succ NeronModelInfra.NeronModelPropertyBundle.endExtensionEquiv_symm_restrict NeronModelInfra.schemeHomOverComp_id_left NeronModelInfra.schemeHomOverComp_id_right NeronModelInfra.schemeHomOverId_coe NeronModelInfra.NeronModelPropertyBundle.endExtensionEquiv_apply NeronModelInfra.NeronModelPropertyBundle.restrict_endExtensionEquiv_symm NeronModelInfra.schemeHomOverComp_coe SheafOfModules.tensorUnit_eq AlgebraicGeometry.Scheme.Modules.tensorUnit_eq PresheafOfModules.InternalHom.presheaf_map_apply PresheafOfModules.InternalHom.curryFamily_app PresheafOfModules.InternalHom.add_app PresheafOfModules.InternalHom.smul_app PresheafOfModules.InternalHom.zero_app PresheafOfModules.ihomObj_map_val PresheafOfModules.ihomFunctor_map PresheafOfModules.InternalHom.restrict_app PresheafOfModules.InternalHom.postcomp_app PresheafOfModules.InternalHom.neg_app PresheafOfModules.curry'_app_val PresheafOfModules.InternalHom.presheaf_obj PresheafOfModules.ihomFunctor_obj PresheafOfModules.ihomObj_obj PresheafOfModules.InternalHom.sub_app PresheafOfModules.ihomMap_app_val AlgebraicGeometry.Scheme.Modules.tensorPow_zero AlgebraicGeometry.Scheme.Modules.tensorPow_succ AlgebraicGeometry.RelPicard.RigidifiedLineBundle.mk.sizeOf_spec AlgebraicGeometry.RelPicard.RigidifiedLineBundle.mk.injEq AlgebraicGeometry.Scheme.OrderedAffineCover.mk.injEq"
p2m_attr_erase "simp" "AlgebraicGeometry.OModulePresheaf.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCover.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.mk.injEq AlgebraicGeometry.Scheme.TwoAffineOpenCover.mk.injEq AlgebraicGeometry.Scheme.TwoAffineOpenCover.mk.sizeOf_spec AlgebraicGeometry.Scheme.TwoAffineOpenCover.pullback_U1 AlgebraicGeometry.Scheme.TwoAffineOpenCover.pullback_U0 TwoChartCech.Sections.mk.injEq TwoChartCech.Cover.mk.injEq TwoChartCech.GrothendieckComplex.mk.injEq TwoChartCech.Sections.mk.sizeOf_spec TwoChartCech.Cover.mk.sizeOf_spec TwoChartCech.Cover.lineBundle_r0_apply TwoChartCech.GrothendieckComplex.mk.sizeOf_spec TwoChartCech.Cover.lineBundle_r1_apply CoherentBaseChange.TwoTermComplex.mk.sizeOf_spec CoherentBaseChange.TwoTermComplex.mk.injEq PresheafOfModules.freeεIso_hom_app PresheafOfModules.freeμIso_hom_app AlgebraicGeometry.RelPicard.RepresentsRelSubPic.mk.injEq AlgebraicGeometry.RelPicard.SubPicCondition.mk.injEq AlgebraicGeometry.RelPicard.SubPicCondition.mk.sizeOf_spec AlgebraicGeometry.RelPicard.RepresentsRelSubPic.mk.sizeOf_spec AlgebraicGeometry.SmoothProperCurve.sectionBaseChange_coe_snd AlgebraicGeometry.SmoothProperCurve.sectionBaseChange_coe_fst AlgebraicCurve.CurveModel.mk.injEq AlgebraicCurve.CurveModel.mk.sizeOf_spec AlgebraicCurve.mulAdele_apply AlgebraicCurve.residuePairing_apply_coe AlgebraicCurve.mem_adeleBdd AlgebraicCurve.weilSmul_one AlgebraicCurve.diagonalHom_apply AlgebraicCurve.weilSmul_apply AlgebraicCurve.adeleSpaceMul_coe AlgebraicCurve.mulAdele_one AlgebraicGeometry.SmoothProperCurve.FiniteMapData.twoAffineOpenCover_U1 AlgebraicGeometry.SmoothProperCurve.FiniteMapData.mk.injEq AlgebraicGeometry.SmoothProperCurve.FiniteMapData.mk.sizeOf_spec AlgebraicGeometry.SmoothProperCurve.FiniteMapData.twoAffineOpenCover_U0 AlgebraicGeometry.RelPicard.SubPicCondition.onClasses_mk"
p2m_attr_erase "simp" "AlgebraicGeometry.RelPicard.relSubPicPresheaf_map_coe CategoryTheory.Functor.OverTotal.ofFibre_fst CategoryTheory.Functor.overTotal_map_fst AlgebraicGeometry.Scheme.LocalRepresentabilityULift.glueData_J AlgebraicGeometry.Scheme.LocalRepresentabilityULift.uliftYoneda_toGlued_uliftYonedaGluedToSheaf AlgebraicGeometry.Scheme.LocalRepresentabilityULift.glueData_t' AlgebraicGeometry.Scheme.LocalRepresentabilityULift.uliftYoneda_toGlued_uliftYonedaGluedToSheaf_assoc AlgebraicGeometry.Scheme.LocalRepresentabilityULift.uliftYonedaGluedToSheaf_app_toGlued AlgebraicGeometry.Scheme.LocalRepresentabilityULift.glueData_openCover_map AlgebraicGeometry.Scheme.LocalRepresentabilityULift.uliftYonedaGluedToSheaf_app_comp AlgebraicGeometry.Scheme.LocalRepresentabilityULift.glueData_V AlgebraicGeometry.Scheme.LocalRepresentabilityULift.glueData_t AlgebraicGeometry.Scheme.LocalRepresentabilityULift.glueData_U AlgebraicGeometry.Scheme.LocalRepresentabilityULift.glueData_f AlgebraicGeometry.RelPicard.designationOfRepresentableBy_P AlgebraicGeometry.RelPicard.designationOfRepresentableBy_toBase AlgebraicGeometry.RelPicard.rigSection_snd AlgebraicGeometry.RelPicard.RigidifiedLineBundle.ofInvertible_L AlgebraicGeometry.RelPicard.rigSection_snd_assoc AlgebraicGeometry.RelPicard.SubPicGroupCondition.mk.injEq AlgebraicGeometry.RelPicard.SubPicGroupCondition.mk.sizeOf_spec AlgebraicCurve.coe_cechH0Equiv_apply AlgebraicCurve.cechH1ToH1_mk AlgebraicCurve.lSpaceOn_univ AlgebraicCurve.lSpaceOn_empty AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.Divisor.mapRestrict_single AlgebraicCurve.Divisor.pushforward_single AlgebraicCurve.Place.coe_restrictInclusion AlgebraicCurve.Place.mem_fiber AlgebraicCurve.Place.restrict_toValuationSubring AlgebraicCurve.Divisor.degree_pushforward AlgebraicCurve.Place.restrictResidueMap_residue AlgebraicCurve.Pic0.coe_pushforwardDegZeroHom AlgebraicCurve.Pic0.coe_pullbackDegZeroHom"
p2m_attr_erase "simp" "AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Divisor.degree_pushforwardAlong AlgebraicCurve.Pic0.coe_degZeroCorrespondence AlgebraicCurve.Place.mem_fiberAlong AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.jqNModC_one ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one"
p2m_attr_erase "simp" "AlgebraicCurve.Place.differentialCoeff_zero AlgebraicCurve.Place.differentialCoeff_dCoord AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.injEq AlgebraicCurve.TranscendenceTower.mk.injEq AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec AlgebraicCurve.PoleDivisorPackage.mk.injEq AlgebraicGeometry.RelPicard.thetaBundle_def AlgebraicGeometry.RelPicard.picardBundle_def AlgebraicGeometry.RelEffCartierDiv.toRelEffDivisor_ofRelEffDivisor AlgebraicGeometry.RelEffCartierDiv.toRelEffDivisor_I AlgebraicGeometry.mapOnProdOver_fst_assoc AlgebraicGeometry.RelEffCartierDiv.mk.sizeOf_spec AlgebraicGeometry.RelEffCartierDiv.mk.injEq AlgebraicGeometry.mapOnProdOver_snd AlgebraicGeometry.mapOnProdOver_fst AlgebraicGeometry.mapOnProdOver_snd_assoc AlgebraicGeometry.mapOnProdOver_id AlgebraicCurve.RelEffDivisor.mk.sizeOf_spec AlgebraicCurve.mapOnProd_fst AlgebraicCurve.mapOnProd_fst_assoc AlgebraicCurve.mapOnProd_snd AlgebraicCurve.UnivDivisorPack.mk.injEq AlgebraicCurve.RelEffDivisor.mk.injEq AlgebraicCurve.UnivDivisorPack.mk.sizeOf_spec AlgebraicCurve.mapOnProd_snd_assoc AlgebraicGeometry.Scheme.Modules.exteriorPower_obj PresheafOfModules.exteriorPower_map_ιMulti PresheafOfModules.ExteriorPower.appₗ_apply AlgebraicGeometry.prodKerGraph_one AlgebraicGeometry.fibrePowOver.proj_comp AlgebraicGeometry.prodKerGraph_zero AlgebraicGeometry.RelEffCartierDiv.empty_I AlgebraicGeometry.fibrePowOver.proj_comp_assoc AlgebraicGeometry.graphOver_fst_assoc AlgebraicGeometry.RelEffCartierDiv.toPoint_comp AlgebraicGeometry.RelEffCartierDiv.toPoint_comp_assoc AlgebraicGeometry.graphOver_fst AlgebraicGeometry.RelEffCartierDiv.ofPoint_I"
p2m_attr_erase "simp" "AlgebraicGeometry.graphOver_snd AlgebraicGeometry.graphOver_snd_assoc AlgebraicCurve.SymmetricPowerPackage.mk.sizeOf_spec AlgebraicCurve.SymmetricPowerPackage.mk.injEq AlgebraicGeometry.FGSubalgebra.cocone_ι_app_apply AlgebraicGeometry.RelPicard.fst_toProdSpec AlgebraicGeometry.RelPicard.toProdSpec_fst_assoc AlgebraicGeometry.RelPicard.pointsSubBasepointModule_cons AlgebraicGeometry.RelPicard.pointsSubBasepointModule_nil AlgebraicGeometry.RelPicard.fst_toProdSpec_assoc AlgebraicGeometry.RelPicard.toProdSpec_fst AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.sub_app AlgebraicGeometry.Scheme.IdealSheafData.sres_sresTop AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.add_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.mk.sizeOf_spec AlgebraicGeometry.Scheme.IdealSheafData.coe_resLE AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.smul_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.coe_ofLE_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.ideal_range AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.zero_app AlgebraicGeometry.Scheme.IdealSheafData.sres_sres AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.comp_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.neg_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.id_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.coe_mulRight_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.nsmul_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.mk.injEq AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.zsmul_app AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.sizeOf_spec AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.injEq AlgebraicCurve.adeleSingle_coe AlgebraicCurve.kaehlerResidueTermKFam_apply AlgebraicCurve.Place.LocalResidueData.mk.injEq AlgebraicCurve.Place.LocalResidueData.mk.sizeOf_spec AlgebraicCurve.Place.kw_ffgc_adicCompletionComapIntegers_coe AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.sizeOf_spec AlgebraicCurve.Place.mem_simplePoleSubmodule AlgebraicCurve.Place.coe_uniformizerSubring ModularCurve.Lg37.Lg37CompletionSection.mk.injEq AlgebraicCurve.Place.CoefficientFieldSection.mk.injEq"
p2m_attr_erase "simp" "AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.injEq ModularCurve.Lg37.Lg37CompletionSection.mk.sizeOf_spec AlgebraicCurve.Place.CoefficientFieldSection.mk.sizeOf_spec AlgebraicCurve.Place.poleSubmodule_one AlgebraicCurve.Place.mem_poleSubmodule AlgebraicGeometry.Scheme.Modules.toUnitSection_ofUnitSection AlgebraicGeometry.Scheme.Modules.pullbackSection_def AlgebraicGeometry.Scheme.Modules.ofUnitSection_toUnitSection PresheafOfModules.InternalHom.IsSheafAux.appAt_toPresheafHom SheafOfModules.ihomSectionsEquivFamily_unit AlgebraicGeometry.Scheme.Modules.restrictHomEquivFamily_apply SheafOfModules.ihomEval_unit_app AlgebraicGeometry.Scheme.Modules.ihomEval_zero_right AlgebraicGeometry.Scheme.Modules.ihomEval_zero_left AlgebraicGeometry.Scheme.Modules.homOfFamily_app_apply SheafOfModules.unit_ihomSectionsEquivFamily AlgebraicGeometry.Scheme.Modules.familyOfHom_app AlgebraicGeometry.Scheme.Modules.restrictUnitIso_hom_app_apply AlgebraicGeometry.Scheme.Modules.restrictUnitIso_inv_app_apply AlgebraicGeometry.Scheme.Modules.restrictHomOfFamily_app_apply AlgebraicGeometry.Scheme.Modules.restrictHomEquivFamily_symm_apply AlgebraicGeometry.Scheme.Modules.tensorSections_zero_right AlgebraicGeometry.Scheme.Modules.map_unitSection AlgebraicGeometry.Scheme.Modules.tensorSectionsBilin_apply AlgebraicGeometry.Scheme.Modules.tensorPowSection_zero AlgebraicGeometry.Scheme.Modules.tensorSections_zero_left AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_neg AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_zero AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_sub AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_add AlgebraicGeometry.Scheme.OrderedAffineCover.toCoverOf_U AlgebraicGeometry.Scheme.OrderedAffineCoverOf.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCoverOf.mk.injEq AlgebraicGeometry.Scheme.OrderedAffineCover.restrict_U AlgebraicGeometry.OModulePresheaf.Hom.mk.injEq AlgebraicGeometry.OModulePresheaf.Hom.id_app AlgebraicGeometry.OModulePresheaf.AffHom.appSections_apply AlgebraicGeometry.OModulePresheaf.AffHom.comp_app AlgebraicGeometry.OModulePresheaf.AffSES.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.AffHom.kerMap_coe"
p2m_attr_erase "simp" "AlgebraicGeometry.OModulePresheaf.AffHom.id_app AlgebraicGeometry.OModulePresheaf.Hom.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.Hom.toAffHom_app AlgebraicGeometry.OModulePresheaf.SES.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.AffHom.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.Hom.comp_app AlgebraicGeometry.OModulePresheaf.SES.mk.injEq AlgebraicGeometry.OModulePresheaf.AffHom.mk.injEq AlgebraicGeometry.OModulePresheaf.Hom.appSections_apply AlgebraicGeometry.OModulePresheaf.AffSES.mk.injEq AlgebraicGeometry.OModulePresheaf.prod_obj AlgebraicGeometry.OModulePresheaf.restrOpen_obj AlgebraicGeometry.OModulePresheaf.DevissageStep.mk.injEq AlgebraicGeometry.OModulePresheaf.pushforward_obj AlgebraicGeometry.OModulePresheaf.im_obj AlgebraicGeometry.OModulePresheaf.pow_obj AlgebraicGeometry.OModulePresheaf.fstHom_app AlgebraicGeometry.OModulePresheaf.ker_obj AlgebraicGeometry.OModulePresheaf.coker_obj AlgebraicGeometry.OModulePresheaf.DevissageStep.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCover.preimage_U AlgebraicGeometry.OModulePresheaf.sndHom_app AlgebraicGeometry.OModulePresheaf.Leray.restrictToPreimage_U DoubleComplex.Bounded.mk.injEq DoubleComplex.Bounded.mk.sizeOf_spec DoubleComplex.Convergence.mk.injEq DoubleComplex.Convergence.mk.sizeOf_spec DoubleComplex.SubQuot.mk.sizeOf_spec DoubleComplex.SubQuot.mk.injEq AlgebraicGeometry.ChowDatumProj.mk.sizeOf_spec AlgebraicGeometry.ChowDatum.mk.sizeOf_spec AlgebraicGeometry.ChowDatumProj.mk.injEq AlgebraicGeometry.ChowDatum.mk.injEq ProjSpaceCech.GradedModule.mk.injEq ProjSpaceCech.GradedModule.mk.sizeOf_spec ProjSpaceCech.GradedModule.Frac.mk.sizeOf_spec ProjSpaceCech.GradedModule.Presentation.mk.injEq ProjSpaceCech.GradedModule.Frac.mk.injEq ProjSpaceCech.GradedModule.Presentation.mk.sizeOf_spec ProjSpaceCech.GradedModule.Hom.shift_toLinearMap"
p2m_attr_erase "simp" "ProjSpaceCech.GradedModule.Hom.mk.sizeOf_spec ProjSpaceCech.GradedModule.Hom.mk.injEq TwoChartCech.Mumford.dK_apply TwoChartCech.Mumford.ι0_apply TwoChartCech.Mumford.ι1_apply TwoChartCech.KerCoprod.dK_apply TwoChartCech.KerCoprod.ι1_apply TwoChartCech.KerCoprod.ι0_apply AlgebraicGeometry.tilde.functorCompPullbackSpecIso_app AlgebraicGeometry.RelPicard.algEquivZeroGroupCut_toSubPicCondition AlgebraicGeometry.RelPicard.LFP.stageHom_val AlgebraicGeometry.RelPicard.BaseChange.relSubPicPresheafRestrictIso_hom_app_coe AlgebraicGeometry.RelPicard.BaseChange.relSubPicPresheafRestrictIso_inv_app_coe AlgebraicGeometry.RelPicard.BaseChange.restrict_P AlgebraicGeometry.RelEffCartierDiv.IsUniversal.lift_comp AlgebraicGeometry.RelEffCartierDiv.functor_map_fst AlgebraicGeometry.RelEffCartierDiv.IsUniversal.homEquiv_apply AlgebraicGeometry.RelEffCartierDiv.IsUniversal.lift_pullbackAlong AlgebraicGeometry.RelEffCartierDiv.IsUniversal.homEquiv_symm_apply AlgebraicGeometry.RelEffCartierDiv.IsUniversal.lift_comp_assoc AlgebraicGeometry.RelEffCartierDiv.supportedIn_top AlgebraicGeometry.RelEffCartierDiv.mem_supportedIn_iff AlgebraicGeometry.RelEffCartierDiv.supportedIn_top_eq AlgebraicGeometry.RelEffCartierDiv.restrictAlong_extendAlong AlgebraicGeometry.RelEffCartierDiv.extendAlong_I AlgebraicGeometry.RelEffCartierDiv.resProdMap_snd AlgebraicGeometry.RelEffCartierDiv.restrictAlong_I AlgebraicGeometry.RelEffCartierDiv.extendAlong_restrictAlong AlgebraicGeometry.RelEffCartierDiv.resProdMap_fst_assoc AlgebraicGeometry.RelEffCartierDiv.resProdMap_snd_assoc AlgebraicGeometry.RelEffCartierDiv.resProdMap_fst CoherentBaseChange.FibreH0Family.mk.sizeOf_spec CoherentBaseChange.FibreH0Family.mk.injEq AlgebraicGeometry.Scheme.Modules.ProjPresentation.mk.injEq AlgebraicGeometry.Scheme.Modules.ProjPresentation.mk.sizeOf_spec AlgebraicCurve.CurveModel.coe_gInf AlgebraicCurve.CurveModel.coe_tInvChart AlgebraicCurve.CurveModel.ιInf_gluedToBase_assoc AlgebraicCurve.CurveModel.ιInf_gluedToBase AlgebraicCurve.CurveModel.primeOfι₀_asIdeal"
p2m_attr_erase "simp" "AlgebraicCurve.CurveModel.coe_tChart AlgebraicCurve.CurveModel.ι₀_gluedToBase_assoc AlgebraicCurve.CurveModel.primeOfιInf_asIdeal AlgebraicCurve.CurveModel.ι₀_gluedToBase AlgebraicCurve.CurveModel.coe_tma AlgebraicCurve.CurveModel.coe_primeEquivChartPlaces RegularLocalRingQuotientAscent.dualNumberFst_apply AlgebraicGeometry.ProjSpace.twistObj.mk.injEq AlgebraicGeometry.ProjSpace.twistObj.zero_val AlgebraicGeometry.ProjSpace.twistObj.add_val AlgebraicGeometry.ProjSpace.twist_res_val AlgebraicGeometry.ProjSpace.twist_smul_val AlgebraicGeometry.ProjSpace.twistGradeToObj_val AlgebraicGeometry.ProjSpace.twistObj.smul_val AlgebraicGeometry.ProjSpace.twistGradeEquiv_apply_val AlgebraicGeometry.ProjSpace.twistObj.mk.sizeOf_spec GoodReductionJacobian.RelativeGroupLaw.fibre_inv GoodReductionJacobian.RelativeGroupLaw.fibrePointToBase_coe GoodReductionJacobian.RelativeGroupLaw.fibrePointOfBase_toBase GoodReductionJacobian.RelativeGroupLaw.fibre_mul GoodReductionJacobian.RelativeGroupLaw.fibrePointToBase_ofBase GoodReductionJacobian.RelativeGroupLaw.fibre_one GoodReductionJacobian.RelativeGroupLaw.fibrePointOfBase_coe AlgebraicGeometry.schemeFibreEndo_snd AlgebraicGeometry.schemeFibreEndo_fst"

set_option autoImplicit false

open scoped Quaternion
open CategoryTheory AlgebraicGeometry CerednikDrinfeld CerednikDrinfeld.QM NeronModelInfra

namespace Swap2

variable {S : Type} [CommRing S] {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} {N : ℕ}

theorem eq_one_of_eq_mul_self (E : FakeEllipticCurve Λ N S) {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of S))
    (x : SchemeHomOver t E.f) (hx : x = E.L.mul t x x) : x = E.L.one t := by
  have := congrArg (fun y => E.L.mul t (E.L.inv t x) y) hx
  rw [E.L.inv_mul_cancel, ← E.L.mul_assoc, E.L.inv_mul_cancel, E.L.one_mul] at this
  exact this.symm

theorem mapPt_one (E E' : FakeEllipticCurve Λ N S) (φ : E.A ⟶ E'.A) (hφ : φ ≫ E'.f = E.f)
    (hφmul : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of S)) (P Q : SchemeHomOver t E.f),
      mapPt φ hφ (E.L.mul t P Q) = E'.L.mul t (mapPt φ hφ P) (mapPt φ hφ Q))
    {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of S)) : mapPt φ hφ (E.L.one t) = E'.L.one t := by
  have h := hφmul t (E.L.one t) (E.L.one t)
  rw [E.L.one_mul] at h
  exact eq_one_of_eq_mul_self E' t _ h

theorem mapPt_comp {A A' A'' : Scheme.{0}}
    {f : A ⟶ Spec (CommRingCat.of S)} {f' : A' ⟶ Spec (CommRingCat.of S)} {f'' : A'' ⟶ Spec (CommRingCat.of S)}
    (φ : A ⟶ A') (hφ : φ ≫ f' = f) (ψ : A' ⟶ A'') (hψ : ψ ≫ f'' = f') (h : (φ ≫ ψ) ≫ f'' = f)
    {T : Scheme.{0}} {t : T ⟶ Spec (CommRingCat.of S)} (P : SchemeHomOver t f) :
    mapPt (φ ≫ ψ) h P = mapPt ψ hψ (mapPt φ hφ P) := by
  apply Subtype.ext; simp only [mapPt_coe, Category.assoc]

theorem mapPt_nsmulPt (E E' : FakeEllipticCurve Λ N S) (φ : E.A ⟶ E'.A) (hφ : φ ≫ E'.f = E.f)
    (hφmul : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of S)) (P Q : SchemeHomOver t E.f),
      mapPt φ hφ (E.L.mul t P Q) = E'.L.mul t (mapPt φ hφ P) (mapPt φ hφ Q))
    {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of S)) (n : ℕ) (P : SchemeHomOver t E.f) :
    mapPt φ hφ (nsmulPt E.L t n P) = nsmulPt E'.L t n (mapPt φ hφ P) := by
  induction n with
  | zero => exact mapPt_one E E' φ hφ hφmul t
  | succ n ih =>
    show mapPt φ hφ (E.L.mul t (nsmulPt E.L t n P) P) = E'.L.mul t (nsmulPt E'.L t n (mapPt φ hφ P)) (mapPt φ hφ P)
    rw [hφmul, ih]

theorem nsmulPt_nsmulPt (E : FakeEllipticCurve Λ N S) {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of S))
    (m n : ℕ) (P : SchemeHomOver t E.f) :
    nsmulPt E.L t m (nsmulPt E.L t n P) = nsmulPt E.L t (n * m) P := by
  letI := E.L.pointGroup t
  have hpow : ∀ (k : ℕ) (Q : SchemeHomOver t E.f), nsmulPt E.L t k Q = Q ^ k := by
    intro k Q
    induction k with
    | zero => rfl
    | succ k ih => show E.L.mul t (nsmulPt E.L t k Q) Q = Q ^ (k + 1); rw [ih, pow_succ]; rfl
  rw [hpow, hpow, hpow, pow_mul]

end Swap2

open Swap2 in
set_option maxHeartbeats 8000000 in
theorem solution
    {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} {N : ℕ} [NeZero N] (hΛ : QuaternionAlgebra.IsOrder Λ)
    (ℓ ℓ' : ℕ) [Fact ℓ.Prime] [Fact ℓ'.Prime] (hℓℓ' : ℓ ≠ ℓ')
    (E E₁ E₁' d d' : FakeEllipticCurve Λ N (AlgebraicClosure ℚ)) (K : E.ExtraLevel ℓ) (K' : E.ExtraLevel ℓ')

    (φ : E.A ⟶ E₁.A) (hφ : φ ≫ E₁.f = E.f) (ψ : E₁.A ⟶ E.A) (hψ : ψ ≫ E.f = E₁.f)
    (hφmul : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of (AlgebraicClosure ℚ))) (P Q : SchemeHomOver t E.f),
      mapPt φ hφ (E.L.mul t P Q) = E₁.L.mul t (mapPt φ hφ P) (mapPt φ hφ Q))
    (hφmul' : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of (AlgebraicClosure ℚ))) (P Q : SchemeHomOver t E₁.f),
      mapPt ψ hψ (E₁.L.mul t P Q) = E.L.mul t (mapPt ψ hψ P) (mapPt ψ hψ Q))
    (hφact : ∀ x : ↥Λ, E.act x ≫ φ = φ ≫ E₁.act x) (hφact' : ∀ x : ↥Λ, E₁.act x ≫ ψ = ψ ≫ E.act x)
    (hφcomp : ∀ hℓ : ((ℓ : ℚ) : ℍ[ℚ, a, b]) ∈ Λ,
      φ ≫ ψ = E.act ⟨((ℓ : ℚ) : ℍ[ℚ, a, b]), hℓ⟩ ∧ ψ ≫ φ = E₁.act ⟨((ℓ : ℚ) : ℍ[ℚ, a, b]), hℓ⟩)
    (hφker : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of (AlgebraicClosure ℚ))) (P : SchemeHomOver t E.f),
      mapPt φ hφ P = E₁.L.one t ↔ FactorsThrough K.levK P)
    (hφlev : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of (AlgebraicClosure ℚ))) (P : SchemeHomOver t E.f),
      FactorsThrough E.lev P → FactorsThrough E₁.lev (mapPt φ hφ P))

    (φ' : E.A ⟶ E₁'.A) (hφ' : φ' ≫ E₁'.f = E.f) (ψ' : E₁'.A ⟶ E.A) (hψ' : ψ' ≫ E.f = E₁'.f)
    (hφ'mul : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of (AlgebraicClosure ℚ))) (P Q : SchemeHomOver t E.f),
      mapPt φ' hφ' (E.L.mul t P Q) = E₁'.L.mul t (mapPt φ' hφ' P) (mapPt φ' hφ' Q))
    (hφ'mul' : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of (AlgebraicClosure ℚ))) (P Q : SchemeHomOver t E₁'.f),
      mapPt ψ' hψ' (E₁'.L.mul t P Q) = E.L.mul t (mapPt ψ' hψ' P) (mapPt ψ' hψ' Q))
    (hφ'act : ∀ x : ↥Λ, E.act x ≫ φ' = φ' ≫ E₁'.act x) (hφ'act' : ∀ x : ↥Λ, E₁'.act x ≫ ψ' = ψ' ≫ E.act x)
    (hφ'comp : ∀ hℓ : ((ℓ' : ℚ) : ℍ[ℚ, a, b]) ∈ Λ,
      φ' ≫ ψ' = E.act ⟨((ℓ' : ℚ) : ℍ[ℚ, a, b]), hℓ⟩ ∧ ψ' ≫ φ' = E₁'.act ⟨((ℓ' : ℚ) : ℍ[ℚ, a, b]), hℓ⟩)
    (hφ'ker : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of (AlgebraicClosure ℚ))) (P : SchemeHomOver t E.f),
      mapPt φ' hφ' P = E₁'.L.one t ↔ FactorsThrough K'.levK P)
    (hφ'lev : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of (AlgebraicClosure ℚ))) (P : SchemeHomOver t E.f),
      FactorsThrough E.lev P → FactorsThrough E₁'.lev (mapPt φ' hφ' P))

    (K₁' : E₁.ExtraLevel ℓ')
    (hK₁' : ∀ x : SchemeHomOver (𝟙 (Spec (CommRingCat.of (AlgebraicClosure ℚ)))) E₁.f,
      FactorsThrough K₁'.levK x ↔ ∃ y : SchemeHomOver (𝟙 (Spec (CommRingCat.of (AlgebraicClosure ℚ)))) E.f, FactorsThrough K'.levK y ∧ mapPt φ hφ y = x)
    (K₁ : E₁'.ExtraLevel ℓ)
    (hK₁ : ∀ x : SchemeHomOver (𝟙 (Spec (CommRingCat.of (AlgebraicClosure ℚ)))) E₁'.f,
      FactorsThrough K₁.levK x ↔ ∃ y : SchemeHomOver (𝟙 (Spec (CommRingCat.of (AlgebraicClosure ℚ)))) E.f, FactorsThrough K.levK y ∧ mapPt φ' hφ' y = x)

    (hd : FakeEllipticCurve.IsLevelIsogeny ℓ' (⟨E₁, K₁'⟩ : FakeEllipticCurve.WithExtraLevel Λ N ℓ' (AlgebraicClosure ℚ)) d)
    (hd' : FakeEllipticCurve.IsLevelIsogeny ℓ (⟨E₁', K₁⟩ : FakeEllipticCurve.WithExtraLevel Λ N ℓ (AlgebraicClosure ℚ)) d') :
    FakeEllipticCurve.Iso d d' := by
  classical

  obtain ⟨φd, hφd, ψd, hψd, hdmul, hdmul', hdact, hdact', hdcomp, hdker, hdlev⟩ := hd
  obtain ⟨φd', hφd', ψd', hψd', hd'mul, hd'mul', hd'act, hd'act', hd'comp, hd'ker, hd'lev⟩ := hd'
  have hℓp : ℓ.Prime := Fact.out
  have hℓ'p : ℓ'.Prime := Fact.out
  have h1Λ : (1 : ℍ[ℚ, a, b]) ∈ Λ := hΛ.one_mem
  have hnatΛ : ∀ n : ℕ, ((n : ℚ) : ℍ[ℚ, a, b]) ∈ Λ := fun n => by
    have : ((n : ℚ) : ℍ[ℚ, a, b]) = (n : ℤ) • (1 : ℍ[ℚ, a, b]) := by
      rw [← Int.cast_smul_eq_zsmul ℚ, Int.cast_natCast, Algebra.smul_def, mul_one]; rfl
    rw [this]; exact Λ.smul_mem _ h1Λ
  have hNQ : ((N : ℕ) : AlgebraicClosure ℚ) ≠ 0 := by exact_mod_cast (NeZero.ne N)
  have hnQ : ((ℓ * ℓ' : ℕ) : AlgebraicClosure ℚ) ≠ 0 := by exact_mod_cast (Nat.mul_ne_zero hℓp.ne_zero hℓ'p.ne_zero)
  have hnpos : 0 < ℓ * ℓ' := Nat.mul_pos hℓp.pos hℓ'p.pos

  have hψφ : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of (AlgebraicClosure ℚ))) (P : SchemeHomOver t E.f), mapPt ψ hψ (mapPt φ hφ P) = nsmulPt E.L t ℓ P := by
    intro T t P; rw [← mapPt_comp φ hφ ψ hψ (by rw [Category.assoc, hψ, hφ]), ← CerednikDrinfeld.QM.FakeEllipticCurve.pushPt_act_natCast_eq_nsmulPt E h1Λ ℓ (hnatΛ ℓ) t P]
    apply Subtype.ext; simp only [mapPt_coe, (hφcomp (hnatΛ ℓ)).1]
  have hφψ : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of (AlgebraicClosure ℚ))) (P : SchemeHomOver t E₁.f), mapPt φ hφ (mapPt ψ hψ P) = nsmulPt E₁.L t ℓ P := by
    intro T t P; rw [← mapPt_comp ψ hψ φ hφ (by rw [Category.assoc, hφ, hψ]), ← CerednikDrinfeld.QM.FakeEllipticCurve.pushPt_act_natCast_eq_nsmulPt E₁ h1Λ ℓ (hnatΛ ℓ) t P]
    apply Subtype.ext; simp only [mapPt_coe, (hφcomp (hnatΛ ℓ)).2]
  have hψφ' : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of (AlgebraicClosure ℚ))) (P : SchemeHomOver t E.f), mapPt ψ' hψ' (mapPt φ' hφ' P) = nsmulPt E.L t ℓ' P := by
    intro T t P; rw [← mapPt_comp φ' hφ' ψ' hψ' (by rw [Category.assoc, hψ', hφ']), ← CerednikDrinfeld.QM.FakeEllipticCurve.pushPt_act_natCast_eq_nsmulPt E h1Λ ℓ' (hnatΛ ℓ') t P]
    apply Subtype.ext; simp only [mapPt_coe, (hφ'comp (hnatΛ ℓ')).1]
  have hφψ' : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of (AlgebraicClosure ℚ))) (P : SchemeHomOver t E₁'.f), mapPt φ' hφ' (mapPt ψ' hψ' P) = nsmulPt E₁'.L t ℓ' P := by
    intro T t P; rw [← mapPt_comp ψ' hψ' φ' hφ' (by rw [Category.assoc, hφ', hψ']), ← CerednikDrinfeld.QM.FakeEllipticCurve.pushPt_act_natCast_eq_nsmulPt E₁' h1Λ ℓ' (hnatΛ ℓ') t P]
    apply Subtype.ext; simp only [mapPt_coe, (hφ'comp (hnatΛ ℓ')).2]
  have hψφd : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of (AlgebraicClosure ℚ))) (P : SchemeHomOver t E₁.f), mapPt ψd hψd (mapPt φd hφd P) = nsmulPt E₁.L t ℓ' P := by
    intro T t P; rw [← mapPt_comp φd hφd ψd hψd (by rw [Category.assoc, hψd, hφd]), ← CerednikDrinfeld.QM.FakeEllipticCurve.pushPt_act_natCast_eq_nsmulPt E₁ h1Λ ℓ' (hnatΛ ℓ') t P]
    apply Subtype.ext; simp only [mapPt_coe, (hdcomp (hnatΛ ℓ')).1]
  have hφψd : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of (AlgebraicClosure ℚ))) (P : SchemeHomOver t d.f), mapPt φd hφd (mapPt ψd hψd P) = nsmulPt d.L t ℓ' P := by
    intro T t P; rw [← mapPt_comp ψd hψd φd hφd (by rw [Category.assoc, hφd, hψd]), ← CerednikDrinfeld.QM.FakeEllipticCurve.pushPt_act_natCast_eq_nsmulPt d h1Λ ℓ' (hnatΛ ℓ') t P]
    apply Subtype.ext; simp only [mapPt_coe, (hdcomp (hnatΛ ℓ')).2]
  have hψφd' : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of (AlgebraicClosure ℚ))) (P : SchemeHomOver t E₁'.f), mapPt ψd' hψd' (mapPt φd' hφd' P) = nsmulPt E₁'.L t ℓ P := by
    intro T t P; rw [← mapPt_comp φd' hφd' ψd' hψd' (by rw [Category.assoc, hψd', hφd']), ← CerednikDrinfeld.QM.FakeEllipticCurve.pushPt_act_natCast_eq_nsmulPt E₁' h1Λ ℓ (hnatΛ ℓ) t P]
    apply Subtype.ext; simp only [mapPt_coe, (hd'comp (hnatΛ ℓ)).1]
  have hφψd' : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of (AlgebraicClosure ℚ))) (P : SchemeHomOver t d'.f), mapPt φd' hφd' (mapPt ψd' hψd' P) = nsmulPt d'.L t ℓ P := by
    intro T t P; rw [← mapPt_comp ψd' hψd' φd' hφd' (by rw [Category.assoc, hφd', hψd']), ← CerednikDrinfeld.QM.FakeEllipticCurve.pushPt_act_natCast_eq_nsmulPt d' h1Λ ℓ (hnatΛ ℓ) t P]
    apply Subtype.ext; simp only [mapPt_coe, (hd'comp (hnatΛ ℓ)).2]

  have hΦ : (φ ≫ φd) ≫ d.f = E.f := by rw [Category.assoc, hφd, hφ]
  have hΨ : (ψd ≫ ψ) ≫ E.f = d.f := by rw [Category.assoc, hψ, hψd]
  have hΦ' : (φ' ≫ φd') ≫ d'.f = E.f := by rw [Category.assoc, hφd', hφ']
  have hΨ' : (ψd' ≫ ψ') ≫ E.f = d'.f := by rw [Category.assoc, hψ', hψd']
  have hΦmul : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of (AlgebraicClosure ℚ))) (P Q : SchemeHomOver t E.f),
      mapPt (φ ≫ φd) hΦ (E.L.mul t P Q) = d.L.mul t (mapPt (φ ≫ φd) hΦ P) (mapPt (φ ≫ φd) hΦ Q) := by
    intro T t P Q; simp only [mapPt_comp φ hφ φd hφd hΦ, hφmul, hdmul]
  have hΦ'mul : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of (AlgebraicClosure ℚ))) (P Q : SchemeHomOver t E.f),
      mapPt (φ' ≫ φd') hΦ' (E.L.mul t P Q) = d'.L.mul t (mapPt (φ' ≫ φd') hΦ' P) (mapPt (φ' ≫ φd') hΦ' Q) := by
    intro T t P Q; simp only [mapPt_comp φ' hφ' φd' hφd' hΦ', hφ'mul, hd'mul]
  have hΦact : ∀ x : ↥Λ, E.act x ≫ (φ ≫ φd) = (φ ≫ φd) ≫ d.act x := by
    intro x; rw [← Category.assoc, hφact, Category.assoc, hdact, Category.assoc]
  have hΦ'act : ∀ x : ↥Λ, E.act x ≫ (φ' ≫ φd') = (φ' ≫ φd') ≫ d'.act x := by
    intro x; rw [← Category.assoc, hφ'act, Category.assoc, hd'act, Category.assoc]
  have hΨΦ : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of (AlgebraicClosure ℚ))) (P : SchemeHomOver t E.f),
      mapPt (ψd ≫ ψ) hΨ (mapPt (φ ≫ φd) hΦ P) = nsmulPt E.L t (ℓ * ℓ') P := by
    intro T t P
    rw [mapPt_comp φ hφ φd hφd hΦ, mapPt_comp ψd hψd ψ hψ hΨ, hψφd, mapPt_nsmulPt E₁ E ψ hψ hφmul', hψφ, nsmulPt_nsmulPt]
  have hΦΨ : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of (AlgebraicClosure ℚ))) (P : SchemeHomOver t d.f),
      mapPt (φ ≫ φd) hΦ (mapPt (ψd ≫ ψ) hΨ P) = nsmulPt d.L t (ℓ * ℓ') P := by
    intro T t P
    rw [mapPt_comp ψd hψd ψ hψ hΨ, mapPt_comp φ hφ φd hφd hΦ, hφψ, mapPt_nsmulPt E₁ d φd hφd hdmul, hφψd, nsmulPt_nsmulPt, Nat.mul_comm]
  have hΨ'Φ' : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of (AlgebraicClosure ℚ))) (P : SchemeHomOver t E.f),
      mapPt (ψd' ≫ ψ') hΨ' (mapPt (φ' ≫ φd') hΦ' P) = nsmulPt E.L t (ℓ * ℓ') P := by
    intro T t P
    rw [mapPt_comp φ' hφ' φd' hφd' hΦ', mapPt_comp ψd' hψd' ψ' hψ' hΨ', hψφd', mapPt_nsmulPt E₁' E ψ' hψ' hφ'mul', hψφ', nsmulPt_nsmulPt, Nat.mul_comm]
  have hΦ'Ψ' : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of (AlgebraicClosure ℚ))) (P : SchemeHomOver t d'.f),
      mapPt (φ' ≫ φd') hΦ' (mapPt (ψd' ≫ ψ') hΨ' P) = nsmulPt d'.L t (ℓ * ℓ') P := by
    intro T t P
    rw [mapPt_comp ψd' hψd' ψ' hψ' hΨ', mapPt_comp φ' hφ' φd' hφd' hΦ', hφψ', mapPt_nsmulPt E₁' d' φd' hφd' hd'mul, hφψd', nsmulPt_nsmulPt]

  have mapPt_inv_aux : ∀ (X Y : FakeEllipticCurve Λ N (AlgebraicClosure ℚ)) (g : X.A ⟶ Y.A) (hg : g ≫ Y.f = X.f)
      (hgmul : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of (AlgebraicClosure ℚ))) (P Q : SchemeHomOver t X.f),
        mapPt g hg (X.L.mul t P Q) = Y.L.mul t (mapPt g hg P) (mapPt g hg Q))
      {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of (AlgebraicClosure ℚ))) (y : SchemeHomOver t X.f),
      mapPt g hg (X.L.inv t y) = Y.L.inv t (mapPt g hg y) := by
    intro X Y g hg hgmul T t y
    letI := Y.L.pointGroup t
    have h := hgmul t (X.L.inv t y) y
    rw [X.L.inv_mul_cancel, mapPt_one X Y g hg hgmul] at h

    have : mapPt g hg (X.L.inv t y) * mapPt g hg y = 1 := h.symm
    exact eq_inv_of_mul_eq_one_left this
  have hkerpt : ∀ P : SchemeHomOver (𝟙 (Spec (CommRingCat.of (AlgebraicClosure ℚ)))) E.f,
      mapPt (φ ≫ φd) hΦ P = d.L.one _ ↔ mapPt (φ' ≫ φd') hΦ' P = d'.L.one _ := by
    intro P
    letI iE := E.L.pointGroup (𝟙 (Spec (CommRingCat.of (AlgebraicClosure ℚ))))
    letI iE₁ := E₁.L.pointGroup (𝟙 (Spec (CommRingCat.of (AlgebraicClosure ℚ))))
    letI iE₁' := E₁'.L.pointGroup (𝟙 (Spec (CommRingCat.of (AlgebraicClosure ℚ))))
    have hcomm : ∀ x y : SchemeHomOver (𝟙 (Spec (CommRingCat.of (AlgebraicClosure ℚ)))) E.f, x * y = y * x :=
      fun x y => E.comm _ x y

    have key : ∀ (Y : FakeEllipticCurve Λ N (AlgebraicClosure ℚ)) (g : E.A ⟶ Y.A) (hg : g ≫ Y.f = E.f)
        (hgmul : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of (AlgebraicClosure ℚ))) (P Q : SchemeHomOver t E.f),
          mapPt g hg (E.L.mul t P Q) = Y.L.mul t (mapPt g hg P) (mapPt g hg Q))
        (Kg Ks : ∀ x : SchemeHomOver (𝟙 (Spec (CommRingCat.of (AlgebraicClosure ℚ)))) E.f, Prop)
        (hgker : ∀ x : SchemeHomOver (𝟙 (Spec (CommRingCat.of (AlgebraicClosure ℚ)))) E.f, mapPt g hg x = Y.L.one _ ↔ Kg x),
        (∃ y, Ks y ∧ mapPt g hg y = mapPt g hg P) ↔ (∃ y, Ks y ∧ Kg (P * y⁻¹)) := by
      intro Y g hg hgmul Kg Ks hgker
      letI iY := Y.L.pointGroup (𝟙 (Spec (CommRingCat.of (AlgebraicClosure ℚ))))
      have hgm : ∀ x y : SchemeHomOver (𝟙 (Spec (CommRingCat.of (AlgebraicClosure ℚ)))) E.f, mapPt g hg (x * y) = mapPt g hg x * mapPt g hg y :=
        fun x y => hgmul _ x y
      have hgi : ∀ y : SchemeHomOver (𝟙 (Spec (CommRingCat.of (AlgebraicClosure ℚ)))) E.f, mapPt g hg y⁻¹ = (mapPt g hg y)⁻¹ :=
        fun y => mapPt_inv_aux E Y g hg hgmul _ y
      refine exists_congr fun y => and_congr_right fun _ => ?_
      rw [← hgker, hgm, hgi]
      constructor
      · intro h; rw [← h]; exact mul_inv_cancel _
      · intro h; exact (mul_inv_eq_one.mp h).symm
    have hL : mapPt (φ ≫ φd) hΦ P = d.L.one _ ↔ ∃ y, FactorsThrough K'.levK y ∧ FactorsThrough K.levK (P * y⁻¹) := by
      rw [mapPt_comp φ hφ φd hφd hΦ, hdker, hK₁']
      exact key E₁ φ hφ hφmul (fun x => FactorsThrough K.levK x) (fun x => FactorsThrough K'.levK x) (fun x => hφker _ x)
    have hR : mapPt (φ' ≫ φd') hΦ' P = d'.L.one _ ↔ ∃ y, FactorsThrough K.levK y ∧ FactorsThrough K'.levK (P * y⁻¹) := by
      rw [mapPt_comp φ' hφ' φd' hφd' hΦ', hd'ker, hK₁]
      exact key E₁' φ' hφ' hφ'mul (fun x => FactorsThrough K'.levK x) (fun x => FactorsThrough K.levK x) (fun x => hφ'ker _ x)
    rw [hL, hR]
    have swap : ∀ (A B : SchemeHomOver (𝟙 (Spec (CommRingCat.of (AlgebraicClosure ℚ)))) E.f → Prop),
        (∃ y, A y ∧ B (P * y⁻¹)) → (∃ z, B z ∧ A (P * z⁻¹)) := by
      intro A B ⟨y, hy, hPy⟩
      refine ⟨P * y⁻¹, hPy, ?_⟩
      have : P * (P * y⁻¹)⁻¹ = y := by rw [mul_inv_rev, inv_inv, hcomm y P⁻¹, mul_inv_cancel_left]
      rw [this]; exact hy
    exact ⟨swap _ _, swap _ _⟩

  have hker : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of (AlgebraicClosure ℚ))) (P : SchemeHomOver t E.f),
      mapPt (φ ≫ φd) hΦ P = d.L.one t → mapPt (φ' ≫ φd') hΦ' P = d'.L.one t :=
    fun {T} t P => CerednikDrinfeld.QM.FakeEllipticCurve.forall_mapPt_eq_one_of_forall_rationalPoint (AlgebraicClosure ℚ) E d d' (ℓ * ℓ') hnQ
      (φ ≫ φd) hΦ hΦmul hΦact (ψd ≫ ψ) hΨ hΨΦ hΦΨ (φ' ≫ φd') hΦ' (fun P h => (hkerpt P).1 h) t P
  have hker' : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of (AlgebraicClosure ℚ))) (P : SchemeHomOver t E.f),
      mapPt (φ' ≫ φd') hΦ' P = d'.L.one t → mapPt (φ ≫ φd) hΦ P = d.L.one t :=
    fun {T} t P => CerednikDrinfeld.QM.FakeEllipticCurve.forall_mapPt_eq_one_of_forall_rationalPoint (AlgebraicClosure ℚ) E d' d (ℓ * ℓ') hnQ
      (φ' ≫ φd') hΦ' hΦ'mul hΦ'act (ψd' ≫ ψ') hΨ' hΨ'Φ' hΦ'Ψ' (φ ≫ φd) hΦ (fun P h => (hkerpt P).2 h) t P

  obtain ⟨χ, hχ, hΦχ, -, hχmul, hχact, hχiso⟩ :=
    CerednikDrinfeld.QM.FakeEllipticCurve.exists_unique_comp_eq_of_forall_mapPt_eq_one (AlgebraicClosure ℚ) E d d'
      (φ ≫ φd) hΦ hΦmul hΦact (ψd ≫ ψ) hΨ (ℓ * ℓ') hnpos hΨΦ hΦΨ
      (φ' ≫ φd') hΦ' hΦ'mul hΦ'act (ψd' ≫ ψ') hΨ' (ℓ * ℓ') hnpos hΨ'Φ' hΦ'Ψ' hker
  haveI hiso : IsIso χ := hχiso hker'

  have hinjΦ : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of (AlgebraicClosure ℚ))) (P : SchemeHomOver t E.f),
      mapPt (φ ≫ φd) hΦ P = d.L.one t → FactorsThrough E.lev P → P = E.L.one t := by
    intro T t P h1 hC
    rw [mapPt_comp φ hφ φd hφd hΦ, hdker] at h1
    have hC₁ : FactorsThrough E₁.lev (mapPt φ hφ P) := hφlev t P hC
    have h2 : mapPt φ hφ P = E₁.L.one t := K₁'.levK_disjoint t _ h1 hC₁
    have h3 : FactorsThrough K.levK P := (hφker t P).1 h2
    exact K.levK_disjoint t P h3 hC
  have hinjΦ' : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of (AlgebraicClosure ℚ))) (P : SchemeHomOver t E.f),
      mapPt (φ' ≫ φd') hΦ' P = d'.L.one t → FactorsThrough E.lev P → P = E.L.one t := by
    intro T t P h1 hC
    rw [mapPt_comp φ' hφ' φd' hφd' hΦ', hd'ker] at h1
    have hC₁ : FactorsThrough E₁'.lev (mapPt φ' hφ' P) := hφ'lev t P hC
    have h2 : mapPt φ' hφ' P = E₁'.L.one t := K₁.levK_disjoint t _ h1 hC₁
    have h3 : FactorsThrough K'.levK P := (hφ'ker t P).1 h2
    exact K'.levK_disjoint t P h3 hC
  have hlevΦ : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of (AlgebraicClosure ℚ))) (P : SchemeHomOver t E.f),
      FactorsThrough E.lev P → FactorsThrough d.lev (mapPt (φ ≫ φd) hΦ P) := by
    intro T t P hC; rw [mapPt_comp φ hφ φd hφd hΦ]; exact hdlev t _ (hφlev t P hC)
  have hlevΦ' : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of (AlgebraicClosure ℚ))) (P : SchemeHomOver t E.f),
      FactorsThrough E.lev P → FactorsThrough d'.lev (mapPt (φ' ≫ φd') hΦ' P) := by
    intro T t P hC; rw [mapPt_comp φ' hφ' φd' hφd' hΦ']; exact hd'lev t _ (hφ'lev t P hC)
  have hontoΦ : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of (AlgebraicClosure ℚ))) (Q : SchemeHomOver t d.f),
      FactorsThrough d.lev Q → ∃ P : SchemeHomOver t E.f, FactorsThrough E.lev P ∧ mapPt (φ ≫ φd) hΦ P = Q :=
    fun {T} t Q => CerednikDrinfeld.QM.FakeEllipticCurve.exists_factorsThrough_lev_mapPt_eq_of_forall_eq_one (AlgebraicClosure ℚ) hNQ
      E d (φ ≫ φd) hΦ hΦmul hinjΦ hlevΦ t Q
  have hontoΦ' : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of (AlgebraicClosure ℚ))) (Q : SchemeHomOver t d'.f),
      FactorsThrough d'.lev Q → ∃ P : SchemeHomOver t E.f, FactorsThrough E.lev P ∧ mapPt (φ' ≫ φd') hΦ' P = Q :=
    fun {T} t Q => CerednikDrinfeld.QM.FakeEllipticCurve.exists_factorsThrough_lev_mapPt_eq_of_forall_eq_one (AlgebraicClosure ℚ) hNQ
      E d' (φ' ≫ φd') hΦ' hΦ'mul hinjΦ' hlevΦ' t Q

  refine ⟨asIso χ, by simpa using hχ, ?_, ?_, ?_⟩
  · intro T t P Q
    have := hχmul hχ t P Q
    convert this using 2 <;> rfl
  · intro x; simpa using hχact x
  · intro T t Q
    constructor
    · intro hQ
      obtain ⟨P, hP, rfl⟩ := hontoΦ t Q hQ
      have : mapPt (asIso χ).hom (by simpa using hχ) (mapPt (φ ≫ φd) hΦ P) = mapPt (φ' ≫ φd') hΦ' P := by
        apply Subtype.ext; simp only [mapPt_coe, asIso_hom, Category.assoc]; rw [← Category.assoc φ φd χ, ← hΦχ]
      rw [this]; exact hlevΦ' t P hP
    · intro hQ
      obtain ⟨P, hP, hPQ⟩ := hontoΦ' t _ hQ
      have h3 := congrArg Subtype.val hPQ
      simp only [mapPt_coe, asIso_hom] at h3
      rw [← hΦχ] at h3
      have h4 : ((P : T ⟶ E.A) ≫ (φ ≫ φd)) ≫ χ = (Q : T ⟶ d.A) ≫ χ := by simpa only [Category.assoc] using h3
      have h5 : mapPt (φ ≫ φd) hΦ P = Q := Subtype.ext ((cancel_mono χ).1 h4)
      rw [← h5]; exact hlevΦ t P hP

end S_CerednikDrinfeld_QM_FakeEllipticCurve_iso_of_isLevelIsogeny_transfer_swap
end P2MW
export P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_iso_of_isLevelIsogeny_transfer_swap (solution)
