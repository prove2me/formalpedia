-- Prove2me | solution 1 for CerednikDrinfeld.QM.FakeEllipticCurve.isAtkinLehnerQuotient_of_isLevelIsogeny_of_isLevelIsogeny
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.141142+00:00
-- url     : https://prove2.me/submissions/6318897a-1bc1-520c-ad17-2b5cf595b926

import Mathlib
import Definitions.Def_CerednikDrinfeld_QMModuliProps
import Theorems.Thm_QuaternionAlgebra_IsOrder_exists_intCast_eq_nrd_and_exists_intCast_eq_trd
import Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_exists_unique_comp_eq_of_forall_mapPt_eq_one
import Theorems.Thm_CerednikDrinfeld_QM_surjective_and_isFinite_and_flat_of_mapPt_mapPt_eq_nsmulPt
import Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_exists_factorsThrough_lev_mapPt_eq_of_forall_eq_one
import Theorems.Thm_AlgebraicGeometry_isIso_of_isClosedImmersion_of_finrank_comp_eq
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_isAtkinLehnerQuotient_of_isLevelIsogeny_of_isLevelIsogeny
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

noncomputable section

universe u

p2m_open "CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra~schemeHomOverComp~schemeHomOverComp_coe GoodReductionJacobian"
open CerednikDrinfeld CerednikDrinfeld.QM CerednikDrinfeld.QM.FakeEllipticCurve QuaternionAlgebra
open scoped Quaternion

namespace ALComm

variable {S : Type u} [CommRing S] {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} {N : ℕ}

abbrev aP (E : FakeEllipticCurve Λ N S) (m : ↥Λ) {T : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of S)}
    (P : SchemeHomOver t E.f) : SchemeHomOver t E.f :=
  pushPt (E.act m) (E.act_over m) P

section Action

variable (E : FakeEllipticCurve Λ N S) {T : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of S)}

theorem aP_coe (m : ↥Λ) (P : SchemeHomOver t E.f) : (aP E m P).1 = P.1 ≫ E.act m := rfl

theorem aP_mul (x y : ↥Λ) (h : (x : ℍ[ℚ, a, b]) * (y : ℍ[ℚ, a, b]) ∈ Λ) (P : SchemeHomOver t E.f) :
    aP E x (aP E y P) = aP E ⟨(x : ℍ[ℚ, a, b]) * (y : ℍ[ℚ, a, b]), h⟩ P := by
  apply Subtype.ext
  simp only [aP_coe, Category.assoc, E.act_mul x y h]

theorem aP_congr {x y : ↥Λ} (h : (x : ℍ[ℚ, a, b]) = (y : ℍ[ℚ, a, b])) (P : SchemeHomOver t E.f) :
    aP E x P = aP E y P := by
  obtain rfl : x = y := Subtype.ext h; rfl

theorem aP_add (x y : ↥Λ) (P : SchemeHomOver t E.f) :
    aP E (x + y) P = E.L.mul t (aP E x P) (aP E y P) := E.act_add x y t P

theorem aP_hom (m : ↥Λ) (P Q : SchemeHomOver t E.f) :
    aP E m (E.L.mul t P Q) = E.L.mul t (aP E m P) (aP E m Q) := E.act_hom m t P Q

theorem aP_one (m : ↥Λ) : aP E m (E.L.one t) = E.L.one t := by
  set x := aP E m (E.L.one t) with hx
  have hxx : E.L.mul t x x = x := by rw [hx, ← aP_hom, E.L.one_mul]
  letI := E.L.pointGroup t
  have h2 : x * x = x * 1 := by rw [mul_one]; exact hxx
  exact mul_left_cancel h2

theorem aP_unit (h1 : (1 : ℍ[ℚ, a, b]) ∈ Λ) (P : SchemeHomOver t E.f) : aP E ⟨1, h1⟩ P = P := by
  apply Subtype.ext
  simp only [aP_coe, E.act_one h1, Category.comp_id]

theorem aP_zero (P : SchemeHomOver t E.f) : aP E 0 P = E.L.one t := by
  have h := aP_add E 0 0 P
  rw [add_zero] at h
  letI := E.L.pointGroup t
  have h2 : aP E 0 P * aP E 0 P = aP E 0 P * 1 := by rw [mul_one]; exact h.symm
  exact mul_left_cancel h2

end Action

section Arithmetic

theorem intCast_mem (hΛ : IsOrder Λ) (z : ℤ) : (((z : ℚ)) : ℍ[ℚ, a, b]) ∈ Λ := by
  have : (((z : ℚ)) : ℍ[ℚ, a, b]) = z • (1 : ℍ[ℚ, a, b]) := by
    rw [zsmul_eq_mul, mul_one, coe_intCast]
  rw [this]; exact Λ.smul_mem z hΛ.one_mem

theorem natCast_mem (hΛ : IsOrder Λ) (n : ℕ) : (((n : ℚ)) : ℍ[ℚ, a, b]) ∈ Λ := by
  have := intCast_mem hΛ (n : ℤ); push_cast at this; exact this

def PCond (r : ℕ) (m : ℍ[ℚ, a, b]) : Prop :=
  ∃ n : ℤ, m * star m = ((((r : ℤ) * n : ℚ)) : ℍ[ℚ, a, b])

theorem pcond_natCast (r : ℕ) : PCond (a := a) (b := b) r ((r : ℚ) : ℍ[ℚ, a, b]) :=
  ⟨r, by rw [star_coe, ← coe_mul]; exact congrArg (fun x : ℚ => (x : ℍ[ℚ, a, b])) (by norm_cast)⟩

theorem pcond_intCast_mul (r : ℕ) (z : ℤ) : PCond (a := a) (b := b) r (((z * r : ℤ) : ℚ) : ℍ[ℚ, a, b]) :=
  ⟨z * z * r, by rw [star_coe, ← coe_mul]; congr 1; push_cast; ring⟩

theorem pcond_mul (hΛ : IsOrder Λ) (r : ℕ) {m m' : ℍ[ℚ, a, b]} (hm : PCond r m) (hm' : m' ∈ Λ) :
    PCond r (m * m') := by
  obtain ⟨n, hn⟩ := hm
  obtain ⟨⟨k, hk⟩, -⟩ := QuaternionAlgebra.IsOrder.exists_intCast_eq_nrd_and_exists_intCast_eq_trd hΛ hm'
  refine ⟨n * k, ?_⟩
  calc m * m' * star (m * m') = m * (m' * star m') * star m := by rw [star_mul]; simp only [mul_assoc]
    _ = m * ((nrd m' : ℚ) : ℍ[ℚ, a, b]) * star m := by rw [mul_star_eq_coe_nrd, mul_assoc]
    _ = ((k : ℚ) : ℍ[ℚ, a, b]) * (m * star m) := by rw [← hk, ← coe_commutes, mul_assoc]
    _ = (((((r : ℤ) : ℚ) * ((n * k : ℤ) : ℚ) : ℚ)) : ℍ[ℚ, a, b]) := by
        rw [hn, ← coe_mul]; exact congrArg (fun x : ℚ => (x : ℍ[ℚ, a, b])) (by push_cast; ring)

end Arithmetic

section Kernel

variable (E : FakeEllipticCurve Λ N S) {T : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of S)}

def Kill (r : ℕ) (P : SchemeHomOver t E.f) : Prop :=
  ∀ (m : ↥Λ) (n : ℤ), (m : ℍ[ℚ, a, b]) * star (m : ℍ[ℚ, a, b]) = ((((r : ℤ) * n : ℚ)) : ℍ[ℚ, a, b]) →
    aP E m P = E.L.one t

theorem kill_iff (r : ℕ) (P : SchemeHomOver t E.f) :
    Kill E r P ↔ ∀ m : ↥Λ, PCond r (m : ℍ[ℚ, a, b]) → aP E m P = E.L.one t :=
  ⟨fun h m ⟨n, hn⟩ => h m n hn, fun h m n hn => h m ⟨n, hn⟩⟩

theorem swap (hΛ : IsOrder Λ) (q q' : ℕ) (hqq' : Nat.Coprime q q') (P : SchemeHomOver t E.f)
    (A1 : ∀ m : ↥Λ, PCond q' (m : ℍ[ℚ, a, b]) → Kill E q (aP E m P)) :
    ∀ m' : ↥Λ, PCond q (m' : ℍ[ℚ, a, b]) → Kill E q' (aP E m' P) := by
  classical

  obtain ⟨A, B, hAB⟩ := hqq'.isCoprime

  let e₁ : ↥Λ := ⟨(((A * q : ℤ) : ℚ) : ℍ[ℚ, a, b]), intCast_mem hΛ _⟩
  let e₂ : ↥Λ := ⟨(((B * q' : ℤ) : ℚ) : ℍ[ℚ, a, b]), intCast_mem hΛ _⟩
  have he : e₁ + e₂ = ⟨1, hΛ.one_mem⟩ := by
    apply Subtype.ext
    show (((A * q : ℤ) : ℚ) : ℍ[ℚ, a, b]) + (((B * q' : ℤ) : ℚ) : ℍ[ℚ, a, b]) = 1
    rw [← coe_add, ← coe_one]; congr 1; exact_mod_cast hAB
  let cq : ↥Λ := ⟨((q : ℚ) : ℍ[ℚ, a, b]), natCast_mem hΛ q⟩
  let cA : ↥Λ := ⟨((A : ℚ) : ℍ[ℚ, a, b]), intCast_mem hΛ A⟩

  have hP₁ : Kill E q' (aP E e₁ P) := by
    rw [kill_iff]
    intro m hm

    have h1 : aP E cq (aP E m P) = E.L.one t := by
      have := A1 m hm; rw [kill_iff] at this
      exact this cq (pcond_natCast q)
    have hmem : ((q : ℚ) : ℍ[ℚ, a, b]) * (m : ℍ[ℚ, a, b]) ∈ Λ := hΛ.mul_mem cq.2 m.2
    rw [aP_mul E cq m hmem] at h1
    have hmem2 : ((A : ℚ) : ℍ[ℚ, a, b]) * (((q : ℚ) : ℍ[ℚ, a, b]) * (m : ℍ[ℚ, a, b])) ∈ Λ := hΛ.mul_mem cA.2 hmem
    have h2 : aP E ⟨_, hmem2⟩ P = E.L.one t := by
      rw [← aP_mul E cA ⟨_, hmem⟩ hmem2, h1, aP_one]
    rw [aP_mul E m e₁ (hΛ.mul_mem m.2 e₁.2), ← h2]
    apply aP_congr
    show (m : ℍ[ℚ, a, b]) * (((A * q : ℤ) : ℚ) : ℍ[ℚ, a, b]) = ((A : ℚ) : ℍ[ℚ, a, b]) * (((q : ℚ) : ℍ[ℚ, a, b]) * (m : ℍ[ℚ, a, b]))
    simp only [mul_coe_eq_smul, coe_mul_eq_smul, smul_smul]
    congr 1
    push_cast
    ring

  have hP₂ : ∀ m' : ↥Λ, PCond q (m' : ℍ[ℚ, a, b]) → aP E m' (aP E e₂ P) = E.L.one t := by
    intro m' hm'
    have := A1 e₂ (pcond_intCast_mul (a := a) (b := b) q' B); rw [kill_iff] at this
    exact this m' hm'

  intro m' hm'
  rw [kill_iff]
  intro m hm
  have hsplit : P = E.L.mul t (aP E e₁ P) (aP E e₂ P) := by
    rw [← aP_add, he, aP_unit]
  rw [hsplit, aP_hom, hP₂ m' hm', E.L.mul_one, aP_mul E m m' (hΛ.mul_mem m.2 m'.2)]
  rw [kill_iff] at hP₁
  exact hP₁ _ (pcond_mul hΛ q' hm m'.2)

theorem swap_iff (hΛ : IsOrder Λ) (q q' : ℕ) (hqq' : Nat.Coprime q q') (P : SchemeHomOver t E.f) :
    (∀ m : ↥Λ, PCond q' (m : ℍ[ℚ, a, b]) → Kill E q (aP E m P)) ↔
      (∀ m' : ↥Λ, PCond q (m' : ℍ[ℚ, a, b]) → Kill E q' (aP E m' P)) :=
  ⟨swap E hΛ q q' hqq' P, swap E hΛ q' q hqq'.symm P⟩

end Kernel

section Composite

variable {E E₁ E₁₂ : FakeEllipticCurve Λ N S}

theorem comp_eq_one_iff (r r' : ℕ)
    (φ₁ : E.A ⟶ E₁.A) (hφ₁ : φ₁ ≫ E₁.f = E.f) (φ₁₂ : E₁.A ⟶ E₁₂.A) (hφ₁₂ : φ₁₂ ≫ E₁₂.f = E₁.f)
    (hlin₁ : ∀ x : ↥Λ, E.act x ≫ φ₁ = φ₁ ≫ E₁.act x)
    (hker₁ : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of S)) (P : SchemeHomOver t E.f),
      mapPt φ₁ hφ₁ P = E₁.L.one t ↔ Kill E r P)
    (hker₁₂ : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of S)) (Q : SchemeHomOver t E₁.f),
      mapPt φ₁₂ hφ₁₂ Q = E₁₂.L.one t ↔ Kill E₁ r' Q)
    {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of S)) (P : SchemeHomOver t E.f) :
    mapPt (φ₁ ≫ φ₁₂) (by rw [Category.assoc, hφ₁₂, hφ₁]) P = E₁₂.L.one t ↔
      ∀ m : ↥Λ, PCond r' (m : ℍ[ℚ, a, b]) → Kill E r (aP E m P) := by
  have hc : mapPt (φ₁ ≫ φ₁₂) (by rw [Category.assoc, hφ₁₂, hφ₁]) P = mapPt φ₁₂ hφ₁₂ (mapPt φ₁ hφ₁ P) :=
    Subtype.ext (by simp only [mapPt_coe, Category.assoc])
  rw [hc, hker₁₂, kill_iff]
  refine forall_congr' fun m => forall_congr' fun _ => ?_
  have hl : aP E₁ m (mapPt φ₁ hφ₁ P) = mapPt φ₁ hφ₁ (aP E m P) :=
    Subtype.ext (by simp only [mapPt_coe, Category.assoc, hlin₁ m])
  rw [hl, hker₁]

end Composite

end ALComm

namespace ALComm

section ActNat

variable {S : Type u} [CommRing S] {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} {N : ℕ}
  (E : FakeEllipticCurve Λ N S) {T : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of S)}

theorem aP_natCast (hΛ : IsOrder Λ) (n : ℕ) (P : SchemeHomOver t E.f) :
    aP E ⟨((n : ℚ) : ℍ[ℚ, a, b]), natCast_mem hΛ n⟩ P = nsmulPt E.L t n P := by
  induction n with
  | zero =>
    have h0 : (⟨(((0 : ℕ) : ℚ) : ℍ[ℚ, a, b]), natCast_mem hΛ 0⟩ : ↥Λ) = 0 := Subtype.ext (by push_cast; rfl)
    rw [h0, aP_zero]; rfl
  | succ n ih =>
    have hs : (⟨(((n + 1 : ℕ) : ℚ) : ℍ[ℚ, a, b]), natCast_mem hΛ (n + 1)⟩ : ↥Λ) =
        ⟨((n : ℚ) : ℍ[ℚ, a, b]), natCast_mem hΛ n⟩ + ⟨1, hΛ.one_mem⟩ := Subtype.ext (by push_cast; rfl)
    rw [hs, aP_add, ih, aP_unit]; rfl

theorem comp_dual_eq_nsmul (hΛ : IsOrder Λ) {E₁ E₁₂ : FakeEllipticCurve Λ N S} (r r' : ℕ)
    (φ₁ : E.A ⟶ E₁.A) (hφ₁ : φ₁ ≫ E₁.f = E.f) (ψ₁ : E₁.A ⟶ E.A) (hψ₁ : ψ₁ ≫ E.f = E₁.f)
    (φ₁₂ : E₁.A ⟶ E₁₂.A) (hφ₁₂ : φ₁₂ ≫ E₁₂.f = E₁.f) (ψ₁₂ : E₁₂.A ⟶ E₁.A) (hψ₁₂ : ψ₁₂ ≫ E₁.f = E₁₂.f)
    (hlin₁ : ∀ x : ↥Λ, E.act x ≫ φ₁ = φ₁ ≫ E₁.act x)
    (hc₁ : φ₁ ≫ ψ₁ = E.act ⟨((r : ℚ) : ℍ[ℚ, a, b]), natCast_mem hΛ r⟩)
    (hc₁₂ : φ₁₂ ≫ ψ₁₂ = E₁.act ⟨((r' : ℚ) : ℍ[ℚ, a, b]), natCast_mem hΛ r'⟩)
    (P : SchemeHomOver t E.f) :
    mapPt (ψ₁₂ ≫ ψ₁) (by rw [Category.assoc, hψ₁, hψ₁₂])
      (mapPt (φ₁ ≫ φ₁₂) (by rw [Category.assoc, hφ₁₂, hφ₁]) P) = nsmulPt E.L t (r * r') P := by
  have hrr : (⟨((((r * r' : ℕ) : ℚ)) : ℍ[ℚ, a, b]), natCast_mem hΛ (r * r')⟩ : ↥Λ) =
      ⟨((r : ℚ) : ℍ[ℚ, a, b]) * ((r' : ℚ) : ℍ[ℚ, a, b]), hΛ.mul_mem (natCast_mem hΛ r) (natCast_mem hΛ r')⟩ :=
    Subtype.ext (by simp only [Nat.cast_mul, coe_mul])
  rw [← aP_natCast E hΛ, hrr]
  apply Subtype.ext
  simp only [mapPt_coe, Category.assoc]
  rw [← Category.assoc φ₁₂ ψ₁₂ ψ₁, hc₁₂, ← Category.assoc φ₁, ← hlin₁, Category.assoc, hc₁,
    E.act_mul ⟨((r : ℚ) : ℍ[ℚ, a, b]), natCast_mem hΛ r⟩ ⟨((r' : ℚ) : ℍ[ℚ, a, b]), natCast_mem hΛ r'⟩]

end ActNat

section More

variable {S : Type u} [CommRing S] {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} {N : ℕ}
  (E : FakeEllipticCurve Λ N S) {T : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of S)}

theorem aP_inv (m : ↥Λ) (P : SchemeHomOver t E.f) : aP E m (E.L.inv t P) = E.L.inv t (aP E m P) := by
  letI := E.L.pointGroup t
  have h : aP E m (E.L.inv t P) * aP E m P = 1 := by
    show E.L.mul t _ _ = E.L.one t
    rw [← aP_hom, E.L.inv_mul_cancel, aP_one]
  exact eq_inv_of_mul_eq_one_left h

theorem intCast_mul_mem (hΛ : IsOrder Λ) (z : ℤ) (m : ↥Λ) : (((z : ℚ)) : ℍ[ℚ, a, b]) * (m : ℍ[ℚ, a, b]) ∈ Λ :=
  hΛ.mul_mem (intCast_mem hΛ z) m.2

end More

end ALComm

namespace IsogFactorAux
variable {S : Type u} [CommRing S] {A A' : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of S)} {f' : A' ⟶ Spec (CommRingCat.of S)}
theorem mapPt_one (L : RelativeGroupLaw S f) (L' : RelativeGroupLaw S f') (φ : A ⟶ A') (hφ : φ ≫ f' = f)
    (hmul : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of S)) (P Q : SchemeHomOver t f),
      mapPt φ hφ (L.mul t P Q) = L'.mul t (mapPt φ hφ P) (mapPt φ hφ Q))
    {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of S)) : mapPt φ hφ (L.one t) = L'.one t := by
  set x := mapPt φ hφ (L.one t) with hx
  have hxx : L'.mul t x x = x := by rw [hx, ← hmul, L.one_mul]
  letI := L'.pointGroup t
  have h2 : x * x = x * 1 := by rw [mul_one]; exact hxx
  exact mul_left_cancel h2
end IsogFactorAux

namespace SubOnto

variable {S : Type u} [CommRing S]
variable {A A' : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of S)} {f' : A' ⟶ Spec (CommRingCat.of S)}

theorem onto (L : RelativeGroupLaw S f) (L' : RelativeGroupLaw S f') (φ : A ⟶ A') (hφ : φ ≫ f' = f)
    (hφmul : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of S)) (P Q : SchemeHomOver t f),
      mapPt φ hφ (L.mul t P Q) = L'.mul t (mapPt φ hφ P) (mapPt φ hφ Q))
    {C C' : Scheme.{u}} (ι : C ⟶ A) (ι' : C' ⟶ A') [IsClosedImmersion ι] [IsClosedImmersion ι']
    [IsFinite (ι ≫ f)] [Flat (ι ≫ f)] [LocallyOfFinitePresentation (ι ≫ f)]
    [IsFinite (ι' ≫ f')] [Flat (ι' ≫ f')] [LocallyOfFinitePresentation (ι' ≫ f')]
    (rk : ℕ) (hrk : ∀ s : ↥(Spec (CommRingCat.of S)), (ι ≫ f).finrank s = rk)
    (hrk' : ∀ s : ↥(Spec (CommRingCat.of S)), (ι' ≫ f').finrank s = rk)
    (hsub : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of S)) (P Q : SchemeHomOver t f),
      FactorsThrough ι P → FactorsThrough ι Q → FactorsThrough ι (L.mul t P (L.inv t Q)))
    (hdisj : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of S)) (P : SchemeHomOver t f),
      FactorsThrough ι P → mapPt φ hφ P = L'.one t → P = L.one t)
    (hcar : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of S)) (P : SchemeHomOver t f),
      FactorsThrough ι P → FactorsThrough ι' (mapPt φ hφ P)) :
    ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of S)) (Q : SchemeHomOver t f'),
      FactorsThrough ι' Q ↔ ∃ P : SchemeHomOver t f, FactorsThrough ι P ∧ mapPt φ hφ P = Q := by
  classical
  let P₀ : SchemeHomOver (ι ≫ f) f := ⟨ι, rfl⟩
  have hP₀ : FactorsThrough ι P₀ := ⟨𝟙 _, Category.id_comp _⟩
  obtain ⟨c, hc⟩ := hcar _ P₀ hP₀
  have hc' : c ≫ ι' = ι ≫ φ := by rw [hc]; rfl
  have hcomp' : c ≫ ι' ≫ f' = ι ≫ f := by rw [← Category.assoc, hc', Category.assoc, hφ]

  have hinj : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of S)) (P P' : SchemeHomOver t f),
      FactorsThrough ι P → FactorsThrough ι P' → mapPt φ hφ P = mapPt φ hφ P' → P = P' := by
    intro T t P P' hP hP' h
    letI := L.pointGroup t
    letI := L'.pointGroup t
    have hD : FactorsThrough ι (L.mul t P (L.inv t P')) := hsub t P P' hP hP'
    have hone : mapPt φ hφ (L.one t) = L'.one t := by
      set x := mapPt φ hφ (L.one t) with hx
      have hxx : L'.mul t x x = x := by rw [hx, ← hφmul, L.one_mul]
      have h2 : x * x = x * 1 := by rw [mul_one]; exact hxx
      exact mul_left_cancel h2
    let Φ : SchemeHomOver t f →* SchemeHomOver t f' :=
      { toFun := mapPt φ hφ, map_one' := hone, map_mul' := fun X Y => hφmul t X Y }
    have hΦD : Φ (P * P'⁻¹) = 1 := by
      rw [map_mul, map_inv, show Φ P = Φ P' from h, mul_inv_cancel]
    have h1 : P * P'⁻¹ = 1 := hdisj t _ hD hΦD
    exact mul_inv_eq_one.1 h1

  have hmono : Mono c := by
    refine ⟨fun {Z} u v huv => ?_⟩
    have hmE : Mono ι := ((IsClosedImmersion.iff_isFinite_and_mono ι).1 inferInstance).2
    rw [← cancel_mono ι]
    have ht : (v ≫ ι) ≫ f = (u ≫ ι) ≫ f := by
      have h1 : ∀ w : Z ⟶ C, (w ≫ ι) ≫ f = (w ≫ c) ≫ ι' ≫ f' := fun w => by
        simp only [Category.assoc, hcomp']
      rw [h1, h1, huv]
    have key := hinj ((u ≫ ι) ≫ f) ⟨u ≫ ι, rfl⟩ ⟨v ≫ ι, ht⟩ ⟨u, rfl⟩ ⟨v, rfl⟩
      (Subtype.ext (by
        simp only [mapPt_coe, Category.assoc]
        rw [← hc', ← Category.assoc, huv, Category.assoc]))
    exact congrArg Subtype.val key
  haveI : IsFinite (c ≫ (ι' ≫ f')) := by rw [hcomp']; infer_instance
  haveI : IsFinite c := IsFinite.of_comp c (ι' ≫ f')
  haveI : IsClosedImmersion c := (IsClosedImmersion.iff_isFinite_and_mono c).2 ⟨inferInstance, hmono⟩
  haveI : IsIso c := AlgebraicGeometry.isIso_of_isClosedImmersion_of_finrank_comp_eq c (ι' ≫ f') (ι ≫ f) hcomp'
    (fun s => by rw [hrk s, hrk' s])
  intro T t Q
  constructor
  · rintro ⟨Q₀, hQ₀⟩
    refine ⟨⟨Q₀ ≫ inv c ≫ ι, ?_⟩, ⟨Q₀ ≫ inv c, by simp only [Category.assoc]⟩, ?_⟩
    · simp only [Category.assoc]
      rw [← hcomp', IsIso.inv_hom_id_assoc, ← Category.assoc, hQ₀]
      exact Q.2
    · apply Subtype.ext
      simp only [mapPt_coe, Category.assoc]
      rw [← hc', IsIso.inv_hom_id_assoc, hQ₀]
  · rintro ⟨P, hP, rfl⟩
    exact hcar t P hP

end SubOnto

namespace Lift

theorem epi_pullback_fst {X Y T : Scheme.{u}} (g : X ⟶ Y) [Flat g] [Surjective g] [QuasiCompact g] (q : T ⟶ Y) :
    Epi (pullback.fst q g) := by
  haveI : Flat (pullback.fst q g) := MorphismProperty.pullback_fst _ _ inferInstance
  haveI : Surjective (pullback.fst q g) := MorphismProperty.pullback_fst _ _ inferInstance
  haveI : QuasiCompact (pullback.fst q g) := MorphismProperty.pullback_fst _ _ inferInstance
  infer_instance

end Lift

open ALComm in
theorem solution
    {N q q' : ℕ} [NeZero N] [Fact q.Prime] [Fact q'.Prime] (hqN : ¬ q ∣ N) (hq'N : ¬ q' ∣ N) (hqq' : q' ≠ q)
    {a b : ℚ} (hB : IsIndefiniteRamifiedExactlyAt a b q q')
    (Λ : Submodule ℤ ℍ[ℚ, a, b]) (hΛ : IsMaximalOrder Λ)
    (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓq : ℓ ≠ q) (hℓq' : ℓ ≠ q')
    (r : ℕ) (hr : r = q ∨ r = q')
    (u u' : QM.FakeEllipticCurve.WithExtraLevel Λ N ℓ (AlgebraicClosure ℚ))
    (d d' : QM.FakeEllipticCurve Λ N (AlgebraicClosure ℚ))
    (hud : QM.FakeEllipticCurve.IsLevelIsogeny ℓ u d)
    (huu' : QM.FakeEllipticCurve.WithExtraLevel.IsAtkinLehnerQuotient r u u')
    (hu'd' : QM.FakeEllipticCurve.IsLevelIsogeny ℓ u' d') :
    QM.FakeEllipticCurve.IsAtkinLehnerQuotient r d d' := by
  classical

  have hO : IsOrder Λ := hΛ.isOrder
  have hrp : r.Prime := by rcases hr with rfl | rfl <;> exact Fact.out
  have hrℓ : Nat.Coprime r ℓ := (Nat.coprime_primes hrp hℓ).mpr (by rcases hr with rfl | rfl <;> [exact hℓq.symm; exact hℓq'.symm])
  have hℓpos : 0 < ℓ := hℓ.pos
  have hrpos : 0 < r := hrp.pos
  have hrΛ : ((r : ℚ) : ℍ[ℚ, a, b]) ∈ Λ := natCast_mem hO r
  have hℓΛ : ((ℓ : ℚ) : ℍ[ℚ, a, b]) ∈ Λ := natCast_mem hO ℓ
  have hNk : (N : AlgebraicClosure ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne N)
  set k := AlgebraicClosure ℚ with hk
  obtain ⟨φd, hφd, ψd, hψd, mφd, mψd, lφd, lψd, cd, kd, vd⟩ := hud
  obtain ⟨φr, hφr, ψr, hψr, mφr, mψr, lφr, lψr, cr, kr, vr, wr⟩ := huu'
  obtain ⟨φd', hφd', ψd', hψd', mφd', mψd', lφd', lψd', cd', kd', vd'⟩ := hu'd'

  have one_natCast : ∀ (E₀ : FakeEllipticCurve Λ N k) (n : ℕ) (hn : ((n : ℚ) : ℍ[ℚ, a, b]) ∈ Λ)
      (θ : E₀.A ⟶ E₀.A) (hθ : θ = E₀.act ⟨((n : ℚ) : ℍ[ℚ, a, b]), hn⟩)
      {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of k)) (P : SchemeHomOver t E₀.f) (hθ' : θ ≫ E₀.f = E₀.f),
      mapPt θ hθ' P = nsmulPt E₀.L t n P := by
    intro E₀ n hn θ hθ T t P hθ'
    subst hθ
    have : (⟨((n : ℚ) : ℍ[ℚ, a, b]), hn⟩ : ↥Λ) = ⟨((n : ℚ) : ℍ[ℚ, a, b]), natCast_mem hO n⟩ := rfl
    exact aP_natCast E₀ hO n P
  have mc : ∀ {A B C : Scheme.{0}} {fA : A ⟶ Spec (CommRingCat.of k)} {fB : B ⟶ Spec (CommRingCat.of k)}
      {fC : C ⟶ Spec (CommRingCat.of k)} (θ : A ⟶ B) (hθ : θ ≫ fB = fA) (θ' : B ⟶ C) (hθ' : θ' ≫ fC = fB)
      (hθθ' : (θ ≫ θ') ≫ fC = fA) {T : Scheme.{0}} {t : T ⟶ Spec (CommRingCat.of k)} (P : SchemeHomOver t fA),
      mapPt (θ ≫ θ') hθθ' P = mapPt θ' hθ' (mapPt θ hθ P) := by
    intro A B C fA fB fC θ hθ θ' hθ' hθθ' T t P
    exact Subtype.ext (by simp only [mapPt_coe, Category.assoc])

  have Dd : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of k)) (P : SchemeHomOver t u.1.f),
      mapPt ψd hψd (mapPt φd hφd P) = nsmulPt u.1.L t ℓ P := by
    intro T t P
    rw [← mc φd hφd ψd hψd (by rw [Category.assoc, hψd, hφd])]
    exact one_natCast u.1 ℓ hℓΛ _ (cd hℓΛ).1 t P _
  have Dd' : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of k)) (Q : SchemeHomOver t d.f),
      mapPt φd hφd (mapPt ψd hψd Q) = nsmulPt d.L t ℓ Q := by
    intro T t Q
    rw [← mc ψd hψd φd hφd (by rw [Category.assoc, hφd, hψd])]
    exact one_natCast d ℓ hℓΛ _ (cd hℓΛ).2 t Q _
  have Ed : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of k)) (P : SchemeHomOver t u'.1.f),
      mapPt ψd' hψd' (mapPt φd' hφd' P) = nsmulPt u'.1.L t ℓ P := by
    intro T t P
    rw [← mc φd' hφd' ψd' hψd' (by rw [Category.assoc, hψd', hφd'])]
    exact one_natCast u'.1 ℓ hℓΛ _ (cd' hℓΛ).1 t P _
  have Ed' : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of k)) (Q : SchemeHomOver t d'.f),
      mapPt φd' hφd' (mapPt ψd' hψd' Q) = nsmulPt d'.L t ℓ Q := by
    intro T t Q
    rw [← mc ψd' hψd' φd' hφd' (by rw [Category.assoc, hφd', hψd'])]
    exact one_natCast d' ℓ hℓΛ _ (cd' hℓΛ).2 t Q _

  obtain ⟨sφd, fφd, flφd⟩ := CerednikDrinfeld.QM.surjective_and_isFinite_and_flat_of_mapPt_mapPt_eq_nsmulPt
    u.1.L u.1.comm u.1.bundle d.L d.comm d.bundle φd hφd mφd ψd hψd ℓ hℓpos Dd Dd'
  obtain ⟨sφd', fφd', flφd'⟩ := CerednikDrinfeld.QM.surjective_and_isFinite_and_flat_of_mapPt_mapPt_eq_nsmulPt
    u'.1.L u'.1.comm u'.1.bundle d'.L d'.comm d'.bundle φd' hφd' mφd' ψd' hψd' ℓ hℓpos Ed Ed'
  haveI := sφd; haveI := fφd; haveI := flφd; haveI := sφd'; haveI := fφd'; haveI := flφd'
  haveI : Epi φd := by haveI : EffectiveEpi φd := inferInstance; infer_instance
  haveI : Epi φd' := by haveI : EffectiveEpi φd' := inferInstance; infer_instance

  have hΦ : (φr ≫ φd') ≫ d'.f = u.1.f := by rw [Category.assoc, hφd', hφr]
  have MΦ : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of k)) (P Q : SchemeHomOver t u.1.f),
      mapPt (φr ≫ φd') hΦ (u.1.L.mul t P Q) = d'.L.mul t (mapPt (φr ≫ φd') hΦ P) (mapPt (φr ≫ φd') hΦ Q) := by
    intro T t P Q; rw [mc φr hφr φd' hφd', mc φr hφr φd' hφd', mc φr hφr φd' hφd', mφr, mφd']
  have LΦ : ∀ x : ↥Λ, u.1.act x ≫ (φr ≫ φd') = (φr ≫ φd') ≫ d'.act x := by
    intro x; rw [← Category.assoc, lφr, Category.assoc, lφd', Category.assoc]
  have hΨ : (ψd' ≫ ψr) ≫ u.1.f = d'.f := by rw [Category.assoc, hψr, hψd']
  have DΦ : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of k)) (P : SchemeHomOver t u.1.f),
      mapPt (ψd' ≫ ψr) hΨ (mapPt (φr ≫ φd') hΦ P) = nsmulPt u.1.L t (r * ℓ) P :=
    fun t P => comp_dual_eq_nsmul u.1 hO r ℓ φr hφr ψr hψr φd' hφd' ψd' hψd' lφr (cr hrΛ).1 (cd' hℓΛ).1 P
  have DΦ' : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of k)) (Q : SchemeHomOver t d'.f),
      mapPt (φr ≫ φd') hΦ (mapPt (ψd' ≫ ψr) hΨ Q) = nsmulPt d'.L t (r * ℓ) Q := by
    intro T t Q
    have := comp_dual_eq_nsmul d' hO ℓ r ψd' hψd' φd' hφd' ψr hψr φr hφr lψd' (cd' hℓΛ).2 (cr hrΛ).2 Q
    rwa [Nat.mul_comm] at this

  have hkerΦ : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of k)) (P : SchemeHomOver t u.1.f),
      mapPt φd hφd P = d.L.one t → mapPt (φr ≫ φd') hΦ P = d'.L.one t := by
    intro T t P hP
    rw [mc φr hφr φd' hφd', kd']
    exact wr t P ((kd t P).1 hP)

  obtain ⟨χ, hχ, hfac, -, χmul, χact, -⟩ :=
    CerednikDrinfeld.QM.FakeEllipticCurve.exists_unique_comp_eq_of_forall_mapPt_eq_one k u.1 d d'
      φd hφd mφd lφd ψd hψd ℓ hℓpos Dd Dd'
      (φr ≫ φd') hΦ MΦ LΦ (ψd' ≫ ψr) hΨ (r * ℓ) (Nat.mul_pos hrpos hℓpos) DΦ DΦ' hkerΦ

  haveI : IsClosedImmersion u.2.levK := u.2.levK_closed
  haveI : IsClosedImmersion u'.2.levK := u'.2.levK_closed
  haveI := u.2.levK_finite; haveI := u.2.levK_flat; haveI := u.2.levK_finitePresentation
  haveI := u'.2.levK_finite; haveI := u'.2.levK_flat; haveI := u'.2.levK_finitePresentation

  have hK_r : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of k)) (P : SchemeHomOver t u.1.f),
      mapPt φr hφr P = u'.1.L.one t → ∀ m : ↥Λ, PCond r (m : ℍ[ℚ, a, b]) → aP u.1 m P = u.1.L.one t := by
    intro T t P hP m hm; exact ((kill_iff u.1 r P).1 ((kr t P).1 hP)) m hm
  have hK_ℓ : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of k)) (P : SchemeHomOver t u.1.f),
      FactorsThrough u.2.levK P → aP u.1 ⟨((ℓ : ℚ) : ℍ[ℚ, a, b]), hℓΛ⟩ P = u.1.L.one t := by
    intro T t P hP
    have := aP_natCast u.1 hO ℓ P
    rw [u.2.levK_torsion t P hP] at this
    exact this
  obtain ⟨sB, tB, hst⟩ := hrℓ.isCoprime
  have hdisjK : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of k)) (P : SchemeHomOver t u.1.f),
      FactorsThrough u.2.levK P → mapPt φr hφr P = u'.1.L.one t → P = u.1.L.one t := by
    intro T t P hK hP
    have h1 : aP u.1 ⟨((r : ℚ) : ℍ[ℚ, a, b]), hrΛ⟩ P = u.1.L.one t := hK_r t P hP _ (pcond_natCast r)
    have h2 := hK_ℓ t P hK

    have e : (⟨1, hO.one_mem⟩ : ↥Λ) =
        ⟨(((sB : ℚ)) : ℍ[ℚ, a, b]) * ((r : ℚ) : ℍ[ℚ, a, b]), intCast_mul_mem hO sB ⟨_, hrΛ⟩⟩ +
        ⟨(((tB : ℚ)) : ℍ[ℚ, a, b]) * ((ℓ : ℚ) : ℍ[ℚ, a, b]), intCast_mul_mem hO tB ⟨_, hℓΛ⟩⟩ := by
      apply Subtype.ext
      show (1 : ℍ[ℚ, a, b]) = ((sB : ℚ) : ℍ[ℚ, a, b]) * ((r : ℚ) : ℍ[ℚ, a, b]) + ((tB : ℚ) : ℍ[ℚ, a, b]) * ((ℓ : ℚ) : ℍ[ℚ, a, b])
      rw [← coe_mul, ← coe_mul, ← coe_add, ← coe_one]; congr 1; exact_mod_cast hst.symm
    rw [← aP_unit u.1 hO.one_mem P, e, aP_add,
      ← aP_mul u.1 ⟨_, intCast_mem hO sB⟩ ⟨_, hrΛ⟩, h1, aP_one,
      ← aP_mul u.1 ⟨_, intCast_mem hO tB⟩ ⟨_, hℓΛ⟩, h2, aP_one, u.1.L.one_mul]
  have OK : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of k)) (Q : SchemeHomOver t u'.1.f),
      FactorsThrough u'.2.levK Q ↔ ∃ P : SchemeHomOver t u.1.f, FactorsThrough u.2.levK P ∧ mapPt φr hφr P = Q :=
    SubOnto.onto u.1.L u'.1.L φr hφr mφr u.2.levK u'.2.levK (ℓ ^ 2) u.2.levK_rank u'.2.levK_rank
      (fun t P Q hP hQ => (u.2.levK_sub t P (u.1.L.inv t Q) hP (u.2.levK_sub t Q Q hQ hQ).2).1)
      hdisjK wr

  have hΘ : (ψr ≫ φd) ≫ d.f = u'.1.f := by rw [Category.assoc, hφd, hψr]
  have MΘ : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of k)) (P Q : SchemeHomOver t u'.1.f),
      mapPt (ψr ≫ φd) hΘ (u'.1.L.mul t P Q) = d.L.mul t (mapPt (ψr ≫ φd) hΘ P) (mapPt (ψr ≫ φd) hΘ Q) := by
    intro T t P Q; rw [mc ψr hψr φd hφd, mc ψr hψr φd hφd, mc ψr hψr φd hφd, mψr, mφd]
  have LΘ : ∀ x : ↥Λ, u'.1.act x ≫ (ψr ≫ φd) = (ψr ≫ φd) ≫ d.act x := by
    intro x; rw [← Category.assoc, lψr, Category.assoc, lφd, Category.assoc]
  have hΘ' : (ψd ≫ φr) ≫ u'.1.f = d.f := by rw [Category.assoc, hφr, hψd]
  have DΘ : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of k)) (P : SchemeHomOver t u'.1.f),
      mapPt (ψd ≫ φr) hΘ' (mapPt (ψr ≫ φd) hΘ P) = nsmulPt u'.1.L t (r * ℓ) P :=
    fun t P => comp_dual_eq_nsmul u'.1 hO r ℓ ψr hψr φr hφr φd hφd ψd hψd lψr (cr hrΛ).2 (cd hℓΛ).1 P
  have DΘ' : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of k)) (Q : SchemeHomOver t d.f),
      mapPt (ψr ≫ φd) hΘ (mapPt (ψd ≫ φr) hΘ' Q) = nsmulPt d.L t (r * ℓ) Q := by
    intro T t Q
    have := comp_dual_eq_nsmul d hO ℓ r ψd hψd φd hφd φr hφr ψr hψr lψd (cd hℓΛ).2 (cr hrΛ).1 Q
    rwa [Nat.mul_comm] at this
  have hkerΘ : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of k)) (Q : SchemeHomOver t u'.1.f),
      mapPt φd' hφd' Q = d'.L.one t → mapPt (ψr ≫ φd) hΘ Q = d.L.one t := by
    intro T t Q hQ
    obtain ⟨P, hP, rfl⟩ := (OK t Q).1 ((kd' t Q).1 hQ)
    rw [mc ψr hψr φd hφd, ← mc φr hφr ψr hψr (by rw [Category.assoc, hψr, hφr])]
    have : mapPt (φr ≫ ψr) (by rw [Category.assoc, hψr, hφr]) P = aP u.1 ⟨((r : ℚ) : ℍ[ℚ, a, b]), hrΛ⟩ P :=
      Subtype.ext (by simp only [mapPt_coe, aP_coe, (cr hrΛ).1])
    rw [this, kd]
    exact u.2.levK_stable _ t P hP
  obtain ⟨ψ, hψ, hfac', -, ψmul, ψact, -⟩ :=
    CerednikDrinfeld.QM.FakeEllipticCurve.exists_unique_comp_eq_of_forall_mapPt_eq_one k u'.1 d' d
      φd' hφd' mφd' lφd' ψd' hψd' ℓ hℓpos Ed Ed'
      (ψr ≫ φd) hΘ MΘ LΘ (ψd ≫ φr) hΘ' (r * ℓ) (Nat.mul_pos hrpos hℓpos) DΘ DΘ' hkerΘ

  have KER : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of k)) (Q : SchemeHomOver t d.f),
      mapPt χ hχ Q = d'.L.one t ↔ Kill d r Q := by
    intro T t Q

    let p := pullback.fst Q.1 φd
    let Pl : SchemeHomOver (p ≫ t) u.1.f := ⟨pullback.snd Q.1 φd, by
      rw [← hφd, ← Category.assoc, ← pullback.condition, Category.assoc, Q.2]⟩
    haveI : Epi p := Lift.epi_pullback_fst φd Q.1
    have hlift : mapPt φd hφd Pl = schemeHomOverComp p rfl Q :=
      Subtype.ext (by rw [mapPt_coe, schemeHomOverComp_coe]; exact pullback.condition.symm)

    have test : ∀ {X : Scheme.{0}} {fX : X ⟶ Spec (CommRingCat.of k)} (R₁ R₂ : SchemeHomOver t fX),
        schemeHomOverComp p rfl R₁ = schemeHomOverComp p rfl R₂ → R₁ = R₂ := by
      intro X fX R₁ R₂ h
      apply Subtype.ext; rw [← cancel_epi p]
      have := congrArg Subtype.val h
      rwa [schemeHomOverComp_coe, schemeHomOverComp_coe] at this
    have hPl : Pl.1 ≫ φd = p ≫ Q.1 := pullback.condition.symm
    have hΦeq : ∀ {T : Scheme.{0}} {t : T ⟶ Spec (CommRingCat.of k)} (P : SchemeHomOver t u.1.f),
        mapPt (φr ≫ φd') hΦ P = mapPt χ hχ (mapPt φd hφd P) :=
      fun P => Subtype.ext (by simp only [mapPt_coe, Category.assoc, ← hfac])
    have e1 : ∀ m : ↥Λ, schemeHomOverComp p rfl (aP d m Q) = mapPt φd hφd (aP u.1 m Pl) := by
      intro m
      apply Subtype.ext
      simp only [schemeHomOverComp_coe, aP_coe, mapPt_coe, Category.assoc, lφd m]
      rw [← Category.assoc p, ← Category.assoc Pl.1, hPl]
    constructor
    ·
      intro hQ
      rw [kill_iff]
      intro m hm
      apply test
      rw [d.L.one_natural]
      rw [e1 m, kd]

      have hΦPl : mapPt (φr ≫ φd') hΦ Pl = d'.L.one (p ≫ t) := by
        rw [hΦeq, hlift]
        have : mapPt χ hχ (schemeHomOverComp p rfl Q) = schemeHomOverComp p rfl (mapPt χ hχ Q) :=
          Subtype.ext (by simp only [mapPt_coe, schemeHomOverComp_coe, Category.assoc])
        rw [this, hQ, d'.L.one_natural]

      have hK' : FactorsThrough u'.2.levK (mapPt φr hφr Pl) := by
        rw [← kd']; rw [← mc φr hφr φd' hφd']; exact hΦPl
      obtain ⟨P₁, hP₁K, hP₁⟩ := (OK _ _).1 hK'
      letI := u.1.L.pointGroup (p ≫ t); letI := u'.1.L.pointGroup (p ≫ t)
      let Φr : SchemeHomOver (p ≫ t) u.1.f →* SchemeHomOver (p ≫ t) u'.1.f :=
        { toFun := mapPt φr hφr, map_one' := IsogFactorAux.mapPt_one u.1.L u'.1.L φr hφr mφr _, map_mul' := fun X Y => mφr _ X Y }
      have hD : Φr (Pl * P₁⁻¹) = 1 := by rw [map_mul, map_inv, show Φr Pl = Φr P₁ from hP₁.symm, mul_inv_cancel]
      have hDm : aP u.1 m (Pl * P₁⁻¹) = 1 := hK_r _ _ hD m hm

      have : aP u.1 m Pl = aP u.1 m P₁ := by
        have h3 : aP u.1 m (Pl * P₁⁻¹) = aP u.1 m Pl * (aP u.1 m P₁)⁻¹ := by
          show aP u.1 m (u.1.L.mul _ Pl (u.1.L.inv _ P₁)) = u.1.L.mul _ (aP u.1 m Pl) (u.1.L.inv _ (aP u.1 m P₁))
          rw [aP_hom, aP_inv]
        rw [h3] at hDm
        exact mul_inv_eq_one.1 hDm
      rw [this]
      exact u.2.levK_stable m _ P₁ hP₁K
    ·
      intro hQ
      apply test
      rw [d'.L.one_natural]
      have e2 : schemeHomOverComp p rfl (mapPt χ hχ Q) = mapPt (φr ≫ φd') hΦ Pl := by
        rw [hΦeq, hlift]
        exact Subtype.ext (by simp only [mapPt_coe, schemeHomOverComp_coe, Category.assoc])
      rw [e2]

      have hQ' : ∀ m : ↥Λ, PCond r (m : ℍ[ℚ, a, b]) → FactorsThrough u.2.levK (aP u.1 m Pl) := by
        intro m hm
        rw [← kd, ← e1 m, (kill_iff d r Q).1 hQ m hm, d.L.one_natural]

      letI := u.1.L.pointGroup (p ≫ t); letI := d'.L.pointGroup (p ≫ t)
      let cr' : ↥Λ := ⟨((r : ℚ) : ℍ[ℚ, a, b]), hrΛ⟩
      let csr : ↥Λ := ⟨(((sB : ℚ)) : ℍ[ℚ, a, b]) * ((r : ℚ) : ℍ[ℚ, a, b]), intCast_mul_mem hO sB cr'⟩
      let k₀ := aP u.1 csr Pl
      have hk₀ : FactorsThrough u.2.levK k₀ := by
        show FactorsThrough u.2.levK (aP u.1 csr Pl)
        rw [← aP_mul u.1 ⟨_, intCast_mem hO sB⟩ cr']
        exact u.2.levK_stable _ _ _ (hQ' cr' (pcond_natCast r))
      have hfix : ∀ m : ↥Λ, PCond r (m : ℍ[ℚ, a, b]) → aP u.1 m k₀ = aP u.1 m Pl := by
        intro m hm

        have x_in_K := hQ' m hm
        have hcomm : aP u.1 m k₀ = aP u.1 csr (aP u.1 m Pl) := by
          show aP u.1 m (aP u.1 csr Pl) = aP u.1 csr (aP u.1 m Pl)
          rw [aP_mul u.1 m csr (hO.mul_mem m.2 csr.2), aP_mul u.1 csr m (hO.mul_mem csr.2 m.2)]
          apply aP_congr
          show (m : ℍ[ℚ, a, b]) * ((((sB : ℚ)) : ℍ[ℚ, a, b]) * ((r : ℚ) : ℍ[ℚ, a, b])) = ((((sB : ℚ)) : ℍ[ℚ, a, b]) * ((r : ℚ) : ℍ[ℚ, a, b])) * (m : ℍ[ℚ, a, b])
          rw [← coe_mul, coe_commutes]
        rw [hcomm]

        have e : csr = ⟨1, hO.one_mem⟩ + ⟨(((-tB : ℤ) : ℚ) : ℍ[ℚ, a, b]) * ((ℓ : ℚ) : ℍ[ℚ, a, b]), intCast_mul_mem hO (-tB) ⟨_, hℓΛ⟩⟩ := by
          apply Subtype.ext
          show ((((sB : ℚ)) : ℍ[ℚ, a, b]) * ((r : ℚ) : ℍ[ℚ, a, b])) = 1 + (((-tB : ℤ) : ℚ) : ℍ[ℚ, a, b]) * ((ℓ : ℚ) : ℍ[ℚ, a, b])
          have hstQ : (sB : ℚ) * (r : ℚ) + (tB : ℚ) * (ℓ : ℚ) = 1 := by exact_mod_cast hst
          rw [← coe_mul, ← coe_mul, ← coe_one, ← coe_add]; congr 1; push_cast; linarith [hstQ]
        rw [e, aP_add, aP_unit, ← aP_mul u.1 ⟨_, intCast_mem hO (-tB)⟩ ⟨_, hℓΛ⟩, hK_ℓ _ _ x_in_K, aP_one, u.1.L.mul_one]
      have hP₀ : ∀ m : ↥Λ, PCond r (m : ℍ[ℚ, a, b]) → aP u.1 m (Pl * k₀⁻¹) = 1 := by
        intro m hm
        show aP u.1 m (u.1.L.mul _ Pl (u.1.L.inv _ k₀)) = u.1.L.one _
        rw [aP_hom, aP_inv, hfix m hm]
        exact mul_inv_cancel (aP u.1 m Pl)
      have hφrP₀ : mapPt φr hφr (Pl * k₀⁻¹) = u'.1.L.one _ := (kr _ _).2 ((kill_iff u.1 r _).2 hP₀)
      let ΦΦ : SchemeHomOver (p ≫ t) u.1.f →* SchemeHomOver (p ≫ t) d'.f :=
        { toFun := mapPt (φr ≫ φd') hΦ, map_one' := IsogFactorAux.mapPt_one u.1.L d'.L _ hΦ MΦ _, map_mul' := fun X Y => MΦ _ X Y }
      have hΦP₀ : ΦΦ (Pl * k₀⁻¹) = 1 := by
        show mapPt (φr ≫ φd') hΦ (Pl * k₀⁻¹) = d'.L.one _
        rw [mc φr hφr φd' hφd', hφrP₀]
        exact IsogFactorAux.mapPt_one u'.1.L d'.L φd' hφd' mφd' _
      have hΦk₀ : ΦΦ k₀ = 1 := by
        show mapPt (φr ≫ φd') hΦ k₀ = d'.L.one _
        rw [mc φr hφr φd' hφd', kd']
        exact wr _ _ hk₀
      have : ΦΦ Pl = 1 := by
        have : Pl = Pl * k₀⁻¹ * k₀ := by rw [inv_mul_cancel_right]
        rw [this, map_mul, hΦP₀, hΦk₀, one_mul]
      exact this

  refine ⟨χ, hχ, ψ, hψ, χmul hχ, ψmul hψ, χact, ψact, ?comp, ?ker, ?lev⟩
  case comp =>
    intro hr'
    have e1 : (⟨((r : ℚ) : ℍ[ℚ, a, b]), hr'⟩ : ↥Λ) = ⟨((r : ℚ) : ℍ[ℚ, a, b]), hrΛ⟩ := rfl
    constructor
    · rw [← cancel_epi φd, ← Category.assoc, hfac, Category.assoc, hfac', ← Category.assoc, (cr hrΛ).1, lφd]
    · rw [← cancel_epi φd', ← Category.assoc, hfac', Category.assoc, hfac, ← Category.assoc, (cr hrΛ).2, lφd']
  case ker =>
    intro T t Q
    exact KER t Q
  case lev =>
    intro T t Q hQ
    have hinjd : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of k)) (P : SchemeHomOver t u.1.f),
        mapPt φd hφd P = d.L.one t → FactorsThrough u.1.lev P → P = u.1.L.one t :=
      fun t P h1 h2 => u.2.levK_disjoint t P ((kd t P).1 h1) h2
    obtain ⟨P, hP, rfl⟩ :=
      CerednikDrinfeld.QM.FakeEllipticCurve.exists_factorsThrough_lev_mapPt_eq_of_forall_eq_one k hNk u.1 d φd hφd mφd hinjd vd t Q hQ
    rw [← mc φd hφd χ hχ (by rw [Category.assoc, hχ, hφd])]
    have : mapPt (φd ≫ χ) (by rw [Category.assoc, hχ, hφd]) P = mapPt (φr ≫ φd') hΦ P :=
      Subtype.ext (by simp only [mapPt_coe, hfac])
    rw [this, mc φr hφr φd' hφd']
    exact vd' t _ (vr t P hP)

end
end S_CerednikDrinfeld_QM_FakeEllipticCurve_isAtkinLehnerQuotient_of_isLevelIsogeny_of_isLevelIsogeny
end P2MW
export P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_isAtkinLehnerQuotient_of_isLevelIsogeny_of_isLevelIsogeny (solution)
