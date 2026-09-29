-- Prove2me | solution 1 for CerednikDrinfeld.QM.FakeEllipticCurve.exists_tateModule_forall_generator_torsion_of_isMaximalOrder_of_prime
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.141142+00:00
-- url     : https://prove2.me/submissions/c34a42c9-0836-5ba0-8ce3-b927fafa9812

import Mathlib
import Definitions.Def_CerednikDrinfeld_QMModuli
import Definitions.Def_EllipticCurve_TateModule
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawAlgPointsV2
import Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_exists_generator_torsionPoints_of_isMaximalOrder_of_prime
import Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_pushPt_act_natCast_eq_nsmulPt
import Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_natCard_isTorsionPoint_eq_pow_of_natCast_ne_zero
import Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_smoothOfRelativeDimension_two
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_exists_tateModule_forall_generator_torsion_of_isMaximalOrder_of_prime
p2m_attr_erase "instance" "AlgebraicGeometry.Scheme.PresheafOfModules.symmetricCategory SheafOfModules.instFaithfulRingSheafPModToPMod SheafOfModules.symmetricCategory AlgebraicGeometry.Scheme.PresheafOfModules.monoidalCategory AlgebraicGeometry.Scheme.PresheafOfModules.monoidalClosed SheafOfModules.instFullRingSheafPModToPMod SheafOfModules.monoidalCategory AlgebraicGeometry.Scheme.Modules.symmetricCategory SheafOfModules.monoidalClosed SheafOfModules.instIsLocalizationPModRingSheafSheafifyFunctorPresheafW SheafOfModules.sheafifyFunctor_monoidal AlgebraicGeometry.Scheme.Modules.monoidalClosed AlgebraicGeometry.instMonoidalPresheafOfModulesModulesSheafify AlgebraicGeometry.Scheme.Modules.monoidalCategory PresheafOfModules.instMonoidalClosed PresheafOfModules.InternalHom.instModuleCarrierObjOppositeCommRingCatSubtypePiFamilyMemAddSubgroupNaturalFamilies PresheafOfModules.InternalHom.instModuleCarrierObjOppositeRingCatCompCommRingCatForget₂RingHomCarrierCarrierAbPresheaf PresheafOfModules.InternalHom.instSMulCarrierObjOppositeCommRingCatSubtypePiFamilyMemAddSubgroupNaturalFamilies AlgebraicGeometry.Scheme.Hom.opensMapFinal AlgebraicGeometry.RelPicard.RigidifiedLineBundle.setoid AlgebraicGeometry.RelPicard.RigidifiedLineBundle.instInhabited AlgebraicGeometry.OModulePresheaf.isScalarTower AlgebraicGeometry.Scheme.OrderedAffineCover.instLinearOrder AlgebraicGeometry.OModulePresheaf.module AlgebraicGeometry.Scheme.OrderedAffineCover.instFintype AlgebraicGeometry.Scheme.OrderedAffineCover.instFintypeIdx AlgebraicGeometry.OModulePresheaf.addCommGroup AlgebraicGeometry.Scheme.OrderedAffineCover.instDecidableEqIdx AlgebraicGeometry.OModulePresheaf.moduleSections TwoChartCech.Sections.M0_moduleA TwoChartCech.Sections.M1_module TwoChartCech.Cover.A01_algebra TwoChartCech.Cover.A0_algebra TwoChartCech.Cover.A1_commRing TwoChartCech.Cover.A1_algebra TwoChartCech.Sections.M01_module TwoChartCech.Sections.M0_addCommGroup TwoChartCech.Sections.M0_tower TwoChartCech.Sections.M01_addCommGroup TwoChartCech.Cover.A0_commRing"
p2m_attr_erase "instance" "TwoChartCech.Sections.M1_tower TwoChartCech.Sections.M01_moduleA TwoChartCech.Sections.M0_module TwoChartCech.Sections.M1_moduleA TwoChartCech.Sections.M1_addCommGroup TwoChartCech.Cover.A01_commRing TwoChartCech.Sections.M01_tower CoherentBaseChange.TwoTermComplex.C0_module CoherentBaseChange.TwoTermComplex.C0_addCommGroup CoherentBaseChange.TwoTermComplex.C1_module CoherentBaseChange.TwoTermComplex.C1_addCommGroup CoherentBaseChange.TwoTermComplex.C0_free CoherentBaseChange.TwoTermComplex.C1_finite CoherentBaseChange.TwoTermComplex.C0_finite CoherentBaseChange.TwoTermComplex.C1_free AlgebraicGeometry.OModulePresheaf.instSubsingletonObjZero AlgebraicGeometry.Scheme.Modules.preservesBinaryProducts_opensMap AlgebraicGeometry.Scheme.Modules.pullback_monoidal AlgebraicGeometry.Scheme.Modules.sheafify_isLocalization' AlgebraicGeometry.Scheme.Modules.preservesTerminal_opensMap AlgebraicGeometry.Scheme.Modules.pullback₀_monoidal AlgebraicGeometry.Scheme.Modules.preservesFiniteProducts_opensMap AlgebraicGeometry.Scheme.Modules.instLiftingPresheafOfModulesSheafifyPresheafWOpensCarrierCarrierCommRingCatGrothendieckTopologyObjFunctorOppositeIsSheafSheafCompPullback₀Pullback PresheafOfModules.PullbackMonoidal.pullback_monoidal PresheafOfModules.PullbackMonoidal.isIso_δ PresheafOfModules.pushforward_laxMonoidal PresheafOfModules.PullbackMonoidal.isIso_η PresheafOfModules.free_monoidal PresheafOfModules.restrictScalars_laxMonoidal PresheafOfModules.PullbackMonoidal.isIso_δ_gS PresheafOfModules.pullback_oplaxMonoidal PresheafOfModules.PullbackMonoidal.instPreservesColimitsOfSizeCompOppositeCommRingCatRingCatForget₂RingHomCarrierCarrierPb PresheafOfModules.pullback_monoidal' AlgebraicGeometry.SmoothOfRelativeDimension.fiberToSpecResidueField AlgebraicGeometry.SmoothOfRelativeDimension.pullback_snd AlgebraicGeometry.SmoothOfRelativeDimension.pullback_fst AlgebraicGeometry.SmoothOfRelativeDimension.smooth_one AlgebraicGeometry.SmoothProperCurve.isIntegral_pullback_Spec_field AlgebraicGeometry.IsProper.fiberToSpecResidueField AlgebraicCurve.CurveModel.isProper"
p2m_attr_erase "instance" "AlgebraicCurve.CurveModel.isIntegral AlgebraicCurve.CurveModel.smooth AlgebraicGeometry.Scheme.LocalRepresentabilityULift.instIsLocallyInjectiveFunUliftYonedaGluedToSheaf AlgebraicGeometry.Scheme.LocalRepresentabilityULift.instIsLocallySurjectiveFunUliftYonedaGluedToSheafOfIsLocallySurjectiveZariskiTopologyDescFunctorOppositeType AlgebraicGeometry.Scheme.LocalRepresentabilityULift.instIsOpenImmersionToGlued AlgebraicGeometry.Scheme.LocalRepresentabilityULift.instIsIsoSheafZariskiTopologyTypeUliftYonedaGluedToSheaf AlgebraicGeometry.RelPicard.instIsOpenImmersionToGlued AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.instFundamentalIdentityOfSumRamificationInertia AlgebraicCurve.Place.instIsScalarTowerResidueFieldRestrictPushforward AlgebraicCurve.Place.instAlgebraResidueFieldRestrictPushforward AlgebraicCurve.Place.instIsLocalHomRestrictInclusion AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions PresheafOfModules.ExteriorPower.instModulePresheafAb AlgebraicGeometry.RelEffCartierDiv.subsingleton_of_degree_zero AlgebraicGeometry.RelEffCartierDiv.isIso_subschemeIota_snd_of_degree_one AlgebraicGeometry.isIso_ker_graphOver_subschemeIota_snd AlgebraicGeometry.isClosedImmersion_graphOver AlgebraicGeometry.FGSubalgebra.instIsDirectedLe AlgebraicGeometry.FGSubalgebra.instQuasiSeparatedSpaceCarrierCarrierCommRingCatObjOppositeSchemeSpecDiagram AlgebraicGeometry.FGSubalgebra.instIsCofilteredOpposite AlgebraicGeometry.FGSubalgebra.instIsAffineObjOppositeSchemeSpecDiagram AlgebraicGeometry.FGSubalgebra.instNonempty AlgebraicGeometry.FGSubalgebra.instNonemptySubtypeLeSubalgebraValFG AlgebraicGeometry.FGSubalgebra.instCompactSpaceCarrierCarrierCommRingCatObjOppositeSchemeSpecDiagram AlgebraicGeometry.FGSubalgebra.instIsDirectedSubtypeLeSubalgebraValFG AlgebraicGeometry.FGSubalgebra.instIsAffineHomMapOppositeSchemeSpecDiagram AlgebraicGeometry.FGSubalgebra.instIsFiltered AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instNeg AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instSMulInt AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instAddCommGroup AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instAdd AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instSub AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instModuleCarrierObjOppositeOpensCarrierCarrierCommRingCatPresheafOpOpensTop"
p2m_attr_erase "instance" "AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instSMulCarrierObjOppositeOpensCarrierCarrierCommRingCatPresheafOpOpensTop AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instSMulNat AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instZero AlgebraicCurve.instHasLocalResidue_of_hasCanonicalLocalResidueK AlgebraicCurve.instHasCanonicalLocalResidueK_of_hasCanonicalLocalResidueKStar AlgebraicCurve.Place.kw_ffgc_finiteDimensional_adicCompletion instAlgebraSubtypeMemValuationSubring_definitions AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersIntegersCompletion ModularCurve.KwF4gRRTate.instAlgebraKAdicCompletionIntegers AlgebraicCurve.Place.kw_ffgc_continuousSMul_adicCompletionComap AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersCompletionCompletion IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions AlgebraicCurve.instHasCanonicalLocalResidueK AlgebraicCurve.Place.instAlgebra_restrictResidueField AlgebraicCurve.Place.instIsScalarTower_restrictResidueField AlgebraicCurve.instHasLocalResidue AlgebraicCurve.HasSeparableResidue.of_perfectField_of_isCurveOver AlgebraicCurve.HasSeparableResidue.of_perfectField AlgebraicCurve.Place.instIsLocalHom_restrictSubringHom AlgebraicCurve.instHasCanonicalLocalResidueKStar ModularCurve.KwNo6Pin.isLocalRing_completion SheafOfModules.isIso_ihomModelToIhom AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instDecidableEqIdx AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instFintype AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instLinearOrder AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instFintypeIdx AlgebraicGeometry.OModulePresheaf.Leray.relAltC_scalarTower AlgebraicGeometry.OModulePresheaf.Leray.ker_relAltd_modΓ AlgebraicGeometry.OModulePresheaf.Leray.relAltC_modΓ AlgebraicGeometry.OModulePresheaf.Leray.biC_abGrp AlgebraicGeometry.OModulePresheaf.Leray.relAltH_modΓ AlgebraicGeometry.OModulePresheaf.Leray.ker_relAltd_smul AlgebraicGeometry.OModulePresheaf.Leray.relAltH_scalarTower AlgebraicGeometry.OModulePresheaf.Leray.relAltH_smul AlgebraicGeometry.OModulePresheaf.Leray.biC_module"
p2m_attr_erase "instance" "DoubleComplex.instModuleE₂I DoubleComplex.Bounded.modR DoubleComplex.instModuleE₂II DoubleComplex.instAddCommGroupE₂II DoubleComplex.Bounded.abGrp DoubleComplex.instAddCommGroupE₂I AlgebraicGeometry.ChowDatum.hι_closed AlgebraicGeometry.ChowDatumProj.hιN_closed AlgebraicGeometry.ChowDatumProj.hp_proper AlgebraicGeometry.ChowDatum.hp_isoU AlgebraicGeometry.ChowDatum.hp_proper AlgebraicGeometry.ProjSpace.algebraAway AlgebraicGeometry.ProjSpace.instIsProperProdOverπ AlgebraicGeometry.ChowDatumProj.hp_isoU AlgebraicGeometry.ProjSpace.isProper_π AlgebraicGeometry.ProjSpace.finiteType_mvPolynomial ProjSpaceCech.GradedModule.H.module ProjSpaceCech.GradedModule.H.addCommGroup ProjSpaceCech.GradedModule.sec.instAdd ProjSpaceCech.GradedModule.sec.instNeg ProjSpaceCech.GradedModule.acg ProjSpaceCech.GradedModule.Frac.setoid ProjSpaceCech.GradedModule.modR ProjSpaceCech.GradedModule.sec.instModule ProjSpaceCech.GradedModule.sec.instAddCommGroup ProjSpaceCech.GradedModule.sec.instZero ProjSpaceCech.GradedModule.Presentation.fJ ProjSpaceCech.GradedModule.sec.instSMul ProjSpaceCech.Twist.H.module ProjSpaceCech.Idx.instFintype ProjSpaceCech.Twist.H.addCommGroup ProjSpaceCech.Idx.instDecidableEq ProjSpaceCech.Twist.Mon.instDecidableEq ProjSpaceCech.Twist.cochain.instAddCommGroup ProjSpaceCech.Twist.cochain.instModule AlgebraicGeometry.FGSubalgebra.tensorStage_directedSystem AlgebraicGeometry.RelEffCartierDiv.isClosedImmersion_subschemeι_resProdMap AlgebraicGeometry.RelEffCartierDiv.isOpenImmersion_resProdMap AlgebraicCurve.CurveModel.locallyOfFiniteType_gluedToBase AlgebraicCurve.CurveModel.isFractionRing_overlap"
p2m_attr_erase "instance" "AlgebraicCurve.CurveModel.isLocallyNoetherian_glued AlgebraicCurve.CurveModel.jacobsonSpace_glued AlgebraicCurve.CurveModel.isOpenImmersion_ι₀ AlgebraicCurve.CurveModel.isIntegral_glued AlgebraicCurve.CurveModel.quasiSeparated_gluedToBase AlgebraicCurve.CurveModel.compactSpace_glued AlgebraicCurve.CurveModel.isIntegral_adjoin_chartRing AlgebraicCurve.CurveModel.isFractionRing_overlap_functionField AlgebraicCurve.CurveModel.isProper_gluedToBase AlgebraicCurve.CurveModel.isOpenImmersion_ιU AlgebraicCurve.CurveModel.isOpenImmersion_f₀ AlgebraicCurve.CurveModel.isOpenImmersion_fInf AlgebraicCurve.CurveModel.isOpenImmersion_ιInf AlgebraicCurve.CurveModel.algebra_overlap_functionField AlgebraicCurve.CurveModel.quasiCompact_gluedToBase AlgebraicCurve.CurveModel.algebraAdjoin AlgebraicCurve.CurveModel.isDedekindDomain_chartRing AlgebraicCurve.CurveModel.isIntegralClosure AlgebraicCurve.CurveModel.finite_chartRing AlgebraicCurve.CurveModel.centre_isPrime AlgebraicCurve.CurveModel.isFractionRing_chartRing AlgebraicCurve.CurveModel.finiteType_chartRing AlgebraicCurve.CurveModel.isNoetherianRing_chartRing AlgebraicCurve.CurveModel.isScalarTower_base_adjoin AlgebraicCurve.CurveModel.isScalarTower_adjoin AlgebraicCurve.CurveModel.chartRing_finitePresentation instTopologicallyFGOfFiniteType AlgebraicGeometry.ProjSpace.twistObj.addCommGroup AlgebraicGeometry.ProjSpace.twistFam.module AlgebraicGeometry.ProjSpace.twistObj.module AlgebraicGeometry.ProjSpace.twistObj.moduleSections AlgebraicGeometry.ProjSpace.twistFam.addCommGroup"
p2m_attr_erase "simp" "GoodReductionJacobian.relativeGroupLawOfGrpObj_inv GoodReductionJacobian.relativeGroupLawOfGrpObj_mul GoodReductionJacobian.overHomEquivSchemeHomOver_apply_coe GoodReductionJacobian.relativeGroupLawOfGrpObj_one GoodReductionJacobian.overHomEquivSchemeHomOver_symm_apply_left SheafOfModules.tensorUnit_eq AlgebraicGeometry.Scheme.Modules.tensorUnit_eq PresheafOfModules.InternalHom.presheaf_map_apply PresheafOfModules.InternalHom.curryFamily_app PresheafOfModules.InternalHom.add_app PresheafOfModules.InternalHom.smul_app PresheafOfModules.InternalHom.zero_app PresheafOfModules.ihomObj_map_val PresheafOfModules.ihomFunctor_map PresheafOfModules.InternalHom.restrict_app PresheafOfModules.InternalHom.postcomp_app PresheafOfModules.InternalHom.neg_app PresheafOfModules.curry'_app_val PresheafOfModules.InternalHom.presheaf_obj PresheafOfModules.ihomFunctor_obj PresheafOfModules.ihomObj_obj PresheafOfModules.InternalHom.sub_app PresheafOfModules.ihomMap_app_val AlgebraicGeometry.Scheme.Modules.tensorPow_zero AlgebraicGeometry.Scheme.Modules.tensorPow_succ AlgebraicGeometry.RelPicard.RigidifiedLineBundle.mk.sizeOf_spec AlgebraicGeometry.RelPicard.RigidifiedLineBundle.mk.injEq AlgebraicGeometry.Scheme.OrderedAffineCover.mk.injEq AlgebraicGeometry.OModulePresheaf.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCover.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.mk.injEq AlgebraicGeometry.Scheme.TwoAffineOpenCover.mk.injEq AlgebraicGeometry.Scheme.TwoAffineOpenCover.mk.sizeOf_spec AlgebraicGeometry.Scheme.TwoAffineOpenCover.pullback_U1 AlgebraicGeometry.Scheme.TwoAffineOpenCover.pullback_U0 TwoChartCech.Sections.mk.injEq TwoChartCech.Cover.mk.injEq TwoChartCech.GrothendieckComplex.mk.injEq TwoChartCech.Sections.mk.sizeOf_spec TwoChartCech.Cover.mk.sizeOf_spec"
p2m_attr_erase "simp" "TwoChartCech.Cover.lineBundle_r0_apply TwoChartCech.GrothendieckComplex.mk.sizeOf_spec TwoChartCech.Cover.lineBundle_r1_apply CoherentBaseChange.TwoTermComplex.mk.sizeOf_spec CoherentBaseChange.TwoTermComplex.mk.injEq AlgebraicGeometry.OModulePresheaf.prod_obj AlgebraicGeometry.OModulePresheaf.restrOpen_obj AlgebraicGeometry.OModulePresheaf.DevissageStep.mk.injEq AlgebraicGeometry.OModulePresheaf.pushforward_obj AlgebraicGeometry.OModulePresheaf.im_obj AlgebraicGeometry.OModulePresheaf.pow_obj AlgebraicGeometry.OModulePresheaf.fstHom_app AlgebraicGeometry.OModulePresheaf.ker_obj AlgebraicGeometry.OModulePresheaf.coker_obj AlgebraicGeometry.OModulePresheaf.DevissageStep.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCover.preimage_U AlgebraicGeometry.OModulePresheaf.sndHom_app AlgebraicGeometry.OModulePresheaf.Hom.mk.injEq AlgebraicGeometry.OModulePresheaf.Hom.id_app AlgebraicGeometry.OModulePresheaf.AffHom.appSections_apply AlgebraicGeometry.OModulePresheaf.AffHom.comp_app AlgebraicGeometry.OModulePresheaf.AffSES.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.AffHom.kerMap_coe AlgebraicGeometry.OModulePresheaf.AffHom.id_app AlgebraicGeometry.OModulePresheaf.Hom.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.Hom.toAffHom_app AlgebraicGeometry.OModulePresheaf.SES.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.AffHom.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.Hom.comp_app AlgebraicGeometry.OModulePresheaf.SES.mk.injEq AlgebraicGeometry.OModulePresheaf.AffHom.mk.injEq AlgebraicGeometry.OModulePresheaf.Hom.appSections_apply AlgebraicGeometry.OModulePresheaf.AffSES.mk.injEq PresheafOfModules.freeεIso_hom_app PresheafOfModules.freeμIso_hom_app AlgebraicGeometry.RelPicard.RepresentsRelSubPic.mk.injEq AlgebraicGeometry.RelPicard.SubPicCondition.mk.injEq AlgebraicGeometry.RelPicard.SubPicCondition.mk.sizeOf_spec AlgebraicGeometry.RelPicard.RepresentsRelSubPic.mk.sizeOf_spec AlgebraicGeometry.SmoothProperCurve.sectionBaseChange_coe_snd"
p2m_attr_erase "simp" "AlgebraicGeometry.SmoothProperCurve.sectionBaseChange_coe_fst AlgebraicCurve.CurveModel.mk.injEq AlgebraicCurve.CurveModel.mk.sizeOf_spec AlgebraicCurve.mulAdele_apply AlgebraicCurve.residuePairing_apply_coe AlgebraicCurve.mem_adeleBdd AlgebraicCurve.weilSmul_one AlgebraicCurve.diagonalHom_apply AlgebraicCurve.weilSmul_apply AlgebraicCurve.adeleSpaceMul_coe AlgebraicCurve.mulAdele_one AlgebraicGeometry.SmoothProperCurve.FiniteMapData.twoAffineOpenCover_U1 AlgebraicGeometry.SmoothProperCurve.FiniteMapData.mk.injEq AlgebraicGeometry.SmoothProperCurve.FiniteMapData.mk.sizeOf_spec AlgebraicGeometry.SmoothProperCurve.FiniteMapData.twoAffineOpenCover_U0 AlgebraicGeometry.RelPicard.SubPicCondition.onClasses_mk AlgebraicGeometry.RelPicard.relSubPicPresheaf_map_coe CategoryTheory.Functor.OverTotal.ofFibre_fst CategoryTheory.Functor.overTotal_map_fst AlgebraicGeometry.Scheme.LocalRepresentabilityULift.glueData_J AlgebraicGeometry.Scheme.LocalRepresentabilityULift.uliftYoneda_toGlued_uliftYonedaGluedToSheaf AlgebraicGeometry.Scheme.LocalRepresentabilityULift.glueData_t' AlgebraicGeometry.Scheme.LocalRepresentabilityULift.uliftYoneda_toGlued_uliftYonedaGluedToSheaf_assoc AlgebraicGeometry.Scheme.LocalRepresentabilityULift.uliftYonedaGluedToSheaf_app_toGlued AlgebraicGeometry.Scheme.LocalRepresentabilityULift.glueData_openCover_map AlgebraicGeometry.Scheme.LocalRepresentabilityULift.uliftYonedaGluedToSheaf_app_comp AlgebraicGeometry.Scheme.LocalRepresentabilityULift.glueData_V AlgebraicGeometry.Scheme.LocalRepresentabilityULift.glueData_t AlgebraicGeometry.Scheme.LocalRepresentabilityULift.glueData_U AlgebraicGeometry.Scheme.LocalRepresentabilityULift.glueData_f AlgebraicGeometry.RelPicard.designationOfRepresentableBy_P AlgebraicGeometry.RelPicard.designationOfRepresentableBy_toBase AlgebraicGeometry.RelPicard.rigSection_snd AlgebraicGeometry.RelPicard.RigidifiedLineBundle.ofInvertible_L AlgebraicGeometry.RelPicard.rigSection_snd_assoc AlgebraicGeometry.RelPicard.SubPicGroupCondition.mk.injEq AlgebraicGeometry.RelPicard.SubPicGroupCondition.mk.sizeOf_spec AlgebraicCurve.coe_cechH0Equiv_apply AlgebraicCurve.cechH1ToH1_mk AlgebraicCurve.lSpaceOn_univ"
p2m_attr_erase "simp" "AlgebraicCurve.lSpaceOn_empty AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.Divisor.mapRestrict_single AlgebraicCurve.Divisor.pushforward_single AlgebraicCurve.Place.coe_restrictInclusion AlgebraicCurve.Place.mem_fiber AlgebraicCurve.Place.restrict_toValuationSubring AlgebraicCurve.Divisor.degree_pushforward AlgebraicCurve.Place.restrictResidueMap_residue AlgebraicCurve.Pic0.coe_pushforwardDegZeroHom AlgebraicCurve.Pic0.coe_pullbackDegZeroHom AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Divisor.degree_pushforwardAlong AlgebraicCurve.Pic0.coe_degZeroCorrespondence AlgebraicCurve.Place.mem_fiberAlong AlgebraicCurve.coe_frobeniusPushforwardDegZero"
p2m_attr_erase "simp" "AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.jqNModC_one ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one AlgebraicCurve.Place.differentialCoeff_zero AlgebraicCurve.Place.differentialCoeff_dCoord AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.injEq AlgebraicCurve.TranscendenceTower.mk.injEq AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec AlgebraicCurve.PoleDivisorPackage.mk.injEq AlgebraicGeometry.RelPicard.thetaBundle_def AlgebraicGeometry.RelPicard.picardBundle_def AlgebraicGeometry.RelEffCartierDiv.toRelEffDivisor_ofRelEffDivisor AlgebraicGeometry.RelEffCartierDiv.toRelEffDivisor_I AlgebraicGeometry.mapOnProdOver_fst_assoc AlgebraicGeometry.RelEffCartierDiv.mk.sizeOf_spec AlgebraicGeometry.RelEffCartierDiv.mk.injEq AlgebraicGeometry.mapOnProdOver_snd AlgebraicGeometry.mapOnProdOver_fst AlgebraicGeometry.mapOnProdOver_snd_assoc AlgebraicGeometry.mapOnProdOver_id AlgebraicCurve.RelEffDivisor.mk.sizeOf_spec AlgebraicCurve.mapOnProd_fst AlgebraicCurve.mapOnProd_fst_assoc AlgebraicCurve.mapOnProd_snd AlgebraicCurve.UnivDivisorPack.mk.injEq"
p2m_attr_erase "simp" "AlgebraicCurve.RelEffDivisor.mk.injEq AlgebraicCurve.UnivDivisorPack.mk.sizeOf_spec AlgebraicCurve.mapOnProd_snd_assoc AlgebraicGeometry.Scheme.Modules.exteriorPower_obj PresheafOfModules.exteriorPower_map_ιMulti PresheafOfModules.ExteriorPower.appₗ_apply AlgebraicGeometry.prodKerGraph_one AlgebraicGeometry.fibrePowOver.proj_comp AlgebraicGeometry.prodKerGraph_zero AlgebraicGeometry.RelEffCartierDiv.empty_I AlgebraicGeometry.fibrePowOver.proj_comp_assoc AlgebraicGeometry.graphOver_fst_assoc AlgebraicGeometry.RelEffCartierDiv.toPoint_comp AlgebraicGeometry.RelEffCartierDiv.toPoint_comp_assoc AlgebraicGeometry.graphOver_fst AlgebraicGeometry.RelEffCartierDiv.ofPoint_I AlgebraicGeometry.graphOver_snd AlgebraicGeometry.graphOver_snd_assoc AlgebraicCurve.SymmetricPowerPackage.mk.sizeOf_spec AlgebraicCurve.SymmetricPowerPackage.mk.injEq AlgebraicGeometry.FGSubalgebra.cocone_ι_app_apply AlgebraicGeometry.RelPicard.fst_toProdSpec AlgebraicGeometry.RelPicard.toProdSpec_fst_assoc AlgebraicGeometry.RelPicard.pointsSubBasepointModule_cons AlgebraicGeometry.RelPicard.pointsSubBasepointModule_nil AlgebraicGeometry.RelPicard.fst_toProdSpec_assoc AlgebraicGeometry.RelPicard.toProdSpec_fst AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.sub_app AlgebraicGeometry.Scheme.IdealSheafData.sres_sresTop AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.add_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.mk.sizeOf_spec AlgebraicGeometry.Scheme.IdealSheafData.coe_resLE AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.smul_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.coe_ofLE_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.ideal_range AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.zero_app AlgebraicGeometry.Scheme.IdealSheafData.sres_sres AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.comp_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.neg_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.id_app"
p2m_attr_erase "simp" "AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.coe_mulRight_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.nsmul_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.mk.injEq AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.zsmul_app AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.sizeOf_spec AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.injEq AlgebraicCurve.adeleSingle_coe AlgebraicCurve.kaehlerResidueTermKFam_apply AlgebraicCurve.Place.LocalResidueData.mk.injEq AlgebraicCurve.Place.LocalResidueData.mk.sizeOf_spec AlgebraicCurve.Place.kw_ffgc_adicCompletionComapIntegers_coe AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.sizeOf_spec AlgebraicCurve.Place.mem_simplePoleSubmodule AlgebraicCurve.Place.coe_uniformizerSubring ModularCurve.Lg37.Lg37CompletionSection.mk.injEq AlgebraicCurve.Place.CoefficientFieldSection.mk.injEq AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.injEq ModularCurve.Lg37.Lg37CompletionSection.mk.sizeOf_spec AlgebraicCurve.Place.CoefficientFieldSection.mk.sizeOf_spec AlgebraicCurve.Place.poleSubmodule_one AlgebraicCurve.Place.mem_poleSubmodule AlgebraicGeometry.Scheme.Modules.toUnitSection_ofUnitSection AlgebraicGeometry.Scheme.Modules.pullbackSection_def AlgebraicGeometry.Scheme.Modules.ofUnitSection_toUnitSection PresheafOfModules.InternalHom.IsSheafAux.appAt_toPresheafHom SheafOfModules.ihomSectionsEquivFamily_unit AlgebraicGeometry.Scheme.Modules.restrictHomEquivFamily_apply SheafOfModules.ihomEval_unit_app AlgebraicGeometry.Scheme.Modules.ihomEval_zero_right AlgebraicGeometry.Scheme.Modules.ihomEval_zero_left AlgebraicGeometry.Scheme.Modules.homOfFamily_app_apply SheafOfModules.unit_ihomSectionsEquivFamily AlgebraicGeometry.Scheme.Modules.familyOfHom_app AlgebraicGeometry.Scheme.Modules.restrictUnitIso_hom_app_apply AlgebraicGeometry.Scheme.Modules.restrictUnitIso_inv_app_apply AlgebraicGeometry.Scheme.Modules.restrictHomOfFamily_app_apply AlgebraicGeometry.Scheme.Modules.restrictHomEquivFamily_symm_apply AlgebraicGeometry.Scheme.Modules.tensorSections_zero_right AlgebraicGeometry.Scheme.Modules.map_unitSection AlgebraicGeometry.Scheme.Modules.tensorSectionsBilin_apply"
p2m_attr_erase "simp" "AlgebraicGeometry.Scheme.Modules.tensorPowSection_zero AlgebraicGeometry.Scheme.Modules.tensorSections_zero_left AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_neg AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_zero AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_sub AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_add AlgebraicGeometry.Scheme.OrderedAffineCover.toCoverOf_U AlgebraicGeometry.Scheme.OrderedAffineCoverOf.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCoverOf.mk.injEq AlgebraicGeometry.Scheme.OrderedAffineCover.restrict_U AlgebraicGeometry.OModulePresheaf.Leray.restrictToPreimage_U DoubleComplex.Bounded.mk.injEq DoubleComplex.Bounded.mk.sizeOf_spec DoubleComplex.Convergence.mk.injEq DoubleComplex.Convergence.mk.sizeOf_spec DoubleComplex.SubQuot.mk.sizeOf_spec DoubleComplex.SubQuot.mk.injEq AlgebraicGeometry.ChowDatumProj.mk.sizeOf_spec AlgebraicGeometry.ChowDatum.mk.sizeOf_spec AlgebraicGeometry.ChowDatumProj.mk.injEq AlgebraicGeometry.ChowDatum.mk.injEq ProjSpaceCech.GradedModule.mk.injEq ProjSpaceCech.GradedModule.mk.sizeOf_spec ProjSpaceCech.GradedModule.Frac.mk.sizeOf_spec ProjSpaceCech.GradedModule.Presentation.mk.injEq ProjSpaceCech.GradedModule.Frac.mk.injEq ProjSpaceCech.GradedModule.Presentation.mk.sizeOf_spec ProjSpaceCech.GradedModule.Hom.shift_toLinearMap ProjSpaceCech.GradedModule.Hom.mk.sizeOf_spec ProjSpaceCech.GradedModule.Hom.mk.injEq TwoChartCech.Mumford.dK_apply TwoChartCech.Mumford.ι0_apply TwoChartCech.Mumford.ι1_apply TwoChartCech.KerCoprod.dK_apply TwoChartCech.KerCoprod.ι1_apply TwoChartCech.KerCoprod.ι0_apply AlgebraicGeometry.tilde.functorCompPullbackSpecIso_app AlgebraicGeometry.RelPicard.algEquivZeroGroupCut_toSubPicCondition AlgebraicGeometry.RelPicard.LFP.stageHom_val AlgebraicGeometry.RelPicard.BaseChange.relSubPicPresheafRestrictIso_hom_app_coe"
p2m_attr_erase "simp" "AlgebraicGeometry.RelPicard.BaseChange.relSubPicPresheafRestrictIso_inv_app_coe AlgebraicGeometry.RelPicard.BaseChange.restrict_P AlgebraicGeometry.RelEffCartierDiv.IsUniversal.lift_comp AlgebraicGeometry.RelEffCartierDiv.functor_map_fst AlgebraicGeometry.RelEffCartierDiv.IsUniversal.homEquiv_apply AlgebraicGeometry.RelEffCartierDiv.IsUniversal.lift_pullbackAlong AlgebraicGeometry.RelEffCartierDiv.IsUniversal.homEquiv_symm_apply AlgebraicGeometry.RelEffCartierDiv.IsUniversal.lift_comp_assoc AlgebraicGeometry.RelEffCartierDiv.supportedIn_top AlgebraicGeometry.RelEffCartierDiv.mem_supportedIn_iff AlgebraicGeometry.RelEffCartierDiv.supportedIn_top_eq AlgebraicGeometry.RelEffCartierDiv.restrictAlong_extendAlong AlgebraicGeometry.RelEffCartierDiv.extendAlong_I AlgebraicGeometry.RelEffCartierDiv.resProdMap_snd AlgebraicGeometry.RelEffCartierDiv.restrictAlong_I AlgebraicGeometry.RelEffCartierDiv.extendAlong_restrictAlong AlgebraicGeometry.RelEffCartierDiv.resProdMap_fst_assoc AlgebraicGeometry.RelEffCartierDiv.resProdMap_snd_assoc AlgebraicGeometry.RelEffCartierDiv.resProdMap_fst CoherentBaseChange.FibreH0Family.mk.sizeOf_spec CoherentBaseChange.FibreH0Family.mk.injEq AlgebraicGeometry.Scheme.Modules.ProjPresentation.mk.injEq AlgebraicGeometry.Scheme.Modules.ProjPresentation.mk.sizeOf_spec AlgebraicCurve.CurveModel.coe_gInf AlgebraicCurve.CurveModel.coe_tInvChart AlgebraicCurve.CurveModel.ιInf_gluedToBase_assoc AlgebraicCurve.CurveModel.ιInf_gluedToBase AlgebraicCurve.CurveModel.primeOfι₀_asIdeal AlgebraicCurve.CurveModel.coe_tChart AlgebraicCurve.CurveModel.ι₀_gluedToBase_assoc AlgebraicCurve.CurveModel.primeOfιInf_asIdeal AlgebraicCurve.CurveModel.ι₀_gluedToBase AlgebraicCurve.CurveModel.coe_tma AlgebraicCurve.CurveModel.coe_primeEquivChartPlaces RegularLocalRingQuotientAscent.dualNumberFst_apply AlgebraicGeometry.ProjSpace.twistObj.mk.injEq AlgebraicGeometry.ProjSpace.twistObj.zero_val AlgebraicGeometry.ProjSpace.twistObj.add_val AlgebraicGeometry.ProjSpace.twist_res_val AlgebraicGeometry.ProjSpace.twist_smul_val"
p2m_attr_erase "simp" "AlgebraicGeometry.ProjSpace.twistGradeToObj_val AlgebraicGeometry.ProjSpace.twistObj.smul_val AlgebraicGeometry.ProjSpace.twistGradeEquiv_apply_val AlgebraicGeometry.ProjSpace.twistObj.mk.sizeOf_spec QuaternionAlgebra.baseChangeRight_tmul QuaternionAlgebra.mapOfAlgebraMapEq_apply QuaternionAlgebra.baseChange_tmul QuaternionAlgebra.ClassSet.map_mk"

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry NeronModelInfra GoodReductionJacobian CerednikDrinfeld CerednikDrinfeld.QM QuaternionAlgebra

open scoped Quaternion

noncomputable section

namespace P2mKcTateRankOnePrime

section General

variable {R : Type} [CommRing R] {A : Scheme.{0}} {f : A ⟶ Spec (CommRingCat.of R)}

theorem nsmulPt_eq_nsmul (L : RelativeGroupLaw R f) {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of R))
    (n : ℕ) (P : SchemeHomOver t f) : nsmulPt L t n P = L.nsmul t n P := by
  induction n with
  | zero => rfl
  | succ n ih => rw [RelativeGroupLaw.nsmul_succ, ← ih]; rfl

theorem mapPt_comp {A' A'' : Scheme.{0}} {f' : A' ⟶ Spec (CommRingCat.of R)} {f'' : A'' ⟶ Spec (CommRingCat.of R)}
    (φ : A ⟶ A') (hφ : φ ≫ f' = f) (ψ : A' ⟶ A'') (hψ : ψ ≫ f'' = f')
    (h : (φ ≫ ψ) ≫ f'' = f) {T : Scheme.{0}} {t : T ⟶ Spec (CommRingCat.of R)} (P : SchemeHomOver t f) :
    mapPt (φ ≫ ψ) h P = mapPt ψ hψ (mapPt φ hφ P) := by
  apply Subtype.ext
  simp only [mapPt_coe, Category.assoc]

end General

theorem specMap_algebraMap_self (K : Type) [Field K] :
    Spec.map (CommRingCat.ofHom (algebraMap K K)) = 𝟙 (Spec (CommRingCat.of K)) := by
  rw [Algebra.algebraMap_self, CommRingCat.ofHom_id]; exact Spec.map_id _

theorem cancel_natCast {a b : ℚ} {n : ℕ} (hn : n ≠ 0) {u v : ℍ[ℚ, a, b]}
    (h : ((n : ℚ) : ℍ[ℚ, a, b]) * u = ((n : ℚ) : ℍ[ℚ, a, b]) * v) : u = v := by
  rw [QuaternionAlgebra.coe_mul_eq_smul, QuaternionAlgebra.coe_mul_eq_smul] at h
  exact smul_right_injective ℍ[ℚ, a, b] (Nat.cast_ne_zero.mpr hn : (n : ℚ) ≠ 0) h

section Main

variable {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} {N : ℕ}
  {K : Type} [Field K] [IsAlgClosed K] (E : FakeEllipticCurve Λ N K)

abbrev tK (K : Type) [Field K] : Spec (CommRingCat.of K) ⟶ Spec (CommRingCat.of K) :=
  Spec.map (CommRingCat.ofHom (algebraMap K K))

abbrev actP (E : FakeEllipticCurve Λ N K) (m : ↥Λ) (P : SchemeHomOver (tK K) E.f) : SchemeHomOver (tK K) E.f :=
  pushPt (E.act m) (E.act_over m) P

omit [IsAlgClosed K] in
theorem actP_mul (m : ↥Λ) (P Q : SchemeHomOver (tK K) E.f) :
    actP E m (E.L.mul (tK K) P Q) = E.L.mul (tK K) (actP E m P) (actP E m Q) :=
  E.act_hom m (tK K) P Q

omit [IsAlgClosed K] in

theorem actP_mul_elem (x y : ↥Λ) (hxy : (x : ℍ[ℚ, a, b]) * y ∈ Λ) (P : SchemeHomOver (tK K) E.f) :
    actP E ⟨(x : ℍ[ℚ, a, b]) * y, hxy⟩ P = actP E x (actP E y P) := by
  show pushPt (E.act ⟨(x : ℍ[ℚ, a, b]) * y, hxy⟩) (E.act_over _) P = _
  have hact := E.act_mul x y hxy
  have hover : (E.act y ≫ E.act x) ≫ E.f = E.f := by rw [Category.assoc, E.act_over, E.act_over]
  have : pushPt (E.act ⟨(x : ℍ[ℚ, a, b]) * y, hxy⟩) (E.act_over _) P =
      mapPt (E.act y ≫ E.act x) hover P := by
    apply Subtype.ext
    simp only [mapPt_coe, hact]
  rw [this]
  exact mapPt_comp (E.act y) (E.act_over y) (E.act x) (E.act_over x) hover P

omit [IsAlgClosed K] in

theorem actP_congr {x y : ↥Λ} (h : (x : ℍ[ℚ, a, b]) = y) (P : SchemeHomOver (tK K) E.f) :
    actP E x P = actP E y P := by
  have : x = y := Subtype.ext h
  subst this; rfl

abbrev actM (E : FakeEllipticCurve Λ N K) (m : ↥Λ) (x : E.L.AlgPoints E.comm K) : E.L.AlgPoints E.comm K :=
  RelativeGroupLaw.AlgPoints.ofPoint (hc := E.comm) (actP E m (RelativeGroupLaw.AlgPoints.toPoint (hc := E.comm) x))

omit [IsAlgClosed K] in
theorem toPoint_actM (m : ↥Λ) (x : E.L.AlgPoints E.comm K) :
    RelativeGroupLaw.AlgPoints.toPoint (actM E m x) = actP E m (RelativeGroupLaw.AlgPoints.toPoint x) := rfl

omit [IsAlgClosed K] in
theorem actM_mul_elem (x y : ↥Λ) (hxy : (x : ℍ[ℚ, a, b]) * y ∈ Λ) (P : E.L.AlgPoints E.comm K) :
    actM E ⟨(x : ℍ[ℚ, a, b]) * y, hxy⟩ P = actM E x (actM E y P) := by
  apply RelativeGroupLaw.AlgPoints.toPoint_injective
  rw [toPoint_actM, toPoint_actM, toPoint_actM, actP_mul_elem]

omit [IsAlgClosed K] in
theorem actM_congr {x y : ↥Λ} (h : (x : ℍ[ℚ, a, b]) = y) (P : E.L.AlgPoints E.comm K) :
    actM E x P = actM E y P := by
  have : x = y := Subtype.ext h
  subst this; rfl

omit [IsAlgClosed K] in
theorem actM_eq_zero_iff (m : ↥Λ) (x : E.L.AlgPoints E.comm K) :
    actM E m x = 0 ↔ actP E m (RelativeGroupLaw.AlgPoints.toPoint x) = E.L.one (tK K) := by
  constructor
  · intro h
    have := congrArg RelativeGroupLaw.AlgPoints.toPoint h
    rwa [toPoint_actM, RelativeGroupLaw.AlgPoints.toPoint_zero] at this
  · intro h
    apply RelativeGroupLaw.AlgPoints.toPoint_injective
    rw [toPoint_actM, h, RelativeGroupLaw.AlgPoints.toPoint_zero]

omit [IsAlgClosed K] in
theorem nsmul_eq_zero_iff' (n : ℕ) (x : E.L.AlgPoints E.comm K) :
    n • x = 0 ↔ E.L.nsmul (tK K) n (RelativeGroupLaw.AlgPoints.toPoint x) = E.L.one (tK K) :=
  RelativeGroupLaw.AlgPoints.nsmul_eq_zero_iff n x

theorem natCard_torsion_of_eq (t : Spec (CommRingCat.of K) ⟶ Spec (CommRingCat.of K)) (ht : t = 𝟙 _)
    (n : ℕ) (hnK : (n : K) ≠ 0) :
    Nat.card {x : SchemeHomOver t E.f // E.L.IsTorsionPoint t n x} = n ^ (2 * 2) := by
  subst ht
  haveI := FakeEllipticCurve.smoothOfRelativeDimension_two K E
  exact RelativeGroupLaw.natCard_isTorsionPoint_eq_pow_of_natCast_ne_zero K E.f E.L E.comm E.bundle 2 n hnK

theorem finite_torsion (n : ℕ) (hnK : (n : K) ≠ 0) : Finite {x : E.L.AlgPoints E.comm K // n • x = 0} := by
  have hcard := natCard_torsion_of_eq E (tK K) (specMap_algebraMap_self K) n hnK
  have hfin : Finite {x : SchemeHomOver (tK K) E.f // E.L.IsTorsionPoint (tK K) n x} := by
    apply Nat.finite_of_card_ne_zero
    rw [hcard]
    exact pow_ne_zero _ (fun h => hnK (by rw [h, Nat.cast_zero]))
  let e : {x : E.L.AlgPoints E.comm K // n • x = 0} →
      {x : SchemeHomOver (tK K) E.f // E.L.IsTorsionPoint (tK K) n x} :=
    fun x => ⟨RelativeGroupLaw.AlgPoints.toPoint x.1, (RelativeGroupLaw.AlgPoints.nsmul_eq_zero_iff n x.1).1 x.2⟩
  have he : Function.Injective e := by
    intro x y h
    apply Subtype.ext
    apply RelativeGroupLaw.AlgPoints.toPoint_injective
    exact congrArg (fun z => z.1) h
  exact Finite.of_injective e he

omit [IsAlgClosed K] in

theorem actM_add (m : ↥Λ) (x y : E.L.AlgPoints E.comm K) : actM E m (x + y) = actM E m x + actM E m y := by
  apply RelativeGroupLaw.AlgPoints.toPoint_injective
  rw [toPoint_actM, RelativeGroupLaw.AlgPoints.toPoint_add, RelativeGroupLaw.AlgPoints.toPoint_add, toPoint_actM,
    toPoint_actM]
  exact actP_mul E m _ _

def actHom (E : FakeEllipticCurve Λ N K) (m : ↥Λ) : E.L.AlgPoints E.comm K →+ E.L.AlgPoints E.comm K :=
  AddMonoidHom.mk' (actM E m) (actM_add E m)

omit [IsAlgClosed K] in
theorem actHom_apply (m : ↥Λ) (x : E.L.AlgPoints E.comm K) : actHom E m x = actM E m x := rfl

omit [IsAlgClosed K] in
theorem actM_zero (m : ↥Λ) : actM E m (0 : E.L.AlgPoints E.comm K) = 0 := by
  rw [← actHom_apply]; exact (actHom E m).map_zero

omit [IsAlgClosed K] in

theorem actM_nsmul (m : ↥Λ) (n : ℕ) (x : E.L.AlgPoints E.comm K) : actM E m (n • x) = n • actM E m x := by
  rw [← actHom_apply, ← actHom_apply]; exact map_nsmul (actHom E m) n x

omit [IsAlgClosed K] in

theorem actM_add_elem (x y : ↥Λ) (P : E.L.AlgPoints E.comm K) : actM E (x + y) P = actM E x P + actM E y P := by
  apply RelativeGroupLaw.AlgPoints.toPoint_injective
  rw [toPoint_actM, RelativeGroupLaw.AlgPoints.toPoint_add, toPoint_actM, toPoint_actM]
  exact E.act_add x y (tK K) _

theorem natCard_torsion (n : ℕ) (hnK : (n : K) ≠ 0) : Nat.card {x : E.L.AlgPoints E.comm K // n • x = 0} = n ^ 4 := by
  have hcard := natCard_torsion_of_eq E (tK K) (specMap_algebraMap_self K) n hnK
  rw [show (2 * 2 : ℕ) = 4 from rfl] at hcard
  rw [← hcard]
  apply Nat.card_congr
  exact
    { toFun := fun x => ⟨RelativeGroupLaw.AlgPoints.toPoint x.1, (RelativeGroupLaw.AlgPoints.nsmul_eq_zero_iff n x.1).1 x.2⟩
      invFun := fun y => ⟨RelativeGroupLaw.AlgPoints.ofPoint (hc := E.comm) y.1,
        (RelativeGroupLaw.AlgPoints.nsmul_eq_zero_iff n _).2 y.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }

variable (hΛ : IsMaximalOrder Λ)
include hΛ

omit [IsAlgClosed K] E in
private theorem _root_.P2mKcTateRankOnePrime.one_mem : (1 : ℍ[ℚ, a, b]) ∈ Λ := hΛ.isOrder.one_mem

p2m_export "P2mKcTateRankOnePrime" "one_mem"
omit [IsAlgClosed K] E in
theorem natCast_mem (n : ℕ) : ((n : ℚ) : ℍ[ℚ, a, b]) ∈ Λ := by
  rw [QuaternionAlgebra.coe_natCast, ← nsmul_one]
  exact nsmul_mem hΛ.isOrder.one_mem n

omit [IsAlgClosed K] E in
private theorem _root_.P2mKcTateRankOnePrime.mul_mem (x y : ↥Λ) : (x : ℍ[ℚ, a, b]) * (y : ℍ[ℚ, a, b]) ∈ Λ :=
  hΛ.isOrder.mul_mem x.2 y.2

p2m_export "P2mKcTateRankOnePrime" "mul_mem"
omit [IsAlgClosed K] E in
theorem natCast_mul_mem (n : ℕ) (m : ↥Λ) : ((n : ℚ) : ℍ[ℚ, a, b]) * (m : ℍ[ℚ, a, b]) ∈ Λ :=
  hΛ.isOrder.mul_mem (natCast_mem hΛ n) m.2

omit [IsAlgClosed K] E in
theorem mul_natCast_mem (n : ℕ) (m : ↥Λ) : (m : ℍ[ℚ, a, b]) * ((n : ℚ) : ℍ[ℚ, a, b]) ∈ Λ :=
  hΛ.isOrder.mul_mem m.2 (natCast_mem hΛ n)

omit [IsAlgClosed K] in

theorem actP_natCast (n : ℕ) (P : SchemeHomOver (tK K) E.f) :
    actP E ⟨((n : ℚ) : ℍ[ℚ, a, b]), natCast_mem hΛ n⟩ P = E.L.nsmul (tK K) n P := by
  rw [← nsmulPt_eq_nsmul]
  exact E.pushPt_act_natCast_eq_nsmulPt (one_mem hΛ) n (natCast_mem hΛ n) (tK K) P

omit [IsAlgClosed K] in

theorem actM_natCast (n : ℕ) (x : E.L.AlgPoints E.comm K) :
    actM E ⟨((n : ℚ) : ℍ[ℚ, a, b]), natCast_mem hΛ n⟩ x = n • x := by
  apply RelativeGroupLaw.AlgPoints.toPoint_injective
  rw [toPoint_actM, actP_natCast E hΛ, RelativeGroupLaw.AlgPoints.toPoint_nsmul]

omit [IsAlgClosed K] in

theorem actM_natCast_mul (n : ℕ) (m : ↥Λ) (x : E.L.AlgPoints E.comm K) :
    actM E ⟨((n : ℚ) : ℍ[ℚ, a, b]) * m, natCast_mul_mem hΛ n m⟩ x = n • actM E m x := by
  rw [actM_mul_elem E ⟨((n : ℚ) : ℍ[ℚ, a, b]), natCast_mem hΛ n⟩ m, actM_natCast E hΛ]

omit [IsAlgClosed K] in

theorem actM_mul_natCast (n : ℕ) (m : ↥Λ) (x : E.L.AlgPoints E.comm K) :
    actM E ⟨(m : ℍ[ℚ, a, b]) * ((n : ℚ) : ℍ[ℚ, a, b]), mul_natCast_mem hΛ n m⟩ x = actM E m (n • x) := by
  rw [actM_mul_elem E m ⟨((n : ℚ) : ℍ[ℚ, a, b]), natCast_mem hΛ n⟩, actM_natCast E hΛ]

theorem torsStruct_prime_of_eq {q q' : ℕ} [Fact q.Prime] [Fact q'.Prime] (hB : IsIndefiniteRamifiedExactlyAt a b q q')
    (t : Spec (CommRingCat.of K) ⟶ Spec (CommRingCat.of K)) (ht : t = 𝟙 _)
    (ℓ : ℕ) [Fact ℓ.Prime] (hℓK : (ℓ : K) ≠ 0) :
    ∃ P₀ : SchemeHomOver t E.f,
      E.L.nsmul t ℓ P₀ = E.L.one t ∧
      (∀ P : SchemeHomOver t E.f, E.L.nsmul t ℓ P = E.L.one t →
        ∃ m : ↥Λ, P = pushPt (E.act m) (E.act_over m) P₀) ∧
      (∀ m : ↥Λ, pushPt (E.act m) (E.act_over m) P₀ = E.L.one t ↔
        ∃ m' : ↥Λ, (m : ℍ[ℚ, a, b]) = ((ℓ : ℚ) : ℍ[ℚ, a, b]) * (m' : ℍ[ℚ, a, b])) := by
  subst ht
  obtain ⟨P₀, h1, h2, h3⟩ :=
    FakeEllipticCurve.exists_generator_torsionPoints_of_isMaximalOrder_of_prime hB Λ hΛ K E ℓ hℓK
  refine ⟨P₀, ?_, ?_, h3⟩
  · rw [← nsmulPt_eq_nsmul]; exact h1
  · intro P hP
    rw [← nsmulPt_eq_nsmul] at hP
    exact h2 P hP

variable (ℓ : ℕ)

def IsGen (E : FakeEllipticCurve Λ N K) (hc : E.L.IsCommutative) (ℓ k : ℕ) (x : E.L.AlgPoints hc K) : Prop :=
  (∀ P : E.L.AlgPoints hc K, ℓ ^ k • P = 0 →
    ∃ m : ↥Λ, RelativeGroupLaw.AlgPoints.toPoint P = actP E m (RelativeGroupLaw.AlgPoints.toPoint x)) ∧
  (∀ m : ↥Λ, actP E m (RelativeGroupLaw.AlgPoints.toPoint x) = E.L.one (tK K) ↔
    ∃ m' : ↥Λ, (m : ℍ[ℚ, a, b]) = (((ℓ ^ k : ℕ) : ℚ) : ℍ[ℚ, a, b]) * (m' : ℍ[ℚ, a, b]))

variable (hℓK : (ℓ : K) ≠ 0)
include hℓK

omit [IsAlgClosed K] E hΛ in
theorem pow_ne_zero_K (k : ℕ) : ((ℓ ^ k : ℕ) : K) ≠ 0 := by
  rw [Nat.cast_pow]; exact pow_ne_zero _ hℓK

omit [IsAlgClosed K] E hΛ in
theorem ℓ_ne_zero : ℓ ≠ 0 := fun h => hℓK (by rw [h, Nat.cast_zero])

omit [IsAlgClosed K] hℓK in

theorem torsion_of_isGen {k : ℕ} {x : E.L.AlgPoints E.comm K} (hx : IsGen E E.comm ℓ k x) : ℓ ^ k • x = 0 := by
  rw [← actM_natCast E hΛ (ℓ ^ k) x, actM_eq_zero_iff]
  refine (hx.2 ⟨(((ℓ ^ k : ℕ) : ℚ) : ℍ[ℚ, a, b]), natCast_mem hΛ (ℓ ^ k)⟩).2 ⟨⟨1, one_mem hΛ⟩, ?_⟩
  simp

theorem isGen_finite (k : ℕ) : Finite {x : E.L.AlgPoints E.comm K // IsGen E E.comm ℓ k x} := by
  haveI := finite_torsion E (ℓ ^ k) (pow_ne_zero_K ℓ hℓK k)
  exact Finite.of_injective (fun x : {x : E.L.AlgPoints E.comm K // IsGen E E.comm ℓ k x} =>
    (⟨x.1, torsion_of_isGen E hΛ ℓ x.2⟩ : {x : E.L.AlgPoints E.comm K // ℓ ^ k • x = 0}))
    (fun x y h => Subtype.ext (congrArg (fun z => z.1) h))

omit [IsAlgClosed K] in

theorem isGen_smul {k : ℕ} {x : E.L.AlgPoints E.comm K} (hx : IsGen E E.comm ℓ (k + 1) x) : IsGen E E.comm ℓ k (ℓ • x) := by
  have hℓ0 : ℓ ≠ 0 := ℓ_ne_zero ℓ hℓK
  constructor
  · intro P hP
    have hP' : ℓ ^ (k + 1) • P = 0 := by rw [pow_succ', mul_smul, hP, smul_zero]
    obtain ⟨m, hm⟩ := hx.1 P hP'

    have hPm : P = actM E m x := RelativeGroupLaw.AlgPoints.toPoint_injective hm
    have hkill : actM E ⟨(((ℓ ^ k : ℕ) : ℚ) : ℍ[ℚ, a, b]) * m, natCast_mul_mem hΛ (ℓ ^ k) m⟩ x = 0 := by
      rw [actM_natCast_mul E hΛ, ← hPm, hP]
    rw [actM_eq_zero_iff] at hkill
    obtain ⟨m', hm'⟩ := (hx.2 _).1 hkill
    have hm'' : (((ℓ ^ k : ℕ) : ℚ) : ℍ[ℚ, a, b]) * (m : ℍ[ℚ, a, b]) =
        (((ℓ ^ (k + 1) : ℕ) : ℚ) : ℍ[ℚ, a, b]) * (m' : ℍ[ℚ, a, b]) := hm'
    have hmeq : (m : ℍ[ℚ, a, b]) = ((ℓ : ℚ) : ℍ[ℚ, a, b]) * m' := by
      apply cancel_natCast (pow_ne_zero k hℓ0)
      rw [hm'', pow_succ, Nat.cast_mul, QuaternionAlgebra.coe_mul, mul_assoc]
    refine ⟨m', ?_⟩
    rw [hm]
    show RelativeGroupLaw.AlgPoints.toPoint (actM E m x) = RelativeGroupLaw.AlgPoints.toPoint (actM E m' (ℓ • x))
    congr 1
    rw [← actM_natCast E hΛ ℓ x, ← actM_mul_elem E m' ⟨((ℓ : ℚ) : ℍ[ℚ, a, b]), natCast_mem hΛ ℓ⟩
      (mul_natCast_mem hΛ ℓ m')]
    apply actM_congr
    rw [hmeq]
    exact QuaternionAlgebra.coe_commutes _ _
  · intro m

    have hrew : actP E m (RelativeGroupLaw.AlgPoints.toPoint (ℓ • x)) =
        actP E ⟨((ℓ : ℚ) : ℍ[ℚ, a, b]) * m, natCast_mul_mem hΛ ℓ m⟩ (RelativeGroupLaw.AlgPoints.toPoint x) := by
      rw [← toPoint_actM, ← toPoint_actM, ← actM_mul_natCast E hΛ ℓ m x]
      congr 1
      apply actM_congr
      exact (QuaternionAlgebra.coe_commutes _ _).symm
    rw [hrew, hx.2]
    constructor
    · rintro ⟨m', hm'⟩
      have hm'' : ((ℓ : ℚ) : ℍ[ℚ, a, b]) * (m : ℍ[ℚ, a, b]) =
          (((ℓ ^ (k + 1) : ℕ) : ℚ) : ℍ[ℚ, a, b]) * (m' : ℍ[ℚ, a, b]) := hm'
      refine ⟨m', cancel_natCast hℓ0 ?_⟩
      rw [hm'', pow_succ', Nat.cast_mul, QuaternionAlgebra.coe_mul, mul_assoc]
    · rintro ⟨m', hm'⟩
      refine ⟨m', ?_⟩
      show ((ℓ : ℚ) : ℍ[ℚ, a, b]) * (m : ℍ[ℚ, a, b]) = _
      rw [hm', pow_succ', Nat.cast_mul, QuaternionAlgebra.coe_mul, mul_assoc]

omit [IsAlgClosed K] in

theorem isGen_pow_smul (i : ℕ) {k : ℕ} {x : E.L.AlgPoints E.comm K} (hx : IsGen E E.comm ℓ (k + i) x) :
    IsGen E E.comm ℓ k (ℓ ^ i • x) := by
  induction i generalizing x with
  | zero => rw [pow_zero, one_smul]; exact hx
  | succ i ih =>
    have h1 : IsGen E E.comm ℓ (k + i) (ℓ • x) := isGen_smul E hΛ ℓ hℓK hx
    have h2 := ih h1
    rwa [← mul_smul, ← pow_succ] at h2

omit hΛ in

theorem exists_smul_eq (k : ℕ) (x : E.L.AlgPoints E.comm K) (hx : ℓ ^ k • x = 0) :
    ∃ y : E.L.AlgPoints E.comm K, ℓ ^ (k + 1) • y = 0 ∧ ℓ • y = x := by

  let G : AddSubgroup (E.L.AlgPoints E.comm K) :=
    { carrier := {y | ℓ ^ (k + 1) • y = 0}
      add_mem' := fun {u v} hu hv => by
        show ℓ ^ (k + 1) • (u + v) = 0
        rw [smul_add, hu, hv, add_zero]
      zero_mem' := smul_zero _
      neg_mem' := fun {u} hu => by
        show ℓ ^ (k + 1) • (-u) = 0
        rw [smul_neg, hu, neg_zero] }

  let φ : G →+ E.L.AlgPoints E.comm K :=
    AddMonoidHom.mk' (fun y => ℓ • (y : E.L.AlgPoints E.comm K)) (fun u v => smul_add _ _ _)
  have hφ : ∀ y : G, φ y = ℓ • (y : E.L.AlgPoints E.comm K) := fun _ => rfl

  have hker : Nat.card φ.ker = ℓ ^ 4 := by
    rw [← natCard_torsion E ℓ hℓK]
    apply Nat.card_congr
    exact
      { toFun := fun z => ⟨((z.1 : G) : E.L.AlgPoints E.comm K), by
          have hz := z.2
          rw [AddMonoidHom.mem_ker, hφ] at hz
          exact hz⟩
        invFun := fun w => ⟨⟨w.1, by
          show ℓ ^ (k + 1) • w.1 = 0
          rw [pow_succ, mul_smul, w.2, smul_zero]⟩, by
          rw [AddMonoidHom.mem_ker, hφ]
          exact w.2⟩
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl }

  have hG : Nat.card G = (ℓ ^ (k + 1)) ^ 4 := natCard_torsion E (ℓ ^ (k + 1)) (pow_ne_zero_K ℓ hℓK (k + 1))

  have hrange : Nat.card φ.range = (ℓ ^ k) ^ 4 := by
    have h1 := AddSubgroup.card_mul_index φ.ker
    rw [AddSubgroup.index_ker, hker, hG] at h1
    have h2 : (ℓ ^ (k + 1)) ^ 4 = ℓ ^ 4 * (ℓ ^ k) ^ 4 := by ring
    rw [h2] at h1
    exact Nat.eq_of_mul_eq_mul_left (pos_of_ne_zero (pow_ne_zero 4 (ℓ_ne_zero ℓ hℓK))) h1

  have hsub : (φ.range : Set (E.L.AlgPoints E.comm K)) ⊆ {z | ℓ ^ k • z = 0} := by
    rintro _ ⟨y, rfl⟩
    show ℓ ^ k • (ℓ • (y : E.L.AlgPoints E.comm K)) = 0
    rw [← mul_smul, ← pow_succ]
    exact y.2
  haveI : Finite {z : E.L.AlgPoints E.comm K // ℓ ^ k • z = 0} := finite_torsion E (ℓ ^ k) (pow_ne_zero_K ℓ hℓK k)
  have hfin : ({z : E.L.AlgPoints E.comm K | ℓ ^ k • z = 0}).Finite :=
    Set.finite_coe_iff.mp (finite_torsion E (ℓ ^ k) (pow_ne_zero_K ℓ hℓK k))
  have heq : (φ.range : Set (E.L.AlgPoints E.comm K)) = {z | ℓ ^ k • z = 0} := by
    refine Set.eq_of_subset_of_ncard_le hsub ?_ hfin
    rw [← Nat.card_coe_set_eq, ← Nat.card_coe_set_eq]
    change Nat.card {z : E.L.AlgPoints E.comm K // ℓ ^ k • z = 0} ≤ Nat.card φ.range
    exact (natCard_torsion E (ℓ ^ k) (pow_ne_zero_K ℓ hℓK k)).trans_le hrange.ge
  have hxmem : x ∈ (φ.range : Set (E.L.AlgPoints E.comm K)) := by rw [heq]; exact hx
  obtain ⟨y, hy⟩ := hxmem
  exact ⟨y, y.2, hy⟩

omit [IsAlgClosed K] hℓK in

theorem isGen_zero : IsGen E E.comm ℓ 0 (0 : E.L.AlgPoints E.comm K) := by
  constructor
  · intro P hP
    rw [pow_zero, one_smul] at hP
    rw [hP]
    refine ⟨⟨1, one_mem hΛ⟩, ?_⟩
    rw [← toPoint_actM, actM_zero]
  · intro m
    constructor
    · intro _
      exact ⟨m, by rw [pow_zero, Nat.cast_one, QuaternionAlgebra.coe_one, one_mul]⟩
    · intro _
      exact (actM_eq_zero_iff E m 0).1 (actM_zero E m)

theorem isGen_one {q q' : ℕ} [Fact q.Prime] [Fact q'.Prime] (hB : IsIndefiniteRamifiedExactlyAt a b q q')
    [Fact ℓ.Prime] : ∃ x : E.L.AlgPoints E.comm K, IsGen E E.comm ℓ 1 x := by
  obtain ⟨P₀, -, h2, h3⟩ := torsStruct_prime_of_eq E hΛ hB (tK K) (specMap_algebraMap_self K) ℓ hℓK
  refine ⟨RelativeGroupLaw.AlgPoints.ofPoint (hc := E.comm) P₀, ?_, ?_⟩
  · intro P hP
    rw [pow_one, nsmul_eq_zero_iff'] at hP
    obtain ⟨m, hm⟩ := h2 _ hP
    exact ⟨m, hm⟩
  · intro m
    rw [pow_one]
    exact h3 m

theorem isGen_succ_succ {j : ℕ} {x : E.L.AlgPoints E.comm K} (hx : IsGen E E.comm ℓ (j + 1) x) :
    ∃ y : E.L.AlgPoints E.comm K, IsGen E E.comm ℓ (j + 2) y := by

  obtain ⟨y, hy1, hy2⟩ := exists_smul_eq E ℓ hℓK (j + 1) x (torsion_of_isGen E hΛ ℓ hx)

  have hz : IsGen E E.comm ℓ 1 (ℓ ^ (j + 1) • y) := by
    have h := isGen_pow_smul E hΛ ℓ hℓK j (k := 1) (x := x) (by rw [Nat.add_comm]; exact hx)
    rwa [← hy2, ← mul_smul, ← pow_succ] at h
  refine ⟨y, ?_, ?_⟩
  ·
    intro P hP
    have hP1 : ℓ ^ (j + 1) • (ℓ • P) = 0 := by rw [← mul_smul, ← pow_succ]; exact hP
    obtain ⟨m, hm⟩ := hx.1 _ hP1
    have hm' : ℓ • P = actM E m x := RelativeGroupLaw.AlgPoints.toPoint_injective hm
    have hQ : ℓ • (P - actM E m y) = 0 := by rw [smul_sub, hm', ← hy2, actM_nsmul, sub_self]
    have hQ' : ℓ ^ (j + 1) • (P - actM E m y) = 0 := by rw [pow_succ, mul_smul, hQ, smul_zero]
    obtain ⟨m', hm'2⟩ := hx.1 _ hQ'
    have hQeq : P - actM E m y = actM E m' x := RelativeGroupLaw.AlgPoints.toPoint_injective hm'2
    have h3 : actM E m' x = actM E ⟨(m' : ℍ[ℚ, a, b]) * ((ℓ : ℚ) : ℍ[ℚ, a, b]), mul_natCast_mem hΛ ℓ m'⟩ y := by
      rw [actM_mul_natCast E hΛ, hy2]
    refine ⟨⟨(m' : ℍ[ℚ, a, b]) * ((ℓ : ℚ) : ℍ[ℚ, a, b]), mul_natCast_mem hΛ ℓ m'⟩ + m, ?_⟩
    rw [← toPoint_actM]
    congr 1
    rw [actM_add_elem, ← h3, ← hQeq, sub_add_cancel]
  ·
    intro m
    rw [← actM_eq_zero_iff]
    constructor
    · intro h0'
      have h1 : actM E m x = 0 := by rw [← hy2, actM_nsmul, h0', smul_zero]
      obtain ⟨m₁, hm₁⟩ := (hx.2 m).1 ((actM_eq_zero_iff E m x).1 h1)
      have h2 : actM E m₁ (ℓ ^ (j + 1) • y) = 0 := by
        rw [← actM_mul_natCast E hΛ (ℓ ^ (j + 1)) m₁, ← h0']
        apply actM_congr
        rw [hm₁]
        exact (QuaternionAlgebra.coe_commutes _ _).symm
      obtain ⟨m₂, hm₂⟩ := (hz.2 m₁).1 ((actM_eq_zero_iff E m₁ _).1 h2)
      have hnat : ((ℓ ^ (j + 1) : ℕ) : ℚ) * ((ℓ ^ 1 : ℕ) : ℚ) = ((ℓ ^ (j + 2) : ℕ) : ℚ) := by
        push_cast; ring
      refine ⟨m₂, ?_⟩
      rw [hm₁, hm₂, ← mul_assoc, ← QuaternionAlgebra.coe_mul, hnat]
    · rintro ⟨m₂, hm₂⟩
      have hy1' : ℓ ^ (j + 2) • y = 0 := hy1
      have : actM E m y =
          actM E ⟨(((ℓ ^ (j + 2) : ℕ) : ℚ) : ℍ[ℚ, a, b]) * m₂, natCast_mul_mem hΛ (ℓ ^ (j + 2)) m₂⟩ y :=
        actM_congr E hm₂ y
      rw [this, actM_natCast_mul E hΛ, ← actM_nsmul, hy1', actM_zero]

theorem isGen_nonempty {q q' : ℕ} [Fact q.Prime] [Fact q'.Prime] (hB : IsIndefiniteRamifiedExactlyAt a b q q')
    [Fact ℓ.Prime] (k : ℕ) : ∃ x : E.L.AlgPoints E.comm K, IsGen E E.comm ℓ k x := by
  induction k with
  | zero => exact ⟨0, isGen_zero E hΛ ℓ⟩
  | succ k ih =>
    cases k with
    | zero => exact isGen_one E hΛ ℓ hℓK hB
    | succ j =>
      obtain ⟨x, hx⟩ := ih
      exact isGen_succ_succ E hΛ ℓ hℓK hx

def genSystem : ℕᵒᵖ ⥤ Type :=
  Functor.ofOpSequence (X := fun k => {x : E.L.AlgPoints E.comm K // IsGen E E.comm ℓ k x})
    (fun _ => TypeCat.ofHom (fun x => ⟨ℓ • x.1, isGen_smul E hΛ ℓ hℓK x.2⟩))

theorem exists_compatible {q q' : ℕ} [Fact q.Prime] [Fact q'.Prime] (hB : IsIndefiniteRamifiedExactlyAt a b q q')
    [Fact ℓ.Prime] :
    ∃ s : ∀ k : ℕ, {x : E.L.AlgPoints E.comm K // IsGen E E.comm ℓ k x},
      ∀ k, ((s k : E.L.AlgPoints E.comm K)) = ℓ • (s (k + 1) : E.L.AlgPoints E.comm K) := by
  haveI : ∀ j : ℕᵒᵖ, Finite ((genSystem E hΛ ℓ hℓK).obj j) := fun j =>
    isGen_finite E hΛ ℓ hℓK (Opposite.unop j)
  haveI : ∀ j : ℕᵒᵖ, Nonempty ((genSystem E hΛ ℓ hℓK).obj j) := fun j => by
    obtain ⟨x, hx⟩ := isGen_nonempty E hΛ ℓ hℓK hB (Opposite.unop j)
    exact ⟨⟨x, hx⟩⟩
  obtain ⟨s, hs⟩ := nonempty_sections_of_finite_inverse_system (genSystem E hΛ ℓ hℓK)
  refine ⟨fun k => s (Opposite.op k), fun k => ?_⟩
  have := hs (homOfLE (Nat.le_add_right k 1)).op
  unfold genSystem at this
  rw [Functor.ofOpSequence_map_homOfLE_succ] at this
  exact (congrArg Subtype.val this).symm

theorem main {q q' : ℕ} [Fact q.Prime] [Fact q'.Prime] (hB : IsIndefiniteRamifiedExactlyAt a b q q')
    [Fact ℓ.Prime] :
    ∃ x : TateModule ℓ (E.L.AlgPoints E.comm K),
      ∀ n : ℕ,
        (∀ P : E.L.AlgPoints E.comm K, ℓ ^ n • P = 0 →
          ∃ m : ↥Λ, RelativeGroupLaw.AlgPoints.toPoint P =
            pushPt (E.act m) (E.act_over m) (RelativeGroupLaw.AlgPoints.toPoint ((x : ℕ → E.L.AlgPoints E.comm K) n))) ∧
        (∀ m : ↥Λ,
          pushPt (E.act m) (E.act_over m) (RelativeGroupLaw.AlgPoints.toPoint ((x : ℕ → E.L.AlgPoints E.comm K) n)) =
              E.L.one (Spec.map (CommRingCat.ofHom (algebraMap K K))) ↔
            ∃ m' : ↥Λ, (m : ℍ[ℚ, a, b]) = (((ℓ ^ n : ℕ) : ℚ) : ℍ[ℚ, a, b]) * (m' : ℍ[ℚ, a, b])) := by
  obtain ⟨s, hs⟩ := exists_compatible E hΛ ℓ hℓK hB
  refine ⟨⟨fun n => (s n : E.L.AlgPoints E.comm K), fun n => ⟨?_, ?_⟩⟩, fun n => (s n).2⟩
  · rw [natCast_zsmul]
    exact torsion_of_isGen E hΛ ℓ (s n).2
  · rw [natCast_zsmul]
    exact (hs n).symm

end Main

end P2mKcTateRankOnePrime

end

open CategoryTheory AlgebraicGeometry NeronModelInfra GoodReductionJacobian CerednikDrinfeld CerednikDrinfeld.QM QuaternionAlgebra in

theorem solution
    {a b : ℚ} {q q' : ℕ} [Fact q.Prime] [Fact q'.Prime] (hB : IsIndefiniteRamifiedExactlyAt a b q q')
    (Λ : Submodule ℤ ℍ[ℚ, a, b]) (hΛ : IsMaximalOrder Λ) {N : ℕ}
    (K : Type) [Field K] [IsAlgClosed K] (E : FakeEllipticCurve Λ N K)
    (ℓ : ℕ) [Fact ℓ.Prime] (hℓK : (ℓ : K) ≠ 0) :
    ∃ x : TateModule ℓ (E.L.AlgPoints E.comm K),
      ∀ n : ℕ,
        (∀ P : E.L.AlgPoints E.comm K, ℓ ^ n • P = 0 →
          ∃ m : ↥Λ, RelativeGroupLaw.AlgPoints.toPoint P =
            pushPt (E.act m) (E.act_over m) (RelativeGroupLaw.AlgPoints.toPoint ((x : ℕ → E.L.AlgPoints E.comm K) n))) ∧
        (∀ m : ↥Λ,
          pushPt (E.act m) (E.act_over m) (RelativeGroupLaw.AlgPoints.toPoint ((x : ℕ → E.L.AlgPoints E.comm K) n)) =
              E.L.one (Spec.map (CommRingCat.ofHom (algebraMap K K))) ↔
            ∃ m' : ↥Λ, (m : ℍ[ℚ, a, b]) = (((ℓ ^ n : ℕ) : ℚ) : ℍ[ℚ, a, b]) * (m' : ℍ[ℚ, a, b])) :=
  P2mKcTateRankOnePrime.main E hΛ ℓ hℓK hB

end S_CerednikDrinfeld_QM_FakeEllipticCurve_exists_tateModule_forall_generator_torsion_of_isMaximalOrder_of_prime
end P2MW
export P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_exists_tateModule_forall_generator_torsion_of_isMaximalOrder_of_prime (solution)
