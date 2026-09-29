-- Prove2me | solution 1 for CerednikDrinfeld.QM.FakeEllipticCurve.nonempty_fullLevel_of_isMaximalOrder
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.141142+00:00
-- url     : https://prove2.me/submissions/202fd12b-ab37-503e-9887-5c64d51db4f2

import Mathlib
import Definitions.Def_CerednikDrinfeld_QMFineModuli
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawKernel
import Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_exists_generator_torsionPoints_of_isMaximalOrder_of_prime
import Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_nsmul_surjective_of_isAlgClosed_of_connectedSpace
import Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_natCard_isTorsionPoint_eq_pow_of_natCast_ne_zero
import Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_smoothOfRelativeDimension_two
import Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_exists_isPullback_levelIff
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_nonempty_fullLevel_of_isMaximalOrder
p2m_attr_erase "instance" "GoodReductionJacobian.RelativeGroupLaw.isIso_endKerStr_schemeHomOverId AlgebraicGeometry.Scheme.PresheafOfModules.symmetricCategory SheafOfModules.instFaithfulRingSheafPModToPMod SheafOfModules.symmetricCategory AlgebraicGeometry.Scheme.PresheafOfModules.monoidalCategory AlgebraicGeometry.Scheme.PresheafOfModules.monoidalClosed SheafOfModules.instFullRingSheafPModToPMod SheafOfModules.monoidalCategory AlgebraicGeometry.Scheme.Modules.symmetricCategory SheafOfModules.monoidalClosed SheafOfModules.instIsLocalizationPModRingSheafSheafifyFunctorPresheafW SheafOfModules.sheafifyFunctor_monoidal AlgebraicGeometry.Scheme.Modules.monoidalClosed AlgebraicGeometry.instMonoidalPresheafOfModulesModulesSheafify AlgebraicGeometry.Scheme.Modules.monoidalCategory PresheafOfModules.instMonoidalClosed PresheafOfModules.InternalHom.instModuleCarrierObjOppositeCommRingCatSubtypePiFamilyMemAddSubgroupNaturalFamilies PresheafOfModules.InternalHom.instModuleCarrierObjOppositeRingCatCompCommRingCatForget₂RingHomCarrierCarrierAbPresheaf PresheafOfModules.InternalHom.instSMulCarrierObjOppositeCommRingCatSubtypePiFamilyMemAddSubgroupNaturalFamilies AlgebraicGeometry.Scheme.Hom.opensMapFinal AlgebraicGeometry.RelPicard.RigidifiedLineBundle.setoid AlgebraicGeometry.RelPicard.RigidifiedLineBundle.instInhabited AlgebraicGeometry.OModulePresheaf.isScalarTower AlgebraicGeometry.Scheme.OrderedAffineCover.instLinearOrder AlgebraicGeometry.OModulePresheaf.module AlgebraicGeometry.Scheme.OrderedAffineCover.instFintype AlgebraicGeometry.Scheme.OrderedAffineCover.instFintypeIdx AlgebraicGeometry.OModulePresheaf.addCommGroup AlgebraicGeometry.Scheme.OrderedAffineCover.instDecidableEqIdx AlgebraicGeometry.OModulePresheaf.moduleSections TwoChartCech.Sections.M0_moduleA TwoChartCech.Sections.M1_module TwoChartCech.Cover.A01_algebra TwoChartCech.Cover.A0_algebra TwoChartCech.Cover.A1_commRing TwoChartCech.Cover.A1_algebra TwoChartCech.Sections.M01_module TwoChartCech.Sections.M0_addCommGroup TwoChartCech.Sections.M0_tower TwoChartCech.Sections.M01_addCommGroup"
p2m_attr_erase "instance" "TwoChartCech.Cover.A0_commRing TwoChartCech.Sections.M1_tower TwoChartCech.Sections.M01_moduleA TwoChartCech.Sections.M0_module TwoChartCech.Sections.M1_moduleA TwoChartCech.Sections.M1_addCommGroup TwoChartCech.Cover.A01_commRing TwoChartCech.Sections.M01_tower CoherentBaseChange.TwoTermComplex.C0_module CoherentBaseChange.TwoTermComplex.C0_addCommGroup CoherentBaseChange.TwoTermComplex.C1_module CoherentBaseChange.TwoTermComplex.C1_addCommGroup CoherentBaseChange.TwoTermComplex.C0_free CoherentBaseChange.TwoTermComplex.C1_finite CoherentBaseChange.TwoTermComplex.C0_finite CoherentBaseChange.TwoTermComplex.C1_free AlgebraicGeometry.OModulePresheaf.instSubsingletonObjZero AlgebraicGeometry.Scheme.Modules.preservesBinaryProducts_opensMap AlgebraicGeometry.Scheme.Modules.pullback_monoidal AlgebraicGeometry.Scheme.Modules.sheafify_isLocalization' AlgebraicGeometry.Scheme.Modules.preservesTerminal_opensMap AlgebraicGeometry.Scheme.Modules.pullback₀_monoidal AlgebraicGeometry.Scheme.Modules.preservesFiniteProducts_opensMap AlgebraicGeometry.Scheme.Modules.instLiftingPresheafOfModulesSheafifyPresheafWOpensCarrierCarrierCommRingCatGrothendieckTopologyObjFunctorOppositeIsSheafSheafCompPullback₀Pullback PresheafOfModules.PullbackMonoidal.pullback_monoidal PresheafOfModules.PullbackMonoidal.isIso_δ PresheafOfModules.pushforward_laxMonoidal PresheafOfModules.PullbackMonoidal.isIso_η PresheafOfModules.free_monoidal PresheafOfModules.restrictScalars_laxMonoidal PresheafOfModules.PullbackMonoidal.isIso_δ_gS PresheafOfModules.pullback_oplaxMonoidal PresheafOfModules.PullbackMonoidal.instPreservesColimitsOfSizeCompOppositeCommRingCatRingCatForget₂RingHomCarrierCarrierPb PresheafOfModules.pullback_monoidal' AlgebraicGeometry.SmoothOfRelativeDimension.fiberToSpecResidueField AlgebraicGeometry.SmoothOfRelativeDimension.pullback_snd AlgebraicGeometry.SmoothOfRelativeDimension.pullback_fst AlgebraicGeometry.SmoothOfRelativeDimension.smooth_one AlgebraicGeometry.SmoothProperCurve.isIntegral_pullback_Spec_field AlgebraicGeometry.IsProper.fiberToSpecResidueField"
p2m_attr_erase "instance" "AlgebraicCurve.CurveModel.isProper AlgebraicCurve.CurveModel.isIntegral AlgebraicCurve.CurveModel.smooth AlgebraicGeometry.Scheme.LocalRepresentabilityULift.instIsLocallyInjectiveFunUliftYonedaGluedToSheaf AlgebraicGeometry.Scheme.LocalRepresentabilityULift.instIsLocallySurjectiveFunUliftYonedaGluedToSheafOfIsLocallySurjectiveZariskiTopologyDescFunctorOppositeType AlgebraicGeometry.Scheme.LocalRepresentabilityULift.instIsOpenImmersionToGlued AlgebraicGeometry.Scheme.LocalRepresentabilityULift.instIsIsoSheafZariskiTopologyTypeUliftYonedaGluedToSheaf AlgebraicGeometry.RelPicard.instIsOpenImmersionToGlued AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.instFundamentalIdentityOfSumRamificationInertia AlgebraicCurve.Place.instIsScalarTowerResidueFieldRestrictPushforward AlgebraicCurve.Place.instAlgebraResidueFieldRestrictPushforward AlgebraicCurve.Place.instIsLocalHomRestrictInclusion AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions PresheafOfModules.ExteriorPower.instModulePresheafAb AlgebraicGeometry.RelEffCartierDiv.subsingleton_of_degree_zero AlgebraicGeometry.RelEffCartierDiv.isIso_subschemeIota_snd_of_degree_one AlgebraicGeometry.isIso_ker_graphOver_subschemeIota_snd AlgebraicGeometry.isClosedImmersion_graphOver AlgebraicGeometry.FGSubalgebra.instIsDirectedLe AlgebraicGeometry.FGSubalgebra.instQuasiSeparatedSpaceCarrierCarrierCommRingCatObjOppositeSchemeSpecDiagram AlgebraicGeometry.FGSubalgebra.instIsCofilteredOpposite AlgebraicGeometry.FGSubalgebra.instIsAffineObjOppositeSchemeSpecDiagram AlgebraicGeometry.FGSubalgebra.instNonempty AlgebraicGeometry.FGSubalgebra.instNonemptySubtypeLeSubalgebraValFG AlgebraicGeometry.FGSubalgebra.instCompactSpaceCarrierCarrierCommRingCatObjOppositeSchemeSpecDiagram AlgebraicGeometry.FGSubalgebra.instIsDirectedSubtypeLeSubalgebraValFG AlgebraicGeometry.FGSubalgebra.instIsAffineHomMapOppositeSchemeSpecDiagram AlgebraicGeometry.FGSubalgebra.instIsFiltered AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instNeg AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instSMulInt AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instAddCommGroup AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instAdd AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instSub"
p2m_attr_erase "instance" "AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instModuleCarrierObjOppositeOpensCarrierCarrierCommRingCatPresheafOpOpensTop AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instSMulCarrierObjOppositeOpensCarrierCarrierCommRingCatPresheafOpOpensTop AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instSMulNat AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instZero AlgebraicCurve.instHasLocalResidue_of_hasCanonicalLocalResidueK AlgebraicCurve.instHasCanonicalLocalResidueK_of_hasCanonicalLocalResidueKStar AlgebraicCurve.Place.kw_ffgc_finiteDimensional_adicCompletion instAlgebraSubtypeMemValuationSubring_definitions AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersIntegersCompletion ModularCurve.KwF4gRRTate.instAlgebraKAdicCompletionIntegers AlgebraicCurve.Place.kw_ffgc_continuousSMul_adicCompletionComap AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersCompletionCompletion IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions AlgebraicCurve.instHasCanonicalLocalResidueK AlgebraicCurve.Place.instAlgebra_restrictResidueField AlgebraicCurve.Place.instIsScalarTower_restrictResidueField AlgebraicCurve.instHasLocalResidue AlgebraicCurve.HasSeparableResidue.of_perfectField_of_isCurveOver AlgebraicCurve.HasSeparableResidue.of_perfectField AlgebraicCurve.Place.instIsLocalHom_restrictSubringHom AlgebraicCurve.instHasCanonicalLocalResidueKStar ModularCurve.KwNo6Pin.isLocalRing_completion SheafOfModules.isIso_ihomModelToIhom AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instDecidableEqIdx AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instFintype AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instLinearOrder AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instFintypeIdx AlgebraicGeometry.OModulePresheaf.Leray.relAltC_scalarTower AlgebraicGeometry.OModulePresheaf.Leray.ker_relAltd_modΓ AlgebraicGeometry.OModulePresheaf.Leray.relAltC_modΓ AlgebraicGeometry.OModulePresheaf.Leray.biC_abGrp AlgebraicGeometry.OModulePresheaf.Leray.relAltH_modΓ AlgebraicGeometry.OModulePresheaf.Leray.ker_relAltd_smul AlgebraicGeometry.OModulePresheaf.Leray.relAltH_scalarTower AlgebraicGeometry.OModulePresheaf.Leray.relAltH_smul"
p2m_attr_erase "instance" "AlgebraicGeometry.OModulePresheaf.Leray.biC_module DoubleComplex.instModuleE₂I DoubleComplex.Bounded.modR DoubleComplex.instModuleE₂II DoubleComplex.instAddCommGroupE₂II DoubleComplex.Bounded.abGrp DoubleComplex.instAddCommGroupE₂I AlgebraicGeometry.ChowDatum.hι_closed AlgebraicGeometry.ChowDatumProj.hιN_closed AlgebraicGeometry.ChowDatumProj.hp_proper AlgebraicGeometry.ChowDatum.hp_isoU AlgebraicGeometry.ChowDatum.hp_proper AlgebraicGeometry.ProjSpace.algebraAway AlgebraicGeometry.ProjSpace.instIsProperProdOverπ AlgebraicGeometry.ChowDatumProj.hp_isoU AlgebraicGeometry.ProjSpace.isProper_π AlgebraicGeometry.ProjSpace.finiteType_mvPolynomial ProjSpaceCech.GradedModule.H.module ProjSpaceCech.GradedModule.H.addCommGroup ProjSpaceCech.GradedModule.sec.instAdd ProjSpaceCech.GradedModule.sec.instNeg ProjSpaceCech.GradedModule.acg ProjSpaceCech.GradedModule.Frac.setoid ProjSpaceCech.GradedModule.modR ProjSpaceCech.GradedModule.sec.instModule ProjSpaceCech.GradedModule.sec.instAddCommGroup ProjSpaceCech.GradedModule.sec.instZero ProjSpaceCech.GradedModule.Presentation.fJ ProjSpaceCech.GradedModule.sec.instSMul ProjSpaceCech.Twist.H.module ProjSpaceCech.Idx.instFintype ProjSpaceCech.Twist.H.addCommGroup ProjSpaceCech.Idx.instDecidableEq ProjSpaceCech.Twist.Mon.instDecidableEq ProjSpaceCech.Twist.cochain.instAddCommGroup ProjSpaceCech.Twist.cochain.instModule AlgebraicGeometry.FGSubalgebra.tensorStage_directedSystem AlgebraicGeometry.RelEffCartierDiv.isClosedImmersion_subschemeι_resProdMap AlgebraicGeometry.RelEffCartierDiv.isOpenImmersion_resProdMap AlgebraicCurve.CurveModel.locallyOfFiniteType_gluedToBase"
p2m_attr_erase "instance" "AlgebraicCurve.CurveModel.isFractionRing_overlap AlgebraicCurve.CurveModel.isLocallyNoetherian_glued AlgebraicCurve.CurveModel.jacobsonSpace_glued AlgebraicCurve.CurveModel.isOpenImmersion_ι₀ AlgebraicCurve.CurveModel.isIntegral_glued AlgebraicCurve.CurveModel.quasiSeparated_gluedToBase AlgebraicCurve.CurveModel.compactSpace_glued AlgebraicCurve.CurveModel.isIntegral_adjoin_chartRing AlgebraicCurve.CurveModel.isFractionRing_overlap_functionField AlgebraicCurve.CurveModel.isProper_gluedToBase AlgebraicCurve.CurveModel.isOpenImmersion_ιU AlgebraicCurve.CurveModel.isOpenImmersion_f₀ AlgebraicCurve.CurveModel.isOpenImmersion_fInf AlgebraicCurve.CurveModel.isOpenImmersion_ιInf AlgebraicCurve.CurveModel.algebra_overlap_functionField AlgebraicCurve.CurveModel.quasiCompact_gluedToBase AlgebraicCurve.CurveModel.algebraAdjoin AlgebraicCurve.CurveModel.isDedekindDomain_chartRing AlgebraicCurve.CurveModel.isIntegralClosure AlgebraicCurve.CurveModel.finite_chartRing AlgebraicCurve.CurveModel.centre_isPrime AlgebraicCurve.CurveModel.isFractionRing_chartRing AlgebraicCurve.CurveModel.finiteType_chartRing AlgebraicCurve.CurveModel.isNoetherianRing_chartRing AlgebraicCurve.CurveModel.isScalarTower_base_adjoin AlgebraicCurve.CurveModel.isScalarTower_adjoin AlgebraicCurve.CurveModel.chartRing_finitePresentation instTopologicallyFGOfFiniteType AlgebraicGeometry.ProjSpace.twistObj.addCommGroup AlgebraicGeometry.ProjSpace.twistFam.module AlgebraicGeometry.ProjSpace.twistObj.module AlgebraicGeometry.ProjSpace.twistObj.moduleSections AlgebraicGeometry.ProjSpace.twistFam.addCommGroup"
p2m_attr_erase "simp" "NeronModelInfra.NeronModelPropertyBundle.endExtensionEquiv_symm_restrict NeronModelInfra.schemeHomOverComp_id_left NeronModelInfra.schemeHomOverComp_id_right NeronModelInfra.schemeHomOverId_coe NeronModelInfra.NeronModelPropertyBundle.endExtensionEquiv_apply NeronModelInfra.NeronModelPropertyBundle.restrict_endExtensionEquiv_symm NeronModelInfra.schemeHomOverComp_coe NeronModelInfra.schemeHomOverNpow_succ NeronModelInfra.schemeHomOverNpow_zero GoodReductionJacobian.relativeGroupLawOfGrpObj_inv GoodReductionJacobian.relativeGroupLawOfGrpObj_mul GoodReductionJacobian.overHomEquivSchemeHomOver_apply_coe GoodReductionJacobian.relativeGroupLawOfGrpObj_one GoodReductionJacobian.overHomEquivSchemeHomOver_symm_apply_left SheafOfModules.tensorUnit_eq AlgebraicGeometry.Scheme.Modules.tensorUnit_eq PresheafOfModules.InternalHom.presheaf_map_apply PresheafOfModules.InternalHom.curryFamily_app PresheafOfModules.InternalHom.add_app PresheafOfModules.InternalHom.smul_app PresheafOfModules.InternalHom.zero_app PresheafOfModules.ihomObj_map_val PresheafOfModules.ihomFunctor_map PresheafOfModules.InternalHom.restrict_app PresheafOfModules.InternalHom.postcomp_app PresheafOfModules.InternalHom.neg_app PresheafOfModules.curry'_app_val PresheafOfModules.InternalHom.presheaf_obj PresheafOfModules.ihomFunctor_obj PresheafOfModules.ihomObj_obj PresheafOfModules.InternalHom.sub_app PresheafOfModules.ihomMap_app_val AlgebraicGeometry.Scheme.Modules.tensorPow_zero AlgebraicGeometry.Scheme.Modules.tensorPow_succ AlgebraicGeometry.RelPicard.RigidifiedLineBundle.mk.sizeOf_spec AlgebraicGeometry.RelPicard.RigidifiedLineBundle.mk.injEq AlgebraicGeometry.Scheme.OrderedAffineCover.mk.injEq AlgebraicGeometry.OModulePresheaf.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCover.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.mk.injEq"
p2m_attr_erase "simp" "AlgebraicGeometry.Scheme.TwoAffineOpenCover.mk.injEq AlgebraicGeometry.Scheme.TwoAffineOpenCover.mk.sizeOf_spec AlgebraicGeometry.Scheme.TwoAffineOpenCover.pullback_U1 AlgebraicGeometry.Scheme.TwoAffineOpenCover.pullback_U0 TwoChartCech.Sections.mk.injEq TwoChartCech.Cover.mk.injEq TwoChartCech.GrothendieckComplex.mk.injEq TwoChartCech.Sections.mk.sizeOf_spec TwoChartCech.Cover.mk.sizeOf_spec TwoChartCech.Cover.lineBundle_r0_apply TwoChartCech.GrothendieckComplex.mk.sizeOf_spec TwoChartCech.Cover.lineBundle_r1_apply CoherentBaseChange.TwoTermComplex.mk.sizeOf_spec CoherentBaseChange.TwoTermComplex.mk.injEq AlgebraicGeometry.OModulePresheaf.prod_obj AlgebraicGeometry.OModulePresheaf.restrOpen_obj AlgebraicGeometry.OModulePresheaf.DevissageStep.mk.injEq AlgebraicGeometry.OModulePresheaf.pushforward_obj AlgebraicGeometry.OModulePresheaf.im_obj AlgebraicGeometry.OModulePresheaf.pow_obj AlgebraicGeometry.OModulePresheaf.fstHom_app AlgebraicGeometry.OModulePresheaf.ker_obj AlgebraicGeometry.OModulePresheaf.coker_obj AlgebraicGeometry.OModulePresheaf.DevissageStep.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCover.preimage_U AlgebraicGeometry.OModulePresheaf.sndHom_app AlgebraicGeometry.OModulePresheaf.Hom.mk.injEq AlgebraicGeometry.OModulePresheaf.Hom.id_app AlgebraicGeometry.OModulePresheaf.AffHom.appSections_apply AlgebraicGeometry.OModulePresheaf.AffHom.comp_app AlgebraicGeometry.OModulePresheaf.AffSES.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.AffHom.kerMap_coe AlgebraicGeometry.OModulePresheaf.AffHom.id_app AlgebraicGeometry.OModulePresheaf.Hom.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.Hom.toAffHom_app AlgebraicGeometry.OModulePresheaf.SES.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.AffHom.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.Hom.comp_app AlgebraicGeometry.OModulePresheaf.SES.mk.injEq AlgebraicGeometry.OModulePresheaf.AffHom.mk.injEq"
p2m_attr_erase "simp" "AlgebraicGeometry.OModulePresheaf.Hom.appSections_apply AlgebraicGeometry.OModulePresheaf.AffSES.mk.injEq PresheafOfModules.freeεIso_hom_app PresheafOfModules.freeμIso_hom_app AlgebraicGeometry.RelPicard.RepresentsRelSubPic.mk.injEq AlgebraicGeometry.RelPicard.SubPicCondition.mk.injEq AlgebraicGeometry.RelPicard.SubPicCondition.mk.sizeOf_spec AlgebraicGeometry.RelPicard.RepresentsRelSubPic.mk.sizeOf_spec AlgebraicGeometry.SmoothProperCurve.sectionBaseChange_coe_snd AlgebraicGeometry.SmoothProperCurve.sectionBaseChange_coe_fst AlgebraicCurve.CurveModel.mk.injEq AlgebraicCurve.CurveModel.mk.sizeOf_spec AlgebraicCurve.mulAdele_apply AlgebraicCurve.residuePairing_apply_coe AlgebraicCurve.mem_adeleBdd AlgebraicCurve.weilSmul_one AlgebraicCurve.diagonalHom_apply AlgebraicCurve.weilSmul_apply AlgebraicCurve.adeleSpaceMul_coe AlgebraicCurve.mulAdele_one AlgebraicGeometry.SmoothProperCurve.FiniteMapData.twoAffineOpenCover_U1 AlgebraicGeometry.SmoothProperCurve.FiniteMapData.mk.injEq AlgebraicGeometry.SmoothProperCurve.FiniteMapData.mk.sizeOf_spec AlgebraicGeometry.SmoothProperCurve.FiniteMapData.twoAffineOpenCover_U0 AlgebraicGeometry.RelPicard.SubPicCondition.onClasses_mk AlgebraicGeometry.RelPicard.relSubPicPresheaf_map_coe CategoryTheory.Functor.OverTotal.ofFibre_fst CategoryTheory.Functor.overTotal_map_fst AlgebraicGeometry.Scheme.LocalRepresentabilityULift.glueData_J AlgebraicGeometry.Scheme.LocalRepresentabilityULift.uliftYoneda_toGlued_uliftYonedaGluedToSheaf AlgebraicGeometry.Scheme.LocalRepresentabilityULift.glueData_t' AlgebraicGeometry.Scheme.LocalRepresentabilityULift.uliftYoneda_toGlued_uliftYonedaGluedToSheaf_assoc AlgebraicGeometry.Scheme.LocalRepresentabilityULift.uliftYonedaGluedToSheaf_app_toGlued AlgebraicGeometry.Scheme.LocalRepresentabilityULift.glueData_openCover_map AlgebraicGeometry.Scheme.LocalRepresentabilityULift.uliftYonedaGluedToSheaf_app_comp AlgebraicGeometry.Scheme.LocalRepresentabilityULift.glueData_V AlgebraicGeometry.Scheme.LocalRepresentabilityULift.glueData_t AlgebraicGeometry.Scheme.LocalRepresentabilityULift.glueData_U AlgebraicGeometry.Scheme.LocalRepresentabilityULift.glueData_f AlgebraicGeometry.RelPicard.designationOfRepresentableBy_P"
p2m_attr_erase "simp" "AlgebraicGeometry.RelPicard.designationOfRepresentableBy_toBase AlgebraicGeometry.RelPicard.rigSection_snd AlgebraicGeometry.RelPicard.RigidifiedLineBundle.ofInvertible_L AlgebraicGeometry.RelPicard.rigSection_snd_assoc AlgebraicGeometry.RelPicard.SubPicGroupCondition.mk.injEq AlgebraicGeometry.RelPicard.SubPicGroupCondition.mk.sizeOf_spec AlgebraicCurve.coe_cechH0Equiv_apply AlgebraicCurve.cechH1ToH1_mk AlgebraicCurve.lSpaceOn_univ AlgebraicCurve.lSpaceOn_empty AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.Divisor.mapRestrict_single AlgebraicCurve.Divisor.pushforward_single AlgebraicCurve.Place.coe_restrictInclusion AlgebraicCurve.Place.mem_fiber AlgebraicCurve.Place.restrict_toValuationSubring AlgebraicCurve.Divisor.degree_pushforward AlgebraicCurve.Place.restrictResidueMap_residue AlgebraicCurve.Pic0.coe_pushforwardDegZeroHom AlgebraicCurve.Pic0.coe_pullbackDegZeroHom AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk"
p2m_attr_erase "simp" "ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Divisor.degree_pushforwardAlong AlgebraicCurve.Pic0.coe_degZeroCorrespondence AlgebraicCurve.Place.mem_fiberAlong AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.jqNModC_one ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one AlgebraicCurve.Place.differentialCoeff_zero AlgebraicCurve.Place.differentialCoeff_dCoord AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.injEq AlgebraicCurve.TranscendenceTower.mk.injEq AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec AlgebraicCurve.PoleDivisorPackage.mk.injEq AlgebraicGeometry.RelPicard.thetaBundle_def AlgebraicGeometry.RelPicard.picardBundle_def AlgebraicGeometry.RelEffCartierDiv.toRelEffDivisor_ofRelEffDivisor AlgebraicGeometry.RelEffCartierDiv.toRelEffDivisor_I AlgebraicGeometry.mapOnProdOver_fst_assoc AlgebraicGeometry.RelEffCartierDiv.mk.sizeOf_spec AlgebraicGeometry.RelEffCartierDiv.mk.injEq"
p2m_attr_erase "simp" "AlgebraicGeometry.mapOnProdOver_snd AlgebraicGeometry.mapOnProdOver_fst AlgebraicGeometry.mapOnProdOver_snd_assoc AlgebraicGeometry.mapOnProdOver_id AlgebraicCurve.RelEffDivisor.mk.sizeOf_spec AlgebraicCurve.mapOnProd_fst AlgebraicCurve.mapOnProd_fst_assoc AlgebraicCurve.mapOnProd_snd AlgebraicCurve.UnivDivisorPack.mk.injEq AlgebraicCurve.RelEffDivisor.mk.injEq AlgebraicCurve.UnivDivisorPack.mk.sizeOf_spec AlgebraicCurve.mapOnProd_snd_assoc AlgebraicGeometry.Scheme.Modules.exteriorPower_obj PresheafOfModules.exteriorPower_map_ιMulti PresheafOfModules.ExteriorPower.appₗ_apply AlgebraicGeometry.prodKerGraph_one AlgebraicGeometry.fibrePowOver.proj_comp AlgebraicGeometry.prodKerGraph_zero AlgebraicGeometry.RelEffCartierDiv.empty_I AlgebraicGeometry.fibrePowOver.proj_comp_assoc AlgebraicGeometry.graphOver_fst_assoc AlgebraicGeometry.RelEffCartierDiv.toPoint_comp AlgebraicGeometry.RelEffCartierDiv.toPoint_comp_assoc AlgebraicGeometry.graphOver_fst AlgebraicGeometry.RelEffCartierDiv.ofPoint_I AlgebraicGeometry.graphOver_snd AlgebraicGeometry.graphOver_snd_assoc AlgebraicCurve.SymmetricPowerPackage.mk.sizeOf_spec AlgebraicCurve.SymmetricPowerPackage.mk.injEq AlgebraicGeometry.FGSubalgebra.cocone_ι_app_apply AlgebraicGeometry.RelPicard.fst_toProdSpec AlgebraicGeometry.RelPicard.toProdSpec_fst_assoc AlgebraicGeometry.RelPicard.pointsSubBasepointModule_cons AlgebraicGeometry.RelPicard.pointsSubBasepointModule_nil AlgebraicGeometry.RelPicard.fst_toProdSpec_assoc AlgebraicGeometry.RelPicard.toProdSpec_fst AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.sub_app AlgebraicGeometry.Scheme.IdealSheafData.sres_sresTop AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.add_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.mk.sizeOf_spec"
p2m_attr_erase "simp" "AlgebraicGeometry.Scheme.IdealSheafData.coe_resLE AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.smul_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.coe_ofLE_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.ideal_range AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.zero_app AlgebraicGeometry.Scheme.IdealSheafData.sres_sres AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.comp_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.neg_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.id_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.coe_mulRight_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.nsmul_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.mk.injEq AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.zsmul_app AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.sizeOf_spec AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.injEq AlgebraicCurve.adeleSingle_coe AlgebraicCurve.kaehlerResidueTermKFam_apply AlgebraicCurve.Place.LocalResidueData.mk.injEq AlgebraicCurve.Place.LocalResidueData.mk.sizeOf_spec AlgebraicCurve.Place.kw_ffgc_adicCompletionComapIntegers_coe AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.sizeOf_spec AlgebraicCurve.Place.mem_simplePoleSubmodule AlgebraicCurve.Place.coe_uniformizerSubring ModularCurve.Lg37.Lg37CompletionSection.mk.injEq AlgebraicCurve.Place.CoefficientFieldSection.mk.injEq AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.injEq ModularCurve.Lg37.Lg37CompletionSection.mk.sizeOf_spec AlgebraicCurve.Place.CoefficientFieldSection.mk.sizeOf_spec AlgebraicCurve.Place.poleSubmodule_one AlgebraicCurve.Place.mem_poleSubmodule AlgebraicGeometry.Scheme.Modules.toUnitSection_ofUnitSection AlgebraicGeometry.Scheme.Modules.pullbackSection_def AlgebraicGeometry.Scheme.Modules.ofUnitSection_toUnitSection PresheafOfModules.InternalHom.IsSheafAux.appAt_toPresheafHom SheafOfModules.ihomSectionsEquivFamily_unit AlgebraicGeometry.Scheme.Modules.restrictHomEquivFamily_apply SheafOfModules.ihomEval_unit_app AlgebraicGeometry.Scheme.Modules.ihomEval_zero_right AlgebraicGeometry.Scheme.Modules.ihomEval_zero_left AlgebraicGeometry.Scheme.Modules.homOfFamily_app_apply"
p2m_attr_erase "simp" "SheafOfModules.unit_ihomSectionsEquivFamily AlgebraicGeometry.Scheme.Modules.familyOfHom_app AlgebraicGeometry.Scheme.Modules.restrictUnitIso_hom_app_apply AlgebraicGeometry.Scheme.Modules.restrictUnitIso_inv_app_apply AlgebraicGeometry.Scheme.Modules.restrictHomOfFamily_app_apply AlgebraicGeometry.Scheme.Modules.restrictHomEquivFamily_symm_apply AlgebraicGeometry.Scheme.Modules.tensorSections_zero_right AlgebraicGeometry.Scheme.Modules.map_unitSection AlgebraicGeometry.Scheme.Modules.tensorSectionsBilin_apply AlgebraicGeometry.Scheme.Modules.tensorPowSection_zero AlgebraicGeometry.Scheme.Modules.tensorSections_zero_left AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_neg AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_zero AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_sub AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_add AlgebraicGeometry.Scheme.OrderedAffineCover.toCoverOf_U AlgebraicGeometry.Scheme.OrderedAffineCoverOf.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCoverOf.mk.injEq AlgebraicGeometry.Scheme.OrderedAffineCover.restrict_U AlgebraicGeometry.OModulePresheaf.Leray.restrictToPreimage_U DoubleComplex.Bounded.mk.injEq DoubleComplex.Bounded.mk.sizeOf_spec DoubleComplex.Convergence.mk.injEq DoubleComplex.Convergence.mk.sizeOf_spec DoubleComplex.SubQuot.mk.sizeOf_spec DoubleComplex.SubQuot.mk.injEq AlgebraicGeometry.ChowDatumProj.mk.sizeOf_spec AlgebraicGeometry.ChowDatum.mk.sizeOf_spec AlgebraicGeometry.ChowDatumProj.mk.injEq AlgebraicGeometry.ChowDatum.mk.injEq ProjSpaceCech.GradedModule.mk.injEq ProjSpaceCech.GradedModule.mk.sizeOf_spec ProjSpaceCech.GradedModule.Frac.mk.sizeOf_spec ProjSpaceCech.GradedModule.Presentation.mk.injEq ProjSpaceCech.GradedModule.Frac.mk.injEq ProjSpaceCech.GradedModule.Presentation.mk.sizeOf_spec ProjSpaceCech.GradedModule.Hom.shift_toLinearMap ProjSpaceCech.GradedModule.Hom.mk.sizeOf_spec ProjSpaceCech.GradedModule.Hom.mk.injEq TwoChartCech.Mumford.dK_apply"
p2m_attr_erase "simp" "TwoChartCech.Mumford.ι0_apply TwoChartCech.Mumford.ι1_apply TwoChartCech.KerCoprod.dK_apply TwoChartCech.KerCoprod.ι1_apply TwoChartCech.KerCoprod.ι0_apply AlgebraicGeometry.tilde.functorCompPullbackSpecIso_app AlgebraicGeometry.RelPicard.algEquivZeroGroupCut_toSubPicCondition AlgebraicGeometry.RelPicard.LFP.stageHom_val AlgebraicGeometry.RelPicard.BaseChange.relSubPicPresheafRestrictIso_hom_app_coe AlgebraicGeometry.RelPicard.BaseChange.relSubPicPresheafRestrictIso_inv_app_coe AlgebraicGeometry.RelPicard.BaseChange.restrict_P AlgebraicGeometry.RelEffCartierDiv.IsUniversal.lift_comp AlgebraicGeometry.RelEffCartierDiv.functor_map_fst AlgebraicGeometry.RelEffCartierDiv.IsUniversal.homEquiv_apply AlgebraicGeometry.RelEffCartierDiv.IsUniversal.lift_pullbackAlong AlgebraicGeometry.RelEffCartierDiv.IsUniversal.homEquiv_symm_apply AlgebraicGeometry.RelEffCartierDiv.IsUniversal.lift_comp_assoc AlgebraicGeometry.RelEffCartierDiv.supportedIn_top AlgebraicGeometry.RelEffCartierDiv.mem_supportedIn_iff AlgebraicGeometry.RelEffCartierDiv.supportedIn_top_eq AlgebraicGeometry.RelEffCartierDiv.restrictAlong_extendAlong AlgebraicGeometry.RelEffCartierDiv.extendAlong_I AlgebraicGeometry.RelEffCartierDiv.resProdMap_snd AlgebraicGeometry.RelEffCartierDiv.restrictAlong_I AlgebraicGeometry.RelEffCartierDiv.extendAlong_restrictAlong AlgebraicGeometry.RelEffCartierDiv.resProdMap_fst_assoc AlgebraicGeometry.RelEffCartierDiv.resProdMap_snd_assoc AlgebraicGeometry.RelEffCartierDiv.resProdMap_fst CoherentBaseChange.FibreH0Family.mk.sizeOf_spec CoherentBaseChange.FibreH0Family.mk.injEq AlgebraicGeometry.Scheme.Modules.ProjPresentation.mk.injEq AlgebraicGeometry.Scheme.Modules.ProjPresentation.mk.sizeOf_spec AlgebraicCurve.CurveModel.coe_gInf AlgebraicCurve.CurveModel.coe_tInvChart AlgebraicCurve.CurveModel.ιInf_gluedToBase_assoc AlgebraicCurve.CurveModel.ιInf_gluedToBase AlgebraicCurve.CurveModel.primeOfι₀_asIdeal AlgebraicCurve.CurveModel.coe_tChart AlgebraicCurve.CurveModel.ι₀_gluedToBase_assoc AlgebraicCurve.CurveModel.primeOfιInf_asIdeal"
p2m_attr_erase "simp" "AlgebraicCurve.CurveModel.ι₀_gluedToBase AlgebraicCurve.CurveModel.coe_tma AlgebraicCurve.CurveModel.coe_primeEquivChartPlaces RegularLocalRingQuotientAscent.dualNumberFst_apply AlgebraicGeometry.ProjSpace.twistObj.mk.injEq AlgebraicGeometry.ProjSpace.twistObj.zero_val AlgebraicGeometry.ProjSpace.twistObj.add_val AlgebraicGeometry.ProjSpace.twist_res_val AlgebraicGeometry.ProjSpace.twist_smul_val AlgebraicGeometry.ProjSpace.twistGradeToObj_val AlgebraicGeometry.ProjSpace.twistObj.smul_val AlgebraicGeometry.ProjSpace.twistGradeEquiv_apply_val AlgebraicGeometry.ProjSpace.twistObj.mk.sizeOf_spec QuaternionAlgebra.baseChangeRight_tmul QuaternionAlgebra.mapOfAlgebraMapEq_apply QuaternionAlgebra.baseChange_tmul QuaternionAlgebra.ClassSet.map_mk GoodReductionJacobian.RelativeGroupLaw.baseChangePointToBase_ofBase GoodReductionJacobian.RelativeGroupLaw.baseChangePointToBase_coe GoodReductionJacobian.RelativeGroupLaw.baseChangePointOfBase_coe GoodReductionJacobian.RelativeGroupLaw.baseChange_inv GoodReductionJacobian.RelativeGroupLaw.baseChangePointOfBase_toBase GoodReductionJacobian.RelativeGroupLaw.baseChange_mul GoodReductionJacobian.RelativeGroupLaw.baseChange_one NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_fst NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_snd NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_fst NeronSpecialFibreInfra.neronEndRestrictEquiv_apply NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_fst_assoc NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_snd NeronSpecialFibreInfra.neronEndExtension_genericFibreRestrict NeronSpecialFibreInfra.specClosedFibreInclusion_eq NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_fst_assoc NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_snd_assoc NeronSpecialFibreInfra.genericFibreRestrict_neronEndExtension NeronSpecialFibreInfra.homOverId_coe NeronSpecialFibreInfra.homOverComp_coe NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_snd_assoc GoodReductionJacobian.RelativeGroupLaw.fibre_inv GoodReductionJacobian.RelativeGroupLaw.fibrePointToBase_coe"
p2m_attr_erase "simp" "GoodReductionJacobian.RelativeGroupLaw.fibrePointOfBase_toBase GoodReductionJacobian.RelativeGroupLaw.fibre_mul GoodReductionJacobian.RelativeGroupLaw.fibrePointToBase_ofBase GoodReductionJacobian.RelativeGroupLaw.fibre_one GoodReductionJacobian.RelativeGroupLaw.fibrePointOfBase_coe AlgebraicGeometry.schemeFibreEndo_snd AlgebraicGeometry.schemeFibreEndo_fst"

set_option autoImplicit false

p2m_open "CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra~schemeHomOverComp~schemeHomOverComp_coe GoodReductionJacobian CerednikDrinfeld CerednikDrinfeld.QM QuaternionAlgebra"

open scoped Quaternion

noncomputable section

namespace P2mKcLevelTorsorEx

section General

variable {R : Type} [CommRing R] {A : Scheme.{0}} {f : A ⟶ Spec (CommRingCat.of R)} (L : RelativeGroupLaw R f)

theorem nsmulPt_eq_nsmul {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of R)) (n : ℕ) (P : SchemeHomOver t f) :
    nsmulPt L t n P = L.nsmul t n P := by
  induction n with
  | zero => rfl
  | succ n ih => rw [RelativeGroupLaw.nsmul_succ, ← ih]; rfl

theorem nsmulPt_natural {T T' : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of R)) (t' : T' ⟶ Spec (CommRingCat.of R))
    (ψ : T' ⟶ T) (hψ : ψ ≫ t = t') (n : ℕ) (x : SchemeHomOver t f) :
    schemeHomOverComp ψ hψ (nsmulPt L t n x) = nsmulPt L t' n (schemeHomOverComp ψ hψ x) := by
  rw [nsmulPt_eq_nsmul, nsmulPt_eq_nsmul, L.nsmul_natural]

variable {L}

def castPt {T : Scheme.{0}} {s s' : T ⟶ Spec (CommRingCat.of R)} (h : s = s') (P : SchemeHomOver s f) :
    SchemeHomOver s' f :=
  ⟨P.1, P.2.trans h⟩

@[scoped simp] theorem castPt_coe {T : Scheme.{0}} {s s' : T ⟶ Spec (CommRingCat.of R)} (h : s = s') (P : SchemeHomOver s f) :
    (castPt h P).1 = P.1 := rfl

theorem castPt_castPt_symm {T : Scheme.{0}} {s s' : T ⟶ Spec (CommRingCat.of R)} (h : s = s') (P : SchemeHomOver s' f) :
    castPt h (castPt h.symm P) = P := Subtype.ext rfl

theorem castPt_symm_castPt {T : Scheme.{0}} {s s' : T ⟶ Spec (CommRingCat.of R)} (h : s = s') (P : SchemeHomOver s f) :
    castPt h.symm (castPt h P) = P := Subtype.ext rfl

variable (L)

theorem nsmulPt_castPt {T : Scheme.{0}} {s s' : T ⟶ Spec (CommRingCat.of R)} (h : s = s') (n : ℕ) (P : SchemeHomOver s f) :
    nsmulPt L s' n (castPt h P) = castPt h (nsmulPt L s n P) := by
  subst h; rfl

theorem one_castPt {T : Scheme.{0}} {s s' : T ⟶ Spec (CommRingCat.of R)} (h : s = s') :
    L.one s' = castPt h (L.one s) := by
  subst h; rfl

end General

section Points

variable {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} {N : ℕ} {K : Type} [Field K]

@[scoped ext] structure Pt (E : FakeEllipticCurve Λ N K) : Type where

  val : SchemeHomOver (𝟙 (Spec (CommRingCat.of K))) E.f

namespace Pt

variable (E : FakeEllipticCurve Λ N K)

def equiv : Pt E ≃ SchemeHomOver (𝟙 (Spec (CommRingCat.of K))) E.f :=
  ⟨Pt.val, Pt.mk, fun _ => rfl, fun _ => rfl⟩

scoped instance : Zero (Pt E) := ⟨⟨E.L.one _⟩⟩

scoped instance : Add (Pt E) := ⟨fun P Q => ⟨E.L.mul _ P.val Q.val⟩⟩

scoped instance : Neg (Pt E) := ⟨fun P => ⟨E.L.inv _ P.val⟩⟩

scoped instance : AddCommGroup (Pt E) where
  add_assoc P Q S := Pt.ext (E.L.mul_assoc _ _ _ _)
  zero_add P := Pt.ext (E.L.one_mul _ _)
  add_zero P := Pt.ext (E.L.mul_one _ _)
  neg_add_cancel P := Pt.ext (E.L.inv_mul_cancel _ _)
  add_comm P Q := Pt.ext (E.comm _ _ _)
  nsmul := nsmulRec
  zsmul := zsmulRec

variable {E}

@[scoped simp] theorem val_add (P Q : Pt E) : (P + Q).val = E.L.mul _ P.val Q.val := rfl

@[scoped simp] theorem val_zero : (0 : Pt E).val = E.L.one _ := rfl

theorem val_nsmul (n : ℕ) (P : Pt E) : (n • P).val = nsmulPt E.L (𝟙 (Spec (CommRingCat.of K))) n P.val := by
  induction n with
  | zero => rw [zero_nsmul]; rfl
  | succ n ih =>
    rw [succ_nsmul, val_add, ih]
    rfl

end Pt
p2m_reactivate "P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_nonempty_fullLevel_of_isMaximalOrder.P2mKcLevelTorsorEx.Pt"

variable {E : FakeEllipticCurve Λ N K}

def ρ (x : ↥Λ) : Pt E →+ Pt E :=
  AddMonoidHom.mk' (fun P => ⟨pushPt (E.act x) (E.act_over x) P.val⟩) fun P Q => Pt.ext (E.act_hom x _ P.val Q.val)

@[scoped simp] theorem val_ρ (x : ↥Λ) (P : Pt E) : (ρ x P).val = pushPt (E.act x) (E.act_over x) P.val := rfl

theorem ρ_add (x y : ↥Λ) (P : Pt E) : ρ (x + y) P = ρ x P + ρ y P :=
  Pt.ext (E.act_add x y _ P.val)

def evalPt (P : Pt E) : ↥Λ →+ Pt E :=
  AddMonoidHom.mk' (fun x => ρ x P) fun x y => ρ_add x y P

theorem ρ_nsmul_left (k : ℕ) (x : ↥Λ) (P : Pt E) : ρ (k • x) P = k • ρ x P :=
  map_nsmul (evalPt P) k x

theorem ρ_zsmul_left (k : ℤ) (x : ↥Λ) (P : Pt E) : ρ (k • x) P = k • ρ x P :=
  map_zsmul (evalPt P) k x

theorem coe_natCast_mul (n : ℕ) (y : ↥Λ) :
    ((n : ℚ) : ℍ[ℚ, a, b]) * (y : ℍ[ℚ, a, b]) = ((n • y : ↥Λ) : ℍ[ℚ, a, b]) := by
  rw [AddSubmonoidClass.coe_nsmul, coe_natCast, nsmul_eq_mul]

theorem eq_nsmul_of_coe_eq {n : ℕ} {x y : ↥Λ} (h : (x : ℍ[ℚ, a, b]) = ((n : ℚ) : ℍ[ℚ, a, b]) * (y : ℍ[ℚ, a, b])) :
    x = n • y :=
  Subtype.ext (by rw [h, coe_natCast_mul])

structure IsGen (n : ℕ) (P : Pt E) : Prop where
  tors : n • P = 0
  gen : ∀ Q : Pt E, n • Q = 0 → ∃ x : ↥Λ, Q = ρ x P
  ann : ∀ x : ↥Λ, ρ x P = 0 ↔ ∃ y : ↥Λ, (x : ℍ[ℚ, a, b]) = ((n : ℚ) : ℍ[ℚ, a, b]) * (y : ℍ[ℚ, a, b])

theorem ρ_eq_zero_of_coe_eq {n : ℕ} {P : Pt E} (hP : n • P = 0) {x y : ↥Λ}
    (h : (x : ℍ[ℚ, a, b]) = ((n : ℚ) : ℍ[ℚ, a, b]) * (y : ℍ[ℚ, a, b])) : ρ x P = 0 := by
  rw [eq_nsmul_of_coe_eq h, ρ_nsmul_left, ← map_nsmul, hP, map_zero]

theorem isGen_one : IsGen 1 (0 : Pt E) where
  tors := nsmul_zero _
  gen Q hQ := ⟨0, by rw [one_nsmul] at hQ; rw [hQ, map_zero]⟩
  ann x := ⟨fun _ => ⟨x, by rw [Nat.cast_one, coe_one, one_mul]⟩, fun _ => map_zero _⟩

theorem exists_isGen_prime {q q' : ℕ} [Fact q.Prime] [Fact q'.Prime] (hB : IsIndefiniteRamifiedExactlyAt a b q q')
    (hΛ : IsMaximalOrder Λ) [IsAlgClosed K] (E : FakeEllipticCurve Λ N K) (p : ℕ) [Fact p.Prime] (hp : (p : K) ≠ 0) :
    ∃ P : Pt E, IsGen p P := by
  obtain ⟨P₀, h1, h2, h3⟩ :=
    CerednikDrinfeld.QM.FakeEllipticCurve.exists_generator_torsionPoints_of_isMaximalOrder_of_prime hB Λ hΛ K E p hp
  refine ⟨⟨P₀⟩, ⟨?_, ?_, ?_⟩⟩
  · exact Pt.ext (by rw [Pt.val_nsmul]; exact h1)
  · intro Q hQ
    obtain ⟨x, hx⟩ := h2 Q.val (by rw [← Pt.val_nsmul, hQ]; rfl)
    exact ⟨x, Pt.ext hx⟩
  · intro x
    rw [← h3 x]
    exact ⟨fun h => congrArg Pt.val h, fun h => Pt.ext h⟩

theorem isGen_pow_of_nsmul_eq {p : ℕ} {P₁ : Pt E} (h₁ : IsGen p P₁) :
    ∀ (d : ℕ) (P : Pt E), p ^ (d + 1) • P = 0 → p ^ d • P = P₁ → IsGen (p ^ (d + 1)) P := by
  intro d
  induction d with
  | zero =>
    intro P _ hP
    rw [pow_zero, one_nsmul] at hP
    subst hP
    simpa using h₁
  | succ d ih =>
    intro P hP0 hP1

    have hP' : IsGen (p ^ (d + 1)) (p • P) := by
      refine ih (p • P) ?_ ?_
      · rw [← mul_nsmul, ← pow_succ', hP0]
      · rw [← mul_nsmul, ← pow_succ', hP1]
    refine ⟨hP0, ?_, ?_⟩
    ·
      intro Q hQ
      have hQ' : p • (p ^ (d + 1) • Q) = 0 := by rw [← mul_nsmul, ← pow_succ, hQ]
      obtain ⟨x, hx⟩ := h₁.gen _ hQ'
      have hd : p ^ (d + 1) • (Q - ρ x P) = 0 := by
        rw [nsmul_sub, hx, ← hP1, map_nsmul, sub_self]
      obtain ⟨y, hy⟩ := hP'.gen _ hd
      refine ⟨p • y + x, ?_⟩
      rw [ρ_add, ρ_nsmul_left, ← map_nsmul, ← hy, sub_add_cancel]
    ·
      intro x
      constructor
      · intro hx0
        have hx1 : ρ x P₁ = 0 := by rw [← hP1, map_nsmul, hx0, nsmul_zero]
        obtain ⟨y, hy⟩ := (h₁.ann x).mp hx1
        have hy0 : ρ y (p • P) = 0 := by
          rw [map_nsmul, ← ρ_nsmul_left, ← eq_nsmul_of_coe_eq hy, hx0]
        obtain ⟨z, hz⟩ := (hP'.ann y).mp hy0
        refine ⟨z, ?_⟩
        rw [hy, hz, ← mul_assoc, ← coe_mul, ← Nat.cast_mul, ← pow_succ']
      · rintro ⟨y, hy⟩
        exact ρ_eq_zero_of_coe_eq hP0 hy

theorem mul_natCast_zsmul_eq_zero {S : Pt E} {k : ℕ} (hS : k • S = 0) (c : ℤ) : (c * (k : ℤ)) • S = 0 := by
  rw [mul_smul, natCast_zsmul, hS, smul_zero]

theorem zsmul_eq_self_of_bezout {S : Pt E} {m n : ℕ} (hS : m • S = 0) {u v : ℤ} (huv : u * m + v * n = 1) :
    (v * (n : ℤ)) • S = S := by
  have : (v * (n : ℤ)) = 1 - u * (m : ℤ) := by linarith
  rw [this, sub_smul, one_smul, mul_natCast_zsmul_eq_zero hS, sub_zero]

theorem isGen_mul {m n : ℕ} (hmn : m.Coprime n) {P₁ P₂ : Pt E} (h₁ : IsGen m P₁) (h₂ : IsGen n P₂) :
    IsGen (m * n) (P₁ + P₂) := by

  obtain ⟨u, v, huv⟩ : ∃ u v : ℤ, u * m + v * n = 1 := by
    refine ⟨m.gcdA n, m.gcdB n, ?_⟩
    have h := Nat.gcd_eq_gcd_ab m n
    rw [Nat.Coprime.gcd_eq_one hmn] at h
    push_cast at h
    linarith
  have huv' : v * n + u * m = 1 := by linarith
  have htors : (m * n) • (P₁ + P₂) = 0 := by
    rw [nsmul_add, mul_nsmul, h₁.tors, nsmul_zero, zero_add, mul_comm m n, mul_nsmul, h₂.tors, nsmul_zero]
  refine ⟨htors, ?_, ?_⟩
  ·
    intro Q hQ
    have hQn : m • (n • Q) = 0 := by rw [← mul_nsmul, mul_comm, hQ]
    have hQm : n • (m • Q) = 0 := by rw [← mul_nsmul, hQ]
    obtain ⟨x₁, hx₁⟩ := h₁.gen _ hQn
    obtain ⟨x₂, hx₂⟩ := h₂.gen _ hQm
    refine ⟨(v * (n : ℤ)) • (v • x₁) + (u * (m : ℤ)) • (u • x₂), ?_⟩
    have e₁ : ρ ((v * (n : ℤ)) • (v • x₁) + (u * (m : ℤ)) • (u • x₂)) P₁ = v • ρ x₁ P₁ := by
      rw [ρ_add, ρ_zsmul_left (v * (n : ℤ)) (v • x₁) P₁, ρ_zsmul_left (u * (m : ℤ)) (u • x₂) P₁,
        zsmul_eq_self_of_bezout (by rw [← map_nsmul, h₁.tors, map_zero]) huv,
        mul_natCast_zsmul_eq_zero (by rw [← map_nsmul, h₁.tors, map_zero]), add_zero, ρ_zsmul_left]
    have e₂ : ρ ((v * (n : ℤ)) • (v • x₁) + (u * (m : ℤ)) • (u • x₂)) P₂ = u • ρ x₂ P₂ := by
      rw [ρ_add, ρ_zsmul_left (v * (n : ℤ)) (v • x₁) P₂, ρ_zsmul_left (u * (m : ℤ)) (u • x₂) P₂,
        mul_natCast_zsmul_eq_zero (by rw [← map_nsmul, h₂.tors, map_zero]),
        zsmul_eq_self_of_bezout (by rw [← map_nsmul, h₂.tors, map_zero]) huv', zero_add, ρ_zsmul_left]
    rw [map_add, e₁, e₂, ← hx₁, ← hx₂, ← natCast_zsmul, ← natCast_zsmul, smul_smul, smul_smul, ← add_smul, huv',
      one_smul]
  ·
    intro x
    constructor
    · intro hx
      have hx' : ρ x P₁ + ρ x P₂ = 0 := by rw [← map_add, hx]

      have hn₁ : ρ (n • x) P₁ = 0 := by
        have h := congrArg (fun S => n • S) hx'
        simp only [nsmul_add, nsmul_zero] at h
        rwa [← map_nsmul (ρ x) n P₂, h₂.tors, map_zero, add_zero, ← ρ_nsmul_left] at h
      have hm₂ : ρ (m • x) P₂ = 0 := by
        have h := congrArg (fun S => m • S) hx'
        simp only [nsmul_add, nsmul_zero] at h
        rwa [← map_nsmul (ρ x) m P₁, h₁.tors, map_zero, zero_add, ← ρ_nsmul_left] at h
      obtain ⟨z₁, hz₁⟩ := (h₁.ann _).mp hn₁
      obtain ⟨z₂, hz₂⟩ := (h₂.ann _).mp hm₂

      rw [AddSubmonoidClass.coe_nsmul, ← Nat.cast_smul_eq_nsmul ℚ, coe_mul_eq_smul] at hz₁ hz₂
      have huvQ : (u : ℚ) * (m : ℚ) + (v : ℚ) * (n : ℚ) = 1 := by exact_mod_cast huv
      refine ⟨u • (u • z₂ + v • x) + v • (u • x + v • z₁), ?_⟩
      rw [coe_mul_eq_smul]
      simp only [Submodule.coe_add, Submodule.coe_smul_of_tower, ← Int.cast_smul_eq_zsmul ℚ]
      push_cast
      linear_combination (norm := module) ((u : ℚ) ^ 2 * (m : ℚ)) • hz₂ + ((v : ℚ) ^ 2 * (n : ℚ)) • hz₁
        + (congrArg (fun r : ℚ => 1 - r ^ 2) huvQ) • (x : ℍ[ℚ, a, b])
    · rintro ⟨y, hy⟩
      exact ρ_eq_zero_of_coe_eq htors hy

omit [Field K] in
theorem preimage_base_singleton_eq_univ {K : Type} [Field K] {A : Scheme.{0}} (f : A ⟶ Spec (CommRingCat.of K))
    (s : ↥(Spec (CommRingCat.of K))) : f.base ⁻¹' {s} = Set.univ := by
  haveI : Subsingleton ↥(Spec (CommRingCat.of K)) := inferInstanceAs (Subsingleton (PrimeSpectrum K))
  exact Set.eq_univ_of_forall fun _ => Subsingleton.elim _ _

theorem connectedSpace_A (E : FakeEllipticCurve Λ N K) : ConnectedSpace E.A := by
  have h := E.bundle.connectedFibres (IsLocalRing.closedPoint K)
  rw [preimage_base_singleton_eq_univ] at h
  exact connectedSpace_iff_univ.mpr h

theorem nsmul_surjective [IsAlgClosed K] (E : FakeEllipticCurve Λ N K) (n : ℕ) (hn : (n : K) ≠ 0) :
    Function.Surjective fun P : Pt E => n • P := by
  haveI : Smooth E.f := E.bundle.smooth
  haveI : ConnectedSpace E.A := connectedSpace_A E
  intro Q
  obtain ⟨P, hP⟩ := RelativeGroupLaw.nsmul_surjective_of_isAlgClosed_of_connectedSpace E.L (fun t x y => E.comm t x y)
    n (isUnit_iff_ne_zero.mpr hn) Q.val
  exact ⟨⟨P⟩, Pt.ext (by rw [Pt.val_nsmul, nsmulPt_eq_nsmul]; exact hP)⟩

theorem natCard_torsion [IsAlgClosed K] (E : FakeEllipticCurve Λ N K) (n : ℕ) (hn : (n : K) ≠ 0) :
    Nat.card {P : Pt E // n • P = 0} = n ^ 4 := by
  haveI := CerednikDrinfeld.QM.FakeEllipticCurve.smoothOfRelativeDimension_two K E
  have h := RelativeGroupLaw.natCard_isTorsionPoint_eq_pow_of_natCast_ne_zero K E.f E.L E.comm E.bundle 2 n hn
  rw [show (4 : ℕ) = 2 * 2 from rfl, ← h]
  apply Nat.card_congr
  refine (Pt.equiv E).subtypeEquiv fun P => ?_
  rw [RelativeGroupLaw.isTorsionPoint_def, ← nsmulPt_eq_nsmul, Pt.ext_iff, Pt.val_nsmul]
  rfl

theorem exists_isGen_primePow {q q' : ℕ} [Fact q.Prime] [Fact q'.Prime] (hB : IsIndefiniteRamifiedExactlyAt a b q q')
    (hΛ : IsMaximalOrder Λ) [IsAlgClosed K] (E : FakeEllipticCurve Λ N K) {p : ℕ} (hp : p.Prime) (hpK : (p : K) ≠ 0)
    (e : ℕ) : ∃ P : Pt E, IsGen (p ^ e) P := by
  haveI := Fact.mk hp
  obtain ⟨P₁, h₁⟩ := exists_isGen_prime hB hΛ E p hpK
  cases e with
  | zero => exact ⟨0, by simpa using (isGen_one (E := E))⟩
  | succ d =>
    obtain ⟨P, hP⟩ := nsmul_surjective E (p ^ d) (by rw [Nat.cast_pow]; exact pow_ne_zero d hpK) P₁
    refine ⟨P, isGen_pow_of_nsmul_eq h₁ d P ?_ hP⟩
    change p ^ d • P = P₁ at hP
    rw [pow_succ, mul_nsmul, hP, h₁.tors]

theorem exists_isGen {q q' : ℕ} [Fact q.Prime] [Fact q'.Prime] (hB : IsIndefiniteRamifiedExactlyAt a b q q')
    (hΛ : IsMaximalOrder Λ) [IsAlgClosed K] (E : FakeEllipticCurve Λ N K) :
    ∀ n : ℕ, (n : K) ≠ 0 → ∃ P : Pt E, IsGen n P := by
  intro n
  induction n using Nat.recOnPosPrimePosCoprime with
  | prime_pow p e hp he =>
    intro h
    refine exists_isGen_primePow hB hΛ E hp (fun h0 => h ?_) e
    rw [Nat.cast_pow, h0, zero_pow he.ne']
  | zero => intro h; exact absurd Nat.cast_zero h
  | one => intro _; exact ⟨0, isGen_one⟩
  | coprime m n _ _ hmn ihm ihn =>
    intro h
    rw [Nat.cast_mul] at h
    obtain ⟨P₁, h₁⟩ := ihm (left_ne_zero_of_mul h)
    obtain ⟨P₂, h₂⟩ := ihn (right_ne_zero_of_mul h)
    exact ⟨P₁ + P₂, isGen_mul hmn h₁ h₂⟩

omit [Field K] in

theorem eq_of_apply_closedPoint_eq {K : Type} [Field K] {X : Scheme.{0}} (f : X ⟶ Spec (CommRingCat.of K))
    (x y : Spec (CommRingCat.of K) ⟶ X) (hx : x ≫ f = 𝟙 _) (hy : y ≫ f = 𝟙 _)
    (h : x.base (IsLocalRing.closedPoint K) = y.base (IsLocalRing.closedPoint K)) : x = y := by
  set p := x.base (IsLocalRing.closedPoint K) with hp
  have hxdec := X.descResidueField_stalkClosedPointTo_fromSpecResidueField K x
  have hydec := X.descResidueField_stalkClosedPointTo_fromSpecResidueField K y
  set φx : X.residueField p ⟶ CommRingCat.of K := X.descResidueField (Scheme.stalkClosedPointTo x) with hφx
  set φy' : X.residueField (y.base (IsLocalRing.closedPoint K)) ⟶ CommRingCat.of K :=
    X.descResidueField (Scheme.stalkClosedPointTo y) with hφy'
  set φy : X.residueField p ⟶ CommRingCat.of K := (X.residueFieldCongr h).hom ≫ φy' with hφy
  have hy' : Spec.map φy ≫ X.fromSpecResidueField p = y := by
    rw [hφy, Spec.map_comp, Category.assoc, Scheme.residueFieldCongr_fromSpecResidueField]
    · exact hydec
  have hx' : Spec.map φx ≫ X.fromSpecResidueField p = x := hxdec
  set G : Spec (X.residueField p) ⟶ Spec (CommRingCat.of K) := X.fromSpecResidueField p ≫ f with hG
  set g : CommRingCat.of K ⟶ X.residueField p := Spec.preimage G with hg
  have hGg : Spec.map g = G := Spec.map_preimage G
  have hgx : g ≫ φx = 𝟙 _ := by
    apply Spec.map_injective
    rw [Spec.map_comp, Spec.map_id, hGg, hG, ← Category.assoc, hx', hx]
  have hgy : g ≫ φy = 𝟙 _ := by
    apply Spec.map_injective
    rw [Spec.map_comp, Spec.map_id, hGg, hG, ← Category.assoc, hy', hy]
  have hφ : φx = φy := by
    ext z
    have hinj : Function.Injective φx.hom := RingHom.injective _
    have h1 : φx.hom (g.hom (φx.hom z)) = φx.hom z := by
      change (g ≫ φx).hom (φx.hom z) = φx.hom z
      rw [hgx]; rfl
    have h2 : g.hom (φx.hom z) = z := hinj h1
    have h3 : φy.hom (g.hom (φx.hom z)) = φx.hom z := by
      change (g ≫ φy).hom (φx.hom z) = φx.hom z
      rw [hgy]; rfl
    rw [h2] at h3
    exact h3.symm
  rw [← hx', ← hy', hφ]

theorem sectionAt_injective (E : FakeEllipticCurve Λ N K) (K' : Type) [Field K'] (sk : K →+* K')
    {P Q : SchemeHomOver (𝟙 (Spec (CommRingCat.of K))) E.f}
    (h : FakeEllipticCurve.sectionAt P K' sk = FakeEllipticCurve.sectionAt Q K' sk) : P = Q := by
  have h1 : geomPoint K' sk ≫ P.1 = geomPoint K' sk ≫ Q.1 := congrArg Subtype.val h
  apply Subtype.ext
  apply eq_of_apply_closedPoint_eq E.f P.1 Q.1 P.2 Q.2
  have hc : (geomPoint K' sk).base (IsLocalRing.closedPoint K') = IsLocalRing.closedPoint K := by
    haveI : Subsingleton ↥(Spec (CommRingCat.of K)) := inferInstanceAs (Subsingleton (PrimeSpectrum K))
    exact Subsingleton.elim _ _
  have h2 := congrArg (fun φ => φ.base (IsLocalRing.closedPoint K')) h1
  simp only [Scheme.Hom.comp_base, TopCat.coe_comp, Function.comp_apply] at h2
  rwa [hc] at h2

theorem sectionAt_val_nsmul (K' : Type) [Field K'] (sk : K →+* K') (n : ℕ) (P : Pt E) :
    FakeEllipticCurve.sectionAt (n • P).val K' sk = nsmulPt E.L (geomPoint K' sk) n (FakeEllipticCurve.sectionAt P.val K' sk) := by
  unfold FakeEllipticCurve.sectionAt
  rw [Pt.val_nsmul, nsmulPt_natural]

theorem sectionAt_val_zero (K' : Type) [Field K'] (sk : K →+* K') :
    FakeEllipticCurve.sectionAt (0 : Pt E).val K' sk = E.L.one (geomPoint K' sk) := by
  unfold FakeEllipticCurve.sectionAt
  rw [Pt.val_zero, E.L.one_natural]

theorem sectionAt_val_ρ (K' : Type) [Field K'] (sk : K →+* K') (x : ↥Λ) (P : Pt E) :
    FakeEllipticCurve.sectionAt (ρ x P).val K' sk = pushPt (E.act x) (E.act_over x) (FakeEllipticCurve.sectionAt P.val K' sk) := by
  apply Subtype.ext
  simp only [FakeEllipticCurve.sectionAt, schemeHomOverComp_coe, val_ρ, mapPt_coe, Category.assoc]

end Points
p2m_reactivate "P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_nonempty_fullLevel_of_isMaximalOrder.P2mKcLevelTorsorEx.Pt"

section Square

variable {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} {N : ℕ} {S S' : Type} [CommRing S] [CommRing S'] {φ : S →+* S'}
  {E : FakeEllipticCurve Λ N S} {E' : FakeEllipticCurve Λ N S'} {g : E'.A ⟶ E.A}
  (hg : CategoryTheory.IsPullback g E'.f E.f (Spec.map (CommRingCat.ofHom φ)))

def gPt {T : Scheme.{0}} {t' : T ⟶ Spec (CommRingCat.of S')} (P : SchemeHomOver t' E'.f) :
    SchemeHomOver (t' ≫ Spec.map (CommRingCat.ofHom φ)) E.f :=
  ⟨P.1 ≫ g, by rw [Category.assoc, hg.w, ← Category.assoc, P.2]⟩

@[scoped simp] theorem gPt_coe {T : Scheme.{0}} {t' : T ⟶ Spec (CommRingCat.of S')} (P : SchemeHomOver t' E'.f) :
    (gPt hg P).1 = P.1 ≫ g := rfl

theorem gPt_injective {T : Scheme.{0}} {t' : T ⟶ Spec (CommRingCat.of S')} {P Q : SchemeHomOver t' E'.f}
    (h : gPt hg P = gPt hg Q) : P = Q := by
  apply Subtype.ext
  exact hg.hom_ext (congrArg Subtype.val h) (P.2.trans Q.2.symm)

def liftPt {T : Scheme.{0}} {t' : T ⟶ Spec (CommRingCat.of S')} (Q : SchemeHomOver (t' ≫ Spec.map (CommRingCat.ofHom φ)) E.f) :
    SchemeHomOver t' E'.f :=
  ⟨hg.lift Q.1 t' Q.2, hg.lift_snd _ _ _⟩

theorem gPt_liftPt {T : Scheme.{0}} {t' : T ⟶ Spec (CommRingCat.of S')}
    (Q : SchemeHomOver (t' ≫ Spec.map (CommRingCat.ofHom φ)) E.f) : gPt hg (liftPt hg Q) = Q := by
  apply Subtype.ext
  simp [gPt, liftPt]

theorem liftPt_gPt {T : Scheme.{0}} {t' : T ⟶ Spec (CommRingCat.of S')} (P : SchemeHomOver t' E'.f) :
    liftPt hg (gPt hg P) = P :=
  gPt_injective hg (gPt_liftPt hg _)

variable
  (hmul : ∀ {T : Scheme.{0}} (t' : T ⟶ Spec (CommRingCat.of S')) (P Q : SchemeHomOver t' E'.f),
    (E'.L.mul t' P Q).1 ≫ g =
      (E.L.mul (t' ≫ Spec.map (CommRingCat.ofHom φ))
        ⟨P.1 ≫ g, by rw [Category.assoc, hg.w, ← Category.assoc, P.2]⟩
        ⟨Q.1 ≫ g, by rw [Category.assoc, hg.w, ← Category.assoc, Q.2]⟩).1)

include hmul

theorem gPt_mul {T : Scheme.{0}} (t' : T ⟶ Spec (CommRingCat.of S')) (P Q : SchemeHomOver t' E'.f) :
    gPt hg (E'.L.mul t' P Q) = E.L.mul _ (gPt hg P) (gPt hg Q) :=
  Subtype.ext (hmul t' P Q)

theorem gPt_one {T : Scheme.{0}} (t' : T ⟶ Spec (CommRingCat.of S')) :
    gPt hg (E'.L.one t') = E.L.one _ := by
  letI := E.L.pointGroup (t' ≫ Spec.map (CommRingCat.ofHom φ))
  have h := gPt_mul hg hmul t' (E'.L.one t') (E'.L.one t')
  rw [E'.L.one_mul] at h
  have : gPt hg (E'.L.one t') * gPt hg (E'.L.one t') = gPt hg (E'.L.one t') * 1 := by
    rw [mul_one]; exact h.symm
  exact mul_left_cancel this

theorem gPt_nsmul {T : Scheme.{0}} (t' : T ⟶ Spec (CommRingCat.of S')) (n : ℕ) (P : SchemeHomOver t' E'.f) :
    gPt hg (nsmulPt E'.L t' n P) = nsmulPt E.L _ n (gPt hg P) := by
  induction n with
  | zero => exact gPt_one hg hmul t'
  | succ n ih =>
    show gPt hg (E'.L.mul t' (nsmulPt E'.L t' n P) P) = E.L.mul _ (nsmulPt E.L _ n (gPt hg P)) (gPt hg P)
    rw [gPt_mul hg hmul, ih]

end Square
p2m_reactivate "P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_nonempty_fullLevel_of_isMaximalOrder.P2mKcLevelTorsorEx.Pt"

section Transfer

variable {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} {N : ℕ} {K : Type} [Field K]

theorem exists_sectionAt_eq_of_torsion [IsAlgClosed K] (E : FakeEllipticCurve Λ N K) (n : ℕ) (hn : (n : K) ≠ 0)
    (K' : Type) [Field K'] [IsAlgClosed K'] (sk : K →+* K')
    (Q : SchemeHomOver (geomPoint K' sk) E.f) (hQ : nsmulPt E.L (geomPoint K' sk) n Q = E.L.one (geomPoint K' sk)) :
    ∃ P : Pt E, n • P = 0 ∧ FakeEllipticCurve.sectionAt P.val K' sk = Q := by
  have hn' : (n : K') ≠ 0 := by
    intro h0
    apply hn
    apply sk.injective
    rw [map_natCast, map_zero, h0]
  have hn0 : n ≠ 0 := by rintro rfl; exact hn Nat.cast_zero

  obtain ⟨E', g, hg, hmul, -, -, -⟩ := CerednikDrinfeld.QM.FakeEllipticCurve.exists_isPullback_levelIff sk E
  have hb : 𝟙 (Spec (CommRingCat.of K')) ≫ Spec.map (CommRingCat.ofHom sk) = geomPoint K' sk := Category.id_comp _

  let Sg := {Q : SchemeHomOver (geomPoint K' sk) E.f // nsmulPt E.L (geomPoint K' sk) n Q = E.L.one (geomPoint K' sk)}
  let e : {P' : Pt E' // n • P' = 0} ≃ Sg :=
    { toFun := fun P' => ⟨castPt hb (gPt hg P'.1.val), by
        rw [nsmulPt_castPt, ← gPt_nsmul hg hmul, ← Pt.val_nsmul, P'.2, Pt.val_zero, gPt_one hg hmul, ← one_castPt]⟩
      invFun := fun Q => ⟨⟨liftPt hg (castPt hb.symm Q.1)⟩, by
        apply Pt.ext
        apply gPt_injective hg
        rw [Pt.val_nsmul, gPt_nsmul hg hmul, gPt_liftPt, nsmulPt_castPt, Q.2, Pt.val_zero, gPt_one hg hmul,
          ← one_castPt]⟩
      left_inv := fun P' => by
        apply Subtype.ext; apply Pt.ext
        simp only [castPt_symm_castPt, liftPt_gPt]
      right_inv := fun Q => by
        apply Subtype.ext
        simp only [gPt_liftPt, castPt_castPt_symm] }
  have hcardg : Nat.card Sg = n ^ 4 := by rw [← Nat.card_congr e, natCard_torsion E' n hn']
  have hcardk : Nat.card {P : Pt E // n • P = 0} = n ^ 4 := natCard_torsion E n hn
  haveI : Finite Sg := Nat.finite_of_card_ne_zero (by rw [hcardg]; exact pow_ne_zero _ hn0)

  let σ : {P : Pt E // n • P = 0} → Sg := fun P => ⟨FakeEllipticCurve.sectionAt P.1.val K' sk, by
    rw [← sectionAt_val_nsmul, P.2, sectionAt_val_zero]⟩
  have hσ : Function.Injective σ := by
    intro P₁ P₂ h
    apply Subtype.ext; apply Pt.ext
    exact sectionAt_injective E K' sk (congrArg Subtype.val h)
  have hbij := hσ.bijective_of_nat_card_le (by rw [hcardg, hcardk])
  obtain ⟨P, hP⟩ := hbij.2 ⟨Q, hQ⟩
  exact ⟨P.1, P.2, congrArg Subtype.val hP⟩

end Transfer
p2m_reactivate "P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_nonempty_fullLevel_of_isMaximalOrder.P2mKcLevelTorsorEx.Pt"

theorem main {a b : ℚ} {q q' : ℕ} [Fact q.Prime] [Fact q'.Prime] (hB : IsIndefiniteRamifiedExactlyAt a b q q')
    (Λ : Submodule ℤ ℍ[ℚ, a, b]) (hΛ : IsMaximalOrder Λ) {N : ℕ} (m : ℕ)
    (k : Type) [Field k] [IsAlgClosed k] (hm : (m : k) ≠ 0)
    (E : FakeEllipticCurve Λ N k) :
    Nonempty (E.FullLevel m) := by
  obtain ⟨P₀, hP₀⟩ := exists_isGen hB hΛ E m hm
  refine ⟨{ P := P₀.val, torsion := ?_, generates := ?_, annihilator := ?_ }⟩
  · rw [← Pt.val_nsmul, hP₀.tors, Pt.val_zero]
  · intro K _ _ sk Q hQ
    obtain ⟨P, hP, hPQ⟩ := exists_sectionAt_eq_of_torsion E m hm K sk Q hQ
    obtain ⟨x, rfl⟩ := hP₀.gen P hP
    exact ⟨x, by rw [← hPQ, sectionAt_val_ρ]⟩
  · intro K _ _ sk x
    rw [← sectionAt_val_ρ, ← sectionAt_val_zero (E := E) K sk]
    constructor
    · intro h
      have h' : ρ x P₀ = 0 := Pt.ext (sectionAt_injective E K sk h)
      obtain ⟨y, hy⟩ := (hP₀.ann x).mp h'
      exact ⟨y, by rw [hy, coe_mul_eq_smul]⟩
    · rintro ⟨y, hy⟩
      have h' : ρ x P₀ = 0 := (hP₀.ann x).mpr ⟨y, by rw [hy, coe_mul_eq_smul]⟩
      rw [h']

end P2mKcLevelTorsorEx
p2m_reactivate "P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_nonempty_fullLevel_of_isMaximalOrder.P2mKcLevelTorsorEx.Pt P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_nonempty_fullLevel_of_isMaximalOrder.P2mKcLevelTorsorEx"

end
p2m_reactivate "P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_nonempty_fullLevel_of_isMaximalOrder.P2mKcLevelTorsorEx.Pt P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_nonempty_fullLevel_of_isMaximalOrder.P2mKcLevelTorsorEx"

theorem solution
    {a b : ℚ} {q q' : ℕ} [Fact q.Prime] [Fact q'.Prime] (hB : IsIndefiniteRamifiedExactlyAt a b q q')
    (Λ : Submodule ℤ ℍ[ℚ, a, b]) (hΛ : IsMaximalOrder Λ) {N : ℕ} (m : ℕ)
    (k : Type) [Field k] [IsAlgClosed k] (hm : (m : k) ≠ 0)
    (E : FakeEllipticCurve Λ N k) :
    Nonempty (E.FullLevel m) :=
  P2mKcLevelTorsorEx.main hB Λ hΛ m k hm E

end S_CerednikDrinfeld_QM_FakeEllipticCurve_nonempty_fullLevel_of_isMaximalOrder
end P2MW
export P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_nonempty_fullLevel_of_isMaximalOrder (solution)
