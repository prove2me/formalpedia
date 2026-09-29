-- Prove2me | solution 1 for CerednikDrinfeld.QM.FakeEllipticCurve.exists_extraLevel_enum
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.837917+00:00
-- url     : https://prove2.me/submissions/f5bcdda4-17cc-583d-bdd6-1eddbe2566b9

import Definitions.Def_CerednikDrinfeld_QMModuliProps
import Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_exists_generator_torsionPoints_of_isMaximalOrder_of_prime
import Theorems.Thm_QuaternionAlgebra_IsMaximalOrder_lineImage_classification
import Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_exists_extraLevel_of_equiv_points
import Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_ExtraLevel_exists_equiv_points
import Theorems.Thm_QuaternionAlgebra_IsMaximalOrder_natCard_properLine_eq_and_inf_eq
import Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_natCard_properLine_image_subset_lev
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_exists_extraLevel_enum
p2m_attr_erase "instance" "GoodReductionJacobian.RelativeGroupLaw.isIso_endKerStr_schemeHomOverId AlgebraicGeometry.Scheme.PresheafOfModules.symmetricCategory SheafOfModules.instFaithfulRingSheafPModToPMod SheafOfModules.symmetricCategory AlgebraicGeometry.Scheme.PresheafOfModules.monoidalCategory AlgebraicGeometry.Scheme.PresheafOfModules.monoidalClosed SheafOfModules.instFullRingSheafPModToPMod SheafOfModules.monoidalCategory AlgebraicGeometry.Scheme.Modules.symmetricCategory SheafOfModules.monoidalClosed SheafOfModules.instIsLocalizationPModRingSheafSheafifyFunctorPresheafW SheafOfModules.sheafifyFunctor_monoidal AlgebraicGeometry.Scheme.Modules.monoidalClosed AlgebraicGeometry.instMonoidalPresheafOfModulesModulesSheafify AlgebraicGeometry.Scheme.Modules.monoidalCategory PresheafOfModules.instMonoidalClosed PresheafOfModules.InternalHom.instModuleCarrierObjOppositeCommRingCatSubtypePiFamilyMemAddSubgroupNaturalFamilies PresheafOfModules.InternalHom.instModuleCarrierObjOppositeRingCatCompCommRingCatForget₂RingHomCarrierCarrierAbPresheaf PresheafOfModules.InternalHom.instSMulCarrierObjOppositeCommRingCatSubtypePiFamilyMemAddSubgroupNaturalFamilies AlgebraicGeometry.Scheme.Hom.opensMapFinal AlgebraicGeometry.RelPicard.RigidifiedLineBundle.setoid AlgebraicGeometry.RelPicard.RigidifiedLineBundle.instInhabited AlgebraicGeometry.OModulePresheaf.isScalarTower AlgebraicGeometry.Scheme.OrderedAffineCover.instLinearOrder AlgebraicGeometry.OModulePresheaf.module AlgebraicGeometry.Scheme.OrderedAffineCover.instFintype AlgebraicGeometry.Scheme.OrderedAffineCover.instFintypeIdx AlgebraicGeometry.OModulePresheaf.addCommGroup AlgebraicGeometry.Scheme.OrderedAffineCover.instDecidableEqIdx AlgebraicGeometry.OModulePresheaf.moduleSections TwoChartCech.Sections.M0_moduleA TwoChartCech.Sections.M1_module TwoChartCech.Cover.A01_algebra TwoChartCech.Cover.A0_algebra TwoChartCech.Cover.A1_commRing TwoChartCech.Cover.A1_algebra TwoChartCech.Sections.M01_module TwoChartCech.Sections.M0_addCommGroup TwoChartCech.Sections.M0_tower TwoChartCech.Sections.M01_addCommGroup"
p2m_attr_erase "instance" "TwoChartCech.Cover.A0_commRing TwoChartCech.Sections.M1_tower TwoChartCech.Sections.M01_moduleA TwoChartCech.Sections.M0_module TwoChartCech.Sections.M1_moduleA TwoChartCech.Sections.M1_addCommGroup TwoChartCech.Cover.A01_commRing TwoChartCech.Sections.M01_tower CoherentBaseChange.TwoTermComplex.C0_module CoherentBaseChange.TwoTermComplex.C0_addCommGroup CoherentBaseChange.TwoTermComplex.C1_module CoherentBaseChange.TwoTermComplex.C1_addCommGroup CoherentBaseChange.TwoTermComplex.C0_free CoherentBaseChange.TwoTermComplex.C1_finite CoherentBaseChange.TwoTermComplex.C0_finite CoherentBaseChange.TwoTermComplex.C1_free AlgebraicGeometry.OModulePresheaf.instSubsingletonObjZero AlgebraicGeometry.Scheme.Modules.preservesBinaryProducts_opensMap AlgebraicGeometry.Scheme.Modules.pullback_monoidal AlgebraicGeometry.Scheme.Modules.sheafify_isLocalization' AlgebraicGeometry.Scheme.Modules.preservesTerminal_opensMap AlgebraicGeometry.Scheme.Modules.pullback₀_monoidal AlgebraicGeometry.Scheme.Modules.preservesFiniteProducts_opensMap AlgebraicGeometry.Scheme.Modules.instLiftingPresheafOfModulesSheafifyPresheafWOpensCarrierCarrierCommRingCatGrothendieckTopologyObjFunctorOppositeIsSheafSheafCompPullback₀Pullback PresheafOfModules.PullbackMonoidal.pullback_monoidal PresheafOfModules.PullbackMonoidal.isIso_δ PresheafOfModules.pushforward_laxMonoidal PresheafOfModules.PullbackMonoidal.isIso_η PresheafOfModules.free_monoidal PresheafOfModules.restrictScalars_laxMonoidal PresheafOfModules.PullbackMonoidal.isIso_δ_gS PresheafOfModules.pullback_oplaxMonoidal PresheafOfModules.PullbackMonoidal.instPreservesColimitsOfSizeCompOppositeCommRingCatRingCatForget₂RingHomCarrierCarrierPb PresheafOfModules.pullback_monoidal' AlgebraicGeometry.SmoothOfRelativeDimension.fiberToSpecResidueField AlgebraicGeometry.SmoothOfRelativeDimension.pullback_snd AlgebraicGeometry.SmoothOfRelativeDimension.pullback_fst AlgebraicGeometry.SmoothOfRelativeDimension.smooth_one AlgebraicGeometry.SmoothProperCurve.isIntegral_pullback_Spec_field AlgebraicGeometry.IsProper.fiberToSpecResidueField"
p2m_attr_erase "instance" "AlgebraicCurve.CurveModel.isProper AlgebraicCurve.CurveModel.isIntegral AlgebraicCurve.CurveModel.smooth AlgebraicGeometry.Scheme.LocalRepresentabilityULift.instIsLocallyInjectiveFunUliftYonedaGluedToSheaf AlgebraicGeometry.Scheme.LocalRepresentabilityULift.instIsLocallySurjectiveFunUliftYonedaGluedToSheafOfIsLocallySurjectiveZariskiTopologyDescFunctorOppositeType AlgebraicGeometry.Scheme.LocalRepresentabilityULift.instIsOpenImmersionToGlued AlgebraicGeometry.Scheme.LocalRepresentabilityULift.instIsIsoSheafZariskiTopologyTypeUliftYonedaGluedToSheaf AlgebraicGeometry.RelPicard.instIsOpenImmersionToGlued AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.instFundamentalIdentityOfSumRamificationInertia AlgebraicCurve.Place.instIsScalarTowerResidueFieldRestrictPushforward AlgebraicCurve.Place.instAlgebraResidueFieldRestrictPushforward AlgebraicCurve.Place.instIsLocalHomRestrictInclusion AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions PresheafOfModules.ExteriorPower.instModulePresheafAb AlgebraicGeometry.RelEffCartierDiv.subsingleton_of_degree_zero AlgebraicGeometry.RelEffCartierDiv.isIso_subschemeIota_snd_of_degree_one AlgebraicGeometry.isIso_ker_graphOver_subschemeIota_snd AlgebraicGeometry.isClosedImmersion_graphOver AlgebraicGeometry.FGSubalgebra.instIsDirectedLe AlgebraicGeometry.FGSubalgebra.instQuasiSeparatedSpaceCarrierCarrierCommRingCatObjOppositeSchemeSpecDiagram AlgebraicGeometry.FGSubalgebra.instIsCofilteredOpposite AlgebraicGeometry.FGSubalgebra.instIsAffineObjOppositeSchemeSpecDiagram AlgebraicGeometry.FGSubalgebra.instNonempty AlgebraicGeometry.FGSubalgebra.instNonemptySubtypeLeSubalgebraValFG AlgebraicGeometry.FGSubalgebra.instCompactSpaceCarrierCarrierCommRingCatObjOppositeSchemeSpecDiagram AlgebraicGeometry.FGSubalgebra.instIsDirectedSubtypeLeSubalgebraValFG AlgebraicGeometry.FGSubalgebra.instIsAffineHomMapOppositeSchemeSpecDiagram AlgebraicGeometry.FGSubalgebra.instIsFiltered AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instNeg AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instSMulInt AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instAddCommGroup AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instAdd AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instSub"
p2m_attr_erase "instance" "AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instModuleCarrierObjOppositeOpensCarrierCarrierCommRingCatPresheafOpOpensTop AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instSMulCarrierObjOppositeOpensCarrierCarrierCommRingCatPresheafOpOpensTop AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instSMulNat AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instZero AlgebraicCurve.instHasLocalResidue_of_hasCanonicalLocalResidueK AlgebraicCurve.instHasCanonicalLocalResidueK_of_hasCanonicalLocalResidueKStar AlgebraicCurve.Place.kw_ffgc_finiteDimensional_adicCompletion instAlgebraSubtypeMemValuationSubring_definitions AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersIntegersCompletion ModularCurve.KwF4gRRTate.instAlgebraKAdicCompletionIntegers AlgebraicCurve.Place.kw_ffgc_continuousSMul_adicCompletionComap AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersCompletionCompletion IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions AlgebraicCurve.instHasCanonicalLocalResidueK AlgebraicCurve.Place.instAlgebra_restrictResidueField AlgebraicCurve.Place.instIsScalarTower_restrictResidueField AlgebraicCurve.instHasLocalResidue AlgebraicCurve.HasSeparableResidue.of_perfectField_of_isCurveOver AlgebraicCurve.HasSeparableResidue.of_perfectField AlgebraicCurve.Place.instIsLocalHom_restrictSubringHom AlgebraicCurve.instHasCanonicalLocalResidueKStar ModularCurve.KwNo6Pin.isLocalRing_completion SheafOfModules.isIso_ihomModelToIhom AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instDecidableEqIdx AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instFintype AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instLinearOrder AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instFintypeIdx AlgebraicGeometry.OModulePresheaf.Leray.relAltC_scalarTower AlgebraicGeometry.OModulePresheaf.Leray.ker_relAltd_modΓ AlgebraicGeometry.OModulePresheaf.Leray.relAltC_modΓ AlgebraicGeometry.OModulePresheaf.Leray.biC_abGrp AlgebraicGeometry.OModulePresheaf.Leray.relAltH_modΓ AlgebraicGeometry.OModulePresheaf.Leray.ker_relAltd_smul AlgebraicGeometry.OModulePresheaf.Leray.relAltH_scalarTower AlgebraicGeometry.OModulePresheaf.Leray.relAltH_smul"
p2m_attr_erase "instance" "AlgebraicGeometry.OModulePresheaf.Leray.biC_module DoubleComplex.instModuleE₂I DoubleComplex.Bounded.modR DoubleComplex.instModuleE₂II DoubleComplex.instAddCommGroupE₂II DoubleComplex.Bounded.abGrp DoubleComplex.instAddCommGroupE₂I AlgebraicGeometry.ChowDatum.hι_closed AlgebraicGeometry.ChowDatumProj.hιN_closed AlgebraicGeometry.ChowDatumProj.hp_proper AlgebraicGeometry.ChowDatum.hp_isoU AlgebraicGeometry.ChowDatum.hp_proper AlgebraicGeometry.ProjSpace.algebraAway AlgebraicGeometry.ProjSpace.instIsProperProdOverπ AlgebraicGeometry.ChowDatumProj.hp_isoU AlgebraicGeometry.ProjSpace.isProper_π AlgebraicGeometry.ProjSpace.finiteType_mvPolynomial ProjSpaceCech.GradedModule.H.module ProjSpaceCech.GradedModule.H.addCommGroup ProjSpaceCech.GradedModule.sec.instAdd ProjSpaceCech.GradedModule.sec.instNeg ProjSpaceCech.GradedModule.acg ProjSpaceCech.GradedModule.Frac.setoid ProjSpaceCech.GradedModule.modR ProjSpaceCech.GradedModule.sec.instModule ProjSpaceCech.GradedModule.sec.instAddCommGroup ProjSpaceCech.GradedModule.sec.instZero ProjSpaceCech.GradedModule.Presentation.fJ ProjSpaceCech.GradedModule.sec.instSMul ProjSpaceCech.Twist.H.module ProjSpaceCech.Idx.instFintype ProjSpaceCech.Twist.H.addCommGroup ProjSpaceCech.Idx.instDecidableEq ProjSpaceCech.Twist.Mon.instDecidableEq ProjSpaceCech.Twist.cochain.instAddCommGroup ProjSpaceCech.Twist.cochain.instModule AlgebraicGeometry.FGSubalgebra.tensorStage_directedSystem AlgebraicGeometry.RelEffCartierDiv.isClosedImmersion_subschemeι_resProdMap AlgebraicGeometry.RelEffCartierDiv.isOpenImmersion_resProdMap AlgebraicCurve.CurveModel.locallyOfFiniteType_gluedToBase"
p2m_attr_erase "instance" "AlgebraicCurve.CurveModel.isFractionRing_overlap AlgebraicCurve.CurveModel.isLocallyNoetherian_glued AlgebraicCurve.CurveModel.jacobsonSpace_glued AlgebraicCurve.CurveModel.isOpenImmersion_ι₀ AlgebraicCurve.CurveModel.isIntegral_glued AlgebraicCurve.CurveModel.quasiSeparated_gluedToBase AlgebraicCurve.CurveModel.compactSpace_glued AlgebraicCurve.CurveModel.isIntegral_adjoin_chartRing AlgebraicCurve.CurveModel.isFractionRing_overlap_functionField AlgebraicCurve.CurveModel.isProper_gluedToBase AlgebraicCurve.CurveModel.isOpenImmersion_ιU AlgebraicCurve.CurveModel.isOpenImmersion_f₀ AlgebraicCurve.CurveModel.isOpenImmersion_fInf AlgebraicCurve.CurveModel.isOpenImmersion_ιInf AlgebraicCurve.CurveModel.algebra_overlap_functionField AlgebraicCurve.CurveModel.quasiCompact_gluedToBase AlgebraicCurve.CurveModel.algebraAdjoin AlgebraicCurve.CurveModel.isDedekindDomain_chartRing AlgebraicCurve.CurveModel.isIntegralClosure AlgebraicCurve.CurveModel.finite_chartRing AlgebraicCurve.CurveModel.centre_isPrime AlgebraicCurve.CurveModel.isFractionRing_chartRing AlgebraicCurve.CurveModel.finiteType_chartRing AlgebraicCurve.CurveModel.isNoetherianRing_chartRing AlgebraicCurve.CurveModel.isScalarTower_base_adjoin AlgebraicCurve.CurveModel.isScalarTower_adjoin AlgebraicCurve.CurveModel.chartRing_finitePresentation instTopologicallyFGOfFiniteType AlgebraicGeometry.ProjSpace.twistObj.addCommGroup AlgebraicGeometry.ProjSpace.twistFam.module AlgebraicGeometry.ProjSpace.twistObj.module AlgebraicGeometry.ProjSpace.twistObj.moduleSections AlgebraicGeometry.ProjSpace.twistFam.addCommGroup"
p2m_attr_erase "simp" "GoodReductionJacobian.RelativeGroupLaw.nsmul_zero GoodReductionJacobian.RelativeGroupLaw.mem_torsionSubset GoodReductionJacobian.RelativeGroupLaw.nsmul_succ NeronModelInfra.NeronModelPropertyBundle.endExtensionEquiv_symm_restrict NeronModelInfra.schemeHomOverComp_id_left NeronModelInfra.schemeHomOverComp_id_right NeronModelInfra.schemeHomOverId_coe NeronModelInfra.NeronModelPropertyBundle.endExtensionEquiv_apply NeronModelInfra.NeronModelPropertyBundle.restrict_endExtensionEquiv_symm NeronModelInfra.schemeHomOverComp_coe NeronModelInfra.schemeHomOverNpow_succ NeronModelInfra.schemeHomOverNpow_zero GoodReductionJacobian.relativeGroupLawOfGrpObj_inv GoodReductionJacobian.relativeGroupLawOfGrpObj_mul GoodReductionJacobian.overHomEquivSchemeHomOver_apply_coe GoodReductionJacobian.relativeGroupLawOfGrpObj_one GoodReductionJacobian.overHomEquivSchemeHomOver_symm_apply_left SheafOfModules.tensorUnit_eq AlgebraicGeometry.Scheme.Modules.tensorUnit_eq PresheafOfModules.InternalHom.presheaf_map_apply PresheafOfModules.InternalHom.curryFamily_app PresheafOfModules.InternalHom.add_app PresheafOfModules.InternalHom.smul_app PresheafOfModules.InternalHom.zero_app PresheafOfModules.ihomObj_map_val PresheafOfModules.ihomFunctor_map PresheafOfModules.InternalHom.restrict_app PresheafOfModules.InternalHom.postcomp_app PresheafOfModules.InternalHom.neg_app PresheafOfModules.curry'_app_val PresheafOfModules.InternalHom.presheaf_obj PresheafOfModules.ihomFunctor_obj PresheafOfModules.ihomObj_obj PresheafOfModules.InternalHom.sub_app PresheafOfModules.ihomMap_app_val AlgebraicGeometry.Scheme.Modules.tensorPow_zero AlgebraicGeometry.Scheme.Modules.tensorPow_succ AlgebraicGeometry.RelPicard.RigidifiedLineBundle.mk.sizeOf_spec AlgebraicGeometry.RelPicard.RigidifiedLineBundle.mk.injEq AlgebraicGeometry.Scheme.OrderedAffineCover.mk.injEq"
p2m_attr_erase "simp" "AlgebraicGeometry.OModulePresheaf.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCover.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.mk.injEq AlgebraicGeometry.Scheme.TwoAffineOpenCover.mk.injEq AlgebraicGeometry.Scheme.TwoAffineOpenCover.mk.sizeOf_spec AlgebraicGeometry.Scheme.TwoAffineOpenCover.pullback_U1 AlgebraicGeometry.Scheme.TwoAffineOpenCover.pullback_U0 TwoChartCech.Sections.mk.injEq TwoChartCech.Cover.mk.injEq TwoChartCech.GrothendieckComplex.mk.injEq TwoChartCech.Sections.mk.sizeOf_spec TwoChartCech.Cover.mk.sizeOf_spec TwoChartCech.Cover.lineBundle_r0_apply TwoChartCech.GrothendieckComplex.mk.sizeOf_spec TwoChartCech.Cover.lineBundle_r1_apply CoherentBaseChange.TwoTermComplex.mk.sizeOf_spec CoherentBaseChange.TwoTermComplex.mk.injEq AlgebraicGeometry.OModulePresheaf.prod_obj AlgebraicGeometry.OModulePresheaf.restrOpen_obj AlgebraicGeometry.OModulePresheaf.DevissageStep.mk.injEq AlgebraicGeometry.OModulePresheaf.pushforward_obj AlgebraicGeometry.OModulePresheaf.im_obj AlgebraicGeometry.OModulePresheaf.pow_obj AlgebraicGeometry.OModulePresheaf.fstHom_app AlgebraicGeometry.OModulePresheaf.ker_obj AlgebraicGeometry.OModulePresheaf.coker_obj AlgebraicGeometry.OModulePresheaf.DevissageStep.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCover.preimage_U AlgebraicGeometry.OModulePresheaf.sndHom_app AlgebraicGeometry.OModulePresheaf.Hom.mk.injEq AlgebraicGeometry.OModulePresheaf.Hom.id_app AlgebraicGeometry.OModulePresheaf.AffHom.appSections_apply AlgebraicGeometry.OModulePresheaf.AffHom.comp_app AlgebraicGeometry.OModulePresheaf.AffSES.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.AffHom.kerMap_coe AlgebraicGeometry.OModulePresheaf.AffHom.id_app AlgebraicGeometry.OModulePresheaf.Hom.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.Hom.toAffHom_app AlgebraicGeometry.OModulePresheaf.SES.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.AffHom.mk.sizeOf_spec"
p2m_attr_erase "simp" "AlgebraicGeometry.OModulePresheaf.Hom.comp_app AlgebraicGeometry.OModulePresheaf.SES.mk.injEq AlgebraicGeometry.OModulePresheaf.AffHom.mk.injEq AlgebraicGeometry.OModulePresheaf.Hom.appSections_apply AlgebraicGeometry.OModulePresheaf.AffSES.mk.injEq PresheafOfModules.freeεIso_hom_app PresheafOfModules.freeμIso_hom_app AlgebraicGeometry.RelPicard.RepresentsRelSubPic.mk.injEq AlgebraicGeometry.RelPicard.SubPicCondition.mk.injEq AlgebraicGeometry.RelPicard.SubPicCondition.mk.sizeOf_spec AlgebraicGeometry.RelPicard.RepresentsRelSubPic.mk.sizeOf_spec AlgebraicGeometry.SmoothProperCurve.sectionBaseChange_coe_snd AlgebraicGeometry.SmoothProperCurve.sectionBaseChange_coe_fst AlgebraicCurve.CurveModel.mk.injEq AlgebraicCurve.CurveModel.mk.sizeOf_spec AlgebraicCurve.mulAdele_apply AlgebraicCurve.residuePairing_apply_coe AlgebraicCurve.mem_adeleBdd AlgebraicCurve.weilSmul_one AlgebraicCurve.diagonalHom_apply AlgebraicCurve.weilSmul_apply AlgebraicCurve.adeleSpaceMul_coe AlgebraicCurve.mulAdele_one AlgebraicGeometry.SmoothProperCurve.FiniteMapData.twoAffineOpenCover_U1 AlgebraicGeometry.SmoothProperCurve.FiniteMapData.mk.injEq AlgebraicGeometry.SmoothProperCurve.FiniteMapData.mk.sizeOf_spec AlgebraicGeometry.SmoothProperCurve.FiniteMapData.twoAffineOpenCover_U0 AlgebraicGeometry.RelPicard.SubPicCondition.onClasses_mk AlgebraicGeometry.RelPicard.relSubPicPresheaf_map_coe CategoryTheory.Functor.OverTotal.ofFibre_fst CategoryTheory.Functor.overTotal_map_fst AlgebraicGeometry.Scheme.LocalRepresentabilityULift.glueData_J AlgebraicGeometry.Scheme.LocalRepresentabilityULift.uliftYoneda_toGlued_uliftYonedaGluedToSheaf AlgebraicGeometry.Scheme.LocalRepresentabilityULift.glueData_t' AlgebraicGeometry.Scheme.LocalRepresentabilityULift.uliftYoneda_toGlued_uliftYonedaGluedToSheaf_assoc AlgebraicGeometry.Scheme.LocalRepresentabilityULift.uliftYonedaGluedToSheaf_app_toGlued AlgebraicGeometry.Scheme.LocalRepresentabilityULift.glueData_openCover_map AlgebraicGeometry.Scheme.LocalRepresentabilityULift.uliftYonedaGluedToSheaf_app_comp AlgebraicGeometry.Scheme.LocalRepresentabilityULift.glueData_V AlgebraicGeometry.Scheme.LocalRepresentabilityULift.glueData_t"
p2m_attr_erase "simp" "AlgebraicGeometry.Scheme.LocalRepresentabilityULift.glueData_U AlgebraicGeometry.Scheme.LocalRepresentabilityULift.glueData_f AlgebraicGeometry.RelPicard.designationOfRepresentableBy_P AlgebraicGeometry.RelPicard.designationOfRepresentableBy_toBase AlgebraicGeometry.RelPicard.rigSection_snd AlgebraicGeometry.RelPicard.RigidifiedLineBundle.ofInvertible_L AlgebraicGeometry.RelPicard.rigSection_snd_assoc AlgebraicGeometry.RelPicard.SubPicGroupCondition.mk.injEq AlgebraicGeometry.RelPicard.SubPicGroupCondition.mk.sizeOf_spec AlgebraicCurve.coe_cechH0Equiv_apply AlgebraicCurve.cechH1ToH1_mk AlgebraicCurve.lSpaceOn_univ AlgebraicCurve.lSpaceOn_empty AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.Divisor.mapRestrict_single AlgebraicCurve.Divisor.pushforward_single AlgebraicCurve.Place.coe_restrictInclusion AlgebraicCurve.Place.mem_fiber AlgebraicCurve.Place.restrict_toValuationSubring AlgebraicCurve.Divisor.degree_pushforward AlgebraicCurve.Place.restrictResidueMap_residue AlgebraicCurve.Pic0.coe_pushforwardDegZeroHom AlgebraicCurve.Pic0.coe_pullbackDegZeroHom AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk"
p2m_attr_erase "simp" "ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Divisor.degree_pushforwardAlong AlgebraicCurve.Pic0.coe_degZeroCorrespondence AlgebraicCurve.Place.mem_fiberAlong AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.jqNModC_one ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one AlgebraicCurve.Place.differentialCoeff_zero AlgebraicCurve.Place.differentialCoeff_dCoord AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.injEq AlgebraicCurve.TranscendenceTower.mk.injEq AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec AlgebraicCurve.PoleDivisorPackage.mk.injEq AlgebraicGeometry.RelPicard.thetaBundle_def AlgebraicGeometry.RelPicard.picardBundle_def AlgebraicGeometry.RelEffCartierDiv.toRelEffDivisor_ofRelEffDivisor AlgebraicGeometry.RelEffCartierDiv.toRelEffDivisor_I"
p2m_attr_erase "simp" "AlgebraicGeometry.mapOnProdOver_fst_assoc AlgebraicGeometry.RelEffCartierDiv.mk.sizeOf_spec AlgebraicGeometry.RelEffCartierDiv.mk.injEq AlgebraicGeometry.mapOnProdOver_snd AlgebraicGeometry.mapOnProdOver_fst AlgebraicGeometry.mapOnProdOver_snd_assoc AlgebraicGeometry.mapOnProdOver_id AlgebraicCurve.RelEffDivisor.mk.sizeOf_spec AlgebraicCurve.mapOnProd_fst AlgebraicCurve.mapOnProd_fst_assoc AlgebraicCurve.mapOnProd_snd AlgebraicCurve.UnivDivisorPack.mk.injEq AlgebraicCurve.RelEffDivisor.mk.injEq AlgebraicCurve.UnivDivisorPack.mk.sizeOf_spec AlgebraicCurve.mapOnProd_snd_assoc AlgebraicGeometry.Scheme.Modules.exteriorPower_obj PresheafOfModules.exteriorPower_map_ιMulti PresheafOfModules.ExteriorPower.appₗ_apply AlgebraicGeometry.prodKerGraph_one AlgebraicGeometry.fibrePowOver.proj_comp AlgebraicGeometry.prodKerGraph_zero AlgebraicGeometry.RelEffCartierDiv.empty_I AlgebraicGeometry.fibrePowOver.proj_comp_assoc AlgebraicGeometry.graphOver_fst_assoc AlgebraicGeometry.RelEffCartierDiv.toPoint_comp AlgebraicGeometry.RelEffCartierDiv.toPoint_comp_assoc AlgebraicGeometry.graphOver_fst AlgebraicGeometry.RelEffCartierDiv.ofPoint_I AlgebraicGeometry.graphOver_snd AlgebraicGeometry.graphOver_snd_assoc AlgebraicCurve.SymmetricPowerPackage.mk.sizeOf_spec AlgebraicCurve.SymmetricPowerPackage.mk.injEq AlgebraicGeometry.FGSubalgebra.cocone_ι_app_apply AlgebraicGeometry.RelPicard.fst_toProdSpec AlgebraicGeometry.RelPicard.toProdSpec_fst_assoc AlgebraicGeometry.RelPicard.pointsSubBasepointModule_cons AlgebraicGeometry.RelPicard.pointsSubBasepointModule_nil AlgebraicGeometry.RelPicard.fst_toProdSpec_assoc AlgebraicGeometry.RelPicard.toProdSpec_fst AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.sub_app"
p2m_attr_erase "simp" "AlgebraicGeometry.Scheme.IdealSheafData.sres_sresTop AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.add_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.mk.sizeOf_spec AlgebraicGeometry.Scheme.IdealSheafData.coe_resLE AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.smul_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.coe_ofLE_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.ideal_range AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.zero_app AlgebraicGeometry.Scheme.IdealSheafData.sres_sres AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.comp_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.neg_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.id_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.coe_mulRight_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.nsmul_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.mk.injEq AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.zsmul_app AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.sizeOf_spec AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.injEq AlgebraicCurve.adeleSingle_coe AlgebraicCurve.kaehlerResidueTermKFam_apply AlgebraicCurve.Place.LocalResidueData.mk.injEq AlgebraicCurve.Place.LocalResidueData.mk.sizeOf_spec AlgebraicCurve.Place.kw_ffgc_adicCompletionComapIntegers_coe AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.sizeOf_spec AlgebraicCurve.Place.mem_simplePoleSubmodule AlgebraicCurve.Place.coe_uniformizerSubring ModularCurve.Lg37.Lg37CompletionSection.mk.injEq AlgebraicCurve.Place.CoefficientFieldSection.mk.injEq AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.injEq ModularCurve.Lg37.Lg37CompletionSection.mk.sizeOf_spec AlgebraicCurve.Place.CoefficientFieldSection.mk.sizeOf_spec AlgebraicCurve.Place.poleSubmodule_one AlgebraicCurve.Place.mem_poleSubmodule AlgebraicGeometry.Scheme.Modules.toUnitSection_ofUnitSection AlgebraicGeometry.Scheme.Modules.pullbackSection_def AlgebraicGeometry.Scheme.Modules.ofUnitSection_toUnitSection PresheafOfModules.InternalHom.IsSheafAux.appAt_toPresheafHom SheafOfModules.ihomSectionsEquivFamily_unit AlgebraicGeometry.Scheme.Modules.restrictHomEquivFamily_apply SheafOfModules.ihomEval_unit_app"
p2m_attr_erase "simp" "AlgebraicGeometry.Scheme.Modules.ihomEval_zero_right AlgebraicGeometry.Scheme.Modules.ihomEval_zero_left AlgebraicGeometry.Scheme.Modules.homOfFamily_app_apply SheafOfModules.unit_ihomSectionsEquivFamily AlgebraicGeometry.Scheme.Modules.familyOfHom_app AlgebraicGeometry.Scheme.Modules.restrictUnitIso_hom_app_apply AlgebraicGeometry.Scheme.Modules.restrictUnitIso_inv_app_apply AlgebraicGeometry.Scheme.Modules.restrictHomOfFamily_app_apply AlgebraicGeometry.Scheme.Modules.restrictHomEquivFamily_symm_apply AlgebraicGeometry.Scheme.Modules.tensorSections_zero_right AlgebraicGeometry.Scheme.Modules.map_unitSection AlgebraicGeometry.Scheme.Modules.tensorSectionsBilin_apply AlgebraicGeometry.Scheme.Modules.tensorPowSection_zero AlgebraicGeometry.Scheme.Modules.tensorSections_zero_left AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_neg AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_zero AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_sub AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_add AlgebraicGeometry.Scheme.OrderedAffineCover.toCoverOf_U AlgebraicGeometry.Scheme.OrderedAffineCoverOf.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCoverOf.mk.injEq AlgebraicGeometry.Scheme.OrderedAffineCover.restrict_U AlgebraicGeometry.OModulePresheaf.Leray.restrictToPreimage_U DoubleComplex.Bounded.mk.injEq DoubleComplex.Bounded.mk.sizeOf_spec DoubleComplex.Convergence.mk.injEq DoubleComplex.Convergence.mk.sizeOf_spec DoubleComplex.SubQuot.mk.sizeOf_spec DoubleComplex.SubQuot.mk.injEq AlgebraicGeometry.ChowDatumProj.mk.sizeOf_spec AlgebraicGeometry.ChowDatum.mk.sizeOf_spec AlgebraicGeometry.ChowDatumProj.mk.injEq AlgebraicGeometry.ChowDatum.mk.injEq ProjSpaceCech.GradedModule.mk.injEq ProjSpaceCech.GradedModule.mk.sizeOf_spec ProjSpaceCech.GradedModule.Frac.mk.sizeOf_spec ProjSpaceCech.GradedModule.Presentation.mk.injEq ProjSpaceCech.GradedModule.Frac.mk.injEq ProjSpaceCech.GradedModule.Presentation.mk.sizeOf_spec ProjSpaceCech.GradedModule.Hom.shift_toLinearMap"
p2m_attr_erase "simp" "ProjSpaceCech.GradedModule.Hom.mk.sizeOf_spec ProjSpaceCech.GradedModule.Hom.mk.injEq TwoChartCech.Mumford.dK_apply TwoChartCech.Mumford.ι0_apply TwoChartCech.Mumford.ι1_apply TwoChartCech.KerCoprod.dK_apply TwoChartCech.KerCoprod.ι1_apply TwoChartCech.KerCoprod.ι0_apply AlgebraicGeometry.tilde.functorCompPullbackSpecIso_app AlgebraicGeometry.RelPicard.algEquivZeroGroupCut_toSubPicCondition AlgebraicGeometry.RelPicard.LFP.stageHom_val AlgebraicGeometry.RelPicard.BaseChange.relSubPicPresheafRestrictIso_hom_app_coe AlgebraicGeometry.RelPicard.BaseChange.relSubPicPresheafRestrictIso_inv_app_coe AlgebraicGeometry.RelPicard.BaseChange.restrict_P AlgebraicGeometry.RelEffCartierDiv.IsUniversal.lift_comp AlgebraicGeometry.RelEffCartierDiv.functor_map_fst AlgebraicGeometry.RelEffCartierDiv.IsUniversal.homEquiv_apply AlgebraicGeometry.RelEffCartierDiv.IsUniversal.lift_pullbackAlong AlgebraicGeometry.RelEffCartierDiv.IsUniversal.homEquiv_symm_apply AlgebraicGeometry.RelEffCartierDiv.IsUniversal.lift_comp_assoc AlgebraicGeometry.RelEffCartierDiv.supportedIn_top AlgebraicGeometry.RelEffCartierDiv.mem_supportedIn_iff AlgebraicGeometry.RelEffCartierDiv.supportedIn_top_eq AlgebraicGeometry.RelEffCartierDiv.restrictAlong_extendAlong AlgebraicGeometry.RelEffCartierDiv.extendAlong_I AlgebraicGeometry.RelEffCartierDiv.resProdMap_snd AlgebraicGeometry.RelEffCartierDiv.restrictAlong_I AlgebraicGeometry.RelEffCartierDiv.extendAlong_restrictAlong AlgebraicGeometry.RelEffCartierDiv.resProdMap_fst_assoc AlgebraicGeometry.RelEffCartierDiv.resProdMap_snd_assoc AlgebraicGeometry.RelEffCartierDiv.resProdMap_fst CoherentBaseChange.FibreH0Family.mk.sizeOf_spec CoherentBaseChange.FibreH0Family.mk.injEq AlgebraicGeometry.Scheme.Modules.ProjPresentation.mk.injEq AlgebraicGeometry.Scheme.Modules.ProjPresentation.mk.sizeOf_spec AlgebraicCurve.CurveModel.coe_gInf AlgebraicCurve.CurveModel.coe_tInvChart AlgebraicCurve.CurveModel.ιInf_gluedToBase_assoc AlgebraicCurve.CurveModel.ιInf_gluedToBase AlgebraicCurve.CurveModel.primeOfι₀_asIdeal"
p2m_attr_erase "simp" "AlgebraicCurve.CurveModel.coe_tChart AlgebraicCurve.CurveModel.ι₀_gluedToBase_assoc AlgebraicCurve.CurveModel.primeOfιInf_asIdeal AlgebraicCurve.CurveModel.ι₀_gluedToBase AlgebraicCurve.CurveModel.coe_tma AlgebraicCurve.CurveModel.coe_primeEquivChartPlaces RegularLocalRingQuotientAscent.dualNumberFst_apply AlgebraicGeometry.ProjSpace.twistObj.mk.injEq AlgebraicGeometry.ProjSpace.twistObj.zero_val AlgebraicGeometry.ProjSpace.twistObj.add_val AlgebraicGeometry.ProjSpace.twist_res_val AlgebraicGeometry.ProjSpace.twist_smul_val AlgebraicGeometry.ProjSpace.twistGradeToObj_val AlgebraicGeometry.ProjSpace.twistObj.smul_val AlgebraicGeometry.ProjSpace.twistGradeEquiv_apply_val AlgebraicGeometry.ProjSpace.twistObj.mk.sizeOf_spec QuaternionAlgebra.baseChangeRight_tmul QuaternionAlgebra.mapOfAlgebraMapEq_apply QuaternionAlgebra.baseChange_tmul QuaternionAlgebra.ClassSet.map_mk"

set_option autoImplicit false

open scoped TensorProduct Quaternion NumberField
p2m_open "CategoryTheory AlgebraicGeometry QuaternionAlgebra CerednikDrinfeld P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_exists_extraLevel_enum.CerednikDrinfeld CerednikDrinfeld.QM P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_exists_extraLevel_enum.CerednikDrinfeld.QM NeronModelInfra"

namespace CerednikDrinfeld
p2m_export "CerednikDrinfeld" "QM.FakeEllipticCurve.ExtraLevel QM.FakeEllipticCurve QM.FakeEllipticCurve.exists_generator_torsionPoints_of_isMaximalOrder_of_prime QM.FakeEllipticCurve.exists_extraLevel_of_equiv_points QM.FakeEllipticCurve.ExtraLevel.exists_equiv_points QM.FakeEllipticCurve.natCard_properLine_image_subset_lev"
namespace QM
p2m_export "CerednikDrinfeld.QM" "FakeEllipticCurve.ExtraLevel mapPt mapPt_coe pushPt FactorsThrough nsmulPt FakeEllipticCurve FakeEllipticCurve.exists_generator_torsionPoints_of_isMaximalOrder_of_prime FakeEllipticCurve.exists_extraLevel_of_equiv_points FakeEllipticCurve.ExtraLevel.exists_equiv_points FakeEllipticCurve.natCard_properLine_image_subset_lev"
namespace EnumAux
p2m_open "CerednikDrinfeld.QM CerednikDrinfeld"

p2m_open "CategoryTheory AlgebraicGeometry NeronModelInfra CerednikDrinfeld.QM P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_exists_extraLevel_enum.CerednikDrinfeld.QM"

variable {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} {N : ℕ} {k : Type} [Field k]

abbrev Pt (E : FakeEllipticCurve Λ N k) : Type := SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) E.f

noncomputable scoped instance ptAdd (E : FakeEllipticCurve Λ N k) : Add (Pt E) := ⟨fun P Q => E.L.mul (𝟙 (Spec (CommRingCat.of k))) P Q⟩
noncomputable scoped instance ptZero (E : FakeEllipticCurve Λ N k) : Zero (Pt E) := ⟨E.L.one (𝟙 (Spec (CommRingCat.of k)))⟩
noncomputable scoped instance ptNeg (E : FakeEllipticCurve Λ N k) : Neg (Pt E) := ⟨fun P => E.L.inv (𝟙 (Spec (CommRingCat.of k))) P⟩

noncomputable scoped instance ptGroup (E : FakeEllipticCurve Λ N k) : AddCommGroup (Pt E) where
  add := (· + ·)
  zero := 0
  neg := Neg.neg
  nsmul := nsmulRec
  zsmul := zsmulRec
  add_assoc := E.L.mul_assoc (𝟙 (Spec (CommRingCat.of k)))
  zero_add := E.L.one_mul (𝟙 (Spec (CommRingCat.of k)))
  add_zero := E.L.mul_one (𝟙 (Spec (CommRingCat.of k)))
  neg_add_cancel := E.L.inv_mul_cancel (𝟙 (Spec (CommRingCat.of k)))
  add_comm P Q := E.comm (𝟙 (Spec (CommRingCat.of k))) P Q

section Basic

variable (E : FakeEllipticCurve Λ N k)

theorem add_def (P Q : Pt E) : P + Q = E.L.mul (𝟙 (Spec (CommRingCat.of k))) P Q := rfl

theorem zero_def : (0 : Pt E) = E.L.one (𝟙 (Spec (CommRingCat.of k))) := rfl

theorem nsmulPt_eq_nsmul (n : ℕ) (P : Pt E) : nsmulPt E.L (𝟙 (Spec (CommRingCat.of k))) n P = n • P := by
  induction n with
  | zero => rw [zero_nsmul]; rfl
  | succ n ih =>
    rw [succ_nsmul, add_def, ← ih]
    rfl

theorem mapPt_comp_eq {T : Scheme.{0}} {t : T ⟶ Spec (CommRingCat.of k)} (φ ψ : E.A ⟶ E.A) (hφ : φ ≫ E.f = E.f)
    (hψ : ψ ≫ E.f = E.f) (h : (φ ≫ ψ) ≫ E.f = E.f) (P : SchemeHomOver t E.f) :
    mapPt (φ ≫ ψ) h P = mapPt ψ hψ (mapPt φ hφ P) := by
  apply Subtype.ext
  simp only [mapPt_coe, Category.assoc]

theorem mapPt_id_eq {T : Scheme.{0}} {t : T ⟶ Spec (CommRingCat.of k)} (h : 𝟙 E.A ≫ E.f = E.f) (P : SchemeHomOver t E.f) :
    mapPt (𝟙 E.A) h P = P := by
  apply Subtype.ext
  simp only [mapPt_coe, Category.comp_id]

noncomputable def actPt (m : ↥Λ) (P : Pt E) : Pt E := pushPt (E.act m) (E.act_over m) P

theorem actPt_def (m : ↥Λ) (P : Pt E) : actPt E m P = pushPt (E.act m) (E.act_over m) P := rfl

theorem actPt_add (m : ↥Λ) (P Q : Pt E) : actPt E m (P + Q) = actPt E m P + actPt E m Q :=
  E.act_hom m (𝟙 (Spec (CommRingCat.of k))) P Q

theorem actPt_add_left (m n : ↥Λ) (P : Pt E) : actPt E (m + n) P = actPt E m P + actPt E n P :=
  E.act_add m n (𝟙 (Spec (CommRingCat.of k))) P

theorem actPt_zero_left (P : Pt E) : actPt E 0 P = 0 := by
  have h := actPt_add_left E 0 0 P
  rw [add_zero] at h
  exact left_eq_add.1 h

theorem actPt_neg_left (m : ↥Λ) (P : Pt E) : actPt E (-m) P = -actPt E m P := by
  have h := actPt_add_left E (-m) m P
  rw [neg_add_cancel, actPt_zero_left] at h
  exact (neg_eq_of_add_eq_zero_left h.symm).symm

theorem actPt_one (h1 : (1 : ℍ[ℚ, a, b]) ∈ Λ) (P : Pt E) : actPt E ⟨1, h1⟩ P = P := by
  have := E.act_one h1
  apply Subtype.ext
  show P.1 ≫ E.act ⟨1, h1⟩ = P.1
  rw [this, Category.comp_id]

theorem actPt_mul (x y : ↥Λ) (h : (x : ℍ[ℚ, a, b]) * (y : ℍ[ℚ, a, b]) ∈ Λ) (P : Pt E) :
    actPt E ⟨(x : ℍ[ℚ, a, b]) * (y : ℍ[ℚ, a, b]), h⟩ P = actPt E x (actPt E y P) := by
  have := E.act_mul x y h
  apply Subtype.ext
  show P.1 ≫ E.act ⟨(x : ℍ[ℚ, a, b]) * (y : ℍ[ℚ, a, b]), h⟩ = (P.1 ≫ E.act y) ≫ E.act x
  rw [this, Category.assoc]

theorem actPt_zero (m : ↥Λ) : actPt E m 0 = 0 := by
  have h := actPt_add E m 0 0
  rw [add_zero] at h
  exact left_eq_add.1 h

noncomputable def actHom (P₀ : Pt E) : ↥Λ →+ Pt E where
  toFun m := actPt E m P₀
  map_zero' := actPt_zero_left E P₀
  map_add' m n := actPt_add_left E m n P₀

theorem actHom_apply (P₀ : Pt E) (m : ↥Λ) : actHom E P₀ m = actPt E m P₀ := rfl

noncomputable def orbit (P₀ : Pt E) : AddSubgroup (Pt E) := (actHom E P₀).range

theorem mem_orbit_iff (P₀ P : Pt E) : P ∈ orbit E P₀ ↔ ∃ m : ↥Λ, P = actPt E m P₀ := by
  rw [orbit, AddMonoidHom.mem_range]
  constructor
  · rintro ⟨m, hm⟩; exact ⟨m, hm.symm⟩
  · rintro ⟨m, hm⟩; exact ⟨m, hm.symm⟩

noncomputable def rho (hΛ : QuaternionAlgebra.IsOrder Λ) (P₀ : Pt E) (n : ↥Λ) : ↥(orbit E P₀) →+ ↥(orbit E P₀) where
  toFun P := ⟨actPt E n P.1, by
    obtain ⟨m, hm⟩ := (mem_orbit_iff E P₀ P.1).1 P.2
    rw [mem_orbit_iff]
    refine ⟨⟨(n : ℍ[ℚ, a, b]) * (m : ℍ[ℚ, a, b]), hΛ.mul_mem n.2 m.2⟩, ?_⟩
    rw [hm, actPt_mul]⟩
  map_zero' := by
    apply Subtype.ext
    show actPt E n (0 : Pt E) = 0
    exact actPt_zero E n
  map_add' P Q := by
    apply Subtype.ext
    show actPt E n (P.1 + Q.1) = actPt E n P.1 + actPt E n Q.1
    exact actPt_add E n P.1 Q.1

theorem rho_apply_coe (hΛ : QuaternionAlgebra.IsOrder Λ) (P₀ : Pt E) (n : ↥Λ) (P : ↥(orbit E P₀)) :
    ((rho E hΛ P₀ n P : ↥(orbit E P₀)) : Pt E) = actPt E n P.1 := rfl

theorem rho_one (hΛ : QuaternionAlgebra.IsOrder Λ) (P₀ : Pt E) (h : (1 : ℍ[ℚ, a, b]) ∈ Λ) :
    rho E hΛ P₀ ⟨1, h⟩ = AddMonoidHom.id _ := by
  refine AddMonoidHom.ext fun P => Subtype.ext ?_
  show actPt E ⟨1, h⟩ P.1 = P.1
  exact actPt_one E h P.1

theorem rho_mul (hΛ : QuaternionAlgebra.IsOrder Λ) (P₀ : Pt E) (x y : ↥Λ) (h : (x : ℍ[ℚ, a, b]) * (y : ℍ[ℚ, a, b]) ∈ Λ) :
    rho E hΛ P₀ ⟨(x : ℍ[ℚ, a, b]) * (y : ℍ[ℚ, a, b]), h⟩ = (rho E hΛ P₀ x).comp (rho E hΛ P₀ y) := by
  refine AddMonoidHom.ext fun P => Subtype.ext ?_
  show actPt E ⟨(x : ℍ[ℚ, a, b]) * (y : ℍ[ℚ, a, b]), h⟩ P.1 = actPt E x (actPt E y P.1)
  exact actPt_mul E x y h P.1

theorem rho_add (hΛ : QuaternionAlgebra.IsOrder Λ) (P₀ : Pt E) (x y : ↥Λ) :
    rho E hΛ P₀ (x + y) = rho E hΛ P₀ x + rho E hΛ P₀ y := by
  refine AddMonoidHom.ext fun P => Subtype.ext ?_
  show actPt E (x + y) P.1 = actPt E x P.1 + actPt E y P.1
  exact actPt_add_left E x y P.1

noncomputable def basePt (hΛ : QuaternionAlgebra.IsOrder Λ) (P₀ : Pt E) : ↥(orbit E P₀) :=
  ⟨P₀, (mem_orbit_iff E P₀ P₀).2 ⟨⟨1, hΛ.one_mem⟩, (actPt_one E hΛ.one_mem P₀).symm⟩⟩

theorem rho_basePt (hΛ : QuaternionAlgebra.IsOrder Λ) (P₀ : Pt E) (m : ↥Λ) :
    ((rho E hΛ P₀ m (basePt E hΛ P₀) : ↥(orbit E P₀)) : Pt E) = actPt E m P₀ := rfl

theorem hgen (hΛ : QuaternionAlgebra.IsOrder Λ) (P₀ : Pt E) (P : ↥(orbit E P₀)) :
    ∃ m : ↥Λ, P = rho E hΛ P₀ m (basePt E hΛ P₀) := by
  obtain ⟨m, hm⟩ := (mem_orbit_iff E P₀ P.1).1 P.2
  exact ⟨m, Subtype.ext hm⟩

end Basic

end CerednikDrinfeld.QM.EnumAux
p2m_reactivate "P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_exists_extraLevel_enum.CerednikDrinfeld P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_exists_extraLevel_enum.CerednikDrinfeld.QM P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_exists_extraLevel_enum.CerednikDrinfeld.QM.EnumAux"
p2m_reactivate "P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_exists_extraLevel_enum.CerednikDrinfeld P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_exists_extraLevel_enum.CerednikDrinfeld.QM"
p2m_reactivate "P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_exists_extraLevel_enum.CerednikDrinfeld"

namespace CerednikDrinfeld
p2m_export "CerednikDrinfeld" "QM.FakeEllipticCurve.ExtraLevel QM.FakeEllipticCurve QM.FakeEllipticCurve.exists_generator_torsionPoints_of_isMaximalOrder_of_prime QM.FakeEllipticCurve.exists_extraLevel_of_equiv_points QM.FakeEllipticCurve.ExtraLevel.exists_equiv_points QM.FakeEllipticCurve.natCard_properLine_image_subset_lev"
namespace QM
p2m_export "CerednikDrinfeld.QM" "FakeEllipticCurve.ExtraLevel mapPt mapPt_coe pushPt FactorsThrough nsmulPt FakeEllipticCurve FakeEllipticCurve.exists_generator_torsionPoints_of_isMaximalOrder_of_prime FakeEllipticCurve.exists_extraLevel_of_equiv_points FakeEllipticCurve.ExtraLevel.exists_equiv_points FakeEllipticCurve.natCard_properLine_image_subset_lev"
namespace EnumAux
p2m_open "CerednikDrinfeld.QM CerednikDrinfeld"

p2m_open "CategoryTheory AlgebraicGeometry NeronModelInfra CerednikDrinfeld.QM P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_exists_extraLevel_enum.CerednikDrinfeld.QM"

section Torsion

theorem card_nsmul_eq_zero_zmod (N ℓ : ℕ) [NeZero N] (hℓ : ℓ ∣ N) (hℓ0 : 0 < ℓ) :
    Nat.card {x : ZMod N // ℓ • x = 0} = ℓ := by
  classical
  have hN : N ≠ 0 := NeZero.ne N
  let φ : ZMod N →+ ZMod N := AddMonoidHom.mulLeft (ℓ : ZMod N)
  have hker : ∀ x : ZMod N, x ∈ φ.ker ↔ ℓ • x = 0 := by
    intro x; rw [AddMonoidHom.mem_ker, AddMonoidHom.coe_mulLeft, nsmul_eq_mul]
  have hrange : φ.range = AddSubgroup.zmultiples (ℓ : ZMod N) := by
    ext y
    rw [AddMonoidHom.mem_range, AddSubgroup.mem_zmultiples_iff]
    constructor
    · rintro ⟨x, rfl⟩
      refine ⟨(x.val : ℤ), ?_⟩
      rw [AddMonoidHom.coe_mulLeft, zsmul_eq_mul, Int.cast_natCast, ZMod.natCast_zmod_val, mul_comm]
    · rintro ⟨z, rfl⟩
      refine ⟨(z : ZMod N), ?_⟩
      rw [AddMonoidHom.coe_mulLeft, zsmul_eq_mul, mul_comm]
  have hcr : Nat.card φ.range = N / ℓ := by
    rw [hrange, Nat.card_zmultiples, ZMod.addOrderOf_coe ℓ hN, Nat.gcd_eq_right hℓ]
  have h1 : Nat.card (ZMod N) = Nat.card (ZMod N ⧸ φ.ker) * Nat.card φ.ker :=
    AddSubgroup.card_eq_card_quotient_mul_card_addSubgroup φ.ker
  rw [Nat.card_congr (QuotientAddGroup.quotientKerEquivRange φ).toEquiv, hcr, Nat.card_zmod] at h1
  have h2 : Nat.card φ.ker = Nat.card {x : ZMod N // ℓ • x = 0} :=
    Nat.card_congr (Equiv.subtypeEquivRight fun x => hker x)
  rw [← h2]
  have hpos : 0 < N / ℓ := Nat.div_pos (Nat.le_of_dvd (Nat.pos_of_ne_zero hN) hℓ) hℓ0
  have h3 : N / ℓ * Nat.card φ.ker = N / ℓ * ℓ := by rw [← h1, Nat.div_mul_cancel hℓ]
  exact Nat.eq_of_mul_eq_mul_left hpos h3

theorem card_nsmul_eq_zero_prod (A B : Type) [AddMonoid A] [AddMonoid B] (ℓ : ℕ) :
    Nat.card {p : A × B // ℓ • p = 0} = Nat.card {x : A // ℓ • x = 0} * Nat.card {y : B // ℓ • y = 0} := by
  rw [← Nat.card_prod]
  apply Nat.card_congr
  exact {
    toFun := fun p => (⟨p.1.1, by have := congrArg Prod.fst p.2; simpa using this⟩,
                       ⟨p.1.2, by have := congrArg Prod.snd p.2; simpa using this⟩)
    invFun := fun q => ⟨(q.1.1, q.2.1), by rw [Prod.smul_mk, q.1.2, q.2.2]; rfl⟩
    left_inv := fun p => rfl
    right_inv := fun q => rfl }

theorem card_nsmul_eq_zero_zmod_prod (N ℓ : ℕ) [NeZero N] (hℓ : ℓ ∣ N) (hℓ0 : 0 < ℓ) :
    Nat.card {p : ZMod N × ZMod N // ℓ • p = 0} = ℓ ^ 2 := by
  rw [card_nsmul_eq_zero_prod, card_nsmul_eq_zero_zmod N ℓ hℓ hℓ0, sq]

theorem equiv_map_zero {G : Type} [AddGroup G] {H : Type} [AddGroup H] {S : Set H} (e : G ≃ S)
    (he : ∀ x y : G, ((e (x + y) : S) : H) = (e x : H) + (e y : H)) : ((e 0 : S) : H) = 0 := by
  have := he 0 0
  rw [add_zero] at this
  exact (left_eq_add.1 this)

theorem equiv_map_nsmul {G : Type} [AddGroup G] {H : Type} [AddGroup H] {S : Set H} (e : G ≃ S)
    (he : ∀ x y : G, ((e (x + y) : S) : H) = (e x : H) + (e y : H)) (n : ℕ) (x : G) :
    ((e (n • x) : S) : H) = n • (e x : H) := by
  induction n with
  | zero => rw [zero_nsmul, zero_nsmul, equiv_map_zero e he]
  | succ n ih => rw [succ_nsmul, succ_nsmul, he, ih]

theorem equiv_map_neg {G : Type} [AddGroup G] {H : Type} [AddGroup H] {S : Set H} (e : G ≃ S)
    (he : ∀ x y : G, ((e (x + y) : S) : H) = (e x : H) + (e y : H)) (x : G) :
    ((e (-x) : S) : H) = -(e x : H) := by
  have := he (-x) x
  rw [neg_add_cancel, equiv_map_zero e he] at this
  exact (neg_eq_of_add_eq_zero_left this.symm).symm

theorem ncard_eq_of_equiv_zmod_prod {H : Type} (ℓ : ℕ) [NeZero ℓ] {S : Set H} (e : ZMod ℓ × ZMod ℓ ≃ S) :
    Nat.card S = ℓ ^ 2 := by
  rw [← Nat.card_congr e, Nat.card_prod, Nat.card_zmod, sq]

end Torsion
p2m_reactivate "P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_exists_extraLevel_enum.CerednikDrinfeld P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_exists_extraLevel_enum.CerednikDrinfeld.QM P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_exists_extraLevel_enum.CerednikDrinfeld.QM.EnumAux"

end CerednikDrinfeld.QM.EnumAux
p2m_reactivate "P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_exists_extraLevel_enum.CerednikDrinfeld P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_exists_extraLevel_enum.CerednikDrinfeld.QM P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_exists_extraLevel_enum.CerednikDrinfeld.QM.EnumAux"
p2m_reactivate "P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_exists_extraLevel_enum.CerednikDrinfeld P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_exists_extraLevel_enum.CerednikDrinfeld.QM P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_exists_extraLevel_enum.CerednikDrinfeld.QM.EnumAux"
p2m_reactivate "P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_exists_extraLevel_enum.CerednikDrinfeld P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_exists_extraLevel_enum.CerednikDrinfeld.QM P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_exists_extraLevel_enum.CerednikDrinfeld.QM.EnumAux"

namespace CerednikDrinfeld
p2m_export "CerednikDrinfeld" "QM.FakeEllipticCurve.ExtraLevel QM.FakeEllipticCurve QM.FakeEllipticCurve.exists_generator_torsionPoints_of_isMaximalOrder_of_prime QM.FakeEllipticCurve.exists_extraLevel_of_equiv_points QM.FakeEllipticCurve.ExtraLevel.exists_equiv_points QM.FakeEllipticCurve.natCard_properLine_image_subset_lev"
namespace QM
p2m_export "CerednikDrinfeld.QM" "FakeEllipticCurve.ExtraLevel mapPt mapPt_coe pushPt FactorsThrough nsmulPt FakeEllipticCurve FakeEllipticCurve.exists_generator_torsionPoints_of_isMaximalOrder_of_prime FakeEllipticCurve.exists_extraLevel_of_equiv_points FakeEllipticCurve.ExtraLevel.exists_equiv_points FakeEllipticCurve.natCard_properLine_image_subset_lev"
namespace EnumAux
p2m_open "CerednikDrinfeld.QM CerednikDrinfeld"

p2m_open "CategoryTheory AlgebraicGeometry NeronModelInfra CerednikDrinfeld.QM P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_exists_extraLevel_enum.CerednikDrinfeld.QM"

section Lines

variable {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} {N : ℕ} {k : Type} [Field k]
variable (E : FakeEllipticCurve Λ N k) (hO : QuaternionAlgebra.IsOrder Λ) (P₀ : Pt E)

def IsLine (Λ : Submodule ℤ ℍ[ℚ, a, b]) (ℓ : ℕ) (J : Submodule ℤ ℍ[ℚ, a, b]) : Prop :=
  J ≤ Λ ∧ (∀ y ∈ Λ, (ℓ : ℤ) • y ∈ J) ∧ (∀ m ∈ Λ, ∀ x ∈ J, m * x ∈ J) ∧
    (∃ x ∈ J, ¬ ∃ y ∈ Λ, x = (ℓ : ℤ) • y) ∧ J ≠ Λ

def img (J : Submodule ℤ ℍ[ℚ, a, b]) : Set (Pt E) := {P | ∃ m : ↥Λ, (m : ℍ[ℚ, a, b]) ∈ J ∧ P = actPt E m P₀}

theorem img_subset_orbit (J : Submodule ℤ ℍ[ℚ, a, b]) : img E P₀ J ⊆ (orbit E P₀ : Set (Pt E)) := by
  rintro P ⟨m, -, rfl⟩
  exact (mem_orbit_iff E P₀ _).2 ⟨m, rfl⟩

theorem mem_img_iff_rho (J : Submodule ℤ ℍ[ℚ, a, b]) (P : ↥(orbit E P₀)) :
    (∃ m : ↥Λ, (m : ℍ[ℚ, a, b]) ∈ J ∧ P = rho E hO P₀ m (basePt E hO P₀)) ↔ (P : Pt E) ∈ img E P₀ J := by
  constructor
  · rintro ⟨m, hm, hP⟩
    exact ⟨m, hm, by rw [hP]; rfl⟩
  · rintro ⟨m, hm, hP⟩
    exact ⟨m, hm, Subtype.ext hP⟩

noncomputable def imgEquiv (J : Submodule ℤ ℍ[ℚ, a, b]) :
    {P : ↥(orbit E P₀) // ∃ m : ↥Λ, (m : ℍ[ℚ, a, b]) ∈ J ∧ P = rho E hO P₀ m (basePt E hO P₀)} ≃ ↥(img E P₀ J) where
  toFun P := ⟨(P.1 : Pt E), (mem_img_iff_rho E hO P₀ J P.1).1 P.2⟩
  invFun Q := ⟨⟨Q.1, img_subset_orbit E P₀ J Q.2⟩, (mem_img_iff_rho E hO P₀ J ⟨Q.1, img_subset_orbit E P₀ J Q.2⟩).2 Q.2⟩
  left_inv P := rfl
  right_inv Q := rfl

theorem img_injective (ℓ : ℕ)
    (hann : ∀ m : ↥Λ, actPt E m P₀ = 0 ↔ ∃ m' : ↥Λ, (m : ℍ[ℚ, a, b]) = ((ℓ : ℚ) : ℍ[ℚ, a, b]) * (m' : ℍ[ℚ, a, b]))
    {J J' : Submodule ℤ ℍ[ℚ, a, b]} (hJ : IsLine Λ ℓ J) (hJ' : IsLine Λ ℓ J') (h : img E P₀ J = img E P₀ J') : J = J' := by

  suffices key : ∀ (J J' : Submodule ℤ ℍ[ℚ, a, b]), IsLine Λ ℓ J → IsLine Λ ℓ J' → img E P₀ J = img E P₀ J' → J ≤ J' from
    le_antisymm (key J J' hJ hJ' h) (key J' J hJ' hJ h.symm)
  intro J J' hJ hJ' h x hx
  have hxΛ : x ∈ Λ := hJ.1 hx
  have hmem : actPt E ⟨x, hxΛ⟩ P₀ ∈ img E P₀ J' := by rw [← h]; exact ⟨⟨x, hxΛ⟩, hx, rfl⟩
  obtain ⟨m', hm', hP⟩ := hmem

  have h0 : actPt E (⟨x, hxΛ⟩ - m') P₀ = 0 := by
    rw [sub_eq_add_neg, actPt_add_left, actPt_neg_left, ← hP, add_neg_cancel]
  obtain ⟨t, ht⟩ := (hann _).1 h0
  have hxeq : x = (m' : ℍ[ℚ, a, b]) + (ℓ : ℤ) • (t : ℍ[ℚ, a, b]) := by
    have : ((⟨x, hxΛ⟩ - m' : ↥Λ) : ℍ[ℚ, a, b]) = x - (m' : ℍ[ℚ, a, b]) := rfl
    rw [this] at ht
    rw [show ((ℓ : ℚ) : ℍ[ℚ, a, b]) = (ℓ : ℍ[ℚ, a, b]) by norm_cast] at ht
    rw [zsmul_eq_mul, Int.cast_natCast, ← ht]
    abel
  rw [hxeq]
  exact J'.add_mem hm' (hJ'.2.1 _ t.2)

noncomputable def levSub : AddSubgroup ↥(orbit E P₀) where
  carrier := {P | FactorsThrough E.lev (P : Pt E)}
  zero_mem' := E.lev_one (𝟙 (Spec (CommRingCat.of k)))
  add_mem' {P Q} hP hQ := (E.lev_sub (𝟙 (Spec (CommRingCat.of k))) (P : Pt E) (Q : Pt E) hP hQ).1
  neg_mem' {P} hP := (E.lev_sub (𝟙 (Spec (CommRingCat.of k))) (P : Pt E) (P : Pt E) hP hP).2

theorem mem_levSub_iff (P : ↥(orbit E P₀)) : P ∈ levSub E P₀ ↔ FactorsThrough E.lev (P : Pt E) := Iff.rfl

theorem levSub_stable (n : ↥Λ) (P : ↥(orbit E P₀)) (hP : P ∈ levSub E P₀) : rho E hO P₀ n P ∈ levSub E P₀ :=
  E.lev_stable n (𝟙 (Spec (CommRingCat.of k))) (P : Pt E) hP

theorem mem_orbit_of_nsmul_eq_zero (ℓ : ℕ)
    (hgen : ∀ P : Pt E, nsmulPt E.L (𝟙 (Spec (CommRingCat.of k))) ℓ P = E.L.one (𝟙 (Spec (CommRingCat.of k))) →
      ∃ m : ↥Λ, P = pushPt (E.act m) (E.act_over m) P₀)
    (P : Pt E) (hP : ℓ • P = 0) : P ∈ orbit E P₀ := by
  rw [← nsmulPt_eq_nsmul] at hP
  obtain ⟨m, hm⟩ := hgen P hP
  exact (mem_orbit_iff E P₀ P).2 ⟨m, hm⟩

theorem nsmul_eq_zero_of_factorsThrough {ℓ : ℕ} (K : E.ExtraLevel ℓ) (P : Pt E) (hP : FactorsThrough K.levK P) :
    ℓ • P = 0 := by
  rw [← nsmulPt_eq_nsmul]
  exact K.levK_torsion (𝟙 (Spec (CommRingCat.of k))) P hP

noncomputable def levKSub {ℓ : ℕ} (K : E.ExtraLevel ℓ) : AddSubgroup ↥(orbit E P₀) where
  carrier := {P | FactorsThrough K.levK (P : Pt E)}
  zero_mem' := K.levK_one (𝟙 (Spec (CommRingCat.of k)))
  add_mem' {P Q} hP hQ := (K.levK_sub (𝟙 (Spec (CommRingCat.of k))) (P : Pt E) (Q : Pt E) hP hQ).1
  neg_mem' {P} hP := (K.levK_sub (𝟙 (Spec (CommRingCat.of k))) (P : Pt E) (P : Pt E) hP hP).2

theorem levKSub_stable {ℓ : ℕ} (K : E.ExtraLevel ℓ) (n : ↥Λ) (P : ↥(orbit E P₀)) (hP : P ∈ levKSub E P₀ K) :
    rho E hO P₀ n P ∈ levKSub E P₀ K :=
  K.levK_stable n (𝟙 (Spec (CommRingCat.of k))) (P : Pt E) hP

end Lines
p2m_reactivate "P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_exists_extraLevel_enum.CerednikDrinfeld P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_exists_extraLevel_enum.CerednikDrinfeld.QM P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_exists_extraLevel_enum.CerednikDrinfeld.QM.EnumAux"

end CerednikDrinfeld.QM.EnumAux
p2m_reactivate "P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_exists_extraLevel_enum.CerednikDrinfeld P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_exists_extraLevel_enum.CerednikDrinfeld.QM P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_exists_extraLevel_enum.CerednikDrinfeld.QM.EnumAux"
p2m_reactivate "P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_exists_extraLevel_enum.CerednikDrinfeld P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_exists_extraLevel_enum.CerednikDrinfeld.QM P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_exists_extraLevel_enum.CerednikDrinfeld.QM.EnumAux"
p2m_reactivate "P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_exists_extraLevel_enum.CerednikDrinfeld P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_exists_extraLevel_enum.CerednikDrinfeld.QM P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_exists_extraLevel_enum.CerednikDrinfeld.QM.EnumAux"

theorem solution
    {q q' : ℕ} [Fact q.Prime] [Fact q'.Prime] (hqq' : q' ≠ q)
    {a b : ℚ} (hB : IsIndefiniteRamifiedExactlyAt a b q q')
    (Λ : Submodule ℤ ℍ[ℚ, a, b]) (hΛ : IsMaximalOrder Λ) {N : ℕ} [NeZero N]
    (ℓ : ℕ) [Fact ℓ.Prime] (hℓq : ℓ ≠ q) (hℓq' : ℓ ≠ q')
    (k : Type) [Field k] [IsAlgClosed k] (hℓk : (ℓ : k) ≠ 0) (hNk : (N : k) ≠ 0)
    (E : FakeEllipticCurve Λ N k) :
    ∃ (n : ℕ) (K : Fin n → E.ExtraLevel ℓ),
      (n = if ℓ ∣ N then ℓ else ℓ + 1) ∧
      (∀ i j : Fin n,
          (∀ x : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) E.f,
            FactorsThrough (K i).levK x ↔ FactorsThrough (K j).levK x) → i = j) ∧
      (∀ K' : E.ExtraLevel ℓ, ∃ i : Fin n,
          ∀ x : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) E.f,
            FactorsThrough K'.levK x ↔ FactorsThrough (K i).levK x) := by
  classical
  obtain ⟨P₀, hP₀, hP₀gen, hP₀ann⟩ :=
    CerednikDrinfeld.QM.FakeEllipticCurve.exists_generator_torsionPoints_of_isMaximalOrder_of_prime hB Λ hΛ k E ℓ hℓk
  have hO : IsOrder Λ := hΛ.1
  have hannA : ∀ m : ↥Λ, EnumAux.actPt E m P₀ = 0 ↔
      ∃ m' : ↥Λ, (m : ℍ[ℚ, a, b]) = ((ℓ : ℚ) : ℍ[ℚ, a, b]) * (m' : ℍ[ℚ, a, b]) := fun m => hP₀ann m
  have hannR : ∀ m : ↥Λ, EnumAux.rho E hO P₀ m (EnumAux.basePt E hO P₀) = 0 ↔
      ∃ m' : ↥Λ, (m : ℍ[ℚ, a, b]) = ((ℓ : ℚ) : ℍ[ℚ, a, b]) * (m' : ℍ[ℚ, a, b]) := fun m => by
    rw [← hannA m]
    exact ⟨fun h => congrArg Subtype.val h, fun h => Subtype.ext h⟩
  obtain ⟨hLa, hLb, hLc, hLd⟩ := QuaternionAlgebra.IsMaximalOrder.lineImage_classification hqq' hB Λ hΛ ℓ hℓq hℓq'
    (↥(EnumAux.orbit E P₀)) (EnumAux.rho E hO P₀) (EnumAux.rho_one E hO P₀) (EnumAux.rho_mul E hO P₀) (EnumAux.rho_add E hO P₀)
    (EnumAux.basePt E hO P₀) (EnumAux.hgen E hO P₀) hannR

  let bad : Submodule ℤ ℍ[ℚ, a, b] → Prop := fun J =>
    ∀ m : ↥Λ, (m : ℍ[ℚ, a, b]) ∈ J → FactorsThrough E.lev (pushPt (E.act m) (E.act_over m) P₀)
  let Line := {J : Submodule ℤ ℍ[ℚ, a, b] // EnumAux.IsLine Λ ℓ J}
  let Good := {J : Submodule ℤ ℍ[ℚ, a, b] // EnumAux.IsLine Λ ℓ J ∧ ¬ bad J}
  have hC3 : Nat.card Line = ℓ + 1 :=
    (QuaternionAlgebra.IsMaximalOrder.natCard_properLine_eq_and_inf_eq hqq' hB Λ hΛ ℓ hℓq hℓq').1
  have hC5 : Nat.card {J : Submodule ℤ ℍ[ℚ, a, b] // EnumAux.IsLine Λ ℓ J ∧ bad J} = (if ℓ ∣ N then 1 else 0) :=
    CerednikDrinfeld.QM.FakeEllipticCurve.natCard_properLine_image_subset_lev hqq' hB Λ hΛ ℓ hℓq hℓq' k hℓk hNk E P₀ hP₀ hP₀gen hP₀ann
  haveI hfinL : Finite Line := Nat.finite_of_card_ne_zero (by rw [hC3]; omega)
  have hGood : Nat.card Good = (if ℓ ∣ N then ℓ else ℓ + 1) := by
    have hsplit : Nat.card Line = Nat.card {J : Submodule ℤ ℍ[ℚ, a, b] // EnumAux.IsLine Λ ℓ J ∧ bad J} + Nat.card Good := by
      rw [← Nat.card_congr (Equiv.subtypeSubtypeEquivSubtypeInter (fun J => EnumAux.IsLine Λ ℓ J) bad),
        ← Nat.card_congr (Equiv.subtypeSubtypeEquivSubtypeInter (fun J => EnumAux.IsLine Λ ℓ J) (fun J => ¬ bad J)),
        ← Nat.card_sum, Nat.card_congr (Equiv.sumCompl (fun J : Line => bad J.1))]
    rw [hC3, hC5] at hsplit
    split_ifs at hsplit ⊢ <;> omega

  have hK : ∀ J : Good, ∃ K : E.ExtraLevel ℓ,
      ∀ P : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) E.f, FactorsThrough K.levK P ↔ P ∈ EnumAux.img E P₀ J.1 := by
    intro J
    obtain ⟨⟨e, he⟩, hst⟩ := hLa J.1 J.2.1
    refine CerednikDrinfeld.QM.FakeEllipticCurve.exists_extraLevel_of_equiv_points Λ ℓ k hℓk E (EnumAux.img E P₀ J.1)
      (e.trans (EnumAux.imgEquiv E hO P₀ J.1)) ?_ ?_ ?_
    · intro x y
      show ((e (x + y) : ↥(EnumAux.orbit E P₀)) : EnumAux.Pt E) =
        ((e x : ↥(EnumAux.orbit E P₀)) : EnumAux.Pt E) + ((e y : ↥(EnumAux.orbit E P₀)) : EnumAux.Pt E)
      rw [he x y]
      rfl
    · intro m P hP
      obtain ⟨m₁, hm₁, rfl⟩ := hP
      obtain ⟨m₂, hm₂, h2⟩ := hst m ⟨EnumAux.actPt E m₁ P₀, (EnumAux.mem_orbit_iff E P₀ _).2 ⟨m₁, rfl⟩⟩ ⟨m₁, hm₁, Subtype.ext rfl⟩
      exact ⟨m₂, hm₂, congrArg Subtype.val h2⟩
    · intro P hP hC
      rcases hLd (EnumAux.levSub E P₀) (EnumAux.levSub_stable E hO P₀) J.1 J.2.1 with h0 | hall
      · obtain ⟨m₁, hm₁, rfl⟩ := hP
        exact congrArg Subtype.val
          (h0 ⟨EnumAux.actPt E m₁ P₀, (EnumAux.mem_orbit_iff E P₀ _).2 ⟨m₁, rfl⟩⟩ ⟨m₁, hm₁, Subtype.ext rfl⟩ hC)
      · exact absurd (fun m hm => hall ⟨EnumAux.actPt E m P₀, (EnumAux.mem_orbit_iff E P₀ _).2 ⟨m, rfl⟩⟩ ⟨m, hm, Subtype.ext rfl⟩) J.2.2
  choose Kfun hKfun using hK
  have hℓ2 : 2 ≤ ℓ := (Fact.out : ℓ.Prime).two_le
  haveI hfinG : Finite Good := Nat.finite_of_card_ne_zero (by rw [hGood]; split_ifs <;> omega)
  refine ⟨Nat.card Good, fun i => Kfun ((Finite.equivFin Good).symm i), hGood, ?_, ?_⟩
  ·
    intro i j hij
    apply (Finite.equivFin Good).symm.injective
    apply Subtype.ext
    apply EnumAux.img_injective E P₀ ℓ hannA ((Finite.equivFin Good).symm i).2.1 ((Finite.equivFin Good).symm j).2.1
    ext P
    rw [← hKfun, ← hKfun]
    exact hij P
  ·
    intro K'
    obtain ⟨e', he'⟩ := CerednikDrinfeld.QM.FakeEllipticCurve.ExtraLevel.exists_equiv_points ℓ k hℓk E K'
    let S : AddSubgroup ↥(EnumAux.orbit E P₀) := EnumAux.levKSub E P₀ K'
    let toOrb : {P : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) E.f // FactorsThrough K'.levK P} → ↥S := fun P =>
      ⟨⟨P.1, EnumAux.mem_orbit_of_nsmul_eq_zero E P₀ ℓ hP₀gen P.1 (EnumAux.nsmul_eq_zero_of_factorsThrough E K' P.1 P.2)⟩, P.2⟩
    let e'' : ZMod ℓ × ZMod ℓ ≃ ↥S := e'.trans
      { toFun := toOrb, invFun := fun Q => ⟨Q.1.1, Q.2⟩, left_inv := fun _ => rfl, right_inv := fun _ => rfl }
    obtain ⟨J, ⟨hJ, hJS⟩, -⟩ := hLc S (EnumAux.levKSub_stable E hO P₀ K')
      ⟨e'', fun x y => Subtype.ext (he' x y)⟩
    have hJgood : ¬ bad J := by
      intro hb
      have h0 : ((e' 0 : {P : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) E.f // FactorsThrough K'.levK P}) : EnumAux.Pt E) = 0 :=
        EnumAux.equiv_map_zero (S := {P : EnumAux.Pt E | FactorsThrough K'.levK P}) e' he'
      have hne : ((e' (1, 0) : {P : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) E.f // FactorsThrough K'.levK P}) : EnumAux.Pt E) ≠ 0 := by
        intro h1
        have : e' (1, 0) = e' 0 := Subtype.ext (h1.trans h0.symm)
        have := e'.injective this
        simp at this
      apply hne
      obtain ⟨m, hm, hPm⟩ := (hJS (toOrb (e' (1, 0)))).1 (e' (1, 0)).2
      have hcoe : ((e' (1, 0) : {P : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) E.f // FactorsThrough K'.levK P}) : EnumAux.Pt E) =
          EnumAux.actPt E m P₀ := congrArg (fun Q : ↥(EnumAux.orbit E P₀) => (Q : EnumAux.Pt E)) hPm
      have hC : FactorsThrough E.lev ((e' (1, 0) : {P : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) E.f // FactorsThrough K'.levK P}) : EnumAux.Pt E) := by
        rw [hcoe]; exact hb m hm
      exact K'.levK_disjoint (𝟙 (Spec (CommRingCat.of k))) _ (e' (1, 0)).2 hC
    refine ⟨Finite.equivFin Good ⟨J, hJ, hJgood⟩, fun P => ?_⟩
    rw [hKfun, Equiv.symm_apply_apply]
    constructor
    · intro hP
      have hPorb := EnumAux.mem_orbit_of_nsmul_eq_zero E P₀ ℓ hP₀gen P (EnumAux.nsmul_eq_zero_of_factorsThrough E K' P hP)
      obtain ⟨m, hm, hPm⟩ := (hJS ⟨P, hPorb⟩).1 hP
      exact ⟨m, hm, congrArg Subtype.val hPm⟩
    · rintro ⟨m, hm, rfl⟩
      exact (hJS ⟨EnumAux.actPt E m P₀, (EnumAux.mem_orbit_iff E P₀ _).2 ⟨m, rfl⟩⟩).2 ⟨m, hm, Subtype.ext rfl⟩

end S_CerednikDrinfeld_QM_FakeEllipticCurve_exists_extraLevel_enum
end P2MW
export P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_exists_extraLevel_enum (solution)
