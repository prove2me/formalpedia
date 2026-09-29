-- Prove2me | solution 1 for CerednikDrinfeld.QM.FakeEllipticCurve.exists_zmod_prod_equiv_factorsThrough_kernel_dual_of_not_dvd
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.141142+00:00
-- url     : https://prove2.me/submissions/a5c5acab-f130-5d78-9ce2-d42ff6b7dc76

import Definitions.Def_CerednikDrinfeld_QMModuliProps
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawKernel
import Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_isReduced_pullback_one_of_natCast_ne_zero
import Theorems.Thm_AlgebraicGeometry_exists_comp_fromSpecResidueField_eq_of_range_subset_singleton
import Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_natCard_isTorsionPoint_eq_pow_of_natCast_ne_zero
import Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_smoothOfRelativeDimension_two
import Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_nsmul_surjective_of_isAlgClosed_of_connectedSpace
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_exists_zmod_prod_equiv_factorsThrough_kernel_dual_of_not_dvd
p2m_attr_erase "instance" "GoodReductionJacobian.RelativeGroupLaw.isIso_endKerStr_schemeHomOverId AlgebraicGeometry.Scheme.PresheafOfModules.symmetricCategory SheafOfModules.instFaithfulRingSheafPModToPMod SheafOfModules.symmetricCategory AlgebraicGeometry.Scheme.PresheafOfModules.monoidalCategory AlgebraicGeometry.Scheme.PresheafOfModules.monoidalClosed SheafOfModules.instFullRingSheafPModToPMod SheafOfModules.monoidalCategory AlgebraicGeometry.Scheme.Modules.symmetricCategory SheafOfModules.monoidalClosed SheafOfModules.instIsLocalizationPModRingSheafSheafifyFunctorPresheafW SheafOfModules.sheafifyFunctor_monoidal AlgebraicGeometry.Scheme.Modules.monoidalClosed AlgebraicGeometry.instMonoidalPresheafOfModulesModulesSheafify AlgebraicGeometry.Scheme.Modules.monoidalCategory PresheafOfModules.instMonoidalClosed PresheafOfModules.InternalHom.instModuleCarrierObjOppositeCommRingCatSubtypePiFamilyMemAddSubgroupNaturalFamilies PresheafOfModules.InternalHom.instModuleCarrierObjOppositeRingCatCompCommRingCatForget₂RingHomCarrierCarrierAbPresheaf PresheafOfModules.InternalHom.instSMulCarrierObjOppositeCommRingCatSubtypePiFamilyMemAddSubgroupNaturalFamilies AlgebraicGeometry.Scheme.Hom.opensMapFinal AlgebraicGeometry.RelPicard.RigidifiedLineBundle.setoid AlgebraicGeometry.RelPicard.RigidifiedLineBundle.instInhabited AlgebraicGeometry.OModulePresheaf.isScalarTower AlgebraicGeometry.Scheme.OrderedAffineCover.instLinearOrder AlgebraicGeometry.OModulePresheaf.module AlgebraicGeometry.Scheme.OrderedAffineCover.instFintype AlgebraicGeometry.Scheme.OrderedAffineCover.instFintypeIdx AlgebraicGeometry.OModulePresheaf.addCommGroup AlgebraicGeometry.Scheme.OrderedAffineCover.instDecidableEqIdx AlgebraicGeometry.OModulePresheaf.moduleSections TwoChartCech.Sections.M0_moduleA TwoChartCech.Sections.M1_module TwoChartCech.Cover.A01_algebra TwoChartCech.Cover.A0_algebra TwoChartCech.Cover.A1_commRing TwoChartCech.Cover.A1_algebra TwoChartCech.Sections.M01_module TwoChartCech.Sections.M0_addCommGroup TwoChartCech.Sections.M0_tower TwoChartCech.Sections.M01_addCommGroup"
p2m_attr_erase "instance" "TwoChartCech.Cover.A0_commRing TwoChartCech.Sections.M1_tower TwoChartCech.Sections.M01_moduleA TwoChartCech.Sections.M0_module TwoChartCech.Sections.M1_moduleA TwoChartCech.Sections.M1_addCommGroup TwoChartCech.Cover.A01_commRing TwoChartCech.Sections.M01_tower CoherentBaseChange.TwoTermComplex.C0_module CoherentBaseChange.TwoTermComplex.C0_addCommGroup CoherentBaseChange.TwoTermComplex.C1_module CoherentBaseChange.TwoTermComplex.C1_addCommGroup CoherentBaseChange.TwoTermComplex.C0_free CoherentBaseChange.TwoTermComplex.C1_finite CoherentBaseChange.TwoTermComplex.C0_finite CoherentBaseChange.TwoTermComplex.C1_free AlgebraicGeometry.OModulePresheaf.instSubsingletonObjZero AlgebraicGeometry.Scheme.Modules.preservesBinaryProducts_opensMap AlgebraicGeometry.Scheme.Modules.pullback_monoidal AlgebraicGeometry.Scheme.Modules.sheafify_isLocalization' AlgebraicGeometry.Scheme.Modules.preservesTerminal_opensMap AlgebraicGeometry.Scheme.Modules.pullback₀_monoidal AlgebraicGeometry.Scheme.Modules.preservesFiniteProducts_opensMap AlgebraicGeometry.Scheme.Modules.instLiftingPresheafOfModulesSheafifyPresheafWOpensCarrierCarrierCommRingCatGrothendieckTopologyObjFunctorOppositeIsSheafSheafCompPullback₀Pullback PresheafOfModules.PullbackMonoidal.pullback_monoidal PresheafOfModules.PullbackMonoidal.isIso_δ PresheafOfModules.pushforward_laxMonoidal PresheafOfModules.PullbackMonoidal.isIso_η PresheafOfModules.free_monoidal PresheafOfModules.restrictScalars_laxMonoidal PresheafOfModules.PullbackMonoidal.isIso_δ_gS PresheafOfModules.pullback_oplaxMonoidal PresheafOfModules.PullbackMonoidal.instPreservesColimitsOfSizeCompOppositeCommRingCatRingCatForget₂RingHomCarrierCarrierPb PresheafOfModules.pullback_monoidal' AlgebraicGeometry.SmoothOfRelativeDimension.fiberToSpecResidueField AlgebraicGeometry.SmoothOfRelativeDimension.pullback_snd AlgebraicGeometry.SmoothOfRelativeDimension.pullback_fst AlgebraicGeometry.SmoothOfRelativeDimension.smooth_one AlgebraicGeometry.SmoothProperCurve.isIntegral_pullback_Spec_field AlgebraicGeometry.IsProper.fiberToSpecResidueField"
p2m_attr_erase "instance" "AlgebraicCurve.CurveModel.isProper AlgebraicCurve.CurveModel.isIntegral AlgebraicCurve.CurveModel.smooth AlgebraicGeometry.Scheme.LocalRepresentabilityULift.instIsLocallyInjectiveFunUliftYonedaGluedToSheaf AlgebraicGeometry.Scheme.LocalRepresentabilityULift.instIsLocallySurjectiveFunUliftYonedaGluedToSheafOfIsLocallySurjectiveZariskiTopologyDescFunctorOppositeType AlgebraicGeometry.Scheme.LocalRepresentabilityULift.instIsOpenImmersionToGlued AlgebraicGeometry.Scheme.LocalRepresentabilityULift.instIsIsoSheafZariskiTopologyTypeUliftYonedaGluedToSheaf AlgebraicGeometry.RelPicard.instIsOpenImmersionToGlued AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.instFundamentalIdentityOfSumRamificationInertia AlgebraicCurve.Place.instIsScalarTowerResidueFieldRestrictPushforward AlgebraicCurve.Place.instAlgebraResidueFieldRestrictPushforward AlgebraicCurve.Place.instIsLocalHomRestrictInclusion AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions PresheafOfModules.ExteriorPower.instModulePresheafAb AlgebraicGeometry.RelEffCartierDiv.subsingleton_of_degree_zero AlgebraicGeometry.RelEffCartierDiv.isIso_subschemeIota_snd_of_degree_one AlgebraicGeometry.isIso_ker_graphOver_subschemeIota_snd AlgebraicGeometry.isClosedImmersion_graphOver AlgebraicGeometry.FGSubalgebra.instIsDirectedLe AlgebraicGeometry.FGSubalgebra.instQuasiSeparatedSpaceCarrierCarrierCommRingCatObjOppositeSchemeSpecDiagram AlgebraicGeometry.FGSubalgebra.instIsCofilteredOpposite AlgebraicGeometry.FGSubalgebra.instIsAffineObjOppositeSchemeSpecDiagram AlgebraicGeometry.FGSubalgebra.instNonempty AlgebraicGeometry.FGSubalgebra.instNonemptySubtypeLeSubalgebraValFG AlgebraicGeometry.FGSubalgebra.instCompactSpaceCarrierCarrierCommRingCatObjOppositeSchemeSpecDiagram AlgebraicGeometry.FGSubalgebra.instIsDirectedSubtypeLeSubalgebraValFG AlgebraicGeometry.FGSubalgebra.instIsAffineHomMapOppositeSchemeSpecDiagram AlgebraicGeometry.FGSubalgebra.instIsFiltered AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instNeg AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instSMulInt AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instAddCommGroup AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instAdd AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instSub"
p2m_attr_erase "instance" "AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instModuleCarrierObjOppositeOpensCarrierCarrierCommRingCatPresheafOpOpensTop AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instSMulCarrierObjOppositeOpensCarrierCarrierCommRingCatPresheafOpOpensTop AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instSMulNat AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instZero AlgebraicCurve.instHasLocalResidue_of_hasCanonicalLocalResidueK AlgebraicCurve.instHasCanonicalLocalResidueK_of_hasCanonicalLocalResidueKStar AlgebraicCurve.Place.kw_ffgc_finiteDimensional_adicCompletion instAlgebraSubtypeMemValuationSubring_definitions AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersIntegersCompletion ModularCurve.KwF4gRRTate.instAlgebraKAdicCompletionIntegers AlgebraicCurve.Place.kw_ffgc_continuousSMul_adicCompletionComap AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersCompletionCompletion IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions AlgebraicCurve.instHasCanonicalLocalResidueK AlgebraicCurve.Place.instAlgebra_restrictResidueField AlgebraicCurve.Place.instIsScalarTower_restrictResidueField AlgebraicCurve.instHasLocalResidue AlgebraicCurve.HasSeparableResidue.of_perfectField_of_isCurveOver AlgebraicCurve.HasSeparableResidue.of_perfectField AlgebraicCurve.Place.instIsLocalHom_restrictSubringHom AlgebraicCurve.instHasCanonicalLocalResidueKStar ModularCurve.KwNo6Pin.isLocalRing_completion SheafOfModules.isIso_ihomModelToIhom AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instDecidableEqIdx AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instFintype AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instLinearOrder AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instFintypeIdx AlgebraicGeometry.OModulePresheaf.Leray.relAltC_scalarTower AlgebraicGeometry.OModulePresheaf.Leray.ker_relAltd_modΓ AlgebraicGeometry.OModulePresheaf.Leray.relAltC_modΓ AlgebraicGeometry.OModulePresheaf.Leray.biC_abGrp AlgebraicGeometry.OModulePresheaf.Leray.relAltH_modΓ AlgebraicGeometry.OModulePresheaf.Leray.ker_relAltd_smul AlgebraicGeometry.OModulePresheaf.Leray.relAltH_scalarTower AlgebraicGeometry.OModulePresheaf.Leray.relAltH_smul"
p2m_attr_erase "instance" "AlgebraicGeometry.OModulePresheaf.Leray.biC_module DoubleComplex.instModuleE₂I DoubleComplex.Bounded.modR DoubleComplex.instModuleE₂II DoubleComplex.instAddCommGroupE₂II DoubleComplex.Bounded.abGrp DoubleComplex.instAddCommGroupE₂I AlgebraicGeometry.ChowDatum.hι_closed AlgebraicGeometry.ChowDatumProj.hιN_closed AlgebraicGeometry.ChowDatumProj.hp_proper AlgebraicGeometry.ChowDatum.hp_isoU AlgebraicGeometry.ChowDatum.hp_proper AlgebraicGeometry.ProjSpace.algebraAway AlgebraicGeometry.ProjSpace.instIsProperProdOverπ AlgebraicGeometry.ChowDatumProj.hp_isoU AlgebraicGeometry.ProjSpace.isProper_π AlgebraicGeometry.ProjSpace.finiteType_mvPolynomial ProjSpaceCech.GradedModule.H.module ProjSpaceCech.GradedModule.H.addCommGroup ProjSpaceCech.GradedModule.sec.instAdd ProjSpaceCech.GradedModule.sec.instNeg ProjSpaceCech.GradedModule.acg ProjSpaceCech.GradedModule.Frac.setoid ProjSpaceCech.GradedModule.modR ProjSpaceCech.GradedModule.sec.instModule ProjSpaceCech.GradedModule.sec.instAddCommGroup ProjSpaceCech.GradedModule.sec.instZero ProjSpaceCech.GradedModule.Presentation.fJ ProjSpaceCech.GradedModule.sec.instSMul ProjSpaceCech.Twist.H.module ProjSpaceCech.Idx.instFintype ProjSpaceCech.Twist.H.addCommGroup ProjSpaceCech.Idx.instDecidableEq ProjSpaceCech.Twist.Mon.instDecidableEq ProjSpaceCech.Twist.cochain.instAddCommGroup ProjSpaceCech.Twist.cochain.instModule AlgebraicGeometry.FGSubalgebra.tensorStage_directedSystem AlgebraicGeometry.RelEffCartierDiv.isClosedImmersion_subschemeι_resProdMap AlgebraicGeometry.RelEffCartierDiv.isOpenImmersion_resProdMap AlgebraicCurve.CurveModel.locallyOfFiniteType_gluedToBase"
p2m_attr_erase "instance" "AlgebraicCurve.CurveModel.isFractionRing_overlap AlgebraicCurve.CurveModel.isLocallyNoetherian_glued AlgebraicCurve.CurveModel.jacobsonSpace_glued AlgebraicCurve.CurveModel.isOpenImmersion_ι₀ AlgebraicCurve.CurveModel.isIntegral_glued AlgebraicCurve.CurveModel.quasiSeparated_gluedToBase AlgebraicCurve.CurveModel.compactSpace_glued AlgebraicCurve.CurveModel.isIntegral_adjoin_chartRing AlgebraicCurve.CurveModel.isFractionRing_overlap_functionField AlgebraicCurve.CurveModel.isProper_gluedToBase AlgebraicCurve.CurveModel.isOpenImmersion_ιU AlgebraicCurve.CurveModel.isOpenImmersion_f₀ AlgebraicCurve.CurveModel.isOpenImmersion_fInf AlgebraicCurve.CurveModel.isOpenImmersion_ιInf AlgebraicCurve.CurveModel.algebra_overlap_functionField AlgebraicCurve.CurveModel.quasiCompact_gluedToBase AlgebraicCurve.CurveModel.algebraAdjoin AlgebraicCurve.CurveModel.isDedekindDomain_chartRing AlgebraicCurve.CurveModel.isIntegralClosure AlgebraicCurve.CurveModel.finite_chartRing AlgebraicCurve.CurveModel.centre_isPrime AlgebraicCurve.CurveModel.isFractionRing_chartRing AlgebraicCurve.CurveModel.finiteType_chartRing AlgebraicCurve.CurveModel.isNoetherianRing_chartRing AlgebraicCurve.CurveModel.isScalarTower_base_adjoin AlgebraicCurve.CurveModel.isScalarTower_adjoin AlgebraicCurve.CurveModel.chartRing_finitePresentation instTopologicallyFGOfFiniteType AlgebraicGeometry.ProjSpace.twistObj.addCommGroup AlgebraicGeometry.ProjSpace.twistFam.module AlgebraicGeometry.ProjSpace.twistObj.module AlgebraicGeometry.ProjSpace.twistObj.moduleSections AlgebraicGeometry.ProjSpace.twistFam.addCommGroup"
p2m_attr_erase "simp" "NeronModelInfra.schemeHomOverNpow_succ NeronModelInfra.schemeHomOverNpow_zero NeronModelInfra.NeronModelPropertyBundle.endExtensionEquiv_symm_restrict NeronModelInfra.schemeHomOverComp_id_left NeronModelInfra.schemeHomOverComp_id_right NeronModelInfra.schemeHomOverId_coe NeronModelInfra.NeronModelPropertyBundle.endExtensionEquiv_apply NeronModelInfra.NeronModelPropertyBundle.restrict_endExtensionEquiv_symm NeronModelInfra.schemeHomOverComp_coe GoodReductionJacobian.relativeGroupLawOfGrpObj_inv GoodReductionJacobian.relativeGroupLawOfGrpObj_mul GoodReductionJacobian.overHomEquivSchemeHomOver_apply_coe GoodReductionJacobian.relativeGroupLawOfGrpObj_one GoodReductionJacobian.overHomEquivSchemeHomOver_symm_apply_left SheafOfModules.tensorUnit_eq AlgebraicGeometry.Scheme.Modules.tensorUnit_eq PresheafOfModules.InternalHom.presheaf_map_apply PresheafOfModules.InternalHom.curryFamily_app PresheafOfModules.InternalHom.add_app PresheafOfModules.InternalHom.smul_app PresheafOfModules.InternalHom.zero_app PresheafOfModules.ihomObj_map_val PresheafOfModules.ihomFunctor_map PresheafOfModules.InternalHom.restrict_app PresheafOfModules.InternalHom.postcomp_app PresheafOfModules.InternalHom.neg_app PresheafOfModules.curry'_app_val PresheafOfModules.InternalHom.presheaf_obj PresheafOfModules.ihomFunctor_obj PresheafOfModules.ihomObj_obj PresheafOfModules.InternalHom.sub_app PresheafOfModules.ihomMap_app_val AlgebraicGeometry.Scheme.Modules.tensorPow_zero AlgebraicGeometry.Scheme.Modules.tensorPow_succ AlgebraicGeometry.RelPicard.RigidifiedLineBundle.mk.sizeOf_spec AlgebraicGeometry.RelPicard.RigidifiedLineBundle.mk.injEq AlgebraicGeometry.Scheme.OrderedAffineCover.mk.injEq AlgebraicGeometry.OModulePresheaf.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCover.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.mk.injEq"
p2m_attr_erase "simp" "AlgebraicGeometry.Scheme.TwoAffineOpenCover.mk.injEq AlgebraicGeometry.Scheme.TwoAffineOpenCover.mk.sizeOf_spec AlgebraicGeometry.Scheme.TwoAffineOpenCover.pullback_U1 AlgebraicGeometry.Scheme.TwoAffineOpenCover.pullback_U0 TwoChartCech.Sections.mk.injEq TwoChartCech.Cover.mk.injEq TwoChartCech.GrothendieckComplex.mk.injEq TwoChartCech.Sections.mk.sizeOf_spec TwoChartCech.Cover.mk.sizeOf_spec TwoChartCech.Cover.lineBundle_r0_apply TwoChartCech.GrothendieckComplex.mk.sizeOf_spec TwoChartCech.Cover.lineBundle_r1_apply CoherentBaseChange.TwoTermComplex.mk.sizeOf_spec CoherentBaseChange.TwoTermComplex.mk.injEq AlgebraicGeometry.OModulePresheaf.prod_obj AlgebraicGeometry.OModulePresheaf.restrOpen_obj AlgebraicGeometry.OModulePresheaf.DevissageStep.mk.injEq AlgebraicGeometry.OModulePresheaf.pushforward_obj AlgebraicGeometry.OModulePresheaf.im_obj AlgebraicGeometry.OModulePresheaf.pow_obj AlgebraicGeometry.OModulePresheaf.fstHom_app AlgebraicGeometry.OModulePresheaf.ker_obj AlgebraicGeometry.OModulePresheaf.coker_obj AlgebraicGeometry.OModulePresheaf.DevissageStep.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCover.preimage_U AlgebraicGeometry.OModulePresheaf.sndHom_app AlgebraicGeometry.OModulePresheaf.Hom.mk.injEq AlgebraicGeometry.OModulePresheaf.Hom.id_app AlgebraicGeometry.OModulePresheaf.AffHom.appSections_apply AlgebraicGeometry.OModulePresheaf.AffHom.comp_app AlgebraicGeometry.OModulePresheaf.AffSES.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.AffHom.kerMap_coe AlgebraicGeometry.OModulePresheaf.AffHom.id_app AlgebraicGeometry.OModulePresheaf.Hom.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.Hom.toAffHom_app AlgebraicGeometry.OModulePresheaf.SES.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.AffHom.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.Hom.comp_app AlgebraicGeometry.OModulePresheaf.SES.mk.injEq AlgebraicGeometry.OModulePresheaf.AffHom.mk.injEq"
p2m_attr_erase "simp" "AlgebraicGeometry.OModulePresheaf.Hom.appSections_apply AlgebraicGeometry.OModulePresheaf.AffSES.mk.injEq PresheafOfModules.freeεIso_hom_app PresheafOfModules.freeμIso_hom_app AlgebraicGeometry.RelPicard.RepresentsRelSubPic.mk.injEq AlgebraicGeometry.RelPicard.SubPicCondition.mk.injEq AlgebraicGeometry.RelPicard.SubPicCondition.mk.sizeOf_spec AlgebraicGeometry.RelPicard.RepresentsRelSubPic.mk.sizeOf_spec AlgebraicGeometry.SmoothProperCurve.sectionBaseChange_coe_snd AlgebraicGeometry.SmoothProperCurve.sectionBaseChange_coe_fst AlgebraicCurve.CurveModel.mk.injEq AlgebraicCurve.CurveModel.mk.sizeOf_spec AlgebraicCurve.mulAdele_apply AlgebraicCurve.residuePairing_apply_coe AlgebraicCurve.mem_adeleBdd AlgebraicCurve.weilSmul_one AlgebraicCurve.diagonalHom_apply AlgebraicCurve.weilSmul_apply AlgebraicCurve.adeleSpaceMul_coe AlgebraicCurve.mulAdele_one AlgebraicGeometry.SmoothProperCurve.FiniteMapData.twoAffineOpenCover_U1 AlgebraicGeometry.SmoothProperCurve.FiniteMapData.mk.injEq AlgebraicGeometry.SmoothProperCurve.FiniteMapData.mk.sizeOf_spec AlgebraicGeometry.SmoothProperCurve.FiniteMapData.twoAffineOpenCover_U0 AlgebraicGeometry.RelPicard.SubPicCondition.onClasses_mk AlgebraicGeometry.RelPicard.relSubPicPresheaf_map_coe CategoryTheory.Functor.OverTotal.ofFibre_fst CategoryTheory.Functor.overTotal_map_fst AlgebraicGeometry.Scheme.LocalRepresentabilityULift.glueData_J AlgebraicGeometry.Scheme.LocalRepresentabilityULift.uliftYoneda_toGlued_uliftYonedaGluedToSheaf AlgebraicGeometry.Scheme.LocalRepresentabilityULift.glueData_t' AlgebraicGeometry.Scheme.LocalRepresentabilityULift.uliftYoneda_toGlued_uliftYonedaGluedToSheaf_assoc AlgebraicGeometry.Scheme.LocalRepresentabilityULift.uliftYonedaGluedToSheaf_app_toGlued AlgebraicGeometry.Scheme.LocalRepresentabilityULift.glueData_openCover_map AlgebraicGeometry.Scheme.LocalRepresentabilityULift.uliftYonedaGluedToSheaf_app_comp AlgebraicGeometry.Scheme.LocalRepresentabilityULift.glueData_V AlgebraicGeometry.Scheme.LocalRepresentabilityULift.glueData_t AlgebraicGeometry.Scheme.LocalRepresentabilityULift.glueData_U AlgebraicGeometry.Scheme.LocalRepresentabilityULift.glueData_f AlgebraicGeometry.RelPicard.designationOfRepresentableBy_P"
p2m_attr_erase "simp" "AlgebraicGeometry.RelPicard.designationOfRepresentableBy_toBase AlgebraicGeometry.RelPicard.rigSection_snd AlgebraicGeometry.RelPicard.RigidifiedLineBundle.ofInvertible_L AlgebraicGeometry.RelPicard.rigSection_snd_assoc AlgebraicGeometry.RelPicard.SubPicGroupCondition.mk.injEq AlgebraicGeometry.RelPicard.SubPicGroupCondition.mk.sizeOf_spec AlgebraicCurve.coe_cechH0Equiv_apply AlgebraicCurve.cechH1ToH1_mk AlgebraicCurve.lSpaceOn_univ AlgebraicCurve.lSpaceOn_empty AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.Divisor.mapRestrict_single AlgebraicCurve.Divisor.pushforward_single AlgebraicCurve.Place.coe_restrictInclusion AlgebraicCurve.Place.mem_fiber AlgebraicCurve.Place.restrict_toValuationSubring AlgebraicCurve.Divisor.degree_pushforward AlgebraicCurve.Place.restrictResidueMap_residue AlgebraicCurve.Pic0.coe_pushforwardDegZeroHom AlgebraicCurve.Pic0.coe_pullbackDegZeroHom AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk"
p2m_attr_erase "simp" "ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Divisor.degree_pushforwardAlong AlgebraicCurve.Pic0.coe_degZeroCorrespondence AlgebraicCurve.Place.mem_fiberAlong AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.jqNModC_one ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one AlgebraicCurve.Place.differentialCoeff_zero AlgebraicCurve.Place.differentialCoeff_dCoord AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.injEq AlgebraicCurve.TranscendenceTower.mk.injEq AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec AlgebraicCurve.PoleDivisorPackage.mk.injEq AlgebraicGeometry.RelPicard.thetaBundle_def AlgebraicGeometry.RelPicard.picardBundle_def AlgebraicGeometry.RelEffCartierDiv.toRelEffDivisor_ofRelEffDivisor AlgebraicGeometry.RelEffCartierDiv.toRelEffDivisor_I AlgebraicGeometry.mapOnProdOver_fst_assoc AlgebraicGeometry.RelEffCartierDiv.mk.sizeOf_spec AlgebraicGeometry.RelEffCartierDiv.mk.injEq"
p2m_attr_erase "simp" "AlgebraicGeometry.mapOnProdOver_snd AlgebraicGeometry.mapOnProdOver_fst AlgebraicGeometry.mapOnProdOver_snd_assoc AlgebraicGeometry.mapOnProdOver_id AlgebraicCurve.RelEffDivisor.mk.sizeOf_spec AlgebraicCurve.mapOnProd_fst AlgebraicCurve.mapOnProd_fst_assoc AlgebraicCurve.mapOnProd_snd AlgebraicCurve.UnivDivisorPack.mk.injEq AlgebraicCurve.RelEffDivisor.mk.injEq AlgebraicCurve.UnivDivisorPack.mk.sizeOf_spec AlgebraicCurve.mapOnProd_snd_assoc AlgebraicGeometry.Scheme.Modules.exteriorPower_obj PresheafOfModules.exteriorPower_map_ιMulti PresheafOfModules.ExteriorPower.appₗ_apply AlgebraicGeometry.prodKerGraph_one AlgebraicGeometry.fibrePowOver.proj_comp AlgebraicGeometry.prodKerGraph_zero AlgebraicGeometry.RelEffCartierDiv.empty_I AlgebraicGeometry.fibrePowOver.proj_comp_assoc AlgebraicGeometry.graphOver_fst_assoc AlgebraicGeometry.RelEffCartierDiv.toPoint_comp AlgebraicGeometry.RelEffCartierDiv.toPoint_comp_assoc AlgebraicGeometry.graphOver_fst AlgebraicGeometry.RelEffCartierDiv.ofPoint_I AlgebraicGeometry.graphOver_snd AlgebraicGeometry.graphOver_snd_assoc AlgebraicCurve.SymmetricPowerPackage.mk.sizeOf_spec AlgebraicCurve.SymmetricPowerPackage.mk.injEq AlgebraicGeometry.FGSubalgebra.cocone_ι_app_apply AlgebraicGeometry.RelPicard.fst_toProdSpec AlgebraicGeometry.RelPicard.toProdSpec_fst_assoc AlgebraicGeometry.RelPicard.pointsSubBasepointModule_cons AlgebraicGeometry.RelPicard.pointsSubBasepointModule_nil AlgebraicGeometry.RelPicard.fst_toProdSpec_assoc AlgebraicGeometry.RelPicard.toProdSpec_fst AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.sub_app AlgebraicGeometry.Scheme.IdealSheafData.sres_sresTop AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.add_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.mk.sizeOf_spec"
p2m_attr_erase "simp" "AlgebraicGeometry.Scheme.IdealSheafData.coe_resLE AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.smul_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.coe_ofLE_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.ideal_range AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.zero_app AlgebraicGeometry.Scheme.IdealSheafData.sres_sres AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.comp_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.neg_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.id_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.coe_mulRight_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.nsmul_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.mk.injEq AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.zsmul_app AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.sizeOf_spec AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.injEq AlgebraicCurve.adeleSingle_coe AlgebraicCurve.kaehlerResidueTermKFam_apply AlgebraicCurve.Place.LocalResidueData.mk.injEq AlgebraicCurve.Place.LocalResidueData.mk.sizeOf_spec AlgebraicCurve.Place.kw_ffgc_adicCompletionComapIntegers_coe AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.sizeOf_spec AlgebraicCurve.Place.mem_simplePoleSubmodule AlgebraicCurve.Place.coe_uniformizerSubring ModularCurve.Lg37.Lg37CompletionSection.mk.injEq AlgebraicCurve.Place.CoefficientFieldSection.mk.injEq AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.injEq ModularCurve.Lg37.Lg37CompletionSection.mk.sizeOf_spec AlgebraicCurve.Place.CoefficientFieldSection.mk.sizeOf_spec AlgebraicCurve.Place.poleSubmodule_one AlgebraicCurve.Place.mem_poleSubmodule AlgebraicGeometry.Scheme.Modules.toUnitSection_ofUnitSection AlgebraicGeometry.Scheme.Modules.pullbackSection_def AlgebraicGeometry.Scheme.Modules.ofUnitSection_toUnitSection PresheafOfModules.InternalHom.IsSheafAux.appAt_toPresheafHom SheafOfModules.ihomSectionsEquivFamily_unit AlgebraicGeometry.Scheme.Modules.restrictHomEquivFamily_apply SheafOfModules.ihomEval_unit_app AlgebraicGeometry.Scheme.Modules.ihomEval_zero_right AlgebraicGeometry.Scheme.Modules.ihomEval_zero_left AlgebraicGeometry.Scheme.Modules.homOfFamily_app_apply"
p2m_attr_erase "simp" "SheafOfModules.unit_ihomSectionsEquivFamily AlgebraicGeometry.Scheme.Modules.familyOfHom_app AlgebraicGeometry.Scheme.Modules.restrictUnitIso_hom_app_apply AlgebraicGeometry.Scheme.Modules.restrictUnitIso_inv_app_apply AlgebraicGeometry.Scheme.Modules.restrictHomOfFamily_app_apply AlgebraicGeometry.Scheme.Modules.restrictHomEquivFamily_symm_apply AlgebraicGeometry.Scheme.Modules.tensorSections_zero_right AlgebraicGeometry.Scheme.Modules.map_unitSection AlgebraicGeometry.Scheme.Modules.tensorSectionsBilin_apply AlgebraicGeometry.Scheme.Modules.tensorPowSection_zero AlgebraicGeometry.Scheme.Modules.tensorSections_zero_left AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_neg AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_zero AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_sub AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_add AlgebraicGeometry.Scheme.OrderedAffineCover.toCoverOf_U AlgebraicGeometry.Scheme.OrderedAffineCoverOf.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCoverOf.mk.injEq AlgebraicGeometry.Scheme.OrderedAffineCover.restrict_U AlgebraicGeometry.OModulePresheaf.Leray.restrictToPreimage_U DoubleComplex.Bounded.mk.injEq DoubleComplex.Bounded.mk.sizeOf_spec DoubleComplex.Convergence.mk.injEq DoubleComplex.Convergence.mk.sizeOf_spec DoubleComplex.SubQuot.mk.sizeOf_spec DoubleComplex.SubQuot.mk.injEq AlgebraicGeometry.ChowDatumProj.mk.sizeOf_spec AlgebraicGeometry.ChowDatum.mk.sizeOf_spec AlgebraicGeometry.ChowDatumProj.mk.injEq AlgebraicGeometry.ChowDatum.mk.injEq ProjSpaceCech.GradedModule.mk.injEq ProjSpaceCech.GradedModule.mk.sizeOf_spec ProjSpaceCech.GradedModule.Frac.mk.sizeOf_spec ProjSpaceCech.GradedModule.Presentation.mk.injEq ProjSpaceCech.GradedModule.Frac.mk.injEq ProjSpaceCech.GradedModule.Presentation.mk.sizeOf_spec ProjSpaceCech.GradedModule.Hom.shift_toLinearMap ProjSpaceCech.GradedModule.Hom.mk.sizeOf_spec ProjSpaceCech.GradedModule.Hom.mk.injEq TwoChartCech.Mumford.dK_apply"
p2m_attr_erase "simp" "TwoChartCech.Mumford.ι0_apply TwoChartCech.Mumford.ι1_apply TwoChartCech.KerCoprod.dK_apply TwoChartCech.KerCoprod.ι1_apply TwoChartCech.KerCoprod.ι0_apply AlgebraicGeometry.tilde.functorCompPullbackSpecIso_app AlgebraicGeometry.RelPicard.algEquivZeroGroupCut_toSubPicCondition AlgebraicGeometry.RelPicard.LFP.stageHom_val AlgebraicGeometry.RelPicard.BaseChange.relSubPicPresheafRestrictIso_hom_app_coe AlgebraicGeometry.RelPicard.BaseChange.relSubPicPresheafRestrictIso_inv_app_coe AlgebraicGeometry.RelPicard.BaseChange.restrict_P AlgebraicGeometry.RelEffCartierDiv.IsUniversal.lift_comp AlgebraicGeometry.RelEffCartierDiv.functor_map_fst AlgebraicGeometry.RelEffCartierDiv.IsUniversal.homEquiv_apply AlgebraicGeometry.RelEffCartierDiv.IsUniversal.lift_pullbackAlong AlgebraicGeometry.RelEffCartierDiv.IsUniversal.homEquiv_symm_apply AlgebraicGeometry.RelEffCartierDiv.IsUniversal.lift_comp_assoc AlgebraicGeometry.RelEffCartierDiv.supportedIn_top AlgebraicGeometry.RelEffCartierDiv.mem_supportedIn_iff AlgebraicGeometry.RelEffCartierDiv.supportedIn_top_eq AlgebraicGeometry.RelEffCartierDiv.restrictAlong_extendAlong AlgebraicGeometry.RelEffCartierDiv.extendAlong_I AlgebraicGeometry.RelEffCartierDiv.resProdMap_snd AlgebraicGeometry.RelEffCartierDiv.restrictAlong_I AlgebraicGeometry.RelEffCartierDiv.extendAlong_restrictAlong AlgebraicGeometry.RelEffCartierDiv.resProdMap_fst_assoc AlgebraicGeometry.RelEffCartierDiv.resProdMap_snd_assoc AlgebraicGeometry.RelEffCartierDiv.resProdMap_fst CoherentBaseChange.FibreH0Family.mk.sizeOf_spec CoherentBaseChange.FibreH0Family.mk.injEq AlgebraicGeometry.Scheme.Modules.ProjPresentation.mk.injEq AlgebraicGeometry.Scheme.Modules.ProjPresentation.mk.sizeOf_spec AlgebraicCurve.CurveModel.coe_gInf AlgebraicCurve.CurveModel.coe_tInvChart AlgebraicCurve.CurveModel.ιInf_gluedToBase_assoc AlgebraicCurve.CurveModel.ιInf_gluedToBase AlgebraicCurve.CurveModel.primeOfι₀_asIdeal AlgebraicCurve.CurveModel.coe_tChart AlgebraicCurve.CurveModel.ι₀_gluedToBase_assoc AlgebraicCurve.CurveModel.primeOfιInf_asIdeal"
p2m_attr_erase "simp" "AlgebraicCurve.CurveModel.ι₀_gluedToBase AlgebraicCurve.CurveModel.coe_tma AlgebraicCurve.CurveModel.coe_primeEquivChartPlaces RegularLocalRingQuotientAscent.dualNumberFst_apply AlgebraicGeometry.ProjSpace.twistObj.mk.injEq AlgebraicGeometry.ProjSpace.twistObj.zero_val AlgebraicGeometry.ProjSpace.twistObj.add_val AlgebraicGeometry.ProjSpace.twist_res_val AlgebraicGeometry.ProjSpace.twist_smul_val AlgebraicGeometry.ProjSpace.twistGradeToObj_val AlgebraicGeometry.ProjSpace.twistObj.smul_val AlgebraicGeometry.ProjSpace.twistGradeEquiv_apply_val AlgebraicGeometry.ProjSpace.twistObj.mk.sizeOf_spec"

set_option autoImplicit false

universe u

open scoped TensorProduct Quaternion NumberField
p2m_open "CategoryTheory CategoryTheory.Limits AlgebraicGeometry QuaternionAlgebra CerednikDrinfeld CerednikDrinfeld.QM NeronModelInfra~schemeHomOverComp GoodReductionJacobian"

namespace GLUEaux

variable {R : Type u} [CommRing R]

theorem eq_one_of_mul_self {A : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of R)} (L : RelativeGroupLaw R f)
    {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (y : SchemeHomOver t f) (h : L.mul t y y = y) :
    y = L.one t := by
  have := congrArg (L.mul t (L.inv t y)) h
  rw [← L.mul_assoc, L.inv_mul_cancel, L.one_mul] at this
  exact this

theorem map_one_of_hom {A A' : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of R)} {f' : A' ⟶ Spec (CommRingCat.of R)}
    (L : RelativeGroupLaw R f) (L' : RelativeGroupLaw R f') (φ : A ⟶ A') (hφ : φ ≫ f' = f)
    (hhom : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (P Q : SchemeHomOver t f),
      mapPt φ hφ (L.mul t P Q) = L'.mul t (mapPt φ hφ P) (mapPt φ hφ Q))
    {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) :
    mapPt φ hφ (L.one t) = L'.one t := by
  apply eq_one_of_mul_self
  rw [← hhom, L.one_mul]

theorem map_nsmulPt_of_hom {A A' : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of R)} {f' : A' ⟶ Spec (CommRingCat.of R)}
    (L : RelativeGroupLaw R f) (L' : RelativeGroupLaw R f') (φ : A ⟶ A') (hφ : φ ≫ f' = f)
    (hhom : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (P Q : SchemeHomOver t f),
      mapPt φ hφ (L.mul t P Q) = L'.mul t (mapPt φ hφ P) (mapPt φ hφ Q))
    {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (n : ℕ) (P : SchemeHomOver t f) :
    mapPt φ hφ (nsmulPt L t n P) = nsmulPt L' t n (mapPt φ hφ P) := by
  induction n with
  | zero => exact map_one_of_hom L L' φ hφ hhom t
  | succ n ih => simp only [nsmulPt]; rw [hhom, ih]

theorem mapPt_mapPt {A A' A'' : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of R)} {f' : A' ⟶ Spec (CommRingCat.of R)}
    {f'' : A'' ⟶ Spec (CommRingCat.of R)} (φ : A ⟶ A') (hφ : φ ≫ f' = f) (ψ : A' ⟶ A'') (hψ : ψ ≫ f'' = f')
    {T : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of R)} (P : SchemeHomOver t f) :
    mapPt ψ hψ (mapPt φ hφ P) = mapPt (φ ≫ ψ) (by rw [Category.assoc, hψ, hφ]) P := by
  apply Subtype.ext; simp [mapPt, Category.assoc]

theorem mapPt_congr {A A' : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of R)} {f' : A' ⟶ Spec (CommRingCat.of R)}
    {φ φ' : A ⟶ A'} (h : φ = φ') (hφ : φ ≫ f' = f) (hφ' : φ' ≫ f' = f)
    {T : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of R)} (P : SchemeHomOver t f) :
    mapPt φ hφ P = mapPt φ' hφ' P := by
  subst h; rfl

theorem mapPt_injective_of_isIso {A A' : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of R)} {f' : A' ⟶ Spec (CommRingCat.of R)}
    (φ : A ⟶ A') (hφ : φ ≫ f' = f) [IsIso φ]
    {T : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of R)} {P Q : SchemeHomOver t f} (h : mapPt φ hφ P = mapPt φ hφ Q) :
    P = Q := by
  apply Subtype.ext
  have := congrArg Subtype.val h
  simp only [mapPt] at this
  exact (cancel_mono φ).1 this

end GLUEaux

namespace GLUEact

variable {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} {N : ℕ} {S : Type u} [CommRing S]

theorem natCast_mem (hΛ : IsOrder Λ) (n : ℕ) : ((n : ℚ) : ℍ[ℚ, a, b]) ∈ Λ := by
  have : ((n : ℚ) : ℍ[ℚ, a, b]) = (n : ℤ) • (1 : ℍ[ℚ, a, b]) := by
    rw [zsmul_eq_mul, mul_one]; norm_cast
  rw [this]; exact Λ.smul_mem _ hΛ.one_mem

theorem act_zero_apply (E : FakeEllipticCurve Λ N S) (h0 : (0 : ℍ[ℚ, a, b]) ∈ Λ)
    {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of S)) (P : SchemeHomOver t E.f) :
    pushPt (E.act ⟨0, h0⟩) (E.act_over _) P = E.L.one t := by
  apply GLUEaux.eq_one_of_mul_self
  have := E.act_add ⟨0, h0⟩ ⟨0, h0⟩ t P
  have e : (⟨0, h0⟩ + ⟨0, h0⟩ : ↥Λ) = ⟨0, h0⟩ := by apply Subtype.ext; simp
  rw [e] at this
  exact this.symm

theorem act_natCast_apply (E : FakeEllipticCurve Λ N S) (hΛ : IsOrder Λ) (n : ℕ)
    {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of S)) (P : SchemeHomOver t E.f) :
    pushPt (E.act ⟨((n : ℚ) : ℍ[ℚ, a, b]), natCast_mem hΛ n⟩) (E.act_over _) P = nsmulPt E.L t n P := by
  induction n with
  | zero =>
    have e : (⟨((0 : ℕ) : ℚ), natCast_mem hΛ 0⟩ : ↥Λ) = ⟨0, by simpa using natCast_mem hΛ 0⟩ := by
      apply Subtype.ext; simp
    rw [show pushPt (E.act ⟨(((0 : ℕ) : ℚ) : ℍ[ℚ, a, b]), natCast_mem hΛ 0⟩) (E.act_over _) P =
        pushPt (E.act ⟨0, by simpa using natCast_mem hΛ 0⟩) (E.act_over _) P from by
          simp only [pushPt]; exact GLUEaux.mapPt_congr (by rw [e]) _ _ P]
    exact act_zero_apply E _ t P
  | succ n ih =>
    have e : (⟨(((n + 1 : ℕ) : ℚ) : ℍ[ℚ, a, b]), natCast_mem hΛ (n + 1)⟩ : ↥Λ) =
        ⟨((n : ℚ) : ℍ[ℚ, a, b]), natCast_mem hΛ n⟩ + ⟨1, hΛ.one_mem⟩ := by
      apply Subtype.ext; push_cast; rfl
    rw [show pushPt (E.act ⟨(((n + 1 : ℕ) : ℚ) : ℍ[ℚ, a, b]), natCast_mem hΛ (n + 1)⟩) (E.act_over _) P =
        pushPt (E.act (⟨((n : ℚ) : ℍ[ℚ, a, b]), natCast_mem hΛ n⟩ + ⟨1, hΛ.one_mem⟩)) (E.act_over _) P from by
          simp only [pushPt]; exact GLUEaux.mapPt_congr (by rw [e]) _ _ P]
    rw [E.act_add, ih]
    simp only [nsmulPt]
    congr 1
    simp only [pushPt]
    rw [GLUEaux.mapPt_congr (E.act_one hΛ.one_mem) _ (by simp) P]
    apply Subtype.ext; simp [mapPt]

end GLUEact

namespace GLUEgrp

variable {R : Type u} [CommRing R] {A : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of R)} (L : RelativeGroupLaw R f)
  {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R))

theorem inv_inv (x : SchemeHomOver t f) : L.inv t (L.inv t x) = x := by
  calc L.inv t (L.inv t x) = L.mul t (L.inv t (L.inv t x)) (L.one t) := (L.mul_one t _).symm
    _ = L.mul t (L.inv t (L.inv t x)) (L.mul t (L.inv t x) x) := by rw [L.inv_mul_cancel]
    _ = L.mul t (L.mul t (L.inv t (L.inv t x)) (L.inv t x)) x := by rw [L.mul_assoc]
    _ = x := by rw [L.inv_mul_cancel, L.one_mul]

theorem mul_inv_cancel (x : SchemeHomOver t f) : L.mul t x (L.inv t x) = L.one t := by
  have := L.inv_mul_cancel t (L.inv t x)
  rwa [inv_inv] at this

theorem eq_of_mul_inv_eq_one {x y : SchemeHomOver t f} (h : L.mul t x (L.inv t y) = L.one t) : x = y := by
  have := congrArg (fun z => L.mul t z y) h
  beta_reduce at this
  rw [L.mul_assoc, L.inv_mul_cancel, L.mul_one, L.one_mul] at this
  exact this

theorem nsmulPt_add (n m : ℕ) (P : SchemeHomOver t f) :
    nsmulPt L t (n + m) P = L.mul t (nsmulPt L t n P) (nsmulPt L t m P) := by
  induction m with
  | zero => simp [nsmulPt, L.mul_one]
  | succ m ih => rw [Nat.add_succ]; simp only [nsmulPt]; rw [ih, L.mul_assoc]

theorem nsmulPt_one_pt (n : ℕ) : nsmulPt L t n (L.one t) = L.one t := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [nsmulPt]; rw [ih, L.one_mul]

theorem nsmulPt_mul (n m : ℕ) (P : SchemeHomOver t f) :
    nsmulPt L t (n * m) P = nsmulPt L t n (nsmulPt L t m P) := by
  induction n with
  | zero => simp [nsmulPt]
  | succ n ih => rw [Nat.succ_mul, nsmulPt_add, ih]; simp only [nsmulPt]

theorem nsmulPt_mod_eq_one {n m : ℕ} (P : SchemeHomOver t f)
    (hn : nsmulPt L t n P = L.one t) (hm : nsmulPt L t m P = L.one t) : nsmulPt L t (n % m) P = L.one t := by
  have e : n = n / m * m + n % m := (Nat.div_add_mod' n m).symm
  have := hn
  rw [e, nsmulPt_add, nsmulPt_mul, hm, nsmulPt_one_pt, L.one_mul] at this
  exact this

theorem eq_one_of_nsmulPt_eq_one_of_coprime {r N : ℕ} (hc : Nat.Coprime r N) (P : SchemeHomOver t f)
    (hr : nsmulPt L t r P = L.one t) (hN : nsmulPt L t N P = L.one t) : P = L.one t := by
  have key : ∀ a b : ℕ, nsmulPt L t a P = L.one t → nsmulPt L t b P = L.one t → nsmulPt L t (Nat.gcd a b) P = L.one t := by
    intro a b
    refine Nat.gcd.induction a b (fun n _ hn => by simpa using hn) (fun m n _ ih hm hn => ?_)
    rw [Nat.gcd_rec]
    exact ih (nsmulPt_mod_eq_one L t P hn hm) hm
  have := key r N hr hN
  rw [hc] at this
  simpa [nsmulPt, L.one_mul] using this

end GLUEgrp

namespace GLUEbc

section A

variable {K : Type u} [Field K] [IsAlgClosed K]

theorem discreteTopology_of_isFinite {Z : Scheme.{u}} (g : Z ⟶ Spec (CommRingCat.of K)) [IsFinite g] :
    DiscreteTopology ↥Z := by
  have h0 : DiscreteTopology ↥(Spec (CommRingCat.of K)) := ⟨Subsingleton.elim _ _⟩
  have h1 : _root_.IsDiscrete (Set.univ : Set ↥(Spec (CommRingCat.of K))) := isDiscrete_univ_iff.mpr h0
  have h2 := g.isDiscrete_preimage h1
  rw [Set.preimage_univ] at h2
  exact isDiscrete_univ_iff.mp h2

theorem isClosed_singleton_of_isFinite {Z : Scheme.{u}} (g : Z ⟶ Spec (CommRingCat.of K)) [IsFinite g] (x : ↥Z) :
    IsClosed ({x} : Set ↥Z) := by
  haveI := discreteTopology_of_isFinite g
  exact isClosed_discrete _

theorem eq_specMap_comp_pointOfClosedPoint {Z : Scheme.{u}} (g : Z ⟶ Spec (CommRingCat.of K)) [IsFinite g]
    (k' : Type u) [Field k'] (sk : K →+* k')
    (z : Spec (CommRingCat.of k') ⟶ Z) (hz : z ≫ g = Spec.map (CommRingCat.ofHom sk)) :
    z = Spec.map (CommRingCat.ofHom sk) ≫
      pointOfClosedPoint g (z.base (IsLocalRing.closedPoint k')) (isClosed_singleton_of_isFinite g _) := by
  set x := z.base (IsLocalRing.closedPoint k') with hx
  have hxc : IsClosed ({x} : Set ↥Z) := isClosed_singleton_of_isFinite g _
  haveI : IsAffine Z := isAffine_of_isAffineHom g
  have hrange : Set.range z.base ⊆ {x} := by
    rintro _ ⟨p, rfl⟩
    rw [Set.mem_singleton_iff, Subsingleton.elim p (IsLocalRing.closedPoint k')]
  obtain ⟨t, ht⟩ :=
    AlgebraicGeometry.exists_comp_fromSpecResidueField_eq_of_range_subset_singleton z x hxc hrange
  have hfrom : Z.fromSpecResidueField x =
      Spec.map (residueFieldIsoBase g x hxc).inv ≫ pointOfClosedPoint g x hxc := by
    rw [pointOfClosedPoint, ← Category.assoc, ← Spec.map_comp, Iso.hom_inv_id, Spec.map_id, Category.id_comp]
  have ht' : t ≫ Spec.map (residueFieldIsoBase g x hxc).inv = Spec.map (CommRingCat.ofHom sk) := by
    have := hz
    rw [← ht, hfrom, Category.assoc, Category.assoc, pointOfClosedPoint_comp, Category.comp_id] at this
    exact this
  rw [← ht', Category.assoc, ← hfrom, ht]

theorem ext_of_base_eq {Z : Scheme.{u}} (g : Z ⟶ Spec (CommRingCat.of K)) [IsFinite g]
    (k' : Type u) [Field k'] (sk : K →+* k')
    {z₁ z₂ : Spec (CommRingCat.of k') ⟶ Z} (h₁ : z₁ ≫ g = Spec.map (CommRingCat.ofHom sk))
    (h₂ : z₂ ≫ g = Spec.map (CommRingCat.ofHom sk))
    (h : z₁.base (IsLocalRing.closedPoint k') = z₂.base (IsLocalRing.closedPoint k')) : z₁ = z₂ := by
  rw [eq_specMap_comp_pointOfClosedPoint g k' sk z₁ h₁, eq_specMap_comp_pointOfClosedPoint g k' sk z₂ h₂]
  congr 1
  exact congrArg (fun y => pointOfClosedPoint g y (isClosed_singleton_of_isFinite g y)) h

theorem base_specMap_comp {Z : Scheme.{u}} (k' : Type u) [Field k'] (sk : K →+* k')
    (p : Spec (CommRingCat.of K) ⟶ Z) :
    (Spec.map (CommRingCat.ofHom sk) ≫ p).base (IsLocalRing.closedPoint k') = p.base (IsLocalRing.closedPoint K) := by
  rw [Scheme.Hom.comp_base, TopCat.coe_comp, Function.comp_apply,
    Subsingleton.elim ((Spec.map (CommRingCat.ofHom sk)).base (IsLocalRing.closedPoint k')) (IsLocalRing.closedPoint K)]

theorem bijective_specMap_comp {Z : Scheme.{u}} (g : Z ⟶ Spec (CommRingCat.of K)) [IsFinite g]
    (k' : Type u) [Field k'] (sk : K →+* k') :
    Function.Bijective (fun p : {p : Spec (CommRingCat.of K) ⟶ Z // p ≫ g = 𝟙 _} =>
      (⟨Spec.map (CommRingCat.ofHom sk) ≫ p.1, by rw [Category.assoc, p.2, Category.comp_id]⟩ :
        {z : Spec (CommRingCat.of k') ⟶ Z // z ≫ g = Spec.map (CommRingCat.ofHom sk)})) := by
  constructor
  · rintro ⟨p₁, hp₁⟩ ⟨p₂, hp₂⟩ h
    have h' := congrArg (fun z : {z : Spec (CommRingCat.of k') ⟶ Z // z ≫ g = Spec.map (CommRingCat.ofHom sk)} =>
      z.1.base (IsLocalRing.closedPoint k')) h
    simp only [base_specMap_comp] at h'
    exact Subtype.ext (ext_of_apply_closedPoint_eq g hp₁ hp₂ h')
  · rintro ⟨z, hz⟩
    refine ⟨⟨pointOfClosedPoint g (z.base (IsLocalRing.closedPoint k')) (isClosed_singleton_of_isFinite g _),
      pointOfClosedPoint_comp _ _ _⟩, Subtype.ext ?_⟩
    exact (eq_specMap_comp_pointOfClosedPoint g k' sk z hz).symm

end A

section B

variable {K : Type u} [Field K] {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} {N : ℕ}
  (E E' : FakeEllipticCurve Λ N K) (φ : E.A ⟶ E'.A)

theorem fst_comp_f (hφ : φ ≫ E'.f = E.f) :
    pullback.fst φ (E'.L.one (𝟙 (Spec (CommRingCat.of K)))).1 ≫ E.f =
      pullback.snd φ (E'.L.one (𝟙 (Spec (CommRingCat.of K)))).1 := by
  rw [← hφ, ← Category.assoc, pullback.condition, Category.assoc, (E'.L.one (𝟙 (Spec (CommRingCat.of K)))).2,
    Category.comp_id]

noncomputable def sectionsEquivKerPts (hφ : φ ≫ E'.f = E.f) :
    {x : Spec (CommRingCat.of K) ⟶ pullback φ (E'.L.one (𝟙 (Spec (CommRingCat.of K)))).1 //
        x ≫ (pullback.fst φ (E'.L.one (𝟙 (Spec (CommRingCat.of K)))).1 ≫ E.f) = 𝟙 _} ≃
    {P : SchemeHomOver (𝟙 (Spec (CommRingCat.of K))) E.f // mapPt φ hφ P = E'.L.one (𝟙 (Spec (CommRingCat.of K)))} where
  toFun x := ⟨⟨x.1 ≫ pullback.fst φ (E'.L.one (𝟙 (Spec (CommRingCat.of K)))).1, by rw [Category.assoc]; exact x.2⟩, by
    apply Subtype.ext
    simp only [mapPt_coe, Category.assoc]
    have hs : x.1 ≫ pullback.snd φ (E'.L.one (𝟙 (Spec (CommRingCat.of K)))).1 = 𝟙 _ := by
      rw [← fst_comp_f E E' φ hφ, ← Category.assoc]; exact x.2
    rw [pullback.condition, ← Category.assoc, hs, Category.id_comp]⟩
  invFun P := ⟨pullback.lift P.1.1 (𝟙 _) (by rw [Category.id_comp]; exact congrArg Subtype.val P.2), by
    rw [← Category.assoc, pullback.lift_fst]; exact P.1.2⟩
  left_inv x := by
    apply Subtype.ext
    apply pullback.hom_ext
    · rw [pullback.lift_fst]
    · rw [pullback.lift_snd, ← fst_comp_f E E' φ hφ, ← Category.assoc]; exact x.2.symm
  right_inv P := by
    apply Subtype.ext; apply Subtype.ext
    simp only [pullback.lift_fst]

theorem natCard_sections_eq_natCard_kerPts (hφ : φ ≫ E'.f = E.f) :
    Nat.card {x : Spec (CommRingCat.of K) ⟶ pullback φ (E'.L.one (𝟙 (Spec (CommRingCat.of K)))).1 //
        x ≫ (pullback.fst φ (E'.L.one (𝟙 (Spec (CommRingCat.of K)))).1 ≫ E.f) = 𝟙 _} =
    Nat.card {P : SchemeHomOver (𝟙 (Spec (CommRingCat.of K))) E.f //
        mapPt φ hφ P = E'.L.one (𝟙 (Spec (CommRingCat.of K)))} :=
  Nat.card_congr (sectionsEquivKerPts E E' φ hφ)

noncomputable def ptsOverEquivFactorsThrough (hφ : φ ≫ E'.f = E.f) (k' : Type u) [Field k'] (sk : K →+* k') :
    {z : Spec (CommRingCat.of k') ⟶ pullback φ (E'.L.one (𝟙 (Spec (CommRingCat.of K)))).1 //
        z ≫ (pullback.fst φ (E'.L.one (𝟙 (Spec (CommRingCat.of K)))).1 ≫ E.f) = Spec.map (CommRingCat.ofHom sk)} ≃
    {P : SchemeHomOver (geomPoint k' sk) E.f //
        FactorsThrough (pullback.fst φ (E'.L.one (𝟙 (Spec (CommRingCat.of K)))).1) P} where
  toFun z := ⟨⟨z.1 ≫ pullback.fst φ (E'.L.one (𝟙 (Spec (CommRingCat.of K)))).1, by
      rw [Category.assoc]; exact z.2⟩, ⟨z.1, rfl⟩⟩
  invFun P := ⟨pullback.lift P.1.1 (geomPoint k' sk) (by
      obtain ⟨z, hz⟩ := P.2
      rw [← hz, Category.assoc, pullback.condition, ← Category.assoc, ← fst_comp_f E E' φ hφ, ← Category.assoc z, hz]
      exact congrArg (· ≫ _) P.1.2), by
    rw [← Category.assoc, pullback.lift_fst]; exact P.1.2⟩
  left_inv z := by
    apply Subtype.ext
    apply pullback.hom_ext
    · rw [pullback.lift_fst]
    · rw [pullback.lift_snd, ← fst_comp_f E E' φ hφ, ← Category.assoc]; exact z.2.symm
  right_inv P := by
    apply Subtype.ext; apply Subtype.ext
    simp only [pullback.lift_fst]

end B

section C

variable {R : Type u} [CommRing R]

private theorem _root_.GLUEbc.eq_one_of_mul_self {A : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of R)} (L : RelativeGroupLaw R f)
    {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (y : SchemeHomOver t f) (h : L.mul t y y = y) :
    y = L.one t := by
  have := congrArg (L.mul t (L.inv t y)) h
  rw [← L.mul_assoc, L.inv_mul_cancel, L.one_mul] at this
  exact this

p2m_export "GLUEbc" "eq_one_of_mul_self"

private theorem _root_.GLUEbc.map_one_of_hom {A A' : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of R)} {f' : A' ⟶ Spec (CommRingCat.of R)}
    (L : RelativeGroupLaw R f) (L' : RelativeGroupLaw R f') (φ : A ⟶ A') (hφ : φ ≫ f' = f)
    (hhom : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (P Q : SchemeHomOver t f),
      mapPt φ hφ (L.mul t P Q) = L'.mul t (mapPt φ hφ P) (mapPt φ hφ Q))
    {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) :
    mapPt φ hφ (L.one t) = L'.one t := by
  apply eq_one_of_mul_self
  rw [← hhom, L.one_mul]

p2m_export "GLUEbc" "map_one_of_hom"
variable {K : Type u} [Field K] {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} {N : ℕ}
  (E E' : FakeEllipticCurve Λ N K) (φ : E.A ⟶ E'.A) (hφ : φ ≫ E'.f = E.f)

theorem exists_equiv_kerPts
    (hφmul : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of K)) (P Q : SchemeHomOver t E.f),
      mapPt φ hφ (E.L.mul t P Q) = E'.L.mul t (mapPt φ hφ P) (mapPt φ hφ Q))
    (ℓ : ℕ) [Fact ℓ.Prime]
    (htors : ∀ P : SchemeHomOver (𝟙 (Spec (CommRingCat.of K))) E.f,
      mapPt φ hφ P = E'.L.one (𝟙 (Spec (CommRingCat.of K))) →
        nsmulPt E.L (𝟙 (Spec (CommRingCat.of K))) ℓ P = E.L.one (𝟙 (Spec (CommRingCat.of K))))
    (hK2 : Nat.card {P : SchemeHomOver (𝟙 (Spec (CommRingCat.of K))) E.f //
      mapPt φ hφ P = E'.L.one (𝟙 (Spec (CommRingCat.of K)))} = ℓ ^ 2) :
    ∃ e : ZMod ℓ × ZMod ℓ ≃ {P : SchemeHomOver (𝟙 (Spec (CommRingCat.of K))) E.f //
        mapPt φ hφ P = E'.L.one (𝟙 (Spec (CommRingCat.of K)))},
      ∀ x y, ((e (x + y)).1 : SchemeHomOver (𝟙 (Spec (CommRingCat.of K))) E.f) =
        E.L.mul (𝟙 (Spec (CommRingCat.of K))) (e x).1 (e y).1 := by
  classical
  have hℓ : ℓ.Prime := Fact.out
  letI grp : CommGroup (SchemeHomOver (𝟙 (Spec (CommRingCat.of K))) E.f) :=
    { E.L.pointGroup (𝟙 _) with mul_comm := fun x y => E.comm (𝟙 _) x y }
  have hmul : ∀ x y : SchemeHomOver (𝟙 (Spec (CommRingCat.of K))) E.f,
      x * y = E.L.mul (𝟙 (Spec (CommRingCat.of K))) x y := fun _ _ => rfl
  have hone : (1 : SchemeHomOver (𝟙 (Spec (CommRingCat.of K))) E.f) = E.L.one (𝟙 (Spec (CommRingCat.of K))) := rfl
  have hpow : ∀ (P : SchemeHomOver (𝟙 (Spec (CommRingCat.of K))) E.f) (n : ℕ),
      P ^ n = nsmulPt E.L (𝟙 (Spec (CommRingCat.of K))) n P := by
    intro P n
    induction n with
    | zero => rfl
    | succ n ih => rw [pow_succ, ih]; rfl
  have hφone : mapPt φ hφ (E.L.one (𝟙 (Spec (CommRingCat.of K)))) = E'.L.one (𝟙 (Spec (CommRingCat.of K))) :=
    map_one_of_hom E.L E'.L φ hφ hφmul _
  let H : Subgroup (SchemeHomOver (𝟙 (Spec (CommRingCat.of K))) E.f) :=
    { carrier := {P | mapPt φ hφ P = E'.L.one (𝟙 (Spec (CommRingCat.of K)))}
      mul_mem' := fun {P Q} hP hQ => by
        simp only [Set.mem_setOf_eq] at hP hQ ⊢
        rw [hmul, hφmul, hP, hQ, E'.L.one_mul]
      one_mem' := by
        simp only [Set.mem_setOf_eq]
        rw [hone]; exact hφone
      inv_mem' := fun {P} hP => by
        simp only [Set.mem_setOf_eq] at hP ⊢
        have h1 : mapPt φ hφ P⁻¹ = E'.L.mul (𝟙 _) (mapPt φ hφ P⁻¹) (mapPt φ hφ P) := by
          rw [hP, E'.L.mul_one]
        rw [h1, ← hφmul, ← hmul, inv_mul_cancel, hone, hφone] }
  let eH : ↥H ≃ {P : SchemeHomOver (𝟙 (Spec (CommRingCat.of K))) E.f //
      mapPt φ hφ P = E'.L.one (𝟙 (Spec (CommRingCat.of K)))} :=
    Equiv.subtypeEquivRight (fun _ => Iff.rfl)
  have hcardH : Nat.card ↥H = ℓ ^ 2 := (Nat.card_congr eH).trans hK2
  haveI : Finite ↥H := Nat.finite_of_card_ne_zero (hcardH ▸ pow_ne_zero 2 hℓ.ne_zero)

  have hexp : ∀ x : Additive ↥H, ℓ • x = 0 := by
    intro x
    have h1 : (Additive.toMul x) ^ ℓ = 1 := by
      apply Subtype.ext
      rw [Subgroup.coe_pow, Subgroup.coe_one, hpow, hone]
      exact htors _ (Additive.toMul x).2
    have h2 := congrArg Additive.ofMul h1
    rwa [ofMul_pow, ofMul_toMul, ofMul_one] at h2
  haveI modH : Module (ZMod ℓ) (Additive ↥H) := AddCommGroup.zmodModule hexp
  haveI finH : Module.Finite (ZMod ℓ) (Additive ↥H) := Module.Finite.of_finite
  have hcardM : Nat.card (Additive ↥H) = ℓ ^ Module.finrank (ZMod ℓ) (Additive ↥H) := by
    rw [@Module.natCard_eq_pow_finrank (ZMod ℓ) (Additive ↥H) _ _ modH finH, Nat.card_zmod]
  have hfin2 : Module.finrank (ZMod ℓ) (Additive ↥H) = 2 := by
    have h3 : ℓ ^ Module.finrank (ZMod ℓ) (Additive ↥H) = ℓ ^ 2 := by
      rw [← hcardM]; exact (Nat.card_congr Additive.toMul).trans hcardH
    exact Nat.pow_right_injective hℓ.two_le h3
  have hfr : Module.finrank (ZMod ℓ) (Additive ↥H) = Module.finrank (ZMod ℓ) (ZMod ℓ × ZMod ℓ) := by
    rw [hfin2, Module.finrank_prod, Module.finrank_self]
  let L : Additive ↥H ≃ₗ[ZMod ℓ] (ZMod ℓ × ZMod ℓ) := LinearEquiv.ofFinrankEq (Additive ↥H) (ZMod ℓ × ZMod ℓ) hfr
  let eA : ZMod ℓ × ZMod ℓ ≃+ Additive ↥H := L.symm.toAddEquiv
  refine ⟨eA.toEquiv.trans (Additive.toMul.trans eH), fun x y => ?_⟩
  have hadd : eA.toEquiv (x + y) = eA.toEquiv x + eA.toEquiv y := eA.map_add x y
  simp only [Equiv.trans_apply]
  rw [hadd, toMul_add]
  rfl

end C

section D

variable {K : Type u} [Field K] [IsAlgClosed K] {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} {N : ℕ}

theorem exists_equiv_factorsThrough_kerScheme
    (E E' : FakeEllipticCurve Λ N K) (φ : E.A ⟶ E'.A) (hφ : φ ≫ E'.f = E.f)
    (hφmul : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of K)) (P Q : SchemeHomOver t E.f),
      mapPt φ hφ (E.L.mul t P Q) = E'.L.mul t (mapPt φ hφ P) (mapPt φ hφ Q))
    (ℓ : ℕ) [Fact ℓ.Prime]
    (htors : ∀ P : SchemeHomOver (𝟙 (Spec (CommRingCat.of K))) E.f,
      mapPt φ hφ P = E'.L.one (𝟙 (Spec (CommRingCat.of K))) →
        nsmulPt E.L (𝟙 (Spec (CommRingCat.of K))) ℓ P = E.L.one (𝟙 (Spec (CommRingCat.of K))))
    [IsFinite (pullback.fst φ (E'.L.one (𝟙 (Spec (CommRingCat.of K)))).1 ≫ E.f)]
    (hK2 : Nat.card {P : SchemeHomOver (𝟙 (Spec (CommRingCat.of K))) E.f //
      mapPt φ hφ P = E'.L.one (𝟙 (Spec (CommRingCat.of K)))} = ℓ ^ 2)
    (k' : Type u) [Field k'] (sk : K →+* k') :
    ∃ e : ZMod ℓ × ZMod ℓ ≃ {P : SchemeHomOver (geomPoint k' sk) E.f //
        FactorsThrough (pullback.fst φ (E'.L.one (𝟙 (Spec (CommRingCat.of K)))).1) P},
      ∀ x y, ((e (x + y)).1 : SchemeHomOver (geomPoint k' sk) E.f) =
        E.L.mul (geomPoint k' sk) (e x).1 (e y).1 := by
  classical
  obtain ⟨e0, he0⟩ := exists_equiv_kerPts E E' φ hφ hφmul ℓ htors hK2
  have hψt : geomPoint k' sk ≫ 𝟙 (Spec (CommRingCat.of K)) = geomPoint k' sk := Category.comp_id _

  let β : SchemeHomOver (𝟙 (Spec (CommRingCat.of K))) E.f → SchemeHomOver (geomPoint k' sk) E.f :=
    fun P => GoodReductionJacobian.schemeHomOverComp (geomPoint k' sk) hψt P
  let sec := sectionsEquivKerPts E E' φ hφ
  let pof := ptsOverEquivFactorsThrough E E' φ hφ k' sk

  let bc : {p : Spec (CommRingCat.of K) ⟶ pullback φ (E'.L.one (𝟙 (Spec (CommRingCat.of K)))).1 //
        p ≫ (pullback.fst φ (E'.L.one (𝟙 (Spec (CommRingCat.of K)))).1 ≫ E.f) = 𝟙 _} →
      {z : Spec (CommRingCat.of k') ⟶ pullback φ (E'.L.one (𝟙 (Spec (CommRingCat.of K)))).1 //
        z ≫ (pullback.fst φ (E'.L.one (𝟙 (Spec (CommRingCat.of K)))).1 ≫ E.f) = Spec.map (CommRingCat.ofHom sk)} :=
    fun p => ⟨Spec.map (CommRingCat.ofHom sk) ≫ p.1, by rw [Category.assoc, p.2, Category.comp_id]⟩
  have hbc : Function.Bijective bc :=
    bijective_specMap_comp (pullback.fst φ (E'.L.one (𝟙 (Spec (CommRingCat.of K)))).1 ≫ E.f) k' sk
  let f : ZMod ℓ × ZMod ℓ → {P : SchemeHomOver (geomPoint k' sk) E.f //
      FactorsThrough (pullback.fst φ (E'.L.one (𝟙 (Spec (CommRingCat.of K)))).1) P} :=
    fun z => pof (bc (sec.symm (e0 z)))
  have hfβ : ∀ z, ((f z).1 : SchemeHomOver (geomPoint k' sk) E.f) = β (e0 z).1 := by
    intro z
    have hx : (sec.symm (e0 z)).1 ≫ pullback.fst φ (E'.L.one (𝟙 (Spec (CommRingCat.of K)))).1 = (e0 z).1.1 :=
      congrArg (fun P => P.1.1) (sec.apply_symm_apply (e0 z))
    apply Subtype.ext
    show (Spec.map (CommRingCat.ofHom sk) ≫ (sec.symm (e0 z)).1) ≫
        pullback.fst φ (E'.L.one (𝟙 (Spec (CommRingCat.of K)))).1 = geomPoint k' sk ≫ (e0 z).1.1
    rw [Category.assoc, hx]
    rfl
  have hbij : Function.Bijective f :=
    pof.bijective.comp (hbc.comp (sec.symm.bijective.comp e0.bijective))
  refine ⟨Equiv.ofBijective f hbij, fun x y => ?_⟩
  simp only [Equiv.ofBijective_apply]
  rw [hfβ, hfβ, hfβ, he0]
  exact E.L.mul_natural _ _ _ hψt _ _

end D

end GLUEbc

theorem solution
    {q q' : ℕ} [Fact q.Prime] [Fact q'.Prime] (hqq' : q' ≠ q)
    {a b : ℚ} (hB : IsIndefiniteRamifiedExactlyAt a b q q')
    (Λ : Submodule ℤ ℍ[ℚ, a, b]) (hΛ : IsMaximalOrder Λ) {N : ℕ} [NeZero N]
    (ℓ : ℕ) [Fact ℓ.Prime] (hℓq : ℓ ≠ q) (hℓq' : ℓ ≠ q')
    (k : Type) [Field k] [IsAlgClosed k] (hℓk : (ℓ : k) ≠ 0) (hNk : (N : k) ≠ 0)
    (hℓN : ¬ ℓ ∣ N)
    (u : FakeEllipticCurve.WithExtraLevel Λ N ℓ k) (E' : FakeEllipticCurve Λ N k)
    (φ : u.1.A ⟶ E'.A) (hφ : φ ≫ E'.f = u.1.f) (ψ : E'.A ⟶ u.1.A) (hψ : ψ ≫ u.1.f = E'.f)
    (φ_hom : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of k)) (P Q : SchemeHomOver t u.1.f),
      mapPt φ hφ (u.1.L.mul t P Q) = E'.L.mul t (mapPt φ hφ P) (mapPt φ hφ Q))
    (ψ_hom : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of k)) (P Q : SchemeHomOver t E'.f),
      mapPt ψ hψ (E'.L.mul t P Q) = u.1.L.mul t (mapPt ψ hψ P) (mapPt ψ hψ Q))
    (φ_act : ∀ x : ↥Λ, u.1.act x ≫ φ = φ ≫ E'.act x) (ψ_act : ∀ x : ↥Λ, E'.act x ≫ ψ = ψ ≫ u.1.act x)
    (hψφ : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of k)) (P : SchemeHomOver t u.1.f),
      mapPt ψ hψ (mapPt φ hφ P) = nsmulPt u.1.L t ℓ P)
    (hφψ : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of k)) (Q : SchemeHomOver t E'.f),
      mapPt φ hφ (mapPt ψ hψ Q) = nsmulPt E'.L t ℓ Q)
    (hkerφ : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of k)) (P : SchemeHomOver t u.1.f),
      mapPt φ hφ P = E'.L.one t ↔ FactorsThrough u.2.levK P)
    (φ_lev : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of k)) (P : SchemeHomOver t u.1.f),
      FactorsThrough u.1.lev P → FactorsThrough E'.lev (mapPt φ hφ P)) :
    ∀ (k' : Type) [Field k'] [IsAlgClosed k'] (sk : k →+* k'), (ℓ : k') ≠ 0 →
      ∃ e : ZMod ℓ × ZMod ℓ ≃ {P : SchemeHomOver (geomPoint k' sk) E'.f //
          FactorsThrough (CategoryTheory.Limits.pullback.fst ψ (u.1.L.one (𝟙 (Spec (CommRingCat.of k)))).1) P},
        ∀ x y : ZMod ℓ × ZMod ℓ, (e (x + y) : SchemeHomOver (geomPoint k' sk) E'.f) =
          E'.L.mul (geomPoint k' sk) (e x) (e y) := by
  intro k' _ _ sk hℓk'
  classical

  obtain ⟨-, -, hfin⟩ := CerednikDrinfeld.QM.FakeEllipticCurve.isReduced_pullback_one_of_natCast_ne_zero
    k E' u.1 ψ hψ ψ_hom ψ_act φ hφ ℓ hℓk hφψ hψφ
  haveI := hfin
  have htors : ∀ P : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) E'.f,
      mapPt ψ hψ P = u.1.L.one _ → nsmulPt E'.L _ ℓ P = E'.L.one _ := fun P hP => by
    rw [← hφψ _ P, hP]; exact GLUEaux.map_one_of_hom u.1.L E'.L φ hφ φ_hom _

  have hK2 : Nat.card {P : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) E'.f //
      mapPt ψ hψ P = u.1.L.one _} = ℓ ^ 2 := by

    letI GU : CommGroup (SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) u.1.f) :=
      { u.1.L.pointGroup (𝟙 _) with mul_comm := u.1.comm (𝟙 _) }
    letI GE : CommGroup (SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) E'.f) :=
      { E'.L.pointGroup (𝟙 _) with mul_comm := E'.comm (𝟙 _) }
    have pow_eq : ∀ (n : ℕ) (P : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) u.1.f), P ^ n = nsmulPt u.1.L _ n P := by
      intro n P; induction n with
      | zero => rfl
      | succ n ih => rw [pow_succ, ih]; rfl
    have pow_eq' : ∀ (n : ℕ) (P : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) E'.f), P ^ n = nsmulPt E'.L _ n P := by
      intro n P; induction n with
      | zero => rfl
      | succ n ih => rw [pow_succ, ih]; rfl

    let fφ : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) u.1.f →* SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) E'.f :=
      { toFun := fun P => mapPt φ hφ P
        map_one' := GLUEaux.map_one_of_hom u.1.L E'.L φ hφ φ_hom _
        map_mul' := fun P Q => φ_hom _ P Q }
    have nsmulPt_eq_nsmul : ∀ {A : Scheme.{0}} {f : A ⟶ Spec (CommRingCat.of k)} (L : RelativeGroupLaw k f)
        (n : ℕ) (P : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) f), nsmulPt L _ n P = L.nsmul _ n P := by
      intro A f L n P
      induction n with
      | zero => rfl
      | succ n ih => rw [GoodReductionJacobian.RelativeGroupLaw.nsmul_succ, ← ih]; rfl

    let Tℓ : Subgroup (SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) u.1.f) :=
      { carrier := {P | nsmulPt u.1.L _ ℓ P = u.1.L.one _}
        one_mem' := GLUEgrp.nsmulPt_one_pt u.1.L _ ℓ
        mul_mem' := by
          intro P Q hP hQ
          show nsmulPt u.1.L _ ℓ (P * Q) = _
          have hP' : nsmulPt u.1.L _ ℓ P = u.1.L.one _ := hP
          have hQ' : nsmulPt u.1.L _ ℓ Q = u.1.L.one _ := hQ
          rw [← pow_eq, mul_pow, pow_eq, pow_eq, hP', hQ']
          exact u.1.L.one_mul _ _
        inv_mem' := by
          intro P hP
          show nsmulPt u.1.L _ ℓ P⁻¹ = _
          have hP' : nsmulPt u.1.L _ ℓ P = u.1.L.one _ := hP
          rw [← pow_eq, inv_pow, pow_eq, hP']
          exact inv_one }
    have hTmem : ∀ P, P ∈ Tℓ ↔ nsmulPt u.1.L _ ℓ P = u.1.L.one _ := fun P => Iff.rfl

    have hTcard : Nat.card Tℓ = ℓ ^ 4 := by
      haveI : SmoothOfRelativeDimension 2 u.1.f := CerednikDrinfeld.QM.FakeEllipticCurve.smoothOfRelativeDimension_two k u.1
      have h := GoodReductionJacobian.RelativeGroupLaw.natCard_isTorsionPoint_eq_pow_of_natCast_ne_zero k u.1.f u.1.L u.1.comm
        u.1.bundle 2 ℓ hℓk
      rw [show (2 * 2 : ℕ) = 4 from rfl] at h
      rw [← h]
      apply Nat.card_congr
      refine Equiv.subtypeEquivRight ?_
      intro P
      show nsmulPt u.1.L _ ℓ P = u.1.L.one _ ↔ _
      rw [GoodReductionJacobian.RelativeGroupLaw.isTorsionPoint_def, nsmulPt_eq_nsmul]

    haveI : Smooth E'.f := E'.bundle.smooth
    haveI : ConnectedSpace E'.A := by
      rw [connectedSpace_iff_univ]
      obtain ⟨s₀⟩ := (inferInstance : Nonempty ↥(Spec (CommRingCat.of k)))
      have := E'.bundle.connectedFibres s₀
      have huniv : E'.f.base ⁻¹' {s₀} = Set.univ := by
        ext x; simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_univ, iff_true]
        exact Subsingleton.elim _ _
      rwa [huniv] at this
    have hsurj := GoodReductionJacobian.RelativeGroupLaw.nsmul_surjective_of_isAlgClosed_of_connectedSpace
      E'.L (fun t x y => E'.comm t x y) ℓ (isUnit_iff_ne_zero.2 hℓk)

    let f' := fφ.comp Tℓ.subtype
    have hrange : Set.range f' = {Q | mapPt ψ hψ Q = u.1.L.one _} := by
      ext Q; constructor
      · rintro ⟨⟨P, hP⟩, rfl⟩
        show mapPt ψ hψ (mapPt φ hφ P) = _
        rw [hψφ]; exact hP
      · intro hQ
        obtain ⟨Q₁, hQ₁⟩ := hsurj Q
        rw [← nsmulPt_eq_nsmul] at hQ₁
        have hmem : mapPt ψ hψ Q₁ ∈ Tℓ := by
          rw [hTmem, ← hψφ, hφψ, hQ₁]; exact hQ
        exact ⟨⟨mapPt ψ hψ Q₁, hmem⟩, by show mapPt φ hφ (mapPt ψ hψ Q₁) = Q; rw [hφψ, hQ₁]⟩
    have hgp : geomPoint (S := k) k (RingHom.id k) = 𝟙 (Spec (CommRingCat.of k)) := by simp [geomPoint]
    have hker : Nat.card f'.ker = ℓ ^ 2 := by
      obtain ⟨eK, -⟩ := u.2.levK_fibre k (RingHom.id k) hℓk
      rw [hgp] at eK
      have e2 : f'.ker ≃ {P : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) u.1.f // FactorsThrough u.2.levK P} :=
        { toFun := fun P => ⟨P.1.1, (hkerφ _ P.1.1).1 (by have := P.2; rwa [MonoidHom.mem_ker] at this)⟩
          invFun := fun P => ⟨⟨P.1, (hTmem _).2 (u.2.levK_torsion _ P.1 P.2)⟩, by
            rw [MonoidHom.mem_ker]; exact (hkerφ _ P.1).2 P.2⟩
          left_inv := fun P => by apply Subtype.ext; apply Subtype.ext; rfl
          right_inv := fun P => by apply Subtype.ext; rfl }
      rw [Nat.card_congr e2, ← Nat.card_congr eK, Nat.card_prod, Nat.card_zmod, pow_two]

    have hci := Subgroup.card_mul_index f'.ker
    rw [Subgroup.index_ker, hker, hTcard] at hci
    have hr : Nat.card ↥f'.range = Nat.card {Q : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) E'.f // mapPt ψ hψ Q = u.1.L.one _} := by
      apply Nat.card_congr
      refine Equiv.subtypeEquivRight ?_
      intro Q
      rw [MonoidHom.mem_range]
      have := Set.ext_iff.1 hrange Q
      simp only [Set.mem_range, Set.mem_setOf_eq] at this
      exact this
    rw [hr] at hci
    have : ℓ ^ 2 * Nat.card {Q : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) E'.f // mapPt ψ hψ Q = u.1.L.one _} = ℓ ^ 2 * ℓ ^ 2 := by
      rw [hci]; ring
    exact Nat.eq_of_mul_eq_mul_left (pow_pos (Fact.out : ℓ.Prime).pos 2) this
  exact GLUEbc.exists_equiv_factorsThrough_kerScheme E' u.1 ψ hψ ψ_hom ℓ htors hK2 k' sk

end S_CerednikDrinfeld_QM_FakeEllipticCurve_exists_zmod_prod_equiv_factorsThrough_kernel_dual_of_not_dvd
end P2MW
export P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_exists_zmod_prod_equiv_factorsThrough_kernel_dual_of_not_dvd (solution)
