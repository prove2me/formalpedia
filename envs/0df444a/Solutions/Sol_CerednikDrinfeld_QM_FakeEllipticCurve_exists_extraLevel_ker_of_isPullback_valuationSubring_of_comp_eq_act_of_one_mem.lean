-- Prove2me | solution 1 for CerednikDrinfeld.QM.FakeEllipticCurve.exists_extraLevel_ker_of_isPullback_valuationSubring_of_comp_eq_act_of_one_mem
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.837917+00:00
-- url     : https://prove2.me/submissions/c89a32b9-4621-5296-a1a6-cd145c460956

import Definitions.Def_CerednikDrinfeld_FakeEllipticFrobenius
import Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_isFinite_flat_surjective_of_mapPt_mapPt_eq_nsmulPt_valuationSubring
import Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_pushPt_act_natCast_eq_nsmulPt
import Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_exists_kernel_of_isFinite_of_flat
import Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_exists_zmod_prod_equiv_factorsThrough_of_isPullback_valuationSubring
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_exists_extraLevel_ker_of_isPullback_valuationSubring_of_comp_eq_act_of_one_mem
p2m_attr_erase "instance" "instTopologicallyFGOfFiniteType GoodReductionJacobian.RelativeGroupLaw.isIso_endKerStr_schemeHomOverId AlgebraicGeometry.Scheme.PresheafOfModules.symmetricCategory SheafOfModules.instFaithfulRingSheafPModToPMod SheafOfModules.symmetricCategory AlgebraicGeometry.Scheme.PresheafOfModules.monoidalCategory AlgebraicGeometry.Scheme.PresheafOfModules.monoidalClosed SheafOfModules.instFullRingSheafPModToPMod SheafOfModules.monoidalCategory AlgebraicGeometry.Scheme.Modules.symmetricCategory SheafOfModules.monoidalClosed SheafOfModules.instIsLocalizationPModRingSheafSheafifyFunctorPresheafW SheafOfModules.sheafifyFunctor_monoidal AlgebraicGeometry.Scheme.Modules.monoidalClosed AlgebraicGeometry.instMonoidalPresheafOfModulesModulesSheafify AlgebraicGeometry.Scheme.Modules.monoidalCategory PresheafOfModules.instMonoidalClosed PresheafOfModules.InternalHom.instModuleCarrierObjOppositeCommRingCatSubtypePiFamilyMemAddSubgroupNaturalFamilies PresheafOfModules.InternalHom.instModuleCarrierObjOppositeRingCatCompCommRingCatForget₂RingHomCarrierCarrierAbPresheaf PresheafOfModules.InternalHom.instSMulCarrierObjOppositeCommRingCatSubtypePiFamilyMemAddSubgroupNaturalFamilies AlgebraicGeometry.Scheme.Hom.opensMapFinal AlgebraicGeometry.RelPicard.RigidifiedLineBundle.setoid AlgebraicGeometry.RelPicard.RigidifiedLineBundle.instInhabited AlgebraicGeometry.OModulePresheaf.isScalarTower AlgebraicGeometry.Scheme.OrderedAffineCover.instLinearOrder AlgebraicGeometry.OModulePresheaf.module AlgebraicGeometry.Scheme.OrderedAffineCover.instFintype AlgebraicGeometry.Scheme.OrderedAffineCover.instFintypeIdx AlgebraicGeometry.OModulePresheaf.addCommGroup AlgebraicGeometry.Scheme.OrderedAffineCover.instDecidableEqIdx AlgebraicGeometry.OModulePresheaf.moduleSections TwoChartCech.Sections.M0_moduleA TwoChartCech.Sections.M1_module TwoChartCech.Cover.A01_algebra TwoChartCech.Cover.A0_algebra TwoChartCech.Cover.A1_commRing TwoChartCech.Cover.A1_algebra TwoChartCech.Sections.M01_module TwoChartCech.Sections.M0_addCommGroup TwoChartCech.Sections.M0_tower"
p2m_attr_erase "instance" "TwoChartCech.Sections.M01_addCommGroup TwoChartCech.Cover.A0_commRing TwoChartCech.Sections.M1_tower TwoChartCech.Sections.M01_moduleA TwoChartCech.Sections.M0_module TwoChartCech.Sections.M1_moduleA TwoChartCech.Sections.M1_addCommGroup TwoChartCech.Cover.A01_commRing TwoChartCech.Sections.M01_tower CoherentBaseChange.TwoTermComplex.C0_module CoherentBaseChange.TwoTermComplex.C0_addCommGroup CoherentBaseChange.TwoTermComplex.C1_module CoherentBaseChange.TwoTermComplex.C1_addCommGroup CoherentBaseChange.TwoTermComplex.C0_free CoherentBaseChange.TwoTermComplex.C1_finite CoherentBaseChange.TwoTermComplex.C0_finite CoherentBaseChange.TwoTermComplex.C1_free AlgebraicGeometry.OModulePresheaf.instSubsingletonObjZero AlgebraicGeometry.Scheme.Modules.preservesBinaryProducts_opensMap AlgebraicGeometry.Scheme.Modules.pullback_monoidal AlgebraicGeometry.Scheme.Modules.sheafify_isLocalization' AlgebraicGeometry.Scheme.Modules.preservesTerminal_opensMap AlgebraicGeometry.Scheme.Modules.pullback₀_monoidal AlgebraicGeometry.Scheme.Modules.preservesFiniteProducts_opensMap AlgebraicGeometry.Scheme.Modules.instLiftingPresheafOfModulesSheafifyPresheafWOpensCarrierCarrierCommRingCatGrothendieckTopologyObjFunctorOppositeIsSheafSheafCompPullback₀Pullback PresheafOfModules.PullbackMonoidal.pullback_monoidal PresheafOfModules.PullbackMonoidal.isIso_δ PresheafOfModules.pushforward_laxMonoidal PresheafOfModules.PullbackMonoidal.isIso_η PresheafOfModules.free_monoidal PresheafOfModules.restrictScalars_laxMonoidal PresheafOfModules.PullbackMonoidal.isIso_δ_gS PresheafOfModules.pullback_oplaxMonoidal PresheafOfModules.PullbackMonoidal.instPreservesColimitsOfSizeCompOppositeCommRingCatRingCatForget₂RingHomCarrierCarrierPb PresheafOfModules.pullback_monoidal' AlgebraicGeometry.SmoothOfRelativeDimension.fiberToSpecResidueField AlgebraicGeometry.SmoothOfRelativeDimension.pullback_snd AlgebraicGeometry.SmoothOfRelativeDimension.pullback_fst AlgebraicGeometry.SmoothOfRelativeDimension.smooth_one AlgebraicGeometry.SmoothProperCurve.isIntegral_pullback_Spec_field"
p2m_attr_erase "instance" "AlgebraicGeometry.IsProper.fiberToSpecResidueField AlgebraicCurve.CurveModel.isProper AlgebraicCurve.CurveModel.isIntegral AlgebraicCurve.CurveModel.smooth AlgebraicGeometry.Scheme.LocalRepresentabilityULift.instIsLocallyInjectiveFunUliftYonedaGluedToSheaf AlgebraicGeometry.Scheme.LocalRepresentabilityULift.instIsLocallySurjectiveFunUliftYonedaGluedToSheafOfIsLocallySurjectiveZariskiTopologyDescFunctorOppositeType AlgebraicGeometry.Scheme.LocalRepresentabilityULift.instIsOpenImmersionToGlued AlgebraicGeometry.Scheme.LocalRepresentabilityULift.instIsIsoSheafZariskiTopologyTypeUliftYonedaGluedToSheaf AlgebraicGeometry.RelPicard.instIsOpenImmersionToGlued AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.instFundamentalIdentityOfSumRamificationInertia AlgebraicCurve.Place.instIsScalarTowerResidueFieldRestrictPushforward AlgebraicCurve.Place.instAlgebraResidueFieldRestrictPushforward AlgebraicCurve.Place.instIsLocalHomRestrictInclusion AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions PresheafOfModules.ExteriorPower.instModulePresheafAb AlgebraicGeometry.RelEffCartierDiv.subsingleton_of_degree_zero AlgebraicGeometry.RelEffCartierDiv.isIso_subschemeIota_snd_of_degree_one AlgebraicGeometry.isIso_ker_graphOver_subschemeIota_snd AlgebraicGeometry.isClosedImmersion_graphOver AlgebraicGeometry.FGSubalgebra.instIsDirectedLe AlgebraicGeometry.FGSubalgebra.instQuasiSeparatedSpaceCarrierCarrierCommRingCatObjOppositeSchemeSpecDiagram AlgebraicGeometry.FGSubalgebra.instIsCofilteredOpposite AlgebraicGeometry.FGSubalgebra.instIsAffineObjOppositeSchemeSpecDiagram AlgebraicGeometry.FGSubalgebra.instNonempty AlgebraicGeometry.FGSubalgebra.instNonemptySubtypeLeSubalgebraValFG AlgebraicGeometry.FGSubalgebra.instCompactSpaceCarrierCarrierCommRingCatObjOppositeSchemeSpecDiagram AlgebraicGeometry.FGSubalgebra.instIsDirectedSubtypeLeSubalgebraValFG AlgebraicGeometry.FGSubalgebra.instIsAffineHomMapOppositeSchemeSpecDiagram AlgebraicGeometry.FGSubalgebra.instIsFiltered AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instNeg AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instSMulInt AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instAddCommGroup AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instAdd"
p2m_attr_erase "instance" "AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instSub AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instModuleCarrierObjOppositeOpensCarrierCarrierCommRingCatPresheafOpOpensTop AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instSMulCarrierObjOppositeOpensCarrierCarrierCommRingCatPresheafOpOpensTop AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instSMulNat AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instZero AlgebraicCurve.instHasLocalResidue_of_hasCanonicalLocalResidueK AlgebraicCurve.instHasCanonicalLocalResidueK_of_hasCanonicalLocalResidueKStar AlgebraicCurve.Place.kw_ffgc_finiteDimensional_adicCompletion instAlgebraSubtypeMemValuationSubring_definitions AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersIntegersCompletion ModularCurve.KwF4gRRTate.instAlgebraKAdicCompletionIntegers AlgebraicCurve.Place.kw_ffgc_continuousSMul_adicCompletionComap AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersCompletionCompletion IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions AlgebraicCurve.instHasCanonicalLocalResidueK AlgebraicCurve.Place.instAlgebra_restrictResidueField AlgebraicCurve.Place.instIsScalarTower_restrictResidueField AlgebraicCurve.instHasLocalResidue AlgebraicCurve.HasSeparableResidue.of_perfectField_of_isCurveOver AlgebraicCurve.HasSeparableResidue.of_perfectField AlgebraicCurve.Place.instIsLocalHom_restrictSubringHom AlgebraicCurve.instHasCanonicalLocalResidueKStar ModularCurve.KwNo6Pin.isLocalRing_completion SheafOfModules.isIso_ihomModelToIhom AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instDecidableEqIdx AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instFintype AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instLinearOrder AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instFintypeIdx AlgebraicGeometry.OModulePresheaf.Leray.relAltC_scalarTower AlgebraicGeometry.OModulePresheaf.Leray.ker_relAltd_modΓ AlgebraicGeometry.OModulePresheaf.Leray.relAltC_modΓ AlgebraicGeometry.OModulePresheaf.Leray.biC_abGrp AlgebraicGeometry.OModulePresheaf.Leray.relAltH_modΓ AlgebraicGeometry.OModulePresheaf.Leray.ker_relAltd_smul AlgebraicGeometry.OModulePresheaf.Leray.relAltH_scalarTower"
p2m_attr_erase "instance" "AlgebraicGeometry.OModulePresheaf.Leray.relAltH_smul AlgebraicGeometry.OModulePresheaf.Leray.biC_module DoubleComplex.instModuleE₂I DoubleComplex.Bounded.modR DoubleComplex.instModuleE₂II DoubleComplex.instAddCommGroupE₂II DoubleComplex.Bounded.abGrp DoubleComplex.instAddCommGroupE₂I AlgebraicGeometry.ChowDatum.hι_closed AlgebraicGeometry.ChowDatumProj.hιN_closed AlgebraicGeometry.ChowDatumProj.hp_proper AlgebraicGeometry.ChowDatum.hp_isoU AlgebraicGeometry.ChowDatum.hp_proper AlgebraicGeometry.ProjSpace.algebraAway AlgebraicGeometry.ProjSpace.instIsProperProdOverπ AlgebraicGeometry.ChowDatumProj.hp_isoU AlgebraicGeometry.ProjSpace.isProper_π AlgebraicGeometry.ProjSpace.finiteType_mvPolynomial ProjSpaceCech.GradedModule.H.module ProjSpaceCech.GradedModule.H.addCommGroup ProjSpaceCech.GradedModule.sec.instAdd ProjSpaceCech.GradedModule.sec.instNeg ProjSpaceCech.GradedModule.acg ProjSpaceCech.GradedModule.Frac.setoid ProjSpaceCech.GradedModule.modR ProjSpaceCech.GradedModule.sec.instModule ProjSpaceCech.GradedModule.sec.instAddCommGroup ProjSpaceCech.GradedModule.sec.instZero ProjSpaceCech.GradedModule.Presentation.fJ ProjSpaceCech.GradedModule.sec.instSMul ProjSpaceCech.Twist.H.module ProjSpaceCech.Idx.instFintype ProjSpaceCech.Twist.H.addCommGroup ProjSpaceCech.Idx.instDecidableEq ProjSpaceCech.Twist.Mon.instDecidableEq ProjSpaceCech.Twist.cochain.instAddCommGroup ProjSpaceCech.Twist.cochain.instModule AlgebraicGeometry.FGSubalgebra.tensorStage_directedSystem AlgebraicGeometry.RelEffCartierDiv.isClosedImmersion_subschemeι_resProdMap AlgebraicGeometry.RelEffCartierDiv.isOpenImmersion_resProdMap"
p2m_attr_erase "instance" "AlgebraicCurve.CurveModel.locallyOfFiniteType_gluedToBase AlgebraicCurve.CurveModel.isFractionRing_overlap AlgebraicCurve.CurveModel.isLocallyNoetherian_glued AlgebraicCurve.CurveModel.jacobsonSpace_glued AlgebraicCurve.CurveModel.isOpenImmersion_ι₀ AlgebraicCurve.CurveModel.isIntegral_glued AlgebraicCurve.CurveModel.quasiSeparated_gluedToBase AlgebraicCurve.CurveModel.compactSpace_glued AlgebraicCurve.CurveModel.isIntegral_adjoin_chartRing AlgebraicCurve.CurveModel.isFractionRing_overlap_functionField AlgebraicCurve.CurveModel.isProper_gluedToBase AlgebraicCurve.CurveModel.isOpenImmersion_ιU AlgebraicCurve.CurveModel.isOpenImmersion_f₀ AlgebraicCurve.CurveModel.isOpenImmersion_fInf AlgebraicCurve.CurveModel.isOpenImmersion_ιInf AlgebraicCurve.CurveModel.algebra_overlap_functionField AlgebraicCurve.CurveModel.quasiCompact_gluedToBase AlgebraicCurve.CurveModel.algebraAdjoin AlgebraicCurve.CurveModel.isDedekindDomain_chartRing AlgebraicCurve.CurveModel.isIntegralClosure AlgebraicCurve.CurveModel.finite_chartRing AlgebraicCurve.CurveModel.centre_isPrime AlgebraicCurve.CurveModel.isFractionRing_chartRing AlgebraicCurve.CurveModel.finiteType_chartRing AlgebraicCurve.CurveModel.isNoetherianRing_chartRing AlgebraicCurve.CurveModel.isScalarTower_base_adjoin AlgebraicCurve.CurveModel.isScalarTower_adjoin AlgebraicCurve.CurveModel.chartRing_finitePresentation AlgebraicGeometry.ProjSpace.twistObj.addCommGroup AlgebraicGeometry.ProjSpace.twistFam.module AlgebraicGeometry.ProjSpace.twistObj.module AlgebraicGeometry.ProjSpace.twistObj.moduleSections AlgebraicGeometry.ProjSpace.twistFam.addCommGroup"
p2m_attr_erase "simp" "RegularLocalRingQuotientAscent.dualNumberFst_apply GoodReductionJacobian.RelativeGroupLaw.fibre_inv GoodReductionJacobian.RelativeGroupLaw.fibrePointToBase_coe GoodReductionJacobian.RelativeGroupLaw.fibrePointOfBase_toBase GoodReductionJacobian.RelativeGroupLaw.fibre_mul GoodReductionJacobian.RelativeGroupLaw.fibrePointToBase_ofBase GoodReductionJacobian.RelativeGroupLaw.fibre_one GoodReductionJacobian.RelativeGroupLaw.fibrePointOfBase_coe GoodReductionJacobian.RelativeGroupLaw.nsmul_zero GoodReductionJacobian.RelativeGroupLaw.mem_torsionSubset GoodReductionJacobian.RelativeGroupLaw.nsmul_succ GoodReductionJacobian.RelativeGroupLaw.baseChangePointToBase_ofBase GoodReductionJacobian.RelativeGroupLaw.baseChangePointToBase_coe GoodReductionJacobian.RelativeGroupLaw.baseChangePointOfBase_coe GoodReductionJacobian.RelativeGroupLaw.baseChange_inv GoodReductionJacobian.RelativeGroupLaw.baseChangePointOfBase_toBase GoodReductionJacobian.RelativeGroupLaw.baseChange_mul GoodReductionJacobian.RelativeGroupLaw.baseChange_one NeronModelInfra.NeronModelPropertyBundle.endExtensionEquiv_symm_restrict NeronModelInfra.schemeHomOverComp_id_left NeronModelInfra.schemeHomOverComp_id_right NeronModelInfra.schemeHomOverId_coe NeronModelInfra.NeronModelPropertyBundle.endExtensionEquiv_apply NeronModelInfra.NeronModelPropertyBundle.restrict_endExtensionEquiv_symm NeronModelInfra.schemeHomOverComp_coe NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_fst NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_snd NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_fst NeronSpecialFibreInfra.neronEndRestrictEquiv_apply NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_fst_assoc NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_snd NeronSpecialFibreInfra.neronEndExtension_genericFibreRestrict NeronSpecialFibreInfra.specClosedFibreInclusion_eq NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_fst_assoc NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_snd_assoc NeronSpecialFibreInfra.genericFibreRestrict_neronEndExtension NeronSpecialFibreInfra.homOverId_coe NeronSpecialFibreInfra.homOverComp_coe NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_snd_assoc NeronModelInfra.schemeHomOverNpow_succ"
p2m_attr_erase "simp" "NeronModelInfra.schemeHomOverNpow_zero GoodReductionJacobian.relativeGroupLawOfGrpObj_inv GoodReductionJacobian.relativeGroupLawOfGrpObj_mul GoodReductionJacobian.overHomEquivSchemeHomOver_apply_coe GoodReductionJacobian.relativeGroupLawOfGrpObj_one GoodReductionJacobian.overHomEquivSchemeHomOver_symm_apply_left SheafOfModules.tensorUnit_eq AlgebraicGeometry.Scheme.Modules.tensorUnit_eq PresheafOfModules.InternalHom.presheaf_map_apply PresheafOfModules.InternalHom.curryFamily_app PresheafOfModules.InternalHom.add_app PresheafOfModules.InternalHom.smul_app PresheafOfModules.InternalHom.zero_app PresheafOfModules.ihomObj_map_val PresheafOfModules.ihomFunctor_map PresheafOfModules.InternalHom.restrict_app PresheafOfModules.InternalHom.postcomp_app PresheafOfModules.InternalHom.neg_app PresheafOfModules.curry'_app_val PresheafOfModules.InternalHom.presheaf_obj PresheafOfModules.ihomFunctor_obj PresheafOfModules.ihomObj_obj PresheafOfModules.InternalHom.sub_app PresheafOfModules.ihomMap_app_val AlgebraicGeometry.Scheme.Modules.tensorPow_zero AlgebraicGeometry.Scheme.Modules.tensorPow_succ AlgebraicGeometry.RelPicard.RigidifiedLineBundle.mk.sizeOf_spec AlgebraicGeometry.RelPicard.RigidifiedLineBundle.mk.injEq AlgebraicGeometry.Scheme.OrderedAffineCover.mk.injEq AlgebraicGeometry.OModulePresheaf.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCover.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.mk.injEq AlgebraicGeometry.Scheme.TwoAffineOpenCover.mk.injEq AlgebraicGeometry.Scheme.TwoAffineOpenCover.mk.sizeOf_spec AlgebraicGeometry.Scheme.TwoAffineOpenCover.pullback_U1 AlgebraicGeometry.Scheme.TwoAffineOpenCover.pullback_U0 TwoChartCech.Sections.mk.injEq TwoChartCech.Cover.mk.injEq TwoChartCech.GrothendieckComplex.mk.injEq TwoChartCech.Sections.mk.sizeOf_spec"
p2m_attr_erase "simp" "TwoChartCech.Cover.mk.sizeOf_spec TwoChartCech.Cover.lineBundle_r0_apply TwoChartCech.GrothendieckComplex.mk.sizeOf_spec TwoChartCech.Cover.lineBundle_r1_apply CoherentBaseChange.TwoTermComplex.mk.sizeOf_spec CoherentBaseChange.TwoTermComplex.mk.injEq AlgebraicGeometry.OModulePresheaf.prod_obj AlgebraicGeometry.OModulePresheaf.restrOpen_obj AlgebraicGeometry.OModulePresheaf.DevissageStep.mk.injEq AlgebraicGeometry.OModulePresheaf.pushforward_obj AlgebraicGeometry.OModulePresheaf.im_obj AlgebraicGeometry.OModulePresheaf.pow_obj AlgebraicGeometry.OModulePresheaf.fstHom_app AlgebraicGeometry.OModulePresheaf.ker_obj AlgebraicGeometry.OModulePresheaf.coker_obj AlgebraicGeometry.OModulePresheaf.DevissageStep.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCover.preimage_U AlgebraicGeometry.OModulePresheaf.sndHom_app AlgebraicGeometry.OModulePresheaf.Hom.mk.injEq AlgebraicGeometry.OModulePresheaf.Hom.id_app AlgebraicGeometry.OModulePresheaf.AffHom.appSections_apply AlgebraicGeometry.OModulePresheaf.AffHom.comp_app AlgebraicGeometry.OModulePresheaf.AffSES.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.AffHom.kerMap_coe AlgebraicGeometry.OModulePresheaf.AffHom.id_app AlgebraicGeometry.OModulePresheaf.Hom.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.Hom.toAffHom_app AlgebraicGeometry.OModulePresheaf.SES.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.AffHom.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.Hom.comp_app AlgebraicGeometry.OModulePresheaf.SES.mk.injEq AlgebraicGeometry.OModulePresheaf.AffHom.mk.injEq AlgebraicGeometry.OModulePresheaf.Hom.appSections_apply AlgebraicGeometry.OModulePresheaf.AffSES.mk.injEq PresheafOfModules.freeεIso_hom_app PresheafOfModules.freeμIso_hom_app AlgebraicGeometry.RelPicard.RepresentsRelSubPic.mk.injEq AlgebraicGeometry.RelPicard.SubPicCondition.mk.injEq AlgebraicGeometry.RelPicard.SubPicCondition.mk.sizeOf_spec AlgebraicGeometry.RelPicard.RepresentsRelSubPic.mk.sizeOf_spec"
p2m_attr_erase "simp" "AlgebraicGeometry.SmoothProperCurve.sectionBaseChange_coe_snd AlgebraicGeometry.SmoothProperCurve.sectionBaseChange_coe_fst AlgebraicCurve.CurveModel.mk.injEq AlgebraicCurve.CurveModel.mk.sizeOf_spec AlgebraicCurve.mulAdele_apply AlgebraicCurve.residuePairing_apply_coe AlgebraicCurve.mem_adeleBdd AlgebraicCurve.weilSmul_one AlgebraicCurve.diagonalHom_apply AlgebraicCurve.weilSmul_apply AlgebraicCurve.adeleSpaceMul_coe AlgebraicCurve.mulAdele_one AlgebraicGeometry.SmoothProperCurve.FiniteMapData.twoAffineOpenCover_U1 AlgebraicGeometry.SmoothProperCurve.FiniteMapData.mk.injEq AlgebraicGeometry.SmoothProperCurve.FiniteMapData.mk.sizeOf_spec AlgebraicGeometry.SmoothProperCurve.FiniteMapData.twoAffineOpenCover_U0 AlgebraicGeometry.RelPicard.SubPicCondition.onClasses_mk AlgebraicGeometry.RelPicard.relSubPicPresheaf_map_coe CategoryTheory.Functor.OverTotal.ofFibre_fst CategoryTheory.Functor.overTotal_map_fst AlgebraicGeometry.Scheme.LocalRepresentabilityULift.glueData_J AlgebraicGeometry.Scheme.LocalRepresentabilityULift.uliftYoneda_toGlued_uliftYonedaGluedToSheaf AlgebraicGeometry.Scheme.LocalRepresentabilityULift.glueData_t' AlgebraicGeometry.Scheme.LocalRepresentabilityULift.uliftYoneda_toGlued_uliftYonedaGluedToSheaf_assoc AlgebraicGeometry.Scheme.LocalRepresentabilityULift.uliftYonedaGluedToSheaf_app_toGlued AlgebraicGeometry.Scheme.LocalRepresentabilityULift.glueData_openCover_map AlgebraicGeometry.Scheme.LocalRepresentabilityULift.uliftYonedaGluedToSheaf_app_comp AlgebraicGeometry.Scheme.LocalRepresentabilityULift.glueData_V AlgebraicGeometry.Scheme.LocalRepresentabilityULift.glueData_t AlgebraicGeometry.Scheme.LocalRepresentabilityULift.glueData_U AlgebraicGeometry.Scheme.LocalRepresentabilityULift.glueData_f AlgebraicGeometry.RelPicard.designationOfRepresentableBy_P AlgebraicGeometry.RelPicard.designationOfRepresentableBy_toBase AlgebraicGeometry.RelPicard.rigSection_snd AlgebraicGeometry.RelPicard.RigidifiedLineBundle.ofInvertible_L AlgebraicGeometry.RelPicard.rigSection_snd_assoc AlgebraicGeometry.RelPicard.SubPicGroupCondition.mk.injEq AlgebraicGeometry.RelPicard.SubPicGroupCondition.mk.sizeOf_spec AlgebraicCurve.coe_cechH0Equiv_apply AlgebraicCurve.cechH1ToH1_mk"
p2m_attr_erase "simp" "AlgebraicCurve.lSpaceOn_univ AlgebraicCurve.lSpaceOn_empty AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.Divisor.mapRestrict_single AlgebraicCurve.Divisor.pushforward_single AlgebraicCurve.Place.coe_restrictInclusion AlgebraicCurve.Place.mem_fiber AlgebraicCurve.Place.restrict_toValuationSubring AlgebraicCurve.Divisor.degree_pushforward AlgebraicCurve.Place.restrictResidueMap_residue AlgebraicCurve.Pic0.coe_pushforwardDegZeroHom AlgebraicCurve.Pic0.coe_pullbackDegZeroHom AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Divisor.degree_pushforwardAlong AlgebraicCurve.Pic0.coe_degZeroCorrespondence AlgebraicCurve.Place.mem_fiberAlong"
p2m_attr_erase "simp" "AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.jqNModC_one ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one AlgebraicCurve.Place.differentialCoeff_zero AlgebraicCurve.Place.differentialCoeff_dCoord AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.injEq AlgebraicCurve.TranscendenceTower.mk.injEq AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec AlgebraicCurve.PoleDivisorPackage.mk.injEq AlgebraicGeometry.RelPicard.thetaBundle_def AlgebraicGeometry.RelPicard.picardBundle_def AlgebraicGeometry.RelEffCartierDiv.toRelEffDivisor_ofRelEffDivisor AlgebraicGeometry.RelEffCartierDiv.toRelEffDivisor_I AlgebraicGeometry.mapOnProdOver_fst_assoc AlgebraicGeometry.RelEffCartierDiv.mk.sizeOf_spec AlgebraicGeometry.RelEffCartierDiv.mk.injEq AlgebraicGeometry.mapOnProdOver_snd AlgebraicGeometry.mapOnProdOver_fst AlgebraicGeometry.mapOnProdOver_snd_assoc AlgebraicGeometry.mapOnProdOver_id AlgebraicCurve.RelEffDivisor.mk.sizeOf_spec AlgebraicCurve.mapOnProd_fst AlgebraicCurve.mapOnProd_fst_assoc AlgebraicCurve.mapOnProd_snd"
p2m_attr_erase "simp" "AlgebraicCurve.UnivDivisorPack.mk.injEq AlgebraicCurve.RelEffDivisor.mk.injEq AlgebraicCurve.UnivDivisorPack.mk.sizeOf_spec AlgebraicCurve.mapOnProd_snd_assoc AlgebraicGeometry.Scheme.Modules.exteriorPower_obj PresheafOfModules.exteriorPower_map_ιMulti PresheafOfModules.ExteriorPower.appₗ_apply AlgebraicGeometry.prodKerGraph_one AlgebraicGeometry.fibrePowOver.proj_comp AlgebraicGeometry.prodKerGraph_zero AlgebraicGeometry.RelEffCartierDiv.empty_I AlgebraicGeometry.fibrePowOver.proj_comp_assoc AlgebraicGeometry.graphOver_fst_assoc AlgebraicGeometry.RelEffCartierDiv.toPoint_comp AlgebraicGeometry.RelEffCartierDiv.toPoint_comp_assoc AlgebraicGeometry.graphOver_fst AlgebraicGeometry.RelEffCartierDiv.ofPoint_I AlgebraicGeometry.graphOver_snd AlgebraicGeometry.graphOver_snd_assoc AlgebraicCurve.SymmetricPowerPackage.mk.sizeOf_spec AlgebraicCurve.SymmetricPowerPackage.mk.injEq AlgebraicGeometry.FGSubalgebra.cocone_ι_app_apply AlgebraicGeometry.RelPicard.fst_toProdSpec AlgebraicGeometry.RelPicard.toProdSpec_fst_assoc AlgebraicGeometry.RelPicard.pointsSubBasepointModule_cons AlgebraicGeometry.RelPicard.pointsSubBasepointModule_nil AlgebraicGeometry.RelPicard.fst_toProdSpec_assoc AlgebraicGeometry.RelPicard.toProdSpec_fst AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.sub_app AlgebraicGeometry.Scheme.IdealSheafData.sres_sresTop AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.add_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.mk.sizeOf_spec AlgebraicGeometry.Scheme.IdealSheafData.coe_resLE AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.smul_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.coe_ofLE_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.ideal_range AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.zero_app AlgebraicGeometry.Scheme.IdealSheafData.sres_sres AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.comp_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.neg_app"
p2m_attr_erase "simp" "AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.id_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.coe_mulRight_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.nsmul_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.mk.injEq AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.zsmul_app AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.sizeOf_spec AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.injEq AlgebraicCurve.adeleSingle_coe AlgebraicCurve.kaehlerResidueTermKFam_apply AlgebraicCurve.Place.LocalResidueData.mk.injEq AlgebraicCurve.Place.LocalResidueData.mk.sizeOf_spec AlgebraicCurve.Place.kw_ffgc_adicCompletionComapIntegers_coe AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.sizeOf_spec AlgebraicCurve.Place.mem_simplePoleSubmodule AlgebraicCurve.Place.coe_uniformizerSubring ModularCurve.Lg37.Lg37CompletionSection.mk.injEq AlgebraicCurve.Place.CoefficientFieldSection.mk.injEq AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.injEq ModularCurve.Lg37.Lg37CompletionSection.mk.sizeOf_spec AlgebraicCurve.Place.CoefficientFieldSection.mk.sizeOf_spec AlgebraicCurve.Place.poleSubmodule_one AlgebraicCurve.Place.mem_poleSubmodule AlgebraicGeometry.Scheme.Modules.toUnitSection_ofUnitSection AlgebraicGeometry.Scheme.Modules.pullbackSection_def AlgebraicGeometry.Scheme.Modules.ofUnitSection_toUnitSection PresheafOfModules.InternalHom.IsSheafAux.appAt_toPresheafHom SheafOfModules.ihomSectionsEquivFamily_unit AlgebraicGeometry.Scheme.Modules.restrictHomEquivFamily_apply SheafOfModules.ihomEval_unit_app AlgebraicGeometry.Scheme.Modules.ihomEval_zero_right AlgebraicGeometry.Scheme.Modules.ihomEval_zero_left AlgebraicGeometry.Scheme.Modules.homOfFamily_app_apply SheafOfModules.unit_ihomSectionsEquivFamily AlgebraicGeometry.Scheme.Modules.familyOfHom_app AlgebraicGeometry.Scheme.Modules.restrictUnitIso_hom_app_apply AlgebraicGeometry.Scheme.Modules.restrictUnitIso_inv_app_apply AlgebraicGeometry.Scheme.Modules.restrictHomOfFamily_app_apply AlgebraicGeometry.Scheme.Modules.restrictHomEquivFamily_symm_apply AlgebraicGeometry.Scheme.Modules.tensorSections_zero_right AlgebraicGeometry.Scheme.Modules.map_unitSection"
p2m_attr_erase "simp" "AlgebraicGeometry.Scheme.Modules.tensorSectionsBilin_apply AlgebraicGeometry.Scheme.Modules.tensorPowSection_zero AlgebraicGeometry.Scheme.Modules.tensorSections_zero_left AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_neg AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_zero AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_sub AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_add AlgebraicGeometry.Scheme.OrderedAffineCover.toCoverOf_U AlgebraicGeometry.Scheme.OrderedAffineCoverOf.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCoverOf.mk.injEq AlgebraicGeometry.Scheme.OrderedAffineCover.restrict_U AlgebraicGeometry.OModulePresheaf.Leray.restrictToPreimage_U DoubleComplex.Bounded.mk.injEq DoubleComplex.Bounded.mk.sizeOf_spec DoubleComplex.Convergence.mk.injEq DoubleComplex.Convergence.mk.sizeOf_spec DoubleComplex.SubQuot.mk.sizeOf_spec DoubleComplex.SubQuot.mk.injEq AlgebraicGeometry.ChowDatumProj.mk.sizeOf_spec AlgebraicGeometry.ChowDatum.mk.sizeOf_spec AlgebraicGeometry.ChowDatumProj.mk.injEq AlgebraicGeometry.ChowDatum.mk.injEq ProjSpaceCech.GradedModule.mk.injEq ProjSpaceCech.GradedModule.mk.sizeOf_spec ProjSpaceCech.GradedModule.Frac.mk.sizeOf_spec ProjSpaceCech.GradedModule.Presentation.mk.injEq ProjSpaceCech.GradedModule.Frac.mk.injEq ProjSpaceCech.GradedModule.Presentation.mk.sizeOf_spec ProjSpaceCech.GradedModule.Hom.shift_toLinearMap ProjSpaceCech.GradedModule.Hom.mk.sizeOf_spec ProjSpaceCech.GradedModule.Hom.mk.injEq TwoChartCech.Mumford.dK_apply TwoChartCech.Mumford.ι0_apply TwoChartCech.Mumford.ι1_apply TwoChartCech.KerCoprod.dK_apply TwoChartCech.KerCoprod.ι1_apply TwoChartCech.KerCoprod.ι0_apply AlgebraicGeometry.tilde.functorCompPullbackSpecIso_app AlgebraicGeometry.RelPicard.algEquivZeroGroupCut_toSubPicCondition AlgebraicGeometry.RelPicard.LFP.stageHom_val"
p2m_attr_erase "simp" "AlgebraicGeometry.RelPicard.BaseChange.relSubPicPresheafRestrictIso_hom_app_coe AlgebraicGeometry.RelPicard.BaseChange.relSubPicPresheafRestrictIso_inv_app_coe AlgebraicGeometry.RelPicard.BaseChange.restrict_P AlgebraicGeometry.RelEffCartierDiv.IsUniversal.lift_comp AlgebraicGeometry.RelEffCartierDiv.functor_map_fst AlgebraicGeometry.RelEffCartierDiv.IsUniversal.homEquiv_apply AlgebraicGeometry.RelEffCartierDiv.IsUniversal.lift_pullbackAlong AlgebraicGeometry.RelEffCartierDiv.IsUniversal.homEquiv_symm_apply AlgebraicGeometry.RelEffCartierDiv.IsUniversal.lift_comp_assoc AlgebraicGeometry.RelEffCartierDiv.supportedIn_top AlgebraicGeometry.RelEffCartierDiv.mem_supportedIn_iff AlgebraicGeometry.RelEffCartierDiv.supportedIn_top_eq AlgebraicGeometry.RelEffCartierDiv.restrictAlong_extendAlong AlgebraicGeometry.RelEffCartierDiv.extendAlong_I AlgebraicGeometry.RelEffCartierDiv.resProdMap_snd AlgebraicGeometry.RelEffCartierDiv.restrictAlong_I AlgebraicGeometry.RelEffCartierDiv.extendAlong_restrictAlong AlgebraicGeometry.RelEffCartierDiv.resProdMap_fst_assoc AlgebraicGeometry.RelEffCartierDiv.resProdMap_snd_assoc AlgebraicGeometry.RelEffCartierDiv.resProdMap_fst CoherentBaseChange.FibreH0Family.mk.sizeOf_spec CoherentBaseChange.FibreH0Family.mk.injEq AlgebraicGeometry.Scheme.Modules.ProjPresentation.mk.injEq AlgebraicGeometry.Scheme.Modules.ProjPresentation.mk.sizeOf_spec AlgebraicCurve.CurveModel.coe_gInf AlgebraicCurve.CurveModel.coe_tInvChart AlgebraicCurve.CurveModel.ιInf_gluedToBase_assoc AlgebraicCurve.CurveModel.ιInf_gluedToBase AlgebraicCurve.CurveModel.primeOfι₀_asIdeal AlgebraicCurve.CurveModel.coe_tChart AlgebraicCurve.CurveModel.ι₀_gluedToBase_assoc AlgebraicCurve.CurveModel.primeOfιInf_asIdeal AlgebraicCurve.CurveModel.ι₀_gluedToBase AlgebraicCurve.CurveModel.coe_tma AlgebraicCurve.CurveModel.coe_primeEquivChartPlaces AlgebraicGeometry.ProjSpace.twistObj.mk.injEq AlgebraicGeometry.ProjSpace.twistObj.zero_val AlgebraicGeometry.ProjSpace.twistObj.add_val AlgebraicGeometry.ProjSpace.twist_res_val AlgebraicGeometry.ProjSpace.twist_smul_val"
p2m_attr_erase "simp" "AlgebraicGeometry.ProjSpace.twistGradeToObj_val AlgebraicGeometry.ProjSpace.twistObj.smul_val AlgebraicGeometry.ProjSpace.twistGradeEquiv_apply_val AlgebraicGeometry.ProjSpace.twistObj.mk.sizeOf_spec AlgebraicGeometry.schemeFibreEndo_snd AlgebraicGeometry.schemeFibreEndo_fst"

set_option autoImplicit false

p2m_open "CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra~schemeHomOverComp GoodReductionJacobian CerednikDrinfeld CerednikDrinfeld.QM CerednikDrinfeld.QM.FakeEllipticCurve"
open scoped Quaternion

universe u

section BC

variable {S S' : Type u} [CommRing S] [CommRing S'] {φ : S →+* S'}
  {X Y : Scheme.{u}} {fX : X ⟶ Spec (CommRingCat.of S')} {fY : Y ⟶ Spec (CommRingCat.of S)}
  (g : X ⟶ Y) (sq : CategoryTheory.IsPullback g fX fY (Spec.map (CommRingCat.ofHom φ)))

def bc {T : Scheme.{u}} {t' : T ⟶ Spec (CommRingCat.of S')} (P : SchemeHomOver t' fX) :
    SchemeHomOver (t' ≫ Spec.map (CommRingCat.ofHom φ)) fY :=
  ⟨P.1 ≫ g, by rw [Category.assoc, sq.w, ← Category.assoc, P.2]⟩

theorem bc_coe {T : Scheme.{u}} {t' : T ⟶ Spec (CommRingCat.of S')} (P : SchemeHomOver t' fX) :
    (bc g sq P).1 = P.1 ≫ g := rfl

theorem bc_injective {T : Scheme.{u}} {t' : T ⟶ Spec (CommRingCat.of S')} {P Q : SchemeHomOver t' fX}
    (h : bc g sq P = bc g sq Q) : P = Q := by
  apply Subtype.ext
  apply sq.hom_ext
  · exact congrArg Subtype.val h
  · rw [P.2, Q.2]

variable (LX : RelativeGroupLaw S' fX) (LY : RelativeGroupLaw S fY)
  (hmul : ∀ {T : Scheme.{u}} (t' : T ⟶ Spec (CommRingCat.of S')) (P Q : SchemeHomOver t' fX),
    (LX.mul t' P Q).1 ≫ g = (LY.mul (t' ≫ Spec.map (CommRingCat.ofHom φ)) (bc g sq P) (bc g sq Q)).1)

include hmul in
theorem bc_mul {T : Scheme.{u}} (t' : T ⟶ Spec (CommRingCat.of S')) (P Q : SchemeHomOver t' fX) :
    bc g sq (LX.mul t' P Q) = LY.mul _ (bc g sq P) (bc g sq Q) := Subtype.ext (hmul t' P Q)

include hmul in
theorem bc_one {T : Scheme.{u}} (t' : T ⟶ Spec (CommRingCat.of S')) : bc g sq (LX.one t') = LY.one _ := by
  have h := bc_mul g sq LX LY hmul t' (LX.one t') (LX.one t')
  rw [LX.one_mul] at h

  have h2 := congrArg (fun z => LY.mul _ (LY.inv _ (bc g sq (LX.one t'))) z) h
  rw [← LY.mul_assoc, LY.inv_mul_cancel, LY.one_mul] at h2
  exact h2.symm

include hmul in
theorem bc_inv {T : Scheme.{u}} (t' : T ⟶ Spec (CommRingCat.of S')) (P : SchemeHomOver t' fX) :
    bc g sq (LX.inv t' P) = LY.inv _ (bc g sq P) := by
  have h := bc_mul g sq LX LY hmul t' (LX.inv t' P) P
  rw [LX.inv_mul_cancel, bc_one g sq LX LY hmul] at h

  have h2 := congrArg (fun z => LY.mul _ z (LY.inv _ (bc g sq P))) h
  rw [LY.one_mul, LY.mul_assoc, RelativeGroupLaw.mul_inv_cancel, LY.mul_one] at h2
  exact h2.symm

include hmul in
theorem bc_nsmul {T : Scheme.{u}} (t' : T ⟶ Spec (CommRingCat.of S')) (n : ℕ) (P : SchemeHomOver t' fX) :
    bc g sq (nsmulPt LX t' n P) = nsmulPt LY _ n (bc g sq P) := by
  induction n with
  | zero => exact bc_one g sq LX LY hmul t'
  | succ n ih =>
    show bc g sq (LX.mul t' (nsmulPt LX t' n P) P) = LY.mul _ (nsmulPt LY _ n (bc g sq P)) (bc g sq P)
    rw [bc_mul g sq LX LY hmul, ih]

omit sq in

theorem factorsThrough_of_val_eq {C : Scheme.{u}} (lev : C ⟶ Y) {T : Scheme.{u}} {t₁ t₂ : T ⟶ Spec (CommRingCat.of S)}
    (P : SchemeHomOver t₁ fY) (Q : SchemeHomOver t₂ fY) (h : P.1 = Q.1) :
    FactorsThrough lev P → FactorsThrough lev Q := by
  rintro ⟨P₀, hP₀⟩; exact ⟨P₀, hP₀.trans h⟩

end BC

section PtAux
variable {R : Type} [CommRing R] {A A' : Scheme.{0}} {f : A ⟶ Spec (CommRingCat.of R)} {f' : A' ⟶ Spec (CommRingCat.of R)}
  (L : RelativeGroupLaw R f) (L' : RelativeGroupLaw R f') (φ : A ⟶ A') (hφ : φ ≫ f' = f)
  (hmul : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of R)) (P Q : SchemeHomOver t f),
    mapPt φ hφ (L.mul t P Q) = L'.mul t (mapPt φ hφ P) (mapPt φ hφ Q))

include hmul in
theorem E3Aux.mapPt_one {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of R)) : mapPt φ hφ (L.one t) = L'.one t := by
  have h := hmul t (L.one t) (L.one t)
  rw [L.one_mul] at h
  have h2 := congrArg (fun z => L'.mul _ (L'.inv _ (mapPt φ hφ (L.one t))) z) h
  rw [← L'.mul_assoc, L'.inv_mul_cancel, L'.one_mul] at h2
  exact h2.symm

include hmul in
theorem E3Aux.mapPt_inv {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of R)) (P : SchemeHomOver t f) :
    mapPt φ hφ (L.inv t P) = L'.inv t (mapPt φ hφ P) := by
  have h := hmul t (L.inv t P) P
  rw [L.inv_mul_cancel, E3Aux.mapPt_one L L' φ hφ hmul] at h
  have h2 := congrArg (fun z => L'.mul _ z (L'.inv _ (mapPt φ hφ P))) h
  rw [L'.one_mul, L'.mul_assoc, RelativeGroupLaw.mul_inv_cancel, L'.mul_one] at h2
  exact h2.symm

omit hmul in
theorem E3Aux.inv_one {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of R)) : L.inv t (L.one t) = L.one t := by
  have := L.inv_mul_cancel t (L.one t)
  rw [L.mul_one] at this
  exact this

omit hmul in

theorem E3Aux.nsmulPt_eq_pow {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of R)) (n : ℕ) (P : SchemeHomOver t f) :
    nsmulPt L t n P = (letI := L.pointGroup t; P ^ n) := by
  letI := L.pointGroup t
  induction n with
  | zero => rfl
  | succ n ih =>
    show L.mul t (nsmulPt L t n P) P = P ^ (n + 1)
    rw [ih, pow_succ]; rfl

omit hmul in
theorem E3Aux.nsmulPt_natural {T T' : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of R)) (t' : T' ⟶ Spec (CommRingCat.of R))
    (ψ : T' ⟶ T) (hψ : ψ ≫ t = t') (n : ℕ) (P : SchemeHomOver t f) :
    schemeHomOverComp ψ hψ (nsmulPt L t n P) = nsmulPt L t' n (schemeHomOverComp ψ hψ P) := by
  induction n with
  | zero => exact L.one_natural t t' ψ hψ
  | succ n ih =>
    show schemeHomOverComp ψ hψ (L.mul t (nsmulPt L t n P) P) = L.mul t' (nsmulPt L t' n (schemeHomOverComp ψ hψ P)) (schemeHomOverComp ψ hψ P)
    rw [L.mul_natural, ih]

omit hmul in
theorem E3Aux.nsmulPt_val_congr {T : Scheme.{0}} {t₁ t₂ : T ⟶ Spec (CommRingCat.of R)} (h : t₁ = t₂) (n : ℕ)
    (P : SchemeHomOver t₁ f) (Q : SchemeHomOver t₂ f) (hPQ : P.1 = Q.1) :
    (nsmulPt L t₁ n P).1 = (nsmulPt L t₂ n Q).1 := by
  subst h
  have : P = Q := Subtype.ext hPQ
  subst this
  rfl

omit hmul in
theorem E3Aux.one_val_congr {T : Scheme.{0}} {t₁ t₂ : T ⟶ Spec (CommRingCat.of R)} (h : t₁ = t₂) :
    (L.one t₁).1 = (L.one t₂).1 := by
  subst h; rfl

omit hmul in

theorem E3Aux.ext_of_schDominant {W X Y Z : Scheme.{0}} (s : Y ⟶ Z) [IsSeparated s] {f₁ f₂ : X ⟶ Y}
    (h : f₁ ≫ s = f₂ ≫ s) (ι : W ⟶ X) [IsSchemeTheoreticallyDominant ι] (hU : ι ≫ f₁ = ι ≫ f₂) : f₁ = f₂ := by
  let X' : Over Z := Over.mk (f₁ ≫ s)
  let Y' : Over Z := Over.mk s
  let U' : Over Z := Over.mk (ι ≫ f₁ ≫ s)
  let f' : X' ⟶ Y' := Over.homMk f₁ rfl
  let g' : X' ⟶ Y' := Over.homMk f₂ h.symm
  let ι' : U' ⟶ X' := Over.homMk ι rfl
  haveI : IsSeparated Y'.hom := ‹IsSeparated s›
  have hfg : ι' ≫ f' = ι' ≫ g' := by ext1; exact hU
  have hl : equalizer.lift ι' hfg ≫ equalizer.ι f' g' = ι' := equalizer.lift_ι _ _
  have hker : (equalizer.ι f' g').left.ker = ⊥ := by
    apply le_bot_iff.mp
    have h1 := (equalizer.lift ι' hfg).left.le_ker_comp (equalizer.ι f' g').left
    rw [← Over.comp_left, hl] at h1
    exact h1.trans (le_of_eq (IsSchemeTheoreticallyDominant.ker_eq_bot ι))
  haveI : IsIso (equalizer.ι f' g').left := IsClosedImmersion.isIso_iff_ker_eq_bot.mpr hker
  apply (cancel_epi (equalizer.ι f' g').left).mp
  have hc := congrArg (fun k => k.left) (equalizer.condition f' g')
  simp only [Over.comp_left] at hc
  exact hc

end PtAux

set_option maxHeartbeats 6400000 in
theorem solution
    {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} {N : ℕ}
    (O : ValuationSubring (AlgebraicClosure ℚ)) (ℓ : ℕ) (hℓN : Nat.Coprime ℓ N) (hℓΛ : ((ℓ : ℚ) : ℍ[ℚ, a, b]) ∈ Λ) (h1 : (1 : ℍ[ℚ, a, b]) ∈ Λ)
    (𝒜 𝒟 : FakeEllipticCurve Λ N ↥O) (E d : FakeEllipticCurve Λ N (AlgebraicClosure ℚ))
    (gE : E.A ⟶ 𝒜.A) (hgE : CategoryTheory.IsPullback gE E.f 𝒜.f (Spec.map (CommRingCat.ofHom O.subtype)))
    (hgE_mul : ∀ {T : Scheme.{0}} (t' : T ⟶ Spec (CommRingCat.of (AlgebraicClosure ℚ))) (P Q : SchemeHomOver t' E.f),
      (E.L.mul t' P Q).1 ≫ gE =
        (𝒜.L.mul (t' ≫ Spec.map (CommRingCat.ofHom O.subtype))
          ⟨P.1 ≫ gE, by rw [Category.assoc, hgE.w, ← Category.assoc, P.2]⟩
          ⟨Q.1 ≫ gE, by rw [Category.assoc, hgE.w, ← Category.assoc, Q.2]⟩).1)
    (hgE_act : ∀ x : ↥Λ, E.act x ≫ gE = gE ≫ 𝒜.act x)
    (hgE_lev : ∀ {T : Scheme.{0}} (t' : T ⟶ Spec (CommRingCat.of (AlgebraicClosure ℚ))) (P : SchemeHomOver t' E.f),
      FactorsThrough E.lev P ↔ ∃ P₀ : T ⟶ 𝒜.C, P₀ ≫ 𝒜.lev = P.1 ≫ gE)
    (gd : d.A ⟶ 𝒟.A) (hgd : CategoryTheory.IsPullback gd d.f 𝒟.f (Spec.map (CommRingCat.ofHom O.subtype)))
    (hgd_mul : ∀ {T : Scheme.{0}} (t' : T ⟶ Spec (CommRingCat.of (AlgebraicClosure ℚ))) (P Q : SchemeHomOver t' d.f),
      (d.L.mul t' P Q).1 ≫ gd =
        (𝒟.L.mul (t' ≫ Spec.map (CommRingCat.ofHom O.subtype))
          ⟨P.1 ≫ gd, by rw [Category.assoc, hgd.w, ← Category.assoc, P.2]⟩
          ⟨Q.1 ≫ gd, by rw [Category.assoc, hgd.w, ← Category.assoc, Q.2]⟩).1)
    (hgd_act : ∀ x : ↥Λ, d.act x ≫ gd = gd ≫ 𝒟.act x)
    (K : E.ExtraLevel ℓ)
    (φ : E.A ⟶ d.A) (hφ : φ ≫ d.f = E.f)
    (hker : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of (AlgebraicClosure ℚ))) (P : SchemeHomOver t E.f),
      mapPt φ hφ P = d.L.one t ↔ FactorsThrough K.levK P)
    (Φ : 𝒜.A ⟶ 𝒟.A) (hΦ : Φ ≫ 𝒟.f = 𝒜.f) (hext : gE ≫ Φ = φ ≫ gd)
    (hΦ_mul : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of ↥O)) (P Q : SchemeHomOver t 𝒜.f),
      mapPt Φ hΦ (𝒜.L.mul t P Q) = 𝒟.L.mul t (mapPt Φ hΦ P) (mapPt Φ hΦ Q))
    (hΦ_act : ∀ x : ↥Λ, 𝒜.act x ≫ Φ = Φ ≫ 𝒟.act x)
    (Ψ : 𝒟.A ⟶ 𝒜.A) (hΨ : Ψ ≫ 𝒜.f = 𝒟.f)
    (hΦΨ : Φ ≫ Ψ = 𝒜.act ⟨((ℓ : ℚ) : ℍ[ℚ, a, b]), hℓΛ⟩)
    (hΨΦ : Ψ ≫ Φ = 𝒟.act ⟨((ℓ : ℚ) : ℍ[ℚ, a, b]), hℓΛ⟩) :
    ∃ 𝒦 : 𝒜.ExtraLevel ℓ,
      (∀ {T : Scheme.{0}} (t' : T ⟶ Spec (CommRingCat.of (AlgebraicClosure ℚ))) (P : SchemeHomOver t' E.f),
          FactorsThrough K.levK P ↔ ∃ P₀ : T ⟶ 𝒦.K, P₀ ≫ 𝒦.levK = P.1 ≫ gE) ∧
      (∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of ↥O)) (P : SchemeHomOver t 𝒜.f),
          mapPt Φ hΦ P = 𝒟.L.one t ↔ FactorsThrough 𝒦.levK P) := by
  classical

  have slot_ell_ne_zero : ℓ ≠ 0 := by
    haveI := K.levK_flat
    haveI := K.levK_finite
    obtain ⟨P₀, hP₀⟩ := K.levK_one (𝟙 (Spec (CommRingCat.of (AlgebraicClosure ℚ))))
    let x : ↥K.K := P₀.base (⟨⊥, Ideal.bot_prime⟩ : PrimeSpectrum (AlgebraicClosure ℚ))
    have h1 := (K.levK ≫ E.f).one_le_finrank_map x
    rw [K.levK_rank] at h1
    intro h
    rw [h] at h1
    simp at h1

  have hΨΦpt : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of ↥O)) (P : SchemeHomOver t 𝒜.f),
      mapPt Ψ hΨ (mapPt Φ hΦ P) = nsmulPt 𝒜.L t ℓ P := by
    intro T t P
    rw [← CerednikDrinfeld.QM.FakeEllipticCurve.pushPt_act_natCast_eq_nsmulPt 𝒜 h1 ℓ hℓΛ t P]
    apply Subtype.ext
    show (P.1 ≫ Φ) ≫ Ψ = P.1 ≫ 𝒜.act ⟨((ℓ : ℚ) : ℍ[ℚ, a, b]), hℓΛ⟩
    rw [Category.assoc, hΦΨ]
  have hΦΨpt : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of ↥O)) (Q : SchemeHomOver t 𝒟.f),
      mapPt Φ hΦ (mapPt Ψ hΨ Q) = nsmulPt 𝒟.L t ℓ Q := by
    intro T t Q
    rw [← CerednikDrinfeld.QM.FakeEllipticCurve.pushPt_act_natCast_eq_nsmulPt 𝒟 h1 ℓ hℓΛ t Q]
    apply Subtype.ext
    show (Q.1 ≫ Ψ) ≫ Φ = Q.1 ≫ 𝒟.act ⟨((ℓ : ℚ) : ℍ[ℚ, a, b]), hℓΛ⟩
    rw [Category.assoc, hΨΦ]
  obtain ⟨hfinΦ, hflatΦ, hlfpΦ, -⟩ :=
    CerednikDrinfeld.QM.FakeEllipticCurve.isFinite_flat_surjective_of_mapPt_mapPt_eq_nsmulPt_valuationSubring
      O 𝒜 𝒟 Φ hΦ hΦ_mul Ψ hΨ ℓ (Nat.pos_of_ne_zero slot_ell_ne_zero) hΨΦpt hΦΨpt
  haveI := hfinΦ; haveI := hflatΦ; haveI := hlfpΦ

  obtain ⟨Kk, ι, hcl, hfinK, hflatK, hlfpK, hkerT, hrankK⟩ :=
    CerednikDrinfeld.QM.FakeEllipticCurve.exists_kernel_of_isFinite_of_flat 𝒜 𝒟 Φ hΦ

  have hΦone : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of ↥O)), mapPt Φ hΦ (𝒜.L.one t) = 𝒟.L.one t := by
    intro T t; exact E3Aux.mapPt_one 𝒜.L 𝒟.L Φ hΦ hΦ_mul t
  have hΦinv : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of ↥O)) (P : SchemeHomOver t 𝒜.f),
      mapPt Φ hΦ (𝒜.L.inv t P) = 𝒟.L.inv t (mapPt Φ hΦ P) := by
    intro T t P; exact E3Aux.mapPt_inv 𝒜.L 𝒟.L Φ hΦ hΦ_mul t P
  have hact_one : ∀ (x : ↥Λ) {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of ↥O)),
      pushPt (𝒟.act x) (𝒟.act_over x) (𝒟.L.one t) = 𝒟.L.one t := by
    intro x T t; exact E3Aux.mapPt_one 𝒟.L 𝒟.L (𝒟.act x) (𝒟.act_over x) (𝒟.act_hom x) t

  have hgen : ∀ {T : Scheme.{0}} (t' : T ⟶ Spec (CommRingCat.of (AlgebraicClosure ℚ))) (P : SchemeHomOver t' E.f),
      FactorsThrough K.levK P ↔ ∃ P₀ : T ⟶ Kk, P₀ ≫ ι = P.1 ≫ gE := by
    intro T t' P
    have hmapbc : mapPt Φ hΦ (bc gE hgE P) = bc gd hgd (mapPt φ hφ P) := by
      apply Subtype.ext
      show (P.1 ≫ gE) ≫ Φ = (P.1 ≫ φ) ≫ gd
      rw [Category.assoc, hext, Category.assoc]
    have hbcone : bc gd hgd (d.L.one t') = 𝒟.L.one _ := bc_one gd hgd d.L 𝒟.L hgd_mul t'
    constructor
    · intro hP
      have h1 : mapPt φ hφ P = d.L.one t' := (hker t' P).2 hP
      have h2 : FactorsThrough ι (bc gE hgE P) := by
        apply (hkerT _ _).2
        rw [hmapbc, h1, hbcone]
      obtain ⟨P₀, hP₀⟩ := h2
      exact ⟨P₀, hP₀⟩
    · rintro ⟨P₀, hP₀⟩
      have h2 : FactorsThrough ι (bc gE hgE P) := ⟨P₀, hP₀⟩
      rw [hkerT, hmapbc, ← hbcone] at h2
      exact (hker t' P).1 (bc_injective gd hgd h2)

  have slot_torsion : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of ↥O)) (P : SchemeHomOver t 𝒜.f),
      FactorsThrough ι P → nsmulPt 𝒜.L t ℓ P = 𝒜.L.one t := by
    haveI := hflatK; haveI := hcl; haveI := hfinK
    haveI := K.levK_flat; haveI := K.levK_finite; haveI := K.levK_closed
    haveI : IsProper 𝒜.f := 𝒜.bundle.proper
    let ι₀ := Spec.map (CommRingCat.ofHom O.subtype)

    haveI : IsDominant ι₀ := by
      refine ⟨?_⟩
      show DenseRange (PrimeSpectrum.comap (CommRingCat.ofHom O.subtype).hom)
      rw [PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical]
      have hk : RingHom.ker (CommRingCat.ofHom O.subtype).hom = ⊥ :=
        (RingHom.injective_iff_ker_eq_bot _).mp (fun a b hab => Subtype.ext hab)
      rw [hk]
      exact bot_le
    haveI : IsSchemeTheoreticallyDominant ι₀ := IsSchemeTheoreticallyDominant.of_isDominant _
    haveI : IsSchemeTheoreticallyDominant (pullback.fst (ι ≫ 𝒜.f) ι₀) :=
      IsSchemeTheoreticallyDominant.of_isPullback (IsPullback.of_hasPullback (ι ≫ 𝒜.f) ι₀).flip

    have hq : (pullback.fst (ι ≫ 𝒜.f) ι₀ ≫ ι) ≫ 𝒜.f = pullback.snd (ι ≫ 𝒜.f) ι₀ ≫ ι₀ := by
      rw [Category.assoc]; exact pullback.condition
    let q₁ : pullback (ι ≫ 𝒜.f) ι₀ ⟶ E.A := hgE.lift (pullback.fst (ι ≫ 𝒜.f) ι₀ ≫ ι) (pullback.snd (ι ≫ 𝒜.f) ι₀) hq
    have hq₁g : q₁ ≫ gE = pullback.fst (ι ≫ 𝒜.f) ι₀ ≫ ι := hgE.lift_fst _ _ _
    have hq₁f : q₁ ≫ E.f = pullback.snd (ι ≫ 𝒜.f) ι₀ := hgE.lift_snd _ _ _
    obtain ⟨v, hv⟩ := (hgen (pullback.snd (ι ≫ 𝒜.f) ι₀) ⟨q₁, hq₁f⟩).2 ⟨pullback.fst (ι ≫ 𝒜.f) ι₀, hq₁g.symm⟩
    have hbase : pullback.fst (ι ≫ 𝒜.f) ι₀ ≫ (ι ≫ 𝒜.f) = pullback.snd (ι ≫ 𝒜.f) ι₀ ≫ ι₀ := by
      rw [← Category.assoc]; exact hq

    let Pu : SchemeHomOver (ι ≫ 𝒜.f) 𝒜.f := ⟨ι, rfl⟩
    have hU : (nsmulPt 𝒜.L (ι ≫ 𝒜.f) ℓ Pu).1 = (𝒜.L.one (ι ≫ 𝒜.f)).1 := by
      apply E3Aux.ext_of_schDominant 𝒜.f (by rw [(nsmulPt 𝒜.L (ι ≫ 𝒜.f) ℓ Pu).2, (𝒜.L.one (ι ≫ 𝒜.f)).2])
        (pullback.fst (ι ≫ 𝒜.f) ι₀)
      have e1 : pullback.fst (ι ≫ 𝒜.f) ι₀ ≫ (nsmulPt 𝒜.L (ι ≫ 𝒜.f) ℓ Pu).1 =
          (nsmulPt 𝒜.L (pullback.fst (ι ≫ 𝒜.f) ι₀ ≫ (ι ≫ 𝒜.f)) ℓ
            (schemeHomOverComp (pullback.fst (ι ≫ 𝒜.f) ι₀) rfl Pu)).1 := by
        rw [← E3Aux.nsmulPt_natural]; rfl
      have e2 : (nsmulPt 𝒜.L (pullback.fst (ι ≫ 𝒜.f) ι₀ ≫ (ι ≫ 𝒜.f)) ℓ
            (schemeHomOverComp (pullback.fst (ι ≫ 𝒜.f) ι₀) rfl Pu)).1 =
          (nsmulPt 𝒜.L (pullback.snd (ι ≫ 𝒜.f) ι₀ ≫ ι₀) ℓ (bc gE hgE ⟨q₁, hq₁f⟩)).1 :=
        E3Aux.nsmulPt_val_congr 𝒜.L hbase ℓ _ _ (by show pullback.fst (ι ≫ 𝒜.f) ι₀ ≫ ι = q₁ ≫ gE; exact hq₁g.symm)
      have e3 : nsmulPt 𝒜.L (pullback.snd (ι ≫ 𝒜.f) ι₀ ≫ ι₀) ℓ (bc gE hgE ⟨q₁, hq₁f⟩) =
          bc gE hgE (nsmulPt E.L (pullback.snd (ι ≫ 𝒜.f) ι₀) ℓ ⟨q₁, hq₁f⟩) :=
        (bc_nsmul gE hgE E.L 𝒜.L hgE_mul _ ℓ _).symm
      have e4 : nsmulPt E.L (pullback.snd (ι ≫ 𝒜.f) ι₀) ℓ ⟨q₁, hq₁f⟩ = E.L.one _ :=
        K.levK_torsion _ _ ⟨v, hv⟩
      have e5 : bc gE hgE (E.L.one (pullback.snd (ι ≫ 𝒜.f) ι₀)) = 𝒜.L.one _ := bc_one gE hgE E.L 𝒜.L hgE_mul _
      have e6 : (𝒜.L.one (pullback.snd (ι ≫ 𝒜.f) ι₀ ≫ ι₀)).1 = (𝒜.L.one (pullback.fst (ι ≫ 𝒜.f) ι₀ ≫ (ι ≫ 𝒜.f))).1 :=
        E3Aux.one_val_congr 𝒜.L hbase.symm
      have e7 : (𝒜.L.one (pullback.fst (ι ≫ 𝒜.f) ι₀ ≫ (ι ≫ 𝒜.f))).1 =
          pullback.fst (ι ≫ 𝒜.f) ι₀ ≫ (𝒜.L.one (ι ≫ 𝒜.f)).1 := by
        rw [← 𝒜.L.one_natural (ι ≫ 𝒜.f) _ (pullback.fst (ι ≫ 𝒜.f) ι₀) rfl]; rfl
      rw [e1, e2, e3, e4, e5, e6, e7]
    intro T t P hP
    obtain ⟨P₀, hP₀⟩ := hP
    apply Subtype.ext
    have hb : P₀ ≫ (ι ≫ 𝒜.f) = t := by rw [← Category.assoc, hP₀, P.2]
    have c1 : (nsmulPt 𝒜.L t ℓ P).1 = (nsmulPt 𝒜.L (P₀ ≫ (ι ≫ 𝒜.f)) ℓ (schemeHomOverComp P₀ rfl Pu)).1 :=
      E3Aux.nsmulPt_val_congr 𝒜.L hb.symm ℓ P _ (by show P.1 = P₀ ≫ ι; exact hP₀.symm)
    have c2 : (nsmulPt 𝒜.L (P₀ ≫ (ι ≫ 𝒜.f)) ℓ (schemeHomOverComp P₀ rfl Pu)).1 = P₀ ≫ (nsmulPt 𝒜.L (ι ≫ 𝒜.f) ℓ Pu).1 := by
      rw [← E3Aux.nsmulPt_natural]; rfl
    have c3 : P₀ ≫ (𝒜.L.one (ι ≫ 𝒜.f)).1 = (𝒜.L.one (P₀ ≫ (ι ≫ 𝒜.f))).1 := by
      rw [← 𝒜.L.one_natural (ι ≫ 𝒜.f) _ P₀ rfl]; rfl
    rw [c1, c2, hU, c3, E3Aux.one_val_congr 𝒜.L hb]

  have slot_rank : ∀ s : ↥(Spec (CommRingCat.of ↥O)), (ι ≫ 𝒜.f).finrank s = ℓ ^ 2 := by
    haveI := hfinK; haveI := hflatK; haveI := hlfpK; haveI := hcl
    haveI := K.levK_flat; haveI := K.levK_finite; haveI := K.levK_closed
    let ι₀ := Spec.map (CommRingCat.ofHom O.subtype)

    obtain ⟨u₀, hu₀⟩ := (hgen (K.levK ≫ E.f) ⟨K.levK, rfl⟩).1 ⟨𝟙 _, Category.id_comp _⟩
    have hu_cond : u₀ ≫ (ι ≫ 𝒜.f) = (K.levK ≫ E.f) ≫ ι₀ := by
      rw [← Category.assoc, hu₀, Category.assoc, hgE.w, Category.assoc]
    let u : K.K ⟶ pullback (ι ≫ 𝒜.f) ι₀ := pullback.lift u₀ (K.levK ≫ E.f) hu_cond
    have hu_fst : u ≫ pullback.fst (ι ≫ 𝒜.f) ι₀ = u₀ := pullback.lift_fst _ _ _
    have hu_snd : u ≫ pullback.snd (ι ≫ 𝒜.f) ι₀ = K.levK ≫ E.f := pullback.lift_snd _ _ _

    have hq : (pullback.fst (ι ≫ 𝒜.f) ι₀ ≫ ι) ≫ 𝒜.f = pullback.snd (ι ≫ 𝒜.f) ι₀ ≫ ι₀ := by
      rw [Category.assoc]; exact pullback.condition
    let q₁ : pullback (ι ≫ 𝒜.f) ι₀ ⟶ E.A := hgE.lift (pullback.fst (ι ≫ 𝒜.f) ι₀ ≫ ι) (pullback.snd (ι ≫ 𝒜.f) ι₀) hq
    have hq₁g : q₁ ≫ gE = pullback.fst (ι ≫ 𝒜.f) ι₀ ≫ ι := hgE.lift_fst _ _ _
    have hq₁f : q₁ ≫ E.f = pullback.snd (ι ≫ 𝒜.f) ι₀ := hgE.lift_snd _ _ _
    obtain ⟨v, hv⟩ := (hgen (pullback.snd (ι ≫ 𝒜.f) ι₀) ⟨q₁, hq₁f⟩).2 ⟨pullback.fst (ι ≫ 𝒜.f) ι₀, hq₁g.symm⟩
    have huq : u ≫ q₁ = K.levK := by
      apply hgE.hom_ext
      · rw [Category.assoc, hq₁g, ← Category.assoc, hu_fst, hu₀]
      · rw [Category.assoc, hq₁f, hu_snd]
    have huv : u ≫ v = 𝟙 _ := by
      rw [← cancel_mono K.levK, Category.assoc, hv, huq, Category.id_comp]
    have hvu : v ≫ u = 𝟙 _ := by
      apply pullback.hom_ext
      · rw [Category.assoc, hu_fst, Category.id_comp, ← cancel_mono ι, Category.assoc, hu₀, ← Category.assoc, hv, hq₁g]
      · rw [Category.assoc, hu_snd, Category.id_comp, ← Category.assoc, hv, hq₁f]
    haveI : IsIso u := ⟨⟨v, huv, hvu⟩⟩
    let pt : ↥(Spec (CommRingCat.of (AlgebraicClosure ℚ))) := ⟨⊥, Ideal.bot_prime⟩
    have h1 : (pullback.snd (ι ≫ 𝒜.f) ι₀).finrank pt = (ι ≫ 𝒜.f).finrank (ι₀ pt) :=
      Scheme.Hom.finrank_of_isPullback _ _ _ _ (IsPullback.of_hasPullback _ _) pt
    have h2 : (pullback.snd (ι ≫ 𝒜.f) ι₀).finrank pt = ℓ ^ 2 := by
      have h3 := Scheme.Hom.finrank_comp_left_of_isIso u (pullback.snd (ι ≫ 𝒜.f) ι₀)
      rw [hu_snd] at h3
      rw [← congrFun h3 pt]
      exact K.levK_rank pt
    have hlc := (ι ≫ 𝒜.f).isLocallyConstant_finrank
    haveI : PreconnectedSpace ↥(Spec (CommRingCat.of ↥O)) :=
      inferInstanceAs (PreconnectedSpace (PrimeSpectrum ↥O))
    intro s
    rw [congrFun (hlc.eq_const (ι₀ pt)) s]
    show (ι ≫ 𝒜.f).finrank (ι₀ pt) = ℓ ^ 2
    rw [← h1, h2]

  have hsub : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of ↥O)) (P Q : SchemeHomOver t 𝒜.f),
      FactorsThrough ι P → FactorsThrough ι Q →
        FactorsThrough ι (𝒜.L.mul t P Q) ∧ FactorsThrough ι (𝒜.L.inv t P) := by
    intro T t P Q hP hQ
    rw [hkerT] at hP hQ
    refine ⟨(hkerT t _).2 ?_, (hkerT t _).2 ?_⟩
    · rw [hΦ_mul, hP, hQ, 𝒟.L.one_mul]
    · rw [hΦinv, hP, E3Aux.inv_one]
  have hone : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of ↥O)), FactorsThrough ι (𝒜.L.one t) :=
    fun t => (hkerT t _).2 (hΦone t)
  have hstable : ∀ (x : ↥Λ) {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of ↥O)) (P : SchemeHomOver t 𝒜.f),
      FactorsThrough ι P → FactorsThrough ι (pushPt (𝒜.act x) (𝒜.act_over x) P) := by
    intro x T t P hP
    rw [hkerT] at hP ⊢
    have : mapPt Φ hΦ (pushPt (𝒜.act x) (𝒜.act_over x) P) = pushPt (𝒟.act x) (𝒟.act_over x) (mapPt Φ hΦ P) := by
      apply Subtype.ext
      show (P.1 ≫ 𝒜.act x) ≫ Φ = (P.1 ≫ Φ) ≫ 𝒟.act x
      rw [Category.assoc, hΦ_act, Category.assoc]
    rw [this, hP, hact_one]
  have hdisj : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of ↥O)) (P : SchemeHomOver t 𝒜.f),
      FactorsThrough ι P → FactorsThrough 𝒜.lev P → P = 𝒜.L.one t := by
    intro T t P hK hL
    have h1 := slot_torsion t P hK
    have h2 := 𝒜.lev_torsion t P hL
    rw [E3Aux.nsmulPt_eq_pow] at h1 h2
    letI := 𝒜.L.pointGroup t
    have h3 : P ^ Nat.gcd ℓ N = 1 := pow_gcd_eq_one.mpr ⟨h1, h2⟩
    rwa [hℓN, pow_one] at h3
  have slot_fibre := fun (k : Type) [Field k] [IsAlgClosed k] (sk : ↥O →+* k) (hk : (ℓ : k) ≠ 0) =>
    (by
      haveI := hcl; haveI := hfinK; haveI := hflatK; haveI := hlfpK
      exact CerednikDrinfeld.QM.FakeEllipticCurve.exists_zmod_prod_equiv_factorsThrough_of_isPullback_valuationSubring
        O ℓ 𝒜 E gE hgE hgE_mul K ι slot_rank hsub hone slot_torsion hgen k sk hk :
      ∃ e : ZMod ℓ × ZMod ℓ ≃ {P : SchemeHomOver (geomPoint k sk) 𝒜.f // FactorsThrough ι P},
        ∀ x y : ZMod ℓ × ZMod ℓ, (e (x + y) : SchemeHomOver (geomPoint k sk) 𝒜.f) =
          𝒜.L.mul (geomPoint k sk) (e x) (e y))
  let 𝒦 : 𝒜.ExtraLevel ℓ :=
    { K := Kk, levK := ι, levK_closed := hcl,
      levK_sub := hsub, levK_one := hone, levK_torsion := slot_torsion, levK_stable := hstable,
      levK_disjoint := hdisj,
      levK_finite := hfinK, levK_flat := hflatK, levK_finitePresentation := hlfpK,
      levK_rank := slot_rank, levK_fibre := slot_fibre }
  exact ⟨𝒦, hgen, fun t P => (hkerT t P).symm⟩

end S_CerednikDrinfeld_QM_FakeEllipticCurve_exists_extraLevel_ker_of_isPullback_valuationSubring_of_comp_eq_act_of_one_mem
end P2MW
export P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_exists_extraLevel_ker_of_isPullback_valuationSubring_of_comp_eq_act_of_one_mem (solution)
