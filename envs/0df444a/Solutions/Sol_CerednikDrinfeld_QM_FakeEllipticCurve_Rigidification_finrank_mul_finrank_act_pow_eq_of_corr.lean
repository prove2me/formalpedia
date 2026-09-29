-- Prove2me | solution 1 for CerednikDrinfeld.QM.FakeEllipticCurve.Rigidification.finrank_mul_finrank_act_pow_eq_of_corr
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.837917+00:00
-- url     : https://prove2.me/submissions/1636f804-8ad6-5232-97ef-a249883bb4ec

import Definitions.Def_CerednikDrinfeld_QMRigidification
import Theorems.Thm_AlgebraicGeometry_Scheme_Hom_finrank_comp_of_finrank_eq_const
import Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_isFinite_flat_surjective_of_isIsogenyPair
import Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_isLocallyConstant_finrank_one
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_Rigidification_finrank_mul_finrank_act_pow_eq_of_corr
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

open scoped TensorProduct Quaternion NumberField
p2m_open "CategoryTheory AlgebraicGeometry QuaternionAlgebra CerednikDrinfeld P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_Rigidification_finrank_mul_finrank_act_pow_eq_of_corr.CerednikDrinfeld CerednikDrinfeld.QM P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_Rigidification_finrank_mul_finrank_act_pow_eq_of_corr.CerednikDrinfeld.QM NeronModelInfra GoodReductionJacobian"

namespace CerednikDrinfeld
p2m_export "CerednikDrinfeld" "QM.FakeEllipticCurve.Rigidification QM.FakeEllipticCurve"
namespace QM
p2m_export "CerednikDrinfeld.QM" "FakeEllipticCurve.Rigidification FakeEllipticCurve FakeEllipticCurve.IsIsogenyPair FakeEllipticCurve.IsPullbackVia FakeEllipticCurve.isFinite_flat_surjective_of_isIsogenyPair FakeEllipticCurve.isLocallyConstant_finrank_one"
namespace FakeEllipticCurve
p2m_export "CerednikDrinfeld.QM.FakeEllipticCurve" "Rigidification IsPullback A f mk act_hom act act_one L act_mul act_over IsIsogenyPair IsPullbackVia isFinite_flat_surjective_of_isIsogenyPair isLocallyConstant_finrank_one"
namespace Rigidification
p2m_export "CerednikDrinfeld.QM.FakeEllipticCurve.Rigidification" "IsPullbackVia φ' isIsogenyPair mk Eb d Ab φ isPullback_Eb gA φ_over gb"
namespace W7Aux
p2m_open "CerednikDrinfeld.QM.FakeEllipticCurve.Rigidification CerednikDrinfeld.QM.FakeEllipticCurve CerednikDrinfeld.QM CerednikDrinfeld"

universe u

theorem finrank_morphismRestrict {X Y : Scheme.{u}} (f : X ⟶ Y) [IsFinite f] [Flat f] (U : Y.Opens) (y : ↥U) :
    (f ∣_ U).finrank y = f.finrank y.1 := by
  rw [Scheme.Hom.finrank_of_isPullback _ _ _ _ (isPullback_morphismRestrict f U).flip y]
  rfl

theorem finrank_comp_of_finrank_eq_on {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    [IsFinite f] [Flat f] [IsFinite g] [Flat g]
    (W : Z.Opens) (m : ℕ) (hf : ∀ y : ↥Y, g.base y ∈ W → f.finrank y = m) (z : ↥Z) (hz : z ∈ W) :
    (f ≫ g).finrank z = m * g.finrank z := by
  have sq : CategoryTheory.IsPullback (f ⁻¹ᵁ (g ⁻¹ᵁ W)).ι (f ∣_ (g ⁻¹ᵁ W) ≫ g ∣_ W) (f ≫ g) W.ι :=
    (isPullback_morphismRestrict f (g ⁻¹ᵁ W)).flip.paste_vert (isPullback_morphismRestrict g W).flip
  have h3 : ∀ v : ↥(g ⁻¹ᵁ W), (f ∣_ (g ⁻¹ᵁ W)).finrank v = m := fun v =>
    (finrank_morphismRestrict f _ v).trans (hf _ v.2)
  have key := Scheme.Hom.finrank_comp_of_finrank_eq_const (f ∣_ (g ⁻¹ᵁ W)) (g ∣_ W) m h3 ⟨z, hz⟩
  rw [Scheme.Hom.finrank_of_isPullback _ _ _ _ sq, finrank_morphismRestrict] at key
  exact key

theorem isIso_of_isPullback_of_isIso {P X Y Z : Scheme.{u}} (fst : P ⟶ X) (snd : P ⟶ Y) (f : X ⟶ Z) (g : Y ⟶ Z)
    (h : CategoryTheory.IsPullback fst snd f g) [IsIso g] : IsIso fst := by
  refine ⟨⟨h.lift (𝟙 X) (f ≫ inv g) (by simp), ?_, by simp⟩⟩
  apply h.hom_ext
  · simp
  · simp only [Category.assoc, IsPullback.lift_snd, Category.id_comp]
    rw [← cancel_mono g, Category.assoc, Category.assoc, IsIso.inv_hom_id, Category.comp_id, h.w]

variable {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} {N : ℕ} {S : Type} [CommRing S]

theorem act_rpow_zero (hΛℤ : ∀ m : ℤ, ((m : ℚ) : ℍ[ℚ, a, b]) ∈ Λ) (A : FakeEllipticCurve Λ N S) (r : ℕ) :
    A.act ⟨(((r ^ 0 : ℕ) : ℤ) : ℚ), hΛℤ _⟩ = 𝟙 A.A := by
  have h1 : (1 : ℍ[ℚ, a, b]) ∈ Λ := by exact_mod_cast hΛℤ 1
  rw [← A.act_one h1]
  congr 1 <;> first | rfl | exact Subtype.ext (by push_cast; norm_num)

theorem act_rpow_succ (hΛℤ : ∀ m : ℤ, ((m : ℚ) : ℍ[ℚ, a, b]) ∈ Λ) (A : FakeEllipticCurve Λ N S) (r k : ℕ) :
    A.act ⟨(((r ^ (k + 1) : ℕ) : ℤ) : ℚ), hΛℤ _⟩ =
      A.act ⟨(((r ^ k : ℕ) : ℤ) : ℚ), hΛℤ _⟩ ≫ A.act ⟨(((r ^ 1 : ℕ) : ℤ) : ℚ), hΛℤ _⟩ := by
  have hmem : ((((r ^ 1 : ℕ) : ℤ) : ℚ) : ℍ[ℚ, a, b]) * ((((r ^ k : ℕ) : ℤ) : ℚ) : ℍ[ℚ, a, b]) ∈ Λ := by
    rw [← coe_mul]; exact_mod_cast hΛℤ ((r ^ 1 : ℕ) * (r ^ k : ℕ) : ℕ)
  rw [← A.act_mul ⟨_, hΛℤ _⟩ ⟨_, hΛℤ _⟩ hmem]
  congr 1
  apply Subtype.ext
  show ((((r ^ (k + 1) : ℕ) : ℤ) : ℚ) : ℍ[ℚ, a, b]) = (((r ^ 1 : ℕ) : ℤ) : ℚ) * ((((r ^ k : ℕ) : ℤ) : ℚ) : ℍ[ℚ, a, b])
  rw [← coe_mul]
  congr 1
  push_cast
  ring

theorem act_comm_act_rpow (hΛℤ : ∀ m : ℤ, ((m : ℚ) : ℍ[ℚ, a, b]) ∈ Λ) (A : FakeEllipticCurve Λ N S) (r k : ℕ) (x : ↥Λ) :
    A.act x ≫ A.act ⟨(((r ^ k : ℕ) : ℤ) : ℚ), hΛℤ _⟩ = A.act ⟨(((r ^ k : ℕ) : ℤ) : ℚ), hΛℤ _⟩ ≫ A.act x := by
  have hmem : ((((r ^ k : ℕ) : ℤ) : ℚ) : ℍ[ℚ, a, b]) * (x : ℍ[ℚ, a, b]) ∈ Λ := by
    rw [coe_mul_eq_smul, Int.cast_smul_eq_zsmul]
    exact Λ.smul_mem _ x.2
  have hmem' : (x : ℍ[ℚ, a, b]) * ((((r ^ k : ℕ) : ℤ) : ℚ) : ℍ[ℚ, a, b]) ∈ Λ := by
    rw [← coe_commutes]; exact hmem
  rw [← A.act_mul _ _ hmem, ← A.act_mul _ _ hmem']
  congr 1
  exact Subtype.ext (coe_commutes _ _)

theorem isIsogenyPair_act_rpow (hΛℤ : ∀ m : ℤ, ((m : ℚ) : ℍ[ℚ, a, b]) ∈ Λ) (A : FakeEllipticCurve Λ N S) (r k : ℕ) :
    FakeEllipticCurve.IsIsogenyPair (r ^ (2 * k)) A A
      (A.act ⟨(((r ^ k : ℕ) : ℤ) : ℚ), hΛℤ _⟩) (A.act ⟨(((r ^ k : ℕ) : ℤ) : ℚ), hΛℤ _⟩) := by
  refine ⟨A.act_over _, A.act_over _, fun t P Q => A.act_hom _ t P Q, fun t P Q => A.act_hom _ t P Q,
    fun x => act_comm_act_rpow hΛℤ A r k x, fun x => act_comm_act_rpow hΛℤ A r k x, fun hd => ?_⟩
  have hmem : ((((r ^ k : ℕ) : ℤ) : ℚ) : ℍ[ℚ, a, b]) * ((((r ^ k : ℕ) : ℤ) : ℚ) : ℍ[ℚ, a, b]) ∈ Λ := by
    rw [← coe_mul]; exact_mod_cast hΛℤ ((r ^ k : ℕ) * (r ^ k : ℕ) : ℕ)
  have heq : A.act ⟨(((r ^ k : ℕ) : ℤ) : ℚ), hΛℤ _⟩ ≫ A.act ⟨(((r ^ k : ℕ) : ℤ) : ℚ), hΛℤ _⟩ =
      A.act ⟨((r ^ (2 * k) : ℕ) : ℚ), hd⟩ := by
    rw [← A.act_mul _ _ hmem]
    congr 1
    apply Subtype.ext
    show (((r ^ k : ℕ) : ℤ) : ℚ) * ((((r ^ k : ℕ) : ℤ) : ℚ) : ℍ[ℚ, a, b]) = (((r ^ (2 * k) : ℕ) : ℚ) : ℍ[ℚ, a, b])
    rw [← coe_mul]
    congr 1
    push_cast
    ring
  exact ⟨heq, heq⟩

end CerednikDrinfeld.QM.FakeEllipticCurve.Rigidification.W7Aux

theorem solution
    {r N : ℕ} [Fact r.Prime] (𝒪 : Type) [CommRing 𝒪] (π : 𝒪) (Onr : Type) [CommRing Onr] [Algebra 𝒪 Onr]
    {a b : ℚ} (Λ : Submodule ℤ ℍ[ℚ, a, b]) (hΛℤ : ∀ m : ℤ, ((m : ℚ) : ℍ[ℚ, a, b]) ∈ Λ)
    (A₀ : FakeEllipticCurve Λ N (Onr ⧸ Ideal.span {algebraMap 𝒪 Onr π}))

    (L : Type) [CommRing L] [Algebra 𝒪 L] (ψL : Onr →ₐ[𝒪] L) (E E' : FakeEllipticCurve Λ N L)
    (ϱ : FakeEllipticCurve.Rigidification r π A₀ ψL E) (ϱ' : FakeEllipticCurve.Rigidification r π A₀ ψL E')

    (i₀ : E.A ≅ E'.A) (hi : i₀.hom ≫ E'.f = E.f)
    (ib : ϱ.Eb.A ⟶ ϱ'.Eb.A) (hib : ib ≫ ϱ'.gb = ϱ.gb ≫ i₀.hom) (hibf : ib ≫ ϱ'.Eb.f = ϱ.Eb.f)
    (uA : ϱ'.Ab.A ⟶ ϱ.Ab.A) (huA : FakeEllipticCurve.IsPullbackVia (RingHom.id _) ϱ.Ab ϱ'.Ab uA) (huAg : uA ≫ ϱ.gA = ϱ'.gA)
    (i₁ j₁ : ℕ)
    (hrel : ib ≫ ϱ'.φ ≫ uA ≫ ϱ.Ab.act ⟨(((r ^ i₁ : ℕ) : ℤ) : ℚ), hΛℤ _⟩ = ϱ.φ ≫ ϱ.Ab.act ⟨(((r ^ j₁ : ℕ) : ℤ) : ℚ), hΛℤ _⟩)
    (y' : ↥ϱ'.Ab.A) :
    ϱ'.φ.finrank y' * ((ϱ.Ab.act ⟨(((r ^ 1 : ℕ) : ℤ) : ℚ), hΛℤ _⟩).finrank (uA.base y')) ^ i₁ =
      ϱ.φ.finrank (uA.base y') * ((ϱ.Ab.act ⟨(((r ^ 1 : ℕ) : ℤ) : ℚ), hΛℤ _⟩).finrank (uA.base y')) ^ j₁ := by
  classical

  obtain ⟨hφfin, hφfl, hφlfp, -⟩ := FakeEllipticCurve.isFinite_flat_surjective_of_isIsogenyPair hΛℤ r ϱ.d _
    ϱ.Eb ϱ.Ab ϱ.φ ϱ.φ' ϱ.isIsogenyPair
  obtain ⟨hφ'fin, hφ'fl, hφ'lfp, -⟩ := FakeEllipticCurve.isFinite_flat_surjective_of_isIsogenyPair hΛℤ r ϱ'.d _
    ϱ'.Eb ϱ'.Ab ϱ'.φ ϱ'.φ' ϱ'.isIsogenyPair
  have hr : ∀ k : ℕ, IsFinite (ϱ.Ab.act ⟨(((r ^ k : ℕ) : ℤ) : ℚ), hΛℤ _⟩) ∧ Flat (ϱ.Ab.act ⟨(((r ^ k : ℕ) : ℤ) : ℚ), hΛℤ _⟩) ∧
      LocallyOfFinitePresentation (ϱ.Ab.act ⟨(((r ^ k : ℕ) : ℤ) : ℚ), hΛℤ _⟩) := fun k =>
    let h := FakeEllipticCurve.isFinite_flat_surjective_of_isIsogenyPair hΛℤ r (2 * k) _ ϱ.Ab ϱ.Ab _ _
      (FakeEllipticCurve.Rigidification.W7Aux.isIsogenyPair_act_rpow hΛℤ ϱ.Ab r k)
    ⟨h.1, h.2.1, h.2.2.1⟩
  haveI := (hr 1).1; haveI := (hr 1).2.1; haveI := (hr 1).2.2

  obtain ⟨hφ1, hφ2⟩ := FakeEllipticCurve.isLocallyConstant_finrank_one _ ϱ.Eb ϱ.Ab ϱ.φ ϱ.φ_over
  obtain ⟨hφ'1, hφ'2⟩ := FakeEllipticCurve.isLocallyConstant_finrank_one _ ϱ'.Eb ϱ'.Ab ϱ'.φ ϱ'.φ_over
  obtain ⟨hc1, hc2⟩ := FakeEllipticCurve.isLocallyConstant_finrank_one _ ϱ.Ab ϱ.Ab
    (ϱ.Ab.act ⟨(((r ^ 1 : ℕ) : ℤ) : ℚ), hΛℤ _⟩) (ϱ.Ab.act_over _)
  obtain ⟨nφ, hnφ⟩ : ∃ n : ↥(Spec (CommRingCat.of (L ⧸ Ideal.span {algebraMap 𝒪 L π}))) → ℕ,
      n = fun t => ϱ.φ.finrank ((ϱ.Ab.L.one (𝟙 (Spec (CommRingCat.of (L ⧸ Ideal.span {algebraMap 𝒪 L π}))))).1.base t) := ⟨_, rfl⟩
  obtain ⟨nφ', hnφ'⟩ : ∃ n : ↥(Spec (CommRingCat.of (L ⧸ Ideal.span {algebraMap 𝒪 L π}))) → ℕ,
      n = fun t => ϱ'.φ.finrank ((ϱ'.Ab.L.one (𝟙 (Spec (CommRingCat.of (L ⧸ Ideal.span {algebraMap 𝒪 L π}))))).1.base t) := ⟨_, rfl⟩
  obtain ⟨nc, hnc⟩ : ∃ n : ↥(Spec (CommRingCat.of (L ⧸ Ideal.span {algebraMap 𝒪 L π}))) → ℕ,
      n = fun t => (ϱ.Ab.act ⟨(((r ^ 1 : ℕ) : ℤ) : ℚ), hΛℤ _⟩).finrank
        ((ϱ.Ab.L.one (𝟙 (Spec (CommRingCat.of (L ⧸ Ideal.span {algebraMap 𝒪 L π}))))).1.base t) := ⟨_, rfl⟩
  rw [← hnφ] at hφ2; rw [← hnφ'] at hφ'2; rw [← hnc] at hc2
  have eφ : ∀ z, ϱ.φ.finrank z = nφ (ϱ.Ab.f.base z) := fun z => by rw [hnφ]; exact hφ1 z
  have eφ' : ∀ z, ϱ'.φ.finrank z = nφ' (ϱ'.Ab.f.base z) := fun z => by rw [hnφ']; exact hφ'1 z
  have ec : ∀ z, (ϱ.Ab.act ⟨(((r ^ 1 : ℕ) : ℤ) : ℚ), hΛℤ _⟩).finrank z = nc (ϱ.Ab.f.base z) := fun z => by
    rw [hnc]; exact hc1 z
  clear hφ1 hφ'1 hc1

  obtain ⟨sq, -, hΛuA, -⟩ := huA
  have hbase : ∀ w : ↥ϱ'.Ab.A, ϱ.Ab.f.base (uA.base w) = ϱ'.Ab.f.base w := fun w => by
    have hw := sq.w
    rw [CommRingCat.ofHom_id, Spec.map_id, Category.comp_id] at hw
    have hw2 := congrArg (fun h => h.base w) hw
    simpa using hw2
  have hact : ∀ (x : ↥Λ) (z : ↥ϱ.Ab.A), ϱ.Ab.f.base ((ϱ.Ab.act x).base z) = ϱ.Ab.f.base z := fun x z => by
    have h2 := congrArg (fun h => h.base z) (ϱ.Ab.act_over x)
    simpa using h2
  obtain ⟨s, hs⟩ : ∃ s, s = ϱ'.Ab.f.base y' := ⟨_, rfl⟩
  let U : (Spec (CommRingCat.of (L ⧸ Ideal.span {algebraMap 𝒪 L π}))).Opens :=
    ⟨nφ ⁻¹' {nφ s} ∩ (nφ' ⁻¹' {nφ' s} ∩ nc ⁻¹' {nc s}), (hφ2 _).inter ((hφ'2 _).inter (hc2 _))⟩
  have hyU : ϱ.Ab.f.base (uA.base y') ∈ U := by
    rw [hbase, ← hs]; exact ⟨rfl, rfl, rfl⟩
  have hyW : uA.base y' ∈ ϱ.Ab.f ⁻¹ᵁ U := hyU

  have hpow : ∀ (j : ℕ) (z : ↥ϱ.Ab.A), ϱ.Ab.f.base z ∈ U →
      (ϱ.Ab.act ⟨(((r ^ j : ℕ) : ℤ) : ℚ), hΛℤ _⟩).finrank z = nc s ^ j := by
    intro j
    induction j with
    | zero =>
      intro z _
      rw [FakeEllipticCurve.Rigidification.W7Aux.act_rpow_zero hΛℤ ϱ.Ab r, Scheme.Hom.finrank_eq_one_of_isIso, pow_zero]
      rfl
    | succ j ih =>
      intro z hz
      haveI := (hr j).1; haveI := (hr j).2.1
      rw [FakeEllipticCurve.Rigidification.W7Aux.act_rpow_succ hΛℤ ϱ.Ab r j,
        FakeEllipticCurve.Rigidification.W7Aux.finrank_comp_of_finrank_eq_on _ _ (ϱ.Ab.f ⁻¹ᵁ U) (nc s ^ j) ?_ z hz, ec z, pow_succ (nc s) j]
      · have h3 : nc (ϱ.Ab.f.base z) = nc s := hz.2.2
        rw [h3]
      · intro w hw
        apply ih
        have hw' : ϱ.Ab.f.base ((ϱ.Ab.act ⟨(((r ^ 1 : ℕ) : ℤ) : ℚ), hΛℤ _⟩).base w) ∈ U := hw
        rwa [hact] at hw'

  have hR : (ϱ.φ ≫ ϱ.Ab.act ⟨(((r ^ j₁ : ℕ) : ℤ) : ℚ), hΛℤ _⟩).finrank (uA.base y') = nφ s * nc s ^ j₁ := by
    haveI := (hr j₁).1; haveI := (hr j₁).2.1
    rw [FakeEllipticCurve.Rigidification.W7Aux.finrank_comp_of_finrank_eq_on _ _ (ϱ.Ab.f ⁻¹ᵁ U) (nφ s) ?_ _ hyW, hpow j₁ _ hyU]
    intro w hw
    have hw' : ϱ.Ab.f.base ((ϱ.Ab.act ⟨(((r ^ j₁ : ℕ) : ℤ) : ℚ), hΛℤ _⟩).base w) ∈ U := hw
    rw [hact] at hw'
    rw [eφ w]
    exact hw'.1

  have huAiso : IsIso uA := by
    have : IsIso (Spec.map (CommRingCat.ofHom (RingHom.id (L ⧸ Ideal.span {algebraMap 𝒪 L π})))) := by
      rw [CommRingCat.ofHom_id, Spec.map_id]; infer_instance
    exact FakeEllipticCurve.Rigidification.W7Aux.isIso_of_isPullback_of_isIso _ _ _ _ sq
  have hib : IsIso ib := by
    obtain ⟨sqb, -⟩ := ϱ.isPullback_Eb
    obtain ⟨sqb', -⟩ := ϱ'.isPullback_Eb
    have w1 : (ϱ'.gb ≫ i₀.inv) ≫ E.f =
        ϱ'.Eb.f ≫ Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (Ideal.span {algebraMap 𝒪 L π}))) := by
      rw [Category.assoc, ← hi, i₀.inv_hom_id_assoc, sqb'.w]
    refine ⟨⟨sqb.lift (ϱ'.gb ≫ i₀.inv) ϱ'.Eb.f w1, ?_, ?_⟩⟩
    · apply sqb.hom_ext
      · rw [Category.assoc, sqb.lift_fst, ← Category.assoc, hib, Category.assoc, i₀.hom_inv_id,
          Category.comp_id, Category.id_comp]
      · rw [Category.assoc, sqb.lift_snd, hibf, Category.id_comp]
    · apply sqb'.hom_ext
      · rw [Category.assoc, hib, ← Category.assoc, sqb.lift_fst, Category.assoc, i₀.inv_hom_id,
          Category.comp_id, Category.id_comp]
      · rw [Category.assoc, hibf, sqb.lift_snd, Category.id_comp]

  have hL : (ib ≫ ϱ'.φ ≫ uA ≫ ϱ.Ab.act ⟨(((r ^ i₁ : ℕ) : ℤ) : ℚ), hΛℤ _⟩).finrank (uA.base y') = nφ' s * nc s ^ i₁ := by
    haveI := (hr i₁).1; haveI := (hr i₁).2.1
    rw [Scheme.Hom.finrank_comp_left_of_isIso,
      FakeEllipticCurve.Rigidification.W7Aux.finrank_comp_of_finrank_eq_on ϱ'.φ _ (ϱ.Ab.f ⁻¹ᵁ U) (nφ' s) ?_ _ hyW,
      Scheme.Hom.finrank_comp_left_of_isIso, hpow i₁ _ hyU]
    intro w' hw'
    have hw'' : ϱ.Ab.f.base ((uA ≫ ϱ.Ab.act ⟨(((r ^ i₁ : ℕ) : ℤ) : ℚ), hΛℤ _⟩).base w') ∈ U := hw'
    change ϱ.Ab.f.base ((ϱ.Ab.act ⟨(((r ^ i₁ : ℕ) : ℤ) : ℚ), hΛℤ _⟩).base (uA.base w')) ∈ U at hw''
    rw [hact, hbase] at hw''
    rw [eφ' w']
    exact hw''.2.1

  have key := congrArg (fun h => Scheme.Hom.finrank h (uA.base y')) hrel
  simp only at key
  rw [hL, hR] at key
  rw [eφ' y', eφ (uA.base y'), ec (uA.base y'), hbase, ← hs]
  have h3 : nc s = nc s ^ 1 := (pow_one _).symm
  exact key

end S_CerednikDrinfeld_QM_FakeEllipticCurve_Rigidification_finrank_mul_finrank_act_pow_eq_of_corr
end P2MW
export P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_Rigidification_finrank_mul_finrank_act_pow_eq_of_corr (solution)
