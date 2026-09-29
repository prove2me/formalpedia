-- Prove2me | solution 1 for CerednikDrinfeld.QM.FakeEllipticCurve.WithExtraLevel.exists_flip_of_not_dvd
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.837917+00:00
-- url     : https://prove2.me/submissions/8bf58f13-905b-5dc4-a464-963a0e51d092

import Definitions.Def_CerednikDrinfeld_QMModuliProps
import Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_exists_quotient_core_of_isAlgClosed
import Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_exists_extraLevel_isLevelIsogeny_of_finrank_kernel_eq
import Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_isFinite_and_finrank_kernel_eq_of_comp_eq_nsmulPt_of_finrank_eq
import Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_exists_zmod_prod_equiv_factorsThrough_kernel_dual_of_not_dvd
import Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_isIso_of_forall_mapPt_eq_one_imp_eq_one
import Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_factorsThrough_lev_iff_exists_mapPt_eq_of_coprime
import Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_pushPt_act_natCast_eq_nsmulPt
import Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_nsmul_surjective_of_isAlgClosed_of_connectedSpace
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_WithExtraLevel_exists_flip_of_not_dvd
p2m_attr_erase "instance" "GoodReductionJacobian.RelativeGroupLaw.isIso_endKerStr_schemeHomOverId AlgebraicGeometry.Scheme.PresheafOfModules.symmetricCategory SheafOfModules.instFaithfulRingSheafPModToPMod SheafOfModules.symmetricCategory AlgebraicGeometry.Scheme.PresheafOfModules.monoidalCategory AlgebraicGeometry.Scheme.PresheafOfModules.monoidalClosed SheafOfModules.instFullRingSheafPModToPMod SheafOfModules.monoidalCategory AlgebraicGeometry.Scheme.Modules.symmetricCategory SheafOfModules.monoidalClosed SheafOfModules.instIsLocalizationPModRingSheafSheafifyFunctorPresheafW SheafOfModules.sheafifyFunctor_monoidal AlgebraicGeometry.Scheme.Modules.monoidalClosed AlgebraicGeometry.instMonoidalPresheafOfModulesModulesSheafify AlgebraicGeometry.Scheme.Modules.monoidalCategory PresheafOfModules.instMonoidalClosed PresheafOfModules.InternalHom.instModuleCarrierObjOppositeCommRingCatSubtypePiFamilyMemAddSubgroupNaturalFamilies PresheafOfModules.InternalHom.instModuleCarrierObjOppositeRingCatCompCommRingCatForget₂RingHomCarrierCarrierAbPresheaf PresheafOfModules.InternalHom.instSMulCarrierObjOppositeCommRingCatSubtypePiFamilyMemAddSubgroupNaturalFamilies AlgebraicGeometry.Scheme.Hom.opensMapFinal AlgebraicGeometry.RelPicard.RigidifiedLineBundle.setoid AlgebraicGeometry.RelPicard.RigidifiedLineBundle.instInhabited AlgebraicGeometry.OModulePresheaf.isScalarTower AlgebraicGeometry.Scheme.OrderedAffineCover.instLinearOrder AlgebraicGeometry.OModulePresheaf.module AlgebraicGeometry.Scheme.OrderedAffineCover.instFintype AlgebraicGeometry.Scheme.OrderedAffineCover.instFintypeIdx AlgebraicGeometry.OModulePresheaf.addCommGroup AlgebraicGeometry.Scheme.OrderedAffineCover.instDecidableEqIdx AlgebraicGeometry.OModulePresheaf.moduleSections TwoChartCech.Sections.M0_moduleA TwoChartCech.Sections.M1_module TwoChartCech.Cover.A01_algebra TwoChartCech.Cover.A0_algebra TwoChartCech.Cover.A1_commRing TwoChartCech.Cover.A1_algebra TwoChartCech.Sections.M01_module TwoChartCech.Sections.M0_addCommGroup TwoChartCech.Sections.M0_tower TwoChartCech.Sections.M01_addCommGroup"
p2m_attr_erase "instance" "TwoChartCech.Cover.A0_commRing TwoChartCech.Sections.M1_tower TwoChartCech.Sections.M01_moduleA TwoChartCech.Sections.M0_module TwoChartCech.Sections.M1_moduleA TwoChartCech.Sections.M1_addCommGroup TwoChartCech.Cover.A01_commRing TwoChartCech.Sections.M01_tower CoherentBaseChange.TwoTermComplex.C0_module CoherentBaseChange.TwoTermComplex.C0_addCommGroup CoherentBaseChange.TwoTermComplex.C1_module CoherentBaseChange.TwoTermComplex.C1_addCommGroup CoherentBaseChange.TwoTermComplex.C0_free CoherentBaseChange.TwoTermComplex.C1_finite CoherentBaseChange.TwoTermComplex.C0_finite CoherentBaseChange.TwoTermComplex.C1_free AlgebraicGeometry.OModulePresheaf.instSubsingletonObjZero AlgebraicGeometry.Scheme.Modules.preservesBinaryProducts_opensMap AlgebraicGeometry.Scheme.Modules.pullback_monoidal AlgebraicGeometry.Scheme.Modules.sheafify_isLocalization' AlgebraicGeometry.Scheme.Modules.preservesTerminal_opensMap AlgebraicGeometry.Scheme.Modules.pullback₀_monoidal AlgebraicGeometry.Scheme.Modules.preservesFiniteProducts_opensMap AlgebraicGeometry.Scheme.Modules.instLiftingPresheafOfModulesSheafifyPresheafWOpensCarrierCarrierCommRingCatGrothendieckTopologyObjFunctorOppositeIsSheafSheafCompPullback₀Pullback PresheafOfModules.PullbackMonoidal.pullback_monoidal PresheafOfModules.PullbackMonoidal.isIso_δ PresheafOfModules.pushforward_laxMonoidal PresheafOfModules.PullbackMonoidal.isIso_η PresheafOfModules.free_monoidal PresheafOfModules.restrictScalars_laxMonoidal PresheafOfModules.PullbackMonoidal.isIso_δ_gS PresheafOfModules.pullback_oplaxMonoidal PresheafOfModules.PullbackMonoidal.instPreservesColimitsOfSizeCompOppositeCommRingCatRingCatForget₂RingHomCarrierCarrierPb PresheafOfModules.pullback_monoidal' AlgebraicGeometry.SmoothOfRelativeDimension.fiberToSpecResidueField AlgebraicGeometry.SmoothOfRelativeDimension.pullback_snd AlgebraicGeometry.SmoothOfRelativeDimension.pullback_fst AlgebraicGeometry.SmoothOfRelativeDimension.smooth_one AlgebraicGeometry.SmoothProperCurve.isIntegral_pullback_Spec_field AlgebraicGeometry.IsProper.fiberToSpecResidueField"
p2m_attr_erase "instance" "AlgebraicCurve.CurveModel.isProper AlgebraicCurve.CurveModel.isIntegral AlgebraicCurve.CurveModel.smooth AlgebraicGeometry.Scheme.LocalRepresentabilityULift.instIsLocallyInjectiveFunUliftYonedaGluedToSheaf AlgebraicGeometry.Scheme.LocalRepresentabilityULift.instIsLocallySurjectiveFunUliftYonedaGluedToSheafOfIsLocallySurjectiveZariskiTopologyDescFunctorOppositeType AlgebraicGeometry.Scheme.LocalRepresentabilityULift.instIsOpenImmersionToGlued AlgebraicGeometry.Scheme.LocalRepresentabilityULift.instIsIsoSheafZariskiTopologyTypeUliftYonedaGluedToSheaf AlgebraicGeometry.RelPicard.instIsOpenImmersionToGlued AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.instFundamentalIdentityOfSumRamificationInertia AlgebraicCurve.Place.instIsScalarTowerResidueFieldRestrictPushforward AlgebraicCurve.Place.instAlgebraResidueFieldRestrictPushforward AlgebraicCurve.Place.instIsLocalHomRestrictInclusion AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions PresheafOfModules.ExteriorPower.instModulePresheafAb AlgebraicGeometry.RelEffCartierDiv.subsingleton_of_degree_zero AlgebraicGeometry.RelEffCartierDiv.isIso_subschemeIota_snd_of_degree_one AlgebraicGeometry.isIso_ker_graphOver_subschemeIota_snd AlgebraicGeometry.isClosedImmersion_graphOver AlgebraicGeometry.FGSubalgebra.instIsDirectedLe AlgebraicGeometry.FGSubalgebra.instQuasiSeparatedSpaceCarrierCarrierCommRingCatObjOppositeSchemeSpecDiagram AlgebraicGeometry.FGSubalgebra.instIsCofilteredOpposite AlgebraicGeometry.FGSubalgebra.instIsAffineObjOppositeSchemeSpecDiagram AlgebraicGeometry.FGSubalgebra.instNonempty AlgebraicGeometry.FGSubalgebra.instNonemptySubtypeLeSubalgebraValFG AlgebraicGeometry.FGSubalgebra.instCompactSpaceCarrierCarrierCommRingCatObjOppositeSchemeSpecDiagram AlgebraicGeometry.FGSubalgebra.instIsDirectedSubtypeLeSubalgebraValFG AlgebraicGeometry.FGSubalgebra.instIsAffineHomMapOppositeSchemeSpecDiagram AlgebraicGeometry.FGSubalgebra.instIsFiltered AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instNeg AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instSMulInt AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instAddCommGroup AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instAdd AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instSub"
p2m_attr_erase "instance" "AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instModuleCarrierObjOppositeOpensCarrierCarrierCommRingCatPresheafOpOpensTop AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instSMulCarrierObjOppositeOpensCarrierCarrierCommRingCatPresheafOpOpensTop AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instSMulNat AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instZero AlgebraicCurve.instHasLocalResidue_of_hasCanonicalLocalResidueK AlgebraicCurve.instHasCanonicalLocalResidueK_of_hasCanonicalLocalResidueKStar AlgebraicCurve.Place.kw_ffgc_finiteDimensional_adicCompletion instAlgebraSubtypeMemValuationSubring_definitions AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersIntegersCompletion ModularCurve.KwF4gRRTate.instAlgebraKAdicCompletionIntegers AlgebraicCurve.Place.kw_ffgc_continuousSMul_adicCompletionComap AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersCompletionCompletion IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions AlgebraicCurve.instHasCanonicalLocalResidueK AlgebraicCurve.Place.instAlgebra_restrictResidueField AlgebraicCurve.Place.instIsScalarTower_restrictResidueField AlgebraicCurve.instHasLocalResidue AlgebraicCurve.HasSeparableResidue.of_perfectField_of_isCurveOver AlgebraicCurve.HasSeparableResidue.of_perfectField AlgebraicCurve.Place.instIsLocalHom_restrictSubringHom AlgebraicCurve.instHasCanonicalLocalResidueKStar ModularCurve.KwNo6Pin.isLocalRing_completion SheafOfModules.isIso_ihomModelToIhom AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instDecidableEqIdx AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instFintype AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instLinearOrder AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instFintypeIdx AlgebraicGeometry.OModulePresheaf.Leray.relAltC_scalarTower AlgebraicGeometry.OModulePresheaf.Leray.ker_relAltd_modΓ AlgebraicGeometry.OModulePresheaf.Leray.relAltC_modΓ AlgebraicGeometry.OModulePresheaf.Leray.biC_abGrp AlgebraicGeometry.OModulePresheaf.Leray.relAltH_modΓ AlgebraicGeometry.OModulePresheaf.Leray.ker_relAltd_smul AlgebraicGeometry.OModulePresheaf.Leray.relAltH_scalarTower AlgebraicGeometry.OModulePresheaf.Leray.relAltH_smul"
p2m_attr_erase "instance" "AlgebraicGeometry.OModulePresheaf.Leray.biC_module DoubleComplex.instModuleE₂I DoubleComplex.Bounded.modR DoubleComplex.instModuleE₂II DoubleComplex.instAddCommGroupE₂II DoubleComplex.Bounded.abGrp DoubleComplex.instAddCommGroupE₂I AlgebraicGeometry.ChowDatum.hι_closed AlgebraicGeometry.ChowDatumProj.hιN_closed AlgebraicGeometry.ChowDatumProj.hp_proper AlgebraicGeometry.ChowDatum.hp_isoU AlgebraicGeometry.ChowDatum.hp_proper AlgebraicGeometry.ProjSpace.algebraAway AlgebraicGeometry.ProjSpace.instIsProperProdOverπ AlgebraicGeometry.ChowDatumProj.hp_isoU AlgebraicGeometry.ProjSpace.isProper_π AlgebraicGeometry.ProjSpace.finiteType_mvPolynomial ProjSpaceCech.GradedModule.H.module ProjSpaceCech.GradedModule.H.addCommGroup ProjSpaceCech.GradedModule.sec.instAdd ProjSpaceCech.GradedModule.sec.instNeg ProjSpaceCech.GradedModule.acg ProjSpaceCech.GradedModule.Frac.setoid ProjSpaceCech.GradedModule.modR ProjSpaceCech.GradedModule.sec.instModule ProjSpaceCech.GradedModule.sec.instAddCommGroup ProjSpaceCech.GradedModule.sec.instZero ProjSpaceCech.GradedModule.Presentation.fJ ProjSpaceCech.GradedModule.sec.instSMul ProjSpaceCech.Twist.H.module ProjSpaceCech.Idx.instFintype ProjSpaceCech.Twist.H.addCommGroup ProjSpaceCech.Idx.instDecidableEq ProjSpaceCech.Twist.Mon.instDecidableEq ProjSpaceCech.Twist.cochain.instAddCommGroup ProjSpaceCech.Twist.cochain.instModule AlgebraicGeometry.FGSubalgebra.tensorStage_directedSystem AlgebraicGeometry.RelEffCartierDiv.isClosedImmersion_subschemeι_resProdMap AlgebraicGeometry.RelEffCartierDiv.isOpenImmersion_resProdMap AlgebraicCurve.CurveModel.locallyOfFiniteType_gluedToBase"
p2m_attr_erase "instance" "AlgebraicCurve.CurveModel.isFractionRing_overlap AlgebraicCurve.CurveModel.isLocallyNoetherian_glued AlgebraicCurve.CurveModel.jacobsonSpace_glued AlgebraicCurve.CurveModel.isOpenImmersion_ι₀ AlgebraicCurve.CurveModel.isIntegral_glued AlgebraicCurve.CurveModel.quasiSeparated_gluedToBase AlgebraicCurve.CurveModel.compactSpace_glued AlgebraicCurve.CurveModel.isIntegral_adjoin_chartRing AlgebraicCurve.CurveModel.isFractionRing_overlap_functionField AlgebraicCurve.CurveModel.isProper_gluedToBase AlgebraicCurve.CurveModel.isOpenImmersion_ιU AlgebraicCurve.CurveModel.isOpenImmersion_f₀ AlgebraicCurve.CurveModel.isOpenImmersion_fInf AlgebraicCurve.CurveModel.isOpenImmersion_ιInf AlgebraicCurve.CurveModel.algebra_overlap_functionField AlgebraicCurve.CurveModel.quasiCompact_gluedToBase AlgebraicCurve.CurveModel.algebraAdjoin AlgebraicCurve.CurveModel.isDedekindDomain_chartRing AlgebraicCurve.CurveModel.isIntegralClosure AlgebraicCurve.CurveModel.finite_chartRing AlgebraicCurve.CurveModel.centre_isPrime AlgebraicCurve.CurveModel.isFractionRing_chartRing AlgebraicCurve.CurveModel.finiteType_chartRing AlgebraicCurve.CurveModel.isNoetherianRing_chartRing AlgebraicCurve.CurveModel.isScalarTower_base_adjoin AlgebraicCurve.CurveModel.isScalarTower_adjoin AlgebraicCurve.CurveModel.chartRing_finitePresentation instTopologicallyFGOfFiniteType AlgebraicGeometry.ProjSpace.twistObj.addCommGroup AlgebraicGeometry.ProjSpace.twistFam.module AlgebraicGeometry.ProjSpace.twistObj.module AlgebraicGeometry.ProjSpace.twistObj.moduleSections AlgebraicGeometry.ProjSpace.twistFam.addCommGroup kmfloorsGlue_int_three_isPrime kmfloorsGlue_int_bot_isPrime"
p2m_attr_erase "simp" "GoodReductionJacobian.RelativeGroupLaw.actionSndPoint_coe GoodReductionJacobian.RelativeGroupLaw.actionFstPoint_coe GoodReductionJacobian.RelativeGroupLaw.fibre_inv GoodReductionJacobian.RelativeGroupLaw.fibrePointToBase_coe GoodReductionJacobian.RelativeGroupLaw.fibrePointOfBase_toBase GoodReductionJacobian.RelativeGroupLaw.fibre_mul GoodReductionJacobian.RelativeGroupLaw.fibrePointToBase_ofBase GoodReductionJacobian.RelativeGroupLaw.fibre_one GoodReductionJacobian.RelativeGroupLaw.fibrePointOfBase_coe GoodReductionJacobian.relativeGroupLawOfGrpObj_inv GoodReductionJacobian.relativeGroupLawOfGrpObj_mul GoodReductionJacobian.overHomEquivSchemeHomOver_apply_coe GoodReductionJacobian.relativeGroupLawOfGrpObj_one GoodReductionJacobian.overHomEquivSchemeHomOver_symm_apply_left RegularLocalRingQuotientAscent.dualNumberFst_apply GoodReductionJacobian.RelativeGroupLaw.baseChangePointToBase_ofBase GoodReductionJacobian.RelativeGroupLaw.baseChangePointToBase_coe GoodReductionJacobian.RelativeGroupLaw.baseChangePointOfBase_coe GoodReductionJacobian.RelativeGroupLaw.baseChange_inv GoodReductionJacobian.RelativeGroupLaw.baseChangePointOfBase_toBase GoodReductionJacobian.RelativeGroupLaw.baseChange_mul GoodReductionJacobian.RelativeGroupLaw.baseChange_one NeronModelInfra.NeronModelPropertyBundle.endExtensionEquiv_symm_restrict NeronModelInfra.schemeHomOverComp_id_left NeronModelInfra.schemeHomOverComp_id_right NeronModelInfra.schemeHomOverId_coe NeronModelInfra.NeronModelPropertyBundle.endExtensionEquiv_apply NeronModelInfra.NeronModelPropertyBundle.restrict_endExtensionEquiv_symm NeronModelInfra.schemeHomOverComp_coe NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_fst NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_snd NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_fst NeronSpecialFibreInfra.neronEndRestrictEquiv_apply NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_fst_assoc NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_snd NeronSpecialFibreInfra.neronEndExtension_genericFibreRestrict NeronSpecialFibreInfra.specClosedFibreInclusion_eq NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_fst_assoc NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_snd_assoc NeronSpecialFibreInfra.genericFibreRestrict_neronEndExtension"
p2m_attr_erase "simp" "NeronSpecialFibreInfra.homOverId_coe NeronSpecialFibreInfra.homOverComp_coe NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_snd_assoc NeronModelInfra.schemeHomOverNpow_succ NeronModelInfra.schemeHomOverNpow_zero SheafOfModules.tensorUnit_eq AlgebraicGeometry.Scheme.Modules.tensorUnit_eq PresheafOfModules.InternalHom.presheaf_map_apply PresheafOfModules.InternalHom.curryFamily_app PresheafOfModules.InternalHom.add_app PresheafOfModules.InternalHom.smul_app PresheafOfModules.InternalHom.zero_app PresheafOfModules.ihomObj_map_val PresheafOfModules.ihomFunctor_map PresheafOfModules.InternalHom.restrict_app PresheafOfModules.InternalHom.postcomp_app PresheafOfModules.InternalHom.neg_app PresheafOfModules.curry'_app_val PresheafOfModules.InternalHom.presheaf_obj PresheafOfModules.ihomFunctor_obj PresheafOfModules.ihomObj_obj PresheafOfModules.InternalHom.sub_app PresheafOfModules.ihomMap_app_val AlgebraicGeometry.Scheme.Modules.tensorPow_zero AlgebraicGeometry.Scheme.Modules.tensorPow_succ AlgebraicGeometry.RelPicard.RigidifiedLineBundle.mk.sizeOf_spec AlgebraicGeometry.RelPicard.RigidifiedLineBundle.mk.injEq AlgebraicGeometry.Scheme.OrderedAffineCover.mk.injEq AlgebraicGeometry.OModulePresheaf.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCover.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.mk.injEq AlgebraicGeometry.Scheme.TwoAffineOpenCover.mk.injEq AlgebraicGeometry.Scheme.TwoAffineOpenCover.mk.sizeOf_spec AlgebraicGeometry.Scheme.TwoAffineOpenCover.pullback_U1 AlgebraicGeometry.Scheme.TwoAffineOpenCover.pullback_U0 TwoChartCech.Sections.mk.injEq TwoChartCech.Cover.mk.injEq TwoChartCech.GrothendieckComplex.mk.injEq TwoChartCech.Sections.mk.sizeOf_spec TwoChartCech.Cover.mk.sizeOf_spec"
p2m_attr_erase "simp" "TwoChartCech.Cover.lineBundle_r0_apply TwoChartCech.GrothendieckComplex.mk.sizeOf_spec TwoChartCech.Cover.lineBundle_r1_apply CoherentBaseChange.TwoTermComplex.mk.sizeOf_spec CoherentBaseChange.TwoTermComplex.mk.injEq AlgebraicGeometry.OModulePresheaf.prod_obj AlgebraicGeometry.OModulePresheaf.restrOpen_obj AlgebraicGeometry.OModulePresheaf.DevissageStep.mk.injEq AlgebraicGeometry.OModulePresheaf.pushforward_obj AlgebraicGeometry.OModulePresheaf.im_obj AlgebraicGeometry.OModulePresheaf.pow_obj AlgebraicGeometry.OModulePresheaf.fstHom_app AlgebraicGeometry.OModulePresheaf.ker_obj AlgebraicGeometry.OModulePresheaf.coker_obj AlgebraicGeometry.OModulePresheaf.DevissageStep.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCover.preimage_U AlgebraicGeometry.OModulePresheaf.sndHom_app AlgebraicGeometry.OModulePresheaf.Hom.mk.injEq AlgebraicGeometry.OModulePresheaf.Hom.id_app AlgebraicGeometry.OModulePresheaf.AffHom.appSections_apply AlgebraicGeometry.OModulePresheaf.AffHom.comp_app AlgebraicGeometry.OModulePresheaf.AffSES.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.AffHom.kerMap_coe AlgebraicGeometry.OModulePresheaf.AffHom.id_app AlgebraicGeometry.OModulePresheaf.Hom.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.Hom.toAffHom_app AlgebraicGeometry.OModulePresheaf.SES.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.AffHom.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.Hom.comp_app AlgebraicGeometry.OModulePresheaf.SES.mk.injEq AlgebraicGeometry.OModulePresheaf.AffHom.mk.injEq AlgebraicGeometry.OModulePresheaf.Hom.appSections_apply AlgebraicGeometry.OModulePresheaf.AffSES.mk.injEq PresheafOfModules.freeεIso_hom_app PresheafOfModules.freeμIso_hom_app AlgebraicGeometry.RelPicard.RepresentsRelSubPic.mk.injEq AlgebraicGeometry.RelPicard.SubPicCondition.mk.injEq AlgebraicGeometry.RelPicard.SubPicCondition.mk.sizeOf_spec AlgebraicGeometry.RelPicard.RepresentsRelSubPic.mk.sizeOf_spec AlgebraicGeometry.SmoothProperCurve.sectionBaseChange_coe_snd"
p2m_attr_erase "simp" "AlgebraicGeometry.SmoothProperCurve.sectionBaseChange_coe_fst AlgebraicCurve.CurveModel.mk.injEq AlgebraicCurve.CurveModel.mk.sizeOf_spec AlgebraicCurve.mulAdele_apply AlgebraicCurve.residuePairing_apply_coe AlgebraicCurve.mem_adeleBdd AlgebraicCurve.weilSmul_one AlgebraicCurve.diagonalHom_apply AlgebraicCurve.weilSmul_apply AlgebraicCurve.adeleSpaceMul_coe AlgebraicCurve.mulAdele_one AlgebraicGeometry.SmoothProperCurve.FiniteMapData.twoAffineOpenCover_U1 AlgebraicGeometry.SmoothProperCurve.FiniteMapData.mk.injEq AlgebraicGeometry.SmoothProperCurve.FiniteMapData.mk.sizeOf_spec AlgebraicGeometry.SmoothProperCurve.FiniteMapData.twoAffineOpenCover_U0 AlgebraicGeometry.RelPicard.SubPicCondition.onClasses_mk AlgebraicGeometry.RelPicard.relSubPicPresheaf_map_coe CategoryTheory.Functor.OverTotal.ofFibre_fst CategoryTheory.Functor.overTotal_map_fst AlgebraicGeometry.Scheme.LocalRepresentabilityULift.glueData_J AlgebraicGeometry.Scheme.LocalRepresentabilityULift.uliftYoneda_toGlued_uliftYonedaGluedToSheaf AlgebraicGeometry.Scheme.LocalRepresentabilityULift.glueData_t' AlgebraicGeometry.Scheme.LocalRepresentabilityULift.uliftYoneda_toGlued_uliftYonedaGluedToSheaf_assoc AlgebraicGeometry.Scheme.LocalRepresentabilityULift.uliftYonedaGluedToSheaf_app_toGlued AlgebraicGeometry.Scheme.LocalRepresentabilityULift.glueData_openCover_map AlgebraicGeometry.Scheme.LocalRepresentabilityULift.uliftYonedaGluedToSheaf_app_comp AlgebraicGeometry.Scheme.LocalRepresentabilityULift.glueData_V AlgebraicGeometry.Scheme.LocalRepresentabilityULift.glueData_t AlgebraicGeometry.Scheme.LocalRepresentabilityULift.glueData_U AlgebraicGeometry.Scheme.LocalRepresentabilityULift.glueData_f AlgebraicGeometry.RelPicard.designationOfRepresentableBy_P AlgebraicGeometry.RelPicard.designationOfRepresentableBy_toBase AlgebraicGeometry.RelPicard.rigSection_snd AlgebraicGeometry.RelPicard.RigidifiedLineBundle.ofInvertible_L AlgebraicGeometry.RelPicard.rigSection_snd_assoc AlgebraicGeometry.RelPicard.SubPicGroupCondition.mk.injEq AlgebraicGeometry.RelPicard.SubPicGroupCondition.mk.sizeOf_spec AlgebraicCurve.coe_cechH0Equiv_apply AlgebraicCurve.cechH1ToH1_mk AlgebraicCurve.lSpaceOn_univ"
p2m_attr_erase "simp" "AlgebraicCurve.lSpaceOn_empty AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.Divisor.mapRestrict_single AlgebraicCurve.Divisor.pushforward_single AlgebraicCurve.Place.coe_restrictInclusion AlgebraicCurve.Place.mem_fiber AlgebraicCurve.Place.restrict_toValuationSubring AlgebraicCurve.Divisor.degree_pushforward AlgebraicCurve.Place.restrictResidueMap_residue AlgebraicCurve.Pic0.coe_pushforwardDegZeroHom AlgebraicCurve.Pic0.coe_pullbackDegZeroHom AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Divisor.degree_pushforwardAlong AlgebraicCurve.Pic0.coe_degZeroCorrespondence AlgebraicCurve.Place.mem_fiberAlong AlgebraicCurve.coe_frobeniusPushforwardDegZero"
p2m_attr_erase "simp" "AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.jqNModC_one ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one AlgebraicCurve.Place.differentialCoeff_zero AlgebraicCurve.Place.differentialCoeff_dCoord AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.injEq AlgebraicCurve.TranscendenceTower.mk.injEq AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec AlgebraicCurve.PoleDivisorPackage.mk.injEq AlgebraicGeometry.RelPicard.thetaBundle_def AlgebraicGeometry.RelPicard.picardBundle_def AlgebraicGeometry.RelEffCartierDiv.toRelEffDivisor_ofRelEffDivisor AlgebraicGeometry.RelEffCartierDiv.toRelEffDivisor_I AlgebraicGeometry.mapOnProdOver_fst_assoc AlgebraicGeometry.RelEffCartierDiv.mk.sizeOf_spec AlgebraicGeometry.RelEffCartierDiv.mk.injEq AlgebraicGeometry.mapOnProdOver_snd AlgebraicGeometry.mapOnProdOver_fst AlgebraicGeometry.mapOnProdOver_snd_assoc AlgebraicGeometry.mapOnProdOver_id AlgebraicCurve.RelEffDivisor.mk.sizeOf_spec AlgebraicCurve.mapOnProd_fst AlgebraicCurve.mapOnProd_fst_assoc AlgebraicCurve.mapOnProd_snd AlgebraicCurve.UnivDivisorPack.mk.injEq"
p2m_attr_erase "simp" "AlgebraicCurve.RelEffDivisor.mk.injEq AlgebraicCurve.UnivDivisorPack.mk.sizeOf_spec AlgebraicCurve.mapOnProd_snd_assoc AlgebraicGeometry.Scheme.Modules.exteriorPower_obj PresheafOfModules.exteriorPower_map_ιMulti PresheafOfModules.ExteriorPower.appₗ_apply AlgebraicGeometry.prodKerGraph_one AlgebraicGeometry.fibrePowOver.proj_comp AlgebraicGeometry.prodKerGraph_zero AlgebraicGeometry.RelEffCartierDiv.empty_I AlgebraicGeometry.fibrePowOver.proj_comp_assoc AlgebraicGeometry.graphOver_fst_assoc AlgebraicGeometry.RelEffCartierDiv.toPoint_comp AlgebraicGeometry.RelEffCartierDiv.toPoint_comp_assoc AlgebraicGeometry.graphOver_fst AlgebraicGeometry.RelEffCartierDiv.ofPoint_I AlgebraicGeometry.graphOver_snd AlgebraicGeometry.graphOver_snd_assoc AlgebraicCurve.SymmetricPowerPackage.mk.sizeOf_spec AlgebraicCurve.SymmetricPowerPackage.mk.injEq AlgebraicGeometry.FGSubalgebra.cocone_ι_app_apply AlgebraicGeometry.RelPicard.fst_toProdSpec AlgebraicGeometry.RelPicard.toProdSpec_fst_assoc AlgebraicGeometry.RelPicard.pointsSubBasepointModule_cons AlgebraicGeometry.RelPicard.pointsSubBasepointModule_nil AlgebraicGeometry.RelPicard.fst_toProdSpec_assoc AlgebraicGeometry.RelPicard.toProdSpec_fst AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.sub_app AlgebraicGeometry.Scheme.IdealSheafData.sres_sresTop AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.add_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.mk.sizeOf_spec AlgebraicGeometry.Scheme.IdealSheafData.coe_resLE AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.smul_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.coe_ofLE_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.ideal_range AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.zero_app AlgebraicGeometry.Scheme.IdealSheafData.sres_sres AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.comp_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.neg_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.id_app"
p2m_attr_erase "simp" "AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.coe_mulRight_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.nsmul_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.mk.injEq AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.zsmul_app AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.sizeOf_spec AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.injEq AlgebraicCurve.adeleSingle_coe AlgebraicCurve.kaehlerResidueTermKFam_apply AlgebraicCurve.Place.LocalResidueData.mk.injEq AlgebraicCurve.Place.LocalResidueData.mk.sizeOf_spec AlgebraicCurve.Place.kw_ffgc_adicCompletionComapIntegers_coe AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.sizeOf_spec AlgebraicCurve.Place.mem_simplePoleSubmodule AlgebraicCurve.Place.coe_uniformizerSubring ModularCurve.Lg37.Lg37CompletionSection.mk.injEq AlgebraicCurve.Place.CoefficientFieldSection.mk.injEq AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.injEq ModularCurve.Lg37.Lg37CompletionSection.mk.sizeOf_spec AlgebraicCurve.Place.CoefficientFieldSection.mk.sizeOf_spec AlgebraicCurve.Place.poleSubmodule_one AlgebraicCurve.Place.mem_poleSubmodule AlgebraicGeometry.Scheme.Modules.toUnitSection_ofUnitSection AlgebraicGeometry.Scheme.Modules.pullbackSection_def AlgebraicGeometry.Scheme.Modules.ofUnitSection_toUnitSection PresheafOfModules.InternalHom.IsSheafAux.appAt_toPresheafHom SheafOfModules.ihomSectionsEquivFamily_unit AlgebraicGeometry.Scheme.Modules.restrictHomEquivFamily_apply SheafOfModules.ihomEval_unit_app AlgebraicGeometry.Scheme.Modules.ihomEval_zero_right AlgebraicGeometry.Scheme.Modules.ihomEval_zero_left AlgebraicGeometry.Scheme.Modules.homOfFamily_app_apply SheafOfModules.unit_ihomSectionsEquivFamily AlgebraicGeometry.Scheme.Modules.familyOfHom_app AlgebraicGeometry.Scheme.Modules.restrictUnitIso_hom_app_apply AlgebraicGeometry.Scheme.Modules.restrictUnitIso_inv_app_apply AlgebraicGeometry.Scheme.Modules.restrictHomOfFamily_app_apply AlgebraicGeometry.Scheme.Modules.restrictHomEquivFamily_symm_apply AlgebraicGeometry.Scheme.Modules.tensorSections_zero_right AlgebraicGeometry.Scheme.Modules.map_unitSection AlgebraicGeometry.Scheme.Modules.tensorSectionsBilin_apply"
p2m_attr_erase "simp" "AlgebraicGeometry.Scheme.Modules.tensorPowSection_zero AlgebraicGeometry.Scheme.Modules.tensorSections_zero_left AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_neg AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_zero AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_sub AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_add AlgebraicGeometry.Scheme.OrderedAffineCover.toCoverOf_U AlgebraicGeometry.Scheme.OrderedAffineCoverOf.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCoverOf.mk.injEq AlgebraicGeometry.Scheme.OrderedAffineCover.restrict_U AlgebraicGeometry.OModulePresheaf.Leray.restrictToPreimage_U DoubleComplex.Bounded.mk.injEq DoubleComplex.Bounded.mk.sizeOf_spec DoubleComplex.Convergence.mk.injEq DoubleComplex.Convergence.mk.sizeOf_spec DoubleComplex.SubQuot.mk.sizeOf_spec DoubleComplex.SubQuot.mk.injEq AlgebraicGeometry.ChowDatumProj.mk.sizeOf_spec AlgebraicGeometry.ChowDatum.mk.sizeOf_spec AlgebraicGeometry.ChowDatumProj.mk.injEq AlgebraicGeometry.ChowDatum.mk.injEq ProjSpaceCech.GradedModule.mk.injEq ProjSpaceCech.GradedModule.mk.sizeOf_spec ProjSpaceCech.GradedModule.Frac.mk.sizeOf_spec ProjSpaceCech.GradedModule.Presentation.mk.injEq ProjSpaceCech.GradedModule.Frac.mk.injEq ProjSpaceCech.GradedModule.Presentation.mk.sizeOf_spec ProjSpaceCech.GradedModule.Hom.shift_toLinearMap ProjSpaceCech.GradedModule.Hom.mk.sizeOf_spec ProjSpaceCech.GradedModule.Hom.mk.injEq TwoChartCech.Mumford.dK_apply TwoChartCech.Mumford.ι0_apply TwoChartCech.Mumford.ι1_apply TwoChartCech.KerCoprod.dK_apply TwoChartCech.KerCoprod.ι1_apply TwoChartCech.KerCoprod.ι0_apply AlgebraicGeometry.tilde.functorCompPullbackSpecIso_app AlgebraicGeometry.RelPicard.algEquivZeroGroupCut_toSubPicCondition AlgebraicGeometry.RelPicard.LFP.stageHom_val AlgebraicGeometry.RelPicard.BaseChange.relSubPicPresheafRestrictIso_hom_app_coe"
p2m_attr_erase "simp" "AlgebraicGeometry.RelPicard.BaseChange.relSubPicPresheafRestrictIso_inv_app_coe AlgebraicGeometry.RelPicard.BaseChange.restrict_P AlgebraicGeometry.RelEffCartierDiv.IsUniversal.lift_comp AlgebraicGeometry.RelEffCartierDiv.functor_map_fst AlgebraicGeometry.RelEffCartierDiv.IsUniversal.homEquiv_apply AlgebraicGeometry.RelEffCartierDiv.IsUniversal.lift_pullbackAlong AlgebraicGeometry.RelEffCartierDiv.IsUniversal.homEquiv_symm_apply AlgebraicGeometry.RelEffCartierDiv.IsUniversal.lift_comp_assoc AlgebraicGeometry.RelEffCartierDiv.supportedIn_top AlgebraicGeometry.RelEffCartierDiv.mem_supportedIn_iff AlgebraicGeometry.RelEffCartierDiv.supportedIn_top_eq AlgebraicGeometry.RelEffCartierDiv.restrictAlong_extendAlong AlgebraicGeometry.RelEffCartierDiv.extendAlong_I AlgebraicGeometry.RelEffCartierDiv.resProdMap_snd AlgebraicGeometry.RelEffCartierDiv.restrictAlong_I AlgebraicGeometry.RelEffCartierDiv.extendAlong_restrictAlong AlgebraicGeometry.RelEffCartierDiv.resProdMap_fst_assoc AlgebraicGeometry.RelEffCartierDiv.resProdMap_snd_assoc AlgebraicGeometry.RelEffCartierDiv.resProdMap_fst CoherentBaseChange.FibreH0Family.mk.sizeOf_spec CoherentBaseChange.FibreH0Family.mk.injEq AlgebraicGeometry.Scheme.Modules.ProjPresentation.mk.injEq AlgebraicGeometry.Scheme.Modules.ProjPresentation.mk.sizeOf_spec AlgebraicCurve.CurveModel.coe_gInf AlgebraicCurve.CurveModel.coe_tInvChart AlgebraicCurve.CurveModel.ιInf_gluedToBase_assoc AlgebraicCurve.CurveModel.ιInf_gluedToBase AlgebraicCurve.CurveModel.primeOfι₀_asIdeal AlgebraicCurve.CurveModel.coe_tChart AlgebraicCurve.CurveModel.ι₀_gluedToBase_assoc AlgebraicCurve.CurveModel.primeOfιInf_asIdeal AlgebraicCurve.CurveModel.ι₀_gluedToBase AlgebraicCurve.CurveModel.coe_tma AlgebraicCurve.CurveModel.coe_primeEquivChartPlaces AlgebraicGeometry.ProjSpace.twistObj.mk.injEq AlgebraicGeometry.ProjSpace.twistObj.zero_val AlgebraicGeometry.ProjSpace.twistObj.add_val AlgebraicGeometry.ProjSpace.twist_res_val AlgebraicGeometry.ProjSpace.twist_smul_val AlgebraicGeometry.ProjSpace.twistGradeToObj_val"
p2m_attr_erase "simp" "AlgebraicGeometry.ProjSpace.twistObj.smul_val AlgebraicGeometry.ProjSpace.twistGradeEquiv_apply_val AlgebraicGeometry.ProjSpace.twistObj.mk.sizeOf_spec AlgebraicGeometry.schemeFibreEndo_snd AlgebraicGeometry.schemeFibreEndo_fst"

set_option autoImplicit false

open scoped Quaternion
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry CerednikDrinfeld CerednikDrinfeld.QM QuaternionAlgebra NeronModelInfra GoodReductionJacobian

universe u

namespace IMGSUB

variable {R : Type u} [CommRing R]
  {A₀ A : Scheme.{u}} {f₀ : A₀ ⟶ Spec (CommRingCat.of R)} {f : A ⟶ Spec (CommRingCat.of R)}
  (L₀ : RelativeGroupLaw R f₀) (L : RelativeGroupLaw R f)
  (p : A₀ ⟶ A) (hp : p ≫ f = f₀)
  (hp_hom : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (P Q : SchemeHomOver t f₀),
    mapPt p hp (L₀.mul t P Q) = L.mul t (mapPt p hp P) (mapPt p hp Q))
  {C₀ : Scheme.{u}} (ι : C₀ ⟶ A₀)
  (hsub : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (P Q : SchemeHomOver t f₀),
    FactorsThrough ι P → FactorsThrough ι Q → FactorsThrough ι (L₀.mul t P Q) ∧ FactorsThrough ι (L₀.inv t P))
  (hdisj : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (P : SchemeHomOver t f₀),
    FactorsThrough ι P → mapPt p hp P = L.one t → P = L₀.one t)

include hp_hom in
private theorem _root_.IMGSUB.map_one {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) : mapPt p hp (L₀.one t) = L.one t := by
  have h := hp_hom t (L₀.one t) (L₀.one t)
  rw [L₀.one_mul] at h
  have := congrArg (L.mul t (L.inv t (mapPt p hp (L₀.one t)))) h
  rw [← L.mul_assoc, L.inv_mul_cancel, L.one_mul] at this
  exact this.symm

p2m_export "IMGSUB" "map_one"
include hp_hom in
theorem map_inv {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (P : SchemeHomOver t f₀) :
    mapPt p hp (L₀.inv t P) = L.inv t (mapPt p hp P) := by
  letI := L.pointGroup t
  have h := hp_hom t (L₀.inv t P) P
  rw [L₀.inv_mul_cancel, map_one L₀ L p hp hp_hom] at h
  exact (inv_eq_of_mul_eq_one_left h.symm).symm

include hp_hom hsub hdisj in

theorem inj {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (P Q : SchemeHomOver t f₀)
    (hP : FactorsThrough ι P) (hQ : FactorsThrough ι Q) (h : mapPt p hp P = mapPt p hp Q) : P = Q := by
  letI := L₀.pointGroup t
  letI := L.pointGroup t
  have hD : FactorsThrough ι (L₀.mul t P (L₀.inv t Q)) := (hsub t _ _ hP (hsub t Q Q hQ hQ).2).1
  have hpD : mapPt p hp (L₀.mul t P (L₀.inv t Q)) = L.one t := by
    rw [hp_hom, map_inv L₀ L p hp hp_hom, h]; exact mul_inv_cancel (mapPt p hp Q)
  have := hdisj t _ hD hpD
  exact mul_inv_eq_one.1 this

include hp_hom hsub hdisj in

theorem isClosedImmersion [IsClosedImmersion ι] [IsFinite (ι ≫ p)] : IsClosedImmersion (ι ≫ p) := by
  rw [IsClosedImmersion.iff_isFinite_and_mono]
  refine ⟨inferInstance, ⟨fun {T} c₁ c₂ hc => ?_⟩⟩

  have ht : c₂ ≫ ι ≫ f₀ = c₁ ≫ ι ≫ f₀ := by
    rw [← hp, ← Category.assoc ι, ← Category.assoc, ← hc, Category.assoc, Category.assoc]
  have h := inj L₀ L p hp hp_hom ι hsub hdisj (c₁ ≫ ι ≫ f₀) ⟨c₁ ≫ ι, by rw [Category.assoc]⟩ ⟨c₂ ≫ ι, by rw [Category.assoc, ht]⟩
    ⟨c₁, rfl⟩ ⟨c₂, rfl⟩ (by apply Subtype.ext; simp only [mapPt, Category.assoc]; simpa [Category.assoc] using hc)
  have := congrArg Subtype.val h
  exact (cancel_mono ι).1 this

theorem factorsThrough_iff {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (Q : SchemeHomOver t f) :
    FactorsThrough (ι ≫ p) Q ↔ ∃ P : SchemeHomOver t f₀, FactorsThrough ι P ∧ mapPt p hp P = Q := by
  constructor
  · rintro ⟨c, hc⟩
    refine ⟨⟨c ≫ ι, by rw [← hp, Category.assoc, ← Category.assoc ι, ← Category.assoc, hc]; exact Q.2⟩, ⟨c, rfl⟩, ?_⟩
    apply Subtype.ext; simp only [mapPt, Category.assoc]; simpa [Category.assoc] using hc
  · rintro ⟨P, ⟨c, hc⟩, rfl⟩
    exact ⟨c, by simp only [mapPt, ← Category.assoc, hc]⟩

include hp_hom hsub in
theorem sub {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (Q Q' : SchemeHomOver t f)
    (hQ : FactorsThrough (ι ≫ p) Q) (hQ' : FactorsThrough (ι ≫ p) Q') :
    FactorsThrough (ι ≫ p) (L.mul t Q Q') ∧ FactorsThrough (ι ≫ p) (L.inv t Q) := by
  rw [factorsThrough_iff p hp ι] at hQ hQ'
  obtain ⟨P, hP, hPQ⟩ := hQ; obtain ⟨P', hP', hPQ'⟩ := hQ'
  subst hPQ hPQ'
  constructor
  · rw [factorsThrough_iff p hp ι]; exact ⟨L₀.mul t P P', (hsub t P P' hP hP').1, hp_hom t P P'⟩
  · rw [factorsThrough_iff p hp ι]; exact ⟨L₀.inv t P, (hsub t P P hP hP).2, map_inv L₀ L p hp hp_hom t P⟩

include hp_hom in
private theorem _root_.IMGSUB.one (hone : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)), FactorsThrough ι (L₀.one t))
    {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) : FactorsThrough (ι ≫ p) (L.one t) := by
  rw [factorsThrough_iff p hp ι]; exact ⟨L₀.one t, hone t, map_one L₀ L p hp hp_hom t⟩

p2m_export "IMGSUB" "one"
include hp_hom in
theorem torsion (n : ℕ) (htor : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (P : SchemeHomOver t f₀),
      FactorsThrough ι P → nsmulPt L₀ t n P = L₀.one t)
    {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (Q : SchemeHomOver t f) (hQ : FactorsThrough (ι ≫ p) Q) :
    nsmulPt L t n Q = L.one t := by
  rw [factorsThrough_iff p hp ι] at hQ
  obtain ⟨P, hP, hPQ⟩ := hQ
  subst hPQ
  have hn : ∀ m : ℕ, mapPt p hp (nsmulPt L₀ t m P) = nsmulPt L t m (mapPt p hp P) := by
    intro m; induction m with
    | zero => exact map_one L₀ L p hp hp_hom t
    | succ m ih => simp only [nsmulPt]; rw [hp_hom, ih]
  rw [← hn, htor t P hP]; exact map_one L₀ L p hp hp_hom t

include hp in

theorem stable (α₀ : A₀ ⟶ A₀) (hα₀ : α₀ ≫ f₀ = f₀) (α : A ⟶ A) (hα : α ≫ f = f) (hcomm : p ≫ α = α₀ ≫ p)
    (hst : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (P : SchemeHomOver t f₀),
      FactorsThrough ι P → FactorsThrough ι (mapPt α₀ hα₀ P))
    {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (Q : SchemeHomOver t f) (hQ : FactorsThrough (ι ≫ p) Q) :
    FactorsThrough (ι ≫ p) (mapPt α hα Q) := by
  rw [factorsThrough_iff p hp ι] at hQ ⊢
  obtain ⟨P, hP, hPQ⟩ := hQ
  subst hPQ
  refine ⟨mapPt α₀ hα₀ P, hst t P hP, ?_⟩
  apply Subtype.ext; simp only [mapPt, Category.assoc, hcomm]

include hp_hom hsub hdisj in

theorem exists_equiv {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) :
    ∃ e : {P : SchemeHomOver t f₀ // FactorsThrough ι P} ≃ {Q : SchemeHomOver t f // FactorsThrough (ι ≫ p) Q},
      (∀ P, ((e P) : SchemeHomOver t f) = mapPt p hp P.1) := by
  refine ⟨Equiv.ofBijective (fun P => ⟨mapPt p hp P.1, (factorsThrough_iff p hp ι t _).2 ⟨P.1, P.2, rfl⟩⟩) ⟨?_, ?_⟩, fun P => rfl⟩
  · intro P P' h
    exact Subtype.ext (inj L₀ L p hp hp_hom ι hsub hdisj t P.1 P'.1 P.2 P'.2 (congrArg Subtype.val h))
  · rintro ⟨Q, hQ⟩
    obtain ⟨P, hP, rfl⟩ := (factorsThrough_iff p hp ι t Q).1 hQ
    exact ⟨⟨P, hP⟩, rfl⟩

theorem torsion' (n : ℕ) (htor : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (P : SchemeHomOver t f₀),
      FactorsThrough ι P → nsmulPt L t n (mapPt p hp P) = L.one t)
    {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (Q : SchemeHomOver t f) (hQ : FactorsThrough (ι ≫ p) Q) :
    nsmulPt L t n Q = L.one t := by
  rw [factorsThrough_iff p hp ι] at hQ
  obtain ⟨P, hP, hPQ⟩ := hQ
  subst hPQ
  exact htor t P hP

end IMGSUB

namespace FLIP

variable {R : Type} [CommRing R]

theorem mapPt_comp {A A' A'' : Scheme.{0}} {f : A ⟶ Spec (CommRingCat.of R)} {f' : A' ⟶ Spec (CommRingCat.of R)}
    {f'' : A'' ⟶ Spec (CommRingCat.of R)} (φ : A ⟶ A') (hφ : φ ≫ f' = f) (ψ : A' ⟶ A'') (hψ : ψ ≫ f'' = f')
    {h : (φ ≫ ψ) ≫ f'' = f} {T : Scheme.{0}} {t : T ⟶ Spec (CommRingCat.of R)} (P : SchemeHomOver t f) :
    mapPt (φ ≫ ψ) h P = mapPt ψ hψ (mapPt φ hφ P) := by
  apply Subtype.ext; simp [mapPt, Category.assoc]

theorem mapPt_id {A : Scheme.{0}} {f : A ⟶ Spec (CommRingCat.of R)} {h : 𝟙 A ≫ f = f}
    {T : Scheme.{0}} {t : T ⟶ Spec (CommRingCat.of R)} (P : SchemeHomOver t f) : mapPt (𝟙 A) h P = P := by
  apply Subtype.ext; simp [mapPt]

theorem eq_of_mapPt_id_eq {A A' : Scheme.{0}} {f : A ⟶ Spec (CommRingCat.of R)} {f' : A' ⟶ Spec (CommRingCat.of R)}
    {φ ψ : A ⟶ A'} {hφ : φ ≫ f' = f} {hψ : ψ ≫ f' = f}
    (h : mapPt φ hφ (⟨𝟙 A, Category.id_comp f⟩ : SchemeHomOver f f) = mapPt ψ hψ ⟨𝟙 A, Category.id_comp f⟩) : φ = ψ := by
  have := congrArg Subtype.val h
  simpa [mapPt] using this

def IsHom {X Y : Scheme.{0}} {gX : X ⟶ Spec (CommRingCat.of R)} {gY : Y ⟶ Spec (CommRingCat.of R)}
    (LX : RelativeGroupLaw R gX) (LY : RelativeGroupLaw R gY) (α : X ⟶ Y) (hα : α ≫ gY = gX) : Prop :=
  ∀ ⦃T : Scheme.{0}⦄ (t : T ⟶ Spec (CommRingCat.of R)) (u v : SchemeHomOver t gX),
    mapPt α hα (LX.mul t u v) = LY.mul t (mapPt α hα u) (mapPt α hα v)

theorem IsHom.comp {X Y Z : Scheme.{0}} {gX : X ⟶ Spec (CommRingCat.of R)} {gY : Y ⟶ Spec (CommRingCat.of R)}
    {gZ : Z ⟶ Spec (CommRingCat.of R)} {LX : RelativeGroupLaw R gX} {LY : RelativeGroupLaw R gY} {LZ : RelativeGroupLaw R gZ}
    {α : X ⟶ Y} {hα : α ≫ gY = gX} {β : Y ⟶ Z} {hβ : β ≫ gZ = gY} (h₁ : IsHom LX LY α hα) (h₂ : IsHom LY LZ β hβ)
    {h : (α ≫ β) ≫ gZ = gX} : IsHom LX LZ (α ≫ β) h := by
  intro T t u v
  rw [mapPt_comp α hα β hβ, h₁, h₂, ← mapPt_comp α hα β hβ, ← mapPt_comp α hα β hβ]

theorem IsHom.map_one {X Y : Scheme.{0}} {gX : X ⟶ Spec (CommRingCat.of R)} {gY : Y ⟶ Spec (CommRingCat.of R)}
    {LX : RelativeGroupLaw R gX} {LY : RelativeGroupLaw R gY} {α : X ⟶ Y} {hα : α ≫ gY = gX} (h : IsHom LX LY α hα)
    {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of R)) : mapPt α hα (LX.one t) = LY.one t := by
  have h' := h t (LX.one t) (LX.one t)
  rw [LX.one_mul] at h'
  have := congrArg (LY.mul t (LY.inv t (mapPt α hα (LX.one t)))) h'
  rw [← LY.mul_assoc, LY.inv_mul_cancel, LY.one_mul] at this
  exact this.symm

theorem IsHom.map_nsmulPt {X Y : Scheme.{0}} {gX : X ⟶ Spec (CommRingCat.of R)} {gY : Y ⟶ Spec (CommRingCat.of R)}
    {LX : RelativeGroupLaw R gX} {LY : RelativeGroupLaw R gY} {α : X ⟶ Y} {hα : α ≫ gY = gX} (h : IsHom LX LY α hα)
    {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of R)) (n : ℕ) (P : SchemeHomOver t gX) :
    mapPt α hα (nsmulPt LX t n P) = nsmulPt LY t n (mapPt α hα P) := by
  induction n with
  | zero => exact h.map_one t
  | succ n ih => simp only [nsmulPt]; rw [h, ih]

theorem mapPt_iso_eq_iff {X Y : Scheme.{0}} {gX : X ⟶ Spec (CommRingCat.of R)} {gY : Y ⟶ Spec (CommRingCat.of R)}
    (e : X ≅ Y) (he : e.hom ≫ gY = gX) {T : Scheme.{0}} {t : T ⟶ Spec (CommRingCat.of R)} (P Q : SchemeHomOver t gX) :
    mapPt e.hom he P = mapPt e.hom he Q ↔ P = Q := by
  constructor
  · intro h
    have := congrArg (fun S : SchemeHomOver t gY => S.1 ≫ e.inv) h
    simp only [mapPt, Category.assoc, e.hom_inv_id, Category.comp_id] at this
    exact Subtype.ext this
  · rintro rfl; rfl

end FLIP

namespace FLIP

open CerednikDrinfeld.QM.FakeEllipticCurve

structure QProps {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} {N : ℕ} {k : Type} [Field k] {ℓ : ℕ}
    (u : FakeEllipticCurve.WithExtraLevel Λ N ℓ k) (E' : FakeEllipticCurve Λ N k)
    (p : u.1.A ⟶ E'.A) (hp : p ≫ E'.f = u.1.f) (ψ : E'.A ⟶ u.1.A) (hψ : ψ ≫ u.1.f = E'.f) : Prop where
  hom_p : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of k)) (P Q : SchemeHomOver t u.1.f),
    mapPt p hp (u.1.L.mul t P Q) = E'.L.mul t (mapPt p hp P) (mapPt p hp Q)
  hom_ψ : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of k)) (P Q : SchemeHomOver t E'.f),
    mapPt ψ hψ (E'.L.mul t P Q) = u.1.L.mul t (mapPt ψ hψ P) (mapPt ψ hψ Q)
  equiv : ∀ x : ↥Λ, u.1.act x ≫ p = p ≫ E'.act x
  ψlin : ∀ x : ↥Λ, E'.act x ≫ ψ = ψ ≫ u.1.act x
  fin : IsFinite p
  flat : Flat p
  lfp : LocallyOfFinitePresentation p
  surj : Surjective p
  rank : ∀ y : ↥E'.A, p.finrank y = ℓ ^ 2
  ker : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of k)) (P : SchemeHomOver t u.1.f),
    mapPt p hp P = E'.L.one t ↔ FactorsThrough u.2.levK P
  ψp : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of k)) (P : SchemeHomOver t u.1.f),
    mapPt ψ hψ (mapPt p hp P) = nsmulPt u.1.L t ℓ P
  pψ : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of k)) (Q : SchemeHomOver t E'.f),
    mapPt p hp (mapPt ψ hψ Q) = nsmulPt E'.L t ℓ Q
  univ : ∀ (X : Scheme.{0}) (gX : X ⟶ Spec (CommRingCat.of k)) (LX : RelativeGroupLaw k gX) (φ : u.1.A ⟶ X) (hφ : φ ≫ gX = u.1.f),
    (∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of k)) (P Q : SchemeHomOver t u.1.f),
      mapPt φ hφ (u.1.L.mul t P Q) = LX.mul t (mapPt φ hφ P) (mapPt φ hφ Q)) →
    (∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of k)) (P : SchemeHomOver t u.1.f),
      FactorsThrough u.2.levK P → mapPt φ hφ P = LX.one t) →
    ∃! χ : SchemeHomOver E'.f gX, p ≫ χ.1 = φ ∧
      ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of k)) (v w : SchemeHomOver t E'.f),
        mapPt χ.1 χ.2 (E'.L.mul t v w) = LX.mul t (mapPt χ.1 χ.2 v) (mapPt χ.1 χ.2 w)
  lev : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of k)) (Q : SchemeHomOver t E'.f),
    FactorsThrough E'.lev Q ↔ ∃ P : SchemeHomOver t u.1.f, FactorsThrough u.1.lev P ∧ mapPt p hp P = Q

theorem exists_quot {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} {N : ℕ} (hO : IsOrder Λ)
    (k : Type) [Field k] [IsAlgClosed k] (ℓ : ℕ) [Fact ℓ.Prime] (hℓk : (ℓ : k) ≠ 0)
    (u : FakeEllipticCurve.WithExtraLevel Λ N ℓ k) :
    ∃ (E' : FakeEllipticCurve Λ N k) (p : u.1.A ⟶ E'.A) (hp : p ≫ E'.f = u.1.f) (ψ : E'.A ⟶ u.1.A) (hψ : ψ ≫ u.1.f = E'.f),
      QProps u E' p hp ψ hψ := by
  classical
  obtain ⟨E, K⟩ := u
  obtain ⟨A, f, L, act, hact, p, hp, ψ, hψ, hcomm, hbundle, hdim, hact_hom, hact_one, hact_mul, hact_add, htrace,
      hp_hom, hequiv, hfin, hflat, hlfp, hsurj, hEt, hrank, hker, hψ_hom, hψ_lin, hψp, hpψ, huniv⟩ :=
    CerednikDrinfeld.QM.FakeEllipticCurve.exists_quotient_core_of_isAlgClosed k E hO ℓ hℓk K.K K.levK K.levK_closed
      K.levK_finite K.levK_flat K.levK_finitePresentation K.levK_one K.levK_sub K.levK_stable K.levK_torsion
  haveI := K.levK_closed
  haveI := E.lev_closed
  haveI := hfin
  have hdisj : ∀ {T : Scheme} (t : T ⟶ Spec (CommRingCat.of k)) (P : SchemeHomOver t E.f),
      FactorsThrough E.lev P → mapPt p hp P = L.one t → P = E.L.one t :=
    fun t P hC hpP => K.levK_disjoint t P ((hker t P).1 hpP) hC
  haveI : IsFinite (E.lev ≫ p) := inferInstance
  have hlevf : (E.lev ≫ p) ≫ f = E.lev ≫ E.f := by rw [Category.assoc, hp]
  let E' : FakeEllipticCurve Λ N k :=
    { A := A
      f := f
      L := L
      comm := hcomm
      bundle := hbundle
      dim_fibre := hdim
      act := act
      act_over := hact
      act_hom := hact_hom
      act_one := hact_one
      act_mul := hact_mul
      act_add := hact_add
      act_trace := htrace
      C := E.C
      lev := E.lev ≫ p
      lev_closed := IMGSUB.isClosedImmersion E.L L p hp hp_hom E.lev E.lev_sub hdisj
      lev_sub := fun t P Q hP hQ => IMGSUB.sub E.L L p hp hp_hom E.lev E.lev_sub t P Q hP hQ
      lev_one := fun t => IMGSUB.one E.L L p hp hp_hom E.lev E.lev_one t
      lev_torsion := fun t P hP => IMGSUB.torsion E.L L p hp hp_hom E.lev N E.lev_torsion t P hP
      lev_stable := fun x _ t P hP =>
        IMGSUB.stable p hp E.lev (E.act x) (E.act_over x) (act x) (hact x) (hequiv x).symm (E.lev_stable x) t P hP
      lev_finite := by rw [hlevf]; exact E.lev_finite
      lev_flat := by rw [hlevf]; exact E.lev_flat
      lev_finitePresentation := by rw [hlevf]; exact E.lev_finitePresentation
      lev_rank := fun s => by rw [hlevf]; exact E.lev_rank s
      lev_fibre := fun k' _ _ sk hN => by
        obtain ⟨e₀, he₀⟩ := E.lev_fibre k' sk hN
        obtain ⟨e₁, he₁⟩ := IMGSUB.exists_equiv E.L L p hp hp_hom E.lev E.lev_sub hdisj (geomPoint k' sk)
        refine ⟨e₀.trans e₁, fun x y => ?_⟩
        simp only [Equiv.trans_apply]
        rw [he₁, he₁, he₁, he₀, hp_hom] }
  refine ⟨E', p, hp, ψ, hψ,
    { hom_p := hp_hom, hom_ψ := hψ_hom, equiv := hequiv, ψlin := hψ_lin, fin := hfin, flat := hflat, lfp := hlfp, surj := hsurj,
      rank := fun y => by rw [hrank y]; exact K.levK_rank _, ker := hker, ψp := hψp, pψ := hpψ, univ := huniv,
      lev := fun t Q => IMGSUB.factorsThrough_iff p hp E.lev t Q }⟩

theorem factorsThrough_lev_nsmulPt {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} {N : ℕ} {S : Type} [CommRing S]
    (E : FakeEllipticCurve Λ N S) {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of S)) (n : ℕ) (P : SchemeHomOver t E.f)
    (hP : FactorsThrough E.lev P) : FactorsThrough E.lev (nsmulPt E.L t n P) := by
  induction n with
  | zero => exact E.lev_one t
  | succ n ih => exact (E.lev_sub t _ _ ih hP).1

end FLIP

namespace FLIP

theorem iso_compat {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} {N : ℕ} {k : Type} [Field k] {ℓ : ℕ} [NeZero ℓ]
    (u v : FakeEllipticCurve.WithExtraLevel Λ N ℓ k)
    (Eu : FakeEllipticCurve Λ N k) (pu : u.1.A ⟶ Eu.A) (hpu : pu ≫ Eu.f = u.1.f) (ψu : Eu.A ⟶ u.1.A) (hψu : ψu ≫ u.1.f = Eu.f)
    (hQu : QProps u Eu pu hpu ψu hψu) (Ku : Eu.ExtraLevel ℓ)
    (hKu : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of k)) (Q : SchemeHomOver t Eu.f),
      FactorsThrough Ku.levK Q ↔ mapPt ψu hψu Q = u.1.L.one t)
    (Ev : FakeEllipticCurve Λ N k) (pv : v.1.A ⟶ Ev.A) (hpv : pv ≫ Ev.f = v.1.f) (ψv : Ev.A ⟶ v.1.A) (hψv : ψv ≫ v.1.f = Ev.f)
    (hQv : QProps v Ev pv hpv ψv hψv) (Kv : Ev.ExtraLevel ℓ)
    (hKv : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of k)) (Q : SchemeHomOver t Ev.f),
      FactorsThrough Kv.levK Q ↔ mapPt ψv hψv Q = v.1.L.one t)
    (huv : FakeEllipticCurve.WithExtraLevel.Iso u v) :
    FakeEllipticCurve.WithExtraLevel.Iso (⟨Eu, Ku⟩ : FakeEllipticCurve.WithExtraLevel Λ N ℓ k) ⟨Ev, Kv⟩ := by
  classical
  obtain ⟨e, he, he_hom, he_act, he_lev, he_levK⟩ := huv
  have he' : e.inv ≫ u.1.f = v.1.f := by rw [← he, ← Category.assoc, e.inv_hom_id, Category.id_comp]
  have hee' : ∀ {T : Scheme.{0}} {t : T ⟶ Spec (CommRingCat.of k)} (P : SchemeHomOver t v.1.f),
      mapPt e.hom he (mapPt e.inv he' P) = P := by
    intro T t P; apply Subtype.ext; simp [mapPt]
  have he'e : ∀ {T : Scheme.{0}} {t : T ⟶ Spec (CommRingCat.of k)} (P : SchemeHomOver t u.1.f),
      mapPt e.inv he' (mapPt e.hom he P) = P := by
    intro T t P; apply Subtype.ext; simp [mapPt]
  have hehom : IsHom u.1.L v.1.L e.hom he := fun _ t P Q => he_hom t P Q
  have he'hom : IsHom v.1.L u.1.L e.inv he' := by
    intro T t P Q
    rw [← mapPt_iso_eq_iff e he, hee', he_hom, hee', hee']
  have he'_levK : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of k)) (P : SchemeHomOver t v.1.f),
      FactorsThrough v.2.levK P → FactorsThrough u.2.levK (mapPt e.inv he' P) := by
    intro T t P hP; rw [he_levK, hee']; exact hP
  have he'_act : ∀ x : ↥Λ, v.1.act x ≫ e.inv = e.inv ≫ u.1.act x := by
    intro x; rw [Iso.comp_inv_eq, Category.assoc, Iso.eq_inv_comp, he_act x]

  have hφ : (e.hom ≫ pv) ≫ Ev.f = u.1.f := by rw [Category.assoc, hpv, he]
  have hφ' : (e.inv ≫ pu) ≫ Eu.f = v.1.f := by rw [Category.assoc, hpu, he']
  have hpuhom : IsHom u.1.L Eu.L pu hpu := fun _ t P Q => hQu.hom_p t P Q
  have hpvhom : IsHom v.1.L Ev.L pv hpv := fun _ t P Q => hQv.hom_p t P Q
  obtain ⟨θ, ⟨hθp, hθhom⟩, hθuniq⟩ := hQu.univ Ev.A Ev.f Ev.L (e.hom ≫ pv) hφ
    (fun t P Q => (hehom.comp hpvhom) t P Q)
    (fun t P hP => by rw [mapPt_comp e.hom he pv hpv, hQv.ker]; exact (he_levK t P).1 hP)
  obtain ⟨θ', ⟨hθ'p, hθ'hom⟩, hθ'uniq⟩ := hQv.univ Eu.A Eu.f Eu.L (e.inv ≫ pu) hφ'
    (fun t P Q => (he'hom.comp hpuhom) t P Q)
    (fun t P hP => by rw [mapPt_comp e.inv he' pu hpu, hQu.ker]; exact he'_levK t P hP)
  have hθhom' : IsHom Eu.L Ev.L θ.1 θ.2 := fun _ t P Q => hθhom t P Q
  have hθ'hom' : IsHom Ev.L Eu.L θ'.1 θ'.2 := fun _ t P Q => hθ'hom t P Q

  have h1 : θ.1 ≫ θ'.1 = 𝟙 _ := by
    obtain ⟨χ, -, hχ⟩ := hQu.univ Eu.A Eu.f Eu.L pu hpu hQu.hom_p (fun t P hP => (hQu.ker t P).2 hP)
    have hA : (⟨θ.1 ≫ θ'.1, by rw [Category.assoc, θ'.2, θ.2]⟩ : SchemeHomOver Eu.f Eu.f) = χ :=
      hχ _ ⟨by rw [← Category.assoc, hθp, Category.assoc, hθ'p, ← Category.assoc, e.hom_inv_id, Category.id_comp],
        fun t P Q => (hθhom'.comp hθ'hom') t P Q⟩
    have hB : (⟨𝟙 _, Category.id_comp _⟩ : SchemeHomOver Eu.f Eu.f) = χ :=
      hχ _ ⟨by simp, fun t P Q => by simp only [mapPt_id]⟩
    exact congrArg Subtype.val (hA.trans hB.symm)
  have h2 : θ'.1 ≫ θ.1 = 𝟙 _ := by
    obtain ⟨χ, -, hχ⟩ := hQv.univ Ev.A Ev.f Ev.L pv hpv hQv.hom_p (fun t P hP => (hQv.ker t P).2 hP)
    have hA : (⟨θ'.1 ≫ θ.1, by rw [Category.assoc, θ.2, θ'.2]⟩ : SchemeHomOver Ev.f Ev.f) = χ :=
      hχ _ ⟨by rw [← Category.assoc, hθ'p, Category.assoc, hθp, ← Category.assoc, e.inv_hom_id, Category.id_comp],
        fun t P Q => (hθ'hom'.comp hθhom') t P Q⟩
    have hB : (⟨𝟙 _, Category.id_comp _⟩ : SchemeHomOver Ev.f Ev.f) = χ :=
      hχ _ ⟨by simp, fun t P Q => by simp only [mapPt_id]⟩
    exact congrArg Subtype.val (hA.trans hB.symm)
  let eθ : Eu.A ≅ Ev.A := ⟨θ.1, θ'.1, h1, h2⟩

  have hθpt : ∀ {T : Scheme.{0}} {t : T ⟶ Spec (CommRingCat.of k)} (P : SchemeHomOver t u.1.f),
      mapPt θ.1 θ.2 (mapPt pu hpu P) = mapPt pv hpv (mapPt e.hom he P) := by
    intro T t P; apply Subtype.ext; simp only [mapPt, Category.assoc, hθp]
  have hθ'pt : ∀ {T : Scheme.{0}} {t : T ⟶ Spec (CommRingCat.of k)} (P : SchemeHomOver t v.1.f),
      mapPt θ'.1 θ'.2 (mapPt pv hpv P) = mapPt pu hpu (mapPt e.inv he' P) := by
    intro T t P; apply Subtype.ext; simp only [mapPt, Category.assoc, hθ'p]
  have hθθ' : ∀ {T : Scheme.{0}} {t : T ⟶ Spec (CommRingCat.of k)} (Q : SchemeHomOver t Eu.f),
      mapPt θ'.1 θ'.2 (mapPt θ.1 θ.2 Q) = Q := by
    intro T t Q; apply Subtype.ext; simp only [mapPt, Category.assoc, h1, Category.comp_id]

  have hψθ : θ.1 ≫ ψv = ψu ≫ e.hom := by
    have hφ₂ : (pu ≫ ψu ≫ e.hom) ≫ v.1.f = u.1.f := by rw [Category.assoc, Category.assoc, he, hψu, hpu]
    have hψuhom : IsHom Eu.L u.1.L ψu hψu := fun _ t P Q => hQu.hom_ψ t P Q
    have hψvhom : IsHom Ev.L v.1.L ψv hψv := fun _ t P Q => hQv.hom_ψ t P Q
    obtain ⟨χ, -, hχ⟩ := hQu.univ v.1.A v.1.f v.1.L (pu ≫ ψu ≫ e.hom) hφ₂
      (fun t P Q => (hpuhom.comp (hψuhom.comp hehom (h := by rw [Category.assoc, he, hψu]))) t P Q)
      (fun t P hP => by
        rw [mapPt_comp pu hpu (ψu ≫ e.hom) (by rw [Category.assoc, he, hψu]), mapPt_comp ψu hψu e.hom he, hQu.ψp,
          u.2.levK_torsion t P hP]
        exact hehom.map_one t)
    have hA : (⟨ψu ≫ e.hom, by rw [Category.assoc, he, hψu]⟩ : SchemeHomOver Eu.f v.1.f) = χ :=
      hχ _ ⟨rfl, fun t P Q => (hψuhom.comp hehom) t P Q⟩
    have hB : (⟨θ.1 ≫ ψv, by rw [Category.assoc, hψv, θ.2]⟩ : SchemeHomOver Eu.f v.1.f) = χ := by
      refine hχ _ ⟨?_, fun t P Q => (hθhom'.comp hψvhom) t P Q⟩

      apply eq_of_mapPt_id_eq (hφ := by rw [Category.assoc, Category.assoc, hψv, θ.2, hpu]) (hψ := hφ₂)
      rw [mapPt_comp pu hpu (θ.1 ≫ ψv) (by rw [Category.assoc, hψv, θ.2]), mapPt_comp θ.1 θ.2 ψv hψv, hθpt,
        hQv.ψp, ← hehom.map_nsmulPt, ← hQu.ψp, ← mapPt_comp ψu hψu e.hom he (h := by rw [Category.assoc, he, hψu]),
        ← mapPt_comp pu hpu (ψu ≫ e.hom) (by rw [Category.assoc, he, hψu])]
    exact congrArg Subtype.val (hB.trans hA.symm)
  refine ⟨eθ, θ.2, hθhom, ?_, ?_, ?_⟩
  ·
    intro x
    have hφ₃ : (u.1.act x ≫ e.hom ≫ pv) ≫ Ev.f = u.1.f := by
      rw [Category.assoc, Category.assoc, hpv, he, u.1.act_over]
    have hacthom : IsHom u.1.L u.1.L (u.1.act x) (u.1.act_over x) := fun _ t P Q => u.1.act_hom x t P Q
    obtain ⟨χ, -, hχ⟩ := hQu.univ Ev.A Ev.f Ev.L (u.1.act x ≫ e.hom ≫ pv) hφ₃
      (fun t P Q => (hacthom.comp (hehom.comp hpvhom (h := hφ))) t P Q)
      (fun t P hP => by
        rw [mapPt_comp (u.1.act x) (u.1.act_over x) (e.hom ≫ pv) hφ, mapPt_comp e.hom he pv hpv, hQv.ker]
        exact (he_levK t _).1 (u.2.levK_stable x t P hP))
    have hA : (⟨Eu.act x ≫ θ.1, by rw [Category.assoc, θ.2, Eu.act_over]⟩ : SchemeHomOver Eu.f Ev.f) = χ :=
      hχ _ ⟨by rw [← Category.assoc, ← hQu.equiv x, Category.assoc, hθp],
        fun t P Q => ((show IsHom Eu.L Eu.L (Eu.act x) (Eu.act_over x) from fun _ t P Q => Eu.act_hom x t P Q).comp hθhom') t P Q⟩
    have hB : (⟨θ.1 ≫ Ev.act x, by rw [Category.assoc, Ev.act_over, θ.2]⟩ : SchemeHomOver Eu.f Ev.f) = χ :=
      hχ _ ⟨by rw [← Category.assoc, hθp, Category.assoc, ← hQv.equiv x, ← Category.assoc, ← he_act x, Category.assoc],
        fun t P Q => (hθhom'.comp (show IsHom Ev.L Ev.L (Ev.act x) (Ev.act_over x) from fun _ t P Q => Ev.act_hom x t P Q)) t P Q⟩
    exact congrArg Subtype.val (hA.trans hB.symm)
  ·
    have fwd : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of k)) (Q : SchemeHomOver t Eu.f),
        FactorsThrough Eu.lev Q → FactorsThrough Ev.lev (mapPt θ.1 θ.2 Q) := by
      intro T t Q hQ
      obtain ⟨P, hP, rfl⟩ := (hQu.lev t Q).1 hQ
      rw [hθpt]
      exact (hQv.lev t _).2 ⟨_, (he_lev t P).1 hP, rfl⟩
    have bwd : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of k)) (Q : SchemeHomOver t Ev.f),
        FactorsThrough Ev.lev Q → FactorsThrough Eu.lev (mapPt θ'.1 θ'.2 Q) := by
      intro T t Q hQ
      obtain ⟨P, hP, rfl⟩ := (hQv.lev t Q).1 hQ
      rw [hθ'pt]
      refine (hQu.lev t _).2 ⟨_, ?_, rfl⟩
      rw [he_lev, hee']; exact hP
    intro T t Q
    exact ⟨fwd t Q, fun h => by rw [← hθθ' Q]; exact bwd t _ h⟩
  ·
    intro T t Q
    show FactorsThrough Ku.levK Q ↔ FactorsThrough Kv.levK (mapPt θ.1 θ.2 Q)
    rw [hKu, hKv, ← mapPt_comp θ.1 θ.2 ψv hψv (h := by rw [Category.assoc, hψv, θ.2])]
    rw [show mapPt (θ.1 ≫ ψv) _ Q = mapPt (ψu ≫ e.hom) (by rw [Category.assoc, he, hψu]) Q from by
      apply Subtype.ext; simp only [mapPt, hψθ]]
    rw [mapPt_comp ψu hψu e.hom he, ← hehom.map_one t, mapPt_iso_eq_iff]

end FLIP

namespace FLIP

theorem nsmulPt_eq_nsmul {R : Type} [CommRing R] {A : Scheme.{0}} {f : A ⟶ Spec (CommRingCat.of R)}
    (L : RelativeGroupLaw R f) {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of R)) (n : ℕ) (P : SchemeHomOver t f) :
    nsmulPt L t n P = L.nsmul t n P := by
  induction n with
  | zero => rfl
  | succ n ih => rw [GoodReductionJacobian.RelativeGroupLaw.nsmul_succ, ← ih]; rfl

theorem nsmulPt_eq_pow {R : Type} [CommRing R] {A : Scheme.{0}} {f : A ⟶ Spec (CommRingCat.of R)}
    (L : RelativeGroupLaw R f) {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of R)) (n : ℕ) (P : SchemeHomOver t f) :
    letI := L.pointGroup t
    nsmulPt L t n P = P ^ n := by
  letI := L.pointGroup t
  induction n with
  | zero => rfl
  | succ n ih => rw [pow_succ, ← ih]; rfl

theorem flip_flip {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} {N : ℕ} [NeZero N] {k : Type} [Field k] [IsAlgClosed k]
    (hO : IsOrder Λ) {ℓ : ℕ} [Fact ℓ.Prime] (hℓk : (ℓ : k) ≠ 0) (hℓN : ¬ ℓ ∣ N)
    (u : FakeEllipticCurve.WithExtraLevel Λ N ℓ k)
    (E₁ : FakeEllipticCurve Λ N k) (p₁ : u.1.A ⟶ E₁.A) (hp₁ : p₁ ≫ E₁.f = u.1.f) (ψ₁ : E₁.A ⟶ u.1.A) (hψ₁ : ψ₁ ≫ u.1.f = E₁.f)
    (hQ₁ : QProps u E₁ p₁ hp₁ ψ₁ hψ₁) (K₁ : E₁.ExtraLevel ℓ)
    (hK₁ : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of k)) (Q : SchemeHomOver t E₁.f),
      FactorsThrough K₁.levK Q ↔ mapPt ψ₁ hψ₁ Q = u.1.L.one t)
    (E₂ : FakeEllipticCurve Λ N k) (p₂ : E₁.A ⟶ E₂.A) (hp₂ : p₂ ≫ E₂.f = E₁.f) (ψ₂ : E₂.A ⟶ E₁.A) (hψ₂ : ψ₂ ≫ E₁.f = E₂.f)
    (hQ₂ : QProps (⟨E₁, K₁⟩ : FakeEllipticCurve.WithExtraLevel Λ N ℓ k) E₂ p₂ hp₂ ψ₂ hψ₂) (K₂ : E₂.ExtraLevel ℓ)
    (hK₂ : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of k)) (R : SchemeHomOver t E₂.f),
      FactorsThrough K₂.levK R ↔ mapPt ψ₂ hψ₂ R = E₁.L.one t) :
    FakeEllipticCurve.WithExtraLevel.Iso (⟨E₂, K₂⟩ : FakeEllipticCurve.WithExtraLevel Λ N ℓ k) u := by
  classical
  have hℓP : ℓ.Prime := Fact.out
  have hℓΛ : ((ℓ : ℚ) : ℍ[ℚ, a, b]) ∈ Λ := by
    have : ((ℓ : ℚ) : ℍ[ℚ, a, b]) = (ℓ : ℤ) • (1 : ℍ[ℚ, a, b]) := by rw [zsmul_eq_mul, mul_one]; norm_cast
    rw [this]; exact Λ.smul_mem _ hO.one_mem
  have hp₁hom : IsHom u.1.L E₁.L p₁ hp₁ := fun _ t P Q => hQ₁.hom_p t P Q
  have hψ₁hom : IsHom E₁.L u.1.L ψ₁ hψ₁ := fun _ t P Q => hQ₁.hom_ψ t P Q
  have hp₂hom : IsHom E₁.L E₂.L p₂ hp₂ := fun _ t P Q => hQ₂.hom_p t P Q
  have hψ₂hom : IsHom E₂.L E₁.L ψ₂ hψ₂ := fun _ t P Q => hQ₂.hom_ψ t P Q

  have hψp₁ : ψ₁ ≫ p₁ = E₁.act ⟨_, hℓΛ⟩ := by
    have h := congrArg Subtype.val ((hQ₁.pψ E₁.f ⟨𝟙 _, Category.id_comp _⟩).trans
      (CerednikDrinfeld.QM.FakeEllipticCurve.pushPt_act_natCast_eq_nsmulPt E₁ hO.one_mem ℓ hℓΛ E₁.f ⟨𝟙 _, Category.id_comp _⟩).symm)
    simpa [mapPt, pushPt] using h
  have hpψ₂ : p₂ ≫ ψ₂ = E₁.act ⟨_, hℓΛ⟩ := by
    have h := congrArg Subtype.val ((hQ₂.ψp E₁.f ⟨𝟙 _, Category.id_comp _⟩).trans
      (CerednikDrinfeld.QM.FakeEllipticCurve.pushPt_act_natCast_eq_nsmulPt E₁ hO.one_mem ℓ hℓΛ E₁.f ⟨𝟙 _, Category.id_comp _⟩).symm)
    simpa [mapPt, pushPt] using h
  have hactℓhom : IsHom E₁.L E₁.L (E₁.act ⟨_, hℓΛ⟩) (E₁.act_over _) := fun _ t P Q => E₁.act_hom _ t P Q
  have hactℓK : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of k)) (Q : SchemeHomOver t E₁.f),
      FactorsThrough K₁.levK Q → mapPt (E₁.act ⟨_, hℓΛ⟩) (E₁.act_over _) Q = E₁.L.one t := by
    intro T t Q hQ
    rw [show mapPt (E₁.act ⟨_, hℓΛ⟩) (E₁.act_over _) Q = pushPt (E₁.act ⟨_, hℓΛ⟩) (E₁.act_over _) Q from rfl,
      CerednikDrinfeld.QM.FakeEllipticCurve.pushPt_act_natCast_eq_nsmulPt E₁ hO.one_mem ℓ hℓΛ t Q]
    exact K₁.levK_torsion t Q hQ

  obtain ⟨θ, ⟨hθp, hθhom⟩, -⟩ := hQ₂.univ u.1.A u.1.f u.1.L ψ₁ hψ₁ hQ₁.hom_ψ (fun t Q hQ => (hK₁ t Q).1 hQ)
  have hθhom' : IsHom E₂.L u.1.L θ.1 θ.2 := fun _ t P Q => hθhom t P Q

  have hθpp : θ.1 ≫ p₁ ≫ p₂ = E₂.act ⟨_, hℓΛ⟩ := by
    obtain ⟨χ, -, hχ⟩ := hQ₂.univ E₂.A E₂.f E₂.L (E₁.act ⟨_, hℓΛ⟩ ≫ p₂) (by rw [Category.assoc, hp₂, E₁.act_over])
      (fun t P Q => (hactℓhom.comp hp₂hom) t P Q)
      (fun t Q hQ => by rw [mapPt_comp (E₁.act _) (E₁.act_over _) p₂ hp₂, hactℓK t Q hQ]; exact hp₂hom.map_one t)
    have hA : (⟨θ.1 ≫ p₁ ≫ p₂, by rw [Category.assoc, Category.assoc, hp₂, hp₁, θ.2]⟩ : SchemeHomOver E₂.f E₂.f) = χ :=
      hχ _ ⟨by rw [← Category.assoc, hθp, ← Category.assoc, hψp₁],
        fun t P Q => (hθhom'.comp (hp₁hom.comp hp₂hom (h := by rw [Category.assoc, hp₂, hp₁]))) t P Q⟩
    have hB : (⟨E₂.act ⟨_, hℓΛ⟩, E₂.act_over _⟩ : SchemeHomOver E₂.f E₂.f) = χ :=
      hχ _ ⟨(hQ₂.equiv _).symm, fun t P Q => E₂.act_hom _ t P Q⟩
    exact congrArg Subtype.val (hA.trans hB.symm)
  have hψ₂θ : ψ₂ = θ.1 ≫ p₁ := by
    obtain ⟨χ, -, hχ⟩ := hQ₂.univ E₁.A E₁.f E₁.L (E₁.act ⟨_, hℓΛ⟩) (E₁.act_over _) (E₁.act_hom _) hactℓK
    have hA : (⟨ψ₂, hψ₂⟩ : SchemeHomOver E₂.f E₁.f) = χ := hχ _ ⟨hpψ₂, hQ₂.hom_ψ⟩
    have hB : (⟨θ.1 ≫ p₁, by rw [Category.assoc, hp₁, θ.2]⟩ : SchemeHomOver E₂.f E₁.f) = χ :=
      hχ _ ⟨by rw [← Category.assoc, hθp, hψp₁], fun t P Q => (hθhom'.comp hp₁hom) t P Q⟩
    exact congrArg Subtype.val (hA.trans hB.symm)

  haveI := hQ₂.fin; haveI := hQ₂.surj
  have hθact : ∀ x : ↥Λ, E₂.act x ≫ θ.1 = θ.1 ≫ u.1.act x := by
    intro x
    have hxhom : IsHom E₁.L E₁.L (E₁.act x) (E₁.act_over x) := fun _ t P Q => E₁.act_hom x t P Q
    obtain ⟨χ, -, hχ⟩ := hQ₂.univ u.1.A u.1.f u.1.L (E₁.act x ≫ ψ₁) (by rw [Category.assoc, hψ₁, E₁.act_over])
      (fun t P Q => (hxhom.comp hψ₁hom) t P Q)
      (fun t Q hQ => by rw [mapPt_comp (E₁.act x) (E₁.act_over x) ψ₁ hψ₁]; exact (hK₁ t _).1 (K₁.levK_stable x t Q hQ))
    have hA : (⟨E₂.act x ≫ θ.1, by rw [Category.assoc, θ.2, E₂.act_over]⟩ : SchemeHomOver E₂.f u.1.f) = χ :=
      hχ _ ⟨by rw [← Category.assoc, ← hQ₂.equiv x, Category.assoc, hθp],
        fun t P Q => ((show IsHom E₂.L E₂.L (E₂.act x) (E₂.act_over x) from fun _ t P Q => E₂.act_hom x t P Q).comp hθhom') t P Q⟩
    have hB : (⟨θ.1 ≫ u.1.act x, by rw [Category.assoc, u.1.act_over, θ.2]⟩ : SchemeHomOver E₂.f u.1.f) = χ :=
      hχ _ ⟨by rw [← Category.assoc, hθp, hQ₁.ψlin x],
        fun t P Q => (hθhom'.comp (show IsHom u.1.L u.1.L (u.1.act x) (u.1.act_over x) from fun _ t P Q => u.1.act_hom x t P Q)) t P Q⟩
    exact congrArg Subtype.val (hA.trans hB.symm)
  have hpp : (p₁ ≫ p₂) ≫ E₂.f = u.1.f := by rw [Category.assoc, hp₂, hp₁]
  haveI hθiso : IsIso θ.1 :=
    CerednikDrinfeld.QM.FakeEllipticCurve.isIso_of_forall_mapPt_eq_one_imp_eq_one k E₂ u.1 θ.1 θ.2 hθhom hθact
      (p₁ ≫ p₂) hpp ℓ hℓP.pos hℓk
      (fun t R => by
        rw [← mapPt_comp θ.1 θ.2 (p₁ ≫ p₂) hpp (h := by rw [Category.assoc, hpp, θ.2])]
        rw [show mapPt (θ.1 ≫ p₁ ≫ p₂) _ R = pushPt (E₂.act ⟨_, hℓΛ⟩) (E₂.act_over _) R from by
          apply Subtype.ext; simp only [mapPt, pushPt, hθpp]]
        exact CerednikDrinfeld.QM.FakeEllipticCurve.pushPt_act_natCast_eq_nsmulPt E₂ hO.one_mem ℓ hℓΛ t R)
      (fun t P => by
        rw [mapPt_comp p₁ hp₁ p₂ hp₂, ← mapPt_comp p₂ hp₂ θ.1 θ.2 (h := by rw [Category.assoc, θ.2, hp₂])]
        rw [show mapPt (p₂ ≫ θ.1) _ (mapPt p₁ hp₁ P) = mapPt ψ₁ hψ₁ (mapPt p₁ hp₁ P) from by
          apply Subtype.ext; simp only [mapPt, hθp]]
        exact hQ₁.ψp t P)
      (fun R hR => by

        haveI : Smooth E₂.f := E₂.bundle.smooth
        haveI : ConnectedSpace E₂.A := by
          rw [connectedSpace_iff_univ]
          let s₀ : ↥(Spec (CommRingCat.of k)) := ⟨⊥, Ideal.isPrime_bot⟩
          have hsub : ∀ s : ↥(Spec (CommRingCat.of k)), s = s₀ := fun s =>
            PrimeSpectrum.ext (Ideal.eq_bot_of_prime s.asIdeal)
          have hs : E₂.f.base ⁻¹' {s₀} = Set.univ := Set.eq_univ_of_forall fun x => hsub _
          rw [← hs]
          exact E₂.bundle.connectedFibres s₀
        obtain ⟨R₀, hR₀⟩ := GoodReductionJacobian.RelativeGroupLaw.nsmul_surjective_of_isAlgClosed_of_connectedSpace
          E₂.L E₂.comm ℓ (isUnit_iff_ne_zero.2 hℓk) R
        have hRQ : R = mapPt p₂ hp₂ (mapPt p₁ hp₁ (mapPt θ.1 θ.2 R₀)) := by
          rw [← hR₀, ← nsmulPt_eq_nsmul,
            ← CerednikDrinfeld.QM.FakeEllipticCurve.pushPt_act_natCast_eq_nsmulPt E₂ hO.one_mem ℓ hℓΛ _ R₀]
          apply Subtype.ext
          simp only [pushPt, mapPt, Category.assoc, ← hθpp]
        set Q := mapPt p₁ hp₁ (mapPt θ.1 θ.2 R₀) with hQdef
        have h1 : mapPt ψ₁ hψ₁ Q = u.1.L.one _ := by
          rw [← hR, hRQ, ← mapPt_comp p₂ hp₂ θ.1 θ.2 (h := by rw [Category.assoc, θ.2, hp₂])]
          apply Subtype.ext; simp only [mapPt, hθp]
        rw [hRQ]
        exact (hQ₂.ker _ Q).2 ((hK₁ _ Q).2 h1))
  let eθ : E₂.A ≅ u.1.A := asIso θ.1

  have hθpt : ∀ {T : Scheme.{0}} {t : T ⟶ Spec (CommRingCat.of k)} (P : SchemeHomOver t u.1.f),
      mapPt θ.1 θ.2 (mapPt p₂ hp₂ (mapPt p₁ hp₁ P)) = nsmulPt u.1.L t ℓ P := by
    intro T t P
    rw [← hQ₁.ψp t P, ← mapPt_comp p₂ hp₂ θ.1 θ.2 (h := by rw [Category.assoc, θ.2, hp₂])]
    apply Subtype.ext; simp only [mapPt, hθp]
  refine ⟨eθ, θ.2, hθhom, hθact, ?_, ?_⟩
  ·
    intro T t R
    constructor
    · intro hR
      obtain ⟨Q, hQ, rfl⟩ := (hQ₂.lev t R).1 hR
      obtain ⟨P, hP, rfl⟩ := (hQ₁.lev t Q).1 hQ
      show FactorsThrough u.1.lev (mapPt θ.1 θ.2 (mapPt p₂ hp₂ (mapPt p₁ hp₁ P)))
      rw [hθpt]
      exact factorsThrough_lev_nsmulPt u.1 t ℓ P hP
    · intro hR

      letI := u.1.L.pointGroup t
      let C' : Subgroup (SchemeHomOver t u.1.f) :=
        { carrier := {P | FactorsThrough u.1.lev P}
          one_mem' := u.1.lev_one t
          mul_mem' := fun {P Q} hP hQ => (u.1.lev_sub t P Q hP hQ).1
          inv_mem' := fun {P} hP => (u.1.lev_sub t P P hP hP).2 }
      have hcC : mapPt θ.1 θ.2 R ∈ C' := hR
      have hcN : mapPt θ.1 θ.2 R ^ N = 1 := by rw [← nsmulPt_eq_pow]; exact u.1.lev_torsion t _ hR
      have hcop : Nat.Coprime ℓ N := (Nat.Prime.coprime_iff_not_dvd hℓP).2 hℓN
      obtain ⟨za, zb, hab⟩ := Nat.isCoprime_iff_coprime.2 hcop
      have hc1 : mapPt θ.1 θ.2 R = (mapPt θ.1 θ.2 R ^ za) ^ ℓ := by
        have h : mapPt θ.1 θ.2 R ^ (za * (ℓ : ℤ) + zb * (N : ℤ)) = mapPt θ.1 θ.2 R := by rw [hab, zpow_one]
        rw [← zpow_natCast, ← zpow_mul]
        conv_lhs => rw [← h]
        rw [zpow_add, mul_comm zb, zpow_mul _ (N : ℤ), zpow_natCast, hcN, one_zpow, mul_one]
      have haC : mapPt θ.1 θ.2 R ^ za ∈ C' := C'.zpow_mem hcC za
      have key : mapPt θ.1 θ.2 (mapPt p₂ hp₂ (mapPt p₁ hp₁ (mapPt θ.1 θ.2 R ^ za))) = mapPt θ.1 θ.2 R := by
        rw [hθpt, nsmulPt_eq_pow]; exact hc1.symm
      have hR' : mapPt p₂ hp₂ (mapPt p₁ hp₁ (mapPt θ.1 θ.2 R ^ za)) = R := (mapPt_iso_eq_iff eθ θ.2 _ _).1 key
      rw [← hR']
      exact (hQ₂.lev t _).2 ⟨_, (hQ₁.lev t _).2 ⟨_, haC, rfl⟩, rfl⟩
  ·
    intro T t R
    show FactorsThrough K₂.levK R ↔ FactorsThrough u.2.levK (mapPt θ.1 θ.2 R)
    rw [hK₂, ← hQ₁.ker, ← mapPt_comp θ.1 θ.2 p₁ hp₁ (h := by rw [Category.assoc, hp₁, θ.2])]
    constructor <;> intro h <;> · convert h using 2; all_goals exact hψ₂θ.symm

end FLIP

theorem solution
    {q q' : ℕ} [Fact q.Prime] [Fact q'.Prime] (hqq' : q' ≠ q)
    {a b : ℚ} (hB : IsIndefiniteRamifiedExactlyAt a b q q')
    (Λ : Submodule ℤ ℍ[ℚ, a, b]) (hΛ : IsMaximalOrder Λ) {N : ℕ} [NeZero N]
    (ℓ : ℕ) [Fact ℓ.Prime] (hℓq : ℓ ≠ q) (hℓq' : ℓ ≠ q') (hℓN : ¬ ℓ ∣ N) :
    ∃ fl : FakeEllipticCurve.WithExtraLevel Λ N ℓ (AlgebraicClosure ℚ) →
        FakeEllipticCurve.WithExtraLevel Λ N ℓ (AlgebraicClosure ℚ),
      (∀ u : FakeEllipticCurve.WithExtraLevel Λ N ℓ (AlgebraicClosure ℚ),
        FakeEllipticCurve.IsLevelIsogeny ℓ u (fl u).1) ∧
      (∀ u v : FakeEllipticCurve.WithExtraLevel Λ N ℓ (AlgebraicClosure ℚ),
        FakeEllipticCurve.WithExtraLevel.Iso u v → FakeEllipticCurve.WithExtraLevel.Iso (fl u) (fl v)) ∧
      (∀ u : FakeEllipticCurve.WithExtraLevel Λ N ℓ (AlgebraicClosure ℚ),
        FakeEllipticCurve.WithExtraLevel.Iso (fl (fl u)) u) := by
  classical
  have hO : IsOrder Λ := hΛ.1
  have hℓP : ℓ.Prime := Fact.out
  have hℓk : (ℓ : AlgebraicClosure ℚ) ≠ 0 := by exact_mod_cast hℓP.ne_zero
  have hNk : (N : AlgebraicClosure ℚ) ≠ 0 := by exact_mod_cast NeZero.ne N

  choose E' p hp ψ hψ hQ using fun u : FakeEllipticCurve.WithExtraLevel Λ N ℓ (AlgebraicClosure ℚ) =>
    FLIP.exists_quot hO (AlgebraicClosure ℚ) ℓ hℓk u

  have hp_lev : ∀ (u : FakeEllipticCurve.WithExtraLevel Λ N ℓ (AlgebraicClosure ℚ)) {T : Scheme.{0}}
      (t : T ⟶ Spec (CommRingCat.of (AlgebraicClosure ℚ))) (P : SchemeHomOver t u.1.f),
      FactorsThrough u.1.lev P → FactorsThrough (E' u).lev (mapPt (p u) (hp u) P) :=
    fun u _ t P hP => ((hQ u).lev t _).2 ⟨P, hP, rfl⟩
  have hψ_lev : ∀ (u : FakeEllipticCurve.WithExtraLevel Λ N ℓ (AlgebraicClosure ℚ)) {T : Scheme.{0}}
      (t : T ⟶ Spec (CommRingCat.of (AlgebraicClosure ℚ))) (Q : SchemeHomOver t (E' u).f),
      FactorsThrough (E' u).lev Q → FactorsThrough u.1.lev (mapPt (ψ u) (hψ u) Q) := by
    intro u T t Q hQ'
    obtain ⟨P, hP, rfl⟩ := ((hQ u).lev t Q).1 hQ'
    rw [(hQ u).ψp]
    exact FLIP.factorsThrough_lev_nsmulPt u.1 t ℓ P hP

  have hK : ∀ u : FakeEllipticCurve.WithExtraLevel Λ N ℓ (AlgebraicClosure ℚ), ∃ K' : (E' u).ExtraLevel ℓ,
      (∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of (AlgebraicClosure ℚ))) (Q : SchemeHomOver t (E' u).f),
        FactorsThrough K'.levK Q ↔ mapPt (ψ u) (hψ u) Q = u.1.L.one t) ∧
      FakeEllipticCurve.IsLevelIsogeny ℓ (⟨E' u, K'⟩ : FakeEllipticCurve.WithExtraLevel Λ N ℓ (AlgebraicClosure ℚ)) u.1 := by
    intro u
    haveI := (hQ u).fin; haveI := (hQ u).flat; haveI := (hQ u).lfp; haveI := (hQ u).surj
    obtain ⟨hkfin, hklfp, hkrank⟩ :=
      CerednikDrinfeld.QM.FakeEllipticCurve.isFinite_and_finrank_kernel_eq_of_comp_eq_nsmulPt_of_finrank_eq
        (AlgebraicClosure ℚ) ℓ u.1 (E' u) (p u) (hp u) (ψ u) (hψ u) (hQ u).hom_p (hQ u).hom_ψ (hQ u).ψp
        (hQ u).fin (hQ u).flat (hQ u).lfp (hQ u).surj (hQ u).rank
    have hfib := CerednikDrinfeld.QM.FakeEllipticCurve.exists_zmod_prod_equiv_factorsThrough_kernel_dual_of_not_dvd
      hqq' hB Λ hΛ ℓ hℓq hℓq' (AlgebraicClosure ℚ) hℓk hNk hℓN u (E' u) (p u) (hp u) (ψ u) (hψ u)
      (hQ u).hom_p (hQ u).hom_ψ (hQ u).equiv (hQ u).ψlin (hQ u).ψp (hQ u).pψ (hQ u).ker (hp_lev u)
    exact CerednikDrinfeld.QM.FakeEllipticCurve.exists_extraLevel_isLevelIsogeny_of_finrank_kernel_eq
      (AlgebraicClosure ℚ) ℓ hℓN hO (E' u) u.1 (ψ u) (hψ u) (p u) (hp u) (hQ u).hom_ψ (hQ u).hom_p (hQ u).ψlin (hQ u).equiv
      (hQ u).pψ (hQ u).ψp (hψ_lev u) hkfin hklfp hkrank hfib
  choose K' hK'pts hK'iso using hK
  refine ⟨fun u => ⟨E' u, K' u⟩, ?_, ?_, ?_⟩
  ·
    intro u
    refine ⟨p u, hp u, ψ u, hψ u, (hQ u).hom_p, (hQ u).hom_ψ, (hQ u).equiv, (hQ u).ψlin, ?_, (hQ u).ker, hp_lev u⟩
    intro hℓ'
    constructor
    · have h := congrArg Subtype.val (((hQ u).ψp u.1.f ⟨𝟙 _, Category.id_comp _⟩).trans
        (CerednikDrinfeld.QM.FakeEllipticCurve.pushPt_act_natCast_eq_nsmulPt u.1 hO.one_mem ℓ hℓ' u.1.f ⟨𝟙 _, Category.id_comp _⟩).symm)
      simpa [mapPt, pushPt] using h
    · have h := congrArg Subtype.val (((hQ u).pψ (E' u).f ⟨𝟙 _, Category.id_comp _⟩).trans
        (CerednikDrinfeld.QM.FakeEllipticCurve.pushPt_act_natCast_eq_nsmulPt (E' u) hO.one_mem ℓ hℓ' (E' u).f ⟨𝟙 _, Category.id_comp _⟩).symm)
      simpa [mapPt, pushPt] using h
  ·
    intro u v huv
    haveI : NeZero ℓ := ⟨hℓP.ne_zero⟩
    exact FLIP.iso_compat u v (E' u) (p u) (hp u) (ψ u) (hψ u) (hQ u) (K' u) (hK'pts u)
      (E' v) (p v) (hp v) (ψ v) (hψ v) (hQ v) (K' v) (hK'pts v) huv
  ·
    intro u
    exact FLIP.flip_flip hO hℓk hℓN u (E' u) (p u) (hp u) (ψ u) (hψ u) (hQ u) (K' u) (hK'pts u)
      (E' ⟨E' u, K' u⟩) (p ⟨E' u, K' u⟩) (hp ⟨E' u, K' u⟩) (ψ ⟨E' u, K' u⟩) (hψ ⟨E' u, K' u⟩) (hQ ⟨E' u, K' u⟩)
      (K' ⟨E' u, K' u⟩) (hK'pts ⟨E' u, K' u⟩)

end S_CerednikDrinfeld_QM_FakeEllipticCurve_WithExtraLevel_exists_flip_of_not_dvd
end P2MW
export P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_WithExtraLevel_exists_flip_of_not_dvd (solution)
