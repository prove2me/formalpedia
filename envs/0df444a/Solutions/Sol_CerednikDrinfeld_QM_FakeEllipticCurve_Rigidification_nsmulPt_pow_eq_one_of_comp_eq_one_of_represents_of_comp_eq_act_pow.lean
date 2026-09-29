-- Prove2me | solution 1 for CerednikDrinfeld.QM.FakeEllipticCurve.Rigidification.nsmulPt_pow_eq_one_of_comp_eq_one_of_represents_of_comp_eq_act_pow
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.837917+00:00
-- url     : https://prove2.me/submissions/0a770ef2-4d63-51e1-b970-4347fb562f3f

import Definitions.Def_CerednikDrinfeld_QMRigidification
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawKernel
import Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_exists_isNilpotent_isInfinitesimal_of_nsmulPt_pow_eq_one_of_one_mem
import Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_pushPt_act_natCast_eq_nsmulPt
import Theorems.Thm_MvFormalGroup_nilEval_subst_of_mem
import Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_IsPullbackVia_exists_isFormalModuleVia_map_and_comp_eq
import Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_apply_nilEval_natCast_eq_mapPt_act_of_isFormalModuleVia
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_Rigidification_nsmulPt_pow_eq_one_of_comp_eq_one_of_represents_of_comp_eq_act_pow
p2m_attr_erase "instance" "instTopologicallyFGOfFiniteType GoodReductionJacobian.RelativeGroupLaw.isIso_endKerStr_schemeHomOverId AlgebraicGeometry.Scheme.PresheafOfModules.symmetricCategory SheafOfModules.instFaithfulRingSheafPModToPMod SheafOfModules.symmetricCategory AlgebraicGeometry.Scheme.PresheafOfModules.monoidalCategory AlgebraicGeometry.Scheme.PresheafOfModules.monoidalClosed SheafOfModules.instFullRingSheafPModToPMod SheafOfModules.monoidalCategory AlgebraicGeometry.Scheme.Modules.symmetricCategory SheafOfModules.monoidalClosed SheafOfModules.instIsLocalizationPModRingSheafSheafifyFunctorPresheafW SheafOfModules.sheafifyFunctor_monoidal AlgebraicGeometry.Scheme.Modules.monoidalClosed AlgebraicGeometry.instMonoidalPresheafOfModulesModulesSheafify AlgebraicGeometry.Scheme.Modules.monoidalCategory PresheafOfModules.instMonoidalClosed PresheafOfModules.InternalHom.instModuleCarrierObjOppositeCommRingCatSubtypePiFamilyMemAddSubgroupNaturalFamilies PresheafOfModules.InternalHom.instModuleCarrierObjOppositeRingCatCompCommRingCatForget₂RingHomCarrierCarrierAbPresheaf PresheafOfModules.InternalHom.instSMulCarrierObjOppositeCommRingCatSubtypePiFamilyMemAddSubgroupNaturalFamilies AlgebraicGeometry.Scheme.Hom.opensMapFinal AlgebraicGeometry.RelPicard.RigidifiedLineBundle.setoid AlgebraicGeometry.RelPicard.RigidifiedLineBundle.instInhabited AlgebraicGeometry.OModulePresheaf.isScalarTower AlgebraicGeometry.Scheme.OrderedAffineCover.instLinearOrder AlgebraicGeometry.OModulePresheaf.module AlgebraicGeometry.Scheme.OrderedAffineCover.instFintype AlgebraicGeometry.Scheme.OrderedAffineCover.instFintypeIdx AlgebraicGeometry.OModulePresheaf.addCommGroup AlgebraicGeometry.Scheme.OrderedAffineCover.instDecidableEqIdx AlgebraicGeometry.OModulePresheaf.moduleSections TwoChartCech.Sections.M0_moduleA TwoChartCech.Sections.M1_module TwoChartCech.Cover.A01_algebra TwoChartCech.Cover.A0_algebra TwoChartCech.Cover.A1_commRing TwoChartCech.Cover.A1_algebra TwoChartCech.Sections.M01_module TwoChartCech.Sections.M0_addCommGroup TwoChartCech.Sections.M0_tower"
p2m_attr_erase "instance" "TwoChartCech.Sections.M01_addCommGroup TwoChartCech.Cover.A0_commRing TwoChartCech.Sections.M1_tower TwoChartCech.Sections.M01_moduleA TwoChartCech.Sections.M0_module TwoChartCech.Sections.M1_moduleA TwoChartCech.Sections.M1_addCommGroup TwoChartCech.Cover.A01_commRing TwoChartCech.Sections.M01_tower CoherentBaseChange.TwoTermComplex.C0_module CoherentBaseChange.TwoTermComplex.C0_addCommGroup CoherentBaseChange.TwoTermComplex.C1_module CoherentBaseChange.TwoTermComplex.C1_addCommGroup CoherentBaseChange.TwoTermComplex.C0_free CoherentBaseChange.TwoTermComplex.C1_finite CoherentBaseChange.TwoTermComplex.C0_finite CoherentBaseChange.TwoTermComplex.C1_free AlgebraicGeometry.OModulePresheaf.instSubsingletonObjZero AlgebraicGeometry.Scheme.Modules.preservesBinaryProducts_opensMap AlgebraicGeometry.Scheme.Modules.pullback_monoidal AlgebraicGeometry.Scheme.Modules.sheafify_isLocalization' AlgebraicGeometry.Scheme.Modules.preservesTerminal_opensMap AlgebraicGeometry.Scheme.Modules.pullback₀_monoidal AlgebraicGeometry.Scheme.Modules.preservesFiniteProducts_opensMap AlgebraicGeometry.Scheme.Modules.instLiftingPresheafOfModulesSheafifyPresheafWOpensCarrierCarrierCommRingCatGrothendieckTopologyObjFunctorOppositeIsSheafSheafCompPullback₀Pullback PresheafOfModules.PullbackMonoidal.pullback_monoidal PresheafOfModules.PullbackMonoidal.isIso_δ PresheafOfModules.pushforward_laxMonoidal PresheafOfModules.PullbackMonoidal.isIso_η PresheafOfModules.free_monoidal PresheafOfModules.restrictScalars_laxMonoidal PresheafOfModules.PullbackMonoidal.isIso_δ_gS PresheafOfModules.pullback_oplaxMonoidal PresheafOfModules.PullbackMonoidal.instPreservesColimitsOfSizeCompOppositeCommRingCatRingCatForget₂RingHomCarrierCarrierPb PresheafOfModules.pullback_monoidal' AlgebraicGeometry.SmoothOfRelativeDimension.fiberToSpecResidueField AlgebraicGeometry.SmoothOfRelativeDimension.pullback_snd AlgebraicGeometry.SmoothOfRelativeDimension.pullback_fst AlgebraicGeometry.SmoothOfRelativeDimension.smooth_one AlgebraicGeometry.SmoothProperCurve.isIntegral_pullback_Spec_field"
p2m_attr_erase "instance" "AlgebraicGeometry.IsProper.fiberToSpecResidueField AlgebraicCurve.CurveModel.isProper AlgebraicCurve.CurveModel.isIntegral AlgebraicCurve.CurveModel.smooth AlgebraicGeometry.Scheme.LocalRepresentabilityULift.instIsLocallyInjectiveFunUliftYonedaGluedToSheaf AlgebraicGeometry.Scheme.LocalRepresentabilityULift.instIsLocallySurjectiveFunUliftYonedaGluedToSheafOfIsLocallySurjectiveZariskiTopologyDescFunctorOppositeType AlgebraicGeometry.Scheme.LocalRepresentabilityULift.instIsOpenImmersionToGlued AlgebraicGeometry.Scheme.LocalRepresentabilityULift.instIsIsoSheafZariskiTopologyTypeUliftYonedaGluedToSheaf AlgebraicGeometry.RelPicard.instIsOpenImmersionToGlued AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.instFundamentalIdentityOfSumRamificationInertia AlgebraicCurve.Place.instIsScalarTowerResidueFieldRestrictPushforward AlgebraicCurve.Place.instAlgebraResidueFieldRestrictPushforward AlgebraicCurve.Place.instIsLocalHomRestrictInclusion AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions PresheafOfModules.ExteriorPower.instModulePresheafAb AlgebraicGeometry.RelEffCartierDiv.subsingleton_of_degree_zero AlgebraicGeometry.RelEffCartierDiv.isIso_subschemeIota_snd_of_degree_one AlgebraicGeometry.isIso_ker_graphOver_subschemeIota_snd AlgebraicGeometry.isClosedImmersion_graphOver AlgebraicGeometry.FGSubalgebra.instIsDirectedLe AlgebraicGeometry.FGSubalgebra.instQuasiSeparatedSpaceCarrierCarrierCommRingCatObjOppositeSchemeSpecDiagram AlgebraicGeometry.FGSubalgebra.instIsCofilteredOpposite AlgebraicGeometry.FGSubalgebra.instIsAffineObjOppositeSchemeSpecDiagram AlgebraicGeometry.FGSubalgebra.instNonempty AlgebraicGeometry.FGSubalgebra.instNonemptySubtypeLeSubalgebraValFG AlgebraicGeometry.FGSubalgebra.instCompactSpaceCarrierCarrierCommRingCatObjOppositeSchemeSpecDiagram AlgebraicGeometry.FGSubalgebra.instIsDirectedSubtypeLeSubalgebraValFG AlgebraicGeometry.FGSubalgebra.instIsAffineHomMapOppositeSchemeSpecDiagram AlgebraicGeometry.FGSubalgebra.instIsFiltered AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instNeg AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instSMulInt AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instAddCommGroup AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instAdd"
p2m_attr_erase "instance" "AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instSub AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instModuleCarrierObjOppositeOpensCarrierCarrierCommRingCatPresheafOpOpensTop AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instSMulCarrierObjOppositeOpensCarrierCarrierCommRingCatPresheafOpOpensTop AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instSMulNat AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instZero AlgebraicCurve.instHasLocalResidue_of_hasCanonicalLocalResidueK AlgebraicCurve.instHasCanonicalLocalResidueK_of_hasCanonicalLocalResidueKStar AlgebraicCurve.Place.kw_ffgc_finiteDimensional_adicCompletion instAlgebraSubtypeMemValuationSubring_definitions AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersIntegersCompletion ModularCurve.KwF4gRRTate.instAlgebraKAdicCompletionIntegers AlgebraicCurve.Place.kw_ffgc_continuousSMul_adicCompletionComap AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersCompletionCompletion IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions AlgebraicCurve.instHasCanonicalLocalResidueK AlgebraicCurve.Place.instAlgebra_restrictResidueField AlgebraicCurve.Place.instIsScalarTower_restrictResidueField AlgebraicCurve.instHasLocalResidue AlgebraicCurve.HasSeparableResidue.of_perfectField_of_isCurveOver AlgebraicCurve.HasSeparableResidue.of_perfectField AlgebraicCurve.Place.instIsLocalHom_restrictSubringHom AlgebraicCurve.instHasCanonicalLocalResidueKStar ModularCurve.KwNo6Pin.isLocalRing_completion SheafOfModules.isIso_ihomModelToIhom AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instDecidableEqIdx AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instFintype AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instLinearOrder AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instFintypeIdx AlgebraicGeometry.OModulePresheaf.Leray.relAltC_scalarTower AlgebraicGeometry.OModulePresheaf.Leray.ker_relAltd_modΓ AlgebraicGeometry.OModulePresheaf.Leray.relAltC_modΓ AlgebraicGeometry.OModulePresheaf.Leray.biC_abGrp AlgebraicGeometry.OModulePresheaf.Leray.relAltH_modΓ AlgebraicGeometry.OModulePresheaf.Leray.ker_relAltd_smul AlgebraicGeometry.OModulePresheaf.Leray.relAltH_scalarTower"
p2m_attr_erase "instance" "AlgebraicGeometry.OModulePresheaf.Leray.relAltH_smul AlgebraicGeometry.OModulePresheaf.Leray.biC_module DoubleComplex.instModuleE₂I DoubleComplex.Bounded.modR DoubleComplex.instModuleE₂II DoubleComplex.instAddCommGroupE₂II DoubleComplex.Bounded.abGrp DoubleComplex.instAddCommGroupE₂I AlgebraicGeometry.ChowDatum.hι_closed AlgebraicGeometry.ChowDatumProj.hιN_closed AlgebraicGeometry.ChowDatumProj.hp_proper AlgebraicGeometry.ChowDatum.hp_isoU AlgebraicGeometry.ChowDatum.hp_proper AlgebraicGeometry.ProjSpace.algebraAway AlgebraicGeometry.ProjSpace.instIsProperProdOverπ AlgebraicGeometry.ChowDatumProj.hp_isoU AlgebraicGeometry.ProjSpace.isProper_π AlgebraicGeometry.ProjSpace.finiteType_mvPolynomial ProjSpaceCech.GradedModule.H.module ProjSpaceCech.GradedModule.H.addCommGroup ProjSpaceCech.GradedModule.sec.instAdd ProjSpaceCech.GradedModule.sec.instNeg ProjSpaceCech.GradedModule.acg ProjSpaceCech.GradedModule.Frac.setoid ProjSpaceCech.GradedModule.modR ProjSpaceCech.GradedModule.sec.instModule ProjSpaceCech.GradedModule.sec.instAddCommGroup ProjSpaceCech.GradedModule.sec.instZero ProjSpaceCech.GradedModule.Presentation.fJ ProjSpaceCech.GradedModule.sec.instSMul ProjSpaceCech.Twist.H.module ProjSpaceCech.Idx.instFintype ProjSpaceCech.Twist.H.addCommGroup ProjSpaceCech.Idx.instDecidableEq ProjSpaceCech.Twist.Mon.instDecidableEq ProjSpaceCech.Twist.cochain.instAddCommGroup ProjSpaceCech.Twist.cochain.instModule AlgebraicGeometry.FGSubalgebra.tensorStage_directedSystem AlgebraicGeometry.RelEffCartierDiv.isClosedImmersion_subschemeι_resProdMap AlgebraicGeometry.RelEffCartierDiv.isOpenImmersion_resProdMap"
p2m_attr_erase "instance" "AlgebraicCurve.CurveModel.locallyOfFiniteType_gluedToBase AlgebraicCurve.CurveModel.isFractionRing_overlap AlgebraicCurve.CurveModel.isLocallyNoetherian_glued AlgebraicCurve.CurveModel.jacobsonSpace_glued AlgebraicCurve.CurveModel.isOpenImmersion_ι₀ AlgebraicCurve.CurveModel.isIntegral_glued AlgebraicCurve.CurveModel.quasiSeparated_gluedToBase AlgebraicCurve.CurveModel.compactSpace_glued AlgebraicCurve.CurveModel.isIntegral_adjoin_chartRing AlgebraicCurve.CurveModel.isFractionRing_overlap_functionField AlgebraicCurve.CurveModel.isProper_gluedToBase AlgebraicCurve.CurveModel.isOpenImmersion_ιU AlgebraicCurve.CurveModel.isOpenImmersion_f₀ AlgebraicCurve.CurveModel.isOpenImmersion_fInf AlgebraicCurve.CurveModel.isOpenImmersion_ιInf AlgebraicCurve.CurveModel.algebra_overlap_functionField AlgebraicCurve.CurveModel.quasiCompact_gluedToBase AlgebraicCurve.CurveModel.algebraAdjoin AlgebraicCurve.CurveModel.isDedekindDomain_chartRing AlgebraicCurve.CurveModel.isIntegralClosure AlgebraicCurve.CurveModel.finite_chartRing AlgebraicCurve.CurveModel.centre_isPrime AlgebraicCurve.CurveModel.isFractionRing_chartRing AlgebraicCurve.CurveModel.finiteType_chartRing AlgebraicCurve.CurveModel.isNoetherianRing_chartRing AlgebraicCurve.CurveModel.isScalarTower_base_adjoin AlgebraicCurve.CurveModel.isScalarTower_adjoin AlgebraicCurve.CurveModel.chartRing_finitePresentation AlgebraicGeometry.ProjSpace.twistObj.addCommGroup AlgebraicGeometry.ProjSpace.twistFam.module AlgebraicGeometry.ProjSpace.twistObj.module AlgebraicGeometry.ProjSpace.twistObj.moduleSections AlgebraicGeometry.ProjSpace.twistFam.addCommGroup kmfloorsGlue_int_three_isPrime kmfloorsGlue_int_bot_isPrime"
p2m_attr_erase "simp" "GoodReductionJacobian.RelativeGroupLaw.baseChangePointToBase_ofBase GoodReductionJacobian.RelativeGroupLaw.baseChangePointToBase_coe GoodReductionJacobian.RelativeGroupLaw.baseChangePointOfBase_coe GoodReductionJacobian.RelativeGroupLaw.baseChange_inv GoodReductionJacobian.RelativeGroupLaw.baseChangePointOfBase_toBase GoodReductionJacobian.RelativeGroupLaw.baseChange_mul GoodReductionJacobian.RelativeGroupLaw.baseChange_one NeronModelInfra.NeronModelPropertyBundle.endExtensionEquiv_symm_restrict NeronModelInfra.schemeHomOverComp_id_left NeronModelInfra.schemeHomOverComp_id_right NeronModelInfra.schemeHomOverId_coe NeronModelInfra.NeronModelPropertyBundle.endExtensionEquiv_apply NeronModelInfra.NeronModelPropertyBundle.restrict_endExtensionEquiv_symm NeronModelInfra.schemeHomOverComp_coe NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_fst NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_snd NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_fst NeronSpecialFibreInfra.neronEndRestrictEquiv_apply NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_fst_assoc NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_snd NeronSpecialFibreInfra.neronEndExtension_genericFibreRestrict NeronSpecialFibreInfra.specClosedFibreInclusion_eq NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_fst_assoc NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_snd_assoc NeronSpecialFibreInfra.genericFibreRestrict_neronEndExtension NeronSpecialFibreInfra.homOverId_coe NeronSpecialFibreInfra.homOverComp_coe NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_snd_assoc GoodReductionJacobian.RelativeGroupLaw.fibre_inv GoodReductionJacobian.RelativeGroupLaw.fibrePointToBase_coe GoodReductionJacobian.RelativeGroupLaw.fibrePointOfBase_toBase GoodReductionJacobian.RelativeGroupLaw.fibre_mul GoodReductionJacobian.RelativeGroupLaw.fibrePointToBase_ofBase GoodReductionJacobian.RelativeGroupLaw.fibre_one GoodReductionJacobian.RelativeGroupLaw.fibrePointOfBase_coe AlgebraicGeometry.schemeFibreEndo_snd AlgebraicGeometry.schemeFibreEndo_fst RegularLocalRingQuotientAscent.dualNumberFst_apply AlgebraicGeometry.Scheme.relFrobenius_snd AlgebraicGeometry.Scheme.frobenius_preimage"
p2m_attr_erase "simp" "AlgebraicGeometry.Scheme.relFrobenius_fst AlgebraicGeometry.Scheme.relFrobenius_snd_assoc AlgebraicGeometry.Scheme.relFrobenius_fst_assoc AlgebraicGeometry.powCharRingHom_apply AlgebraicGeometry.Scheme.frobenius_base NeronModelInfra.schemeHomOverNpow_succ NeronModelInfra.schemeHomOverNpow_zero GoodReductionJacobian.relativeGroupLawOfGrpObj_inv GoodReductionJacobian.relativeGroupLawOfGrpObj_mul GoodReductionJacobian.overHomEquivSchemeHomOver_apply_coe GoodReductionJacobian.relativeGroupLawOfGrpObj_one GoodReductionJacobian.overHomEquivSchemeHomOver_symm_apply_left SheafOfModules.tensorUnit_eq AlgebraicGeometry.Scheme.Modules.tensorUnit_eq PresheafOfModules.InternalHom.presheaf_map_apply PresheafOfModules.InternalHom.curryFamily_app PresheafOfModules.InternalHom.add_app PresheafOfModules.InternalHom.smul_app PresheafOfModules.InternalHom.zero_app PresheafOfModules.ihomObj_map_val PresheafOfModules.ihomFunctor_map PresheafOfModules.InternalHom.restrict_app PresheafOfModules.InternalHom.postcomp_app PresheafOfModules.InternalHom.neg_app PresheafOfModules.curry'_app_val PresheafOfModules.InternalHom.presheaf_obj PresheafOfModules.ihomFunctor_obj PresheafOfModules.ihomObj_obj PresheafOfModules.InternalHom.sub_app PresheafOfModules.ihomMap_app_val AlgebraicGeometry.Scheme.Modules.tensorPow_zero AlgebraicGeometry.Scheme.Modules.tensorPow_succ AlgebraicGeometry.RelPicard.RigidifiedLineBundle.mk.sizeOf_spec AlgebraicGeometry.RelPicard.RigidifiedLineBundle.mk.injEq AlgebraicGeometry.Scheme.OrderedAffineCover.mk.injEq AlgebraicGeometry.OModulePresheaf.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCover.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.mk.injEq AlgebraicGeometry.Scheme.TwoAffineOpenCover.mk.injEq AlgebraicGeometry.Scheme.TwoAffineOpenCover.mk.sizeOf_spec"
p2m_attr_erase "simp" "AlgebraicGeometry.Scheme.TwoAffineOpenCover.pullback_U1 AlgebraicGeometry.Scheme.TwoAffineOpenCover.pullback_U0 TwoChartCech.Sections.mk.injEq TwoChartCech.Cover.mk.injEq TwoChartCech.GrothendieckComplex.mk.injEq TwoChartCech.Sections.mk.sizeOf_spec TwoChartCech.Cover.mk.sizeOf_spec TwoChartCech.Cover.lineBundle_r0_apply TwoChartCech.GrothendieckComplex.mk.sizeOf_spec TwoChartCech.Cover.lineBundle_r1_apply CoherentBaseChange.TwoTermComplex.mk.sizeOf_spec CoherentBaseChange.TwoTermComplex.mk.injEq AlgebraicGeometry.OModulePresheaf.prod_obj AlgebraicGeometry.OModulePresheaf.restrOpen_obj AlgebraicGeometry.OModulePresheaf.DevissageStep.mk.injEq AlgebraicGeometry.OModulePresheaf.pushforward_obj AlgebraicGeometry.OModulePresheaf.im_obj AlgebraicGeometry.OModulePresheaf.pow_obj AlgebraicGeometry.OModulePresheaf.fstHom_app AlgebraicGeometry.OModulePresheaf.ker_obj AlgebraicGeometry.OModulePresheaf.coker_obj AlgebraicGeometry.OModulePresheaf.DevissageStep.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCover.preimage_U AlgebraicGeometry.OModulePresheaf.sndHom_app AlgebraicGeometry.OModulePresheaf.Hom.mk.injEq AlgebraicGeometry.OModulePresheaf.Hom.id_app AlgebraicGeometry.OModulePresheaf.AffHom.appSections_apply AlgebraicGeometry.OModulePresheaf.AffHom.comp_app AlgebraicGeometry.OModulePresheaf.AffSES.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.AffHom.kerMap_coe AlgebraicGeometry.OModulePresheaf.AffHom.id_app AlgebraicGeometry.OModulePresheaf.Hom.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.Hom.toAffHom_app AlgebraicGeometry.OModulePresheaf.SES.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.AffHom.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.Hom.comp_app AlgebraicGeometry.OModulePresheaf.SES.mk.injEq AlgebraicGeometry.OModulePresheaf.AffHom.mk.injEq AlgebraicGeometry.OModulePresheaf.Hom.appSections_apply AlgebraicGeometry.OModulePresheaf.AffSES.mk.injEq"
p2m_attr_erase "simp" "PresheafOfModules.freeεIso_hom_app PresheafOfModules.freeμIso_hom_app AlgebraicGeometry.RelPicard.RepresentsRelSubPic.mk.injEq AlgebraicGeometry.RelPicard.SubPicCondition.mk.injEq AlgebraicGeometry.RelPicard.SubPicCondition.mk.sizeOf_spec AlgebraicGeometry.RelPicard.RepresentsRelSubPic.mk.sizeOf_spec AlgebraicGeometry.SmoothProperCurve.sectionBaseChange_coe_snd AlgebraicGeometry.SmoothProperCurve.sectionBaseChange_coe_fst AlgebraicCurve.CurveModel.mk.injEq AlgebraicCurve.CurveModel.mk.sizeOf_spec AlgebraicCurve.mulAdele_apply AlgebraicCurve.residuePairing_apply_coe AlgebraicCurve.mem_adeleBdd AlgebraicCurve.weilSmul_one AlgebraicCurve.diagonalHom_apply AlgebraicCurve.weilSmul_apply AlgebraicCurve.adeleSpaceMul_coe AlgebraicCurve.mulAdele_one AlgebraicGeometry.SmoothProperCurve.FiniteMapData.twoAffineOpenCover_U1 AlgebraicGeometry.SmoothProperCurve.FiniteMapData.mk.injEq AlgebraicGeometry.SmoothProperCurve.FiniteMapData.mk.sizeOf_spec AlgebraicGeometry.SmoothProperCurve.FiniteMapData.twoAffineOpenCover_U0 AlgebraicGeometry.RelPicard.SubPicCondition.onClasses_mk AlgebraicGeometry.RelPicard.relSubPicPresheaf_map_coe CategoryTheory.Functor.OverTotal.ofFibre_fst CategoryTheory.Functor.overTotal_map_fst AlgebraicGeometry.Scheme.LocalRepresentabilityULift.glueData_J AlgebraicGeometry.Scheme.LocalRepresentabilityULift.uliftYoneda_toGlued_uliftYonedaGluedToSheaf AlgebraicGeometry.Scheme.LocalRepresentabilityULift.glueData_t' AlgebraicGeometry.Scheme.LocalRepresentabilityULift.uliftYoneda_toGlued_uliftYonedaGluedToSheaf_assoc AlgebraicGeometry.Scheme.LocalRepresentabilityULift.uliftYonedaGluedToSheaf_app_toGlued AlgebraicGeometry.Scheme.LocalRepresentabilityULift.glueData_openCover_map AlgebraicGeometry.Scheme.LocalRepresentabilityULift.uliftYonedaGluedToSheaf_app_comp AlgebraicGeometry.Scheme.LocalRepresentabilityULift.glueData_V AlgebraicGeometry.Scheme.LocalRepresentabilityULift.glueData_t AlgebraicGeometry.Scheme.LocalRepresentabilityULift.glueData_U AlgebraicGeometry.Scheme.LocalRepresentabilityULift.glueData_f AlgebraicGeometry.RelPicard.designationOfRepresentableBy_P AlgebraicGeometry.RelPicard.designationOfRepresentableBy_toBase AlgebraicGeometry.RelPicard.rigSection_snd"
p2m_attr_erase "simp" "AlgebraicGeometry.RelPicard.RigidifiedLineBundle.ofInvertible_L AlgebraicGeometry.RelPicard.rigSection_snd_assoc AlgebraicGeometry.RelPicard.SubPicGroupCondition.mk.injEq AlgebraicGeometry.RelPicard.SubPicGroupCondition.mk.sizeOf_spec AlgebraicCurve.coe_cechH0Equiv_apply AlgebraicCurve.cechH1ToH1_mk AlgebraicCurve.lSpaceOn_univ AlgebraicCurve.lSpaceOn_empty AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.Divisor.mapRestrict_single AlgebraicCurve.Divisor.pushforward_single AlgebraicCurve.Place.coe_restrictInclusion AlgebraicCurve.Place.mem_fiber AlgebraicCurve.Place.restrict_toValuationSubring AlgebraicCurve.Divisor.degree_pushforward AlgebraicCurve.Place.restrictResidueMap_residue AlgebraicCurve.Pic0.coe_pushforwardDegZeroHom AlgebraicCurve.Pic0.coe_pullbackDegZeroHom AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk"
p2m_attr_erase "simp" "ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Divisor.degree_pushforwardAlong AlgebraicCurve.Pic0.coe_degZeroCorrespondence AlgebraicCurve.Place.mem_fiberAlong AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.jqNModC_one ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one AlgebraicCurve.Place.differentialCoeff_zero AlgebraicCurve.Place.differentialCoeff_dCoord AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.injEq AlgebraicCurve.TranscendenceTower.mk.injEq AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec AlgebraicCurve.PoleDivisorPackage.mk.injEq AlgebraicGeometry.RelPicard.thetaBundle_def AlgebraicGeometry.RelPicard.picardBundle_def AlgebraicGeometry.RelEffCartierDiv.toRelEffDivisor_ofRelEffDivisor AlgebraicGeometry.RelEffCartierDiv.toRelEffDivisor_I AlgebraicGeometry.mapOnProdOver_fst_assoc AlgebraicGeometry.RelEffCartierDiv.mk.sizeOf_spec AlgebraicGeometry.RelEffCartierDiv.mk.injEq AlgebraicGeometry.mapOnProdOver_snd AlgebraicGeometry.mapOnProdOver_fst"
p2m_attr_erase "simp" "AlgebraicGeometry.mapOnProdOver_snd_assoc AlgebraicGeometry.mapOnProdOver_id AlgebraicCurve.RelEffDivisor.mk.sizeOf_spec AlgebraicCurve.mapOnProd_fst AlgebraicCurve.mapOnProd_fst_assoc AlgebraicCurve.mapOnProd_snd AlgebraicCurve.UnivDivisorPack.mk.injEq AlgebraicCurve.RelEffDivisor.mk.injEq AlgebraicCurve.UnivDivisorPack.mk.sizeOf_spec AlgebraicCurve.mapOnProd_snd_assoc AlgebraicGeometry.Scheme.Modules.exteriorPower_obj PresheafOfModules.exteriorPower_map_ιMulti PresheafOfModules.ExteriorPower.appₗ_apply AlgebraicGeometry.prodKerGraph_one AlgebraicGeometry.fibrePowOver.proj_comp AlgebraicGeometry.prodKerGraph_zero AlgebraicGeometry.RelEffCartierDiv.empty_I AlgebraicGeometry.fibrePowOver.proj_comp_assoc AlgebraicGeometry.graphOver_fst_assoc AlgebraicGeometry.RelEffCartierDiv.toPoint_comp AlgebraicGeometry.RelEffCartierDiv.toPoint_comp_assoc AlgebraicGeometry.graphOver_fst AlgebraicGeometry.RelEffCartierDiv.ofPoint_I AlgebraicGeometry.graphOver_snd AlgebraicGeometry.graphOver_snd_assoc AlgebraicCurve.SymmetricPowerPackage.mk.sizeOf_spec AlgebraicCurve.SymmetricPowerPackage.mk.injEq AlgebraicGeometry.FGSubalgebra.cocone_ι_app_apply AlgebraicGeometry.RelPicard.fst_toProdSpec AlgebraicGeometry.RelPicard.toProdSpec_fst_assoc AlgebraicGeometry.RelPicard.pointsSubBasepointModule_cons AlgebraicGeometry.RelPicard.pointsSubBasepointModule_nil AlgebraicGeometry.RelPicard.fst_toProdSpec_assoc AlgebraicGeometry.RelPicard.toProdSpec_fst AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.sub_app AlgebraicGeometry.Scheme.IdealSheafData.sres_sresTop AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.add_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.mk.sizeOf_spec AlgebraicGeometry.Scheme.IdealSheafData.coe_resLE AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.smul_app"
p2m_attr_erase "simp" "AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.coe_ofLE_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.ideal_range AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.zero_app AlgebraicGeometry.Scheme.IdealSheafData.sres_sres AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.comp_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.neg_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.id_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.coe_mulRight_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.nsmul_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.mk.injEq AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.zsmul_app AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.sizeOf_spec AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.injEq AlgebraicCurve.adeleSingle_coe AlgebraicCurve.kaehlerResidueTermKFam_apply AlgebraicCurve.Place.LocalResidueData.mk.injEq AlgebraicCurve.Place.LocalResidueData.mk.sizeOf_spec AlgebraicCurve.Place.kw_ffgc_adicCompletionComapIntegers_coe AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.sizeOf_spec AlgebraicCurve.Place.mem_simplePoleSubmodule AlgebraicCurve.Place.coe_uniformizerSubring ModularCurve.Lg37.Lg37CompletionSection.mk.injEq AlgebraicCurve.Place.CoefficientFieldSection.mk.injEq AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.injEq ModularCurve.Lg37.Lg37CompletionSection.mk.sizeOf_spec AlgebraicCurve.Place.CoefficientFieldSection.mk.sizeOf_spec AlgebraicCurve.Place.poleSubmodule_one AlgebraicCurve.Place.mem_poleSubmodule AlgebraicGeometry.Scheme.Modules.toUnitSection_ofUnitSection AlgebraicGeometry.Scheme.Modules.pullbackSection_def AlgebraicGeometry.Scheme.Modules.ofUnitSection_toUnitSection PresheafOfModules.InternalHom.IsSheafAux.appAt_toPresheafHom SheafOfModules.ihomSectionsEquivFamily_unit AlgebraicGeometry.Scheme.Modules.restrictHomEquivFamily_apply SheafOfModules.ihomEval_unit_app AlgebraicGeometry.Scheme.Modules.ihomEval_zero_right AlgebraicGeometry.Scheme.Modules.ihomEval_zero_left AlgebraicGeometry.Scheme.Modules.homOfFamily_app_apply SheafOfModules.unit_ihomSectionsEquivFamily AlgebraicGeometry.Scheme.Modules.familyOfHom_app"
p2m_attr_erase "simp" "AlgebraicGeometry.Scheme.Modules.restrictUnitIso_hom_app_apply AlgebraicGeometry.Scheme.Modules.restrictUnitIso_inv_app_apply AlgebraicGeometry.Scheme.Modules.restrictHomOfFamily_app_apply AlgebraicGeometry.Scheme.Modules.restrictHomEquivFamily_symm_apply AlgebraicGeometry.Scheme.Modules.tensorSections_zero_right AlgebraicGeometry.Scheme.Modules.map_unitSection AlgebraicGeometry.Scheme.Modules.tensorSectionsBilin_apply AlgebraicGeometry.Scheme.Modules.tensorPowSection_zero AlgebraicGeometry.Scheme.Modules.tensorSections_zero_left AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_neg AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_zero AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_sub AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_add AlgebraicGeometry.Scheme.OrderedAffineCover.toCoverOf_U AlgebraicGeometry.Scheme.OrderedAffineCoverOf.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCoverOf.mk.injEq AlgebraicGeometry.Scheme.OrderedAffineCover.restrict_U AlgebraicGeometry.OModulePresheaf.Leray.restrictToPreimage_U DoubleComplex.Bounded.mk.injEq DoubleComplex.Bounded.mk.sizeOf_spec DoubleComplex.Convergence.mk.injEq DoubleComplex.Convergence.mk.sizeOf_spec DoubleComplex.SubQuot.mk.sizeOf_spec DoubleComplex.SubQuot.mk.injEq AlgebraicGeometry.ChowDatumProj.mk.sizeOf_spec AlgebraicGeometry.ChowDatum.mk.sizeOf_spec AlgebraicGeometry.ChowDatumProj.mk.injEq AlgebraicGeometry.ChowDatum.mk.injEq ProjSpaceCech.GradedModule.mk.injEq ProjSpaceCech.GradedModule.mk.sizeOf_spec ProjSpaceCech.GradedModule.Frac.mk.sizeOf_spec ProjSpaceCech.GradedModule.Presentation.mk.injEq ProjSpaceCech.GradedModule.Frac.mk.injEq ProjSpaceCech.GradedModule.Presentation.mk.sizeOf_spec ProjSpaceCech.GradedModule.Hom.shift_toLinearMap ProjSpaceCech.GradedModule.Hom.mk.sizeOf_spec ProjSpaceCech.GradedModule.Hom.mk.injEq TwoChartCech.Mumford.dK_apply TwoChartCech.Mumford.ι0_apply TwoChartCech.Mumford.ι1_apply"
p2m_attr_erase "simp" "TwoChartCech.KerCoprod.dK_apply TwoChartCech.KerCoprod.ι1_apply TwoChartCech.KerCoprod.ι0_apply AlgebraicGeometry.tilde.functorCompPullbackSpecIso_app AlgebraicGeometry.RelPicard.algEquivZeroGroupCut_toSubPicCondition AlgebraicGeometry.RelPicard.LFP.stageHom_val AlgebraicGeometry.RelPicard.BaseChange.relSubPicPresheafRestrictIso_hom_app_coe AlgebraicGeometry.RelPicard.BaseChange.relSubPicPresheafRestrictIso_inv_app_coe AlgebraicGeometry.RelPicard.BaseChange.restrict_P AlgebraicGeometry.RelEffCartierDiv.IsUniversal.lift_comp AlgebraicGeometry.RelEffCartierDiv.functor_map_fst AlgebraicGeometry.RelEffCartierDiv.IsUniversal.homEquiv_apply AlgebraicGeometry.RelEffCartierDiv.IsUniversal.lift_pullbackAlong AlgebraicGeometry.RelEffCartierDiv.IsUniversal.homEquiv_symm_apply AlgebraicGeometry.RelEffCartierDiv.IsUniversal.lift_comp_assoc AlgebraicGeometry.RelEffCartierDiv.supportedIn_top AlgebraicGeometry.RelEffCartierDiv.mem_supportedIn_iff AlgebraicGeometry.RelEffCartierDiv.supportedIn_top_eq AlgebraicGeometry.RelEffCartierDiv.restrictAlong_extendAlong AlgebraicGeometry.RelEffCartierDiv.extendAlong_I AlgebraicGeometry.RelEffCartierDiv.resProdMap_snd AlgebraicGeometry.RelEffCartierDiv.restrictAlong_I AlgebraicGeometry.RelEffCartierDiv.extendAlong_restrictAlong AlgebraicGeometry.RelEffCartierDiv.resProdMap_fst_assoc AlgebraicGeometry.RelEffCartierDiv.resProdMap_snd_assoc AlgebraicGeometry.RelEffCartierDiv.resProdMap_fst CoherentBaseChange.FibreH0Family.mk.sizeOf_spec CoherentBaseChange.FibreH0Family.mk.injEq AlgebraicGeometry.Scheme.Modules.ProjPresentation.mk.injEq AlgebraicGeometry.Scheme.Modules.ProjPresentation.mk.sizeOf_spec AlgebraicCurve.CurveModel.coe_gInf AlgebraicCurve.CurveModel.coe_tInvChart AlgebraicCurve.CurveModel.ιInf_gluedToBase_assoc AlgebraicCurve.CurveModel.ιInf_gluedToBase AlgebraicCurve.CurveModel.primeOfι₀_asIdeal AlgebraicCurve.CurveModel.coe_tChart AlgebraicCurve.CurveModel.ι₀_gluedToBase_assoc AlgebraicCurve.CurveModel.primeOfιInf_asIdeal AlgebraicCurve.CurveModel.ι₀_gluedToBase AlgebraicCurve.CurveModel.coe_tma"
p2m_attr_erase "simp" "AlgebraicCurve.CurveModel.coe_primeEquivChartPlaces AlgebraicGeometry.ProjSpace.twistObj.mk.injEq AlgebraicGeometry.ProjSpace.twistObj.zero_val AlgebraicGeometry.ProjSpace.twistObj.add_val AlgebraicGeometry.ProjSpace.twist_res_val AlgebraicGeometry.ProjSpace.twist_smul_val AlgebraicGeometry.ProjSpace.twistGradeToObj_val AlgebraicGeometry.ProjSpace.twistObj.smul_val AlgebraicGeometry.ProjSpace.twistGradeEquiv_apply_val AlgebraicGeometry.ProjSpace.twistObj.mk.sizeOf_spec"

set_option autoImplicit false

open scoped TensorProduct Quaternion NumberField
p2m_open "CategoryTheory AlgebraicGeometry QuaternionAlgebra IsDedekindDomain CerednikDrinfeld CerednikDrinfeld.QM CerednikDrinfeld.FormalOmega CerednikDrinfeld.SpecialFormal NeronModelInfra~schemeHomOverComp~schemeHomOverComp_coe GoodReductionJacobian"

set_option linter.unusedVariables false

namespace KerKillS25

variable {R : Type} [CommRing R]

def IsHom {A A' : Scheme.{0}} {f : A ⟶ Spec (CommRingCat.of R)} {f' : A' ⟶ Spec (CommRingCat.of R)}
    (L : RelativeGroupLaw R f) (L' : RelativeGroupLaw R f') (Φ : A ⟶ A') (hΦ : Φ ≫ f' = f) : Prop :=
  ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of R)) (P Q : SchemeHomOver t f),
    mapPt Φ hΦ (L.mul t P Q) = L'.mul t (mapPt Φ hΦ P) (mapPt Φ hΦ Q)

theorem IsHom.comp {A A' A'' : Scheme.{0}} {f : A ⟶ Spec (CommRingCat.of R)} {f' : A' ⟶ Spec (CommRingCat.of R)}
    {f'' : A'' ⟶ Spec (CommRingCat.of R)}
    {L : RelativeGroupLaw R f} {L' : RelativeGroupLaw R f'} {L'' : RelativeGroupLaw R f''}
    {Φ : A ⟶ A'} {hΦ : Φ ≫ f' = f} {Ψ : A' ⟶ A''} {hΨ : Ψ ≫ f'' = f'}
    (h1 : IsHom L L' Φ hΦ) (h2 : IsHom L' L'' Ψ hΨ) (hc : (Φ ≫ Ψ) ≫ f'' = f) :
    IsHom L L'' (Φ ≫ Ψ) hc := by
  intro T t P Q
  have e : ∀ X : SchemeHomOver t f, mapPt (Φ ≫ Ψ) hc X = mapPt Ψ hΨ (mapPt Φ hΦ X) := fun X =>
    Subtype.ext (by simp only [mapPt_coe, Category.assoc])
  rw [e, e, e, h1, h2]

theorem IsHom.val {A A' : Scheme.{0}} {f : A ⟶ Spec (CommRingCat.of R)} {f' : A' ⟶ Spec (CommRingCat.of R)}
    {L : RelativeGroupLaw R f} {L' : RelativeGroupLaw R f'} {Φ : A ⟶ A'} {hΦ : Φ ≫ f' = f} (h : IsHom L L' Φ hΦ) :
    ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of R)) (P Q : SchemeHomOver t f),
      (L.mul t P Q).1 ≫ Φ =
        (L'.mul t ⟨P.1 ≫ Φ, by rw [Category.assoc, hΦ]; exact P.2⟩ ⟨Q.1 ≫ Φ, by rw [Category.assoc, hΦ]; exact Q.2⟩).1 :=
  fun t P Q => congrArg Subtype.val (h t P Q)

theorem eq_one_of_mul_self {A : Scheme.{0}} {f : A ⟶ Spec (CommRingCat.of R)} (L : RelativeGroupLaw R f)
    {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of R)) (x : SchemeHomOver t f) (h : L.mul t x x = x) :
    x = L.one t := by
  have h2 : L.mul t (L.inv t x) (L.mul t x x) = L.mul t (L.inv t x) x := by rw [h]
  rw [← L.mul_assoc, L.inv_mul_cancel, L.one_mul] at h2
  exact h2

theorem IsHom.map_one {A A' : Scheme.{0}} {f : A ⟶ Spec (CommRingCat.of R)} {f' : A' ⟶ Spec (CommRingCat.of R)}
    {L : RelativeGroupLaw R f} {L' : RelativeGroupLaw R f'} {Φ : A ⟶ A'} {hΦ : Φ ≫ f' = f} (h : IsHom L L' Φ hΦ)
    {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of R)) : mapPt Φ hΦ (L.one t) = L'.one t := by
  apply eq_one_of_mul_self
  rw [← h, L.one_mul]

theorem nsmulPt_eq_nsmul {A : Scheme.{0}} {f : A ⟶ Spec (CommRingCat.of R)} (L : RelativeGroupLaw R f)
    {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of R)) (n : ℕ) (P : SchemeHomOver t f) :
    nsmulPt L t n P = L.nsmul t n P := by
  induction n with
  | zero => rw [RelativeGroupLaw.nsmul_zero]; rfl
  | succ n ih => rw [RelativeGroupLaw.nsmul_succ, ← ih]; rfl

theorem val_comp_schemeNsmul {A : Scheme.{0}} {f : A ⟶ Spec (CommRingCat.of R)} (L : RelativeGroupLaw R f)
    {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of R)) (n : ℕ) (Q : SchemeHomOver t f) :
    Q.1 ≫ L.schemeNsmul n = (nsmulPt L t n Q).1 := by
  have h := L.nsmul_natural f t Q.1 Q.2 n RelativeGroupLaw.idPoint
  have hid : schemeHomOverComp Q.1 Q.2 (RelativeGroupLaw.idPoint (f := f)) = Q :=
    Subtype.ext (by rw [schemeHomOverComp_coe]; exact Category.comp_id _)
  rw [hid, ← nsmulPt_eq_nsmul L t n Q] at h
  rw [← h, schemeHomOverComp_coe]
  rfl

theorem act_natCast_eq_schemeNsmul {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} {N : ℕ} (E : FakeEllipticCurve Λ N R)
    (h1 : (1 : ℍ[ℚ, a, b]) ∈ Λ) (n : ℕ) (hn : ((n : ℚ) : ℍ[ℚ, a, b]) ∈ Λ) :
    E.act ⟨((n : ℚ) : ℍ[ℚ, a, b]), hn⟩ = E.L.schemeNsmul n := by
  have h := CerednikDrinfeld.QM.FakeEllipticCurve.pushPt_act_natCast_eq_nsmulPt E h1 n hn E.f RelativeGroupLaw.idPoint
  have h' := congrArg Subtype.val h
  rw [← val_comp_schemeNsmul] at h'
  simpa [pushPt, mapPt_coe] using h'

theorem aeval_mem_of_coeff_zero {S C : Type} [CommRing S] [CommRing C] [Algebra S C] {σ : Type} (J : Ideal C)
    (p : MvPolynomial σ S) (hp : p.coeff 0 = 0) (a : σ → C) (ha : ∀ i, a i ∈ J) : MvPolynomial.aeval a p ∈ J := by
  classical
  rw [p.as_sum, map_sum]
  refine Ideal.sum_mem _ fun d _ => ?_
  rw [MvPolynomial.aeval_monomial]
  by_cases hd0 : d = 0
  · subst hd0
    rw [hp, map_zero, zero_mul]
    exact J.zero_mem
  · obtain ⟨s, hs⟩ : ∃ s, d s ≠ 0 := by
      by_contra h
      push Not at h
      exact hd0 (Finsupp.ext fun s => by simpa using h s)
    refine Ideal.mul_mem_left _ _ ?_
    rw [Finsupp.prod, ← Finset.mul_prod_erase _ _ (Finsupp.mem_support_iff.mpr hs)]
    refine Ideal.mul_mem_right _ _ ?_
    obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero hs
    rw [hk, pow_succ]
    exact Ideal.mul_mem_left _ _ (ha s)

theorem nilEval_mem {S C : Type} [CommRing S] [CommRing C] [Algebra S C] {σ : Type} [Fintype σ] [DecidableEq σ]
    (J : Ideal C) (n : ℕ) (φ : MvPowerSeries σ S) (hφ : MvPowerSeries.constantCoeff φ = 0) (a : σ → C)
    (ha : ∀ i, a i ∈ J) : MvFormalGroup.nilEval n φ a ∈ J := by
  unfold MvFormalGroup.nilEval
  refine aeval_mem_of_coeff_zero J _ ?_ a ha
  rw [MvPowerSeries.coeff_trunc', if_pos (Finsupp.le_def.2 fun _ => Nat.zero_le _),
    MvPowerSeries.coeff_zero_eq_constantCoeff_apply, hφ]

theorem nilEval_zero {σ : Type} [Fintype σ] [DecidableEq σ] {S C : Type} [CommRing S] [CommRing C] [Algebra S C]
    (m : ℕ) (φ : MvPowerSeries σ S) (hφ : MvPowerSeries.constantCoeff φ = 0) :
    MvFormalGroup.nilEval m φ (0 : σ → C) = 0 := by
  have h := nilEval_mem (⊥ : Ideal C) m φ hφ 0 (fun _ => Ideal.zero_mem _)
  rwa [Ideal.mem_bot] at h

theorem nilMul_zero {g : ℕ} {S C : Type} [CommRing S] [CommRing C] [Algebra S C] (F : MvFormalGroup g S) (m : ℕ) :
    F.nilMul m (0 : Fin g → C) 0 = 0 := by
  funext i
  show MvFormalGroup.nilEval m (F.toPowerSeries i) (Sum.elim 0 0) = 0
  have : (Sum.elim (0 : Fin g → C) (0 : Fin g → C)) = 0 := by funext x; cases x <;> rfl
  rw [this]
  exact nilEval_zero m _ (F.constantCoeff_eq_zero i)

theorem act_comm_natCast {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} {N : ℕ} (E : FakeEllipticCurve Λ N R) (x : ↥Λ) (n : ℕ)
    (hn : ((n : ℚ) : ℍ[ℚ, a, b]) ∈ Λ) :
    E.act x ≫ E.act ⟨((n : ℚ) : ℍ[ℚ, a, b]), hn⟩ = E.act ⟨((n : ℚ) : ℍ[ℚ, a, b]), hn⟩ ≫ E.act x := by
  have hnx : ((n : ℚ) : ℍ[ℚ, a, b]) * (x : ℍ[ℚ, a, b]) ∈ Λ := by
    rw [QuaternionAlgebra.coe_natCast, ← nsmul_eq_mul]; exact nsmul_mem x.2 n
  have hxn : (x : ℍ[ℚ, a, b]) * ((n : ℚ) : ℍ[ℚ, a, b]) ∈ Λ := by
    rw [QuaternionAlgebra.coe_natCast, ← nsmul_eq_mul']; exact nsmul_mem x.2 n
  have h1 := E.act_mul ⟨((n : ℚ) : ℍ[ℚ, a, b]), hn⟩ x hnx
  have h2 := E.act_mul x ⟨((n : ℚ) : ℍ[ℚ, a, b]), hn⟩ hxn
  have h3 : (⟨((n : ℚ) : ℍ[ℚ, a, b]) * (x : ℍ[ℚ, a, b]), hnx⟩ : ↥Λ) = ⟨(x : ℍ[ℚ, a, b]) * ((n : ℚ) : ℍ[ℚ, a, b]), hxn⟩ :=
    Subtype.ext (QuaternionAlgebra.coe_commutes _ _)
  rw [← h1, h3, h2]

theorem rpow_mem {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} (hΛℤ : ∀ m : ℤ, ((m : ℚ) : ℍ[ℚ, a, b]) ∈ Λ) (r k : ℕ) :
    (((r ^ k : ℕ) : ℚ) : ℍ[ℚ, a, b]) ∈ Λ := by
  have := hΛℤ ((r ^ k : ℕ) : ℤ); rwa [Int.cast_natCast] at this

theorem act_natq_eq {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} {N : ℕ} {S : Type} [CommRing S]
    (hΛℤ : ∀ m : ℤ, ((m : ℚ) : ℍ[ℚ, a, b]) ∈ Λ) (E : FakeEllipticCurve Λ N S) (r k : ℕ) :
    E.act ⟨(((r ^ k : ℕ) : ℚ) : ℍ[ℚ, a, b]), rpow_mem hΛℤ r k⟩ = E.act ⟨(((r ^ k : ℕ) : ℤ) : ℚ), hΛℤ _⟩ := by
  congr 1

theorem act_pow_eq {p : ℕ} [Fact p.Prime] {B : Type} [CommRing B] (X : FormalODModule p B) (d : ℕ) :
    X.act ((p : Zp2 p) ^ d) = (((p ^ d : ℕ) : MvFormalGroup.End X.F)).toPowerSeries := by
  rw [← Nat.cast_pow]
  show (X.actRingHom ((p ^ d : ℕ) : Zp2 p)).toPowerSeries = _
  rw [map_natCast]

theorem isNilpotent_of_mem {B' : Type} [CommRing B'] {J : Ideal B'} {m : ℕ} (hJ : J ^ (m + 1) = ⊥) {x : B'} (hx : x ∈ J) :
    IsNilpotent x :=
  ⟨m + 1, by
    have := Ideal.pow_mem_pow hx (m + 1)
    rw [hJ] at this
    exact (Submodule.mem_bot _).mp this⟩

theorem IsHom.nsmulPt_map {A A' : Scheme.{0}} {f : A ⟶ Spec (CommRingCat.of R)} {f' : A' ⟶ Spec (CommRingCat.of R)}
    {L : RelativeGroupLaw R f} {L' : RelativeGroupLaw R f'} {Φ : A ⟶ A'} {hΦ : Φ ≫ f' = f} (h : IsHom L L' Φ hΦ)
    {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of R)) (n : ℕ) (P : SchemeHomOver t f) :
    mapPt Φ hΦ (nsmulPt L t n P) = nsmulPt L' t n (mapPt Φ hΦ P) := by
  induction n with
  | zero => exact h.map_one t
  | succ n ih =>
      show mapPt Φ hΦ (L.mul t (nsmulPt L t n P) P) = L'.mul t (nsmulPt L' t n (mapPt Φ hΦ P)) (mapPt Φ hΦ P)
      rw [h, ih]

theorem nsmulPt_one {A : Scheme.{0}} {f : A ⟶ Spec (CommRingCat.of R)} (L : RelativeGroupLaw R f)
    {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of R)) (n : ℕ) : nsmulPt L t n (L.one t) = L.one t := by
  induction n with
  | zero => rfl
  | succ n ih =>
      show L.mul t (nsmulPt L t n (L.one t)) (L.one t) = L.one t
      rw [ih, L.mul_one]

theorem forall_nsmulPt_eq_one_of_comp_eq_one_of_forall_specOver
    {S : Type} [CommRing S] {A A' : Scheme.{0}}
    {f : A ⟶ Spec (CommRingCat.of S)} {f' : A' ⟶ Spec (CommRingCat.of S)}
    (L : RelativeGroupLaw S f) (L' : RelativeGroupLaw S f') (F : A ⟶ A') (n : ℕ)
    (haff : ∀ (C : Type) [CommRing C] [Algebra S C]
      (P : SchemeHomOver (Scheme.specOver (𝒪 := S) C) f),
      P.1 ≫ F = (L'.one (Scheme.specOver (𝒪 := S) C)).1 →
        nsmulPt L (Scheme.specOver (𝒪 := S) C) n P = L.one (Scheme.specOver (𝒪 := S) C)) :
    ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of S)) (P : SchemeHomOver t f),
      P.1 ≫ F = (L'.one t).1 → nsmulPt L t n P = L.one t := by
  intro T t P hP
  apply Subtype.ext
  apply T.affineOpenCover.cover.hom_ext
  intro x
  change T.affineOpenCover.f x ≫ (nsmulPt L t n P).1 = T.affineOpenCover.f x ≫ (L.one t).1
  obtain ⟨φ, hφ⟩ := Spec.map_surjective (T.affineOpenCover.f x ≫ t)
  letI hAlg : Algebra S (T.affineOpenCover.X x) := φ.hom.toAlgebra
  have hbase : T.affineOpenCover.f x ≫ t = Scheme.specOver (𝒪 := S) (T.affineOpenCover.X x) := by
    rw [← hφ]; rfl
  have hP' : (schemeHomOverComp (T.affineOpenCover.f x) hbase P).1 ≫ F =
      (L'.one (Scheme.specOver (𝒪 := S) (T.affineOpenCover.X x))).1 := by
    rw [schemeHomOverComp_coe, Category.assoc, hP, ← L'.one_natural t _ (T.affineOpenCover.f x) hbase,
      schemeHomOverComp_coe]
  have h := @haff (T.affineOpenCover.X x) _ hAlg (schemeHomOverComp (T.affineOpenCover.f x) hbase P) hP'
  have hn : schemeHomOverComp (T.affineOpenCover.f x) hbase (nsmulPt L t n P) =
      nsmulPt L _ n (schemeHomOverComp (T.affineOpenCover.f x) hbase P) := by
    rw [nsmulPt_eq_nsmul, nsmulPt_eq_nsmul]; exact L.nsmul_natural t _ _ hbase n P
  rw [← schemeHomOverComp_coe (T.affineOpenCover.f x) hbase (nsmulPt L t n P), hn, h,
    ← L.one_natural t _ (T.affineOpenCover.f x) hbase, schemeHomOverComp_coe]

end KerKillS25

open KerKillS25

theorem solution
    {r N : ℕ} [Fact r.Prime] {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]}
    (hΛ1 : (1 : ℍ[ℚ, a, b]) ∈ Λ) (hΛℤ : ∀ m : ℤ, ((m : ℚ) : ℍ[ℚ, a, b]) ∈ Λ)
    (coord : ↥Λ → Zp2 r × Zp2 r) (hcoord : IsOrderCoord Λ r coord)

    (𝒪 : Type) [CommRing 𝒪] (π : 𝒪) (Onr : Type) [CommRing Onr] [Algebra 𝒪 Onr]
    (A₀ : FakeEllipticCurve Λ N (Onr ⧸ Ideal.span {algebraMap 𝒪 Onr π}))
    (X₀ : FormalODModule r (Onr ⧸ Ideal.span {algebraMap 𝒪 Onr π}))
    (θ₀ : RelativeGroupLaw.FormalCoordinates A₀.f 2) (hA₀ : A₀.IsFormalModuleVia coord X₀ θ₀)

    (B : Type) [CommRing B] [IsNoetherianRing B] [Algebra 𝒪 B] (ψ : Onr →ₐ[𝒪] B)
    (hBr : IsNilpotent ((r : ℕ) : B ⧸ Ideal.span {algebraMap 𝒪 B π}))
    (E : FakeEllipticCurve Λ N B) (X : FormalODModule r B) (θ : RelativeGroupLaw.FormalCoordinates E.f 2)
    (hX : E.IsFormalModuleVia coord X θ)
    (ρ : FakeEllipticCurve.Rigidification r π A₀ ψ E)

    (k : ℕ) (ψ' : ρ.Ab.A ⟶ ρ.Eb.A) (hfac : ρ.Ab.L.schemeNsmul (r ^ k) ≫ ψ' = ρ.φ')
    (hψ'f : ψ' ≫ ρ.Eb.f = ρ.Ab.f)
    (hψ'hom : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of (B ⧸ Ideal.span {algebraMap 𝒪 B π}))) (P Q : SchemeHomOver t ρ.Ab.f),
      (ρ.Ab.L.mul t P Q).1 ≫ ψ' =
        (ρ.Eb.L.mul t ⟨P.1 ≫ ψ', by rw [Category.assoc, hψ'f]; exact P.2⟩
          ⟨Q.1 ≫ ψ', by rw [Category.assoc, hψ'f]; exact Q.2⟩).1)

    (σ₁ : Series (B ⧸ Ideal.span {algebraMap 𝒪 B π})) (hσ₁ : ∀ i, MvPowerSeries.constantCoeff (σ₁ i) = 0)
    (hσ₁rep : ∀ (B'' : Type) [CommRing B''] [Algebra (B ⧸ Ideal.span {algebraMap 𝒪 B π}) B''] [Algebra B B'']
        [Algebra (Onr ⧸ Ideal.span {algebraMap 𝒪 Onr π}) B''],
        algebraMap B B'' = (algebraMap (B ⧸ Ideal.span {algebraMap 𝒪 B π}) B'').comp (Ideal.Quotient.mk _) →
        algebraMap (Onr ⧸ Ideal.span {algebraMap 𝒪 Onr π}) B'' =
          (algebraMap (B ⧸ Ideal.span {algebraMap 𝒪 B π}) B'').comp (FakeEllipticCurve.Rigidification.residueLeg π ψ) →
        ∀ (J : Ideal B'') (m : ℕ), J ^ (m + 1) = ⊥ → ∀ s : Fin 2 → B'', (∀ i, s i ∈ J) →
          ∀ PA : Spec (CommRingCat.of B'') ⟶ ρ.Ab.A,
            PA ≫ ρ.Ab.f = Spec.map (CommRingCat.ofHom (algebraMap (B ⧸ Ideal.span {algebraMap 𝒪 B π}) B'')) →
            PA ≫ ρ.gA = (θ₀ B'' s).1 →
              PA ≫ ψ' ≫ ρ.gb = (θ B'' (fun i => MvFormalGroup.nilEval m (σ₁ i) s)).1)

    (h : ℕ) (δ : Series (B ⧸ Ideal.span {algebraMap 𝒪 B π})) (hδ0 : ∀ i, MvPowerSeries.constantCoeff (δ i) = 0)
    (hδσ : δ.comp σ₁ = (X₀.map (FakeEllipticCurve.Rigidification.residueLeg π ψ)).act ((r : Zp2 r) ^ h)) :
    ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of (B ⧸ Ideal.span {algebraMap 𝒪 B π}))) (P : SchemeHomOver t ρ.Ab.f),
      P.1 ≫ ψ' = (ρ.Eb.L.one t).1 → nsmulPt ρ.Ab.L t (r ^ h) P = ρ.Ab.L.one t := by
  classical
  letI algO : Algebra (Onr ⧸ Ideal.span {algebraMap 𝒪 Onr π}) (B ⧸ Ideal.span {algebraMap 𝒪 B π}) :=
    (FakeEllipticCurve.Rigidification.residueLeg π ψ).toAlgebra
  have halgO : algebraMap (Onr ⧸ Ideal.span {algebraMap 𝒪 Onr π}) (B ⧸ Ideal.span {algebraMap 𝒪 B π}) =
      FakeEllipticCurve.Rigidification.residueLeg π ψ := rfl

  have hpbAb : FakeEllipticCurve.IsPullbackVia (algebraMap (Onr ⧸ Ideal.span {algebraMap 𝒪 Onr π}) (B ⧸ Ideal.span {algebraMap 𝒪 B π}))
      A₀ ρ.Ab ρ.gA := by rw [halgO]; exact ρ.isPullback_Ab
  obtain ⟨θA, hθA, hθAg⟩ := CerednikDrinfeld.QM.FakeEllipticCurve.IsPullbackVia.exists_isFormalModuleVia_map_and_comp_eq
      coord (Onr ⧸ Ideal.span {algebraMap 𝒪 Onr π}) (B ⧸ Ideal.span {algebraMap 𝒪 B π}) A₀ ρ.Ab ρ.gA hpbAb X₀ θ₀ hA₀
  have hθA' : ρ.Ab.IsFormalModuleVia coord (X₀.map (FakeEllipticCurve.Rigidification.residueLeg π ψ)) θA := hθA
  obtain ⟨hpbA, hmulA, hactA, -⟩ := hpbAb

  obtain ⟨hφo, hφ'o, hφmul, hφ'mul, hφΛ, hφ'Λ, hdeg⟩ := ρ.isIsogenyPair
  have hφH : IsHom ρ.Eb.L ρ.Ab.L ρ.φ hφo := fun t P Q => hφmul t P Q
  have hψH : IsHom ρ.Ab.L ρ.Eb.L ψ' hψ'f := fun t P Q => Subtype.ext (hψ'hom t P Q)

  have hrd : (((r ^ ρ.d : ℕ) : ℚ) : ℍ[ℚ, a, b]) ∈ Λ := rpow_mem hΛℤ r ρ.d
  have hrh : (((r ^ h : ℕ) : ℚ) : ℍ[ℚ, a, b]) ∈ Λ := rpow_mem hΛℤ r h
  obtain ⟨-, hc2⟩ := hdeg hrd
  have hNd : ρ.Ab.act ⟨_, hrd⟩ = ρ.Ab.L.schemeNsmul (r ^ ρ.d) := act_natCast_eq_schemeNsmul ρ.Ab hΛ1 _ hrd

  have haff : ∀ (C : Type) [CommRing C] [Algebra (B ⧸ Ideal.span {algebraMap 𝒪 B π}) C]
      (P : SchemeHomOver (Scheme.specOver (𝒪 := B ⧸ Ideal.span {algebraMap 𝒪 B π}) C) ρ.Ab.f),
      P.1 ≫ ψ' = (ρ.Eb.L.one (Scheme.specOver (𝒪 := B ⧸ Ideal.span {algebraMap 𝒪 B π}) C)).1 →
        nsmulPt ρ.Ab.L (Scheme.specOver (𝒪 := B ⧸ Ideal.span {algebraMap 𝒪 B π}) C) (r ^ h) P =
          ρ.Ab.L.one (Scheme.specOver (𝒪 := B ⧸ Ideal.span {algebraMap 𝒪 B π}) C) := by
    intro C _ _ P hP
    letI algB : Algebra B C := ((algebraMap (B ⧸ Ideal.span {algebraMap 𝒪 B π}) C).comp (Ideal.Quotient.mk _)).toAlgebra
    letI algOC : Algebra (Onr ⧸ Ideal.span {algebraMap 𝒪 Onr π}) C :=
      ((algebraMap (B ⧸ Ideal.span {algebraMap 𝒪 B π}) C).comp (FakeEllipticCurve.Rigidification.residueLeg π ψ)).toAlgebra
    haveI : IsScalarTower (Onr ⧸ Ideal.span {algebraMap 𝒪 Onr π}) (B ⧸ Ideal.span {algebraMap 𝒪 B π}) C :=
      IsScalarTower.of_algebraMap_eq (fun _ => rfl)
    have h1 : algebraMap B C = (algebraMap (B ⧸ Ideal.span {algebraMap 𝒪 B π}) C).comp (Ideal.Quotient.mk _) := rfl
    have h2 : algebraMap (Onr ⧸ Ideal.span {algebraMap 𝒪 Onr π}) C =
        (algebraMap (B ⧸ Ideal.span {algebraMap 𝒪 B π}) C).comp (FakeEllipticCurve.Rigidification.residueLeg π ψ) := rfl

    have hmapP : mapPt ψ' hψ'f P = ρ.Eb.L.one _ := Subtype.ext hP
    have hφ'P : P.1 ≫ ρ.φ' = (ρ.Eb.L.one (Scheme.specOver (𝒪 := B ⧸ Ideal.span {algebraMap 𝒪 B π}) C)).1 := by
      rw [← hfac, ← Category.assoc, val_comp_schemeNsmul]
      have key := hψH.nsmulPt_map _ (r ^ k) P
      rw [hmapP, nsmulPt_one] at key
      exact congrArg Subtype.val key
    have hPt : nsmulPt ρ.Ab.L (Scheme.specOver (𝒪 := B ⧸ Ideal.span {algebraMap 𝒪 B π}) C) (r ^ ρ.d) P = ρ.Ab.L.one _ := by
      apply Subtype.ext
      rw [← val_comp_schemeNsmul, ← hNd, ← hc2, ← Category.assoc, hφ'P]
      exact congrArg Subtype.val (hφH.map_one _)

    obtain ⟨J, hJnil, hPinf⟩ :=
      CerednikDrinfeld.QM.FakeEllipticCurve.exists_isNilpotent_isInfinitesimal_of_nsmulPt_pow_eq_one_of_one_mem
        coord hcoord hΛ1 (B ⧸ Ideal.span {algebraMap 𝒪 B π}) hBr ρ.Ab _ θA hθA C ρ.d P hPt
    obtain ⟨m, hm⟩ := hJnil
    have hJm : J ^ (m + 1) = ⊥ := by rw [pow_succ, hm, zero_mul]; rfl
    obtain ⟨-, hinjA, hontoA, hhomA⟩ := hθA.1.2 C J m hJm
    obtain ⟨s, hs, hsP⟩ := hontoA P hPinf
    have hsnil : ∀ i, IsNilpotent (s i) := fun i => isNilpotent_of_mem hJm (hs i)
    have hPg : P.1 ≫ ρ.gA = (θ₀ C s).1 := by rw [← hsP]; exact hθAg C s hsnil

    have hrep := hσ₁rep C h1 h2 J m hJm s hs P.1 P.2 hPg
    obtain ⟨-, hinjE, -, hhomE⟩ := hX.1.2 C J m hJm
    have hzero : ∀ i, (0 : Fin 2 → C) i ∈ J := fun _ => J.zero_mem
    have hθ0 : θ C 0 = E.L.one _ := by
      apply eq_one_of_mul_self
      rw [← hhomE 0 0 hzero hzero, nilMul_zero]
    have hθA0 : θA C 0 = ρ.Ab.L.one _ := by
      apply eq_one_of_mul_self
      rw [← hhomA 0 0 hzero hzero, nilMul_zero]
    obtain ⟨hpbE, hmulE, -, -⟩ := ρ.isPullback_Eb
    have hbaseE : Scheme.specOver (𝒪 := B) C =
        Scheme.specOver (𝒪 := B ⧸ Ideal.span {algebraMap 𝒪 B π}) C ≫
          Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (Ideal.span {algebraMap 𝒪 B π}))) := by
      show Spec.map (CommRingCat.ofHom (algebraMap B C)) = _
      rw [h1, CommRingCat.ofHom_comp, Spec.map_comp]
    have hone_gb : (ρ.Eb.L.one (Scheme.specOver (𝒪 := B ⧸ Ideal.span {algebraMap 𝒪 B π}) C)).1 ≫ ρ.gb =
        (E.L.one (Scheme.specOver (𝒪 := B) C)).1 := by
      rw [hbaseE]
      have key := hmulE (Scheme.specOver (𝒪 := B ⧸ Ideal.span {algebraMap 𝒪 B π}) C) (ρ.Eb.L.one _) (ρ.Eb.L.one _)
      rw [ρ.Eb.L.one_mul] at key
      have hx := eq_one_of_mul_self E.L _
        ⟨(ρ.Eb.L.one (Scheme.specOver (𝒪 := B ⧸ Ideal.span {algebraMap 𝒪 B π}) C)).1 ≫ ρ.gb, by
          rw [Category.assoc, hpbE.w, ← Category.assoc, (ρ.Eb.L.one _).2]⟩ (Subtype.ext key.symm)
      exact congrArg Subtype.val hx
    have hσ₁J : ∀ j, MvFormalGroup.nilEval m (σ₁ j) s ∈ J :=
      (MvFormalGroup.nilEval_subst_of_mem J m hJm s hs σ₁ hσ₁ 0).1
    have hσ₁s : (fun i => MvFormalGroup.nilEval m (σ₁ i) s) = 0 := by
      apply hinjE _ _ hσ₁J hzero
      rw [hθ0]
      apply Subtype.ext
      rw [← hrep, ← Category.assoc, hP, hone_gb]

    have hns : (fun i => MvFormalGroup.nilEval m
        ((((r ^ h : ℕ) : MvFormalGroup.End (X₀.map (FakeEllipticCurve.Rigidification.residueLeg π ψ)).F)).toPowerSeries i)
          s) = (0 : Fin 2 → C) := by
      rw [← act_pow_eq (X₀.map (FakeEllipticCurve.Rigidification.residueLeg π ψ)) h, ← hδσ]
      funext i
      show MvFormalGroup.nilEval m (MvPowerSeries.subst σ₁ (δ i)) s = 0
      rw [(MvFormalGroup.nilEval_subst_of_mem J m hJm s hs σ₁ hσ₁ (δ i)).2, hσ₁s]
      exact nilEval_zero m (δ i) (hδ0 i)

    have key := CerednikDrinfeld.QM.FakeEllipticCurve.apply_nilEval_natCast_eq_mapPt_act_of_isFormalModuleVia ρ.Ab coord hcoord
      (X₀.map (FakeEllipticCurve.Rigidification.residueLeg π ψ)) θA hθA' hΛ1 (r ^ h) hrh C J m hJm s hs
    rw [hns, hθA0, hsP] at key
    rw [← CerednikDrinfeld.QM.FakeEllipticCurve.pushPt_act_natCast_eq_nsmulPt ρ.Ab hΛ1 (r ^ h) hrh _ P]
    exact key.symm

  intro T t P hP
  exact forall_nsmulPt_eq_one_of_comp_eq_one_of_forall_specOver ρ.Ab.L ρ.Eb.L ψ' (r ^ h) haff t P hP

end S_CerednikDrinfeld_QM_FakeEllipticCurve_Rigidification_nsmulPt_pow_eq_one_of_comp_eq_one_of_represents_of_comp_eq_act_pow
end P2MW
export P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_Rigidification_nsmulPt_pow_eq_one_of_comp_eq_one_of_represents_of_comp_eq_act_pow (solution)
