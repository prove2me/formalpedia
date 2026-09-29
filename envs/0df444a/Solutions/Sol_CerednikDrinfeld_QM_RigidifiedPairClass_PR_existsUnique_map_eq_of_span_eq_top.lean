-- Prove2me | solution 1 for CerednikDrinfeld.QM.RigidifiedPairClass.PR.existsUnique_map_eq_of_span_eq_top
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.141142+00:00
-- url     : https://prove2.me/submissions/64fcb6dd-bc96-5d1f-9941-fe466dfd9fca

import Mathlib
import Definitions.Def_CerednikDrinfeld_RigidifiedPairClassModel
import Theorems.Thm_AlgebraicGeometry_Scheme_section_ext_and_exists_section_of_isLocalizationAway_of_span_eq_top
import Theorems.Thm_CerednikDrinfeld_QM_IsFineModuli_exists_strata_point_locally_corr_of_span_eq_top
import Theorems.Thm_CerednikDrinfeld_QM_RigidifiedPairClass_rel_equivalence
import Theorems.Thm_CerednikDrinfeld_QM_RigidifiedPairClass_rel_of_forall_rel_map
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_QM_RigidifiedPairClass_PR_existsUnique_map_eq_of_span_eq_top
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
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry QuaternionAlgebra CerednikDrinfeld CerednikDrinfeld.QM NeronModelInfra

namespace Ws16SH

variable {C : Type} [CommRing C] {X : Scheme.{0}} (g : X ⟶ Spec (CommRingCat.of C))

theorem specMap_algebraMap_comp (A B : Type) [CommRing A] [CommRing B] [Algebra C A] [Algebra A B]
    [Algebra C B] [IsScalarTower C A B] :
    Spec.map (CommRingCat.ofHom (algebraMap A B)) ≫ Spec.map (CommRingCat.ofHom (algebraMap C A)) =
      Spec.map (CommRingCat.ofHom (algebraMap C B)) := by
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, ← IsScalarTower.algebraMap_eq C A B]

noncomputable def toAwayRight {A : Type} [CommRing A] (a b : A) (S P : Type) [CommRing S] [Algebra A S]
    [IsLocalization.Away a S] [CommRing P] [Algebra A P] [IsLocalization.Away (a * b) P] : S →ₐ[A] P :=
  { IsLocalization.Away.awayToAwayRight a b (S := S) (P := P) with
    commutes' := fun x => IsLocalization.Away.awayToAwayRight_eq a b x }

noncomputable def toAwayLeft {A : Type} [CommRing A] (a b : A) (S P : Type) [CommRing S] [Algebra A S]
    [IsLocalization.Away b S] [CommRing P] [Algebra A P] [IsLocalization.Away (a * b) P] : S →ₐ[A] P :=
  { IsLocalization.Away.awayToAwayLeft b a (S := S) (P := P) with
    commutes' := fun x => IsLocalization.Away.awayToAwayLeft_eq b a x }

@[scoped simp] theorem toAwayRight_toRingHom {A : Type} [CommRing A] (a b : A) (S P : Type) [CommRing S] [Algebra A S]
    [IsLocalization.Away a S] [CommRing P] [Algebra A P] [IsLocalization.Away (a * b) P] :
    (toAwayRight a b S P).toRingHom = IsLocalization.Away.awayToAwayRight a b := rfl

@[scoped simp] theorem toAwayLeft_toRingHom {A : Type} [CommRing A] (a b : A) (S P : Type) [CommRing S] [Algebra A S]
    [IsLocalization.Away b S] [CommRing P] [Algebra A P] [IsLocalization.Away (a * b) P] :
    (toAwayLeft a b S P).toRingHom = IsLocalization.Away.awayToAwayLeft b a := rfl

section core

variable (A : Type) [CommRing A] [Algebra C A] (n : ℕ) (f : Fin n → A)
  (hf : Ideal.span (Set.range f) = ⊤)
  (B : Fin n → Type) [∀ i, CommRing (B i)] [∀ i, Algebra A (B i)] [∀ i, IsLocalization.Away (f i) (B i)]

include f hf

theorem points_ext
    (x x' : Spec (CommRingCat.of A) ⟶ X)
    (hx : x ≫ g = Spec.map (CommRingCat.ofHom (algebraMap C A)))
    (hx' : x' ≫ g = Spec.map (CommRingCat.ofHom (algebraMap C A)))
    (h : ∀ i, Spec.map (CommRingCat.ofHom (algebraMap A (B i))) ≫ x =
      Spec.map (CommRingCat.ofHom (algebraMap A (B i))) ≫ x') : x = x' := by
  have key := (AlgebraicGeometry.Scheme.section_ext_and_exists_section_of_isLocalizationAway_of_span_eq_top
    (pullback.snd g (Spec.map (CommRingCat.ofHom (algebraMap C A)))) n f hf B
    (fun i j => Localization.Away (f i * f j))
    (fun i j => IsLocalization.Away.awayToAwayRight (f i) (f j))
    (fun i j => IsLocalization.Away.awayToAwayLeft (f j) (f i))
    (fun i j => by ext a; simp [IsLocalization.Away.awayToAwayRight_eq])
    (fun i j => by ext a; simp [IsLocalization.Away.awayToAwayLeft_eq])).1
  have e := key
    (pullback.lift x (𝟙 _) (by rw [hx, Category.id_comp]))
    (pullback.lift x' (𝟙 _) (by rw [hx', Category.id_comp]))
    (pullback.lift_snd _ _ _) (pullback.lift_snd _ _ _)
    (fun i => by
      apply pullback.hom_ext
      · rw [Category.assoc, Category.assoc, pullback.lift_fst, pullback.lift_fst]
        exact h i
      · rw [Category.assoc, Category.assoc, pullback.lift_snd, pullback.lift_snd])
  have e' := congrArg (fun s => s ≫ pullback.fst g (Spec.map (CommRingCat.ofHom (algebraMap C A)))) e
  simpa only [pullback.lift_fst] using e'

theorem points_glue [∀ i, Algebra C (B i)] [∀ i, IsScalarTower C A (B i)]
    (p : ∀ i, Spec (CommRingCat.of (B i)) ⟶ X)
    (hp : ∀ i, p i ≫ g = Spec.map (CommRingCat.ofHom (algebraMap C (B i))))
    (hov : ∀ i j,
      Spec.map (CommRingCat.ofHom
        (IsLocalization.Away.awayToAwayRight (f i) (f j) (S := B i) (P := Localization.Away (f i * f j)))) ≫ p i =
      Spec.map (CommRingCat.ofHom
        (IsLocalization.Away.awayToAwayLeft (f j) (f i) (S := B j) (P := Localization.Away (f i * f j)))) ≫ p j) :
    ∃ x : Spec (CommRingCat.of A) ⟶ X, x ≫ g = Spec.map (CommRingCat.ofHom (algebraMap C A)) ∧
      ∀ i, Spec.map (CommRingCat.ofHom (algebraMap A (B i))) ≫ x = p i := by
  have hl : ∀ i j, (IsLocalization.Away.awayToAwayRight (f i) (f j) (S := B i)
      (P := Localization.Away (f i * f j))).comp (algebraMap A (B i)) = algebraMap A (Localization.Away (f i * f j)) :=
    fun i j => by ext a; simp [IsLocalization.Away.awayToAwayRight_eq]
  have hr : ∀ i j, (IsLocalization.Away.awayToAwayLeft (f j) (f i) (S := B j)
      (P := Localization.Away (f i * f j))).comp (algebraMap A (B j)) = algebraMap A (Localization.Away (f i * f j)) :=
    fun i j => by ext a; simp [IsLocalization.Away.awayToAwayLeft_eq]
  have key := (AlgebraicGeometry.Scheme.section_ext_and_exists_section_of_isLocalizationAway_of_span_eq_top
    (pullback.snd g (Spec.map (CommRingCat.ofHom (algebraMap C A)))) n f hf B
    (fun i j => Localization.Away (f i * f j))
    (fun i j => IsLocalization.Away.awayToAwayRight (f i) (f j))
    (fun i j => IsLocalization.Away.awayToAwayLeft (f j) (f i)) hl hr).2

  have hcond : ∀ i, p i ≫ g =
      Spec.map (CommRingCat.ofHom (algebraMap A (B i))) ≫ Spec.map (CommRingCat.ofHom (algebraMap C A)) :=
    fun i => by rw [hp i, specMap_algebraMap_comp]
  obtain ⟨sec, hsec, hseci⟩ := key
    (fun i => pullback.lift (p i) (Spec.map (CommRingCat.ofHom (algebraMap A (B i)))) (hcond i))
    (fun i => pullback.lift_snd _ _ _)
    (fun i j => by
      apply pullback.hom_ext
      · rw [Category.assoc, Category.assoc, pullback.lift_fst, pullback.lift_fst]
        exact hov i j
      · rw [Category.assoc, Category.assoc, pullback.lift_snd, pullback.lift_snd,
          ← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp, hl, hr])
  refine ⟨sec ≫ pullback.fst g (Spec.map (CommRingCat.ofHom (algebraMap C A))), ?_, fun i => ?_⟩
  · rw [Category.assoc, pullback.condition, ← Category.assoc, hsec, Category.id_comp]
  · rw [← Category.assoc, hseci i, pullback.lift_fst]

theorem points_glue_of_forall [∀ i, Algebra C (B i)] [∀ i, IsScalarTower C A (B i)]
    (p : ∀ i, Spec (CommRingCat.of (B i)) ⟶ X)
    (hp : ∀ i, p i ≫ g = Spec.map (CommRingCat.ofHom (algebraMap C (B i))))
    (hov : ∀ (i j : Fin n) (D : Type) [CommRing D] [Algebra A D] [Algebra C D] [IsScalarTower C A D]
      [IsLocalization.Away (f i * f j) D] (ρ₁ : B i →ₐ[A] D) (ρ₂ : B j →ₐ[A] D),
      Spec.map (CommRingCat.ofHom ρ₁.toRingHom) ≫ p i = Spec.map (CommRingCat.ofHom ρ₂.toRingHom) ≫ p j) :
    ∃ x : Spec (CommRingCat.of A) ⟶ X, x ≫ g = Spec.map (CommRingCat.ofHom (algebraMap C A)) ∧
      ∀ i, Spec.map (CommRingCat.ofHom (algebraMap A (B i))) ≫ x = p i := by
  refine points_glue g A n f hf B p hp fun i j => ?_
  have := hov i j (Localization.Away (f i * f j))
    (toAwayRight (f i) (f j) (B i) (Localization.Away (f i * f j)))
    (toAwayLeft (f i) (f j) (B j) (Localization.Away (f i * f j)))
  simpa only [toAwayRight_toRingHom, toAwayLeft_toRingHom] using this

theorem existsUnique_point_of_forall [∀ i, Algebra C (B i)] [∀ i, IsScalarTower C A (B i)]
    (p : ∀ i, NeronModelInfra.SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap C (B i)))) g)
    (hov : ∀ (i j : Fin n) (D : Type) [CommRing D] [Algebra A D] [Algebra C D] [IsScalarTower C A D]
      [IsLocalization.Away (f i * f j) D] (ρ₁ : B i →ₐ[A] D) (ρ₂ : B j →ₐ[A] D),
      Spec.map (CommRingCat.ofHom ρ₁.toRingHom) ≫ (p i).1 = Spec.map (CommRingCat.ofHom ρ₂.toRingHom) ≫ (p j).1) :
    ∃! x : NeronModelInfra.SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap C A))) g,
      ∀ i, Spec.map (CommRingCat.ofHom (algebraMap A (B i))) ≫ x.1 = (p i).1 := by
  obtain ⟨x, hx, hxi⟩ := points_glue_of_forall g A n f hf B (fun i => (p i).1) (fun i => (p i).2) hov
  refine ⟨⟨x, hx⟩, hxi, fun y hy => Subtype.ext ?_⟩
  exact points_ext g A n f hf B y.1 x y.2 hx fun i => by rw [hy i, hxi i]

end core

section modpi

variable (ϖ : C)

abbrev piIdeal (T : Type) [CommRing T] [Algebra C T] : Ideal T := Ideal.span {algebraMap C T ϖ}

theorem piIdeal_le_comap (A B : Type) [CommRing A] [CommRing B] [Algebra C A] [Algebra A B]
    [Algebra C B] [IsScalarTower C A B] :
    piIdeal ϖ A ≤ (piIdeal ϖ B).comap (algebraMap A B) := by
  rw [piIdeal, Ideal.span_le, Set.singleton_subset_iff, SetLike.mem_coe, Ideal.mem_comap,
    ← IsScalarTower.algebraMap_apply]
  exact Ideal.subset_span rfl

theorem piIdeal_map (A B : Type) [CommRing A] [CommRing B] [Algebra C A] [Algebra A B]
    [Algebra C B] [IsScalarTower C A B] :
    (piIdeal ϖ A).map (algebraMap A B) = piIdeal ϖ B := by
  rw [piIdeal, piIdeal, Ideal.map_span, Set.image_singleton, ← IsScalarTower.algebraMap_apply]

@[reducible] noncomputable def algebraModPi (A B : Type) [CommRing A] [CommRing B] [Algebra C A] [Algebra A B]
    [Algebra C B] [IsScalarTower C A B] : Algebra (A ⧸ piIdeal ϖ A) (B ⧸ piIdeal ϖ B) :=
  (Ideal.quotientMap (piIdeal ϖ B) (algebraMap A B) (piIdeal_le_comap ϖ A B)).toAlgebra

theorem algebraMap_modPi_mk (A B : Type) [CommRing A] [CommRing B] [Algebra C A] [Algebra A B]
    [Algebra C B] [IsScalarTower C A B] (a : A) :
    letI := algebraModPi ϖ A B
    algebraMap (A ⧸ piIdeal ϖ A) (B ⧸ piIdeal ϖ B) (Ideal.Quotient.mk _ a) =
      Ideal.Quotient.mk _ (algebraMap A B a) := rfl

theorem isScalarTower_modPi (A B : Type) [CommRing A] [CommRing B] [Algebra C A] [Algebra A B]
    [Algebra C B] [IsScalarTower C A B] :
    letI := algebraModPi ϖ A B
    IsScalarTower C (A ⧸ piIdeal ϖ A) (B ⧸ piIdeal ϖ B) := by
  letI := algebraModPi ϖ A B
  refine IsScalarTower.of_algebraMap_eq fun c => ?_
  show Ideal.Quotient.mk (piIdeal ϖ B) (algebraMap C B c) =
    Ideal.quotientMap (piIdeal ϖ B) (algebraMap A B) (piIdeal_le_comap ϖ A B)
      (Ideal.Quotient.mk (piIdeal ϖ A) (algebraMap C A c))
  rw [Ideal.quotientMap_mk, ← IsScalarTower.algebraMap_apply]

theorem isLocalizationAway_modPi (A B : Type) [CommRing A] [CommRing B] [Algebra C A] [Algebra A B]
    [Algebra C B] [IsScalarTower C A B] (a : A) [IsLocalization.Away a B] :
    letI := algebraModPi ϖ A B
    IsLocalization.Away (Ideal.Quotient.mk (piIdeal ϖ A) a) (B ⧸ piIdeal ϖ B) := by
  letI := algebraModPi ϖ A B
  show IsLocalization (Submonoid.powers (Ideal.Quotient.mk (piIdeal ϖ A) a)) (B ⧸ piIdeal ϖ B)
  rw [← Submonoid.map_powers]
  refine IsLocalization.of_surjective (Submonoid.powers a) B (Ideal.Quotient.mk (piIdeal ϖ A))
    Ideal.Quotient.mk_surjective (Ideal.Quotient.mk (piIdeal ϖ B)) Ideal.Quotient.mk_surjective ?_ ?_
  · exact (Ideal.quotientMap_comp_mk (piIdeal_le_comap ϖ A B)).symm
  · rw [Ideal.mk_ker, Ideal.mk_ker, piIdeal_map]

theorem span_range_mk_eq_top (A : Type) [CommRing A] [Algebra C A] {n : ℕ} (f : Fin n → A)
    (hf : Ideal.span (Set.range f) = ⊤) :
    Ideal.span (Set.range fun i => Ideal.Quotient.mk (piIdeal ϖ A) (f i)) = ⊤ := by
  have : (Set.range fun i => Ideal.Quotient.mk (piIdeal ϖ A) (f i)) = Ideal.Quotient.mk (piIdeal ϖ A) '' Set.range f := by
    rw [← Set.range_comp]; rfl
  rw [this, ← Ideal.map_span, hf, Ideal.map_top]

noncomputable def reduceModPi (A : Type) [CommRing A] [Algebra C A] {S D : Type} [CommRing S] [CommRing D]
    [Algebra A S] [Algebra A D] [Algebra C S] [Algebra C D]
    [IsScalarTower C A S] [IsScalarTower C A D] (ρ : S →ₐ[A] D) :
    (S ⧸ piIdeal ϖ S) →ₐ[C] (D ⧸ piIdeal ϖ D) :=
  Ideal.quotientMapₐ (piIdeal ϖ D) (ρ.restrictScalars C) (by
    rw [piIdeal, Ideal.span_le, Set.singleton_subset_iff, SetLike.mem_coe, Ideal.mem_comap, AlgHom.coe_restrictScalars',
      IsScalarTower.algebraMap_apply C A S, AlgHom.commutes, ← IsScalarTower.algebraMap_apply]
    exact Ideal.subset_span rfl)

theorem reduceModPi_mk (A : Type) [CommRing A] [Algebra C A] {S D : Type} [CommRing S] [CommRing D]
    [Algebra A S] [Algebra A D] [Algebra C S] [Algebra C D]
    [IsScalarTower C A S] [IsScalarTower C A D] (ρ : S →ₐ[A] D) (s : S) :
    reduceModPi ϖ A ρ (Ideal.Quotient.mk _ s) = Ideal.Quotient.mk _ (ρ s) := rfl

end modpi

section gen

variable (A : Type) [CommRing A] [Algebra C A] (n : ℕ) (f : Fin n → A)
  (hf : Ideal.span (Set.range f) = ⊤)
  (B : Fin n → Type) [∀ i, CommRing (B i)] [∀ i, Algebra A (B i)] [∀ i, IsLocalization.Away (f i) (B i)]

include f hf

theorem points_glue_gen [∀ i, Algebra C (B i)] [∀ i, IsScalarTower C A (B i)]
    (L₂ : Fin n → Fin n → Type) [∀ i j, CommRing (L₂ i j)] [∀ i j, Algebra A (L₂ i j)]
    [∀ i j, IsLocalization.Away (f i * f j) (L₂ i j)]
    (l : ∀ i j, B i →+* L₂ i j) (r : ∀ i j, B j →+* L₂ i j)
    (hl : ∀ i j, (l i j).comp (algebraMap A (B i)) = algebraMap A (L₂ i j))
    (hr : ∀ i j, (r i j).comp (algebraMap A (B j)) = algebraMap A (L₂ i j))
    (p : ∀ i, Spec (CommRingCat.of (B i)) ⟶ X)
    (hp : ∀ i, p i ≫ g = Spec.map (CommRingCat.ofHom (algebraMap C (B i))))
    (hov : ∀ i j, Spec.map (CommRingCat.ofHom (l i j)) ≫ p i = Spec.map (CommRingCat.ofHom (r i j)) ≫ p j) :
    ∃ x : Spec (CommRingCat.of A) ⟶ X, x ≫ g = Spec.map (CommRingCat.ofHom (algebraMap C A)) ∧
      ∀ i, Spec.map (CommRingCat.ofHom (algebraMap A (B i))) ≫ x = p i := by
  have key := (AlgebraicGeometry.Scheme.section_ext_and_exists_section_of_isLocalizationAway_of_span_eq_top
    (pullback.snd g (Spec.map (CommRingCat.ofHom (algebraMap C A)))) n f hf B L₂ l r hl hr).2
  have hcond : ∀ i, p i ≫ g =
      Spec.map (CommRingCat.ofHom (algebraMap A (B i))) ≫ Spec.map (CommRingCat.ofHom (algebraMap C A)) :=
    fun i => by rw [hp i, specMap_algebraMap_comp]
  obtain ⟨sec, hsec, hseci⟩ := key
    (fun i => pullback.lift (p i) (Spec.map (CommRingCat.ofHom (algebraMap A (B i)))) (hcond i))
    (fun i => pullback.lift_snd _ _ _)
    (fun i j => by
      apply pullback.hom_ext
      · rw [Category.assoc, Category.assoc, pullback.lift_fst, pullback.lift_fst]
        exact hov i j
      · rw [Category.assoc, Category.assoc, pullback.lift_snd, pullback.lift_snd,
          ← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp, hl, hr])
  refine ⟨sec ≫ pullback.fst g (Spec.map (CommRingCat.ofHom (algebraMap C A))), ?_, fun i => ?_⟩
  · rw [Category.assoc, pullback.condition, ← Category.assoc, hsec, Category.id_comp]
  · rw [← Category.assoc, hseci i, pullback.lift_fst]

end gen

section modpi_glue

variable (ϖ : C) (A : Type) [CommRing A] [Algebra C A] (n : ℕ) (f : Fin n → A)
  (hf : Ideal.span (Set.range f) = ⊤)
  (B : Fin n → Type) [∀ i, CommRing (B i)] [∀ i, Algebra A (B i)] [∀ i, IsLocalization.Away (f i) (B i)]
  [∀ i, Algebra C (B i)] [∀ i, IsScalarTower C A (B i)]

include f hf

theorem points_ext_modPi
    (x x' : Spec (CommRingCat.of (A ⧸ piIdeal ϖ A)) ⟶ X)
    (hx : x ≫ g = Spec.map (CommRingCat.ofHom (algebraMap C (A ⧸ piIdeal ϖ A))))
    (hx' : x' ≫ g = Spec.map (CommRingCat.ofHom (algebraMap C (A ⧸ piIdeal ϖ A))))
    (h : ∀ i, Spec.map (CommRingCat.ofHom (Ideal.quotientMap (piIdeal ϖ (B i)) (algebraMap A (B i))
        (piIdeal_le_comap ϖ A (B i)))) ≫ x =
      Spec.map (CommRingCat.ofHom (Ideal.quotientMap (piIdeal ϖ (B i)) (algebraMap A (B i))
        (piIdeal_le_comap ϖ A (B i)))) ≫ x') : x = x' := by
  letI : ∀ i, Algebra (A ⧸ piIdeal ϖ A) (B i ⧸ piIdeal ϖ (B i)) := fun i => algebraModPi ϖ A (B i)
  haveI : ∀ i, IsLocalization.Away (Ideal.Quotient.mk (piIdeal ϖ A) (f i)) (B i ⧸ piIdeal ϖ (B i)) :=
    fun i => isLocalizationAway_modPi ϖ A (B i) (f i)
  exact points_ext g (A ⧸ piIdeal ϖ A) n (fun i => Ideal.Quotient.mk (piIdeal ϖ A) (f i))
    (span_range_mk_eq_top ϖ A f hf) (fun i => B i ⧸ piIdeal ϖ (B i)) x x' hx hx' h

theorem points_glue_modPi_of_forall
    (p : ∀ i, Spec (CommRingCat.of (B i ⧸ piIdeal ϖ (B i))) ⟶ X)
    (hp : ∀ i, p i ≫ g = Spec.map (CommRingCat.ofHom (algebraMap C (B i ⧸ piIdeal ϖ (B i)))))
    (hov : ∀ (i j : Fin n) (D : Type) [CommRing D] [Algebra A D] [Algebra C D] [IsScalarTower C A D]
      [IsLocalization.Away (f i * f j) D] (ρ₁ : B i →ₐ[A] D) (ρ₂ : B j →ₐ[A] D),
      Spec.map (CommRingCat.ofHom (reduceModPi ϖ A ρ₁).toRingHom) ≫ p i =
        Spec.map (CommRingCat.ofHom (reduceModPi ϖ A ρ₂).toRingHom) ≫ p j) :
    ∃ x : Spec (CommRingCat.of (A ⧸ piIdeal ϖ A)) ⟶ X,
      x ≫ g = Spec.map (CommRingCat.ofHom (algebraMap C (A ⧸ piIdeal ϖ A))) ∧
      ∀ i, Spec.map (CommRingCat.ofHom (Ideal.quotientMap (piIdeal ϖ (B i)) (algebraMap A (B i))
        (piIdeal_le_comap ϖ A (B i)))) ≫ x = p i := by
  letI : ∀ i, Algebra (A ⧸ piIdeal ϖ A) (B i ⧸ piIdeal ϖ (B i)) := fun i => algebraModPi ϖ A (B i)
  haveI : ∀ i, IsLocalization.Away (Ideal.Quotient.mk (piIdeal ϖ A) (f i)) (B i ⧸ piIdeal ϖ (B i)) :=
    fun i => isLocalizationAway_modPi ϖ A (B i) (f i)
  haveI : ∀ i, IsScalarTower C (A ⧸ piIdeal ϖ A) (B i ⧸ piIdeal ϖ (B i)) := fun i => isScalarTower_modPi ϖ A (B i)

  let L : Fin n → Fin n → Type := fun i j => Localization.Away (f i * f j)
  letI : ∀ i j, Algebra (A ⧸ piIdeal ϖ A) (L i j ⧸ piIdeal ϖ (L i j)) := fun i j => algebraModPi ϖ A (L i j)
  haveI : ∀ i j, IsLocalization.Away (Ideal.Quotient.mk (piIdeal ϖ A) (f i) * Ideal.Quotient.mk (piIdeal ϖ A) (f j))
      (L i j ⧸ piIdeal ϖ (L i j)) := fun i j => by
    rw [← map_mul]; exact isLocalizationAway_modPi ϖ A (L i j) (f i * f j)
  refine points_glue_gen g (A ⧸ piIdeal ϖ A) n (fun i => Ideal.Quotient.mk (piIdeal ϖ A) (f i))
    (span_range_mk_eq_top ϖ A f hf) (fun i => B i ⧸ piIdeal ϖ (B i))
    (fun i j => L i j ⧸ piIdeal ϖ (L i j))
    (fun i j => (reduceModPi ϖ A (toAwayRight (f i) (f j) (B i) (L i j))).toRingHom)
    (fun i j => (reduceModPi ϖ A (toAwayLeft (f i) (f j) (B j) (L i j))).toRingHom)
    (fun i j => ?_) (fun i j => ?_) p hp (fun i j => hov i j (L i j) _ _)
  · refine RingHom.ext fun a => ?_
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective a
    show reduceModPi ϖ A _ (Ideal.Quotient.mk _ (algebraMap A (B i) a)) = Ideal.Quotient.mk _ (algebraMap A (L i j) a)
    rw [reduceModPi_mk, AlgHom.commutes]
  · refine RingHom.ext fun a => ?_
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective a
    show reduceModPi ϖ A _ (Ideal.Quotient.mk _ (algebraMap A (B j) a)) = Ideal.Quotient.mk _ (algebraMap A (L i j) a)
    rw [reduceModPi_mk, AlgHom.commutes]

end modpi_glue

end Ws16SH
p2m_reactivate "P2MW.S_CerednikDrinfeld_QM_RigidifiedPairClass_PR_existsUnique_map_eq_of_span_eq_top.Ws16SH"

open CerednikDrinfeld.QM.RigidifiedPairClass in
theorem solution
    {r N : ℕ} [Fact r.Prime] [NeZero N] (hrN : ¬ r ∣ N) {rbar : ℕ} [Fact rbar.Prime] (hrr : rbar ≠ r)

    (𝒪 : Type) [CommRing 𝒪] (π : 𝒪) (hunr : Ideal.span {((r : ℕ) : 𝒪)} = Ideal.span {π}) (Onr : Type) [CommRing Onr] [Algebra 𝒪 Onr]
    {a b : ℚ} (hBq : IsIndefiniteRamifiedExactlyAt a b r rbar)
    (Λ : Submodule ℤ ℍ[ℚ, a, b]) (hΛ : IsMaximalOrder Λ) (hΛℤ : ∀ m : ℤ, ((m : ℚ) : ℍ[ℚ, a, b]) ∈ Λ)

    (coord : ↥Λ → Zp2 r × Zp2 r) (hcoord : IsOrderCoord Λ r coord)
    (A₀ : FakeEllipticCurve Λ N (Onr ⧸ Ideal.span {algebraMap 𝒪 Onr π}))

    (n : ℕ) (hn : 3 ≤ n) (hrn : ¬ r ∣ n) (M : Scheme.{0}) (fM : M ⟶ Spec (CommRingCat.of 𝒪))
    (ptF : ∀ (S : Type) [CommRing S] (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of 𝒪)),
      FakeEllipticCurve.WithFullLevel Λ N n S → SchemeHomOver s fM)
    (hM : IsFineModuli Λ N n M fM ptF)

    (C : Type) [CommRing C] [IsNoetherianRing C] [Algebra 𝒪 C] (hC : IsNilpotent (algebraMap 𝒪 C π)) (ψ : Onr →ₐ[𝒪] C)

    (X : ℕ → Scheme.{0}) (ξ : ∀ d, X d ⟶ Limits.pullback fM (Spec.map (CommRingCat.ofHom (algebraMap 𝒪 C))))

    (tM : ∀ (T : Type) [CommRing T] [Algebra C T],
      FakeEllipticCurve.WithFullLevel Λ N n T → SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap C T))) (Limits.pullback.snd fM (Spec.map (CommRingCat.ofHom (algebraMap 𝒪 C)))))
    (xOf : ∀ (T : Type) [CommRing T] [Algebra C T] [Algebra 𝒪 T] [IsScalarTower 𝒪 C T]
      (ψT : Onr →ₐ[𝒪] T) (_ : ψT = (IsScalarTower.toAlgHom 𝒪 C T).comp ψ)
      (u : FakeEllipticCurve.WithFullLevel Λ N n T) (ρ : FakeEllipticCurve.Rigidification r π A₀ ψT u.1),
      { x : Spec (CommRingCat.of (T ⧸ Ideal.span {algebraMap C T (algebraMap 𝒪 C π)})) ⟶ X ρ.d //
        x ≫ ξ ρ.d = Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (Ideal.span {algebraMap C T (algebraMap 𝒪 C π)}))) ≫ (tM T u).1 })

    (hx2 : (∀ (d : ℕ) (T T' : Type) [CommRing T] [Algebra C T] [Algebra 𝒪 T] [IsScalarTower 𝒪 C T]
                [CommRing T'] [Algebra C T'] [Algebra 𝒪 T'] [IsScalarTower 𝒪 C T'] (φ : T →ₐ[C] T')
                (ψT : Onr →ₐ[𝒪] T) (hψT : ψT = (IsScalarTower.toAlgHom 𝒪 C T).comp ψ)
                (hψT' : (φ.restrictScalars 𝒪).comp ψT = (IsScalarTower.toAlgHom 𝒪 C T').comp ψ)
                (u : FakeEllipticCurve.WithFullLevel Λ N n T) (u' : FakeEllipticCurve.WithFullLevel Λ N n T')
                (ρ : FakeEllipticCurve.Rigidification r π A₀ ψT u.1)
                (ρ' : FakeEllipticCurve.Rigidification r π A₀ ((φ.restrictScalars 𝒪).comp ψT) u'.1)
                (g : u'.1.A ⟶ u.1.A) (hg : FakeEllipticCurve.IsPullbackVia (φ : T →+* T') u.1 u'.1 g)
                (hd : ρ.d = d) (hd' : ρ'.d = d) (h0 : algebraMap C T (algebraMap 𝒪 C π) = 0) (h0' : algebraMap C T' (algebraMap 𝒪 C π) = 0),
                (u'.2.P).1 ≫ g = Spec.map (CommRingCat.ofHom (φ : T →+* T')) ≫ (u.2.P).1 →
                FakeEllipticCurve.Rigidification.IsPullbackVia (φ.restrictScalars 𝒪) g hg ρ ρ' →
                  (RigidifiedPairClass.ptX 𝒪 π Onr Λ A₀ n C ψ (Limits.pullback.snd fM (Spec.map (CommRingCat.ofHom (algebraMap 𝒪 C)))) X ξ tM xOf d T' ((φ.restrictScalars 𝒪).comp ψT) hψT' u' ρ' hd' h0').1 =
                    Spec.map (CommRingCat.ofHom (φ : T →+* T')) ≫ (RigidifiedPairClass.ptX 𝒪 π Onr Λ A₀ n C ψ (Limits.pullback.snd fM (Spec.map (CommRingCat.ofHom (algebraMap 𝒪 C)))) X ξ tM xOf d T ψT hψT u ρ hd h0).1))
    (hx3 : (∀ (d : ℕ) (T : Type) [CommRing T] [Algebra C T] [Algebra 𝒪 T] [IsScalarTower 𝒪 C T]
                (ψT : Onr →ₐ[𝒪] T) (hψT : ψT = (IsScalarTower.toAlgHom 𝒪 C T).comp ψ)
                (h0 : algebraMap C T (algebraMap 𝒪 C π) = 0) (x : SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap C T))) (ξ d ≫ Limits.pullback.snd fM (Spec.map (CommRingCat.ofHom (algebraMap 𝒪 C))))),
                ∃ (u : FakeEllipticCurve.WithFullLevel Λ N n T) (ρ : FakeEllipticCurve.Rigidification r π A₀ ψT u.1) (hd : ρ.d = d),
                  RigidifiedPairClass.ptX 𝒪 π Onr Λ A₀ n C ψ (Limits.pullback.snd fM (Spec.map (CommRingCat.ofHom (algebraMap 𝒪 C)))) X ξ tM xOf d T ψT hψT u ρ hd h0 = x))
    (hx4 : (∀ (d : ℕ) (T : Type) [CommRing T] [Algebra C T] [Algebra 𝒪 T] [IsScalarTower 𝒪 C T]
                (ψT : Onr →ₐ[𝒪] T) (hψT : ψT = (IsScalarTower.toAlgHom 𝒪 C T).comp ψ)
                (h0 : algebraMap C T (algebraMap 𝒪 C π) = 0)
                (u u' : FakeEllipticCurve.WithFullLevel Λ N n T)
                (ρ : FakeEllipticCurve.Rigidification r π A₀ ψT u.1) (ρ' : FakeEllipticCurve.Rigidification r π A₀ ψT u'.1)
                (hd : ρ.d = d) (hd' : ρ'.d = d),
                (RigidifiedPairClass.ptX 𝒪 π Onr Λ A₀ n C ψ (Limits.pullback.snd fM (Spec.map (CommRingCat.ofHom (algebraMap 𝒪 C)))) X ξ tM xOf d T ψT hψT u ρ hd h0 = RigidifiedPairClass.ptX 𝒪 π Onr Λ A₀ n C ψ (Limits.pullback.snd fM (Spec.map (CommRingCat.ofHom (algebraMap 𝒪 C)))) X ξ tM xOf d T ψT hψT u' ρ' hd' h0 ↔
                  ∃ (i : u.1.A ≅ u'.1.A) (hi : i.hom ≫ u'.1.f = u.1.f), FakeEllipticCurve.WithFullLevel.IsoVia u u' i hi ∧
                    ∃ (ib : ρ.Eb.A ⟶ ρ'.Eb.A) (_ : ib ≫ ρ'.gb = ρ.gb ≫ i.hom) (_ : ib ≫ ρ'.Eb.f = ρ.Eb.f)
                      (uA : ρ'.Ab.A ⟶ ρ.Ab.A) (_ : FakeEllipticCurve.IsPullbackVia (RingHom.id _) ρ.Ab ρ'.Ab uA) (_ : uA ≫ ρ.gA = ρ'.gA),
                      ib ≫ ρ'.φ ≫ uA = ρ.φ)))

    (hxM : ∀ (d : ℕ) (T : Type) [CommRing T] [Algebra C T] [Algebra 𝒪 T] [IsScalarTower 𝒪 C T]
        (ψT : Onr →ₐ[𝒪] T) (hψT : ψT = (IsScalarTower.toAlgHom 𝒪 C T).comp ψ)
        (u : FakeEllipticCurve.WithFullLevel Λ N n T) (ρ : FakeEllipticCurve.Rigidification r π A₀ ψT u.1)
        (hd : ρ.d = d) (h0 : algebraMap C T (algebraMap 𝒪 C π) = 0),
        (RigidifiedPairClass.ptX 𝒪 π Onr Λ A₀ n C ψ (Limits.pullback.snd fM (Spec.map (CommRingCat.ofHom (algebraMap 𝒪 C)))) X ξ tM xOf d T ψT hψT u ρ hd h0).1 ≫ ξ d ≫ Limits.pullback.fst fM (Spec.map (CommRingCat.ofHom (algebraMap 𝒪 C))) =
          (ptF T (Spec.map (CommRingCat.ofHom (algebraMap 𝒪 T))) u).1)

    (hmap : RigidifiedPairClass.MapCompat 𝒪 π Onr Λ hΛℤ A₀ n C ψ (Limits.pullback.snd fM (Spec.map (CommRingCat.ofHom (algebraMap 𝒪 C)))) X ξ tM xOf) :
    ∀ (A : Type) [CommRing A] [Algebra C A] (m : ℕ) (f : Fin m → A),
      Ideal.span (Set.range f) = ⊤ →
      ∀ (B : Fin m → Type) [∀ i, CommRing (B i)] [∀ i, Algebra A (B i)] [∀ i, Algebra C (B i)]
        [∀ i, IsScalarTower C A (B i)] [∀ i, IsLocalization.Away (f i) (B i)]
        (s : ∀ i, (RigidifiedPairClass.PR 𝒪 π Onr Λ hΛℤ A₀ n C ψ (Limits.pullback.snd fM (Spec.map (CommRingCat.ofHom (algebraMap 𝒪 C)))) X ξ tM xOf hmap).obj (B i)),
      (∀ (i j : Fin m) (D : Type) [CommRing D] [Algebra A D] [Algebra C D] [IsScalarTower C A D]
          [IsLocalization.Away (f i * f j) D] (ρ₁ : B i →ₐ[A] D) (ρ₂ : B j →ₐ[A] D),
          (RigidifiedPairClass.PR 𝒪 π Onr Λ hΛℤ A₀ n C ψ (Limits.pullback.snd fM (Spec.map (CommRingCat.ofHom (algebraMap 𝒪 C)))) X ξ tM xOf hmap).map (ρ₁.restrictScalars C) (s i) =
          (RigidifiedPairClass.PR 𝒪 π Onr Λ hΛℤ A₀ n C ψ (Limits.pullback.snd fM (Spec.map (CommRingCat.ofHom (algebraMap 𝒪 C)))) X ξ tM xOf hmap).map (ρ₂.restrictScalars C) (s j)) →
      ∃! s₀ : (RigidifiedPairClass.PR 𝒪 π Onr Λ hΛℤ A₀ n C ψ (Limits.pullback.snd fM (Spec.map (CommRingCat.ofHom (algebraMap 𝒪 C)))) X ξ tM xOf hmap).obj A,
        ∀ i, (RigidifiedPairClass.PR 𝒪 π Onr Λ hΛℤ A₀ n C ψ (Limits.pullback.snd fM (Spec.map (CommRingCat.ofHom (algebraMap 𝒪 C)))) X ξ tM xOf hmap).map (IsScalarTower.toAlgHom C A (B i)) s₀ = s i := by
  intro A _ _ nA f hf B _ _ _ _ _ s hov

  have hequiv : ∀ (T : Type) [CommRing T] [Algebra C T], Equivalence (Rel 𝒪 π Onr Λ hΛℤ A₀ n C ψ (Limits.pullback.snd fM (Spec.map (CommRingCat.ofHom (algebraMap 𝒪 C)))) X ξ tM xOf T) :=
    fun T _ _ => CerednikDrinfeld.QM.RigidifiedPairClass.rel_equivalence hrN hrr 𝒪 π hunr Onr hBq Λ hΛ hΛℤ coord hcoord A₀ n hn hrn M fM ptF hM C hC ψ X ξ tM xOf hx2 hx3
      (fun d T _ _ _ _ ψT hψT h0 u u' ρ ρ' hd hd' h => (hx4 d T ψT hψT h0 u u' ρ ρ' hd hd').mp h) T
  have hlocal : ∀ (p q : Pt (algebraMap 𝒪 C π) (Limits.pullback.snd fM (Spec.map (CommRingCat.ofHom (algebraMap 𝒪 C)))) X ξ A),
      (∀ i, Rel 𝒪 π Onr Λ hΛℤ A₀ n C ψ (Limits.pullback.snd fM (Spec.map (CommRingCat.ofHom (algebraMap 𝒪 C)))) X ξ tM xOf (B i) (p.map (IsScalarTower.toAlgHom C A (B i))) (q.map (IsScalarTower.toAlgHom C A (B i)))) →
      Rel 𝒪 π Onr Λ hΛℤ A₀ n C ψ (Limits.pullback.snd fM (Spec.map (CommRingCat.ofHom (algebraMap 𝒪 C)))) X ξ tM xOf A p q :=
    fun p q h => CerednikDrinfeld.QM.RigidifiedPairClass.rel_of_forall_rel_map hrN hrr 𝒪 π hunr Onr hBq Λ hΛ hΛℤ coord hcoord A₀ n hn hrn M fM ptF hM C hC ψ X ξ tM xOf A nA f hf B p q h

  have hmapq : ∀ (T T' : Type) [CommRing T] [Algebra C T] [CommRing T'] [Algebra C T'] (φ : T →ₐ[C] T')
      (p : Pt (algebraMap 𝒪 C π) (Limits.pullback.snd fM (Spec.map (CommRingCat.ofHom (algebraMap 𝒪 C)))) X ξ T),
      (PR 𝒪 π Onr Λ hΛℤ A₀ n C ψ (Limits.pullback.snd fM (Spec.map (CommRingCat.ofHom (algebraMap 𝒪 C)))) X ξ tM xOf hmap).map φ (Quot.mk _ p) = Quot.mk _ (p.map φ) :=
    fun _ _ _ _ _ _ _ _ => rfl
  have hEqv : ∀ (T : Type) [CommRing T] [Algebra C T] (a b : Pt (algebraMap 𝒪 C π) (Limits.pullback.snd fM (Spec.map (CommRingCat.ofHom (algebraMap 𝒪 C)))) X ξ T),
      Relation.EqvGen (Rel 𝒪 π Onr Λ hΛℤ A₀ n C ψ (Limits.pullback.snd fM (Spec.map (CommRingCat.ofHom (algebraMap 𝒪 C)))) X ξ tM xOf T) a b → Rel 𝒪 π Onr Λ hΛℤ A₀ n C ψ (Limits.pullback.snd fM (Spec.map (CommRingCat.ofHom (algebraMap 𝒪 C)))) X ξ tM xOf T a b := by
    intro T _ _ a b h
    induction h with
    | rel x y hxy => exact hxy
    | refl x => exact (hequiv T).refl x
    | symm x y _ ih => exact (hequiv T).symm ih
    | trans x y z _ _ ih₁ ih₂ => exact (hequiv T).trans ih₁ ih₂
  have hrep : ∀ i, ∃ p : Pt (algebraMap 𝒪 C π) (Limits.pullback.snd fM (Spec.map (CommRingCat.ofHom (algebraMap 𝒪 C)))) X ξ (B i), Quot.mk _ p = s i := fun i => Quot.exists_rep (s i)
  choose p hp using hrep
  have hovRel : ∀ (i j : Fin nA) (D : Type) [CommRing D] [Algebra A D] [Algebra C D] [IsScalarTower C A D]
      [IsLocalization.Away (f i * f j) D] (ρ₁ : B i →ₐ[A] D) (ρ₂ : B j →ₐ[A] D),
      Rel 𝒪 π Onr Λ hΛℤ A₀ n C ψ (Limits.pullback.snd fM (Spec.map (CommRingCat.ofHom (algebraMap 𝒪 C)))) X ξ tM xOf D ((p i).map (ρ₁.restrictScalars C)) ((p j).map (ρ₂.restrictScalars C)) := by
    intro i j D _ _ _ _ _ ρ₁ ρ₂
    have h := hov i j D ρ₁ ρ₂
    rw [← hp i, ← hp j] at h
    exact hEqv D _ _ (Quot.eq.mp h)
  have hovt : ∀ (i j : Fin nA) (D : Type) [CommRing D] [Algebra A D] [Algebra C D] [IsScalarTower C A D]
      [IsLocalization.Away (f i * f j) D] (ρ₁ : B i →ₐ[A] D) (ρ₂ : B j →ₐ[A] D),
      Spec.map (CommRingCat.ofHom ρ₁.toRingHom) ≫ (p i).t = Spec.map (CommRingCat.ofHom ρ₂.toRingHom) ≫ (p j).t := by
    intro i j D _ _ _ _ _ ρ₁ ρ₂
    have h := (hovRel i j D ρ₁ ρ₂).1
    exact h
  obtain ⟨t₀, ht₀, -⟩ := Ws16SH.existsUnique_point_of_forall (Limits.pullback.snd fM (Spec.map (CommRingCat.ofHom (algebraMap 𝒪 C)))) A nA f hf B
    (fun i => (⟨(p i).t, (p i).ht⟩ : SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap C (B i)))) (Limits.pullback.snd fM (Spec.map (CommRingCat.ofHom (algebraMap 𝒪 C)))))) hovt
  obtain ⟨e, x₀, hx₀, hcorr⟩ :=
    CerednikDrinfeld.QM.IsFineModuli.exists_strata_point_locally_corr_of_span_eq_top
      hrN hrr 𝒪 π hunr Onr hBq Λ hΛ hΛℤ coord hcoord A₀ n hn hrn M fM ptF hM C hC ψ
      X ξ (RigidifiedPairClass.ptX 𝒪 π Onr Λ A₀ n C ψ (Limits.pullback.snd fM (Spec.map (CommRingCat.ofHom (algebraMap 𝒪 C)))) X ξ tM xOf) hx2 hx3 hx4 hxM
      A nA f hf B (fun i => (p i).t) (fun i => (p i).ht) (fun i => (p i).d) (fun i => (p i).x) (fun i => (p i).hx)
      t₀.1 t₀.2 ht₀ (by
        intro i j D _ _ _ _ _ σ₁ σ₂ τ₁ hτ₁ τ₂ hτ₂
        have e₁ : τ₁ = qmap (algebraMap 𝒪 C π) (σ₁.restrictScalars C) :=
          Ideal.Quotient.ringHom_ext (by rw [qmap_comp_mk]; exact hτ₁)
        have e₂ : τ₂ = qmap (algebraMap 𝒪 C π) (σ₂.restrictScalars C) :=
          Ideal.Quotient.ringHom_ext (by rw [qmap_comp_mk]; exact hτ₂)
        subst e₁ e₂
        exact (hovRel i j D σ₁ σ₂).2)
  let q : Pt (algebraMap 𝒪 C π) (Limits.pullback.snd fM (Spec.map (CommRingCat.ofHom (algebraMap 𝒪 C)))) X ξ A := ⟨t₀.1, t₀.2, e, x₀, hx₀⟩
  have hq : ∀ i, Rel 𝒪 π Onr Λ hΛℤ A₀ n C ψ (Limits.pullback.snd fM (Spec.map (CommRingCat.ofHom (algebraMap 𝒪 C)))) X ξ tM xOf (B i) (q.map (IsScalarTower.toAlgHom C A (B i))) (p i) := by
    intro i
    refine ⟨?_, ?_⟩
    · show Spec.map (CommRingCat.ofHom ((IsScalarTower.toAlgHom C A (B i) : A →ₐ[C] B i) : A →+* B i)) ≫ t₀.1 = (p i).t
      exact ht₀ i
    · exact hcorr i (qmap (algebraMap 𝒪 C π) (IsScalarTower.toAlgHom C A (B i))) (qmap_comp_mk _ _)
  refine ⟨Quot.mk _ q, fun i => ?_, fun z' hz' => ?_⟩
  · rw [hmapq, ← hp i]
    exact Quot.sound (hq i)
  · induction z' using Quot.ind with
    | mk q' =>
      refine Quot.sound (hlocal q' q fun i => ?_)
      have h := hz' i
      rw [hmapq, ← hp i] at h
      exact (hequiv (B i)).trans (hEqv (B i) _ _ (Quot.eq.mp h)) ((hequiv (B i)).symm (hq i))

end S_CerednikDrinfeld_QM_RigidifiedPairClass_PR_existsUnique_map_eq_of_span_eq_top
end P2MW
export P2MW.S_CerednikDrinfeld_QM_RigidifiedPairClass_PR_existsUnique_map_eq_of_span_eq_top (solution)
