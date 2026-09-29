-- Prove2me | solution 1 for CerednikDrinfeld.QM.FakeEllipticCurve.exists_isIsogenyPair_preservesLevel_comp_act_eq_of_schemeNsmul_comp_eq_of_forall_ker
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.141142+00:00
-- url     : https://prove2.me/submissions/c8801d17-686a-51a4-aa47-34002a86bf26

import Definitions.Def_CerednikDrinfeld_QMIsogeny
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawKernel
import Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_existsUnique_schemeNsmul_comp_eq_of_forall_isTorsionPoint
import Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_isFinite_and_flat_schemeNsmul
import Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_surjective_schemeNsmul
import Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_pushPt_act_natCast_eq_nsmulPt
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_exists_isIsogenyPair_preservesLevel_comp_act_eq_of_schemeNsmul_comp_eq_of_forall_ker
p2m_attr_erase "instance" "GoodReductionJacobian.RelativeGroupLaw.isIso_endKerStr_schemeHomOverId AlgebraicGeometry.Scheme.PresheafOfModules.symmetricCategory SheafOfModules.instFaithfulRingSheafPModToPMod SheafOfModules.symmetricCategory AlgebraicGeometry.Scheme.PresheafOfModules.monoidalCategory AlgebraicGeometry.Scheme.PresheafOfModules.monoidalClosed SheafOfModules.instFullRingSheafPModToPMod SheafOfModules.monoidalCategory AlgebraicGeometry.Scheme.Modules.symmetricCategory SheafOfModules.monoidalClosed SheafOfModules.instIsLocalizationPModRingSheafSheafifyFunctorPresheafW SheafOfModules.sheafifyFunctor_monoidal AlgebraicGeometry.Scheme.Modules.monoidalClosed AlgebraicGeometry.instMonoidalPresheafOfModulesModulesSheafify AlgebraicGeometry.Scheme.Modules.monoidalCategory PresheafOfModules.instMonoidalClosed PresheafOfModules.InternalHom.instModuleCarrierObjOppositeCommRingCatSubtypePiFamilyMemAddSubgroupNaturalFamilies PresheafOfModules.InternalHom.instModuleCarrierObjOppositeRingCatCompCommRingCatForget₂RingHomCarrierCarrierAbPresheaf PresheafOfModules.InternalHom.instSMulCarrierObjOppositeCommRingCatSubtypePiFamilyMemAddSubgroupNaturalFamilies AlgebraicGeometry.Scheme.Hom.opensMapFinal AlgebraicGeometry.RelPicard.RigidifiedLineBundle.setoid AlgebraicGeometry.RelPicard.RigidifiedLineBundle.instInhabited AlgebraicGeometry.OModulePresheaf.isScalarTower AlgebraicGeometry.Scheme.OrderedAffineCover.instLinearOrder AlgebraicGeometry.OModulePresheaf.module AlgebraicGeometry.Scheme.OrderedAffineCover.instFintype AlgebraicGeometry.Scheme.OrderedAffineCover.instFintypeIdx AlgebraicGeometry.OModulePresheaf.addCommGroup AlgebraicGeometry.Scheme.OrderedAffineCover.instDecidableEqIdx AlgebraicGeometry.OModulePresheaf.moduleSections TwoChartCech.Sections.M0_moduleA TwoChartCech.Sections.M1_module TwoChartCech.Cover.A01_algebra TwoChartCech.Cover.A0_algebra TwoChartCech.Cover.A1_commRing TwoChartCech.Cover.A1_algebra TwoChartCech.Sections.M01_module TwoChartCech.Sections.M0_addCommGroup TwoChartCech.Sections.M0_tower TwoChartCech.Sections.M01_addCommGroup"
p2m_attr_erase "instance" "TwoChartCech.Cover.A0_commRing TwoChartCech.Sections.M1_tower TwoChartCech.Sections.M01_moduleA TwoChartCech.Sections.M0_module TwoChartCech.Sections.M1_moduleA TwoChartCech.Sections.M1_addCommGroup TwoChartCech.Cover.A01_commRing TwoChartCech.Sections.M01_tower CoherentBaseChange.TwoTermComplex.C0_module CoherentBaseChange.TwoTermComplex.C0_addCommGroup CoherentBaseChange.TwoTermComplex.C1_module CoherentBaseChange.TwoTermComplex.C1_addCommGroup CoherentBaseChange.TwoTermComplex.C0_free CoherentBaseChange.TwoTermComplex.C1_finite CoherentBaseChange.TwoTermComplex.C0_finite CoherentBaseChange.TwoTermComplex.C1_free AlgebraicGeometry.OModulePresheaf.instSubsingletonObjZero AlgebraicGeometry.Scheme.Modules.preservesBinaryProducts_opensMap AlgebraicGeometry.Scheme.Modules.pullback_monoidal AlgebraicGeometry.Scheme.Modules.sheafify_isLocalization' AlgebraicGeometry.Scheme.Modules.preservesTerminal_opensMap AlgebraicGeometry.Scheme.Modules.pullback₀_monoidal AlgebraicGeometry.Scheme.Modules.preservesFiniteProducts_opensMap AlgebraicGeometry.Scheme.Modules.instLiftingPresheafOfModulesSheafifyPresheafWOpensCarrierCarrierCommRingCatGrothendieckTopologyObjFunctorOppositeIsSheafSheafCompPullback₀Pullback PresheafOfModules.PullbackMonoidal.pullback_monoidal PresheafOfModules.PullbackMonoidal.isIso_δ PresheafOfModules.pushforward_laxMonoidal PresheafOfModules.PullbackMonoidal.isIso_η PresheafOfModules.free_monoidal PresheafOfModules.restrictScalars_laxMonoidal PresheafOfModules.PullbackMonoidal.isIso_δ_gS PresheafOfModules.pullback_oplaxMonoidal PresheafOfModules.PullbackMonoidal.instPreservesColimitsOfSizeCompOppositeCommRingCatRingCatForget₂RingHomCarrierCarrierPb PresheafOfModules.pullback_monoidal' AlgebraicGeometry.SmoothOfRelativeDimension.fiberToSpecResidueField AlgebraicGeometry.SmoothOfRelativeDimension.pullback_snd AlgebraicGeometry.SmoothOfRelativeDimension.pullback_fst AlgebraicGeometry.SmoothOfRelativeDimension.smooth_one AlgebraicGeometry.SmoothProperCurve.isIntegral_pullback_Spec_field AlgebraicGeometry.IsProper.fiberToSpecResidueField"
p2m_attr_erase "instance" "AlgebraicCurve.CurveModel.isProper AlgebraicCurve.CurveModel.isIntegral AlgebraicCurve.CurveModel.smooth AlgebraicGeometry.Scheme.LocalRepresentabilityULift.instIsLocallyInjectiveFunUliftYonedaGluedToSheaf AlgebraicGeometry.Scheme.LocalRepresentabilityULift.instIsLocallySurjectiveFunUliftYonedaGluedToSheafOfIsLocallySurjectiveZariskiTopologyDescFunctorOppositeType AlgebraicGeometry.Scheme.LocalRepresentabilityULift.instIsOpenImmersionToGlued AlgebraicGeometry.Scheme.LocalRepresentabilityULift.instIsIsoSheafZariskiTopologyTypeUliftYonedaGluedToSheaf AlgebraicGeometry.RelPicard.instIsOpenImmersionToGlued AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.instFundamentalIdentityOfSumRamificationInertia AlgebraicCurve.Place.instIsScalarTowerResidueFieldRestrictPushforward AlgebraicCurve.Place.instAlgebraResidueFieldRestrictPushforward AlgebraicCurve.Place.instIsLocalHomRestrictInclusion AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions PresheafOfModules.ExteriorPower.instModulePresheafAb AlgebraicGeometry.RelEffCartierDiv.subsingleton_of_degree_zero AlgebraicGeometry.RelEffCartierDiv.isIso_subschemeIota_snd_of_degree_one AlgebraicGeometry.isIso_ker_graphOver_subschemeIota_snd AlgebraicGeometry.isClosedImmersion_graphOver AlgebraicGeometry.FGSubalgebra.instIsDirectedLe AlgebraicGeometry.FGSubalgebra.instQuasiSeparatedSpaceCarrierCarrierCommRingCatObjOppositeSchemeSpecDiagram AlgebraicGeometry.FGSubalgebra.instIsCofilteredOpposite AlgebraicGeometry.FGSubalgebra.instIsAffineObjOppositeSchemeSpecDiagram AlgebraicGeometry.FGSubalgebra.instNonempty AlgebraicGeometry.FGSubalgebra.instNonemptySubtypeLeSubalgebraValFG AlgebraicGeometry.FGSubalgebra.instCompactSpaceCarrierCarrierCommRingCatObjOppositeSchemeSpecDiagram AlgebraicGeometry.FGSubalgebra.instIsDirectedSubtypeLeSubalgebraValFG AlgebraicGeometry.FGSubalgebra.instIsAffineHomMapOppositeSchemeSpecDiagram AlgebraicGeometry.FGSubalgebra.instIsFiltered AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instNeg AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instSMulInt AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instAddCommGroup AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instAdd AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instSub"
p2m_attr_erase "instance" "AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instModuleCarrierObjOppositeOpensCarrierCarrierCommRingCatPresheafOpOpensTop AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instSMulCarrierObjOppositeOpensCarrierCarrierCommRingCatPresheafOpOpensTop AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instSMulNat AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instZero AlgebraicCurve.instHasLocalResidue_of_hasCanonicalLocalResidueK AlgebraicCurve.instHasCanonicalLocalResidueK_of_hasCanonicalLocalResidueKStar AlgebraicCurve.Place.kw_ffgc_finiteDimensional_adicCompletion instAlgebraSubtypeMemValuationSubring_definitions AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersIntegersCompletion ModularCurve.KwF4gRRTate.instAlgebraKAdicCompletionIntegers AlgebraicCurve.Place.kw_ffgc_continuousSMul_adicCompletionComap AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersCompletionCompletion IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions AlgebraicCurve.instHasCanonicalLocalResidueK AlgebraicCurve.Place.instAlgebra_restrictResidueField AlgebraicCurve.Place.instIsScalarTower_restrictResidueField AlgebraicCurve.instHasLocalResidue AlgebraicCurve.HasSeparableResidue.of_perfectField_of_isCurveOver AlgebraicCurve.HasSeparableResidue.of_perfectField AlgebraicCurve.Place.instIsLocalHom_restrictSubringHom AlgebraicCurve.instHasCanonicalLocalResidueKStar ModularCurve.KwNo6Pin.isLocalRing_completion SheafOfModules.isIso_ihomModelToIhom AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instDecidableEqIdx AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instFintype AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instLinearOrder AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instFintypeIdx AlgebraicGeometry.OModulePresheaf.Leray.relAltC_scalarTower AlgebraicGeometry.OModulePresheaf.Leray.ker_relAltd_modΓ AlgebraicGeometry.OModulePresheaf.Leray.relAltC_modΓ AlgebraicGeometry.OModulePresheaf.Leray.biC_abGrp AlgebraicGeometry.OModulePresheaf.Leray.relAltH_modΓ AlgebraicGeometry.OModulePresheaf.Leray.ker_relAltd_smul AlgebraicGeometry.OModulePresheaf.Leray.relAltH_scalarTower AlgebraicGeometry.OModulePresheaf.Leray.relAltH_smul"
p2m_attr_erase "instance" "AlgebraicGeometry.OModulePresheaf.Leray.biC_module DoubleComplex.instModuleE₂I DoubleComplex.Bounded.modR DoubleComplex.instModuleE₂II DoubleComplex.instAddCommGroupE₂II DoubleComplex.Bounded.abGrp DoubleComplex.instAddCommGroupE₂I AlgebraicGeometry.ChowDatum.hι_closed AlgebraicGeometry.ChowDatumProj.hιN_closed AlgebraicGeometry.ChowDatumProj.hp_proper AlgebraicGeometry.ChowDatum.hp_isoU AlgebraicGeometry.ChowDatum.hp_proper AlgebraicGeometry.ProjSpace.algebraAway AlgebraicGeometry.ProjSpace.instIsProperProdOverπ AlgebraicGeometry.ChowDatumProj.hp_isoU AlgebraicGeometry.ProjSpace.isProper_π AlgebraicGeometry.ProjSpace.finiteType_mvPolynomial ProjSpaceCech.GradedModule.H.module ProjSpaceCech.GradedModule.H.addCommGroup ProjSpaceCech.GradedModule.sec.instAdd ProjSpaceCech.GradedModule.sec.instNeg ProjSpaceCech.GradedModule.acg ProjSpaceCech.GradedModule.Frac.setoid ProjSpaceCech.GradedModule.modR ProjSpaceCech.GradedModule.sec.instModule ProjSpaceCech.GradedModule.sec.instAddCommGroup ProjSpaceCech.GradedModule.sec.instZero ProjSpaceCech.GradedModule.Presentation.fJ ProjSpaceCech.GradedModule.sec.instSMul ProjSpaceCech.Twist.H.module ProjSpaceCech.Idx.instFintype ProjSpaceCech.Twist.H.addCommGroup ProjSpaceCech.Idx.instDecidableEq ProjSpaceCech.Twist.Mon.instDecidableEq ProjSpaceCech.Twist.cochain.instAddCommGroup ProjSpaceCech.Twist.cochain.instModule AlgebraicGeometry.FGSubalgebra.tensorStage_directedSystem AlgebraicGeometry.RelEffCartierDiv.isClosedImmersion_subschemeι_resProdMap AlgebraicGeometry.RelEffCartierDiv.isOpenImmersion_resProdMap AlgebraicCurve.CurveModel.locallyOfFiniteType_gluedToBase"
p2m_attr_erase "instance" "AlgebraicCurve.CurveModel.isFractionRing_overlap AlgebraicCurve.CurveModel.isLocallyNoetherian_glued AlgebraicCurve.CurveModel.jacobsonSpace_glued AlgebraicCurve.CurveModel.isOpenImmersion_ι₀ AlgebraicCurve.CurveModel.isIntegral_glued AlgebraicCurve.CurveModel.quasiSeparated_gluedToBase AlgebraicCurve.CurveModel.compactSpace_glued AlgebraicCurve.CurveModel.isIntegral_adjoin_chartRing AlgebraicCurve.CurveModel.isFractionRing_overlap_functionField AlgebraicCurve.CurveModel.isProper_gluedToBase AlgebraicCurve.CurveModel.isOpenImmersion_ιU AlgebraicCurve.CurveModel.isOpenImmersion_f₀ AlgebraicCurve.CurveModel.isOpenImmersion_fInf AlgebraicCurve.CurveModel.isOpenImmersion_ιInf AlgebraicCurve.CurveModel.algebra_overlap_functionField AlgebraicCurve.CurveModel.quasiCompact_gluedToBase AlgebraicCurve.CurveModel.algebraAdjoin AlgebraicCurve.CurveModel.isDedekindDomain_chartRing AlgebraicCurve.CurveModel.isIntegralClosure AlgebraicCurve.CurveModel.finite_chartRing AlgebraicCurve.CurveModel.centre_isPrime AlgebraicCurve.CurveModel.isFractionRing_chartRing AlgebraicCurve.CurveModel.finiteType_chartRing AlgebraicCurve.CurveModel.isNoetherianRing_chartRing AlgebraicCurve.CurveModel.isScalarTower_base_adjoin AlgebraicCurve.CurveModel.isScalarTower_adjoin AlgebraicCurve.CurveModel.chartRing_finitePresentation instTopologicallyFGOfFiniteType AlgebraicGeometry.ProjSpace.twistObj.addCommGroup AlgebraicGeometry.ProjSpace.twistFam.module AlgebraicGeometry.ProjSpace.twistObj.module AlgebraicGeometry.ProjSpace.twistObj.moduleSections AlgebraicGeometry.ProjSpace.twistFam.addCommGroup kmfloorsGlue_int_three_isPrime kmfloorsGlue_int_bot_isPrime"
p2m_attr_erase "simp" "GoodReductionJacobian.RelativeGroupLaw.fibre_inv GoodReductionJacobian.RelativeGroupLaw.fibrePointToBase_coe GoodReductionJacobian.RelativeGroupLaw.fibrePointOfBase_toBase GoodReductionJacobian.RelativeGroupLaw.fibre_mul GoodReductionJacobian.RelativeGroupLaw.fibrePointToBase_ofBase GoodReductionJacobian.RelativeGroupLaw.fibre_one GoodReductionJacobian.RelativeGroupLaw.fibrePointOfBase_coe AlgebraicGeometry.schemeFibreEndo_snd AlgebraicGeometry.schemeFibreEndo_fst GoodReductionJacobian.RelativeGroupLaw.baseChangePointToBase_ofBase GoodReductionJacobian.RelativeGroupLaw.baseChangePointToBase_coe GoodReductionJacobian.RelativeGroupLaw.baseChangePointOfBase_coe GoodReductionJacobian.RelativeGroupLaw.baseChange_inv GoodReductionJacobian.RelativeGroupLaw.baseChangePointOfBase_toBase GoodReductionJacobian.RelativeGroupLaw.baseChange_mul GoodReductionJacobian.RelativeGroupLaw.baseChange_one NeronModelInfra.NeronModelPropertyBundle.endExtensionEquiv_symm_restrict NeronModelInfra.schemeHomOverComp_id_left NeronModelInfra.schemeHomOverComp_id_right NeronModelInfra.schemeHomOverId_coe NeronModelInfra.NeronModelPropertyBundle.endExtensionEquiv_apply NeronModelInfra.NeronModelPropertyBundle.restrict_endExtensionEquiv_symm NeronModelInfra.schemeHomOverComp_coe NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_fst NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_snd NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_fst NeronSpecialFibreInfra.neronEndRestrictEquiv_apply NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_fst_assoc NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_snd NeronSpecialFibreInfra.neronEndExtension_genericFibreRestrict NeronSpecialFibreInfra.specClosedFibreInclusion_eq NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_fst_assoc NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_snd_assoc NeronSpecialFibreInfra.genericFibreRestrict_neronEndExtension NeronSpecialFibreInfra.homOverId_coe NeronSpecialFibreInfra.homOverComp_coe NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_snd_assoc NeronModelInfra.schemeHomOverNpow_succ NeronModelInfra.schemeHomOverNpow_zero GoodReductionJacobian.relativeGroupLawOfGrpObj_inv"
p2m_attr_erase "simp" "GoodReductionJacobian.relativeGroupLawOfGrpObj_mul GoodReductionJacobian.overHomEquivSchemeHomOver_apply_coe GoodReductionJacobian.relativeGroupLawOfGrpObj_one GoodReductionJacobian.overHomEquivSchemeHomOver_symm_apply_left SheafOfModules.tensorUnit_eq AlgebraicGeometry.Scheme.Modules.tensorUnit_eq PresheafOfModules.InternalHom.presheaf_map_apply PresheafOfModules.InternalHom.curryFamily_app PresheafOfModules.InternalHom.add_app PresheafOfModules.InternalHom.smul_app PresheafOfModules.InternalHom.zero_app PresheafOfModules.ihomObj_map_val PresheafOfModules.ihomFunctor_map PresheafOfModules.InternalHom.restrict_app PresheafOfModules.InternalHom.postcomp_app PresheafOfModules.InternalHom.neg_app PresheafOfModules.curry'_app_val PresheafOfModules.InternalHom.presheaf_obj PresheafOfModules.ihomFunctor_obj PresheafOfModules.ihomObj_obj PresheafOfModules.InternalHom.sub_app PresheafOfModules.ihomMap_app_val AlgebraicGeometry.Scheme.Modules.tensorPow_zero AlgebraicGeometry.Scheme.Modules.tensorPow_succ AlgebraicGeometry.RelPicard.RigidifiedLineBundle.mk.sizeOf_spec AlgebraicGeometry.RelPicard.RigidifiedLineBundle.mk.injEq AlgebraicGeometry.Scheme.OrderedAffineCover.mk.injEq AlgebraicGeometry.OModulePresheaf.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCover.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.mk.injEq AlgebraicGeometry.Scheme.TwoAffineOpenCover.mk.injEq AlgebraicGeometry.Scheme.TwoAffineOpenCover.mk.sizeOf_spec AlgebraicGeometry.Scheme.TwoAffineOpenCover.pullback_U1 AlgebraicGeometry.Scheme.TwoAffineOpenCover.pullback_U0 TwoChartCech.Sections.mk.injEq TwoChartCech.Cover.mk.injEq TwoChartCech.GrothendieckComplex.mk.injEq TwoChartCech.Sections.mk.sizeOf_spec TwoChartCech.Cover.mk.sizeOf_spec TwoChartCech.Cover.lineBundle_r0_apply"
p2m_attr_erase "simp" "TwoChartCech.GrothendieckComplex.mk.sizeOf_spec TwoChartCech.Cover.lineBundle_r1_apply CoherentBaseChange.TwoTermComplex.mk.sizeOf_spec CoherentBaseChange.TwoTermComplex.mk.injEq AlgebraicGeometry.OModulePresheaf.prod_obj AlgebraicGeometry.OModulePresheaf.restrOpen_obj AlgebraicGeometry.OModulePresheaf.DevissageStep.mk.injEq AlgebraicGeometry.OModulePresheaf.pushforward_obj AlgebraicGeometry.OModulePresheaf.im_obj AlgebraicGeometry.OModulePresheaf.pow_obj AlgebraicGeometry.OModulePresheaf.fstHom_app AlgebraicGeometry.OModulePresheaf.ker_obj AlgebraicGeometry.OModulePresheaf.coker_obj AlgebraicGeometry.OModulePresheaf.DevissageStep.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCover.preimage_U AlgebraicGeometry.OModulePresheaf.sndHom_app AlgebraicGeometry.OModulePresheaf.Hom.mk.injEq AlgebraicGeometry.OModulePresheaf.Hom.id_app AlgebraicGeometry.OModulePresheaf.AffHom.appSections_apply AlgebraicGeometry.OModulePresheaf.AffHom.comp_app AlgebraicGeometry.OModulePresheaf.AffSES.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.AffHom.kerMap_coe AlgebraicGeometry.OModulePresheaf.AffHom.id_app AlgebraicGeometry.OModulePresheaf.Hom.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.Hom.toAffHom_app AlgebraicGeometry.OModulePresheaf.SES.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.AffHom.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.Hom.comp_app AlgebraicGeometry.OModulePresheaf.SES.mk.injEq AlgebraicGeometry.OModulePresheaf.AffHom.mk.injEq AlgebraicGeometry.OModulePresheaf.Hom.appSections_apply AlgebraicGeometry.OModulePresheaf.AffSES.mk.injEq PresheafOfModules.freeεIso_hom_app PresheafOfModules.freeμIso_hom_app AlgebraicGeometry.RelPicard.RepresentsRelSubPic.mk.injEq AlgebraicGeometry.RelPicard.SubPicCondition.mk.injEq AlgebraicGeometry.RelPicard.SubPicCondition.mk.sizeOf_spec AlgebraicGeometry.RelPicard.RepresentsRelSubPic.mk.sizeOf_spec AlgebraicGeometry.SmoothProperCurve.sectionBaseChange_coe_snd AlgebraicGeometry.SmoothProperCurve.sectionBaseChange_coe_fst"
p2m_attr_erase "simp" "AlgebraicCurve.CurveModel.mk.injEq AlgebraicCurve.CurveModel.mk.sizeOf_spec AlgebraicCurve.mulAdele_apply AlgebraicCurve.residuePairing_apply_coe AlgebraicCurve.mem_adeleBdd AlgebraicCurve.weilSmul_one AlgebraicCurve.diagonalHom_apply AlgebraicCurve.weilSmul_apply AlgebraicCurve.adeleSpaceMul_coe AlgebraicCurve.mulAdele_one AlgebraicGeometry.SmoothProperCurve.FiniteMapData.twoAffineOpenCover_U1 AlgebraicGeometry.SmoothProperCurve.FiniteMapData.mk.injEq AlgebraicGeometry.SmoothProperCurve.FiniteMapData.mk.sizeOf_spec AlgebraicGeometry.SmoothProperCurve.FiniteMapData.twoAffineOpenCover_U0 AlgebraicGeometry.RelPicard.SubPicCondition.onClasses_mk AlgebraicGeometry.RelPicard.relSubPicPresheaf_map_coe CategoryTheory.Functor.OverTotal.ofFibre_fst CategoryTheory.Functor.overTotal_map_fst AlgebraicGeometry.Scheme.LocalRepresentabilityULift.glueData_J AlgebraicGeometry.Scheme.LocalRepresentabilityULift.uliftYoneda_toGlued_uliftYonedaGluedToSheaf AlgebraicGeometry.Scheme.LocalRepresentabilityULift.glueData_t' AlgebraicGeometry.Scheme.LocalRepresentabilityULift.uliftYoneda_toGlued_uliftYonedaGluedToSheaf_assoc AlgebraicGeometry.Scheme.LocalRepresentabilityULift.uliftYonedaGluedToSheaf_app_toGlued AlgebraicGeometry.Scheme.LocalRepresentabilityULift.glueData_openCover_map AlgebraicGeometry.Scheme.LocalRepresentabilityULift.uliftYonedaGluedToSheaf_app_comp AlgebraicGeometry.Scheme.LocalRepresentabilityULift.glueData_V AlgebraicGeometry.Scheme.LocalRepresentabilityULift.glueData_t AlgebraicGeometry.Scheme.LocalRepresentabilityULift.glueData_U AlgebraicGeometry.Scheme.LocalRepresentabilityULift.glueData_f AlgebraicGeometry.RelPicard.designationOfRepresentableBy_P AlgebraicGeometry.RelPicard.designationOfRepresentableBy_toBase AlgebraicGeometry.RelPicard.rigSection_snd AlgebraicGeometry.RelPicard.RigidifiedLineBundle.ofInvertible_L AlgebraicGeometry.RelPicard.rigSection_snd_assoc AlgebraicGeometry.RelPicard.SubPicGroupCondition.mk.injEq AlgebraicGeometry.RelPicard.SubPicGroupCondition.mk.sizeOf_spec AlgebraicCurve.coe_cechH0Equiv_apply AlgebraicCurve.cechH1ToH1_mk AlgebraicCurve.lSpaceOn_univ AlgebraicCurve.lSpaceOn_empty"
p2m_attr_erase "simp" "AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.Divisor.mapRestrict_single AlgebraicCurve.Divisor.pushforward_single AlgebraicCurve.Place.coe_restrictInclusion AlgebraicCurve.Place.mem_fiber AlgebraicCurve.Place.restrict_toValuationSubring AlgebraicCurve.Divisor.degree_pushforward AlgebraicCurve.Place.restrictResidueMap_residue AlgebraicCurve.Pic0.coe_pushforwardDegZeroHom AlgebraicCurve.Pic0.coe_pullbackDegZeroHom AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Divisor.degree_pushforwardAlong AlgebraicCurve.Pic0.coe_degZeroCorrespondence AlgebraicCurve.Place.mem_fiberAlong AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero"
p2m_attr_erase "simp" "ModularCurve.jqNModC_one ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one AlgebraicCurve.Place.differentialCoeff_zero AlgebraicCurve.Place.differentialCoeff_dCoord AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.injEq AlgebraicCurve.TranscendenceTower.mk.injEq AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec AlgebraicCurve.PoleDivisorPackage.mk.injEq AlgebraicGeometry.RelPicard.thetaBundle_def AlgebraicGeometry.RelPicard.picardBundle_def AlgebraicGeometry.RelEffCartierDiv.toRelEffDivisor_ofRelEffDivisor AlgebraicGeometry.RelEffCartierDiv.toRelEffDivisor_I AlgebraicGeometry.mapOnProdOver_fst_assoc AlgebraicGeometry.RelEffCartierDiv.mk.sizeOf_spec AlgebraicGeometry.RelEffCartierDiv.mk.injEq AlgebraicGeometry.mapOnProdOver_snd AlgebraicGeometry.mapOnProdOver_fst AlgebraicGeometry.mapOnProdOver_snd_assoc AlgebraicGeometry.mapOnProdOver_id AlgebraicCurve.RelEffDivisor.mk.sizeOf_spec AlgebraicCurve.mapOnProd_fst AlgebraicCurve.mapOnProd_fst_assoc AlgebraicCurve.mapOnProd_snd AlgebraicCurve.UnivDivisorPack.mk.injEq AlgebraicCurve.RelEffDivisor.mk.injEq"
p2m_attr_erase "simp" "AlgebraicCurve.UnivDivisorPack.mk.sizeOf_spec AlgebraicCurve.mapOnProd_snd_assoc AlgebraicGeometry.Scheme.Modules.exteriorPower_obj PresheafOfModules.exteriorPower_map_ιMulti PresheafOfModules.ExteriorPower.appₗ_apply AlgebraicGeometry.prodKerGraph_one AlgebraicGeometry.fibrePowOver.proj_comp AlgebraicGeometry.prodKerGraph_zero AlgebraicGeometry.RelEffCartierDiv.empty_I AlgebraicGeometry.fibrePowOver.proj_comp_assoc AlgebraicGeometry.graphOver_fst_assoc AlgebraicGeometry.RelEffCartierDiv.toPoint_comp AlgebraicGeometry.RelEffCartierDiv.toPoint_comp_assoc AlgebraicGeometry.graphOver_fst AlgebraicGeometry.RelEffCartierDiv.ofPoint_I AlgebraicGeometry.graphOver_snd AlgebraicGeometry.graphOver_snd_assoc AlgebraicCurve.SymmetricPowerPackage.mk.sizeOf_spec AlgebraicCurve.SymmetricPowerPackage.mk.injEq AlgebraicGeometry.FGSubalgebra.cocone_ι_app_apply AlgebraicGeometry.RelPicard.fst_toProdSpec AlgebraicGeometry.RelPicard.toProdSpec_fst_assoc AlgebraicGeometry.RelPicard.pointsSubBasepointModule_cons AlgebraicGeometry.RelPicard.pointsSubBasepointModule_nil AlgebraicGeometry.RelPicard.fst_toProdSpec_assoc AlgebraicGeometry.RelPicard.toProdSpec_fst AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.sub_app AlgebraicGeometry.Scheme.IdealSheafData.sres_sresTop AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.add_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.mk.sizeOf_spec AlgebraicGeometry.Scheme.IdealSheafData.coe_resLE AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.smul_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.coe_ofLE_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.ideal_range AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.zero_app AlgebraicGeometry.Scheme.IdealSheafData.sres_sres AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.comp_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.neg_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.id_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.coe_mulRight_app"
p2m_attr_erase "simp" "AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.nsmul_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.mk.injEq AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.zsmul_app AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.sizeOf_spec AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.injEq AlgebraicCurve.adeleSingle_coe AlgebraicCurve.kaehlerResidueTermKFam_apply AlgebraicCurve.Place.LocalResidueData.mk.injEq AlgebraicCurve.Place.LocalResidueData.mk.sizeOf_spec AlgebraicCurve.Place.kw_ffgc_adicCompletionComapIntegers_coe AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.sizeOf_spec AlgebraicCurve.Place.mem_simplePoleSubmodule AlgebraicCurve.Place.coe_uniformizerSubring ModularCurve.Lg37.Lg37CompletionSection.mk.injEq AlgebraicCurve.Place.CoefficientFieldSection.mk.injEq AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.injEq ModularCurve.Lg37.Lg37CompletionSection.mk.sizeOf_spec AlgebraicCurve.Place.CoefficientFieldSection.mk.sizeOf_spec AlgebraicCurve.Place.poleSubmodule_one AlgebraicCurve.Place.mem_poleSubmodule AlgebraicGeometry.Scheme.Modules.toUnitSection_ofUnitSection AlgebraicGeometry.Scheme.Modules.pullbackSection_def AlgebraicGeometry.Scheme.Modules.ofUnitSection_toUnitSection PresheafOfModules.InternalHom.IsSheafAux.appAt_toPresheafHom SheafOfModules.ihomSectionsEquivFamily_unit AlgebraicGeometry.Scheme.Modules.restrictHomEquivFamily_apply SheafOfModules.ihomEval_unit_app AlgebraicGeometry.Scheme.Modules.ihomEval_zero_right AlgebraicGeometry.Scheme.Modules.ihomEval_zero_left AlgebraicGeometry.Scheme.Modules.homOfFamily_app_apply SheafOfModules.unit_ihomSectionsEquivFamily AlgebraicGeometry.Scheme.Modules.familyOfHom_app AlgebraicGeometry.Scheme.Modules.restrictUnitIso_hom_app_apply AlgebraicGeometry.Scheme.Modules.restrictUnitIso_inv_app_apply AlgebraicGeometry.Scheme.Modules.restrictHomOfFamily_app_apply AlgebraicGeometry.Scheme.Modules.restrictHomEquivFamily_symm_apply AlgebraicGeometry.Scheme.Modules.tensorSections_zero_right AlgebraicGeometry.Scheme.Modules.map_unitSection AlgebraicGeometry.Scheme.Modules.tensorSectionsBilin_apply AlgebraicGeometry.Scheme.Modules.tensorPowSection_zero"
p2m_attr_erase "simp" "AlgebraicGeometry.Scheme.Modules.tensorSections_zero_left AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_neg AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_zero AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_sub AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_add AlgebraicGeometry.Scheme.OrderedAffineCover.toCoverOf_U AlgebraicGeometry.Scheme.OrderedAffineCoverOf.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCoverOf.mk.injEq AlgebraicGeometry.Scheme.OrderedAffineCover.restrict_U AlgebraicGeometry.OModulePresheaf.Leray.restrictToPreimage_U DoubleComplex.Bounded.mk.injEq DoubleComplex.Bounded.mk.sizeOf_spec DoubleComplex.Convergence.mk.injEq DoubleComplex.Convergence.mk.sizeOf_spec DoubleComplex.SubQuot.mk.sizeOf_spec DoubleComplex.SubQuot.mk.injEq AlgebraicGeometry.ChowDatumProj.mk.sizeOf_spec AlgebraicGeometry.ChowDatum.mk.sizeOf_spec AlgebraicGeometry.ChowDatumProj.mk.injEq AlgebraicGeometry.ChowDatum.mk.injEq ProjSpaceCech.GradedModule.mk.injEq ProjSpaceCech.GradedModule.mk.sizeOf_spec ProjSpaceCech.GradedModule.Frac.mk.sizeOf_spec ProjSpaceCech.GradedModule.Presentation.mk.injEq ProjSpaceCech.GradedModule.Frac.mk.injEq ProjSpaceCech.GradedModule.Presentation.mk.sizeOf_spec ProjSpaceCech.GradedModule.Hom.shift_toLinearMap ProjSpaceCech.GradedModule.Hom.mk.sizeOf_spec ProjSpaceCech.GradedModule.Hom.mk.injEq TwoChartCech.Mumford.dK_apply TwoChartCech.Mumford.ι0_apply TwoChartCech.Mumford.ι1_apply TwoChartCech.KerCoprod.dK_apply TwoChartCech.KerCoprod.ι1_apply TwoChartCech.KerCoprod.ι0_apply AlgebraicGeometry.tilde.functorCompPullbackSpecIso_app AlgebraicGeometry.RelPicard.algEquivZeroGroupCut_toSubPicCondition AlgebraicGeometry.RelPicard.LFP.stageHom_val AlgebraicGeometry.RelPicard.BaseChange.relSubPicPresheafRestrictIso_hom_app_coe AlgebraicGeometry.RelPicard.BaseChange.relSubPicPresheafRestrictIso_inv_app_coe"
p2m_attr_erase "simp" "AlgebraicGeometry.RelPicard.BaseChange.restrict_P AlgebraicGeometry.RelEffCartierDiv.IsUniversal.lift_comp AlgebraicGeometry.RelEffCartierDiv.functor_map_fst AlgebraicGeometry.RelEffCartierDiv.IsUniversal.homEquiv_apply AlgebraicGeometry.RelEffCartierDiv.IsUniversal.lift_pullbackAlong AlgebraicGeometry.RelEffCartierDiv.IsUniversal.homEquiv_symm_apply AlgebraicGeometry.RelEffCartierDiv.IsUniversal.lift_comp_assoc AlgebraicGeometry.RelEffCartierDiv.supportedIn_top AlgebraicGeometry.RelEffCartierDiv.mem_supportedIn_iff AlgebraicGeometry.RelEffCartierDiv.supportedIn_top_eq AlgebraicGeometry.RelEffCartierDiv.restrictAlong_extendAlong AlgebraicGeometry.RelEffCartierDiv.extendAlong_I AlgebraicGeometry.RelEffCartierDiv.resProdMap_snd AlgebraicGeometry.RelEffCartierDiv.restrictAlong_I AlgebraicGeometry.RelEffCartierDiv.extendAlong_restrictAlong AlgebraicGeometry.RelEffCartierDiv.resProdMap_fst_assoc AlgebraicGeometry.RelEffCartierDiv.resProdMap_snd_assoc AlgebraicGeometry.RelEffCartierDiv.resProdMap_fst CoherentBaseChange.FibreH0Family.mk.sizeOf_spec CoherentBaseChange.FibreH0Family.mk.injEq AlgebraicGeometry.Scheme.Modules.ProjPresentation.mk.injEq AlgebraicGeometry.Scheme.Modules.ProjPresentation.mk.sizeOf_spec AlgebraicCurve.CurveModel.coe_gInf AlgebraicCurve.CurveModel.coe_tInvChart AlgebraicCurve.CurveModel.ιInf_gluedToBase_assoc AlgebraicCurve.CurveModel.ιInf_gluedToBase AlgebraicCurve.CurveModel.primeOfι₀_asIdeal AlgebraicCurve.CurveModel.coe_tChart AlgebraicCurve.CurveModel.ι₀_gluedToBase_assoc AlgebraicCurve.CurveModel.primeOfιInf_asIdeal AlgebraicCurve.CurveModel.ι₀_gluedToBase AlgebraicCurve.CurveModel.coe_tma AlgebraicCurve.CurveModel.coe_primeEquivChartPlaces RegularLocalRingQuotientAscent.dualNumberFst_apply AlgebraicGeometry.ProjSpace.twistObj.mk.injEq AlgebraicGeometry.ProjSpace.twistObj.zero_val AlgebraicGeometry.ProjSpace.twistObj.add_val AlgebraicGeometry.ProjSpace.twist_res_val AlgebraicGeometry.ProjSpace.twist_smul_val AlgebraicGeometry.ProjSpace.twistGradeToObj_val"
p2m_attr_erase "simp" "AlgebraicGeometry.ProjSpace.twistObj.smul_val AlgebraicGeometry.ProjSpace.twistGradeEquiv_apply_val AlgebraicGeometry.ProjSpace.twistObj.mk.sizeOf_spec"

set_option autoImplicit false

p2m_open "CategoryTheory AlgebraicGeometry NeronModelInfra~schemeHomOverComp GoodReductionJacobian CerednikDrinfeld CerednikDrinfeld.QM"
open scoped Quaternion

namespace DualS25

variable {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} {N : ℕ} {S : Type} [CommRing S]

section law
variable {A : Scheme.{0}} {f : A ⟶ Spec (CommRingCat.of S)} (L : RelativeGroupLaw S f)

theorem nsmulPt_eq_nsmul {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of S)) (n : ℕ) (P : SchemeHomOver t f) :
    nsmulPt L t n P = L.nsmul t n P := by
  induction n with
  | zero => rfl
  | succ n ih => rw [RelativeGroupLaw.nsmul_succ, ← ih]; rfl

theorem nsmul_coe {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of S)) (n : ℕ) (P : SchemeHomOver t f) :
    (L.nsmul t n P).1 = P.1 ≫ L.schemeNsmul n := by
  have hP : schemeHomOverComp P.1 P.2 (RelativeGroupLaw.idPoint (f := f)) = P := Subtype.ext (Category.comp_id _)
  have := L.nsmul_natural f t P.1 P.2 n RelativeGroupLaw.idPoint
  rw [hP] at this
  rw [← this]
  rfl

theorem one_coe {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of S)) :
    (L.one t).1 = t ≫ (L.one (𝟙 _)).1 := by
  have := L.one_natural (𝟙 _) t t (Category.comp_id t)
  rw [← this]
  rfl

theorem nsmul_mul (hc : L.IsCommutative) {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of S)) (n : ℕ)
    (P Q : SchemeHomOver t f) : L.nsmul t n (L.mul t P Q) = L.mul t (L.nsmul t n P) (L.nsmul t n Q) := by
  letI : CommGroup (SchemeHomOver t f) := { L.pointGroup t with mul_comm := fun x y => hc t x y }
  have hpow : ∀ (m : ℕ) (R : SchemeHomOver t f), L.nsmul t m R = R ^ m := by
    intro m R
    induction m with
    | zero => rfl
    | succ m ih => rw [RelativeGroupLaw.nsmul_succ, ih, pow_succ]; rfl
  rw [hpow, hpow, hpow]
  exact mul_pow P Q n

theorem nsmul_mul_nsmul {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of S)) (m n : ℕ) (P : SchemeHomOver t f) :
    L.nsmul t n (L.nsmul t m P) = L.nsmul t (m * n) P := by
  letI := L.pointGroup t
  have hpow : ∀ (m : ℕ) (R : SchemeHomOver t f), L.nsmul t m R = R ^ m := by
    intro m R
    induction m with
    | zero => rfl
    | succ m ih => rw [RelativeGroupLaw.nsmul_succ, ih, pow_succ]; rfl
  rw [hpow, hpow, hpow, ← pow_mul]

theorem nsmul_add {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of S)) (m n : ℕ) (P : SchemeHomOver t f) :
    L.nsmul t (m + n) P = L.mul t (L.nsmul t m P) (L.nsmul t n P) := by
  letI := L.pointGroup t
  have hpow : ∀ (m : ℕ) (R : SchemeHomOver t f), L.nsmul t m R = R ^ m := by
    intro m R
    induction m with
    | zero => rfl
    | succ m ih => rw [RelativeGroupLaw.nsmul_succ, ih, pow_succ]; rfl
  rw [hpow, hpow, hpow, pow_add]
  rfl

theorem schemeNsmul_mul (m n : ℕ) : L.schemeNsmul (m * n) = L.schemeNsmul m ≫ L.schemeNsmul n := by
  show (L.nsmul f (m * n) RelativeGroupLaw.idPoint).1 = _
  rw [← nsmul_mul_nsmul, nsmul_coe]
  rfl

theorem schemeNsmul_hom (hc : L.IsCommutative) (n : ℕ) {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of S))
    (P Q : SchemeHomOver t f) :
    (L.mul t P Q).1 ≫ L.schemeNsmul n =
      (L.mul t ⟨P.1 ≫ L.schemeNsmul n, by rw [Category.assoc, L.schemeNsmul_over]; exact P.2⟩
        ⟨Q.1 ≫ L.schemeNsmul n, by rw [Category.assoc, L.schemeNsmul_over]; exact Q.2⟩).1 := by
  rw [← nsmul_coe, nsmul_mul L hc]
  congr 1
  congr 1 <;> exact Subtype.ext (nsmul_coe L t n _)

end law

section hom
variable (E A : FakeEllipticCurve Λ N S)

def IsHomS (w : E.A ⟶ A.A) (hw : w ≫ A.f = E.f) : Prop :=
  ∀ (T : Scheme.{0}) (t : T ⟶ Spec (CommRingCat.of S)) (P Q : SchemeHomOver t E.f),
    (E.L.mul t P Q).1 ≫ w =
      (A.L.mul t ⟨P.1 ≫ w, by rw [Category.assoc, hw]; exact P.2⟩ ⟨Q.1 ≫ w, by rw [Category.assoc, hw]; exact Q.2⟩).1

variable {E A}

theorem IsHomS.mapPt_mul {w : E.A ⟶ A.A} {hw : w ≫ A.f = E.f} (h : IsHomS E A w hw)
    {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of S)) (P Q : SchemeHomOver t E.f) :
    mapPt w hw (E.L.mul t P Q) = A.L.mul t (mapPt w hw P) (mapPt w hw Q) :=
  Subtype.ext (h T t P Q)

theorem IsHomS.of_mapPt {w : E.A ⟶ A.A} {hw : w ≫ A.f = E.f}
    (h : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of S)) (P Q : SchemeHomOver t E.f),
      mapPt w hw (E.L.mul t P Q) = A.L.mul t (mapPt w hw P) (mapPt w hw Q)) : IsHomS E A w hw :=
  fun _ t P Q => congrArg Subtype.val (h t P Q)

theorem IsHomS.mapPt_one {w : E.A ⟶ A.A} {hw : w ≫ A.f = E.f} (h : IsHomS E A w hw)
    {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of S)) : mapPt w hw (E.L.one t) = A.L.one t := by
  set x := mapPt w hw (E.L.one t) with hx
  have hxx : A.L.mul t x x = x := by rw [hx, ← h.mapPt_mul, E.L.one_mul]
  letI := A.L.pointGroup t
  have h2 : x * x = x * 1 := by rw [mul_one]; exact hxx
  exact mul_left_cancel h2

theorem IsHomS.one_comp {w : E.A ⟶ A.A} {hw : w ≫ A.f = E.f} (h : IsHomS E A w hw)
    {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of S)) : (E.L.one t).1 ≫ w = (A.L.one t).1 :=
  congrArg Subtype.val (h.mapPt_one t)

theorem IsHomS.mapPt_nsmul {w : E.A ⟶ A.A} {hw : w ≫ A.f = E.f} (h : IsHomS E A w hw)
    {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of S)) (n : ℕ) (P : SchemeHomOver t E.f) :
    mapPt w hw (E.L.nsmul t n P) = A.L.nsmul t n (mapPt w hw P) := by
  induction n with
  | zero => exact h.mapPt_one t
  | succ n ih => rw [RelativeGroupLaw.nsmul_succ, RelativeGroupLaw.nsmul_succ, h.mapPt_mul, ih]

theorem IsHomS.schemeNsmul_comm {w : E.A ⟶ A.A} {hw : w ≫ A.f = E.f} (h : IsHomS E A w hw) (n : ℕ) :
    E.L.schemeNsmul n ≫ w = w ≫ A.L.schemeNsmul n := by
  have h0 := congrArg Subtype.val (h.mapPt_nsmul E.f n RelativeGroupLaw.idPoint)
  have h1 : (E.L.nsmul E.f n RelativeGroupLaw.idPoint).1 ≫ w = (A.L.nsmul E.f n (mapPt w hw RelativeGroupLaw.idPoint)).1 := h0
  rw [nsmul_coe, nsmul_coe] at h1
  have h2 : (𝟙 E.A ≫ E.L.schemeNsmul n) ≫ w = (𝟙 E.A ≫ w) ≫ A.L.schemeNsmul n := h1
  simpa [Category.id_comp] using h2

theorem IsHomS.comp {E A C : FakeEllipticCurve Λ N S} {w : E.A ⟶ A.A} {hw : w ≫ A.f = E.f}
    {v : A.A ⟶ C.A} {hv : v ≫ C.f = A.f} (h : IsHomS E A w hw) (h' : IsHomS A C v hv) :
    IsHomS E C (w ≫ v) (by rw [Category.assoc, hv, hw]) := by
  intro T t P Q
  rw [← Category.assoc, h T t P Q, h' T t]
  rfl

theorem IsHomS.schemeNsmul (E : FakeEllipticCurve Λ N S) (n : ℕ) :
    IsHomS E E (E.L.schemeNsmul n) (E.L.schemeNsmul_over n) :=
  fun _ t P Q => schemeNsmul_hom E.L E.comm n t P Q

end hom

theorem act_natCast_eq_schemeNsmul (E : FakeEllipticCurve Λ N S) (h1 : (1 : ℍ[ℚ, a, b]) ∈ Λ) (n : ℕ)
    (hn : ((n : ℚ) : ℍ[ℚ, a, b]) ∈ Λ) :
    E.act ⟨((n : ℚ) : ℍ[ℚ, a, b]), hn⟩ = E.L.schemeNsmul n := by
  have := congrArg Subtype.val
    (CerednikDrinfeld.QM.FakeEllipticCurve.pushPt_act_natCast_eq_nsmulPt E h1 n hn E.f (RelativeGroupLaw.idPoint (f := E.f)))
  rw [nsmulPt_eq_nsmul] at this
  have h2 : (RelativeGroupLaw.idPoint (f := E.f)).1 ≫ E.act ⟨((n : ℚ) : ℍ[ℚ, a, b]), hn⟩ = E.L.schemeNsmul n := this
  simpa [Category.id_comp] using h2

theorem act_intCast_eq_schemeNsmul (E : FakeEllipticCurve Λ N S) (hΛℤ : ∀ m : ℤ, ((m : ℚ) : ℍ[ℚ, a, b]) ∈ Λ) (n : ℕ) :
    E.act ⟨(((n : ℕ) : ℤ) : ℚ), hΛℤ _⟩ = E.L.schemeNsmul n := by
  have h1 : (1 : ℍ[ℚ, a, b]) ∈ Λ := by simpa using hΛℤ 1
  have hn : ((n : ℚ) : ℍ[ℚ, a, b]) ∈ Λ := by have := hΛℤ n; rwa [Int.cast_natCast] at this
  have : (⟨(((n : ℕ) : ℤ) : ℚ), hΛℤ _⟩ : ↥Λ) = ⟨((n : ℚ) : ℍ[ℚ, a, b]), hn⟩ := Subtype.ext (by push_cast; rfl)
  rw [this]
  exact act_natCast_eq_schemeNsmul E h1 n hn

section divide
variable [IsNoetherianRing S]

theorem divide (E : FakeEllipticCurve Λ N S) (n : ℕ) (hn : 0 < n)
    {A' : Scheme.{0}} (f' : A' ⟶ Spec (CommRingCat.of S)) (L' : RelativeGroupLaw S f')
    (F : E.A ⟶ A') (hF : F ≫ f' = E.f)
    (hFhom : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of S)) (P Q : SchemeHomOver t E.f),
      (E.L.mul t P Q).1 ≫ F =
        (L'.mul t ⟨P.1 ≫ F, by rw [Category.assoc, hF]; exact P.2⟩
          ⟨Q.1 ≫ F, by rw [Category.assoc, hF]; exact Q.2⟩).1)
    (hFker : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of S)) (P : SchemeHomOver t E.f),
      E.L.nsmul t n P = E.L.one t → P.1 ≫ F = (L'.one t).1) :
    ∃ w : E.A ⟶ A', (E.L.schemeNsmul n ≫ w = F) ∧
      (∀ w' : E.A ⟶ A', E.L.schemeNsmul n ≫ w' = F → w' = w) ∧
      ∃ hw : w ≫ f' = E.f,
        ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of S)) (P Q : SchemeHomOver t E.f),
          (E.L.mul t P Q).1 ≫ w =
            (L'.mul t ⟨P.1 ≫ w, by rw [Category.assoc, hw]; exact P.2⟩
              ⟨Q.1 ≫ w, by rw [Category.assoc, hw]; exact Q.2⟩).1 := by
  obtain ⟨hfin, hflat⟩ :=
    GoodReductionJacobian.RelativeGroupLaw.isFinite_and_flat_schemeNsmul E.L E.bundle (fun t x y => E.comm t x y) n hn
  haveI := hfin
  haveI := hflat
  haveI : Surjective (E.L.schemeNsmul n) :=
    GoodReductionJacobian.RelativeGroupLaw.surjective_schemeNsmul E.L E.comm E.bundle n hn
  exact GoodReductionJacobian.RelativeGroupLaw.existsUnique_schemeNsmul_comp_eq_of_forall_isTorsionPoint S E.f E.L E.comm n
    f' L' F hF hFhom (fun t P hP => hFker t P hP)

theorem cancel (E A : FakeEllipticCurve Λ N S) (n : ℕ) (hn : 0 < n)
    (w₁ w₂ : E.A ⟶ A.A) (hw₁ : w₁ ≫ A.f = E.f) (hom₁ : IsHomS E A w₁ hw₁)
    (h : E.L.schemeNsmul n ≫ w₁ = E.L.schemeNsmul n ≫ w₂) : w₁ = w₂ := by
  have hF := (IsHomS.schemeNsmul E n).comp hom₁
  obtain ⟨w, -, huniq, -⟩ := divide E n hn A.f A.L (E.L.schemeNsmul n ≫ w₁)
    (by rw [Category.assoc, hw₁, E.L.schemeNsmul_over]) (fun t P Q => hF _ t P Q)
    (by
      intro T t P hP
      rw [← Category.assoc, ← nsmul_coe, hP, hom₁.one_comp])
  exact (huniq w₁ rfl).trans (huniq w₂ h.symm).symm

end divide

theorem natCast_mem (hΛℤ : ∀ m : ℤ, ((m : ℚ) : ℍ[ℚ, a, b]) ∈ Λ) (n : ℕ) : ((n : ℚ) : ℍ[ℚ, a, b]) ∈ Λ := by
  have := hΛℤ n; rwa [Int.cast_natCast] at this

end DualS25

open DualS25 in
theorem solution
    {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} {N : ℕ} (hΛℤ : ∀ m : ℤ, ((m : ℚ) : ℍ[ℚ, a, b]) ∈ Λ)
    {r : ℕ} [Fact r.Prime] (hrN : ¬ r ∣ N)
    {S : Type} [CommRing S] [IsNoetherianRing S]
    (E A : FakeEllipticCurve Λ N S)

    (φ : E.A ⟶ A.A) (hφ : φ ≫ A.f = E.f) (φ' : A.A ⟶ E.A) (d : ℕ)
    (hpair : FakeEllipticCurve.IsIsogenyPair (r ^ d) E A φ φ')
    (hφlev : FakeEllipticCurve.PreservesLevel E A φ hφ)

    (k : ℕ) (hkd : k ≤ d) (ψ' : A.A ⟶ E.A)
    (hfac : A.L.schemeNsmul (r ^ k) ≫ ψ' = φ')
    (hψ'f : ψ' ≫ E.f = A.f)
    (hψ'hom : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of S)) (P Q : SchemeHomOver t A.f),
      (A.L.mul t P Q).1 ≫ ψ' =
        (E.L.mul t ⟨P.1 ≫ ψ', by rw [Category.assoc, hψ'f]; exact P.2⟩
          ⟨Q.1 ≫ ψ', by rw [Category.assoc, hψ'f]; exact Q.2⟩).1)

    (h : ℕ)
    (hker : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of S)) (P : SchemeHomOver t A.f),
      P.1 ≫ ψ' = (E.L.one t).1 → nsmulPt A.L t (r ^ h) P = A.L.one t) :
    ∃ (γ : E.A ⟶ A.A) (hγ : γ ≫ A.f = E.f),
      FakeEllipticCurve.IsIsogenyPair (r ^ h) E A γ ψ' ∧
      FakeEllipticCurve.PreservesLevel E A γ hγ ∧
      γ ≫ A.act ⟨(((r ^ (d - k) : ℕ) : ℤ) : ℚ), hΛℤ _⟩ = φ ≫ A.act ⟨(((r ^ h : ℕ) : ℤ) : ℚ), hΛℤ _⟩ := by
  classical
  have hr : 0 < r := (Fact.out : r.Prime).pos
  have hrpos : ∀ n : ℕ, 0 < r ^ n := fun n => pow_pos hr n
  have h1Λ : (1 : ℍ[ℚ, a, b]) ∈ Λ := by simpa using hΛℤ 1
  obtain ⟨hφo, hφ'o, hmulφ, hmulφ', hlinφ, hlinφ', hcompφ⟩ := hpair
  obtain ⟨hc1, hc2⟩ := hcompφ (natCast_mem hΛℤ (r ^ d))

  rw [act_natCast_eq_schemeNsmul E h1Λ] at hc1
  rw [act_natCast_eq_schemeNsmul A h1Λ] at hc2
  have homφ : IsHomS E A φ hφ := IsHomS.of_mapPt (fun t P Q => hmulφ t P Q)
  have homφ' : IsHomS A E φ' hφ'o := IsHomS.of_mapPt (fun t P Q => hmulφ' t P Q)
  have homψ' : IsHomS A E ψ' hψ'f := fun _ t P Q => hψ'hom t P Q

  set m := d - k with hm
  have hdk : d = k + m := by omega

  have hA1 : φ ≫ ψ' = E.L.schemeNsmul (r ^ m) := by
    apply cancel E E (r ^ k) (hrpos k) _ _ (by rw [Category.assoc, hψ'f, hφ]) (homφ.comp homψ')
    rw [← Category.assoc, homφ.schemeNsmul_comm, Category.assoc, hfac, hc1, ← schemeNsmul_mul, ← pow_add, ← hdk]
  have hA2 : ψ' ≫ φ = A.L.schemeNsmul (r ^ m) := by
    apply cancel A A (r ^ k) (hrpos k) _ _ (by rw [Category.assoc, hφ, hψ'f]) (homψ'.comp homφ)
    rw [← Category.assoc, hfac, hc2, ← schemeNsmul_mul, ← pow_add, ← hdk]

  have hFf : (φ ≫ A.L.schemeNsmul (r ^ h)) ≫ A.f = E.f := by rw [Category.assoc, A.L.schemeNsmul_over, hφ]
  have hFhom : IsHomS E A (φ ≫ A.L.schemeNsmul (r ^ h)) hFf := homφ.comp (IsHomS.schemeNsmul A (r ^ h))
  obtain ⟨γ, hγdef, hγuniq, hγf, hγhom⟩ := divide E (r ^ m) (hrpos m) A.f A.L (φ ≫ A.L.schemeNsmul (r ^ h)) hFf
    (fun t P Q => hFhom _ t P Q)
    (by
      intro T t P hP

      let Q : SchemeHomOver t A.f := mapPt φ hφ P
      have hQ : Q.1 ≫ ψ' = (E.L.one t).1 := by
        show (P.1 ≫ φ) ≫ ψ' = _
        rw [Category.assoc, hA1, ← nsmul_coe, hP]
      have := congrArg Subtype.val (hker t Q hQ)
      rw [nsmulPt_eq_nsmul, nsmul_coe] at this
      rw [← Category.assoc]
      exact this)
  have homγ : IsHomS E A γ hγf := fun _ t P Q => hγhom t P Q

  have hC : ψ' ≫ γ = A.L.schemeNsmul (r ^ h) := by
    apply cancel A A (r ^ m) (hrpos m) _ _ (by rw [Category.assoc, hγf, hψ'f]) (homψ'.comp homγ)
    rw [← Category.assoc, homψ'.schemeNsmul_comm, Category.assoc, hγdef, ← Category.assoc, hA2]

  have hD : γ ≫ ψ' = E.L.schemeNsmul (r ^ h) := by
    apply cancel E E (r ^ m) (hrpos m) _ _ (by rw [Category.assoc, hψ'f, hγf]) (homγ.comp homψ')
    rw [← Category.assoc, hγdef, Category.assoc, homψ'.schemeNsmul_comm, ← Category.assoc, hA1]

  have hlinγ : ∀ x : ↥Λ, E.act x ≫ γ = γ ≫ A.act x := by
    intro x
    have homEx : IsHomS E E (E.act x) (E.act_over x) := IsHomS.of_mapPt (fun t P Q => E.act_hom x t P Q)
    have homAx : IsHomS A A (A.act x) (A.act_over x) := IsHomS.of_mapPt (fun t P Q => A.act_hom x t P Q)
    apply cancel E A (r ^ m) (hrpos m) _ _ (by rw [Category.assoc, hγf, E.act_over]) (homEx.comp homγ)
    rw [← Category.assoc, homEx.schemeNsmul_comm, Category.assoc, hγdef, ← Category.assoc, hlinφ x, Category.assoc,
      ← homAx.schemeNsmul_comm, ← Category.assoc, ← hγdef, Category.assoc]
  have hlinψ' : ∀ x : ↥Λ, A.act x ≫ ψ' = ψ' ≫ E.act x := by
    intro x
    have homEx : IsHomS E E (E.act x) (E.act_over x) := IsHomS.of_mapPt (fun t P Q => E.act_hom x t P Q)
    have homAx : IsHomS A A (A.act x) (A.act_over x) := IsHomS.of_mapPt (fun t P Q => A.act_hom x t P Q)
    apply cancel A E (r ^ k) (hrpos k) _ _ (by rw [Category.assoc, hψ'f, A.act_over]) (homAx.comp homψ')
    rw [← Category.assoc, homAx.schemeNsmul_comm, Category.assoc, hfac, hlinφ' x, ← Category.assoc, hfac]
  refine ⟨γ, hγf, ⟨hγf, hψ'f, fun t P Q => homγ.mapPt_mul t P Q, fun t P Q => homψ'.mapPt_mul t P Q, hlinγ, hlinψ',
    fun hd' => ?_⟩, ?_, ?_⟩
  ·
    have hact_E : E.act ⟨((r ^ h : ℕ) : ℚ), hd'⟩ = E.L.schemeNsmul (r ^ h) := act_natCast_eq_schemeNsmul E h1Λ _ hd'
    have hact_A : A.act ⟨((r ^ h : ℕ) : ℚ), hd'⟩ = A.L.schemeNsmul (r ^ h) := act_natCast_eq_schemeNsmul A h1Λ _ hd'
    exact ⟨hD.trans hact_E.symm, hC.trans hact_A.symm⟩
  ·
    intro T t P hP

    have hN0 : N ≠ 0 := by rintro rfl; exact hrN (dvd_zero r)
    have hcop : Nat.Coprime (r ^ m) N :=
      Nat.Coprime.pow_left m (((Fact.out : r.Prime).coprime_iff_not_dvd).mpr hrN)
    obtain ⟨u, c, huc⟩ : ∃ u c : ℕ, u * r ^ m = N * c + 1 := by
      rcases Nat.lt_or_ge 1 N with hN1 | hN1
      · obtain ⟨u, -, hu⟩ := Nat.exists_mul_mod_eq_one_of_coprime hcop hN1
        refine ⟨u, r ^ m * u / N, ?_⟩
        have := Nat.div_add_mod (r ^ m * u) N
        rw [hu] at this
        rw [mul_comm]
        exact this.symm
      · have hN1' : N = 1 := by omega
        subst hN1'
        exact ⟨1, r ^ m - 1, by have := hrpos m; omega⟩

    have levE : ∀ (n : ℕ) (R : SchemeHomOver t E.f), FactorsThrough E.lev R → FactorsThrough E.lev (E.L.nsmul t n R) := by
      intro n R hR
      induction n with
      | zero => exact E.lev_one t
      | succ n ih => rw [RelativeGroupLaw.nsmul_succ]; exact (E.lev_sub t _ _ ih hR).1
    have levA : ∀ (n : ℕ) (R : SchemeHomOver t A.f), FactorsThrough A.lev R → FactorsThrough A.lev (A.L.nsmul t n R) := by
      intro n R hR
      induction n with
      | zero => exact A.lev_one t
      | succ n ih => rw [RelativeGroupLaw.nsmul_succ]; exact (A.lev_sub t _ _ ih hR).1

    obtain ⟨Q', hQ'⟩ : ∃ Q' : SchemeHomOver t E.f, Q' = E.L.nsmul t u P := ⟨_, rfl⟩
    have hQ'lev : FactorsThrough E.lev Q' := hQ' ▸ levE u P hP
    have hPN : E.L.nsmul t N P = E.L.one t := by rw [← nsmulPt_eq_nsmul]; exact E.lev_torsion t P hP
    have hPQ' : E.L.nsmul t (r ^ m) Q' = P := by
      rw [hQ', nsmul_mul_nsmul, huc, DualS25.nsmul_add, ← nsmul_mul_nsmul, hPN,
        RelativeGroupLaw.nsmul_unit, RelativeGroupLaw.nsmul_one_apply, E.L.one_mul]
    obtain ⟨R₀, hR₀⟩ := levA (r ^ h) (mapPt φ hφ Q') (hφlev t Q' hQ'lev)
    have e1 : (A.L.nsmul t (r ^ h) (mapPt φ hφ Q')).1 = (Q'.1 ≫ φ) ≫ A.L.schemeNsmul (r ^ h) :=
      nsmul_coe A.L t (r ^ h) _
    have e2 : P.1 = Q'.1 ≫ E.L.schemeNsmul (r ^ m) := by rw [← hPQ']; exact nsmul_coe E.L t (r ^ m) Q'
    refine ⟨R₀, ?_⟩
    rw [hR₀, e1]
    show _ = P.1 ≫ γ
    rw [e2]
    simp only [Category.assoc]
    rw [hγdef]
  ·
    rw [act_intCast_eq_schemeNsmul A hΛℤ (r ^ (d - k)), act_intCast_eq_schemeNsmul A hΛℤ (r ^ h), ← hm, ← hA2,
      ← Category.assoc, hD, homφ.schemeNsmul_comm]

end S_CerednikDrinfeld_QM_FakeEllipticCurve_exists_isIsogenyPair_preservesLevel_comp_act_eq_of_schemeNsmul_comp_eq_of_forall_ker
end P2MW
export P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_exists_isIsogenyPair_preservesLevel_comp_act_eq_of_schemeNsmul_comp_eq_of_forall_ker (solution)
