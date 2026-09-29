-- Prove2me | solution 1 for CerednikDrinfeld.QM.FakeEllipticCurve.existsUnique_iso_lift_of_isFormalModuleVia_of_one_mem
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.837917+00:00
-- url     : https://prove2.me/submissions/56c0dcee-1447-58f1-a055-d4c6af4e0bb1

import Definitions.Def_CerednikDrinfeld_QMFormalModuleOf
import Theorems.Thm_MvFormalGroup_nilEval_X_of_mem
import Theorems.Thm_MvFormalGroup_nilEval_subst_of_mem
import Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_existsUnique_lev_lift
import Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_existsUnique_hom_lift_of_isFormalModuleVia_of_one_mem
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_existsUnique_iso_lift_of_isFormalModuleVia_of_one_mem
p2m_attr_erase "instance" "MvFormalGroup.Points.instNeg MvFormalGroup.Points.instZero MvFormalGroup.Points.instAdd MvFormalGroup.Points.instAddCommGroup MvFormalGroup.Points.instAddGroup instTopologicallyFGOfFiniteType GoodReductionJacobian.RelativeGroupLaw.isIso_endKerStr_schemeHomOverId AlgebraicGeometry.Scheme.PresheafOfModules.symmetricCategory SheafOfModules.instFaithfulRingSheafPModToPMod SheafOfModules.symmetricCategory AlgebraicGeometry.Scheme.PresheafOfModules.monoidalCategory AlgebraicGeometry.Scheme.PresheafOfModules.monoidalClosed SheafOfModules.instFullRingSheafPModToPMod SheafOfModules.monoidalCategory AlgebraicGeometry.Scheme.Modules.symmetricCategory SheafOfModules.monoidalClosed SheafOfModules.instIsLocalizationPModRingSheafSheafifyFunctorPresheafW SheafOfModules.sheafifyFunctor_monoidal AlgebraicGeometry.Scheme.Modules.monoidalClosed AlgebraicGeometry.instMonoidalPresheafOfModulesModulesSheafify AlgebraicGeometry.Scheme.Modules.monoidalCategory PresheafOfModules.instMonoidalClosed PresheafOfModules.InternalHom.instModuleCarrierObjOppositeCommRingCatSubtypePiFamilyMemAddSubgroupNaturalFamilies PresheafOfModules.InternalHom.instModuleCarrierObjOppositeRingCatCompCommRingCatForget₂RingHomCarrierCarrierAbPresheaf PresheafOfModules.InternalHom.instSMulCarrierObjOppositeCommRingCatSubtypePiFamilyMemAddSubgroupNaturalFamilies AlgebraicGeometry.Scheme.Hom.opensMapFinal AlgebraicGeometry.RelPicard.RigidifiedLineBundle.setoid AlgebraicGeometry.RelPicard.RigidifiedLineBundle.instInhabited AlgebraicGeometry.OModulePresheaf.isScalarTower AlgebraicGeometry.Scheme.OrderedAffineCover.instLinearOrder AlgebraicGeometry.OModulePresheaf.module AlgebraicGeometry.Scheme.OrderedAffineCover.instFintype AlgebraicGeometry.Scheme.OrderedAffineCover.instFintypeIdx AlgebraicGeometry.OModulePresheaf.addCommGroup AlgebraicGeometry.Scheme.OrderedAffineCover.instDecidableEqIdx AlgebraicGeometry.OModulePresheaf.moduleSections TwoChartCech.Sections.M0_moduleA TwoChartCech.Sections.M1_module TwoChartCech.Cover.A01_algebra TwoChartCech.Cover.A0_algebra"
p2m_attr_erase "instance" "TwoChartCech.Cover.A1_commRing TwoChartCech.Cover.A1_algebra TwoChartCech.Sections.M01_module TwoChartCech.Sections.M0_addCommGroup TwoChartCech.Sections.M0_tower TwoChartCech.Sections.M01_addCommGroup TwoChartCech.Cover.A0_commRing TwoChartCech.Sections.M1_tower TwoChartCech.Sections.M01_moduleA TwoChartCech.Sections.M0_module TwoChartCech.Sections.M1_moduleA TwoChartCech.Sections.M1_addCommGroup TwoChartCech.Cover.A01_commRing TwoChartCech.Sections.M01_tower CoherentBaseChange.TwoTermComplex.C0_module CoherentBaseChange.TwoTermComplex.C0_addCommGroup CoherentBaseChange.TwoTermComplex.C1_module CoherentBaseChange.TwoTermComplex.C1_addCommGroup CoherentBaseChange.TwoTermComplex.C0_free CoherentBaseChange.TwoTermComplex.C1_finite CoherentBaseChange.TwoTermComplex.C0_finite CoherentBaseChange.TwoTermComplex.C1_free AlgebraicGeometry.OModulePresheaf.instSubsingletonObjZero AlgebraicGeometry.Scheme.Modules.preservesBinaryProducts_opensMap AlgebraicGeometry.Scheme.Modules.pullback_monoidal AlgebraicGeometry.Scheme.Modules.sheafify_isLocalization' AlgebraicGeometry.Scheme.Modules.preservesTerminal_opensMap AlgebraicGeometry.Scheme.Modules.pullback₀_monoidal AlgebraicGeometry.Scheme.Modules.preservesFiniteProducts_opensMap AlgebraicGeometry.Scheme.Modules.instLiftingPresheafOfModulesSheafifyPresheafWOpensCarrierCarrierCommRingCatGrothendieckTopologyObjFunctorOppositeIsSheafSheafCompPullback₀Pullback PresheafOfModules.PullbackMonoidal.pullback_monoidal PresheafOfModules.PullbackMonoidal.isIso_δ PresheafOfModules.pushforward_laxMonoidal PresheafOfModules.PullbackMonoidal.isIso_η PresheafOfModules.free_monoidal PresheafOfModules.restrictScalars_laxMonoidal PresheafOfModules.PullbackMonoidal.isIso_δ_gS PresheafOfModules.pullback_oplaxMonoidal PresheafOfModules.PullbackMonoidal.instPreservesColimitsOfSizeCompOppositeCommRingCatRingCatForget₂RingHomCarrierCarrierPb PresheafOfModules.pullback_monoidal'"
p2m_attr_erase "instance" "AlgebraicGeometry.SmoothOfRelativeDimension.fiberToSpecResidueField AlgebraicGeometry.SmoothOfRelativeDimension.pullback_snd AlgebraicGeometry.SmoothOfRelativeDimension.pullback_fst AlgebraicGeometry.SmoothOfRelativeDimension.smooth_one AlgebraicGeometry.SmoothProperCurve.isIntegral_pullback_Spec_field AlgebraicGeometry.IsProper.fiberToSpecResidueField AlgebraicCurve.CurveModel.isProper AlgebraicCurve.CurveModel.isIntegral AlgebraicCurve.CurveModel.smooth AlgebraicGeometry.Scheme.LocalRepresentabilityULift.instIsLocallyInjectiveFunUliftYonedaGluedToSheaf AlgebraicGeometry.Scheme.LocalRepresentabilityULift.instIsLocallySurjectiveFunUliftYonedaGluedToSheafOfIsLocallySurjectiveZariskiTopologyDescFunctorOppositeType AlgebraicGeometry.Scheme.LocalRepresentabilityULift.instIsOpenImmersionToGlued AlgebraicGeometry.Scheme.LocalRepresentabilityULift.instIsIsoSheafZariskiTopologyTypeUliftYonedaGluedToSheaf AlgebraicGeometry.RelPicard.instIsOpenImmersionToGlued AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.instFundamentalIdentityOfSumRamificationInertia AlgebraicCurve.Place.instIsScalarTowerResidueFieldRestrictPushforward AlgebraicCurve.Place.instAlgebraResidueFieldRestrictPushforward AlgebraicCurve.Place.instIsLocalHomRestrictInclusion AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions PresheafOfModules.ExteriorPower.instModulePresheafAb AlgebraicGeometry.RelEffCartierDiv.subsingleton_of_degree_zero AlgebraicGeometry.RelEffCartierDiv.isIso_subschemeIota_snd_of_degree_one AlgebraicGeometry.isIso_ker_graphOver_subschemeIota_snd AlgebraicGeometry.isClosedImmersion_graphOver AlgebraicGeometry.FGSubalgebra.instIsDirectedLe AlgebraicGeometry.FGSubalgebra.instQuasiSeparatedSpaceCarrierCarrierCommRingCatObjOppositeSchemeSpecDiagram AlgebraicGeometry.FGSubalgebra.instIsCofilteredOpposite AlgebraicGeometry.FGSubalgebra.instIsAffineObjOppositeSchemeSpecDiagram AlgebraicGeometry.FGSubalgebra.instNonempty AlgebraicGeometry.FGSubalgebra.instNonemptySubtypeLeSubalgebraValFG AlgebraicGeometry.FGSubalgebra.instCompactSpaceCarrierCarrierCommRingCatObjOppositeSchemeSpecDiagram AlgebraicGeometry.FGSubalgebra.instIsDirectedSubtypeLeSubalgebraValFG AlgebraicGeometry.FGSubalgebra.instIsAffineHomMapOppositeSchemeSpecDiagram"
p2m_attr_erase "instance" "AlgebraicGeometry.FGSubalgebra.instIsFiltered AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instNeg AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instSMulInt AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instAddCommGroup AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instAdd AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instSub AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instModuleCarrierObjOppositeOpensCarrierCarrierCommRingCatPresheafOpOpensTop AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instSMulCarrierObjOppositeOpensCarrierCarrierCommRingCatPresheafOpOpensTop AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instSMulNat AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instZero AlgebraicCurve.instHasLocalResidue_of_hasCanonicalLocalResidueK AlgebraicCurve.instHasCanonicalLocalResidueK_of_hasCanonicalLocalResidueKStar AlgebraicCurve.Place.kw_ffgc_finiteDimensional_adicCompletion instAlgebraSubtypeMemValuationSubring_definitions AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersIntegersCompletion ModularCurve.KwF4gRRTate.instAlgebraKAdicCompletionIntegers AlgebraicCurve.Place.kw_ffgc_continuousSMul_adicCompletionComap AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersCompletionCompletion IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions AlgebraicCurve.instHasCanonicalLocalResidueK AlgebraicCurve.Place.instAlgebra_restrictResidueField AlgebraicCurve.Place.instIsScalarTower_restrictResidueField AlgebraicCurve.instHasLocalResidue AlgebraicCurve.HasSeparableResidue.of_perfectField_of_isCurveOver AlgebraicCurve.HasSeparableResidue.of_perfectField AlgebraicCurve.Place.instIsLocalHom_restrictSubringHom AlgebraicCurve.instHasCanonicalLocalResidueKStar ModularCurve.KwNo6Pin.isLocalRing_completion SheafOfModules.isIso_ihomModelToIhom AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instDecidableEqIdx AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instFintype AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instLinearOrder AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instFintypeIdx AlgebraicGeometry.OModulePresheaf.Leray.relAltC_scalarTower AlgebraicGeometry.OModulePresheaf.Leray.ker_relAltd_modΓ"
p2m_attr_erase "instance" "AlgebraicGeometry.OModulePresheaf.Leray.relAltC_modΓ AlgebraicGeometry.OModulePresheaf.Leray.biC_abGrp AlgebraicGeometry.OModulePresheaf.Leray.relAltH_modΓ AlgebraicGeometry.OModulePresheaf.Leray.ker_relAltd_smul AlgebraicGeometry.OModulePresheaf.Leray.relAltH_scalarTower AlgebraicGeometry.OModulePresheaf.Leray.relAltH_smul AlgebraicGeometry.OModulePresheaf.Leray.biC_module DoubleComplex.instModuleE₂I DoubleComplex.Bounded.modR DoubleComplex.instModuleE₂II DoubleComplex.instAddCommGroupE₂II DoubleComplex.Bounded.abGrp DoubleComplex.instAddCommGroupE₂I AlgebraicGeometry.ChowDatum.hι_closed AlgebraicGeometry.ChowDatumProj.hιN_closed AlgebraicGeometry.ChowDatumProj.hp_proper AlgebraicGeometry.ChowDatum.hp_isoU AlgebraicGeometry.ChowDatum.hp_proper AlgebraicGeometry.ProjSpace.algebraAway AlgebraicGeometry.ProjSpace.instIsProperProdOverπ AlgebraicGeometry.ChowDatumProj.hp_isoU AlgebraicGeometry.ProjSpace.isProper_π AlgebraicGeometry.ProjSpace.finiteType_mvPolynomial ProjSpaceCech.GradedModule.H.module ProjSpaceCech.GradedModule.H.addCommGroup ProjSpaceCech.GradedModule.sec.instAdd ProjSpaceCech.GradedModule.sec.instNeg ProjSpaceCech.GradedModule.acg ProjSpaceCech.GradedModule.Frac.setoid ProjSpaceCech.GradedModule.modR ProjSpaceCech.GradedModule.sec.instModule ProjSpaceCech.GradedModule.sec.instAddCommGroup ProjSpaceCech.GradedModule.sec.instZero ProjSpaceCech.GradedModule.Presentation.fJ ProjSpaceCech.GradedModule.sec.instSMul ProjSpaceCech.Twist.H.module ProjSpaceCech.Idx.instFintype ProjSpaceCech.Twist.H.addCommGroup ProjSpaceCech.Idx.instDecidableEq ProjSpaceCech.Twist.Mon.instDecidableEq"
p2m_attr_erase "instance" "ProjSpaceCech.Twist.cochain.instAddCommGroup ProjSpaceCech.Twist.cochain.instModule AlgebraicGeometry.FGSubalgebra.tensorStage_directedSystem AlgebraicGeometry.RelEffCartierDiv.isClosedImmersion_subschemeι_resProdMap AlgebraicGeometry.RelEffCartierDiv.isOpenImmersion_resProdMap AlgebraicCurve.CurveModel.locallyOfFiniteType_gluedToBase AlgebraicCurve.CurveModel.isFractionRing_overlap AlgebraicCurve.CurveModel.isLocallyNoetherian_glued AlgebraicCurve.CurveModel.jacobsonSpace_glued AlgebraicCurve.CurveModel.isOpenImmersion_ι₀ AlgebraicCurve.CurveModel.isIntegral_glued AlgebraicCurve.CurveModel.quasiSeparated_gluedToBase AlgebraicCurve.CurveModel.compactSpace_glued AlgebraicCurve.CurveModel.isIntegral_adjoin_chartRing AlgebraicCurve.CurveModel.isFractionRing_overlap_functionField AlgebraicCurve.CurveModel.isProper_gluedToBase AlgebraicCurve.CurveModel.isOpenImmersion_ιU AlgebraicCurve.CurveModel.isOpenImmersion_f₀ AlgebraicCurve.CurveModel.isOpenImmersion_fInf AlgebraicCurve.CurveModel.isOpenImmersion_ιInf AlgebraicCurve.CurveModel.algebra_overlap_functionField AlgebraicCurve.CurveModel.quasiCompact_gluedToBase AlgebraicCurve.CurveModel.algebraAdjoin AlgebraicCurve.CurveModel.isDedekindDomain_chartRing AlgebraicCurve.CurveModel.isIntegralClosure AlgebraicCurve.CurveModel.finite_chartRing AlgebraicCurve.CurveModel.centre_isPrime AlgebraicCurve.CurveModel.isFractionRing_chartRing AlgebraicCurve.CurveModel.finiteType_chartRing AlgebraicCurve.CurveModel.isNoetherianRing_chartRing AlgebraicCurve.CurveModel.isScalarTower_base_adjoin AlgebraicCurve.CurveModel.isScalarTower_adjoin AlgebraicCurve.CurveModel.chartRing_finitePresentation AlgebraicGeometry.ProjSpace.twistObj.addCommGroup AlgebraicGeometry.ProjSpace.twistFam.module AlgebraicGeometry.ProjSpace.twistObj.module AlgebraicGeometry.ProjSpace.twistObj.moduleSections AlgebraicGeometry.ProjSpace.twistFam.addCommGroup AdicCompletion.instIsLocalRingMaximalIdeal kmfloorsGlue_int_three_isPrime"
p2m_attr_erase "instance" "kmfloorsGlue_int_bot_isPrime"
p2m_attr_erase "simp" "GoodReductionJacobian.RelativeGroupLaw.nsmul_zero GoodReductionJacobian.RelativeGroupLaw.mem_torsionSubset GoodReductionJacobian.RelativeGroupLaw.nsmul_succ GoodReductionJacobian.RelativeGroupLaw.baseChangePointToBase_ofBase GoodReductionJacobian.RelativeGroupLaw.baseChangePointToBase_coe GoodReductionJacobian.RelativeGroupLaw.baseChangePointOfBase_coe GoodReductionJacobian.RelativeGroupLaw.baseChange_inv GoodReductionJacobian.RelativeGroupLaw.baseChangePointOfBase_toBase GoodReductionJacobian.RelativeGroupLaw.baseChange_mul GoodReductionJacobian.RelativeGroupLaw.baseChange_one NeronModelInfra.NeronModelPropertyBundle.endExtensionEquiv_symm_restrict NeronModelInfra.schemeHomOverComp_id_left NeronModelInfra.schemeHomOverComp_id_right NeronModelInfra.schemeHomOverId_coe NeronModelInfra.NeronModelPropertyBundle.endExtensionEquiv_apply NeronModelInfra.NeronModelPropertyBundle.restrict_endExtensionEquiv_symm NeronModelInfra.schemeHomOverComp_coe NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_fst NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_snd NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_fst NeronSpecialFibreInfra.neronEndRestrictEquiv_apply NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_fst_assoc NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_snd NeronSpecialFibreInfra.neronEndExtension_genericFibreRestrict NeronSpecialFibreInfra.specClosedFibreInclusion_eq NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_fst_assoc NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_snd_assoc NeronSpecialFibreInfra.genericFibreRestrict_neronEndExtension NeronSpecialFibreInfra.homOverId_coe NeronSpecialFibreInfra.homOverComp_coe NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_snd_assoc GoodReductionJacobian.RelativeGroupLaw.fibre_inv GoodReductionJacobian.RelativeGroupLaw.fibrePointToBase_coe GoodReductionJacobian.RelativeGroupLaw.fibrePointOfBase_toBase GoodReductionJacobian.RelativeGroupLaw.fibre_mul GoodReductionJacobian.RelativeGroupLaw.fibrePointToBase_ofBase GoodReductionJacobian.RelativeGroupLaw.fibre_one GoodReductionJacobian.RelativeGroupLaw.fibrePointOfBase_coe GoodReductionJacobian.relativeGroupLawOfGrpObj_inv GoodReductionJacobian.relativeGroupLawOfGrpObj_mul"
p2m_attr_erase "simp" "GoodReductionJacobian.overHomEquivSchemeHomOver_apply_coe GoodReductionJacobian.relativeGroupLawOfGrpObj_one GoodReductionJacobian.overHomEquivSchemeHomOver_symm_apply_left MvFormalGroup.Points.mk.injEq MvFormalGroup.Points.mk.sizeOf_spec CerednikDrinfeld.QM.FakeEllipticCurve.ExtraLevel.mk.injEq CerednikDrinfeld.QM.FakeEllipticCurve.ExtraLevel.mk.sizeOf_spec RegularLocalRingQuotientAscent.dualNumberFst_apply NeronModelInfra.schemeHomOverNpow_succ NeronModelInfra.schemeHomOverNpow_zero SheafOfModules.tensorUnit_eq AlgebraicGeometry.Scheme.Modules.tensorUnit_eq PresheafOfModules.InternalHom.presheaf_map_apply PresheafOfModules.InternalHom.curryFamily_app PresheafOfModules.InternalHom.add_app PresheafOfModules.InternalHom.smul_app PresheafOfModules.InternalHom.zero_app PresheafOfModules.ihomObj_map_val PresheafOfModules.ihomFunctor_map PresheafOfModules.InternalHom.restrict_app PresheafOfModules.InternalHom.postcomp_app PresheafOfModules.InternalHom.neg_app PresheafOfModules.curry'_app_val PresheafOfModules.InternalHom.presheaf_obj PresheafOfModules.ihomFunctor_obj PresheafOfModules.ihomObj_obj PresheafOfModules.InternalHom.sub_app PresheafOfModules.ihomMap_app_val AlgebraicGeometry.Scheme.Modules.tensorPow_zero AlgebraicGeometry.Scheme.Modules.tensorPow_succ AlgebraicGeometry.RelPicard.RigidifiedLineBundle.mk.sizeOf_spec AlgebraicGeometry.RelPicard.RigidifiedLineBundle.mk.injEq AlgebraicGeometry.Scheme.OrderedAffineCover.mk.injEq AlgebraicGeometry.OModulePresheaf.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCover.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.mk.injEq AlgebraicGeometry.Scheme.TwoAffineOpenCover.mk.injEq AlgebraicGeometry.Scheme.TwoAffineOpenCover.mk.sizeOf_spec AlgebraicGeometry.Scheme.TwoAffineOpenCover.pullback_U1 AlgebraicGeometry.Scheme.TwoAffineOpenCover.pullback_U0"
p2m_attr_erase "simp" "TwoChartCech.Sections.mk.injEq TwoChartCech.Cover.mk.injEq TwoChartCech.GrothendieckComplex.mk.injEq TwoChartCech.Sections.mk.sizeOf_spec TwoChartCech.Cover.mk.sizeOf_spec TwoChartCech.Cover.lineBundle_r0_apply TwoChartCech.GrothendieckComplex.mk.sizeOf_spec TwoChartCech.Cover.lineBundle_r1_apply CoherentBaseChange.TwoTermComplex.mk.sizeOf_spec CoherentBaseChange.TwoTermComplex.mk.injEq AlgebraicGeometry.OModulePresheaf.prod_obj AlgebraicGeometry.OModulePresheaf.restrOpen_obj AlgebraicGeometry.OModulePresheaf.DevissageStep.mk.injEq AlgebraicGeometry.OModulePresheaf.pushforward_obj AlgebraicGeometry.OModulePresheaf.im_obj AlgebraicGeometry.OModulePresheaf.pow_obj AlgebraicGeometry.OModulePresheaf.fstHom_app AlgebraicGeometry.OModulePresheaf.ker_obj AlgebraicGeometry.OModulePresheaf.coker_obj AlgebraicGeometry.OModulePresheaf.DevissageStep.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCover.preimage_U AlgebraicGeometry.OModulePresheaf.sndHom_app AlgebraicGeometry.OModulePresheaf.Hom.mk.injEq AlgebraicGeometry.OModulePresheaf.Hom.id_app AlgebraicGeometry.OModulePresheaf.AffHom.appSections_apply AlgebraicGeometry.OModulePresheaf.AffHom.comp_app AlgebraicGeometry.OModulePresheaf.AffSES.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.AffHom.kerMap_coe AlgebraicGeometry.OModulePresheaf.AffHom.id_app AlgebraicGeometry.OModulePresheaf.Hom.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.Hom.toAffHom_app AlgebraicGeometry.OModulePresheaf.SES.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.AffHom.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.Hom.comp_app AlgebraicGeometry.OModulePresheaf.SES.mk.injEq AlgebraicGeometry.OModulePresheaf.AffHom.mk.injEq AlgebraicGeometry.OModulePresheaf.Hom.appSections_apply AlgebraicGeometry.OModulePresheaf.AffSES.mk.injEq PresheafOfModules.freeεIso_hom_app PresheafOfModules.freeμIso_hom_app"
p2m_attr_erase "simp" "AlgebraicGeometry.RelPicard.RepresentsRelSubPic.mk.injEq AlgebraicGeometry.RelPicard.SubPicCondition.mk.injEq AlgebraicGeometry.RelPicard.SubPicCondition.mk.sizeOf_spec AlgebraicGeometry.RelPicard.RepresentsRelSubPic.mk.sizeOf_spec AlgebraicGeometry.SmoothProperCurve.sectionBaseChange_coe_snd AlgebraicGeometry.SmoothProperCurve.sectionBaseChange_coe_fst AlgebraicCurve.CurveModel.mk.injEq AlgebraicCurve.CurveModel.mk.sizeOf_spec AlgebraicCurve.mulAdele_apply AlgebraicCurve.residuePairing_apply_coe AlgebraicCurve.mem_adeleBdd AlgebraicCurve.weilSmul_one AlgebraicCurve.diagonalHom_apply AlgebraicCurve.weilSmul_apply AlgebraicCurve.adeleSpaceMul_coe AlgebraicCurve.mulAdele_one AlgebraicGeometry.SmoothProperCurve.FiniteMapData.twoAffineOpenCover_U1 AlgebraicGeometry.SmoothProperCurve.FiniteMapData.mk.injEq AlgebraicGeometry.SmoothProperCurve.FiniteMapData.mk.sizeOf_spec AlgebraicGeometry.SmoothProperCurve.FiniteMapData.twoAffineOpenCover_U0 AlgebraicGeometry.RelPicard.SubPicCondition.onClasses_mk AlgebraicGeometry.RelPicard.relSubPicPresheaf_map_coe CategoryTheory.Functor.OverTotal.ofFibre_fst CategoryTheory.Functor.overTotal_map_fst AlgebraicGeometry.Scheme.LocalRepresentabilityULift.glueData_J AlgebraicGeometry.Scheme.LocalRepresentabilityULift.uliftYoneda_toGlued_uliftYonedaGluedToSheaf AlgebraicGeometry.Scheme.LocalRepresentabilityULift.glueData_t' AlgebraicGeometry.Scheme.LocalRepresentabilityULift.uliftYoneda_toGlued_uliftYonedaGluedToSheaf_assoc AlgebraicGeometry.Scheme.LocalRepresentabilityULift.uliftYonedaGluedToSheaf_app_toGlued AlgebraicGeometry.Scheme.LocalRepresentabilityULift.glueData_openCover_map AlgebraicGeometry.Scheme.LocalRepresentabilityULift.uliftYonedaGluedToSheaf_app_comp AlgebraicGeometry.Scheme.LocalRepresentabilityULift.glueData_V AlgebraicGeometry.Scheme.LocalRepresentabilityULift.glueData_t AlgebraicGeometry.Scheme.LocalRepresentabilityULift.glueData_U AlgebraicGeometry.Scheme.LocalRepresentabilityULift.glueData_f AlgebraicGeometry.RelPicard.designationOfRepresentableBy_P AlgebraicGeometry.RelPicard.designationOfRepresentableBy_toBase AlgebraicGeometry.RelPicard.rigSection_snd AlgebraicGeometry.RelPicard.RigidifiedLineBundle.ofInvertible_L AlgebraicGeometry.RelPicard.rigSection_snd_assoc"
p2m_attr_erase "simp" "AlgebraicGeometry.RelPicard.SubPicGroupCondition.mk.injEq AlgebraicGeometry.RelPicard.SubPicGroupCondition.mk.sizeOf_spec AlgebraicCurve.coe_cechH0Equiv_apply AlgebraicCurve.cechH1ToH1_mk AlgebraicCurve.lSpaceOn_univ AlgebraicCurve.lSpaceOn_empty AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.Divisor.mapRestrict_single AlgebraicCurve.Divisor.pushforward_single AlgebraicCurve.Place.coe_restrictInclusion AlgebraicCurve.Place.mem_fiber AlgebraicCurve.Place.restrict_toValuationSubring AlgebraicCurve.Divisor.degree_pushforward AlgebraicCurve.Place.restrictResidueMap_residue AlgebraicCurve.Pic0.coe_pushforwardDegZeroHom AlgebraicCurve.Pic0.coe_pullbackDegZeroHom AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single"
p2m_attr_erase "simp" "ModularCurve.qExpandAlgC_apply AlgebraicCurve.Divisor.degree_pushforwardAlong AlgebraicCurve.Pic0.coe_degZeroCorrespondence AlgebraicCurve.Place.mem_fiberAlong AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.jqNModC_one ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one AlgebraicCurve.Place.differentialCoeff_zero AlgebraicCurve.Place.differentialCoeff_dCoord AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.injEq AlgebraicCurve.TranscendenceTower.mk.injEq AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec AlgebraicCurve.PoleDivisorPackage.mk.injEq AlgebraicGeometry.RelPicard.thetaBundle_def AlgebraicGeometry.RelPicard.picardBundle_def AlgebraicGeometry.RelEffCartierDiv.toRelEffDivisor_ofRelEffDivisor AlgebraicGeometry.RelEffCartierDiv.toRelEffDivisor_I AlgebraicGeometry.mapOnProdOver_fst_assoc AlgebraicGeometry.RelEffCartierDiv.mk.sizeOf_spec AlgebraicGeometry.RelEffCartierDiv.mk.injEq AlgebraicGeometry.mapOnProdOver_snd AlgebraicGeometry.mapOnProdOver_fst AlgebraicGeometry.mapOnProdOver_snd_assoc AlgebraicGeometry.mapOnProdOver_id"
p2m_attr_erase "simp" "AlgebraicCurve.RelEffDivisor.mk.sizeOf_spec AlgebraicCurve.mapOnProd_fst AlgebraicCurve.mapOnProd_fst_assoc AlgebraicCurve.mapOnProd_snd AlgebraicCurve.UnivDivisorPack.mk.injEq AlgebraicCurve.RelEffDivisor.mk.injEq AlgebraicCurve.UnivDivisorPack.mk.sizeOf_spec AlgebraicCurve.mapOnProd_snd_assoc AlgebraicGeometry.Scheme.Modules.exteriorPower_obj PresheafOfModules.exteriorPower_map_ιMulti PresheafOfModules.ExteriorPower.appₗ_apply AlgebraicGeometry.prodKerGraph_one AlgebraicGeometry.fibrePowOver.proj_comp AlgebraicGeometry.prodKerGraph_zero AlgebraicGeometry.RelEffCartierDiv.empty_I AlgebraicGeometry.fibrePowOver.proj_comp_assoc AlgebraicGeometry.graphOver_fst_assoc AlgebraicGeometry.RelEffCartierDiv.toPoint_comp AlgebraicGeometry.RelEffCartierDiv.toPoint_comp_assoc AlgebraicGeometry.graphOver_fst AlgebraicGeometry.RelEffCartierDiv.ofPoint_I AlgebraicGeometry.graphOver_snd AlgebraicGeometry.graphOver_snd_assoc AlgebraicCurve.SymmetricPowerPackage.mk.sizeOf_spec AlgebraicCurve.SymmetricPowerPackage.mk.injEq AlgebraicGeometry.FGSubalgebra.cocone_ι_app_apply AlgebraicGeometry.RelPicard.fst_toProdSpec AlgebraicGeometry.RelPicard.toProdSpec_fst_assoc AlgebraicGeometry.RelPicard.pointsSubBasepointModule_cons AlgebraicGeometry.RelPicard.pointsSubBasepointModule_nil AlgebraicGeometry.RelPicard.fst_toProdSpec_assoc AlgebraicGeometry.RelPicard.toProdSpec_fst AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.sub_app AlgebraicGeometry.Scheme.IdealSheafData.sres_sresTop AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.add_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.mk.sizeOf_spec AlgebraicGeometry.Scheme.IdealSheafData.coe_resLE AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.smul_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.coe_ofLE_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.ideal_range"
p2m_attr_erase "simp" "AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.zero_app AlgebraicGeometry.Scheme.IdealSheafData.sres_sres AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.comp_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.neg_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.id_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.coe_mulRight_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.nsmul_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.mk.injEq AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.zsmul_app AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.sizeOf_spec AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.injEq AlgebraicCurve.adeleSingle_coe AlgebraicCurve.kaehlerResidueTermKFam_apply AlgebraicCurve.Place.LocalResidueData.mk.injEq AlgebraicCurve.Place.LocalResidueData.mk.sizeOf_spec AlgebraicCurve.Place.kw_ffgc_adicCompletionComapIntegers_coe AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.sizeOf_spec AlgebraicCurve.Place.mem_simplePoleSubmodule AlgebraicCurve.Place.coe_uniformizerSubring ModularCurve.Lg37.Lg37CompletionSection.mk.injEq AlgebraicCurve.Place.CoefficientFieldSection.mk.injEq AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.injEq ModularCurve.Lg37.Lg37CompletionSection.mk.sizeOf_spec AlgebraicCurve.Place.CoefficientFieldSection.mk.sizeOf_spec AlgebraicCurve.Place.poleSubmodule_one AlgebraicCurve.Place.mem_poleSubmodule AlgebraicGeometry.Scheme.Modules.toUnitSection_ofUnitSection AlgebraicGeometry.Scheme.Modules.pullbackSection_def AlgebraicGeometry.Scheme.Modules.ofUnitSection_toUnitSection PresheafOfModules.InternalHom.IsSheafAux.appAt_toPresheafHom SheafOfModules.ihomSectionsEquivFamily_unit AlgebraicGeometry.Scheme.Modules.restrictHomEquivFamily_apply SheafOfModules.ihomEval_unit_app AlgebraicGeometry.Scheme.Modules.ihomEval_zero_right AlgebraicGeometry.Scheme.Modules.ihomEval_zero_left AlgebraicGeometry.Scheme.Modules.homOfFamily_app_apply SheafOfModules.unit_ihomSectionsEquivFamily AlgebraicGeometry.Scheme.Modules.familyOfHom_app AlgebraicGeometry.Scheme.Modules.restrictUnitIso_hom_app_apply AlgebraicGeometry.Scheme.Modules.restrictUnitIso_inv_app_apply"
p2m_attr_erase "simp" "AlgebraicGeometry.Scheme.Modules.restrictHomOfFamily_app_apply AlgebraicGeometry.Scheme.Modules.restrictHomEquivFamily_symm_apply AlgebraicGeometry.Scheme.Modules.tensorSections_zero_right AlgebraicGeometry.Scheme.Modules.map_unitSection AlgebraicGeometry.Scheme.Modules.tensorSectionsBilin_apply AlgebraicGeometry.Scheme.Modules.tensorPowSection_zero AlgebraicGeometry.Scheme.Modules.tensorSections_zero_left AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_neg AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_zero AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_sub AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_add AlgebraicGeometry.Scheme.OrderedAffineCover.toCoverOf_U AlgebraicGeometry.Scheme.OrderedAffineCoverOf.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCoverOf.mk.injEq AlgebraicGeometry.Scheme.OrderedAffineCover.restrict_U AlgebraicGeometry.OModulePresheaf.Leray.restrictToPreimage_U DoubleComplex.Bounded.mk.injEq DoubleComplex.Bounded.mk.sizeOf_spec DoubleComplex.Convergence.mk.injEq DoubleComplex.Convergence.mk.sizeOf_spec DoubleComplex.SubQuot.mk.sizeOf_spec DoubleComplex.SubQuot.mk.injEq AlgebraicGeometry.ChowDatumProj.mk.sizeOf_spec AlgebraicGeometry.ChowDatum.mk.sizeOf_spec AlgebraicGeometry.ChowDatumProj.mk.injEq AlgebraicGeometry.ChowDatum.mk.injEq ProjSpaceCech.GradedModule.mk.injEq ProjSpaceCech.GradedModule.mk.sizeOf_spec ProjSpaceCech.GradedModule.Frac.mk.sizeOf_spec ProjSpaceCech.GradedModule.Presentation.mk.injEq ProjSpaceCech.GradedModule.Frac.mk.injEq ProjSpaceCech.GradedModule.Presentation.mk.sizeOf_spec ProjSpaceCech.GradedModule.Hom.shift_toLinearMap ProjSpaceCech.GradedModule.Hom.mk.sizeOf_spec ProjSpaceCech.GradedModule.Hom.mk.injEq TwoChartCech.Mumford.dK_apply TwoChartCech.Mumford.ι0_apply TwoChartCech.Mumford.ι1_apply TwoChartCech.KerCoprod.dK_apply TwoChartCech.KerCoprod.ι1_apply"
p2m_attr_erase "simp" "TwoChartCech.KerCoprod.ι0_apply AlgebraicGeometry.tilde.functorCompPullbackSpecIso_app AlgebraicGeometry.RelPicard.algEquivZeroGroupCut_toSubPicCondition AlgebraicGeometry.RelPicard.LFP.stageHom_val AlgebraicGeometry.RelPicard.BaseChange.relSubPicPresheafRestrictIso_hom_app_coe AlgebraicGeometry.RelPicard.BaseChange.relSubPicPresheafRestrictIso_inv_app_coe AlgebraicGeometry.RelPicard.BaseChange.restrict_P AlgebraicGeometry.RelEffCartierDiv.IsUniversal.lift_comp AlgebraicGeometry.RelEffCartierDiv.functor_map_fst AlgebraicGeometry.RelEffCartierDiv.IsUniversal.homEquiv_apply AlgebraicGeometry.RelEffCartierDiv.IsUniversal.lift_pullbackAlong AlgebraicGeometry.RelEffCartierDiv.IsUniversal.homEquiv_symm_apply AlgebraicGeometry.RelEffCartierDiv.IsUniversal.lift_comp_assoc AlgebraicGeometry.RelEffCartierDiv.supportedIn_top AlgebraicGeometry.RelEffCartierDiv.mem_supportedIn_iff AlgebraicGeometry.RelEffCartierDiv.supportedIn_top_eq AlgebraicGeometry.RelEffCartierDiv.restrictAlong_extendAlong AlgebraicGeometry.RelEffCartierDiv.extendAlong_I AlgebraicGeometry.RelEffCartierDiv.resProdMap_snd AlgebraicGeometry.RelEffCartierDiv.restrictAlong_I AlgebraicGeometry.RelEffCartierDiv.extendAlong_restrictAlong AlgebraicGeometry.RelEffCartierDiv.resProdMap_fst_assoc AlgebraicGeometry.RelEffCartierDiv.resProdMap_snd_assoc AlgebraicGeometry.RelEffCartierDiv.resProdMap_fst CoherentBaseChange.FibreH0Family.mk.sizeOf_spec CoherentBaseChange.FibreH0Family.mk.injEq AlgebraicGeometry.Scheme.Modules.ProjPresentation.mk.injEq AlgebraicGeometry.Scheme.Modules.ProjPresentation.mk.sizeOf_spec AlgebraicCurve.CurveModel.coe_gInf AlgebraicCurve.CurveModel.coe_tInvChart AlgebraicCurve.CurveModel.ιInf_gluedToBase_assoc AlgebraicCurve.CurveModel.ιInf_gluedToBase AlgebraicCurve.CurveModel.primeOfι₀_asIdeal AlgebraicCurve.CurveModel.coe_tChart AlgebraicCurve.CurveModel.ι₀_gluedToBase_assoc AlgebraicCurve.CurveModel.primeOfιInf_asIdeal AlgebraicCurve.CurveModel.ι₀_gluedToBase AlgebraicCurve.CurveModel.coe_tma AlgebraicCurve.CurveModel.coe_primeEquivChartPlaces AlgebraicGeometry.ProjSpace.twistObj.mk.injEq"
p2m_attr_erase "simp" "AlgebraicGeometry.ProjSpace.twistObj.zero_val AlgebraicGeometry.ProjSpace.twistObj.add_val AlgebraicGeometry.ProjSpace.twist_res_val AlgebraicGeometry.ProjSpace.twist_smul_val AlgebraicGeometry.ProjSpace.twistGradeToObj_val AlgebraicGeometry.ProjSpace.twistObj.smul_val AlgebraicGeometry.ProjSpace.twistGradeEquiv_apply_val AlgebraicGeometry.ProjSpace.twistObj.mk.sizeOf_spec AlgebraicGeometry.schemeFibreEndo_snd AlgebraicGeometry.schemeFibreEndo_fst AlgebraicGeometry.Scheme.relFrobenius_snd AlgebraicGeometry.Scheme.frobenius_preimage AlgebraicGeometry.Scheme.relFrobenius_fst AlgebraicGeometry.Scheme.relFrobenius_snd_assoc AlgebraicGeometry.Scheme.relFrobenius_fst_assoc AlgebraicGeometry.powCharRingHom_apply AlgebraicGeometry.Scheme.frobenius_base"

set_option autoImplicit false

p2m_open "CategoryTheory AlgebraicGeometry NeronModelInfra GoodReductionJacobian QuaternionAlgebra CerednikDrinfeld P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_existsUnique_iso_lift_of_isFormalModuleVia_of_one_mem.CerednikDrinfeld CerednikDrinfeld.QM P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_existsUnique_iso_lift_of_isFormalModuleVia_of_one_mem.CerednikDrinfeld.QM CerednikDrinfeld.SpecialFormal"

open scoped Quaternion TensorProduct NumberField

namespace CerednikDrinfeld
p2m_export "CerednikDrinfeld" "Zp2 FormalODModule FormalODModule.Hom FormalODModule.Hom.id FormalODModule.Hom.toSeries QM.FakeEllipticCurve QM.FakeEllipticCurve.existsUnique_lev_lift QM.FakeEllipticCurve.existsUnique_hom_lift_of_isFormalModuleVia_of_one_mem"
namespace QM
p2m_export "CerednikDrinfeld.QM" "IsOrderCoord FakeEllipticCurve.IsPullbackVia mapPt mapPt_coe FactorsThrough FakeEllipticCurve FakeEllipticCurve.existsUnique_lev_lift FakeEllipticCurve.existsUnique_hom_lift_of_isFormalModuleVia_of_one_mem"
namespace STIsoAux
p2m_open "CerednikDrinfeld.QM CerednikDrinfeld"

open CategoryTheory

variable {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} {N : ℕ}

theorem mapPt_comp {B : Type} [CommRing B] {A₁ A₂ A₃ : Scheme.{0}} {f₁ : A₁ ⟶ Spec (CommRingCat.of B)}
    {f₂ : A₂ ⟶ Spec (CommRingCat.of B)} {f₃ : A₃ ⟶ Spec (CommRingCat.of B)}
    (φ : A₁ ⟶ A₂) (hφ : φ ≫ f₂ = f₁) (ψ : A₂ ⟶ A₃) (hψ : ψ ≫ f₃ = f₂) (h : (φ ≫ ψ) ≫ f₃ = f₁)
    {T : Scheme.{0}} {t : T ⟶ Spec (CommRingCat.of B)} (P : SchemeHomOver t f₁) :
    mapPt (φ ≫ ψ) h P = mapPt ψ hψ (mapPt φ hφ P) := by
  apply Subtype.ext; simp only [mapPt_coe, Category.assoc]

theorem mapPt_id' {B : Type} [CommRing B] {A₁ : Scheme.{0}} {f₁ : A₁ ⟶ Spec (CommRingCat.of B)}
    (h : 𝟙 A₁ ≫ f₁ = f₁) {T : Scheme.{0}} {t : T ⟶ Spec (CommRingCat.of B)} (P : SchemeHomOver t f₁) :
    mapPt (𝟙 A₁) h P = P := by
  apply Subtype.ext; simp only [mapPt_coe, Category.comp_id]

theorem mapPt_congr {B : Type} [CommRing B] {A₁ A₂ : Scheme.{0}} {f₁ : A₁ ⟶ Spec (CommRingCat.of B)}
    {f₂ : A₂ ⟶ Spec (CommRingCat.of B)} {φ ψ : A₁ ⟶ A₂} (hφ : φ ≫ f₂ = f₁) (hψ : ψ ≫ f₂ = f₁) (h : φ = ψ)
    {T : Scheme.{0}} {t : T ⟶ Spec (CommRingCat.of B)} (P : SchemeHomOver t f₁) :
    mapPt φ hφ P = mapPt ψ hψ P := by
  subst h; rfl

theorem inv_mul {B : Type} [CommRing B] (E E' : FakeEllipticCurve Λ N B) (e : E.A ≅ E'.A) (he : e.hom ≫ E'.f = E.f)
    (hmul : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of B)) (P Q : SchemeHomOver t E.f),
      mapPt e.hom he (E.L.mul t P Q) = E'.L.mul t (mapPt e.hom he P) (mapPt e.hom he Q))
    (hinv : e.inv ≫ E.f = E'.f)
    {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of B)) (P Q : SchemeHomOver t E'.f) :
    mapPt e.inv hinv (E'.L.mul t P Q) = E.L.mul t (mapPt e.inv hinv P) (mapPt e.inv hinv Q) := by
  have h := hmul t (mapPt e.inv hinv P) (mapPt e.inv hinv Q)
  have hid : (e.inv ≫ e.hom) ≫ E'.f = E'.f := by rw [Iso.inv_hom_id, Category.id_comp]
  rw [← mapPt_comp e.inv hinv e.hom he hid, ← mapPt_comp e.inv hinv e.hom he hid,
    mapPt_congr hid (by rw [Category.id_comp]) e.inv_hom_id, mapPt_congr hid (by rw [Category.id_comp]) e.inv_hom_id,
    mapPt_id', mapPt_id'] at h
  have hid' : (e.hom ≫ e.inv) ≫ E.f = E.f := by rw [Iso.hom_inv_id, Category.id_comp]
  have := congrArg (mapPt e.inv hinv) h
  rw [← mapPt_comp e.hom he e.inv hinv hid', mapPt_congr hid' (by rw [Category.id_comp]) e.hom_inv_id, mapPt_id'] at this
  exact this.symm

theorem inv_act {B : Type} [CommRing B] (E E' : FakeEllipticCurve Λ N B) (e : E.A ≅ E'.A)
    (hact : ∀ x : ↥Λ, E.act x ≫ e.hom = e.hom ≫ E'.act x) (x : ↥Λ) :
    E'.act x ≫ e.inv = e.inv ≫ E.act x := by
  rw [Iso.comp_inv_eq, Category.assoc, Iso.eq_inv_comp, hact]

end CerednikDrinfeld.QM.STIsoAux

theorem solution
    {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} {N : ℕ} {q : ℕ} [Fact q.Prime]
    (coord : ↥Λ → Zp2 q × Zp2 q) (hcoord : IsOrderCoord Λ q coord)
    (h1 : (1 : ℍ[ℚ, a, b]) ∈ Λ)

    (B B₀ : Type) [CommRing B] [IsNoetherianRing B] [CommRing B₀] [Algebra B B₀]
    (hπ : Function.Surjective (algebraMap B B₀)) (hker : IsNilpotent (RingHom.ker (algebraMap B B₀)))
    (hq : IsNilpotent ((q : ℕ) : B)) (hN : IsUnit ((N : ℕ) : B))
    (E E' : FakeEllipticCurve Λ N B) (X X' : FormalODModule q B)
    (θ : RelativeGroupLaw.FormalCoordinates E.f 2) (θ' : RelativeGroupLaw.FormalCoordinates E'.f 2)
    (hE : E.IsFormalModuleVia coord X θ) (hE' : E'.IsFormalModuleVia coord X' θ')
    (E₀ E₀' : FakeEllipticCurve Λ N B₀) (g : E₀.A ⟶ E.A) (g' : E₀'.A ⟶ E'.A)
    (hg : FakeEllipticCurve.IsPullbackVia (algebraMap B B₀) E E₀ g) (hg' : FakeEllipticCurve.IsPullbackVia (algebraMap B B₀) E' E₀' g')

    (e₀ : E₀.A ≅ E₀'.A) (he₀f : e₀.hom ≫ E₀'.f = E₀.f)
    (he₀mul : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of B₀)) (P Q : SchemeHomOver t E₀.f),
      mapPt e₀.hom he₀f (E₀.L.mul t P Q) = E₀'.L.mul t (mapPt e₀.hom he₀f P) (mapPt e₀.hom he₀f Q))
    (he₀act : ∀ x : ↥Λ, E₀.act x ≫ e₀.hom = e₀.hom ≫ E₀'.act x)
    (he₀lev : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of B₀)) (P : SchemeHomOver t E₀.f),
      FactorsThrough E₀.lev P ↔ FactorsThrough E₀'.lev (mapPt e₀.hom he₀f P))

    (T : FormalODModule.Hom X X') (hT : T.IsIso)
    (hTe₀ : ∀ (B'' : Type) [CommRing B''] [Algebra B B''] [Algebra B₀ B''] [IsScalarTower B B₀ B'']
      (J : Ideal B'') (n : ℕ), J ^ (n + 1) = ⊥ → ∀ (s : Fin 2 → B''), (∀ i, s i ∈ J) →
      ∀ p₀ : SchemeHomOver (Scheme.specOver (𝒪 := B₀) B'') E₀.f, p₀.1 ≫ g = (θ B'' s).1 →
        p₀.1 ≫ e₀.hom ≫ g' = (θ' B'' (fun i => MvFormalGroup.nilEval n (T.toSeries i) s)).1) :
    ∃! e : E.A ≅ E'.A, g ≫ e.hom = e₀.hom ≫ g' ∧
      ∃ he : e.hom ≫ E'.f = E.f,
        (∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of B)) (P Q : SchemeHomOver t E.f),
          mapPt e.hom he (E.L.mul t P Q) = E'.L.mul t (mapPt e.hom he P) (mapPt e.hom he Q)) ∧
        (∀ x : ↥Λ, E.act x ≫ e.hom = e.hom ≫ E'.act x) ∧
        (∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of B)) (P : SchemeHomOver t E.f),
          FactorsThrough E.lev P ↔ FactorsThrough E'.lev (mapPt e.hom he P)) ∧
        (∀ (B'' : Type) [CommRing B''] [Algebra B B''] (J : Ideal B'') (n : ℕ), J ^ (n + 1) = ⊥ →
          ∀ s : Fin 2 → B'', (∀ i, s i ∈ J) →
            (θ B'' s).1 ≫ e.hom = (θ' B'' (fun i => MvFormalGroup.nilEval n (T.toSeries i) s)).1) := by
  classical
  obtain ⟨S, hST, hTS⟩ := hT
  have hT0 : ∀ j, MvPowerSeries.constantCoeff (T.toSeries j) = 0 := fun j => T.isODHom.constantCoeff j
  have hS0 : ∀ j, MvPowerSeries.constantCoeff (S.toSeries j) = 0 := fun j => S.isODHom.constantCoeff j
  have hSTser : ∀ i, MvPowerSeries.subst T.toSeries (S.toSeries i) = MvPowerSeries.X i := fun i =>
    congrFun (congrArg FormalODModule.Hom.toSeries hST) i
  have hTSser : ∀ i, MvPowerSeries.subst S.toSeries (T.toSeries i) = MvPowerSeries.X i := fun i =>
    congrFun (congrArg FormalODModule.Hom.toSeries hTS) i

  have evalST : ∀ (B'' : Type) [CommRing B''] [Algebra B B''] (J : Ideal B'') (n : ℕ), J ^ (n + 1) = ⊥ →
      ∀ s : Fin 2 → B'', (∀ i, s i ∈ J) →
        (∀ i, MvFormalGroup.nilEval n (T.toSeries i) s ∈ J) ∧
        (fun i => MvFormalGroup.nilEval n (S.toSeries i) (fun j => MvFormalGroup.nilEval n (T.toSeries j) s)) = s := by
    intro B'' _ _ J n hJ s hs
    refine ⟨(MvFormalGroup.nilEval_subst_of_mem J n hJ s hs T.toSeries hT0 (S.toSeries 0)).1, ?_⟩
    funext i
    rw [← (MvFormalGroup.nilEval_subst_of_mem J n hJ s hs T.toSeries hT0 (S.toSeries i)).2, hSTser,
      MvFormalGroup.nilEval_X_of_mem J n hJ s hs]
  have evalTS : ∀ (B'' : Type) [CommRing B''] [Algebra B B''] (J : Ideal B'') (n : ℕ), J ^ (n + 1) = ⊥ →
      ∀ s : Fin 2 → B'', (∀ i, s i ∈ J) →
        (∀ i, MvFormalGroup.nilEval n (S.toSeries i) s ∈ J) ∧
        (fun i => MvFormalGroup.nilEval n (T.toSeries i) (fun j => MvFormalGroup.nilEval n (S.toSeries j) s)) = s := by
    intro B'' _ _ J n hJ s hs
    refine ⟨(MvFormalGroup.nilEval_subst_of_mem J n hJ s hs S.toSeries hS0 (T.toSeries 0)).1, ?_⟩
    funext i
    rw [← (MvFormalGroup.nilEval_subst_of_mem J n hJ s hs S.toSeries hS0 (T.toSeries i)).2, hTSser,
      MvFormalGroup.nilEval_X_of_mem J n hJ s hs]
  have evalId : ∀ (B'' : Type) [CommRing B''] [Algebra B B''] (J : Ideal B'') (n : ℕ), J ^ (n + 1) = ⊥ →
      ∀ s : Fin 2 → B'', (∀ i, s i ∈ J) → ∀ (Y : FormalODModule q B),
        (fun i => MvFormalGroup.nilEval n ((FormalODModule.Hom.id Y).toSeries i) s) = s := by
    intro B'' _ _ J n hJ s hs Y
    funext i
    exact MvFormalGroup.nilEval_X_of_mem J n hJ s hs i

  obtain ⟨φ, ⟨hφg, hφf, φmul, φact, φformal⟩, φuniq⟩ :=
    CerednikDrinfeld.QM.FakeEllipticCurve.existsUnique_hom_lift_of_isFormalModuleVia_of_one_mem coord hcoord h1 B B₀ hπ hker hq
      E E' X X' θ θ' hE hE' E₀ E₀' g g' hg hg' e₀.hom he₀f he₀mul he₀act T hTe₀

  have he₀f' : e₀.inv ≫ E₀.f = E₀'.f := by rw [Iso.inv_comp_eq, he₀f]
  have hSe₀ : ∀ (B'' : Type) [CommRing B''] [Algebra B B''] [Algebra B₀ B''] [IsScalarTower B B₀ B'']
      (J : Ideal B'') (n : ℕ), J ^ (n + 1) = ⊥ → ∀ (s' : Fin 2 → B''), (∀ i, s' i ∈ J) →
      ∀ p₀' : SchemeHomOver (Scheme.specOver (𝒪 := B₀) B'') E₀'.f, p₀'.1 ≫ g' = (θ' B'' s').1 →
        p₀'.1 ≫ e₀.inv ≫ g = (θ B'' (fun i => MvFormalGroup.nilEval n (S.toSeries i) s')).1 := by
    intro B'' _ _ _ _ J n hJ s' hs' p₀' hp₀'
    obtain ⟨hsJ, hTS'⟩ := evalTS B'' J n hJ s' hs'
    set s : Fin 2 → B'' := fun i => MvFormalGroup.nilEval n (S.toSeries i) s' with hs_def
    obtain ⟨hsq, -, -, -⟩ := hg
    obtain ⟨hsq', -, -, -⟩ := hg'
    have w : (θ B'' s).1 ≫ E.f = Spec.map (CommRingCat.ofHom (algebraMap B₀ B'')) ≫ Spec.map (CommRingCat.ofHom (algebraMap B B₀)) := by
      rw [(θ B'' s).2, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← IsScalarTower.algebraMap_eq B B₀ B'']
      try rfl
    let p₀ : SchemeHomOver (Scheme.specOver (𝒪 := B₀) B'') E₀.f :=
      ⟨hsq.lift (θ B'' s).1 (Spec.map (CommRingCat.ofHom (algebraMap B₀ B''))) w, hsq.lift_snd _ _ _⟩
    have hp₀ : p₀.1 ≫ g = (θ B'' s).1 := hsq.lift_fst _ _ _
    have key := hTe₀ B'' J n hJ s hsJ p₀ hp₀
    rw [hTS'] at key
    have heq : p₀'.1 = p₀.1 ≫ e₀.hom := by
      apply hsq'.hom_ext
      · rw [hp₀', Category.assoc, key]
      · rw [p₀'.2, Category.assoc, he₀f, p₀.2]
    rw [heq, Category.assoc, e₀.hom_inv_id_assoc, hp₀]
  obtain ⟨φ', ⟨hφ'g, hφ'f, φ'mul, φ'act, φ'formal⟩, -⟩ :=
    CerednikDrinfeld.QM.FakeEllipticCurve.existsUnique_hom_lift_of_isFormalModuleVia_of_one_mem coord hcoord h1 B B₀ hπ hker hq
      E' E X' X θ' θ hE' hE E₀' E₀ g' g hg' hg e₀.inv he₀f'
      (fun t P Q => STIsoAux.inv_mul E₀ E₀' e₀ he₀f he₀mul he₀f' t P Q) (STIsoAux.inv_act E₀ E₀' e₀ he₀act) S hSe₀

  have hid : ∀ (F : FakeEllipticCurve Λ N B) (Y : FormalODModule q B) (ϑ : RelativeGroupLaw.FormalCoordinates F.f 2)
      (hF : F.IsFormalModuleVia coord Y ϑ) (F₀ : FakeEllipticCurve Λ N B₀) (γ : F₀.A ⟶ F.A)
      (hγ : FakeEllipticCurve.IsPullbackVia (algebraMap B B₀) F F₀ γ) (χ : F.A ⟶ F.A),
      (γ ≫ χ = 𝟙 F₀.A ≫ γ ∧ ∃ hχ : χ ≫ F.f = F.f,
        (∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of B)) (P Q : SchemeHomOver t F.f),
          mapPt χ hχ (F.L.mul t P Q) = F.L.mul t (mapPt χ hχ P) (mapPt χ hχ Q)) ∧
        (∀ x : ↥Λ, F.act x ≫ χ = χ ≫ F.act x) ∧
        (∀ (B'' : Type) [CommRing B''] [Algebra B B''] (J : Ideal B'') (n : ℕ), J ^ (n + 1) = ⊥ →
          ∀ s : Fin 2 → B'', (∀ i, s i ∈ J) →
            (ϑ B'' s).1 ≫ χ = (ϑ B'' (fun i => MvFormalGroup.nilEval n ((FormalODModule.Hom.id Y).toSeries i) s)).1)) →
      χ = 𝟙 F.A := by
    intro F Y ϑ hF F₀ γ hγ χ hχ
    obtain ⟨ι, -, huniq⟩ :=
      CerednikDrinfeld.QM.FakeEllipticCurve.existsUnique_hom_lift_of_isFormalModuleVia_of_one_mem coord hcoord h1 B B₀ hπ hker hq
        F F Y Y ϑ ϑ hF hF F₀ F₀ γ γ hγ hγ (𝟙 F₀.A) (Category.id_comp _)
        (fun t P Q => by rw [STIsoAux.mapPt_id', STIsoAux.mapPt_id', STIsoAux.mapPt_id'])
        (fun x => by rw [Category.comp_id, Category.id_comp]) (FormalODModule.Hom.id Y)
        (fun B'' _ _ _ _ J n hJ s hs p₀ hp₀ => by rw [Category.id_comp, hp₀, evalId B'' J n hJ s hs Y])
    have h1 := huniq χ hχ
    have h2 := huniq (𝟙 F.A) ⟨by rw [Category.comp_id, Category.id_comp], Category.id_comp _,
      fun t P Q => by rw [STIsoAux.mapPt_id', STIsoAux.mapPt_id', STIsoAux.mapPt_id'],
      fun x => by rw [Category.comp_id, Category.id_comp],
      fun B'' _ _ J n hJ s hs => by rw [Category.comp_id, evalId B'' J n hJ s hs Y]⟩
    rw [h1, h2]
  have hφφ' : φ ≫ φ' = 𝟙 E.A := by
    apply hid E X θ hE E₀ g hg
    refine ⟨by rw [← Category.assoc, hφg, Category.assoc, hφ'g, e₀.hom_inv_id_assoc, Category.id_comp], ?_⟩
    refine ⟨by rw [Category.assoc, hφ'f, hφf], fun t P Q => ?_, fun x => ?_, fun B'' _ _ J n hJ s hs => ?_⟩
    · simp only [STIsoAux.mapPt_comp φ hφf φ' hφ'f, φmul, φ'mul]
    · rw [← Category.assoc, φact, Category.assoc, φ'act, Category.assoc]
    · obtain ⟨hsJ, hback⟩ := evalST B'' J n hJ s hs
      rw [evalId B'' J n hJ s hs X, ← Category.assoc, φformal B'' J n hJ s hs, φ'formal B'' J n hJ _ hsJ, hback]
  have hφ'φ : φ' ≫ φ = 𝟙 E'.A := by
    apply hid E' X' θ' hE' E₀' g' hg'
    refine ⟨by rw [← Category.assoc, hφ'g, Category.assoc, hφg, e₀.inv_hom_id_assoc, Category.id_comp], ?_⟩
    refine ⟨by rw [Category.assoc, hφf, hφ'f], fun t P Q => ?_, fun x => ?_, fun B'' _ _ J n hJ s hs => ?_⟩
    · simp only [STIsoAux.mapPt_comp φ' hφ'f φ hφf, φ'mul, φmul]
    · rw [← Category.assoc, φ'act, Category.assoc, φact, Category.assoc]
    · obtain ⟨hsJ, hback⟩ := evalTS B'' J n hJ s hs
      rw [evalId B'' J n hJ s hs X', ← Category.assoc, φ'formal B'' J n hJ s hs, φformal B'' J n hJ _ hsJ, hback]
  let e : E.A ≅ E'.A := ⟨φ, φ', hφφ', hφ'φ⟩

  have hlev : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of B)) (P : SchemeHomOver t E.f),
      FactorsThrough E.lev P ↔ FactorsThrough E'.lev (mapPt e.hom hφf P) := by
    intro T t P₁
    obtain ⟨hsq, hgmul, hgact, hglev⟩ := hg
    obtain ⟨hsq', hg'mul, hg'act, hg'lev⟩ := hg'

    have hpbE : FakeEllipticCurve.IsPullbackVia (algebraMap B B₀) E E₀' (g' ≫ e.inv) := by
      have hge : g' ≫ e.inv = e₀.inv ≫ g := by
        show g' ≫ φ' = e₀.inv ≫ g
        rw [hφ'g]
      rw [hge]
      refine ⟨?_, ?_, ?_, ?_⟩
      · exact hsq.of_iso e₀ (Iso.refl _) (Iso.refl _) (Iso.refl _)
          (by rw [Iso.refl_hom, Category.comp_id, e₀.hom_inv_id_assoc])
          (by rw [Iso.refl_hom, Category.comp_id, he₀f]) (by simp) (by simp)
      · intro T' t' P Q
        have h1 := STIsoAux.inv_mul E₀ E₀' e₀ he₀f he₀mul he₀f' t' P Q
        have h2 := hgmul t' (mapPt e₀.inv he₀f' P) (mapPt e₀.inv he₀f' Q)
        have h1' := congrArg (fun R : SchemeHomOver t' E₀.f => R.1 ≫ g) h1
        simp only [mapPt_coe, Category.assoc] at h1' h2 ⊢
        rw [h1', h2]
      · intro x
        rw [← Category.assoc, STIsoAux.inv_act E₀ E₀' e₀ he₀act x, Category.assoc, hgact, Category.assoc]
      · intro T' t' P hP
        have hP' : FactorsThrough E₀.lev (mapPt e₀.inv he₀f' P) := by
          rw [he₀lev]
          have hid : (e₀.inv ≫ e₀.hom) ≫ E₀'.f = E₀'.f := by rw [Iso.inv_hom_id, Category.id_comp]
          rw [← STIsoAux.mapPt_comp e₀.inv he₀f' e₀.hom he₀f hid,
            STIsoAux.mapPt_congr hid (by rw [Category.id_comp]) e₀.inv_hom_id, STIsoAux.mapPt_id']
          exact hP
        obtain ⟨P₀, hP₀⟩ := hglev t' (mapPt e₀.inv he₀f' P) hP'
        exact ⟨P₀, by rw [hP₀, mapPt_coe, Category.assoc]⟩

    obtain ⟨Es, es, hes, esmul, esact, hpbs, huniq⟩ :=
      CerednikDrinfeld.QM.FakeEllipticCurve.existsUnique_lev_lift B B₀ hπ hker hN E' E₀' g' hsq' hg'mul hg'act
    have hrefl : FakeEllipticCurve.IsPullbackVia (algebraMap B B₀) E' E₀' (g' ≫ (Iso.refl E'.A).inv) := by
      rw [Iso.refl_inv, Category.comp_id]; exact ⟨hsq', hg'mul, hg'act, hg'lev⟩
    have u1 := huniq E' (Iso.refl E'.A) (Category.id_comp _)
      (fun t' P Q => by simp only [Iso.refl_hom, STIsoAux.mapPt_id'])
      (fun x => by simp only [Iso.refl_hom, Category.comp_id, Category.id_comp]) hrefl t (mapPt e.hom hφf P₁)
    have u2 := huniq E e hφf φmul φact hpbE t (mapPt e.hom hφf P₁)
    rw [u1] at u2

    have hl : mapPt (Iso.refl E'.A).inv (by simp) (mapPt e.hom hφf P₁) = mapPt e.hom hφf P₁ := by
      apply Subtype.ext; simp only [mapPt_coe, Iso.refl_inv, Category.comp_id]
    have hr : mapPt e.inv (by rw [Iso.inv_comp_eq, hφf]) (mapPt e.hom hφf P₁) = P₁ := by
      apply Subtype.ext; simp only [mapPt_coe, Category.assoc, Iso.hom_inv_id, Category.comp_id]
    rw [hl, hr] at u2
    exact u2.symm

  refine ⟨e, ⟨hφg, hφf, φmul, φact, hlev, φformal⟩, ?_⟩
  rintro e' ⟨he'g, he'f, e'mul, e'act, -, e'formal⟩
  ext
  exact φuniq e'.hom ⟨he'g, he'f, e'mul, e'act, e'formal⟩

end S_CerednikDrinfeld_QM_FakeEllipticCurve_existsUnique_iso_lift_of_isFormalModuleVia_of_one_mem
end P2MW
export P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_existsUnique_iso_lift_of_isFormalModuleVia_of_one_mem (solution)
