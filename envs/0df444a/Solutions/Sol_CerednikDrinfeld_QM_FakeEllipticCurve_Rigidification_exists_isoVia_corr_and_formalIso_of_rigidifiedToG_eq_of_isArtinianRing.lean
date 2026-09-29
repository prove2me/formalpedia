-- Prove2me | solution 1 for CerednikDrinfeld.QM.FakeEllipticCurve.Rigidification.exists_isoVia_corr_and_formalIso_of_rigidifiedToG_eq_of_isArtinianRing
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.837917+00:00
-- url     : https://prove2.me/submissions/9c0b9de2-6e64-51c6-ae65-eda7eb4bab6e

import Definitions.Def_CerednikDrinfeld_QMRigidification
import Definitions.Def_CerednikDrinfeld_SpecialFormalFunctorG
import Definitions.Def_CerednikDrinfeld_CosetGraphAtPrime

import Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_IsPullbackVia_exists_isFormalModuleVia_map_and_comp_eq
import Theorems.Thm_CerednikDrinfeld_SpecialFormal_Rigidified_IsAdmissible_map_ringHom
import Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_isFinite_flat_surjective_of_mapPt_mapPt_eq_nsmulPt
import Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_pushPt_act_natCast_eq_nsmulPt
import Theorems.Thm_MvFormalGroup_nilEval_subst_of_mem
import Theorems.Thm_CerednikDrinfeld_FormalOmega_eq_of_frobTwist_eq_frobTwist_of_isNilpotent_of_nontrivial
import Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_exists_isoVia_corr_inducing_of_formalIso_of_isRigTransport_of_isAlgClosed
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_Rigidification_exists_isoVia_corr_and_formalIso_of_rigidifiedToG_eq_of_isArtinianRing
p2m_attr_erase "instance" "instTopologicallyFGOfFiniteType GoodReductionJacobian.RelativeGroupLaw.isIso_endKerStr_schemeHomOverId AlgebraicGeometry.Scheme.PresheafOfModules.symmetricCategory SheafOfModules.instFaithfulRingSheafPModToPMod SheafOfModules.symmetricCategory AlgebraicGeometry.Scheme.PresheafOfModules.monoidalCategory AlgebraicGeometry.Scheme.PresheafOfModules.monoidalClosed SheafOfModules.instFullRingSheafPModToPMod SheafOfModules.monoidalCategory AlgebraicGeometry.Scheme.Modules.symmetricCategory SheafOfModules.monoidalClosed SheafOfModules.instIsLocalizationPModRingSheafSheafifyFunctorPresheafW SheafOfModules.sheafifyFunctor_monoidal AlgebraicGeometry.Scheme.Modules.monoidalClosed AlgebraicGeometry.instMonoidalPresheafOfModulesModulesSheafify AlgebraicGeometry.Scheme.Modules.monoidalCategory PresheafOfModules.instMonoidalClosed PresheafOfModules.InternalHom.instModuleCarrierObjOppositeCommRingCatSubtypePiFamilyMemAddSubgroupNaturalFamilies PresheafOfModules.InternalHom.instModuleCarrierObjOppositeRingCatCompCommRingCatForget₂RingHomCarrierCarrierAbPresheaf PresheafOfModules.InternalHom.instSMulCarrierObjOppositeCommRingCatSubtypePiFamilyMemAddSubgroupNaturalFamilies AlgebraicGeometry.Scheme.Hom.opensMapFinal AlgebraicGeometry.RelPicard.RigidifiedLineBundle.setoid AlgebraicGeometry.RelPicard.RigidifiedLineBundle.instInhabited AlgebraicGeometry.OModulePresheaf.isScalarTower AlgebraicGeometry.Scheme.OrderedAffineCover.instLinearOrder AlgebraicGeometry.OModulePresheaf.module AlgebraicGeometry.Scheme.OrderedAffineCover.instFintype AlgebraicGeometry.Scheme.OrderedAffineCover.instFintypeIdx AlgebraicGeometry.OModulePresheaf.addCommGroup AlgebraicGeometry.Scheme.OrderedAffineCover.instDecidableEqIdx AlgebraicGeometry.OModulePresheaf.moduleSections TwoChartCech.Sections.M0_moduleA TwoChartCech.Sections.M1_module TwoChartCech.Cover.A01_algebra TwoChartCech.Cover.A0_algebra TwoChartCech.Cover.A1_commRing TwoChartCech.Cover.A1_algebra TwoChartCech.Sections.M01_module TwoChartCech.Sections.M0_addCommGroup TwoChartCech.Sections.M0_tower"
p2m_attr_erase "instance" "TwoChartCech.Sections.M01_addCommGroup TwoChartCech.Cover.A0_commRing TwoChartCech.Sections.M1_tower TwoChartCech.Sections.M01_moduleA TwoChartCech.Sections.M0_module TwoChartCech.Sections.M1_moduleA TwoChartCech.Sections.M1_addCommGroup TwoChartCech.Cover.A01_commRing TwoChartCech.Sections.M01_tower CoherentBaseChange.TwoTermComplex.C0_module CoherentBaseChange.TwoTermComplex.C0_addCommGroup CoherentBaseChange.TwoTermComplex.C1_module CoherentBaseChange.TwoTermComplex.C1_addCommGroup CoherentBaseChange.TwoTermComplex.C0_free CoherentBaseChange.TwoTermComplex.C1_finite CoherentBaseChange.TwoTermComplex.C0_finite CoherentBaseChange.TwoTermComplex.C1_free AlgebraicGeometry.OModulePresheaf.instSubsingletonObjZero AlgebraicGeometry.Scheme.Modules.preservesBinaryProducts_opensMap AlgebraicGeometry.Scheme.Modules.pullback_monoidal AlgebraicGeometry.Scheme.Modules.sheafify_isLocalization' AlgebraicGeometry.Scheme.Modules.preservesTerminal_opensMap AlgebraicGeometry.Scheme.Modules.pullback₀_monoidal AlgebraicGeometry.Scheme.Modules.preservesFiniteProducts_opensMap AlgebraicGeometry.Scheme.Modules.instLiftingPresheafOfModulesSheafifyPresheafWOpensCarrierCarrierCommRingCatGrothendieckTopologyObjFunctorOppositeIsSheafSheafCompPullback₀Pullback PresheafOfModules.PullbackMonoidal.pullback_monoidal PresheafOfModules.PullbackMonoidal.isIso_δ PresheafOfModules.pushforward_laxMonoidal PresheafOfModules.PullbackMonoidal.isIso_η PresheafOfModules.free_monoidal PresheafOfModules.restrictScalars_laxMonoidal PresheafOfModules.PullbackMonoidal.isIso_δ_gS PresheafOfModules.pullback_oplaxMonoidal PresheafOfModules.PullbackMonoidal.instPreservesColimitsOfSizeCompOppositeCommRingCatRingCatForget₂RingHomCarrierCarrierPb PresheafOfModules.pullback_monoidal' AlgebraicGeometry.SmoothOfRelativeDimension.fiberToSpecResidueField AlgebraicGeometry.SmoothOfRelativeDimension.pullback_snd AlgebraicGeometry.SmoothOfRelativeDimension.pullback_fst AlgebraicGeometry.SmoothOfRelativeDimension.smooth_one AlgebraicGeometry.SmoothProperCurve.isIntegral_pullback_Spec_field"
p2m_attr_erase "instance" "AlgebraicGeometry.IsProper.fiberToSpecResidueField AlgebraicCurve.CurveModel.isProper AlgebraicCurve.CurveModel.isIntegral AlgebraicCurve.CurveModel.smooth AlgebraicGeometry.Scheme.LocalRepresentabilityULift.instIsLocallyInjectiveFunUliftYonedaGluedToSheaf AlgebraicGeometry.Scheme.LocalRepresentabilityULift.instIsLocallySurjectiveFunUliftYonedaGluedToSheafOfIsLocallySurjectiveZariskiTopologyDescFunctorOppositeType AlgebraicGeometry.Scheme.LocalRepresentabilityULift.instIsOpenImmersionToGlued AlgebraicGeometry.Scheme.LocalRepresentabilityULift.instIsIsoSheafZariskiTopologyTypeUliftYonedaGluedToSheaf AlgebraicGeometry.RelPicard.instIsOpenImmersionToGlued AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.instFundamentalIdentityOfSumRamificationInertia AlgebraicCurve.Place.instIsScalarTowerResidueFieldRestrictPushforward AlgebraicCurve.Place.instAlgebraResidueFieldRestrictPushforward AlgebraicCurve.Place.instIsLocalHomRestrictInclusion AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions PresheafOfModules.ExteriorPower.instModulePresheafAb AlgebraicGeometry.RelEffCartierDiv.subsingleton_of_degree_zero AlgebraicGeometry.RelEffCartierDiv.isIso_subschemeIota_snd_of_degree_one AlgebraicGeometry.isIso_ker_graphOver_subschemeIota_snd AlgebraicGeometry.isClosedImmersion_graphOver AlgebraicGeometry.FGSubalgebra.instIsDirectedLe AlgebraicGeometry.FGSubalgebra.instQuasiSeparatedSpaceCarrierCarrierCommRingCatObjOppositeSchemeSpecDiagram AlgebraicGeometry.FGSubalgebra.instIsCofilteredOpposite AlgebraicGeometry.FGSubalgebra.instIsAffineObjOppositeSchemeSpecDiagram AlgebraicGeometry.FGSubalgebra.instNonempty AlgebraicGeometry.FGSubalgebra.instNonemptySubtypeLeSubalgebraValFG AlgebraicGeometry.FGSubalgebra.instCompactSpaceCarrierCarrierCommRingCatObjOppositeSchemeSpecDiagram AlgebraicGeometry.FGSubalgebra.instIsDirectedSubtypeLeSubalgebraValFG AlgebraicGeometry.FGSubalgebra.instIsAffineHomMapOppositeSchemeSpecDiagram AlgebraicGeometry.FGSubalgebra.instIsFiltered AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instNeg AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instSMulInt AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instAddCommGroup AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instAdd"
p2m_attr_erase "instance" "AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instSub AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instModuleCarrierObjOppositeOpensCarrierCarrierCommRingCatPresheafOpOpensTop AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instSMulCarrierObjOppositeOpensCarrierCarrierCommRingCatPresheafOpOpensTop AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instSMulNat AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instZero AlgebraicCurve.instHasLocalResidue_of_hasCanonicalLocalResidueK AlgebraicCurve.instHasCanonicalLocalResidueK_of_hasCanonicalLocalResidueKStar AlgebraicCurve.Place.kw_ffgc_finiteDimensional_adicCompletion instAlgebraSubtypeMemValuationSubring_definitions AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersIntegersCompletion ModularCurve.KwF4gRRTate.instAlgebraKAdicCompletionIntegers AlgebraicCurve.Place.kw_ffgc_continuousSMul_adicCompletionComap AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersCompletionCompletion IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions AlgebraicCurve.instHasCanonicalLocalResidueK AlgebraicCurve.Place.instAlgebra_restrictResidueField AlgebraicCurve.Place.instIsScalarTower_restrictResidueField AlgebraicCurve.instHasLocalResidue AlgebraicCurve.HasSeparableResidue.of_perfectField_of_isCurveOver AlgebraicCurve.HasSeparableResidue.of_perfectField AlgebraicCurve.Place.instIsLocalHom_restrictSubringHom AlgebraicCurve.instHasCanonicalLocalResidueKStar ModularCurve.KwNo6Pin.isLocalRing_completion SheafOfModules.isIso_ihomModelToIhom AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instDecidableEqIdx AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instFintype AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instLinearOrder AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instFintypeIdx AlgebraicGeometry.OModulePresheaf.Leray.relAltC_scalarTower AlgebraicGeometry.OModulePresheaf.Leray.ker_relAltd_modΓ AlgebraicGeometry.OModulePresheaf.Leray.relAltC_modΓ AlgebraicGeometry.OModulePresheaf.Leray.biC_abGrp AlgebraicGeometry.OModulePresheaf.Leray.relAltH_modΓ AlgebraicGeometry.OModulePresheaf.Leray.ker_relAltd_smul AlgebraicGeometry.OModulePresheaf.Leray.relAltH_scalarTower"
p2m_attr_erase "instance" "AlgebraicGeometry.OModulePresheaf.Leray.relAltH_smul AlgebraicGeometry.OModulePresheaf.Leray.biC_module DoubleComplex.instModuleE₂I DoubleComplex.Bounded.modR DoubleComplex.instModuleE₂II DoubleComplex.instAddCommGroupE₂II DoubleComplex.Bounded.abGrp DoubleComplex.instAddCommGroupE₂I AlgebraicGeometry.ChowDatum.hι_closed AlgebraicGeometry.ChowDatumProj.hιN_closed AlgebraicGeometry.ChowDatumProj.hp_proper AlgebraicGeometry.ChowDatum.hp_isoU AlgebraicGeometry.ChowDatum.hp_proper AlgebraicGeometry.ProjSpace.algebraAway AlgebraicGeometry.ProjSpace.instIsProperProdOverπ AlgebraicGeometry.ChowDatumProj.hp_isoU AlgebraicGeometry.ProjSpace.isProper_π AlgebraicGeometry.ProjSpace.finiteType_mvPolynomial ProjSpaceCech.GradedModule.H.module ProjSpaceCech.GradedModule.H.addCommGroup ProjSpaceCech.GradedModule.sec.instAdd ProjSpaceCech.GradedModule.sec.instNeg ProjSpaceCech.GradedModule.acg ProjSpaceCech.GradedModule.Frac.setoid ProjSpaceCech.GradedModule.modR ProjSpaceCech.GradedModule.sec.instModule ProjSpaceCech.GradedModule.sec.instAddCommGroup ProjSpaceCech.GradedModule.sec.instZero ProjSpaceCech.GradedModule.Presentation.fJ ProjSpaceCech.GradedModule.sec.instSMul ProjSpaceCech.Twist.H.module ProjSpaceCech.Idx.instFintype ProjSpaceCech.Twist.H.addCommGroup ProjSpaceCech.Idx.instDecidableEq ProjSpaceCech.Twist.Mon.instDecidableEq ProjSpaceCech.Twist.cochain.instAddCommGroup ProjSpaceCech.Twist.cochain.instModule AlgebraicGeometry.FGSubalgebra.tensorStage_directedSystem AlgebraicGeometry.RelEffCartierDiv.isClosedImmersion_subschemeι_resProdMap AlgebraicGeometry.RelEffCartierDiv.isOpenImmersion_resProdMap"
p2m_attr_erase "instance" "AlgebraicCurve.CurveModel.locallyOfFiniteType_gluedToBase AlgebraicCurve.CurveModel.isFractionRing_overlap AlgebraicCurve.CurveModel.isLocallyNoetherian_glued AlgebraicCurve.CurveModel.jacobsonSpace_glued AlgebraicCurve.CurveModel.isOpenImmersion_ι₀ AlgebraicCurve.CurveModel.isIntegral_glued AlgebraicCurve.CurveModel.quasiSeparated_gluedToBase AlgebraicCurve.CurveModel.compactSpace_glued AlgebraicCurve.CurveModel.isIntegral_adjoin_chartRing AlgebraicCurve.CurveModel.isFractionRing_overlap_functionField AlgebraicCurve.CurveModel.isProper_gluedToBase AlgebraicCurve.CurveModel.isOpenImmersion_ιU AlgebraicCurve.CurveModel.isOpenImmersion_f₀ AlgebraicCurve.CurveModel.isOpenImmersion_fInf AlgebraicCurve.CurveModel.isOpenImmersion_ιInf AlgebraicCurve.CurveModel.algebra_overlap_functionField AlgebraicCurve.CurveModel.quasiCompact_gluedToBase AlgebraicCurve.CurveModel.algebraAdjoin AlgebraicCurve.CurveModel.isDedekindDomain_chartRing AlgebraicCurve.CurveModel.isIntegralClosure AlgebraicCurve.CurveModel.finite_chartRing AlgebraicCurve.CurveModel.centre_isPrime AlgebraicCurve.CurveModel.isFractionRing_chartRing AlgebraicCurve.CurveModel.finiteType_chartRing AlgebraicCurve.CurveModel.isNoetherianRing_chartRing AlgebraicCurve.CurveModel.isScalarTower_base_adjoin AlgebraicCurve.CurveModel.isScalarTower_adjoin AlgebraicCurve.CurveModel.chartRing_finitePresentation AlgebraicGeometry.ProjSpace.twistObj.addCommGroup AlgebraicGeometry.ProjSpace.twistFam.module AlgebraicGeometry.ProjSpace.twistObj.module AlgebraicGeometry.ProjSpace.twistObj.moduleSections AlgebraicGeometry.ProjSpace.twistFam.addCommGroup MvFormalGroup.Points.instNeg MvFormalGroup.Points.instZero MvFormalGroup.Points.instAdd MvFormalGroup.Points.instAddCommGroup MvFormalGroup.Points.instAddGroup kmfloorsGlue_int_three_isPrime kmfloorsGlue_int_bot_isPrime"
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
p2m_attr_erase "simp" "AlgebraicGeometry.ProjSpace.twistGradeToObj_val AlgebraicGeometry.ProjSpace.twistObj.smul_val AlgebraicGeometry.ProjSpace.twistGradeEquiv_apply_val AlgebraicGeometry.ProjSpace.twistObj.mk.sizeOf_spec AlgebraicGeometry.schemeFibreEndo_snd AlgebraicGeometry.schemeFibreEndo_fst MvFormalGroup.Points.mk.injEq MvFormalGroup.Points.mk.sizeOf_spec AlgebraicGeometry.Scheme.relFrobenius_snd AlgebraicGeometry.Scheme.frobenius_preimage AlgebraicGeometry.Scheme.relFrobenius_fst AlgebraicGeometry.Scheme.relFrobenius_snd_assoc AlgebraicGeometry.Scheme.relFrobenius_fst_assoc AlgebraicGeometry.powCharRingHom_apply AlgebraicGeometry.Scheme.frobenius_base"

set_option autoImplicit false

open scoped TensorProduct Quaternion NumberField
open CategoryTheory AlgebraicGeometry QuaternionAlgebra IsDedekindDomain CerednikDrinfeld CerednikDrinfeld.QM CerednikDrinfeld.FormalOmega CerednikDrinfeld.SpecialFormal NeronModelInfra GoodReductionJacobian

namespace XCSol

open MvPowerSeries in

theorem nilEval_map {σ : Type} [Fintype σ] [DecidableEq σ] {R R' B'' : Type} [CommRing R] [CommRing R'] [CommRing B'']
    [Algebra R B''] [Algebra R' B''] (f : R →+* R') (h : algebraMap R B'' = (algebraMap R' B'').comp f)
    (n : ℕ) (φ : MvPowerSeries σ R) (a : σ → B'') :
    MvFormalGroup.nilEval n (MvPowerSeries.map f φ) a = MvFormalGroup.nilEval n φ a := by
  unfold MvFormalGroup.nilEval
  rw [MvPowerSeries.trunc'_map, MvPolynomial.aeval_def, MvPolynomial.aeval_def, MvPolynomial.eval₂_map, ← h]

open MvPowerSeries in

theorem constantCoeff_subst_of_constantCoeff_eq_zero {σ τ : Type} [Finite σ] {R : Type} [CommRing R]
    {a : σ → MvPowerSeries τ R} (ha' : ∀ i, (a i).constantCoeff = 0) (f : MvPowerSeries σ R) :
    MvPowerSeries.constantCoeff (subst a f) = MvPowerSeries.constantCoeff f := by
  have ha := hasSubst_of_constantCoeff_zero ha'
  rw [constantCoeff_subst ha, finsum_eq_single _ 0]
  · simp
  · intro d hd
    have : constantCoeff (d.prod fun s e ↦ a s ^ e) = 0 := by
      obtain ⟨i, hi⟩ : ∃ i : σ, d i ≠ 0 := by
        by_contra! hc
        exact hd <| Finsupp.ext hc
      first
        | simpa [map_finsuppProd, ha'] using
            Finset.prod_eq_zero (i := i) (by simp [hi]) (by simp [ha', zero_pow hi])
        | (simp only [map_finsuppProd, ha']
           exact Finset.prod_eq_zero (i := i) (by simp [hi]) (by simp [ha', zero_pow hi]))
    rw [this, smul_zero]

end XCSol

theorem xc_with_rel
    {r rbar N : ℕ} [Fact r.Prime] [Fact rbar.Prime] [NeZero N] (hrr : rbar ≠ r) (hrN : ¬ r ∣ N)

    (𝒪 : Type) [CommRing 𝒪] [IsDomain 𝒪] [CharZero 𝒪] (hdvr : IsDiscreteValuationRing 𝒪)
    (π : 𝒪) (hπ : Irreducible π) (hcomplete : IsAdicComplete (Ideal.span {π}) 𝒪)
    (hres : Nat.card (𝒪 ⧸ Ideal.span {π}) = r) (hunr : Ideal.span {((r : ℕ) : 𝒪)} = Ideal.span {π})
    (K₀ : Type) [Field K₀] [CharZero K₀] [Algebra 𝒪 K₀] [IsFractionRing 𝒪 K₀]

    (Onr : Type) [CommRing Onr] [IsDomain Onr] [CharZero Onr] [Algebra 𝒪 Onr] (Fr : Onr ≃ₐ[𝒪] Onr)
    (hOnr_complete : IsAdicComplete (Ideal.span {algebraMap 𝒪 Onr π}) Onr)
    (hOnr_max : (Ideal.span {algebraMap 𝒪 Onr π}).IsMaximal)
    (hOnr_alg : ∀ x : Onr, ∃ p : Polynomial 𝒪, p.Monic ∧ Polynomial.aeval x p ∈ Ideal.span {algebraMap 𝒪 Onr π})
    (hOnr_closed : ∀ p : Polynomial Onr, p.Monic → 0 < p.natDegree → ∃ x : Onr, Polynomial.eval x p ∈ Ideal.span {algebraMap 𝒪 Onr π})
    (hFr : ∀ x : Onr, Fr x - x ^ r ∈ Ideal.span {algebraMap 𝒪 Onr π})

    {a b : ℚ} (hB : IsIndefiniteRamifiedExactlyAt a b r rbar)
    (Λ : Submodule ℤ ℍ[ℚ, a, b]) (hΛ : IsMaximalOrder Λ) (hΛℤ : ∀ m : ℤ, ((m : ℚ) : ℍ[ℚ, a, b]) ∈ Λ)
    (coord : ↥Λ → Zp2 r × Zp2 r) (hcoord : IsOrderCoord Λ r coord)
    (A₀ : FakeEllipticCurve Λ N (Onr ⧸ Ideal.span {algebraMap 𝒪 Onr π}))
    (X₀ : FormalODModule r (Onr ⧸ Ideal.span {algebraMap 𝒪 Onr π})) (hX₀ : X₀.HasHeight 4)
    (θ₀ : RelativeGroupLaw.FormalCoordinates A₀.f 2) (hA₀ : A₀.IsFormalModuleVia coord X₀ θ₀)

    (ι : Zp2 r →+* Onr)
    (Φ : FormalODModule r (Onr ⧸ pIdeal r Onr))
    (hΦ : Φ.IsSpecial ((Ideal.Quotient.mk (pIdeal r Onr)).comp ι))
    (hΦ4 : Φ.HasHeight 4)
    (M : ModuliPackage.{0, 0} r Onr) (hM : M.IsZariskiSheaf)
    (η : ∀ (B : Type) [CommRing B] (ψ : Onr →+* B) (hB : IsNilpotent (r : B)),
      Rigidified r Φ B → M.obj B ψ hB)
    (hη : (∀ (B : Type) [CommRing B] [IsNoetherianRing B] (ψ : Onr →+* B) (hB : IsNilpotent (r : B))
          (t t' : Rigidified r Φ B), t.IsAdmissible ι ψ → t'.IsAdmissible ι ψ →
          (η B ψ hB t = η B ψ hB t' ↔ t.IsIsomorphic t')) ∧
      (∀ (B B' : Type) [CommRing B] [CommRing B'] [IsNoetherianRing B] [IsNoetherianRing B'] (ψ : Onr →+* B) (ψ' : Onr →+* B')
          (hB : IsNilpotent (r : B)) (hB' : IsNilpotent (r : B')) (f : B →+* B')
          (hf : f.comp ψ = ψ') (t : Rigidified r Φ B), t.IsAdmissible ι ψ →
          η B' ψ' hB' (t.map f) = M.map hB hB' f hf (η B ψ hB t)) ∧
      (∀ (B : Type) [CommRing B] [IsNoetherianRing B] (ψ : Onr →+* B) (hB : IsNilpotent (r : B)) (m : M.obj B ψ hB),
          ∃ (n : ℕ) (f : Fin n → B), Ideal.span (Set.range f) = ⊤ ∧
            ∀ (i : Fin n) (L : Type) [CommRing L] [IsNoetherianRing L] [Algebra B L] [IsLocalization.Away (f i) L]
              (hL : IsNilpotent (r : L)),
              ∃ t : Rigidified r Φ L, t.IsAdmissible ι ((algebraMap B L).comp ψ) ∧
                η L ((algebraMap B L).comp ψ) hL t =
                  M.map (ψ' := (algebraMap B L).comp ψ) hB hL (algebraMap B L) rfl m))
    (E₀ : Subring.centralizer (Set.range Φ.actEnd ∪ {Φ.varpiEnd}) →+* Matrix (Fin 2) (Fin 2) K₀)
    (hE₀ : Function.Injective E₀ ∧
      ∃ m : ℕ,
        (∀ A : Matrix (Fin 2) (Fin 2) 𝒪, ∃ e, E₀ e = (r : K₀) ^ m • A.map (algebraMap 𝒪 K₀)) ∧
        (∀ e, ∃ A : Matrix (Fin 2) (Fin 2) 𝒪, (r : K₀) ^ m • E₀ e = A.map (algebraMap 𝒪 K₀)))

    (κ : (Onr ⧸ Ideal.span {algebraMap 𝒪 Onr π}) →+* (Onr ⧸ pIdeal r Onr))
    (hκ : κ.comp (Ideal.Quotient.mk (Ideal.span {algebraMap 𝒪 Onr π})) = Ideal.Quotient.mk (pIdeal r Onr))
    (n₀ : ℕ) (β₀ : Series (Onr ⧸ pIdeal r Onr)) (hβ₀ : FormalODModule.IsIsogenyOfHeight Φ (X₀.map κ) β₀ (4 * n₀))

    (B : Type) [CommRing B] [IsNoetherianRing B] [Algebra 𝒪 B] (B' : Type) [CommRing B'] [IsNoetherianRing B'] [Algebra 𝒪 B']
    (φ : B →ₐ[𝒪] B') (ψ : Onr →ₐ[𝒪] B) (hB : IsNilpotent (algebraMap 𝒪 B π)) (hB' : IsNilpotent (algebraMap 𝒪 B' π))
    (hBr : IsNilpotent ((r : ℕ) : B)) (hBr' : IsNilpotent ((r : ℕ) : B'))
    (x : FakeEllipticCurve.RigidifiedCurve r π A₀ B ψ) (x' : FakeEllipticCurve.RigidifiedCurve r π A₀ B' (φ.comp ψ))
    (g : x'.1.A ⟶ x.1.A) (hg : FakeEllipticCurve.IsPullbackVia (φ : B →+* B') x.1 x'.1 g)
    (hρ : FakeEllipticCurve.Rigidification.IsPullbackVia φ g hg x.2 x'.2)
    (X : FormalODModule r B) (θ : RelativeGroupLaw.FormalCoordinates x.1.f 2) (hX : x.1.IsFormalModuleVia coord X θ)
    (j : ℕ) (t : Rigidified r Φ B) (hj : j ≤ 1) (htX : t.X = X)
    (htr : FakeEllipticCurve.Rigidification.IsRigTransport θ₀ κ β₀ x.2 θ j t) (hadm : t.IsAdmissible ι ((frobTwist Onr Fr (-(j : ℤ)) ψ : Onr →ₐ[𝒪] B) : Onr →+* B))
    :
    ∃ θ' : RelativeGroupLaw.FormalCoordinates x'.1.f 2,
      x'.1.IsFormalModuleVia coord (X.map (φ : B →+* B')) θ' ∧
      (∀ (B'' : Type) [CommRing B''] [Algebra B B''] [Algebra B' B''],
        algebraMap B B'' = (algebraMap B' B'').comp (φ : B →+* B') →
        ∀ (s : Fin 2 → B''), (∀ i, IsNilpotent (s i)) → (θ' B'' s).1 ≫ g = (θ B'' s).1) ∧
      (t.map (φ : B →+* B')).X = X.map (φ : B →+* B') ∧ (t.map (φ : B →+* B')).n = t.n ∧
      FakeEllipticCurve.Rigidification.IsRigTransport θ₀ κ β₀ x'.2 θ' j (t.map (φ : B →+* B')) ∧
      (t.map (φ : B →+* B')).IsAdmissible ι ((frobTwist Onr Fr (-(j : ℤ)) (φ.comp ψ) : Onr →ₐ[𝒪] B') : Onr →+* B') ∧
      η B' ((frobTwist Onr Fr (-(j : ℤ)) (φ.comp ψ) : Onr →ₐ[𝒪] B') : Onr →+* B') hBr' (t.map (φ : B →+* B')) =
        M.map hBr hBr' (φ : B →+* B') rfl (η B ((frobTwist Onr Fr (-(j : ℤ)) ψ : Onr →ₐ[𝒪] B) : Onr →+* B) hBr t) := by
  classical

  letI : Algebra B B' := (φ : B →+* B').toAlgebra
  have hφalg : algebraMap B B' = (φ : B →+* B') := rfl
  obtain ⟨θ', hθ', hθ'g⟩ := CerednikDrinfeld.QM.FakeEllipticCurve.IsPullbackVia.exists_isFormalModuleVia_map_and_comp_eq
    coord B B' x.1 x'.1 g hg X θ hX

  have hleg : ((frobTwist Onr Fr (-(j : ℤ)) (φ.comp ψ) : Onr →ₐ[𝒪] B') : Onr →+* B') =
      (φ : B →+* B').comp ((frobTwist Onr Fr (-(j : ℤ)) ψ : Onr →ₐ[𝒪] B) : Onr →+* B) := rfl
  refine ⟨θ', hθ', ?hrel, ?_, rfl, ?_, ?_, ?_⟩
  case hrel =>
    intro B'' _ _ _ halg s hs
    haveI : IsScalarTower B B' B'' := IsScalarTower.of_algebraMap_eq (fun b => by
      rw [halg, hφalg]; rfl)
    exact hθ'g B'' s hs
  · rw [CerednikDrinfeld.SpecialFormal.Rigidified.map_X, htX]
  ·
    obtain ⟨κB, σ, hκ1, hκ2, hrep, hρt⟩ := htr
    obtain ⟨ub, uA, hub, hubg, huA, huAg, hdd, hφφ⟩ := hρ

    have hπr : Ideal.span {algebraMap 𝒪 B' π} ≤ CerednikDrinfeld.SpecialFormal.pIdeal r B' := by
      rw [Ideal.span_le, Set.singleton_subset_iff, SetLike.mem_coe]
      have : π ∈ Ideal.span {((r : ℕ) : 𝒪)} := by rw [hunr]; exact Ideal.subset_span rfl
      obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.mp this
      rw [← hc, map_mul, map_natCast]
      exact Ideal.mul_mem_left _ _ (Ideal.subset_span rfl)
    let κB' : (B' ⧸ Ideal.span {algebraMap 𝒪 B' π}) →+* (B' ⧸ CerednikDrinfeld.SpecialFormal.pIdeal r B') :=
      Ideal.Quotient.factor hπr
    have hκB'mk : κB'.comp (Ideal.Quotient.mk _) = Ideal.Quotient.mk _ := Ideal.Quotient.factor_comp_mk hπr

    set φb : (B ⧸ Ideal.span {algebraMap 𝒪 B π}) →+* (B' ⧸ Ideal.span {algebraMap 𝒪 B' π}) :=
      Ideal.quotientMap (Ideal.span {algebraMap 𝒪 B' π}) (φ : B →+* B')
        (Ideal.span_le.mpr (Set.singleton_subset_iff.mpr (Ideal.mem_comap.mpr
          (by rw [show (φ : B →+* B') (algebraMap 𝒪 B π) = algebraMap 𝒪 B' π from φ.commutes π]
              exact Ideal.subset_span rfl)))) with hφb
    have hφbmk : φb.comp (Ideal.Quotient.mk _) = (Ideal.Quotient.mk _).comp (φ : B →+* B') := by
      rw [hφb]; exact Ideal.quotientMap_comp_mk _
    refine ⟨κB', σ.map φb, hκB'mk, ?_, ?_, ?_⟩
    ·
      apply Ideal.Quotient.ringHom_ext
      refine RingHom.ext fun z => ?_
      have h3 : κ (Ideal.Quotient.mk _ z) = Ideal.Quotient.mk _ z := congrArg (fun g => g z) hκ
      show κB' (FakeEllipticCurve.Rigidification.residueLeg π (φ.comp ψ) (Ideal.Quotient.mk _ z)) =
        CerednikDrinfeld.SpecialFormal.residueMap ((φ.comp ψ : Onr →ₐ[𝒪] B') : Onr →+* B') (κ (Ideal.Quotient.mk _ z))
      rw [h3]
      dsimp only [FakeEllipticCurve.Rigidification.residueLeg, CerednikDrinfeld.SpecialFormal.residueMap]
      rw [Ideal.quotientMap_mk, Ideal.quotientMap_mk]
      exact Ideal.Quotient.factor_mk hπr _
    ·
      intro B'' _ instQ' instB' instO h1 h2 J m hJ s hs PA hPAf hPAg
      letI instQ : Algebra (B ⧸ Ideal.span {algebraMap 𝒪 B π}) B'' :=
        ((algebraMap (B' ⧸ Ideal.span {algebraMap 𝒪 B' π}) B'').comp φb).toAlgebra
      letI instB : Algebra B B'' := ((algebraMap B' B'').comp (φ : B →+* B')).toAlgebra
      haveI : IsScalarTower B B' B'' := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
      have halgQ : algebraMap (B ⧸ Ideal.span {algebraMap 𝒪 B π}) B'' =
          (algebraMap (B' ⧸ Ideal.span {algebraMap 𝒪 B' π}) B'').comp φb := rfl

      have hrπ : ((r : ℕ) : B) ∈ Ideal.span {algebraMap 𝒪 B π} := by
        have : ((r : ℕ) : 𝒪) ∈ Ideal.span {π} := by rw [← hunr]; exact Ideal.subset_span rfl
        obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.mp this
        have := congrArg (algebraMap 𝒪 B) hc
        rw [map_mul, map_natCast] at this
        rw [← this]
        exact Ideal.mul_mem_left _ _ (Ideal.subset_span rfl)
      have hκinj : ∀ c, κB c = 0 → c = 0 := by
        intro c hc
        obtain ⟨c₀, rfl⟩ := Ideal.Quotient.mk_surjective c
        have h0 : Ideal.Quotient.mk (CerednikDrinfeld.SpecialFormal.pIdeal r B) c₀ = 0 := by
          rw [← hc]; exact (congrArg (fun g => g c₀) hκ1).symm
        rw [Ideal.Quotient.eq_zero_iff_mem] at h0 ⊢
        obtain ⟨e, he⟩ := Ideal.mem_span_singleton'.mp h0
        rw [← he]
        exact Ideal.mul_mem_left _ _ hrπ
      have hβ₀c : ∀ i, MvPowerSeries.constantCoeff (β₀ i) = 0 := hβ₀.1.constantCoeff
      have hinner : ∀ i, MvPowerSeries.constantCoeff
          (((CerednikDrinfeld.SpecialFormal.Series.map (CerednikDrinfeld.SpecialFormal.residueMap (ψ : Onr →+* B)) β₀).comp
            (fun i => (MvPowerSeries.X i : MvPowerSeries (Fin 2) (B ⧸ CerednikDrinfeld.SpecialFormal.pIdeal r B)) ^ (r ^ j))) i) = 0 := by
        refine CerednikDrinfeld.SpecialFormal.Series.constantCoeff_comp (fun i => ?_) (fun i => ?_)
        · show MvPowerSeries.constantCoeff (MvPowerSeries.map _ (β₀ i)) = 0
          rw [MvPowerSeries.constantCoeff_map, hβ₀c, map_zero]
        · simp only [map_pow, MvPowerSeries.constantCoeff_X, zero_pow (pow_pos (Fact.out : r.Prime).pos j).ne']
      have hσc : ∀ i, MvPowerSeries.constantCoeff (σ i) = 0 := by
        intro i
        apply hκinj
        have h0 := hadm.constantCoeff_ρ i
        rw [hρt] at h0
        change MvPowerSeries.constantCoeff (MvPowerSeries.subst _ ((CerednikDrinfeld.SpecialFormal.Series.map κB σ) i)) = 0 at h0
        rw [XCSol.constantCoeff_subst_of_constantCoeff_eq_zero hinner] at h0
        rwa [show (CerednikDrinfeld.SpecialFormal.Series.map κB σ) i = MvPowerSeries.map κB (σ i) from rfl,
          MvPowerSeries.constantCoeff_map] at h0

      have hs₁J : ∀ i, MvFormalGroup.nilEval m (σ i) s ∈ J :=
        (MvFormalGroup.nilEval_subst_of_mem J m hJ s hs σ hσc (MvPowerSeries.X 0)).1
      have hs₁nil : ∀ i, IsNilpotent (MvFormalGroup.nilEval m (σ i) s) := by
        intro i
        refine ⟨m + 1, ?_⟩
        have := Ideal.pow_mem_pow (hs₁J i) (m + 1)
        rwa [hJ, Ideal.mem_bot] at this
      have hev : (fun i => MvFormalGroup.nilEval m ((CerednikDrinfeld.SpecialFormal.Series.map φb σ) i) s) =
          fun i => MvFormalGroup.nilEval m (σ i) s := by
        funext i
        exact XCSol.nilEval_map φb halgQ m (σ i) s
      rw [hev]

      obtain ⟨hpbA, -, hactA, -⟩ := huA
      obtain ⟨hpbb, -, hactb, -⟩ := hub
      have h1' : algebraMap B B'' = (algebraMap (B ⧸ Ideal.span {algebraMap 𝒪 B π}) B'').comp (Ideal.Quotient.mk _) := by
        rw [halgQ, RingHom.comp_assoc, hφbmk, ← RingHom.comp_assoc, ← h1]; rfl
      have hlegc : FakeEllipticCurve.Rigidification.residueLeg π (φ.comp ψ) =
          φb.comp (FakeEllipticCurve.Rigidification.residueLeg π ψ) := by
        apply Ideal.Quotient.ringHom_ext
        refine RingHom.ext fun z => ?_
        show FakeEllipticCurve.Rigidification.residueLeg π (φ.comp ψ) (Ideal.Quotient.mk _ z) =
          φb (FakeEllipticCurve.Rigidification.residueLeg π ψ (Ideal.Quotient.mk _ z))
        dsimp only [FakeEllipticCurve.Rigidification.residueLeg]
        rw [Ideal.quotientMap_mk, Ideal.quotientMap_mk, hφb, Ideal.quotientMap_mk]
        rfl
      have h2' : algebraMap (Onr ⧸ Ideal.span {algebraMap 𝒪 Onr π}) B'' =
          (algebraMap (B ⧸ Ideal.span {algebraMap 𝒪 B π}) B'').comp (FakeEllipticCurve.Rigidification.residueLeg π ψ) := by
        rw [h2, hlegc, halgQ, RingHom.comp_assoc]
      have hf' : (PA ≫ uA) ≫ x.2.Ab.f =
          Spec.map (CommRingCat.ofHom (algebraMap (B ⧸ Ideal.span {algebraMap 𝒪 B π}) B'')) := by
        rw [Category.assoc, hpbA.w, ← Category.assoc, hPAf, halgQ, CommRingCat.ofHom_comp, Spec.map_comp]
      have hg' : (PA ≫ uA) ≫ x.2.gA = (θ₀ B'' s).1 := by rw [Category.assoc, huAg, hPAg]
      have R := hrep B'' h1' h2' J m hJ s hs (PA ≫ uA) hf' hg'

      obtain ⟨hφo', hφ'o', hmφ', -, -, -, hdeg'⟩ := x'.2.isIsogenyPair
      obtain ⟨-, -, -, -, -, -, hdeg⟩ := x.2.isIsogenyPair
      have h1Λ : (1 : ℍ[ℚ, a, b]) ∈ Λ := by simpa using hΛℤ 1
      have hdΛ' : (((r ^ x'.2.d : ℕ) : ℚ) : ℍ[ℚ, a, b]) ∈ Λ := by
        have := hΛℤ ((r ^ x'.2.d : ℕ) : ℤ); rwa [Int.cast_natCast] at this
      have hdΛ : (((r ^ x.2.d : ℕ) : ℚ) : ℍ[ℚ, a, b]) ∈ Λ := by
        have := hΛℤ ((r ^ x.2.d : ℕ) : ℤ); rwa [Int.cast_natCast] at this
      have hfs := CerednikDrinfeld.QM.FakeEllipticCurve.isFinite_flat_surjective_of_mapPt_mapPt_eq_nsmulPt
        x'.2.Eb x'.2.Ab x'.2.φ hφo' hmφ' x'.2.φ' hφ'o' (r ^ x'.2.d) (pow_pos (Fact.out : r.Prime).pos _)
        (fun t P => by
          rw [← CerednikDrinfeld.QM.FakeEllipticCurve.pushPt_act_natCast_eq_nsmulPt x'.2.Eb h1Λ (r ^ x'.2.d) hdΛ' t P]
          apply Subtype.ext
          simp only [mapPt_coe, pushPt, Category.assoc]
          rw [(hdeg' hdΛ').1])
        (fun t Q => by
          rw [← CerednikDrinfeld.QM.FakeEllipticCurve.pushPt_act_natCast_eq_nsmulPt x'.2.Ab h1Λ (r ^ x'.2.d) hdΛ' t Q]
          apply Subtype.ext
          simp only [mapPt_coe, pushPt, Category.assoc]
          rw [(hdeg' hdΛ').2])
      haveI : Flat x'.2.φ := hfs.2.1
      haveI : Surjective x'.2.φ := hfs.2.2.2
      haveI : Epi x'.2.φ := AlgebraicGeometry.Flat.epi_of_flat_of_surjective _
      have KEY : x'.2.φ' ≫ ub = uA ≫ x.2.φ' := by
        rw [← cancel_epi x'.2.φ, ← Category.assoc, (hdeg' hdΛ').1, hactb, ← Category.assoc, ← hφφ, Category.assoc]
        congr 1
        have e : x.2.Eb.act ⟨(((r ^ x'.2.d : ℕ) : ℚ) : ℍ[ℚ, a, b]), hdΛ'⟩ = x.2.Eb.act ⟨(((r ^ x.2.d : ℕ) : ℚ) : ℍ[ℚ, a, b]), hdΛ⟩ := by
          congr 1; exact Subtype.ext (congrArg (fun n : ℕ => (((r ^ n : ℕ) : ℚ) : ℍ[ℚ, a, b])) hdd)
        rw [e]
        exact ((hdeg hdΛ).1).symm

      obtain ⟨hpbg, -, -, -⟩ := hg
      obtain ⟨hpbe, -, -, -⟩ := x'.2.isPullback_Eb
      apply hpbg.hom_ext
      · rw [Category.assoc, Category.assoc, ← hubg, ← Category.assoc x'.2.φ', KEY, hθ'g B'' _ hs₁nil, ← R]
        simp only [Category.assoc]
      · rw [(θ' B'' _).2, Category.assoc, Category.assoc, hpbe.w, ← Category.assoc x'.2.φ', hφ'o', ← Category.assoc, hPAf,
          ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← h1]
    ·
      have hβ₀c : ∀ i, MvPowerSeries.constantCoeff (β₀ i) = 0 := hβ₀.1.constantCoeff
      have hFrc : ∀ i, MvPowerSeries.constantCoeff
          ((fun i => (MvPowerSeries.X i : MvPowerSeries (Fin 2) (B ⧸ CerednikDrinfeld.SpecialFormal.pIdeal r B)) ^ (r ^ j)) i) = 0 := by
        intro i
        simp only [map_pow, MvPowerSeries.constantCoeff_X, zero_pow (pow_pos (Fact.out : r.Prime).pos j).ne']
      have hinner : ∀ i, MvPowerSeries.constantCoeff
          (((CerednikDrinfeld.SpecialFormal.Series.map (CerednikDrinfeld.SpecialFormal.residueMap (ψ : Onr →+* B)) β₀).comp
            (fun i => (MvPowerSeries.X i : MvPowerSeries (Fin 2) (B ⧸ CerednikDrinfeld.SpecialFormal.pIdeal r B)) ^ (r ^ j))) i) = 0 := by
        refine CerednikDrinfeld.SpecialFormal.Series.constantCoeff_comp (fun i => ?_) hFrc
        show MvPowerSeries.constantCoeff (MvPowerSeries.map _ (β₀ i)) = 0
        rw [MvPowerSeries.constantCoeff_map, hβ₀c, map_zero]
      rw [CerednikDrinfeld.SpecialFormal.Rigidified.map_ρ, hρt,
        CerednikDrinfeld.SpecialFormal.Series.map_comp _ _ _ hinner,
        CerednikDrinfeld.SpecialFormal.Series.map_comp _ _ _ hFrc,
        CerednikDrinfeld.SpecialFormal.Series.map_map, CerednikDrinfeld.SpecialFormal.Series.map_map,
        CerednikDrinfeld.SpecialFormal.Series.map_map]
      have hsq : (CerednikDrinfeld.SpecialFormal.reduceMap (p := r) (φ : B →+* B')).comp κB = κB'.comp φb := by
        apply Ideal.Quotient.ringHom_ext
        rw [RingHom.comp_assoc, hκ1, RingHom.comp_assoc, hφbmk, ← RingHom.comp_assoc, hκB'mk]
        rfl
      have hres : (CerednikDrinfeld.SpecialFormal.reduceMap (p := r) (φ : B →+* B')).comp
          (CerednikDrinfeld.SpecialFormal.residueMap (ψ : Onr →+* B)) =
          CerednikDrinfeld.SpecialFormal.residueMap (((φ.comp ψ : Onr →ₐ[𝒪] B')) : Onr →+* B') :=
        (CerednikDrinfeld.SpecialFormal.residueMap_comp _ _).symm
      have hFr : CerednikDrinfeld.SpecialFormal.Series.map (CerednikDrinfeld.SpecialFormal.reduceMap (p := r) (φ : B →+* B'))
          (fun i => (MvPowerSeries.X i : MvPowerSeries (Fin 2) (B ⧸ CerednikDrinfeld.SpecialFormal.pIdeal r B)) ^ (r ^ j)) =
          (fun i => (MvPowerSeries.X i : MvPowerSeries (Fin 2) (B' ⧸ CerednikDrinfeld.SpecialFormal.pIdeal r B')) ^ (r ^ j)) := by
        funext i
        show MvPowerSeries.map _ _ = _
        rw [map_pow, MvPowerSeries.map_X]
      rw [hsq, hres, hFr]
  ·
    rw [hleg]
    exact CerednikDrinfeld.SpecialFormal.Rigidified.IsAdmissible.map_ringHom ι _ (φ : B →+* B') t hadm
  ·
    exact hη.2.1 B B' _ _ hBr hBr' (φ : B →+* B') rfl t hadm

namespace E3Sol

open MvPowerSeries

variable {p : ℕ} [Fact p.Prime] {O : Type} [CommRing O] {Φ : FormalODModule p (O ⧸ pIdeal p O)}

theorem conn_of_isLocalRing (B : Type) [CommRing B] [IsLocalRing B] (e : B) (he : IsIdempotentElem e) : e = 0 ∨ e = 1 := by
  rcases IsLocalRing.isUnit_or_isUnit_one_sub_self e with h | h
  · right
    obtain ⟨w, hw⟩ := h
    have h2 : e * e = e := he
    have : (w : B) * (↑w⁻¹ : B) = 1 := w.mul_inv
    calc e = e * ((w : B) * (↑w⁻¹ : B)) := by rw [this, mul_one]
      _ = (e * e) * (↑w⁻¹ : B) := by rw [hw, mul_assoc]
      _ = e * (↑w⁻¹ : B) := by rw [h2]
      _ = 1 := by rw [← hw]; exact w.mul_inv
  · left
    obtain ⟨w, hw⟩ := h
    have h2 : (1 - e) * e = 0 := by rw [sub_mul, one_mul, he]; exact sub_self e
    calc e = ((↑w⁻¹ : B) * (w : B)) * e := by rw [w.inv_mul, one_mul]
      _ = (↑w⁻¹ : B) * ((1 - e) * e) := by rw [hw, mul_assoc]
      _ = 0 := by rw [h2, mul_zero]

theorem isIso_map {R S : Type} [CommRing R] [CommRing S] (f : R →+* S) {X Y : FormalODModule p R}
    (T : FormalODModule.Hom X Y) (hT : T.IsIso) : (T.map f).IsIso := by
  obtain ⟨g, hg1, hg2⟩ := hT
  refine ⟨g.map f, ?_, ?_⟩
  · apply FormalODModule.Hom.ext
    have h := congrArg (fun (k : FormalODModule.Hom X X) => k.toSeries.map f) hg1
    simp only [FormalODModule.Hom.comp, FormalODModule.Hom.id] at h
    rw [Series.map_comp f _ _ T.isODHom.constantCoeff, Series.map_id] at h
    exact h
  · apply FormalODModule.Hom.ext
    have h := congrArg (fun (k : FormalODModule.Hom Y Y) => k.toSeries.map f) hg2
    simp only [FormalODModule.Hom.comp, FormalODModule.Hom.id] at h
    rw [Series.map_comp f _ _ g.isODHom.constantCoeff, Series.map_id] at h
    exact h

theorem compat_map {R S : Type} [CommRing R] [CommRing S] (f : R →+* S) (t t' : Rigidified p Φ R) (u : Series R)
    (hu0 : ∀ i, constantCoeff (u i) = 0) (hρ0 : ∀ i, constantCoeff (t.ρ i) = 0) (hρ0' : ∀ i, constantCoeff (t'.ρ i) = 0)
    (m : ℕ)
    (hc : (t'.Xbar.act ((p : Zp2 p) ^ (m + t'.n))).comp ((u.map (Ideal.Quotient.mk (pIdeal p R))).comp t.ρ) =
      (t'.Xbar.act ((p : Zp2 p) ^ (m + t.n))).comp t'.ρ) :
    ((t'.map f).Xbar.act ((p : Zp2 p) ^ (m + (t'.map f).n))).comp
        (((u.map f).map (Ideal.Quotient.mk (pIdeal p S))).comp (t.map f).ρ) =
      ((t'.map f).Xbar.act ((p : Zp2 p) ^ (m + (t.map f).n))).comp (t'.map f).ρ := by
  have key := congrArg (Series.map (reduceMap (p := p) f)) hc
  have hu0' : ∀ i, constantCoeff ((u.map (Ideal.Quotient.mk (pIdeal p R))) i) = 0 := fun i => by
    show constantCoeff (MvPowerSeries.map _ (u i)) = 0
    rw [MvPowerSeries.constantCoeff_map, hu0 i, map_zero]
  have hin : ∀ i, constantCoeff (((u.map (Ideal.Quotient.mk (pIdeal p R))).comp t.ρ) i) = 0 :=
    Series.constantCoeff_comp hu0' hρ0
  rw [Series.map_comp _ _ _ hin, Series.map_comp _ _ _ hρ0, Series.map_comp _ _ _ hρ0'] at key

  have hmk : (reduceMap (p := p) f).comp (Ideal.Quotient.mk (pIdeal p R)) = (Ideal.Quotient.mk (pIdeal p S)).comp f :=
    RingHom.ext fun _ => rfl
  have hX : t'.Xbar.map (reduceMap (p := p) f) = (t'.map f).Xbar := by
    show (t'.X.map _).map _ = ((t'.X.map f).map _)
    rw [FormalODModule.map_map, FormalODModule.map_map, hmk]
  have hact : ∀ c : Zp2 p, (t'.Xbar.act c).map (reduceMap (p := p) f) = ((t'.map f).Xbar).act c := fun c => by
    rw [← hX]
    simp only [FormalODModule.map_act]
  have hu : (u.map (Ideal.Quotient.mk (pIdeal p R))).map (reduceMap (p := p) f) =
      (u.map f).map (Ideal.Quotient.mk (pIdeal p S)) := by
    rw [Series.map_map, Series.map_map, hmk]
  rw [hact, hact, hu] at key
  simpa only [Rigidified.map_ρ, Rigidified.map_n] using key

end E3Sol

open E3Sol in
theorem solution
    {r rbar N : ℕ} [Fact r.Prime] [Fact rbar.Prime] [NeZero N] (hrr : rbar ≠ r) (hrN : ¬ r ∣ N)

    (𝒪 : Type) [CommRing 𝒪] [IsDomain 𝒪] [CharZero 𝒪] (hdvr : IsDiscreteValuationRing 𝒪)
    (π : 𝒪) (hπ : Irreducible π) (hcomplete : IsAdicComplete (Ideal.span {π}) 𝒪)
    (hres : Nat.card (𝒪 ⧸ Ideal.span {π}) = r) (hunr : Ideal.span {((r : ℕ) : 𝒪)} = Ideal.span {π})
    (K₀ : Type) [Field K₀] [CharZero K₀] [Algebra 𝒪 K₀] [IsFractionRing 𝒪 K₀]

    (Onr : Type) [CommRing Onr] [IsDomain Onr] [CharZero Onr] [Algebra 𝒪 Onr] (Fr : Onr ≃ₐ[𝒪] Onr)
    (hOnr_complete : IsAdicComplete (Ideal.span {algebraMap 𝒪 Onr π}) Onr)
    (hOnr_max : (Ideal.span {algebraMap 𝒪 Onr π}).IsMaximal)
    (hOnr_alg : ∀ x : Onr, ∃ p : Polynomial 𝒪, p.Monic ∧ Polynomial.aeval x p ∈ Ideal.span {algebraMap 𝒪 Onr π})
    (hOnr_closed : ∀ p : Polynomial Onr, p.Monic → 0 < p.natDegree → ∃ x : Onr, Polynomial.eval x p ∈ Ideal.span {algebraMap 𝒪 Onr π})
    (hFr : ∀ x : Onr, Fr x - x ^ r ∈ Ideal.span {algebraMap 𝒪 Onr π})

    {a b : ℚ} (hB : IsIndefiniteRamifiedExactlyAt a b r rbar)
    (Λ : Submodule ℤ ℍ[ℚ, a, b]) (hΛ : IsMaximalOrder Λ) (hΛℤ : ∀ m : ℤ, ((m : ℚ) : ℍ[ℚ, a, b]) ∈ Λ)
    (coord : ↥Λ → Zp2 r × Zp2 r) (hcoord : IsOrderCoord Λ r coord)
    (A₀ : FakeEllipticCurve Λ N (Onr ⧸ Ideal.span {algebraMap 𝒪 Onr π}))
    (X₀ : FormalODModule r (Onr ⧸ Ideal.span {algebraMap 𝒪 Onr π})) (hX₀ : X₀.HasHeight 4)
    (θ₀ : RelativeGroupLaw.FormalCoordinates A₀.f 2) (hA₀ : A₀.IsFormalModuleVia coord X₀ θ₀)

    (ι : Zp2 r →+* Onr)
    (Φ : FormalODModule r (Onr ⧸ pIdeal r Onr))
    (hΦ : Φ.IsSpecial ((Ideal.Quotient.mk (pIdeal r Onr)).comp ι))
    (hΦ4 : Φ.HasHeight 4)
    (M : ModuliPackage.{0, 0} r Onr) (hM : M.IsZariskiSheaf)
    (η : ∀ (B : Type) [CommRing B] (ψ : Onr →+* B) (hB : IsNilpotent (r : B)),
      Rigidified r Φ B → M.obj B ψ hB)
    (hη : (∀ (B : Type) [CommRing B] [IsNoetherianRing B] (ψ : Onr →+* B) (hB : IsNilpotent (r : B))
          (t t' : Rigidified r Φ B), t.IsAdmissible ι ψ → t'.IsAdmissible ι ψ →
          (η B ψ hB t = η B ψ hB t' ↔ t.IsIsomorphic t')) ∧
      (∀ (B B' : Type) [CommRing B] [CommRing B'] [IsNoetherianRing B] [IsNoetherianRing B'] (ψ : Onr →+* B) (ψ' : Onr →+* B')
          (hB : IsNilpotent (r : B)) (hB' : IsNilpotent (r : B')) (f : B →+* B')
          (hf : f.comp ψ = ψ') (t : Rigidified r Φ B), t.IsAdmissible ι ψ →
          η B' ψ' hB' (t.map f) = M.map hB hB' f hf (η B ψ hB t)) ∧
      (∀ (B : Type) [CommRing B] [IsNoetherianRing B] (ψ : Onr →+* B) (hB : IsNilpotent (r : B)) (m : M.obj B ψ hB),
          ∃ (n : ℕ) (f : Fin n → B), Ideal.span (Set.range f) = ⊤ ∧
            ∀ (i : Fin n) (L : Type) [CommRing L] [IsNoetherianRing L] [Algebra B L] [IsLocalization.Away (f i) L]
              (hL : IsNilpotent (r : L)),
              ∃ t : Rigidified r Φ L, t.IsAdmissible ι ((algebraMap B L).comp ψ) ∧
                η L ((algebraMap B L).comp ψ) hL t =
                  M.map (ψ' := (algebraMap B L).comp ψ) hB hL (algebraMap B L) rfl m))
    (E₀ : Subring.centralizer (Set.range Φ.actEnd ∪ {Φ.varpiEnd}) →+* Matrix (Fin 2) (Fin 2) K₀)
    (hE₀ : Function.Injective E₀ ∧
      ∃ m : ℕ,
        (∀ A : Matrix (Fin 2) (Fin 2) 𝒪, ∃ e, E₀ e = (r : K₀) ^ m • A.map (algebraMap 𝒪 K₀)) ∧
        (∀ e, ∃ A : Matrix (Fin 2) (Fin 2) 𝒪, (r : K₀) ^ m • E₀ e = A.map (algebraMap 𝒪 K₀)))

    (κ : (Onr ⧸ Ideal.span {algebraMap 𝒪 Onr π}) →+* (Onr ⧸ pIdeal r Onr))
    (hκ : κ.comp (Ideal.Quotient.mk (Ideal.span {algebraMap 𝒪 Onr π})) = Ideal.Quotient.mk (pIdeal r Onr))
    (n₀ : ℕ) (β₀ : Series (Onr ⧸ pIdeal r Onr)) (hβ₀ : FormalODModule.IsIsogenyOfHeight Φ (X₀.map κ) β₀ (4 * n₀))

    (Ξ : ∀ (B : Type) [CommRing B] [IsNoetherianRing B] [Algebra 𝒪 B] (ψ : Onr →ₐ[𝒪] B),
        IsNilpotent (algebraMap 𝒪 B π) → FakeEllipticCurve.RigidifiedCurve r π A₀ B ψ → ModuliPackage.GPoint 𝒪 M B)

    (hΞleg :
      (∀ (B : Type) [CommRing B] [IsNoetherianRing B] [Algebra 𝒪 B] (ψ : Onr →ₐ[𝒪] B) (hB : IsNilpotent (algebraMap 𝒪 B π))
          (hconn : ∀ e : B, IsIdempotentElem e → e = 0 ∨ e = 1)
          (x : FakeEllipticCurve.RigidifiedCurve r π A₀ B ψ), ∃ k : ℤ, (Ξ B ψ hB x).ψ = frobTwist Onr Fr k ψ))

    (hΞnat :
      (∀ (B : Type) [CommRing B] [IsNoetherianRing B] [Algebra 𝒪 B] (B' : Type) [CommRing B'] [IsNoetherianRing B'] [Algebra 𝒪 B']
          (φ : B →ₐ[𝒪] B') (ψ : Onr →ₐ[𝒪] B) (hB : IsNilpotent (algebraMap 𝒪 B π)) (hB' : IsNilpotent (algebraMap 𝒪 B' π))
          (x : FakeEllipticCurve.RigidifiedCurve r π A₀ B ψ) (x' : FakeEllipticCurve.RigidifiedCurve r π A₀ B' (φ.comp ψ))
          (g : x'.1.A ⟶ x.1.A) (hg : FakeEllipticCurve.IsPullbackVia (φ : B →+* B') x.1 x'.1 g),
          FakeEllipticCurve.Rigidification.IsPullbackVia φ g hg x.2 x'.2 → Ξ B' (φ.comp ψ) hB' x' = (Ξ B ψ hB x).map φ))

    (hΞiso :
      (∀ (B : Type) [CommRing B] [IsNoetherianRing B] [Algebra 𝒪 B] (ψ : Onr →ₐ[𝒪] B) (hB : IsNilpotent (algebraMap 𝒪 B π))
          (x x' : FakeEllipticCurve.RigidifiedCurve r π A₀ B ψ) (i : x.1.A ≅ x'.1.A) (hi : i.hom ≫ x'.1.f = x.1.f),
          FakeEllipticCurve.IsoVia x.1 x'.1 i hi →
          (∃ (ib : x.2.Eb.A ⟶ x'.2.Eb.A) (_ : ib ≫ x'.2.gb = x.2.gb ≫ i.hom) (_ : ib ≫ x'.2.Eb.f = x.2.Eb.f)
            (uA : x'.2.Ab.A ⟶ x.2.Ab.A) (_ : FakeEllipticCurve.IsPullbackVia (RingHom.id _) x.2.Ab x'.2.Ab uA) (_ : uA ≫ x.2.gA = x'.2.gA)
            (i₁ j₁ : ℕ),
            ib ≫ x'.2.φ ≫ uA ≫ x.2.Ab.act ⟨(((r ^ i₁ : ℕ) : ℤ) : ℚ), hΛℤ _⟩ = x.2.φ ≫ x.2.Ab.act ⟨(((r ^ j₁ : ℕ) : ℤ) : ℚ), hΛℤ _⟩) →
            Ξ B ψ hB x = Ξ B ψ hB x'))

    (hΞdef :
      (∀ (B : Type) [CommRing B] [IsNoetherianRing B] [Algebra 𝒪 B] (ψ : Onr →ₐ[𝒪] B) (hB : IsNilpotent (algebraMap 𝒪 B π))
          (hconn : ∀ e : B, IsIdempotentElem e → e = 0 ∨ e = 1)
          (hBr : IsNilpotent ((r : ℕ) : B))
          (x : FakeEllipticCurve.RigidifiedCurve r π A₀ B ψ) (X : FormalODModule r B) (θ : RelativeGroupLaw.FormalCoordinates x.1.f 2),
          x.1.IsFormalModuleVia coord X θ →
          ∃ (j : ℕ) (t : Rigidified r Φ B), j ≤ 1 ∧ t.X = X ∧
            FakeEllipticCurve.Rigidification.IsRigTransport θ₀ κ β₀ x.2 θ j t ∧
            t.IsAdmissible ι ((frobTwist Onr Fr (-(j : ℤ)) ψ : Onr →ₐ[𝒪] B) : Onr →+* B) ∧
            Ξ B ψ hB x = ⟨frobTwist Onr Fr (-(j : ℤ)) ψ, hBr, η B ((frobTwist Onr Fr (-(j : ℤ)) ψ : Onr →ₐ[𝒪] B) : Onr →+* B) hBr t⟩))

    (A : Type) [CommRing A] [IsArtinianRing A] [IsLocalRing A] [Algebra 𝒪 A] (hA : IsNilpotent (algebraMap 𝒪 A π))
    (κ : Type) [Field κ] [IsAlgClosed κ] [Algebra 𝒪 κ] (hκ : IsNilpotent (algebraMap 𝒪 κ π))
    (qκ : A →ₐ[𝒪] κ) (hqκ : Function.Surjective qκ) (hker : RingHom.ker (qκ : A →+* κ) = IsLocalRing.maximalIdeal A)
    (ψ : Onr →ₐ[𝒪] A)
    (hAr : IsNilpotent ((r : ℕ) : A))

    (x x' : FakeEllipticCurve.RigidifiedCurve r π A₀ A ψ)
    (X X' : FormalODModule r A)
    (θ : RelativeGroupLaw.FormalCoordinates x.1.f 2) (θ' : RelativeGroupLaw.FormalCoordinates x'.1.f 2)
    (hX : x.1.IsFormalModuleVia coord X θ) (hX' : x'.1.IsFormalModuleVia coord X' θ')

    (x₀ x₀' : FakeEllipticCurve.RigidifiedCurve r π A₀ κ (qκ.comp ψ))
    (g : x₀.1.A ⟶ x.1.A) (hg : FakeEllipticCurve.IsPullbackVia (qκ : A →+* κ) x.1 x₀.1 g)
    (hρ : FakeEllipticCurve.Rigidification.IsPullbackVia qκ g hg x.2 x₀.2)
    (g' : x₀'.1.A ⟶ x'.1.A) (hg' : FakeEllipticCurve.IsPullbackVia (qκ : A →+* κ) x'.1 x₀'.1 g')
    (hρ' : FakeEllipticCurve.Rigidification.IsPullbackVia qκ g' hg' x'.2 x₀'.2)

    (hΞ : Ξ A ψ hA x = Ξ A ψ hA x') :
    ∃ (e₀ : x₀.1.A ≅ x₀'.1.A) (he₀ : e₀.hom ≫ x₀'.1.f = x₀.1.f) (he₀V : FakeEllipticCurve.IsoVia x₀.1 x₀'.1 e₀ he₀)
    (ib₀ : x₀.2.Eb.A ⟶ x₀'.2.Eb.A) (hib₀ : ib₀ ≫ x₀'.2.gb = x₀.2.gb ≫ e₀.hom) (hib₀f : ib₀ ≫ x₀'.2.Eb.f = x₀.2.Eb.f)
    (uA₀ : x₀'.2.Ab.A ⟶ x₀.2.Ab.A) (huA₀ : FakeEllipticCurve.IsPullbackVia (RingHom.id _) x₀.2.Ab x₀'.2.Ab uA₀)
    (huA₀g : uA₀ ≫ x₀.2.gA = x₀'.2.gA) (i₀ j₀ : ℕ)
    (hcorr₀ : ib₀ ≫ x₀'.2.φ ≫ uA₀ ≫ x₀.2.Ab.act ⟨(((r ^ i₀ : ℕ) : ℤ) : ℚ), hΛℤ _⟩ =
      x₀.2.φ ≫ x₀.2.Ab.act ⟨(((r ^ j₀ : ℕ) : ℤ) : ℚ), hΛℤ _⟩)
      (T : FormalODModule.Hom X X') (hT : T.IsIso),
      ∀ (B'' : Type) [CommRing B''] [Algebra A B''] [Algebra κ B''],
      algebraMap A B'' = (algebraMap κ B'').comp (qκ : A →+* κ) →
      ∀ (J : Ideal B'') (n : ℕ), J ^ (n + 1) = ⊥ → ∀ (s : Fin 2 → B''), (∀ i, s i ∈ J) →
      ∀ p₀ : SchemeHomOver (Scheme.specOver (𝒪 := κ) B'') x₀.1.f, p₀.1 ≫ g = (θ B'' s).1 →
        p₀.1 ≫ e₀.hom ≫ g' = (θ' B'' (fun i => MvFormalGroup.nilEval n (T.toSeries i) s)).1 := by
  classical

  haveI : IsNoetherianRing A := inferInstance
  have hconnA : ∀ e : A, IsIdempotentElem e → e = 0 ∨ e = 1 := conn_of_isLocalRing A
  have hκr : IsNilpotent ((r : ℕ) : κ) := by
    have h := hAr.map (qκ : A →+* κ)
    rwa [map_natCast] at h

  obtain ⟨j, t, hj, htX, ht, hta, hΞx⟩ := hΞdef A ψ hA hconnA hAr x X θ hX
  obtain ⟨j', t', hj', ht'X, ht', ht'a, hΞx'⟩ := hΞdef A ψ hA hconnA hAr x' X' θ' hX'
  have hΞΞ := hΞx.symm.trans (hΞ.trans hΞx')

  have hlegs : frobTwist Onr Fr (-(j : ℤ)) ψ = frobTwist Onr Fr (-(j' : ℤ)) ψ := congrArg ModuliPackage.GPoint.ψ hΞΞ
  have hjj : (-(j : ℤ)) = -(j' : ℤ) :=
    CerednikDrinfeld.FormalOmega.eq_of_frobTwist_eq_frobTwist_of_isNilpotent_of_nontrivial π Onr Fr hOnr_closed hFr A hA ψ
      _ _ hlegs
  obtain rfl : j = j' := by omega

  have hpt : η A ((frobTwist Onr Fr (-(j : ℤ)) ψ : Onr →ₐ[𝒪] A) : Onr →+* A) hAr t =
      η A ((frobTwist Onr Fr (-(j : ℤ)) ψ : Onr →ₐ[𝒪] A) : Onr →+* A) hAr t' := by
    have h := hΞΞ
    simp only [ModuliPackage.GPoint.mk.injEq, heq_eq_eq, true_and] at h
    exact h
  have hiso : t.IsIsomorphic t' :=
    (hη.1 A ((frobTwist Onr Fr (-(j : ℤ)) ψ : Onr →ₐ[𝒪] A) : Onr →+* A) hAr t t' hta ht'a).mp hpt
  obtain ⟨u, v, m, hu, hv, hvu, huv, hc⟩ := hiso
  subst htX ht'X
  let T : FormalODModule.Hom t.X t'.X := ⟨u, hu⟩
  have hT : T.IsIso :=
    ⟨⟨v, hv⟩, FormalODModule.Hom.ext hvu, FormalODModule.Hom.ext huv⟩

  obtain ⟨θE, hθE, hrelE, -, -, htrE, htaE, -⟩ := xc_with_rel hrr hrN 𝒪 hdvr π hπ hcomplete hres hunr K₀ Onr Fr hOnr_complete hOnr_max hOnr_alg hOnr_closed hFr hB Λ hΛ hΛℤ coord hcoord A₀ X₀ hX₀ θ₀ hA₀ ι Φ hΦ hΦ4 M hM η hη E₀ hE₀ _ (by assumption) n₀ β₀ hβ₀
    A κ qκ ψ hA hκ hAr hκr x x₀ g hg hρ t.X θ hX j t hj rfl ht hta
  obtain ⟨θE', hθE', hrelE', -, -, htrE', htaE', -⟩ := xc_with_rel hrr hrN 𝒪 hdvr π hπ hcomplete hres hunr K₀ Onr Fr hOnr_complete hOnr_max hOnr_alg hOnr_closed hFr hB Λ hΛ hΛℤ coord hcoord A₀ X₀ hX₀ θ₀ hA₀ ι Φ hΦ hΦ4 M hM η hη E₀ hE₀ _ (by assumption) n₀ β₀ hβ₀
    A κ qκ ψ hA hκ hAr hκr x' x₀' g' hg' hρ' t'.X θ' hX' j t' hj' rfl ht' ht'a

  have hc₀ := compat_map (qκ : A →+* κ) t t' u hu.constantCoeff hta.constantCoeff_ρ ht'a.constantCoeff_ρ m hc

  obtain ⟨i, hi, hiV, hind, ib, hib, hibf, uA, huA, huAg, i₁, j₁, hcorr⟩ :=
    CerednikDrinfeld.QM.FakeEllipticCurve.exists_isoVia_corr_inducing_of_formalIso_of_isRigTransport_of_isAlgClosed
      hrr hrN 𝒪 hdvr π hπ hcomplete hres hunr K₀ Onr Fr hOnr_complete hOnr_max hOnr_alg hOnr_closed hFr hB Λ hΛ hΛℤ coord hcoord A₀ X₀ hX₀ θ₀ hA₀ ι Φ hΦ hΦ4 E₀ hE₀ _ (by assumption) n₀ β₀ hβ₀
      κ hκ hκr (qκ.comp ψ) x₀ x₀' (t.X.map (qκ : A →+* κ)) (t'.X.map (qκ : A →+* κ)) θE θE' hθE hθE'
      j (t.map (qκ : A →+* κ)) (t'.map (qκ : A →+* κ)) rfl rfl htrE htrE' htaE htaE'
      (T.map (qκ : A →+* κ)) (isIso_map (qκ : A →+* κ) T hT) m hc₀
  refine ⟨i, hi, hiV, ib, hib, hibf, uA, huA, huAg, i₁, j₁, hcorr, T, hT, ?_⟩

  intro B'' _ _ _ halg J n hJ s hs p₀ hp₀
  have hsn : ∀ l, IsNilpotent (s l) := fun l => ⟨n + 1, by
    have h := Ideal.pow_mem_pow (hs l) (n + 1)
    rwa [hJ, Ideal.mem_bot] at h⟩
  obtain ⟨hsq, -⟩ := id hg
  have hp : p₀.1 = (θE B'' s).1 := by
    apply hsq.hom_ext
    · rw [hp₀, hrelE B'' halg s hsn]
    · rw [p₀.2, (θE B'' s).2]
  have hev : (fun l => MvFormalGroup.nilEval n ((T.map (qκ : A →+* κ)).toSeries l) s) =
      fun l => MvFormalGroup.nilEval n (T.toSeries l) s :=
    funext fun l => XCSol.nilEval_map (qκ : A →+* κ) halg n (T.toSeries l) s
  have hyn : ∀ l, IsNilpotent (MvFormalGroup.nilEval n (T.toSeries l) s) := by
    intro l
    have hmem := (MvFormalGroup.nilEval_subst_of_mem J n hJ s hs T.toSeries hu.constantCoeff (MvPowerSeries.X 0)).1 l
    exact ⟨n + 1, by
      have h := Ideal.pow_mem_pow hmem (n + 1)
      rwa [hJ, Ideal.mem_bot] at h⟩
  rw [hp, ← Category.assoc, hind B'' J n hJ s hs, hev]
  exact hrelE' B'' halg _ hyn

end S_CerednikDrinfeld_QM_FakeEllipticCurve_Rigidification_exists_isoVia_corr_and_formalIso_of_rigidifiedToG_eq_of_isArtinianRing
end P2MW
export P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_Rigidification_exists_isoVia_corr_and_formalIso_of_rigidifiedToG_eq_of_isArtinianRing (solution)
