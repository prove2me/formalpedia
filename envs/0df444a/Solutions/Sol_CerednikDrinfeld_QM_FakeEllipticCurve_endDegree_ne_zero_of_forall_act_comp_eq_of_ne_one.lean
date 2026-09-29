-- Prove2me | solution 1 for CerednikDrinfeld.QM.FakeEllipticCurve.endDegree_ne_zero_of_forall_act_comp_eq_of_ne_one
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.837917+00:00
-- url     : https://prove2.me/submissions/71cefbb0-f0b6-5a33-a5e2-362907ae316b

import Mathlib
import Definitions.Def_CerednikDrinfeld_QMModuli
import Definitions.Def_AlgebraicGeometry_RelativeGroupLawEndDegree
import Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_exists_relativeGroupLaw_image_of_homomorphism
import Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_exists_smoothOfRelativeDimension_of_smooth_of_isLocalRing
import Theorems.Thm_AlgebraicGeometry_SmoothOfRelativeDimension_le_topologicalKrullDim
import Theorems.Thm_AlgebraicGeometry_SmoothOfRelativeDimension_topologicalKrullDim_le
import Theorems.Thm_IsIrreducible_topologicalKrullDim_add_one_le_of_isClosed_of_ne
import Theorems.Thm_GoodReductionJacobian_AbelianSchemePropertyBundle_isIntegral_of_field
import Theorems.Thm_GoodReductionJacobian_AbelianSchemePropertyBundle_geometricallyIntegral
import Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_isFinite_endKerStr_of_surjective
import Theorems.Thm_CerednikDrinfeld_QM_exists_comp_eq_of_forall_factorsThrough_of_isReduced
import Theorems.Thm_CerednikDrinfeld_QM_surjective_and_isFinite_and_flat_of_mapPt_mapPt_eq_nsmulPt
import Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_endDegree_schemeHomOverComp_of_isFinite_of_flat
import Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_exists_isHomogeneous_eval_eq_endDegree_of_abelianSchemePropertyBundle
import Theorems.Thm_QuaternionAlgebra_IsIndefiniteRamifiedExactlyAt_isUnit_of_ne_zero
import Theorems.Thm_QuaternionAlgebra_exists_ne_zero_and_not_isUnit_of_forall_map_mul_of_forall_pos
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_endDegree_ne_zero_of_forall_act_comp_eq_of_ne_one
p2m_attr_erase "instance" "AlgebraicGeometry.Scheme.PresheafOfModules.symmetricCategory SheafOfModules.instFaithfulRingSheafPModToPMod SheafOfModules.symmetricCategory AlgebraicGeometry.Scheme.PresheafOfModules.monoidalCategory AlgebraicGeometry.Scheme.PresheafOfModules.monoidalClosed SheafOfModules.instFullRingSheafPModToPMod SheafOfModules.monoidalCategory AlgebraicGeometry.Scheme.Modules.symmetricCategory SheafOfModules.monoidalClosed SheafOfModules.instIsLocalizationPModRingSheafSheafifyFunctorPresheafW SheafOfModules.sheafifyFunctor_monoidal AlgebraicGeometry.Scheme.Modules.monoidalClosed AlgebraicGeometry.instMonoidalPresheafOfModulesModulesSheafify AlgebraicGeometry.Scheme.Modules.monoidalCategory PresheafOfModules.instMonoidalClosed PresheafOfModules.InternalHom.instModuleCarrierObjOppositeCommRingCatSubtypePiFamilyMemAddSubgroupNaturalFamilies PresheafOfModules.InternalHom.instModuleCarrierObjOppositeRingCatCompCommRingCatForget₂RingHomCarrierCarrierAbPresheaf PresheafOfModules.InternalHom.instSMulCarrierObjOppositeCommRingCatSubtypePiFamilyMemAddSubgroupNaturalFamilies AlgebraicGeometry.Scheme.Hom.opensMapFinal AlgebraicGeometry.RelPicard.RigidifiedLineBundle.setoid AlgebraicGeometry.RelPicard.RigidifiedLineBundle.instInhabited AlgebraicGeometry.OModulePresheaf.isScalarTower AlgebraicGeometry.Scheme.OrderedAffineCover.instLinearOrder AlgebraicGeometry.OModulePresheaf.module AlgebraicGeometry.Scheme.OrderedAffineCover.instFintype AlgebraicGeometry.Scheme.OrderedAffineCover.instFintypeIdx AlgebraicGeometry.OModulePresheaf.addCommGroup AlgebraicGeometry.Scheme.OrderedAffineCover.instDecidableEqIdx AlgebraicGeometry.OModulePresheaf.moduleSections TwoChartCech.Sections.M0_moduleA TwoChartCech.Sections.M1_module TwoChartCech.Cover.A01_algebra TwoChartCech.Cover.A0_algebra TwoChartCech.Cover.A1_commRing TwoChartCech.Cover.A1_algebra TwoChartCech.Sections.M01_module TwoChartCech.Sections.M0_addCommGroup TwoChartCech.Sections.M0_tower TwoChartCech.Sections.M01_addCommGroup TwoChartCech.Cover.A0_commRing"
p2m_attr_erase "instance" "TwoChartCech.Sections.M1_tower TwoChartCech.Sections.M01_moduleA TwoChartCech.Sections.M0_module TwoChartCech.Sections.M1_moduleA TwoChartCech.Sections.M1_addCommGroup TwoChartCech.Cover.A01_commRing TwoChartCech.Sections.M01_tower CoherentBaseChange.TwoTermComplex.C0_module CoherentBaseChange.TwoTermComplex.C0_addCommGroup CoherentBaseChange.TwoTermComplex.C1_module CoherentBaseChange.TwoTermComplex.C1_addCommGroup CoherentBaseChange.TwoTermComplex.C0_free CoherentBaseChange.TwoTermComplex.C1_finite CoherentBaseChange.TwoTermComplex.C0_finite CoherentBaseChange.TwoTermComplex.C1_free AlgebraicGeometry.Scheme.Modules.preservesBinaryProducts_opensMap AlgebraicGeometry.Scheme.Modules.pullback_monoidal AlgebraicGeometry.Scheme.Modules.sheafify_isLocalization' AlgebraicGeometry.Scheme.Modules.preservesTerminal_opensMap AlgebraicGeometry.Scheme.Modules.pullback₀_monoidal AlgebraicGeometry.Scheme.Modules.preservesFiniteProducts_opensMap AlgebraicGeometry.Scheme.Modules.instLiftingPresheafOfModulesSheafifyPresheafWOpensCarrierCarrierCommRingCatGrothendieckTopologyObjFunctorOppositeIsSheafSheafCompPullback₀Pullback PresheafOfModules.PullbackMonoidal.pullback_monoidal PresheafOfModules.PullbackMonoidal.isIso_δ PresheafOfModules.pushforward_laxMonoidal PresheafOfModules.PullbackMonoidal.isIso_η PresheafOfModules.free_monoidal PresheafOfModules.restrictScalars_laxMonoidal PresheafOfModules.PullbackMonoidal.isIso_δ_gS PresheafOfModules.pullback_oplaxMonoidal PresheafOfModules.PullbackMonoidal.instPreservesColimitsOfSizeCompOppositeCommRingCatRingCatForget₂RingHomCarrierCarrierPb PresheafOfModules.pullback_monoidal' AlgebraicGeometry.SmoothOfRelativeDimension.fiberToSpecResidueField AlgebraicGeometry.SmoothOfRelativeDimension.pullback_snd AlgebraicGeometry.SmoothOfRelativeDimension.pullback_fst AlgebraicGeometry.SmoothOfRelativeDimension.smooth_one AlgebraicGeometry.SmoothProperCurve.isIntegral_pullback_Spec_field AlgebraicGeometry.IsProper.fiberToSpecResidueField AlgebraicCurve.CurveModel.isProper AlgebraicCurve.CurveModel.isIntegral"
p2m_attr_erase "instance" "AlgebraicCurve.CurveModel.smooth AlgebraicGeometry.Scheme.LocalRepresentabilityULift.instIsLocallyInjectiveFunUliftYonedaGluedToSheaf AlgebraicGeometry.Scheme.LocalRepresentabilityULift.instIsLocallySurjectiveFunUliftYonedaGluedToSheafOfIsLocallySurjectiveZariskiTopologyDescFunctorOppositeType AlgebraicGeometry.Scheme.LocalRepresentabilityULift.instIsOpenImmersionToGlued AlgebraicGeometry.Scheme.LocalRepresentabilityULift.instIsIsoSheafZariskiTopologyTypeUliftYonedaGluedToSheaf AlgebraicGeometry.RelPicard.instIsOpenImmersionToGlued AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.instFundamentalIdentityOfSumRamificationInertia AlgebraicCurve.Place.instIsScalarTowerResidueFieldRestrictPushforward AlgebraicCurve.Place.instAlgebraResidueFieldRestrictPushforward AlgebraicCurve.Place.instIsLocalHomRestrictInclusion AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions PresheafOfModules.ExteriorPower.instModulePresheafAb AlgebraicGeometry.RelEffCartierDiv.subsingleton_of_degree_zero AlgebraicGeometry.RelEffCartierDiv.isIso_subschemeIota_snd_of_degree_one AlgebraicGeometry.isIso_ker_graphOver_subschemeIota_snd AlgebraicGeometry.isClosedImmersion_graphOver AlgebraicGeometry.FGSubalgebra.instIsDirectedLe AlgebraicGeometry.FGSubalgebra.instQuasiSeparatedSpaceCarrierCarrierCommRingCatObjOppositeSchemeSpecDiagram AlgebraicGeometry.FGSubalgebra.instIsCofilteredOpposite AlgebraicGeometry.FGSubalgebra.instIsAffineObjOppositeSchemeSpecDiagram AlgebraicGeometry.FGSubalgebra.instNonempty AlgebraicGeometry.FGSubalgebra.instNonemptySubtypeLeSubalgebraValFG AlgebraicGeometry.FGSubalgebra.instCompactSpaceCarrierCarrierCommRingCatObjOppositeSchemeSpecDiagram AlgebraicGeometry.FGSubalgebra.instIsDirectedSubtypeLeSubalgebraValFG AlgebraicGeometry.FGSubalgebra.instIsAffineHomMapOppositeSchemeSpecDiagram AlgebraicGeometry.FGSubalgebra.instIsFiltered AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instNeg AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instSMulInt AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instAddCommGroup AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instAdd AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instSub AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instModuleCarrierObjOppositeOpensCarrierCarrierCommRingCatPresheafOpOpensTop AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instSMulCarrierObjOppositeOpensCarrierCarrierCommRingCatPresheafOpOpensTop"
p2m_attr_erase "instance" "AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instSMulNat AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instZero AlgebraicCurve.instHasLocalResidue_of_hasCanonicalLocalResidueK AlgebraicCurve.instHasCanonicalLocalResidueK_of_hasCanonicalLocalResidueKStar AlgebraicCurve.Place.kw_ffgc_finiteDimensional_adicCompletion instAlgebraSubtypeMemValuationSubring_definitions AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersIntegersCompletion ModularCurve.KwF4gRRTate.instAlgebraKAdicCompletionIntegers AlgebraicCurve.Place.kw_ffgc_continuousSMul_adicCompletionComap AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersCompletionCompletion IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions AlgebraicCurve.instHasCanonicalLocalResidueK AlgebraicCurve.Place.instAlgebra_restrictResidueField AlgebraicCurve.Place.instIsScalarTower_restrictResidueField AlgebraicCurve.instHasLocalResidue AlgebraicCurve.HasSeparableResidue.of_perfectField_of_isCurveOver AlgebraicCurve.HasSeparableResidue.of_perfectField AlgebraicCurve.Place.instIsLocalHom_restrictSubringHom AlgebraicCurve.instHasCanonicalLocalResidueKStar ModularCurve.KwNo6Pin.isLocalRing_completion SheafOfModules.isIso_ihomModelToIhom AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instDecidableEqIdx AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instFintype AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instLinearOrder AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instFintypeIdx AlgebraicGeometry.OModulePresheaf.instSubsingletonObjZero AlgebraicGeometry.OModulePresheaf.Leray.relAltC_scalarTower AlgebraicGeometry.OModulePresheaf.Leray.ker_relAltd_modΓ AlgebraicGeometry.OModulePresheaf.Leray.relAltC_modΓ AlgebraicGeometry.OModulePresheaf.Leray.biC_abGrp AlgebraicGeometry.OModulePresheaf.Leray.relAltH_modΓ AlgebraicGeometry.OModulePresheaf.Leray.ker_relAltd_smul AlgebraicGeometry.OModulePresheaf.Leray.relAltH_scalarTower AlgebraicGeometry.OModulePresheaf.Leray.relAltH_smul AlgebraicGeometry.OModulePresheaf.Leray.biC_module"
p2m_attr_erase "instance" "DoubleComplex.instModuleE₂I DoubleComplex.Bounded.modR DoubleComplex.instModuleE₂II DoubleComplex.instAddCommGroupE₂II DoubleComplex.Bounded.abGrp DoubleComplex.instAddCommGroupE₂I AlgebraicGeometry.ChowDatum.hι_closed AlgebraicGeometry.ChowDatumProj.hιN_closed AlgebraicGeometry.ChowDatumProj.hp_proper AlgebraicGeometry.ChowDatum.hp_isoU AlgebraicGeometry.ChowDatum.hp_proper AlgebraicGeometry.ProjSpace.algebraAway AlgebraicGeometry.ProjSpace.instIsProperProdOverπ AlgebraicGeometry.ChowDatumProj.hp_isoU AlgebraicGeometry.ProjSpace.isProper_π AlgebraicGeometry.ProjSpace.finiteType_mvPolynomial ProjSpaceCech.GradedModule.H.module ProjSpaceCech.GradedModule.H.addCommGroup ProjSpaceCech.GradedModule.sec.instAdd ProjSpaceCech.GradedModule.sec.instNeg ProjSpaceCech.GradedModule.acg ProjSpaceCech.GradedModule.Frac.setoid ProjSpaceCech.GradedModule.modR ProjSpaceCech.GradedModule.sec.instModule ProjSpaceCech.GradedModule.sec.instAddCommGroup ProjSpaceCech.GradedModule.sec.instZero ProjSpaceCech.GradedModule.Presentation.fJ ProjSpaceCech.GradedModule.sec.instSMul ProjSpaceCech.Twist.H.module ProjSpaceCech.Idx.instFintype ProjSpaceCech.Twist.H.addCommGroup ProjSpaceCech.Idx.instDecidableEq ProjSpaceCech.Twist.Mon.instDecidableEq ProjSpaceCech.Twist.cochain.instAddCommGroup ProjSpaceCech.Twist.cochain.instModule AlgebraicGeometry.FGSubalgebra.tensorStage_directedSystem AlgebraicGeometry.RelEffCartierDiv.isClosedImmersion_subschemeι_resProdMap AlgebraicGeometry.RelEffCartierDiv.isOpenImmersion_resProdMap AlgebraicCurve.CurveModel.locallyOfFiniteType_gluedToBase AlgebraicCurve.CurveModel.isFractionRing_overlap"
p2m_attr_erase "instance" "AlgebraicCurve.CurveModel.isLocallyNoetherian_glued AlgebraicCurve.CurveModel.jacobsonSpace_glued AlgebraicCurve.CurveModel.isOpenImmersion_ι₀ AlgebraicCurve.CurveModel.isIntegral_glued AlgebraicCurve.CurveModel.quasiSeparated_gluedToBase AlgebraicCurve.CurveModel.compactSpace_glued AlgebraicCurve.CurveModel.isIntegral_adjoin_chartRing AlgebraicCurve.CurveModel.isFractionRing_overlap_functionField AlgebraicCurve.CurveModel.isProper_gluedToBase AlgebraicCurve.CurveModel.isOpenImmersion_ιU AlgebraicCurve.CurveModel.isOpenImmersion_f₀ AlgebraicCurve.CurveModel.isOpenImmersion_fInf AlgebraicCurve.CurveModel.isOpenImmersion_ιInf AlgebraicCurve.CurveModel.algebra_overlap_functionField AlgebraicCurve.CurveModel.quasiCompact_gluedToBase AlgebraicCurve.CurveModel.algebraAdjoin AlgebraicCurve.CurveModel.isDedekindDomain_chartRing AlgebraicCurve.CurveModel.isIntegralClosure AlgebraicCurve.CurveModel.finite_chartRing AlgebraicCurve.CurveModel.centre_isPrime AlgebraicCurve.CurveModel.isFractionRing_chartRing AlgebraicCurve.CurveModel.finiteType_chartRing AlgebraicCurve.CurveModel.isNoetherianRing_chartRing AlgebraicCurve.CurveModel.isScalarTower_base_adjoin AlgebraicCurve.CurveModel.isScalarTower_adjoin AlgebraicCurve.CurveModel.chartRing_finitePresentation instTopologicallyFGOfFiniteType AlgebraicGeometry.ProjSpace.twistObj.addCommGroup AlgebraicGeometry.ProjSpace.twistFam.module AlgebraicGeometry.ProjSpace.twistObj.module AlgebraicGeometry.ProjSpace.twistObj.moduleSections AlgebraicGeometry.ProjSpace.twistFam.addCommGroup kmfloorsGlue_int_three_isPrime kmfloorsGlue_int_bot_isPrime"
p2m_attr_erase "simp" "GoodReductionJacobian.relativeGroupLawOfGrpObj_inv GoodReductionJacobian.relativeGroupLawOfGrpObj_mul GoodReductionJacobian.overHomEquivSchemeHomOver_apply_coe GoodReductionJacobian.relativeGroupLawOfGrpObj_one GoodReductionJacobian.overHomEquivSchemeHomOver_symm_apply_left RegularLocalRingQuotientAscent.dualNumberFst_apply SheafOfModules.tensorUnit_eq AlgebraicGeometry.Scheme.Modules.tensorUnit_eq PresheafOfModules.InternalHom.presheaf_map_apply PresheafOfModules.InternalHom.curryFamily_app PresheafOfModules.InternalHom.add_app PresheafOfModules.InternalHom.smul_app PresheafOfModules.InternalHom.zero_app PresheafOfModules.ihomObj_map_val PresheafOfModules.ihomFunctor_map PresheafOfModules.InternalHom.restrict_app PresheafOfModules.InternalHom.postcomp_app PresheafOfModules.InternalHom.neg_app PresheafOfModules.curry'_app_val PresheafOfModules.InternalHom.presheaf_obj PresheafOfModules.ihomFunctor_obj PresheafOfModules.ihomObj_obj PresheafOfModules.InternalHom.sub_app PresheafOfModules.ihomMap_app_val AlgebraicGeometry.Scheme.Modules.tensorPow_zero AlgebraicGeometry.Scheme.Modules.tensorPow_succ AlgebraicGeometry.RelPicard.RigidifiedLineBundle.mk.sizeOf_spec AlgebraicGeometry.RelPicard.RigidifiedLineBundle.mk.injEq AlgebraicGeometry.Scheme.OrderedAffineCover.mk.injEq AlgebraicGeometry.OModulePresheaf.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCover.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.mk.injEq AlgebraicGeometry.Scheme.TwoAffineOpenCover.mk.injEq AlgebraicGeometry.Scheme.TwoAffineOpenCover.mk.sizeOf_spec AlgebraicGeometry.Scheme.TwoAffineOpenCover.pullback_U1 AlgebraicGeometry.Scheme.TwoAffineOpenCover.pullback_U0 TwoChartCech.Sections.mk.injEq TwoChartCech.Cover.mk.injEq TwoChartCech.GrothendieckComplex.mk.injEq TwoChartCech.Sections.mk.sizeOf_spec"
p2m_attr_erase "simp" "TwoChartCech.Cover.mk.sizeOf_spec TwoChartCech.Cover.lineBundle_r0_apply TwoChartCech.GrothendieckComplex.mk.sizeOf_spec TwoChartCech.Cover.lineBundle_r1_apply CoherentBaseChange.TwoTermComplex.mk.sizeOf_spec CoherentBaseChange.TwoTermComplex.mk.injEq PresheafOfModules.freeεIso_hom_app PresheafOfModules.freeμIso_hom_app AlgebraicGeometry.RelPicard.RepresentsRelSubPic.mk.injEq AlgebraicGeometry.RelPicard.SubPicCondition.mk.injEq AlgebraicGeometry.RelPicard.SubPicCondition.mk.sizeOf_spec AlgebraicGeometry.RelPicard.RepresentsRelSubPic.mk.sizeOf_spec AlgebraicGeometry.SmoothProperCurve.sectionBaseChange_coe_snd AlgebraicGeometry.SmoothProperCurve.sectionBaseChange_coe_fst AlgebraicCurve.CurveModel.mk.injEq AlgebraicCurve.CurveModel.mk.sizeOf_spec AlgebraicCurve.mulAdele_apply AlgebraicCurve.residuePairing_apply_coe AlgebraicCurve.mem_adeleBdd AlgebraicCurve.weilSmul_one AlgebraicCurve.diagonalHom_apply AlgebraicCurve.weilSmul_apply AlgebraicCurve.adeleSpaceMul_coe AlgebraicCurve.mulAdele_one AlgebraicGeometry.SmoothProperCurve.FiniteMapData.twoAffineOpenCover_U1 AlgebraicGeometry.SmoothProperCurve.FiniteMapData.mk.injEq AlgebraicGeometry.SmoothProperCurve.FiniteMapData.mk.sizeOf_spec AlgebraicGeometry.SmoothProperCurve.FiniteMapData.twoAffineOpenCover_U0 AlgebraicGeometry.RelPicard.SubPicCondition.onClasses_mk AlgebraicGeometry.RelPicard.relSubPicPresheaf_map_coe CategoryTheory.Functor.OverTotal.ofFibre_fst CategoryTheory.Functor.overTotal_map_fst AlgebraicGeometry.Scheme.LocalRepresentabilityULift.glueData_J AlgebraicGeometry.Scheme.LocalRepresentabilityULift.uliftYoneda_toGlued_uliftYonedaGluedToSheaf AlgebraicGeometry.Scheme.LocalRepresentabilityULift.glueData_t' AlgebraicGeometry.Scheme.LocalRepresentabilityULift.uliftYoneda_toGlued_uliftYonedaGluedToSheaf_assoc AlgebraicGeometry.Scheme.LocalRepresentabilityULift.uliftYonedaGluedToSheaf_app_toGlued AlgebraicGeometry.Scheme.LocalRepresentabilityULift.glueData_openCover_map AlgebraicGeometry.Scheme.LocalRepresentabilityULift.uliftYonedaGluedToSheaf_app_comp AlgebraicGeometry.Scheme.LocalRepresentabilityULift.glueData_V"
p2m_attr_erase "simp" "AlgebraicGeometry.Scheme.LocalRepresentabilityULift.glueData_t AlgebraicGeometry.Scheme.LocalRepresentabilityULift.glueData_U AlgebraicGeometry.Scheme.LocalRepresentabilityULift.glueData_f AlgebraicGeometry.RelPicard.designationOfRepresentableBy_P AlgebraicGeometry.RelPicard.designationOfRepresentableBy_toBase AlgebraicGeometry.RelPicard.rigSection_snd AlgebraicGeometry.RelPicard.RigidifiedLineBundle.ofInvertible_L AlgebraicGeometry.RelPicard.rigSection_snd_assoc AlgebraicGeometry.RelPicard.SubPicGroupCondition.mk.injEq AlgebraicGeometry.RelPicard.SubPicGroupCondition.mk.sizeOf_spec AlgebraicCurve.coe_cechH0Equiv_apply AlgebraicCurve.cechH1ToH1_mk AlgebraicCurve.lSpaceOn_univ AlgebraicCurve.lSpaceOn_empty AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.Divisor.mapRestrict_single AlgebraicCurve.Divisor.pushforward_single AlgebraicCurve.Place.coe_restrictInclusion AlgebraicCurve.Place.mem_fiber AlgebraicCurve.Place.restrict_toValuationSubring AlgebraicCurve.Divisor.degree_pushforward AlgebraicCurve.Place.restrictResidueMap_residue AlgebraicCurve.Pic0.coe_pushforwardDegZeroHom AlgebraicCurve.Pic0.coe_pullbackDegZeroHom AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe"
p2m_attr_erase "simp" "ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Divisor.degree_pushforwardAlong AlgebraicCurve.Pic0.coe_degZeroCorrespondence AlgebraicCurve.Place.mem_fiberAlong AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.jqNModC_one ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one AlgebraicCurve.Place.differentialCoeff_zero AlgebraicCurve.Place.differentialCoeff_dCoord AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.injEq AlgebraicCurve.TranscendenceTower.mk.injEq AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec AlgebraicCurve.PoleDivisorPackage.mk.injEq AlgebraicGeometry.RelPicard.thetaBundle_def AlgebraicGeometry.RelPicard.picardBundle_def AlgebraicGeometry.RelEffCartierDiv.toRelEffDivisor_ofRelEffDivisor"
p2m_attr_erase "simp" "AlgebraicGeometry.RelEffCartierDiv.toRelEffDivisor_I AlgebraicGeometry.mapOnProdOver_fst_assoc AlgebraicGeometry.RelEffCartierDiv.mk.sizeOf_spec AlgebraicGeometry.RelEffCartierDiv.mk.injEq AlgebraicGeometry.mapOnProdOver_snd AlgebraicGeometry.mapOnProdOver_fst AlgebraicGeometry.mapOnProdOver_snd_assoc AlgebraicGeometry.mapOnProdOver_id AlgebraicCurve.RelEffDivisor.mk.sizeOf_spec AlgebraicCurve.mapOnProd_fst AlgebraicCurve.mapOnProd_fst_assoc AlgebraicCurve.mapOnProd_snd AlgebraicCurve.UnivDivisorPack.mk.injEq AlgebraicCurve.RelEffDivisor.mk.injEq AlgebraicCurve.UnivDivisorPack.mk.sizeOf_spec AlgebraicCurve.mapOnProd_snd_assoc AlgebraicGeometry.Scheme.Modules.exteriorPower_obj PresheafOfModules.exteriorPower_map_ιMulti PresheafOfModules.ExteriorPower.appₗ_apply AlgebraicGeometry.prodKerGraph_one AlgebraicGeometry.fibrePowOver.proj_comp AlgebraicGeometry.prodKerGraph_zero AlgebraicGeometry.RelEffCartierDiv.empty_I AlgebraicGeometry.fibrePowOver.proj_comp_assoc AlgebraicGeometry.graphOver_fst_assoc AlgebraicGeometry.RelEffCartierDiv.toPoint_comp AlgebraicGeometry.RelEffCartierDiv.toPoint_comp_assoc AlgebraicGeometry.graphOver_fst AlgebraicGeometry.RelEffCartierDiv.ofPoint_I AlgebraicGeometry.graphOver_snd AlgebraicGeometry.graphOver_snd_assoc AlgebraicCurve.SymmetricPowerPackage.mk.sizeOf_spec AlgebraicCurve.SymmetricPowerPackage.mk.injEq AlgebraicGeometry.FGSubalgebra.cocone_ι_app_apply AlgebraicGeometry.RelPicard.fst_toProdSpec AlgebraicGeometry.RelPicard.toProdSpec_fst_assoc AlgebraicGeometry.RelPicard.pointsSubBasepointModule_cons AlgebraicGeometry.RelPicard.pointsSubBasepointModule_nil AlgebraicGeometry.RelPicard.fst_toProdSpec_assoc AlgebraicGeometry.RelPicard.toProdSpec_fst"
p2m_attr_erase "simp" "AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.sub_app AlgebraicGeometry.Scheme.IdealSheafData.sres_sresTop AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.add_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.mk.sizeOf_spec AlgebraicGeometry.Scheme.IdealSheafData.coe_resLE AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.smul_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.coe_ofLE_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.ideal_range AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.zero_app AlgebraicGeometry.Scheme.IdealSheafData.sres_sres AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.comp_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.neg_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.id_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.coe_mulRight_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.nsmul_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.mk.injEq AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.zsmul_app AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.sizeOf_spec AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.injEq AlgebraicCurve.adeleSingle_coe AlgebraicCurve.kaehlerResidueTermKFam_apply AlgebraicCurve.Place.LocalResidueData.mk.injEq AlgebraicCurve.Place.LocalResidueData.mk.sizeOf_spec AlgebraicCurve.Place.kw_ffgc_adicCompletionComapIntegers_coe AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.sizeOf_spec AlgebraicCurve.Place.mem_simplePoleSubmodule AlgebraicCurve.Place.coe_uniformizerSubring ModularCurve.Lg37.Lg37CompletionSection.mk.injEq AlgebraicCurve.Place.CoefficientFieldSection.mk.injEq AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.injEq ModularCurve.Lg37.Lg37CompletionSection.mk.sizeOf_spec AlgebraicCurve.Place.CoefficientFieldSection.mk.sizeOf_spec AlgebraicCurve.Place.poleSubmodule_one AlgebraicCurve.Place.mem_poleSubmodule AlgebraicGeometry.Scheme.Modules.toUnitSection_ofUnitSection AlgebraicGeometry.Scheme.Modules.pullbackSection_def AlgebraicGeometry.Scheme.Modules.ofUnitSection_toUnitSection PresheafOfModules.InternalHom.IsSheafAux.appAt_toPresheafHom SheafOfModules.ihomSectionsEquivFamily_unit AlgebraicGeometry.Scheme.Modules.restrictHomEquivFamily_apply"
p2m_attr_erase "simp" "SheafOfModules.ihomEval_unit_app AlgebraicGeometry.Scheme.Modules.ihomEval_zero_right AlgebraicGeometry.Scheme.Modules.ihomEval_zero_left AlgebraicGeometry.Scheme.Modules.homOfFamily_app_apply SheafOfModules.unit_ihomSectionsEquivFamily AlgebraicGeometry.Scheme.Modules.familyOfHom_app AlgebraicGeometry.Scheme.Modules.restrictUnitIso_hom_app_apply AlgebraicGeometry.Scheme.Modules.restrictUnitIso_inv_app_apply AlgebraicGeometry.Scheme.Modules.restrictHomOfFamily_app_apply AlgebraicGeometry.Scheme.Modules.restrictHomEquivFamily_symm_apply AlgebraicGeometry.Scheme.Modules.tensorSections_zero_right AlgebraicGeometry.Scheme.Modules.map_unitSection AlgebraicGeometry.Scheme.Modules.tensorSectionsBilin_apply AlgebraicGeometry.Scheme.Modules.tensorPowSection_zero AlgebraicGeometry.Scheme.Modules.tensorSections_zero_left AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_neg AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_zero AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_sub AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_add AlgebraicGeometry.Scheme.OrderedAffineCover.toCoverOf_U AlgebraicGeometry.Scheme.OrderedAffineCoverOf.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCoverOf.mk.injEq AlgebraicGeometry.Scheme.OrderedAffineCover.restrict_U AlgebraicGeometry.OModulePresheaf.Hom.mk.injEq AlgebraicGeometry.OModulePresheaf.Hom.id_app AlgebraicGeometry.OModulePresheaf.AffHom.appSections_apply AlgebraicGeometry.OModulePresheaf.AffHom.comp_app AlgebraicGeometry.OModulePresheaf.AffSES.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.AffHom.kerMap_coe AlgebraicGeometry.OModulePresheaf.AffHom.id_app AlgebraicGeometry.OModulePresheaf.Hom.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.Hom.toAffHom_app AlgebraicGeometry.OModulePresheaf.SES.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.AffHom.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.Hom.comp_app AlgebraicGeometry.OModulePresheaf.SES.mk.injEq AlgebraicGeometry.OModulePresheaf.AffHom.mk.injEq AlgebraicGeometry.OModulePresheaf.Hom.appSections_apply AlgebraicGeometry.OModulePresheaf.AffSES.mk.injEq AlgebraicGeometry.OModulePresheaf.prod_obj"
p2m_attr_erase "simp" "AlgebraicGeometry.OModulePresheaf.restrOpen_obj AlgebraicGeometry.OModulePresheaf.DevissageStep.mk.injEq AlgebraicGeometry.OModulePresheaf.pushforward_obj AlgebraicGeometry.OModulePresheaf.im_obj AlgebraicGeometry.OModulePresheaf.pow_obj AlgebraicGeometry.OModulePresheaf.fstHom_app AlgebraicGeometry.OModulePresheaf.ker_obj AlgebraicGeometry.OModulePresheaf.coker_obj AlgebraicGeometry.OModulePresheaf.DevissageStep.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCover.preimage_U AlgebraicGeometry.OModulePresheaf.sndHom_app AlgebraicGeometry.OModulePresheaf.Leray.restrictToPreimage_U DoubleComplex.Bounded.mk.injEq DoubleComplex.Bounded.mk.sizeOf_spec DoubleComplex.Convergence.mk.injEq DoubleComplex.Convergence.mk.sizeOf_spec DoubleComplex.SubQuot.mk.sizeOf_spec DoubleComplex.SubQuot.mk.injEq AlgebraicGeometry.ChowDatumProj.mk.sizeOf_spec AlgebraicGeometry.ChowDatum.mk.sizeOf_spec AlgebraicGeometry.ChowDatumProj.mk.injEq AlgebraicGeometry.ChowDatum.mk.injEq ProjSpaceCech.GradedModule.mk.injEq ProjSpaceCech.GradedModule.mk.sizeOf_spec ProjSpaceCech.GradedModule.Frac.mk.sizeOf_spec ProjSpaceCech.GradedModule.Presentation.mk.injEq ProjSpaceCech.GradedModule.Frac.mk.injEq ProjSpaceCech.GradedModule.Presentation.mk.sizeOf_spec ProjSpaceCech.GradedModule.Hom.shift_toLinearMap ProjSpaceCech.GradedModule.Hom.mk.sizeOf_spec ProjSpaceCech.GradedModule.Hom.mk.injEq TwoChartCech.Mumford.dK_apply TwoChartCech.Mumford.ι0_apply TwoChartCech.Mumford.ι1_apply TwoChartCech.KerCoprod.dK_apply TwoChartCech.KerCoprod.ι1_apply TwoChartCech.KerCoprod.ι0_apply AlgebraicGeometry.tilde.functorCompPullbackSpecIso_app AlgebraicGeometry.RelPicard.algEquivZeroGroupCut_toSubPicCondition AlgebraicGeometry.RelPicard.LFP.stageHom_val"
p2m_attr_erase "simp" "AlgebraicGeometry.RelPicard.BaseChange.relSubPicPresheafRestrictIso_hom_app_coe AlgebraicGeometry.RelPicard.BaseChange.relSubPicPresheafRestrictIso_inv_app_coe AlgebraicGeometry.RelPicard.BaseChange.restrict_P AlgebraicGeometry.RelEffCartierDiv.IsUniversal.lift_comp AlgebraicGeometry.RelEffCartierDiv.functor_map_fst AlgebraicGeometry.RelEffCartierDiv.IsUniversal.homEquiv_apply AlgebraicGeometry.RelEffCartierDiv.IsUniversal.lift_pullbackAlong AlgebraicGeometry.RelEffCartierDiv.IsUniversal.homEquiv_symm_apply AlgebraicGeometry.RelEffCartierDiv.IsUniversal.lift_comp_assoc AlgebraicGeometry.RelEffCartierDiv.supportedIn_top AlgebraicGeometry.RelEffCartierDiv.mem_supportedIn_iff AlgebraicGeometry.RelEffCartierDiv.supportedIn_top_eq AlgebraicGeometry.RelEffCartierDiv.restrictAlong_extendAlong AlgebraicGeometry.RelEffCartierDiv.extendAlong_I AlgebraicGeometry.RelEffCartierDiv.resProdMap_snd AlgebraicGeometry.RelEffCartierDiv.restrictAlong_I AlgebraicGeometry.RelEffCartierDiv.extendAlong_restrictAlong AlgebraicGeometry.RelEffCartierDiv.resProdMap_fst_assoc AlgebraicGeometry.RelEffCartierDiv.resProdMap_snd_assoc AlgebraicGeometry.RelEffCartierDiv.resProdMap_fst CoherentBaseChange.FibreH0Family.mk.sizeOf_spec CoherentBaseChange.FibreH0Family.mk.injEq AlgebraicGeometry.Scheme.Modules.ProjPresentation.mk.injEq AlgebraicGeometry.Scheme.Modules.ProjPresentation.mk.sizeOf_spec AlgebraicCurve.CurveModel.coe_gInf AlgebraicCurve.CurveModel.coe_tInvChart AlgebraicCurve.CurveModel.ιInf_gluedToBase_assoc AlgebraicCurve.CurveModel.ιInf_gluedToBase AlgebraicCurve.CurveModel.primeOfι₀_asIdeal AlgebraicCurve.CurveModel.coe_tChart AlgebraicCurve.CurveModel.ι₀_gluedToBase_assoc AlgebraicCurve.CurveModel.primeOfιInf_asIdeal AlgebraicCurve.CurveModel.ι₀_gluedToBase AlgebraicCurve.CurveModel.coe_tma AlgebraicCurve.CurveModel.coe_primeEquivChartPlaces AlgebraicGeometry.ProjSpace.twistObj.mk.injEq AlgebraicGeometry.ProjSpace.twistObj.zero_val AlgebraicGeometry.ProjSpace.twistObj.add_val AlgebraicGeometry.ProjSpace.twist_res_val AlgebraicGeometry.ProjSpace.twist_smul_val"
p2m_attr_erase "simp" "AlgebraicGeometry.ProjSpace.twistGradeToObj_val AlgebraicGeometry.ProjSpace.twistObj.smul_val AlgebraicGeometry.ProjSpace.twistGradeEquiv_apply_val AlgebraicGeometry.ProjSpace.twistObj.mk.sizeOf_spec GoodReductionJacobian.RelativeGroupLaw.fibre_inv GoodReductionJacobian.RelativeGroupLaw.fibrePointToBase_coe GoodReductionJacobian.RelativeGroupLaw.fibrePointOfBase_toBase GoodReductionJacobian.RelativeGroupLaw.fibre_mul GoodReductionJacobian.RelativeGroupLaw.fibrePointToBase_ofBase GoodReductionJacobian.RelativeGroupLaw.fibre_one GoodReductionJacobian.RelativeGroupLaw.fibrePointOfBase_coe AlgebraicGeometry.schemeFibreEndo_snd AlgebraicGeometry.schemeFibreEndo_fst"

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian IsDedekindDomain AlgebraicCurve QuaternionAlgebra CerednikDrinfeld CerednikDrinfeld.QM

open scoped Quaternion TensorProduct NumberField

universe u

noncomputable section

namespace P2mKcLambdaSimpleA

section Poly

variable {ι : Type*}

theorem exists_eq_single_of_degree_eq_one (d : ι →₀ ℕ) (hd : d.degree = 1) :
    ∃ i, d = Finsupp.single i 1 := by
  classical
  have hd0 : d ≠ 0 := by
    intro h; rw [h, map_zero] at hd; exact zero_ne_one hd
  obtain ⟨i, hi⟩ : ∃ i, d i ≠ 0 := by simpa using Finsupp.ne_iff.mp hd0
  have hle : Finsupp.single i 1 ≤ d := by
    rw [Finsupp.single_le_iff]; exact Nat.one_le_iff_ne_zero.mpr hi
  have hsplit : d = (d - Finsupp.single i 1) + Finsupp.single i 1 := (tsub_add_cancel_of_le hle).symm
  have hdeg : (d - Finsupp.single i 1).degree = 0 := by
    have h := congrArg Finsupp.degree hsplit
    rw [map_add, Finsupp.degree_single, hd] at h
    omega
  rw [Finsupp.degree_eq_zero_iff] at hdeg
  exact ⟨i, by rw [hsplit, hdeg, zero_add]⟩

theorem exists_eq_single_add_single_of_degree_eq_two (d : ι →₀ ℕ) (hd : d.degree = 2) :
    ∃ i j, d = Finsupp.single i 1 + Finsupp.single j 1 := by
  classical
  have hd0 : d ≠ 0 := by
    intro h; rw [h, map_zero] at hd; exact two_ne_zero hd.symm
  obtain ⟨i, hi⟩ : ∃ i, d i ≠ 0 := by simpa using Finsupp.ne_iff.mp hd0
  have hle : Finsupp.single i 1 ≤ d := by
    rw [Finsupp.single_le_iff]; exact Nat.one_le_iff_ne_zero.mpr hi
  have hsplit : d = (d - Finsupp.single i 1) + Finsupp.single i 1 := (tsub_add_cancel_of_le hle).symm
  have hdeg : (d - Finsupp.single i 1).degree = 1 := by
    have h := congrArg Finsupp.degree hsplit
    rw [map_add, Finsupp.degree_single, hd] at h
    omega
  obtain ⟨j, hj⟩ := exists_eq_single_of_degree_eq_one _ hdeg
  exact ⟨j, i, by rw [hsplit, hj]⟩

noncomputable def qPair (a b : ι) : QuadraticMap ℚ (ι → ℚ) ℚ :=
  LinearMap.BilinMap.toQuadraticMap
    ((LinearMap.mul ℚ ℚ).compl₁₂ (LinearMap.proj a) (LinearMap.proj b))

theorem qPair_apply (a b : ι) (v : ι → ℚ) : qPair a b v = v a * v b := by
  simp [qPair, LinearMap.BilinMap.toQuadraticMap_apply]

variable [Fintype ι]

theorem prod_pow_single (v : ι → ℚ) (a : ι) : ∏ i, v i ^ (Finsupp.single a 1) i = v a := by
  classical
  simp only [Finsupp.single_apply, pow_ite, pow_one, pow_zero]
  rw [Finset.prod_ite_eq]; simp

theorem prod_pow_single_add_single (v : ι → ℚ) (a b : ι) :
    ∏ i, v i ^ (Finsupp.single a 1 + Finsupp.single b 1 : ι →₀ ℕ) i = v a * v b := by
  simp only [Finsupp.add_apply, pow_add, Finset.prod_mul_distrib, prod_pow_single]

open Classical in

noncomputable def qMono (d : ι →₀ ℕ) : QuadraticMap ℚ (ι → ℚ) ℚ :=
  if h : d.degree = 2 then
    qPair (exists_eq_single_add_single_of_degree_eq_two d h).choose
      (exists_eq_single_add_single_of_degree_eq_two d h).choose_spec.choose
  else 0

theorem qMono_apply (d : ι →₀ ℕ) (hd : d.degree = 2) (v : ι → ℚ) :
    qMono d v = ∏ i, v i ^ d i := by
  classical
  rw [qMono, dif_pos hd, qPair_apply]
  have h := (exists_eq_single_add_single_of_degree_eq_two d hd).choose_spec.choose_spec
  conv_rhs => rw [h]
  exact (prod_pow_single_add_single v _ _).symm

noncomputable def qPoly (P : MvPolynomial ι ℚ) : QuadraticMap ℚ (ι → ℚ) ℚ :=
  ∑ d ∈ P.support, P.coeff d • qMono d

theorem qPoly_apply (P : MvPolynomial ι ℚ) (hP : P.IsHomogeneous 2) (v : ι → ℚ) :
    qPoly P v = MvPolynomial.eval v P := by
  classical
  rw [qPoly, QuadraticMap.sum_apply, MvPolynomial.eval_eq']
  refine Finset.sum_congr rfl fun d hd => ?_
  have hdeg : d.degree = 2 := by
    by_contra h
    exact (MvPolynomial.mem_support_iff.mp hd) (hP.coeff_eq_zero h)
  rw [QuadraticMap.smul_apply, qMono_apply d hdeg, smul_eq_mul]

end Poly

section Lattice

variable {a b : ℚ}

theorem exists_nsmul_mem_of_mem_span (Λ : Submodule ℤ ℍ[ℚ, a, b]) (v : ℍ[ℚ, a, b])
    (hv : v ∈ Submodule.span ℚ (Λ : Set ℍ[ℚ, a, b])) :
    ∃ n : ℕ, 0 < n ∧ (n • v) ∈ Λ := by
  induction hv using Submodule.span_induction with
  | mem x hx => exact ⟨1, one_pos, by simpa using hx⟩
  | zero => exact ⟨1, one_pos, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨m, hm, hmx⟩ := hx
    obtain ⟨n, hn, hny⟩ := hy
    refine ⟨m * n, Nat.mul_pos hm hn, ?_⟩
    have h1 : (m * n) • (x + y) = n • (m • x) + m • (n • y) := by
      rw [smul_add, mul_comm m n, mul_smul, mul_comm n m, mul_smul]
    rw [h1]
    exact Λ.add_mem (nsmul_mem hmx n) (nsmul_mem hny m)
  | smul c x _ hx =>
    obtain ⟨n, hn, hnx⟩ := hx
    refine ⟨n * c.den, Nat.mul_pos hn c.den_pos, ?_⟩
    have h1 : (n * c.den) • (c • x) = c.num • (n • x) := by
      rw [← Nat.cast_smul_eq_nsmul ℚ, ← Nat.cast_smul_eq_nsmul ℚ n, ← Int.cast_smul_eq_zsmul ℚ,
        smul_smul, smul_smul, Nat.cast_mul, mul_assoc, Rat.den_mul_eq_num, mul_comm]
    rw [h1]
    exact zsmul_mem hnx c.num

theorem exists_nsmul_mem (Λ : Submodule ℤ ℍ[ℚ, a, b])
    (hspan : Submodule.span ℚ (Λ : Set ℍ[ℚ, a, b]) = ⊤) (v : ℍ[ℚ, a, b]) :
    ∃ n : ℕ, 0 < n ∧ (n • v) ∈ Λ :=
  exists_nsmul_mem_of_mem_span Λ v (by rw [hspan]; exact Submodule.mem_top)

theorem linearIndependent_rat {ι : Type*} (Λ : Submodule ℤ ℍ[ℚ, a, b]) (bΛ : Module.Basis ι ℤ ↥Λ) :
    LinearIndependent ℚ (fun i => (bΛ i : ℍ[ℚ, a, b])) := by
  have h : LinearIndependent ℤ (fun i => (bΛ i : ℍ[ℚ, a, b])) :=
    bΛ.linearIndependent.map' Λ.subtype (Submodule.ker_subtype Λ)
  exact (LinearIndependent.iff_fractionRing ℤ ℚ).mp h

theorem coe_eq_sum {ι : Type*} [Fintype ι] (Λ : Submodule ℤ ℍ[ℚ, a, b]) (bΛ : Module.Basis ι ℤ ↥Λ)
    (x : ↥Λ) : (x : ℍ[ℚ, a, b]) = ∑ i, ((bΛ.repr x i : ℤ) : ℚ) • (bΛ i : ℍ[ℚ, a, b]) := by
  conv_lhs => rw [← bΛ.sum_repr x]
  rw [Submodule.coe_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Submodule.coe_smul, Int.cast_smul_eq_zsmul]

theorem top_le_span_rat {ι : Type*} [Fintype ι] (Λ : Submodule ℤ ℍ[ℚ, a, b])
    (hspan : Submodule.span ℚ (Λ : Set ℍ[ℚ, a, b]) = ⊤) (bΛ : Module.Basis ι ℤ ↥Λ) :
    ⊤ ≤ Submodule.span ℚ (Set.range fun i => (bΛ i : ℍ[ℚ, a, b])) := by
  rw [← hspan, Submodule.span_le]
  intro x hx
  have h := coe_eq_sum Λ bΛ ⟨x, hx⟩
  simp only at h
  rw [SetLike.mem_coe, h]
  exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)

noncomputable def ratBasis {ι : Type*} [Fintype ι] (Λ : Submodule ℤ ℍ[ℚ, a, b])
    (hspan : Submodule.span ℚ (Λ : Set ℍ[ℚ, a, b]) = ⊤) (bΛ : Module.Basis ι ℤ ↥Λ) :
    Module.Basis ι ℚ ℍ[ℚ, a, b] :=
  Module.Basis.mk (linearIndependent_rat Λ bΛ) (top_le_span_rat Λ hspan bΛ)

theorem ratBasis_equivFun {ι : Type*} [Fintype ι] (Λ : Submodule ℤ ℍ[ℚ, a, b])
    (hspan : Submodule.span ℚ (Λ : Set ℍ[ℚ, a, b]) = ⊤) (bΛ : Module.Basis ι ℤ ↥Λ) (x : ↥Λ) :
    (ratBasis Λ hspan bΛ).equivFun (x : ℍ[ℚ, a, b]) = fun i => ((bΛ.repr x i : ℤ) : ℚ) := by
  have hx : (x : ℍ[ℚ, a, b]) = ∑ i, ((bΛ.repr x i : ℤ) : ℚ) • ratBasis Λ hspan bΛ i := by
    rw [coe_eq_sum Λ bΛ x]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [ratBasis, Module.Basis.coe_mk]
  rw [hx, ← Module.Basis.equivFun_symm_apply, LinearEquiv.apply_symm_apply]

theorem nsmul_ne_zero_of_ne_zero {n : ℕ} (hn : 0 < n) {v : ℍ[ℚ, a, b]} (hv : v ≠ 0) : n • v ≠ 0 := by
  rw [← Nat.cast_smul_eq_nsmul ℚ]
  exact smul_ne_zero (Nat.cast_ne_zero.mpr hn.ne') hv

theorem exists_quasiInv {q q' : ℕ} [Fact q.Prime] (hB : IsIndefiniteRamifiedExactlyAt a b q q')
    (Λ : Submodule ℤ ℍ[ℚ, a, b]) (hspan : Submodule.span ℚ (Λ : Set ℍ[ℚ, a, b]) = ⊤)
    (x : ℍ[ℚ, a, b]) (hx : x ≠ 0) :
    ∃ (m : ℕ) (y : ℍ[ℚ, a, b]), 0 < m ∧ y ∈ Λ ∧ x * y = m ∧ y * x = m := by
  obtain ⟨u, rfl⟩ := hB.isUnit_of_ne_zero x hx
  obtain ⟨m, hm, hmem⟩ := exists_nsmul_mem Λ hspan (↑u⁻¹ : ℍ[ℚ, a, b])
  refine ⟨m, m • (↑u⁻¹ : ℍ[ℚ, a, b]), hm, hmem, ?_, ?_⟩
  · rw [nsmul_eq_mul, ← mul_assoc, ← (Nat.cast_commute m (↑u : ℍ[ℚ, a, b])).eq, mul_assoc,
      Units.mul_inv, mul_one]
  · rw [nsmul_eq_mul, mul_assoc, Units.inv_mul, mul_one]

theorem false_of_quadratic {q q' : ℕ} [Fact q.Prime] (hB : IsIndefiniteRamifiedExactlyAt a b q q')
    (Λ : Submodule ℤ ℍ[ℚ, a, b]) (hΛ : IsOrder Λ)
    {ι : Type*} [Fintype ι] (bΛ : Module.Basis ι ℤ ↥Λ)
    (Q : ↥Λ → ℕ) (P : MvPolynomial ι ℚ) (hP : P.IsHomogeneous 2)
    (hQP : ∀ x : ↥Λ, (Q x : ℚ) = MvPolynomial.eval (fun i => ((bΛ.repr x i : ℤ) : ℚ)) P)
    (hQpos : ∀ x : ↥Λ, x ≠ 0 → Q x ≠ 0)
    (hQmul : ∀ x y : ↥Λ, x ≠ 0 → y ≠ 0 → Q ⟨x * y, hΛ.mul_mem x.2 y.2⟩ = Q x * Q y) : False := by
  classical
  set bB := ratBasis Λ hΛ.spanTop bΛ with hbB
  let QB : QuadraticMap ℚ ℍ[ℚ, a, b] ℚ := (qPoly P).comp bB.equivFun.toLinearMap

  have hkey : ∀ x : ↥Λ, QB (x : ℍ[ℚ, a, b]) = Q x := by
    intro x
    rw [QuadraticMap.comp_apply, LinearEquiv.coe_toLinearMap, hbB, ratBasis_equivFun, qPoly_apply P hP,
      hQP]
  have hsc : ∀ (n : ℕ) (v : ℍ[ℚ, a, b]), QB (n • v) = ((n : ℚ) * n) * QB v := by
    intro n v
    rw [← Nat.cast_smul_eq_nsmul ℚ, QuadraticMap.map_smul, smul_eq_mul]

  have hmul : ∀ u v : ℍ[ℚ, a, b], QB (u * v) = QB u * QB v := by
    intro u v
    by_cases hu : u = 0
    · rw [hu, zero_mul, QuadraticMap.map_zero, zero_mul]
    by_cases hv : v = 0
    · rw [hv, mul_zero, QuadraticMap.map_zero, mul_zero]
    obtain ⟨m, hm, hmu⟩ := exists_nsmul_mem Λ hΛ.spanTop u
    obtain ⟨n, hn, hnv⟩ := exists_nsmul_mem Λ hΛ.spanTop v
    have hmu0 : (⟨m • u, hmu⟩ : ↥Λ) ≠ 0 := by
      intro h
      have h' : m • u = 0 := congrArg Subtype.val h
      exact (nsmul_ne_zero_of_ne_zero hm hu) h'
    have hnv0 : (⟨n • v, hnv⟩ : ↥Λ) ≠ 0 := by
      intro h
      have h' : n • v = 0 := congrArg Subtype.val h
      exact (nsmul_ne_zero_of_ne_zero hn hv) h'
    have h := hQmul _ _ hmu0 hnv0
    have h' := congrArg (fun t : ℕ => (t : ℚ)) h
    simp only [Nat.cast_mul] at h'
    rw [← hkey, ← hkey, ← hkey] at h'
    change QB ((m • u) * (n • v)) = QB (m • u) * QB (n • v) at h'
    have hprod : (m • u) * (n • v) = (m * n) • (u * v) := by
      rw [smul_mul_smul_comm]
    rw [hprod, hsc, hsc, hsc] at h'
    have hmn : ((m * n : ℕ) : ℚ) * (m * n : ℕ) ≠ 0 := by positivity
    have : ((m * n : ℕ) : ℚ) * (m * n : ℕ) * (QB (u * v) - QB u * QB v) = 0 := by
      push_cast at h' ⊢
      linear_combination h'
    rcases mul_eq_zero.mp this with h0 | h0
    · exact absurd h0 hmn
    · exact sub_eq_zero.mp h0

  have hpos : ∀ v : ℍ[ℚ, a, b], v ≠ 0 → 0 < QB v := by
    intro v hv
    obtain ⟨n, hn, hnv⟩ := exists_nsmul_mem Λ hΛ.spanTop v
    have hnv0 : (⟨n • v, hnv⟩ : ↥Λ) ≠ 0 := by
      intro h
      have h' : n • v = 0 := congrArg Subtype.val h
      exact (nsmul_ne_zero_of_ne_zero hn hv) h'
    have h1 : (1 : ℚ) ≤ Q ⟨n • v, hnv⟩ := by
      exact_mod_cast Nat.one_le_iff_ne_zero.mpr (hQpos _ hnv0)
    rw [← hkey] at h1
    change 1 ≤ QB (n • v) at h1
    rw [hsc] at h1
    have hn' : (0 : ℚ) < (n : ℚ) * n := by positivity
    nlinarith
  obtain ⟨x, hx0, hxu⟩ :=
    QuaternionAlgebra.exists_ne_zero_and_not_isUnit_of_forall_map_mul_of_forall_pos hB.1 QB hmul hpos
  exact hxu (hB.isUnit_of_ne_zero x hx0)

end Lattice

end P2mKcLambdaSimpleA

namespace P2mKcLambdaSimpleB

section Points

variable {R : Type u} [CommRing R] {G H : Scheme.{u}}
  {gG : G ⟶ Spec (CommRingCat.of R)} {gH : H ⟶ Spec (CommRingCat.of R)}

def pointHom (LG : RelativeGroupLaw R gG) (LH : RelativeGroupLaw R gH) (v : SchemeHomOver gG gH)
    (hv : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (x y : SchemeHomOver t gG),
      NeronModelInfra.schemeHomOverComp (LG.mul t x y) v =
        LH.mul t (NeronModelInfra.schemeHomOverComp x v) (NeronModelInfra.schemeHomOverComp y v))
    {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) :
    letI := LG.pointGroup t
    letI := LH.pointGroup t
    SchemeHomOver t gG →* SchemeHomOver t gH :=
  letI := LG.pointGroup t
  letI := LH.pointGroup t
  MonoidHom.mk' (fun x => NeronModelInfra.schemeHomOverComp x v) (fun x y => hv t x y)

theorem hom_one (LG : RelativeGroupLaw R gG) (LH : RelativeGroupLaw R gH) (v : SchemeHomOver gG gH)
    (hv : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (x y : SchemeHomOver t gG),
      NeronModelInfra.schemeHomOverComp (LG.mul t x y) v =
        LH.mul t (NeronModelInfra.schemeHomOverComp x v) (NeronModelInfra.schemeHomOverComp y v))
    {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) :
    NeronModelInfra.schemeHomOverComp (LG.one t) v = LH.one t := by
  letI := LG.pointGroup t
  letI := LH.pointGroup t
  exact (pointHom LG LH v hv t).map_one

def evalHom (LG : RelativeGroupLaw R gG) {T : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of R)}
    (P : SchemeHomOver t gG) :
    letI := LG.pointGroup gG
    letI := LG.pointGroup t
    SchemeHomOver gG gG →* SchemeHomOver t gG :=
  letI := LG.pointGroup gG
  letI := LG.pointGroup t
  MonoidHom.mk' (fun E => NeronModelInfra.schemeHomOverComp P E)
    (fun x y => LG.mul_natural gG t P.1 P.2 x y)

theorem pow_eq_nsmulPt (LG : RelativeGroupLaw R gG) {T : Scheme.{u}}
    (t : T ⟶ Spec (CommRingCat.of R)) (P : SchemeHomOver t gG) (n : ℕ) :
    (letI := LG.pointGroup t; P ^ n) = nsmulPt LG t n P := by
  letI := LG.pointGroup t
  induction n with
  | zero => rw [pow_zero]; rfl
  | succ n ih => rw [pow_succ, ih]; rfl

theorem mapPt_eq {T : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of R)} (β : SchemeHomOver gG gH)
    (P : SchemeHomOver t gG) : mapPt β.1 β.2 P = NeronModelInfra.schemeHomOverComp P β := rfl

end Points

section Field

variable {k : Type u} [Field k] {A : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of k)}

theorem connectedSpace_of_bundle (hA : AbelianSchemePropertyBundle k f) : ConnectedSpace A := by
  have h := hA.connectedFibres (IsLocalRing.closedPoint k)
  refine connectedSpace_iff_univ.mpr ?_
  convert h using 1
  exact (Set.eq_univ_of_forall fun x => Subsingleton.elim _ _).symm

theorem nonempty_endKer (L : RelativeGroupLaw k f) (β : SchemeHomOver f f)
    (hβ : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of k)) (x y : SchemeHomOver t f),
      NeronModelInfra.schemeHomOverComp (L.mul t x y) β =
        L.mul t (NeronModelInfra.schemeHomOverComp x β) (NeronModelInfra.schemeHomOverComp y β)) :
    Nonempty (L.endKer β) := by
  have h1 : (L.one (𝟙 (Spec (CommRingCat.of k)))).1 ≫ β.1 =
      𝟙 _ ≫ (L.one (𝟙 (Spec (CommRingCat.of k)))).1 := by
    rw [Category.id_comp]
    exact congrArg Subtype.val (hom_one L L β hβ (𝟙 _))
  exact ⟨(pullback.lift _ _ h1).base (IsLocalRing.closedPoint k)⟩

theorem endDegree_ne_zero_of_isFinite (L : RelativeGroupLaw k f) (β : SchemeHomOver f f)
    (hβ : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of k)) (x y : SchemeHomOver t f),
      NeronModelInfra.schemeHomOverComp (L.mul t x y) β =
        L.mul t (NeronModelInfra.schemeHomOverComp x β) (NeronModelInfra.schemeHomOverComp y β))
    [IsFinite (L.endKerStr β)] : L.endDegree β ≠ 0 := by
  rw [RelativeGroupLaw.endDegree_of_isFinite]
  obtain ⟨x⟩ := nonempty_endKer L β hβ
  have h := Scheme.Hom.one_le_finrank_map (L.endKerStr β) x
  rw [Subsingleton.elim ((L.endKerStr β) x) (IsLocalRing.closedPoint k)] at h
  omega

end Field

section Engine

variable {k : Type u} [Field k] [IsAlgClosed k] {Z : Scheme.{u}} {g : Z ⟶ Spec (CommRingCat.of k)}

theorem false_of_action (LB : RelativeGroupLaw k g) (hc : LB.IsCommutative)
    (hZ : AbelianSchemePropertyBundle k g) [SmoothOfRelativeDimension 1 g]
    {a b : ℚ} {q q' : ℕ} [Fact q.Prime] (hB : IsIndefiniteRamifiedExactlyAt a b q q')
    (Λ : Submodule ℤ ℍ[ℚ, a, b]) (hΛ : IsOrder Λ)
    (ρ : ↥Λ → SchemeHomOver g g)
    (hρhom : ∀ (x : ↥Λ) {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of k)) (P Q : SchemeHomOver t g),
      NeronModelInfra.schemeHomOverComp (LB.mul t P Q) (ρ x) =
        LB.mul t (NeronModelInfra.schemeHomOverComp P (ρ x)) (NeronModelInfra.schemeHomOverComp Q (ρ x)))
    (hρone : ρ ⟨1, hΛ.one_mem⟩ = schemeHomOverId g)
    (hρmul : ∀ x y : ↥Λ, ρ ⟨(x : ℍ[ℚ, a, b]) * y, hΛ.mul_mem x.2 y.2⟩ =
      NeronModelInfra.schemeHomOverComp (ρ y) (ρ x))
    (hρadd : ∀ x y : ↥Λ, ρ (x + y) = LB.mul g (ρ x) (ρ y)) : False := by
  classical
  haveI : IsProper g := hZ.proper
  haveI : Smooth g := hZ.smooth
  haveI : ConnectedSpace Z := connectedSpace_of_bundle hZ
  letI instCG : CommGroup (SchemeHomOver g g) := LB.pointCommGroup hc g

  have hρzero : ρ 0 = 1 := by
    have h := hρadd 0 0
    rw [add_zero] at h
    have h2 : ρ 0 * ρ 0 = ρ 0 * 1 := by rw [mul_one]; exact h.symm
    exact mul_left_cancel h2
  let ρA : ↥Λ →+ Additive (SchemeHomOver g g) :=
    { toFun := fun x => Additive.ofMul (ρ x)
      map_zero' := by rw [hρzero]; rfl
      map_add' := fun x y => hρadd x y }
  have hρA : ∀ x, ρ x = Additive.toMul (ρA x) := fun x => rfl
  have hone_mem : ∀ m : ℕ, ((m : ℚ) : ℍ[ℚ, a, b]) ∈ Λ := fun m => by
    rw [QuaternionAlgebra.coe_natCast, ← Nat.smul_one_eq_cast]; exact nsmul_mem hΛ.one_mem m
  have hρnat : ∀ m : ℕ, ρ ⟨((m : ℚ) : ℍ[ℚ, a, b]), hone_mem m⟩ = schemeHomOverId g ^ m := by
    intro m
    induction m with
    | zero =>
      have h0 : (⟨(((0 : ℕ) : ℚ) : ℍ[ℚ, a, b]), hone_mem 0⟩ : ↥Λ) = 0 := Subtype.ext (by push_cast; rfl)
      rw [h0, hρzero, pow_zero]
    | succ m ih =>
      have h1 : (⟨(((m + 1 : ℕ) : ℚ) : ℍ[ℚ, a, b]), hone_mem (m + 1)⟩ : ↥Λ) =
          ⟨((m : ℚ) : ℍ[ℚ, a, b]), hone_mem m⟩ + ⟨1, hΛ.one_mem⟩ := Subtype.ext (by push_cast; rfl)
      rw [h1, hρadd, ih, hρone, pow_succ]; rfl

  have hquasi : ∀ x : ↥Λ, x ≠ 0 → ∃ (m : ℕ) (y : ↥Λ), 0 < m ∧
      NeronModelInfra.schemeHomOverComp (ρ x) (ρ y) = schemeHomOverId g ^ m ∧
      NeronModelInfra.schemeHomOverComp (ρ y) (ρ x) = schemeHomOverId g ^ m := by
    intro x hx
    have hx' : (x : ℍ[ℚ, a, b]) ≠ 0 := fun h => hx (Subtype.ext h)
    obtain ⟨m, y, hm, hy, hxy, hyx⟩ := P2mKcLambdaSimpleA.exists_quasiInv hB Λ hΛ.spanTop x hx'
    refine ⟨m, ⟨y, hy⟩, hm, ?_, ?_⟩
    · rw [← hρmul ⟨y, hy⟩ x, ← hρnat m]
      congr 1; exact Subtype.ext hyx
    · rw [← hρmul x ⟨y, hy⟩, ← hρnat m]
      congr 1; exact Subtype.ext hxy

  have hsff : ∀ x : ↥Λ, x ≠ 0 → Surjective (ρ x).1 ∧ IsFinite (ρ x).1 ∧ Flat (ρ x).1 := by
    intro x hx
    obtain ⟨m, y, hm, hxy, hyx⟩ := hquasi x hx
    refine CerednikDrinfeld.QM.surjective_and_isFinite_and_flat_of_mapPt_mapPt_eq_nsmulPt LB hc hZ LB hc hZ
      (ρ x).1 (ρ x).2 (fun t P Q => hρhom x t P Q) (ρ y).1 (ρ y).2 m hm ?_ ?_
    · intro T t P
      rw [mapPt_eq, mapPt_eq, NeronModelInfra.schemeHomOverComp_assoc, hxy]
      letI := LB.pointGroup t
      change evalHom LB P (schemeHomOverId g ^ m) = _
      rw [map_pow]
      change NeronModelInfra.schemeHomOverComp P (schemeHomOverId g) ^ m = _
      rw [NeronModelInfra.schemeHomOverComp_id_right, pow_eq_nsmulPt]
    · intro T t P
      rw [mapPt_eq, mapPt_eq, NeronModelInfra.schemeHomOverComp_assoc, hyx]
      letI := LB.pointGroup t
      change evalHom LB P (schemeHomOverId g ^ m) = _
      rw [map_pow]
      change NeronModelInfra.schemeHomOverComp P (schemeHomOverId g) ^ m = _
      rw [NeronModelInfra.schemeHomOverComp_id_right, pow_eq_nsmulPt]

  let Q : ↥Λ → ℕ := fun x => LB.endDegree (ρ x)
  have hQpos : ∀ x : ↥Λ, x ≠ 0 → Q x ≠ 0 := by
    intro x hx
    haveI := (hsff x hx).1
    haveI : IsFinite (LB.endKerStr (ρ x)) :=
      GoodReductionJacobian.RelativeGroupLaw.isFinite_endKerStr_of_surjective k g LB hZ (ρ x)
        (fun t P Q => hρhom x t P Q)
    exact endDegree_ne_zero_of_isFinite LB (ρ x) (fun t P Q => hρhom x t P Q)
  have hQmul : ∀ x y : ↥Λ, x ≠ 0 → y ≠ 0 → Q ⟨(x : ℍ[ℚ, a, b]) * y, hΛ.mul_mem x.2 y.2⟩ = Q x * Q y := by
    intro x y hx hy
    haveI := (hsff x hx).2.1; haveI := (hsff x hx).2.2
    haveI := (hsff y hy).2.1; haveI := (hsff y hy).2.2
    change LB.endDegree _ = LB.endDegree _ * LB.endDegree _
    rw [hρmul, GoodReductionJacobian.RelativeGroupLaw.endDegree_schemeHomOverComp_of_isFinite_of_flat k g LB,
      mul_comm]

  haveI : Module.Finite ℤ ↥Λ := Module.Finite.iff_fg.mpr hΛ.fg
  haveI : IsAddTorsionFree ℍ[ℚ, a, b] := IsAddTorsionFree.of_module_rat _
  haveI : Module.Free ℤ ↥Λ := Module.free_of_finite_type_torsion_free'
  let bΛ := Module.Free.chooseBasis ℤ ↥Λ
  obtain ⟨P, hP, hPev⟩ :=
    GoodReductionJacobian.RelativeGroupLaw.exists_isHomogeneous_eval_eq_endDegree_of_abelianSchemePropertyBundle
      k g LB hc hZ 1 (fun i => ρ (bΛ i)) (@fun i T t P Q => hρhom (bΛ i) t P Q)
  have hQP : ∀ x : ↥Λ, (Q x : ℚ) = MvPolynomial.eval (fun i => ((bΛ.repr x i : ℤ) : ℚ)) P := by
    intro x
    rw [← hPev]
    show ((LB.endDegree (ρ x) : ℕ) : ℚ) = _
    have hx : ρ x = ∏ i, ρ (bΛ i) ^ (bΛ.repr x i : ℤ) := by
      conv_lhs => rw [← bΛ.sum_repr x, hρA, map_sum, toMul_sum]
      refine Finset.prod_congr rfl fun i _ => ?_
      rw [map_zsmul, toMul_zsmul, ← hρA]
    rw [hx]
  exact P2mKcLambdaSimpleA.false_of_quadratic hB Λ hΛ bΛ Q P (by simpa using hP) hQP hQpos hQmul

end Engine

end P2mKcLambdaSimpleB

namespace P2mKcLambdaSimpleC

open P2mKcLambdaSimpleB

section Topology

variable {k : Type u} [Field k] {A : Scheme.{u}}

theorem preimage_base_singleton_eq_univ (f : A ⟶ Spec (CommRingCat.of k)) (s : ↥(Spec (CommRingCat.of k))) :
    f.base ⁻¹' {s} = Set.univ :=
  Set.eq_univ_of_forall fun _ => Subsingleton.elim _ _

theorem topologicalKrullDim_fibre (f : A ⟶ Spec (CommRingCat.of k)) (s : ↥(Spec (CommRingCat.of k))) :
    topologicalKrullDim ↥(f.base ⁻¹' {s}) = topologicalKrullDim A := by
  let e : ↥(f.base ⁻¹' {s}) ≃ₜ A :=
    (Homeomorph.setCongr (preimage_base_singleton_eq_univ f s)).trans (Homeomorph.Set.univ A)
  exact IsHomeomorph.topologicalKrullDim_eq e e.isHomeomorph

theorem topologicalKrullDim_eq_of_smoothOfRelativeDimension (f : A ⟶ Spec (CommRingCat.of k)) (n : ℕ)
    [SmoothOfRelativeDimension n f] [Nonempty A] : topologicalKrullDim A = n :=
  le_antisymm (SmoothOfRelativeDimension.topologicalKrullDim_le f n)
    (SmoothOfRelativeDimension.le_topologicalKrullDim f n)

theorem topologicalKrullDim_range {Z : Scheme.{u}} (i : Z ⟶ A) [IsClosedImmersion i] :
    topologicalKrullDim ↥(Set.range i) = topologicalKrullDim Z :=
  (IsHomeomorph.topologicalKrullDim_eq _ i.isClosedEmbedding.isEmbedding.toHomeomorph.isHomeomorph).symm

theorem subsingleton_of_topologicalKrullDim_le_zero (X : Type u) [TopologicalSpace X] [IrreducibleSpace X]
    [T0Space X] (h : topologicalKrullDim X ≤ 0) : Subsingleton X := by
  rw [topologicalKrullDim, Order.krullDim_nonpos_iff_forall_isMax] at h
  have hgen : ∀ x : X, closure ({x} : Set X) = Set.univ := by
    intro x
    let C : TopologicalSpace.IrreducibleCloseds X :=
      ⟨closure {x}, isIrreducible_singleton.closure, isClosed_closure⟩
    let U : TopologicalSpace.IrreducibleCloseds X :=
      ⟨Set.univ, IrreducibleSpace.isIrreducible_univ X, isClosed_univ⟩
    have hle : C ≤ U := fun _ _ => Set.mem_univ _
    have hUC : (U : Set X) ⊆ C := h C hle
    exact Set.eq_univ_of_univ_subset hUC
  refine ⟨fun x y => ?_⟩
  have hxy : x ⤳ y := by
    rw [specializes_iff_mem_closure, hgen]; exact Set.mem_univ _
  have hyx : y ⤳ x := by
    rw [specializes_iff_mem_closure, hgen]; exact Set.mem_univ _
  exact (hxy.antisymm hyx).eq

end Topology

section Main

variable {q q' : ℕ} [Fact q.Prime] {a b : ℚ}

theorem main_core (hB : IsIndefiniteRamifiedExactlyAt a b q q')
    (Λ : Submodule ℤ ℍ[ℚ, a, b]) (hO : IsOrder Λ) {N : ℕ}
    (k : Type u) [Field k] [IsAlgClosed k] (E : FakeEllipticCurve Λ N k)
    (β : SchemeHomOver E.f E.f)
    (hβ : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of k)) (x y : SchemeHomOver t E.f),
      NeronModelInfra.schemeHomOverComp (E.L.mul t x y) β =
        E.L.mul t (NeronModelInfra.schemeHomOverComp x β) (NeronModelInfra.schemeHomOverComp y β))
    (hact : ∀ x : ↥Λ, E.act x ≫ β.1 = β.1 ≫ E.act x)
    (hne : β ≠ E.L.one E.f)
    {Z : Scheme.{u}} (ιZ : Z ⟶ E.A) [IsClosedImmersion ιZ] {gZ : Z ⟶ Spec (CommRingCat.of k)}
    (hgZ : ιZ ≫ E.f = gZ) (LB : RelativeGroupLaw k gZ) (hZb : AbelianSchemePropertyBundle k gZ)
    (hZc : LB.IsCommutative)
    (hιhom : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of k)) (x y : SchemeHomOver t gZ),
      NeronModelInfra.schemeHomOverComp (LB.mul t x y) (⟨ιZ, hgZ⟩ : SchemeHomOver gZ E.f) =
        E.L.mul t (NeronModelInfra.schemeHomOverComp x ⟨ιZ, hgZ⟩) (NeronModelInfra.schemeHomOverComp y ⟨ιZ, hgZ⟩))
    (hpts : ∀ z : SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap k k))) E.f,
      (∃ b' : SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap k k))) gZ,
          NeronModelInfra.schemeHomOverComp b' (⟨ιZ, hgZ⟩ : SchemeHomOver gZ E.f) = z) ↔
        ∃ y : SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap k k))) E.f,
          NeronModelInfra.schemeHomOverComp y β = z)
    (π : E.A ⟶ Z) (hπ : π ≫ ιZ = β.1) [UniversallyClosed π] [IsDominant π] :
    E.L.endDegree β ≠ 0 := by
  classical

  set ιpt : SchemeHomOver gZ E.f := ⟨ιZ, hgZ⟩ with hιptdef
  haveI : IsProper E.f := E.bundle.proper
  haveI : Smooth E.f := E.bundle.smooth
  haveI : ConnectedSpace E.A := connectedSpace_of_bundle E.bundle
  haveI : IsIntegral E.A := GoodReductionJacobian.AbelianSchemePropertyBundle.isIntegral_of_field E.bundle
  haveI : IsProper gZ := hZb.proper
  haveI : Smooth gZ := hZb.smooth
  haveI : ConnectedSpace Z := connectedSpace_of_bundle hZb
  haveI : IsIntegral Z := GoodReductionJacobian.AbelianSchemePropertyBundle.isIntegral_of_field hZb
  haveI : Nonempty Z := ⟨(LB.one (𝟙 _)).1.base (IsLocalRing.closedPoint k)⟩
  have hinj : ∀ {T : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of k)} (P P' : SchemeHomOver t gZ),
      NeronModelInfra.schemeHomOverComp P ιpt = NeronModelInfra.schemeHomOverComp P' ιpt → P = P' := by
    intro T t P P' h
    have h1 : P.1 ≫ ιZ = P'.1 ≫ ιZ := congrArg Subtype.val h
    exact Subtype.ext ((cancel_mono ιZ).mp h1)

  obtain ⟨d, hd⟩ := GoodReductionJacobian.RelativeGroupLaw.exists_smoothOfRelativeDimension_of_smooth_of_isLocalRing LB
  haveI := hd
  have hdimZ : topologicalKrullDim Z = d := topologicalKrullDim_eq_of_smoothOfRelativeDimension gZ d
  have hdimA : topologicalKrullDim E.A = 2 := by
    rw [← topologicalKrullDim_fibre E.f (IsLocalRing.closedPoint k)]; exact E.dim_fibre _
  have hdle : (d : WithBot ℕ∞) ≤ 2 := by
    rw [← hdimZ, ← hdimA]
    exact Topology.IsInducing.topologicalKrullDim_le ιZ.isClosedEmbedding.isInducing
  have hd2 : d ≤ 2 := by
    have h : ((d : ℕ∞) : WithBot ℕ∞) ≤ ((2 : ℕ∞) : WithBot ℕ∞) := hdle
    have h' : (d : ℕ∞) ≤ (2 : ℕ∞) := WithBot.coe_le_coe.mp h
    exact_mod_cast h'

  by_cases hd2' : d = 2
  · subst hd2'
    have hrange : Set.range ιZ = Set.univ := by
      by_contra hne'
      have h := IsIrreducible.topologicalKrullDim_add_one_le_of_isClosed_of_ne
        (IrreducibleSpace.isIrreducible_univ E.A) ιZ.isClosedEmbedding.isClosed_range (Set.subset_univ _) hne'
      rw [topologicalKrullDim_range ιZ, hdimZ, IsHomeomorph.topologicalKrullDim_eq _ (Homeomorph.Set.univ E.A).isHomeomorph,
        hdimA] at h
      have h' : (((2 : ℕ) : ℕ∞) : WithBot ℕ∞) + 1 ≤ ((2 : ℕ∞) : WithBot ℕ∞) := h
      rw [← WithBot.coe_one, ← WithBot.coe_add, WithBot.coe_le_coe] at h'
      have e3 : (((2 : ℕ) : ℕ∞)) + 1 = ((3 : ℕ) : ℕ∞) := by norm_cast
      rw [e3] at h'
      have h3 : (3 : ℕ) ≤ 2 := by exact_mod_cast h'
      omega
    haveI : Surjective ιZ := ⟨Set.range_eq_univ.mp hrange⟩
    haveI : Surjective π := inferInstance
    haveI : Surjective β.1 := by
      have h : Surjective (π ≫ ιZ) := inferInstance
      rwa [hπ] at h
    haveI : IsFinite (E.L.endKerStr β) :=
      GoodReductionJacobian.RelativeGroupLaw.isFinite_endKerStr_of_surjective k E.f E.L E.bundle β hβ
    exact endDegree_ne_zero_of_isFinite E.L β hβ

  by_cases hd0 : d = 0
  · subst hd0
    exfalso
    apply hne
    haveI : Subsingleton Z := subsingleton_of_topologicalKrullDim_le_zero Z (by rw [hdimZ]; exact le_rfl)
    haveI : LocallyOfFiniteType (β.1 ≫ E.f) := by rw [β.2]; infer_instance
    have hone : ∀ x : E.A, (E.L.one E.f).1 x = ιZ ((LB.one E.f).1 x) := by
      intro x
      have h := congrArg Subtype.val (hom_one LB E.L ιpt hιhom E.f)
      change (LB.one E.f).1 ≫ ιZ = (E.L.one E.f).1 at h
      rw [← h]; rfl
    apply Subtype.ext
    refine ext_of_apply_eq E.f Set.univ isOpen_univ.isLocallyClosed dense_univ (fun x _ _ => ?_) ?_
    · rw [hone x]
      conv_lhs => rw [← hπ]
      change ιZ (π x) = ιZ ((LB.one E.f).1 x)
      rw [Subsingleton.elim (π x) ((LB.one E.f).1 x)]
    · rw [β.2]; exact (E.L.one E.f).2.symm

  obtain rfl : d = 1 := by omega
  exfalso

  have hs₀ : Spec.map (CommRingCat.ofHom (algebraMap k k)) = 𝟙 (Spec (CommRingCat.of k)) := by
    rw [Algebra.algebraMap_self, CommRingCat.ofHom_id]; exact Spec.map_id _

  have hfac : ∀ x : ↥Λ, ∃ ρ₀ : Z ⟶ Z, ρ₀ ≫ ιZ = ιZ ≫ E.act x := by
    intro x
    refine CerednikDrinfeld.QM.exists_comp_eq_of_forall_factorsThrough_of_isReduced k gZ E.f ιZ (ιZ ≫ E.act x)
      (by rw [Category.assoc, E.act_over, hgZ]) fun z => ?_

    let z' : SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap k k))) gZ :=
      ⟨z.1, by rw [hs₀]; exact z.2⟩
    obtain ⟨y, hy⟩ := (hpts (NeronModelInfra.schemeHomOverComp z' ιpt)).mp ⟨z', rfl⟩
    have hy1 : y.1 ≫ β.1 = z.1 ≫ ιZ := congrArg Subtype.val hy

    let yx : SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap k k))) E.f :=
      ⟨y.1 ≫ E.act x, by rw [Category.assoc, E.act_over]; exact y.2⟩
    have hwover : (z.1 ≫ ιZ ≫ E.act x) ≫ E.f = Spec.map (CommRingCat.ofHom (algebraMap k k)) := by
      rw [Category.assoc, Category.assoc, E.act_over, hgZ, hs₀]; exact z.2
    let w : SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap k k))) E.f := ⟨z.1 ≫ ιZ ≫ E.act x, hwover⟩
    have hw : NeronModelInfra.schemeHomOverComp yx β = w := by
      apply Subtype.ext
      change (y.1 ≫ E.act x) ≫ β.1 = z.1 ≫ ιZ ≫ E.act x
      rw [Category.assoc, hact x, ← Category.assoc, hy1, Category.assoc]
    obtain ⟨b', hb'⟩ := (hpts w).mpr ⟨yx, hw⟩
    exact ⟨b'.1, congrArg Subtype.val hb'⟩
  choose ρ₀ hρ₀ using hfac
  have hρover : ∀ x : ↥Λ, ρ₀ x ≫ gZ = gZ := fun x => by
    rw [← hgZ, ← Category.assoc, hρ₀, Category.assoc, E.act_over]
  let ρ : ↥Λ → SchemeHomOver gZ gZ := fun x => ⟨ρ₀ x, hρover x⟩

  have hρι : ∀ (x : ↥Λ) {T : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of k)} (P : SchemeHomOver t gZ),
      NeronModelInfra.schemeHomOverComp (NeronModelInfra.schemeHomOverComp P (ρ x)) ιpt =
        pushPt (E.act x) (E.act_over x) (NeronModelInfra.schemeHomOverComp P ιpt) := by
    intro x T t P
    apply Subtype.ext
    change (P.1 ≫ ρ₀ x) ≫ ιZ = (P.1 ≫ ιZ) ≫ E.act x
    rw [Category.assoc, hρ₀, Category.assoc]
  have hρhom : ∀ (x : ↥Λ) {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of k)) (P Q : SchemeHomOver t gZ),
      NeronModelInfra.schemeHomOverComp (LB.mul t P Q) (ρ x) =
        LB.mul t (NeronModelInfra.schemeHomOverComp P (ρ x)) (NeronModelInfra.schemeHomOverComp Q (ρ x)) := by
    intro x T t P Q
    apply hinj
    rw [hρι, hιhom, hιhom, hρι, hρι]
    exact E.act_hom x t _ _
  have hρone : ρ ⟨1, hO.one_mem⟩ = schemeHomOverId gZ := by
    apply Subtype.ext
    rw [← cancel_mono ιZ]
    change ρ₀ ⟨1, hO.one_mem⟩ ≫ ιZ = 𝟙 Z ≫ ιZ
    rw [hρ₀, E.act_one hO.one_mem, Category.comp_id, Category.id_comp]
  have hρmul : ∀ x y : ↥Λ, ρ ⟨(x : ℍ[ℚ, a, b]) * y, hO.mul_mem x.2 y.2⟩ =
      NeronModelInfra.schemeHomOverComp (ρ y) (ρ x) := by
    intro x y
    apply Subtype.ext
    rw [← cancel_mono ιZ]
    change ρ₀ _ ≫ ιZ = (ρ₀ y ≫ ρ₀ x) ≫ ιZ
    have hr : (ρ₀ y ≫ ρ₀ x) ≫ ιZ = ιZ ≫ E.act y ≫ E.act x := by
      rw [Category.assoc, hρ₀, ← Category.assoc, hρ₀, Category.assoc]
    rw [hr, hρ₀, E.act_mul x y (hO.mul_mem x.2 y.2)]
  have hρadd : ∀ x y : ↥Λ, ρ (x + y) = LB.mul gZ (ρ x) (ρ y) := by
    intro x y
    apply hinj
    have h1 : ∀ w : ↥Λ, NeronModelInfra.schemeHomOverComp (ρ w) ιpt = pushPt (E.act w) (E.act_over w) ιpt := by
      intro w
      have h := hρι w (schemeHomOverId gZ)
      rwa [NeronModelInfra.schemeHomOverComp_id_left, NeronModelInfra.schemeHomOverComp_id_left] at h
    rw [hιhom, h1, h1, h1]
    exact E.act_add x y gZ ιpt
  exact false_of_action LB hZc hZb hB Λ hO ρ hρhom hρone hρmul hρadd

theorem main (hB : IsIndefiniteRamifiedExactlyAt a b q q')
    (Λ : Submodule ℤ ℍ[ℚ, a, b]) (hΛ : IsMaximalOrder Λ) {N : ℕ}
    (k : Type u) [Field k] [IsAlgClosed k] (E : FakeEllipticCurve Λ N k)
    (φ : E.A ⟶ E.A) (hφ : φ ≫ E.f = E.f)
    (hmul : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of k)) (P Q : SchemeHomOver t E.f),
      mapPt φ hφ (E.L.mul t P Q) = E.L.mul t (mapPt φ hφ P) (mapPt φ hφ Q))
    (hact : ∀ x : ↥Λ, E.act x ≫ φ = φ ≫ E.act x)
    (hne : (⟨φ, hφ⟩ : SchemeHomOver E.f E.f) ≠ E.L.one E.f) :
    E.L.endDegree ⟨φ, hφ⟩ ≠ 0 := by
  have hβ : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of k)) (x y : SchemeHomOver t E.f),
      NeronModelInfra.schemeHomOverComp (E.L.mul t x y) ⟨φ, hφ⟩ =
        E.L.mul t (NeronModelInfra.schemeHomOverComp x ⟨φ, hφ⟩) (NeronModelInfra.schemeHomOverComp y ⟨φ, hφ⟩) :=
    fun t x y => hmul t x y
  haveI : IsProper E.f := E.bundle.proper
  haveI : Smooth E.f := E.bundle.smooth
  haveI : ConnectedSpace E.A := connectedSpace_of_bundle E.bundle
  haveI : GeometricallyIntegral E.f :=
    GoodReductionJacobian.AbelianSchemePropertyBundle.geometricallyIntegral E.bundle
  haveI : IsProper φ := by
    have : IsProper (φ ≫ E.f) := by rw [hφ]; infer_instance
    exact IsProper.of_comp φ E.f
  obtain ⟨LB, hZb, hZc, hιhom, hpts⟩ :=
    GoodReductionJacobian.RelativeGroupLaw.exists_relativeGroupLaw_image_of_homomorphism E.L E.bundle E.comm E.L
      ⟨φ, hφ⟩ hβ
  exact main_core hB Λ hΛ.1 k E ⟨φ, hφ⟩ hβ hact hne φ.imageι rfl LB hZb (fun t x y => hZc t x y) hιhom (hpts k)
    φ.toImage φ.toImage_imageι

end Main

end P2mKcLambdaSimpleC

end

set_option linter.unusedVariables false in
open P2mKcLambdaSimpleC in

theorem solution
    {q q' : ℕ} [Fact q.Prime] [Fact q'.Prime] (hqq' : q' ≠ q)
    {a b : ℚ} (hB : IsIndefiniteRamifiedExactlyAt a b q q')
    (Λ : Submodule ℤ ℍ[ℚ, a, b]) (hΛ : IsMaximalOrder Λ) {N : ℕ}
    (k : Type u) [Field k] [IsAlgClosed k] (E : FakeEllipticCurve Λ N k)
    (φ : E.A ⟶ E.A) (hφ : φ ≫ E.f = E.f)
    (hmul : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of k)) (P Q : SchemeHomOver t E.f),
      mapPt φ hφ (E.L.mul t P Q) = E.L.mul t (mapPt φ hφ P) (mapPt φ hφ Q))
    (hact : ∀ x : ↥Λ, E.act x ≫ φ = φ ≫ E.act x)
    (hne : (⟨φ, hφ⟩ : SchemeHomOver E.f E.f) ≠ E.L.one E.f) :
    E.L.endDegree ⟨φ, hφ⟩ ≠ 0 :=
  main hB Λ hΛ k E φ hφ (fun t P Q => hmul t P Q) hact hne

end S_CerednikDrinfeld_QM_FakeEllipticCurve_endDegree_ne_zero_of_forall_act_comp_eq_of_ne_one
end P2MW
export P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_endDegree_ne_zero_of_forall_act_comp_eq_of_ne_one (solution)
