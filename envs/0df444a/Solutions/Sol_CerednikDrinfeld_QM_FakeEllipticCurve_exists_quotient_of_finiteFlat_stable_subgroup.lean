-- Prove2me | solution 1 for CerednikDrinfeld.QM.FakeEllipticCurve.exists_quotient_of_finiteFlat_stable_subgroup
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.141142+00:00
-- url     : https://prove2.me/submissions/4a5fccd8-0f58-52e9-a1ad-462e016af118

import Definitions.Def_CerednikDrinfeld_QMModuli
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawAction
import Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_exists_quotient_abelianSchemePropertyBundle_of_finiteFlat_subgroup_of_affineOrbit_of_commRing
import Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_existsUnique_quotient_desc_hom_of_isColimit
import Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_pushPt_act_natCast_eq_nsmulPt
import Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_exists_isAffineOpen_forall_action_mem_of_nsmulPt_eq_one
import Theorems.Thm_AlgebraicGeometry_topologicalKrullDim_preimage_eq_of_isFinite_of_surjective
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_exists_quotient_of_finiteFlat_stable_subgroup
p2m_attr_erase "instance" "instTopologicallyFGOfFiniteType GoodReductionJacobian.RelativeGroupLaw.isIso_endKerStr_schemeHomOverId AlgebraicGeometry.Scheme.PresheafOfModules.symmetricCategory SheafOfModules.instFaithfulRingSheafPModToPMod SheafOfModules.symmetricCategory AlgebraicGeometry.Scheme.PresheafOfModules.monoidalCategory AlgebraicGeometry.Scheme.PresheafOfModules.monoidalClosed SheafOfModules.instFullRingSheafPModToPMod SheafOfModules.monoidalCategory AlgebraicGeometry.Scheme.Modules.symmetricCategory SheafOfModules.monoidalClosed SheafOfModules.instIsLocalizationPModRingSheafSheafifyFunctorPresheafW SheafOfModules.sheafifyFunctor_monoidal AlgebraicGeometry.Scheme.Modules.monoidalClosed AlgebraicGeometry.instMonoidalPresheafOfModulesModulesSheafify AlgebraicGeometry.Scheme.Modules.monoidalCategory PresheafOfModules.instMonoidalClosed PresheafOfModules.InternalHom.instModuleCarrierObjOppositeCommRingCatSubtypePiFamilyMemAddSubgroupNaturalFamilies PresheafOfModules.InternalHom.instModuleCarrierObjOppositeRingCatCompCommRingCatForget₂RingHomCarrierCarrierAbPresheaf PresheafOfModules.InternalHom.instSMulCarrierObjOppositeCommRingCatSubtypePiFamilyMemAddSubgroupNaturalFamilies AlgebraicGeometry.Scheme.Hom.opensMapFinal AlgebraicGeometry.RelPicard.RigidifiedLineBundle.setoid AlgebraicGeometry.RelPicard.RigidifiedLineBundle.instInhabited AlgebraicGeometry.OModulePresheaf.isScalarTower AlgebraicGeometry.Scheme.OrderedAffineCover.instLinearOrder AlgebraicGeometry.OModulePresheaf.module AlgebraicGeometry.Scheme.OrderedAffineCover.instFintype AlgebraicGeometry.Scheme.OrderedAffineCover.instFintypeIdx AlgebraicGeometry.OModulePresheaf.addCommGroup AlgebraicGeometry.Scheme.OrderedAffineCover.instDecidableEqIdx AlgebraicGeometry.OModulePresheaf.moduleSections TwoChartCech.Sections.M0_moduleA TwoChartCech.Sections.M1_module TwoChartCech.Cover.A01_algebra TwoChartCech.Cover.A0_algebra TwoChartCech.Cover.A1_commRing TwoChartCech.Cover.A1_algebra TwoChartCech.Sections.M01_module TwoChartCech.Sections.M0_addCommGroup TwoChartCech.Sections.M0_tower"
p2m_attr_erase "instance" "TwoChartCech.Sections.M01_addCommGroup TwoChartCech.Cover.A0_commRing TwoChartCech.Sections.M1_tower TwoChartCech.Sections.M01_moduleA TwoChartCech.Sections.M0_module TwoChartCech.Sections.M1_moduleA TwoChartCech.Sections.M1_addCommGroup TwoChartCech.Cover.A01_commRing TwoChartCech.Sections.M01_tower CoherentBaseChange.TwoTermComplex.C0_module CoherentBaseChange.TwoTermComplex.C0_addCommGroup CoherentBaseChange.TwoTermComplex.C1_module CoherentBaseChange.TwoTermComplex.C1_addCommGroup CoherentBaseChange.TwoTermComplex.C0_free CoherentBaseChange.TwoTermComplex.C1_finite CoherentBaseChange.TwoTermComplex.C0_finite CoherentBaseChange.TwoTermComplex.C1_free AlgebraicGeometry.OModulePresheaf.instSubsingletonObjZero AlgebraicGeometry.Scheme.Modules.preservesBinaryProducts_opensMap AlgebraicGeometry.Scheme.Modules.pullback_monoidal AlgebraicGeometry.Scheme.Modules.sheafify_isLocalization' AlgebraicGeometry.Scheme.Modules.preservesTerminal_opensMap AlgebraicGeometry.Scheme.Modules.pullback₀_monoidal AlgebraicGeometry.Scheme.Modules.preservesFiniteProducts_opensMap AlgebraicGeometry.Scheme.Modules.instLiftingPresheafOfModulesSheafifyPresheafWOpensCarrierCarrierCommRingCatGrothendieckTopologyObjFunctorOppositeIsSheafSheafCompPullback₀Pullback PresheafOfModules.PullbackMonoidal.pullback_monoidal PresheafOfModules.PullbackMonoidal.isIso_δ PresheafOfModules.pushforward_laxMonoidal PresheafOfModules.PullbackMonoidal.isIso_η PresheafOfModules.free_monoidal PresheafOfModules.restrictScalars_laxMonoidal PresheafOfModules.PullbackMonoidal.isIso_δ_gS PresheafOfModules.pullback_oplaxMonoidal PresheafOfModules.PullbackMonoidal.instPreservesColimitsOfSizeCompOppositeCommRingCatRingCatForget₂RingHomCarrierCarrierPb PresheafOfModules.pullback_monoidal' AlgebraicGeometry.SmoothOfRelativeDimension.fiberToSpecResidueField AlgebraicGeometry.SmoothOfRelativeDimension.pullback_snd AlgebraicGeometry.SmoothOfRelativeDimension.pullback_fst AlgebraicGeometry.SmoothOfRelativeDimension.smooth_one AlgebraicGeometry.SmoothProperCurve.isIntegral_pullback_Spec_field"
p2m_attr_erase "instance" "AlgebraicGeometry.IsProper.fiberToSpecResidueField AlgebraicCurve.CurveModel.isProper AlgebraicCurve.CurveModel.isIntegral AlgebraicCurve.CurveModel.smooth AlgebraicGeometry.Scheme.LocalRepresentabilityULift.instIsLocallyInjectiveFunUliftYonedaGluedToSheaf AlgebraicGeometry.Scheme.LocalRepresentabilityULift.instIsLocallySurjectiveFunUliftYonedaGluedToSheafOfIsLocallySurjectiveZariskiTopologyDescFunctorOppositeType AlgebraicGeometry.Scheme.LocalRepresentabilityULift.instIsOpenImmersionToGlued AlgebraicGeometry.Scheme.LocalRepresentabilityULift.instIsIsoSheafZariskiTopologyTypeUliftYonedaGluedToSheaf AlgebraicGeometry.RelPicard.instIsOpenImmersionToGlued AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.instFundamentalIdentityOfSumRamificationInertia AlgebraicCurve.Place.instIsScalarTowerResidueFieldRestrictPushforward AlgebraicCurve.Place.instAlgebraResidueFieldRestrictPushforward AlgebraicCurve.Place.instIsLocalHomRestrictInclusion AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions PresheafOfModules.ExteriorPower.instModulePresheafAb AlgebraicGeometry.RelEffCartierDiv.subsingleton_of_degree_zero AlgebraicGeometry.RelEffCartierDiv.isIso_subschemeIota_snd_of_degree_one AlgebraicGeometry.isIso_ker_graphOver_subschemeIota_snd AlgebraicGeometry.isClosedImmersion_graphOver AlgebraicGeometry.FGSubalgebra.instIsDirectedLe AlgebraicGeometry.FGSubalgebra.instQuasiSeparatedSpaceCarrierCarrierCommRingCatObjOppositeSchemeSpecDiagram AlgebraicGeometry.FGSubalgebra.instIsCofilteredOpposite AlgebraicGeometry.FGSubalgebra.instIsAffineObjOppositeSchemeSpecDiagram AlgebraicGeometry.FGSubalgebra.instNonempty AlgebraicGeometry.FGSubalgebra.instNonemptySubtypeLeSubalgebraValFG AlgebraicGeometry.FGSubalgebra.instCompactSpaceCarrierCarrierCommRingCatObjOppositeSchemeSpecDiagram AlgebraicGeometry.FGSubalgebra.instIsDirectedSubtypeLeSubalgebraValFG AlgebraicGeometry.FGSubalgebra.instIsAffineHomMapOppositeSchemeSpecDiagram AlgebraicGeometry.FGSubalgebra.instIsFiltered AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instNeg AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instSMulInt AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instAddCommGroup AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instAdd"
p2m_attr_erase "instance" "AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instSub AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instModuleCarrierObjOppositeOpensCarrierCarrierCommRingCatPresheafOpOpensTop AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instSMulCarrierObjOppositeOpensCarrierCarrierCommRingCatPresheafOpOpensTop AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instSMulNat AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instZero AlgebraicCurve.instHasLocalResidue_of_hasCanonicalLocalResidueK AlgebraicCurve.instHasCanonicalLocalResidueK_of_hasCanonicalLocalResidueKStar AlgebraicCurve.Place.kw_ffgc_finiteDimensional_adicCompletion instAlgebraSubtypeMemValuationSubring_definitions AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersIntegersCompletion ModularCurve.KwF4gRRTate.instAlgebraKAdicCompletionIntegers AlgebraicCurve.Place.kw_ffgc_continuousSMul_adicCompletionComap AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersCompletionCompletion IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions AlgebraicCurve.instHasCanonicalLocalResidueK AlgebraicCurve.Place.instAlgebra_restrictResidueField AlgebraicCurve.Place.instIsScalarTower_restrictResidueField AlgebraicCurve.instHasLocalResidue AlgebraicCurve.HasSeparableResidue.of_perfectField_of_isCurveOver AlgebraicCurve.HasSeparableResidue.of_perfectField AlgebraicCurve.Place.instIsLocalHom_restrictSubringHom AlgebraicCurve.instHasCanonicalLocalResidueKStar ModularCurve.KwNo6Pin.isLocalRing_completion SheafOfModules.isIso_ihomModelToIhom AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instDecidableEqIdx AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instFintype AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instLinearOrder AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instFintypeIdx AlgebraicGeometry.OModulePresheaf.Leray.relAltC_scalarTower AlgebraicGeometry.OModulePresheaf.Leray.ker_relAltd_modΓ AlgebraicGeometry.OModulePresheaf.Leray.relAltC_modΓ AlgebraicGeometry.OModulePresheaf.Leray.biC_abGrp AlgebraicGeometry.OModulePresheaf.Leray.relAltH_modΓ AlgebraicGeometry.OModulePresheaf.Leray.ker_relAltd_smul AlgebraicGeometry.OModulePresheaf.Leray.relAltH_scalarTower"
p2m_attr_erase "instance" "AlgebraicGeometry.OModulePresheaf.Leray.relAltH_smul AlgebraicGeometry.OModulePresheaf.Leray.biC_module DoubleComplex.instModuleE₂I DoubleComplex.Bounded.modR DoubleComplex.instModuleE₂II DoubleComplex.instAddCommGroupE₂II DoubleComplex.Bounded.abGrp DoubleComplex.instAddCommGroupE₂I AlgebraicGeometry.ChowDatum.hι_closed AlgebraicGeometry.ChowDatumProj.hιN_closed AlgebraicGeometry.ChowDatumProj.hp_proper AlgebraicGeometry.ChowDatum.hp_isoU AlgebraicGeometry.ChowDatum.hp_proper AlgebraicGeometry.ProjSpace.algebraAway AlgebraicGeometry.ProjSpace.instIsProperProdOverπ AlgebraicGeometry.ChowDatumProj.hp_isoU AlgebraicGeometry.ProjSpace.isProper_π AlgebraicGeometry.ProjSpace.finiteType_mvPolynomial ProjSpaceCech.GradedModule.H.module ProjSpaceCech.GradedModule.H.addCommGroup ProjSpaceCech.GradedModule.sec.instAdd ProjSpaceCech.GradedModule.sec.instNeg ProjSpaceCech.GradedModule.acg ProjSpaceCech.GradedModule.Frac.setoid ProjSpaceCech.GradedModule.modR ProjSpaceCech.GradedModule.sec.instModule ProjSpaceCech.GradedModule.sec.instAddCommGroup ProjSpaceCech.GradedModule.sec.instZero ProjSpaceCech.GradedModule.Presentation.fJ ProjSpaceCech.GradedModule.sec.instSMul ProjSpaceCech.Twist.H.module ProjSpaceCech.Idx.instFintype ProjSpaceCech.Twist.H.addCommGroup ProjSpaceCech.Idx.instDecidableEq ProjSpaceCech.Twist.Mon.instDecidableEq ProjSpaceCech.Twist.cochain.instAddCommGroup ProjSpaceCech.Twist.cochain.instModule AlgebraicGeometry.FGSubalgebra.tensorStage_directedSystem AlgebraicGeometry.RelEffCartierDiv.isClosedImmersion_subschemeι_resProdMap AlgebraicGeometry.RelEffCartierDiv.isOpenImmersion_resProdMap"
p2m_attr_erase "instance" "AlgebraicCurve.CurveModel.locallyOfFiniteType_gluedToBase AlgebraicCurve.CurveModel.isFractionRing_overlap AlgebraicCurve.CurveModel.isLocallyNoetherian_glued AlgebraicCurve.CurveModel.jacobsonSpace_glued AlgebraicCurve.CurveModel.isOpenImmersion_ι₀ AlgebraicCurve.CurveModel.isIntegral_glued AlgebraicCurve.CurveModel.quasiSeparated_gluedToBase AlgebraicCurve.CurveModel.compactSpace_glued AlgebraicCurve.CurveModel.isIntegral_adjoin_chartRing AlgebraicCurve.CurveModel.isFractionRing_overlap_functionField AlgebraicCurve.CurveModel.isProper_gluedToBase AlgebraicCurve.CurveModel.isOpenImmersion_ιU AlgebraicCurve.CurveModel.isOpenImmersion_f₀ AlgebraicCurve.CurveModel.isOpenImmersion_fInf AlgebraicCurve.CurveModel.isOpenImmersion_ιInf AlgebraicCurve.CurveModel.algebra_overlap_functionField AlgebraicCurve.CurveModel.quasiCompact_gluedToBase AlgebraicCurve.CurveModel.algebraAdjoin AlgebraicCurve.CurveModel.isDedekindDomain_chartRing AlgebraicCurve.CurveModel.isIntegralClosure AlgebraicCurve.CurveModel.finite_chartRing AlgebraicCurve.CurveModel.centre_isPrime AlgebraicCurve.CurveModel.isFractionRing_chartRing AlgebraicCurve.CurveModel.finiteType_chartRing AlgebraicCurve.CurveModel.isNoetherianRing_chartRing AlgebraicCurve.CurveModel.isScalarTower_base_adjoin AlgebraicCurve.CurveModel.isScalarTower_adjoin AlgebraicCurve.CurveModel.chartRing_finitePresentation AlgebraicGeometry.ProjSpace.twistObj.addCommGroup AlgebraicGeometry.ProjSpace.twistFam.module AlgebraicGeometry.ProjSpace.twistObj.module AlgebraicGeometry.ProjSpace.twistObj.moduleSections AlgebraicGeometry.ProjSpace.twistFam.addCommGroup"
p2m_attr_erase "simp" "GoodReductionJacobian.RelativeGroupLaw.fibre_inv GoodReductionJacobian.RelativeGroupLaw.fibrePointToBase_coe GoodReductionJacobian.RelativeGroupLaw.fibrePointOfBase_toBase GoodReductionJacobian.RelativeGroupLaw.fibre_mul GoodReductionJacobian.RelativeGroupLaw.fibrePointToBase_ofBase GoodReductionJacobian.RelativeGroupLaw.fibre_one GoodReductionJacobian.RelativeGroupLaw.fibrePointOfBase_coe GoodReductionJacobian.relativeGroupLawOfGrpObj_inv GoodReductionJacobian.relativeGroupLawOfGrpObj_mul GoodReductionJacobian.overHomEquivSchemeHomOver_apply_coe GoodReductionJacobian.relativeGroupLawOfGrpObj_one GoodReductionJacobian.overHomEquivSchemeHomOver_symm_apply_left CerednikDrinfeld.QM.FakeEllipticCurve.ExtraLevel.mk.injEq CerednikDrinfeld.QM.FakeEllipticCurve.ExtraLevel.mk.sizeOf_spec RegularLocalRingQuotientAscent.dualNumberFst_apply GoodReductionJacobian.RelativeGroupLaw.baseChangePointToBase_ofBase GoodReductionJacobian.RelativeGroupLaw.baseChangePointToBase_coe GoodReductionJacobian.RelativeGroupLaw.baseChangePointOfBase_coe GoodReductionJacobian.RelativeGroupLaw.baseChange_inv GoodReductionJacobian.RelativeGroupLaw.baseChangePointOfBase_toBase GoodReductionJacobian.RelativeGroupLaw.baseChange_mul GoodReductionJacobian.RelativeGroupLaw.baseChange_one NeronModelInfra.NeronModelPropertyBundle.endExtensionEquiv_symm_restrict NeronModelInfra.schemeHomOverComp_id_left NeronModelInfra.schemeHomOverComp_id_right NeronModelInfra.schemeHomOverId_coe NeronModelInfra.NeronModelPropertyBundle.endExtensionEquiv_apply NeronModelInfra.NeronModelPropertyBundle.restrict_endExtensionEquiv_symm NeronModelInfra.schemeHomOverComp_coe NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_fst NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_snd NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_fst NeronSpecialFibreInfra.neronEndRestrictEquiv_apply NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_fst_assoc NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_snd NeronSpecialFibreInfra.neronEndExtension_genericFibreRestrict NeronSpecialFibreInfra.specClosedFibreInclusion_eq NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_fst_assoc NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_snd_assoc NeronSpecialFibreInfra.genericFibreRestrict_neronEndExtension"
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

open scoped TensorProduct Quaternion NumberField
p2m_open "CategoryTheory CategoryTheory.Limits AlgebraicGeometry QuaternionAlgebra CerednikDrinfeld CerednikDrinfeld.QM NeronModelInfra~schemeHomOverComp GoodReductionJacobian"

universe u

namespace QuotFwd

variable {R : Type u} [CommRing R]

theorem mapPt_comp {A A' A'' : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of R)} {f' : A' ⟶ Spec (CommRingCat.of R)}
    {f'' : A'' ⟶ Spec (CommRingCat.of R)} (φ : A ⟶ A') (hφ : φ ≫ f' = f) (ψ : A' ⟶ A'') (hψ : ψ ≫ f'' = f')
    {h : (φ ≫ ψ) ≫ f'' = f} {T : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of R)} (P : SchemeHomOver t f) :
    mapPt (φ ≫ ψ) h P = mapPt ψ hψ (mapPt φ hφ P) := by
  apply Subtype.ext; simp [mapPt, Category.assoc]

theorem nsmulPt_eq_nsmul {A : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of R)}
    (L : RelativeGroupLaw R f) {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (n : ℕ) (P : SchemeHomOver t f) :
    nsmulPt L t n P = L.nsmul t n P := by
  induction n with
  | zero => rfl
  | succ n ih => rw [GoodReductionJacobian.RelativeGroupLaw.nsmul_succ, ← ih]; rfl

def IsHom {X Y : Scheme.{u}} {gX : X ⟶ Spec (CommRingCat.of R)} {gY : Y ⟶ Spec (CommRingCat.of R)}
    (LX : RelativeGroupLaw R gX) (LY : RelativeGroupLaw R gY) (α : SchemeHomOver gX gY) : Prop :=
  ∀ ⦃T : Scheme.{u}⦄ (t : T ⟶ Spec (CommRingCat.of R)) (u v : SchemeHomOver t gX),
    mapPt α.1 α.2 (LX.mul t u v) = LY.mul t (mapPt α.1 α.2 u) (mapPt α.1 α.2 v)

theorem IsHom.comp {X Y Z : Scheme.{u}} {gX : X ⟶ Spec (CommRingCat.of R)} {gY : Y ⟶ Spec (CommRingCat.of R)}
    {gZ : Z ⟶ Spec (CommRingCat.of R)} {LX : RelativeGroupLaw R gX} {LY : RelativeGroupLaw R gY} {LZ : RelativeGroupLaw R gZ}
    {α : SchemeHomOver gX gY} {β : SchemeHomOver gY gZ} (hα : IsHom LX LY α) (hβ : IsHom LY LZ β) :
    IsHom LX LZ ⟨α.1 ≫ β.1, by rw [Category.assoc, β.2, α.2]⟩ := by
  intro T t u v
  show mapPt (α.1 ≫ β.1) _ (LX.mul t u v) = LZ.mul t (mapPt (α.1 ≫ β.1) _ u) (mapPt (α.1 ≫ β.1) _ v)
  rw [mapPt_comp α.1 α.2 β.1 β.2, hα, hβ, ← mapPt_comp α.1 α.2 β.1 β.2, ← mapPt_comp α.1 α.2 β.1 β.2]

theorem IsHom.map_one {X Y : Scheme.{u}} {gX : X ⟶ Spec (CommRingCat.of R)} {gY : Y ⟶ Spec (CommRingCat.of R)}
    {LX : RelativeGroupLaw R gX} {LY : RelativeGroupLaw R gY} {α : SchemeHomOver gX gY} (hα : IsHom LX LY α)
    {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) : mapPt α.1 α.2 (LX.one t) = LY.one t := by
  have h := hα t (LX.one t) (LX.one t)
  rw [LX.one_mul] at h
  have := congrArg (LY.mul t (LY.inv t (mapPt α.1 α.2 (LX.one t)))) h
  rw [← LY.mul_assoc, LY.inv_mul_cancel, LY.one_mul] at this
  exact this.symm

theorem IsHom.map_nsmulPt {X Y : Scheme.{u}} {gX : X ⟶ Spec (CommRingCat.of R)} {gY : Y ⟶ Spec (CommRingCat.of R)}
    {LX : RelativeGroupLaw R gX} {LY : RelativeGroupLaw R gY} {α : SchemeHomOver gX gY} (hα : IsHom LX LY α)
    {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (n : ℕ) (P : SchemeHomOver t gX) :
    mapPt α.1 α.2 (nsmulPt LX t n P) = nsmulPt LY t n (mapPt α.1 α.2 P) := by
  induction n with
  | zero => exact hα.map_one t
  | succ n ih => simp only [nsmulPt]; rw [hα, ih]

theorem IsHom.map_inv {X Y : Scheme.{u}} {gX : X ⟶ Spec (CommRingCat.of R)} {gY : Y ⟶ Spec (CommRingCat.of R)}
    {LX : RelativeGroupLaw R gX} {LY : RelativeGroupLaw R gY} {α : SchemeHomOver gX gY} (hα : IsHom LX LY α)
    {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (P : SchemeHomOver t gX) :
    mapPt α.1 α.2 (LX.inv t P) = LY.inv t (mapPt α.1 α.2 P) := by
  letI := LY.pointGroup t
  have h := hα t (LX.inv t P) P
  rw [LX.inv_mul_cancel, hα.map_one] at h
  exact (inv_eq_of_mul_eq_one_left h.symm).symm

theorem topologicalKrullDim_fibre_eq {S : Type u} [CommRing S] {X Y : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of S)) (g : Y ⟶ Spec (CommRingCat.of S))
    (p : X ⟶ Y) (hp : p ≫ g = f) [IsFinite p] [Surjective p] (s : ↥(Spec (CommRingCat.of S))) :
    topologicalKrullDim ↥(g.base ⁻¹' {s}) = topologicalKrullDim ↥(f.base ⁻¹' {s}) := by
  classical

  let k : Type u := ↥((Spec (CommRingCat.of S)).residueField s)
  let Ys : Scheme.{u} := g.fiber s
  let gs : Ys ⟶ Spec (CommRingCat.of k) := g.fiberToSpecResidueField s
  let Xs : Scheme.{u} := pullback p (g.fiberι s)
  let ps : Xs ⟶ Ys := pullback.snd p (g.fiberι s)
  let fs : Xs ⟶ Spec (CommRingCat.of k) := ps ≫ gs
  haveI : IsFinite ps := inferInstance
  haveI : Surjective ps := inferInstance

  let s₀ : ↥(Spec (CommRingCat.of k)) := default
  have hfield := AlgebraicGeometry.topologicalKrullDim_preimage_eq_of_isFinite_of_surjective fs gs ps rfl s₀

  have hY1 : gs.base ⁻¹' {s₀} = Set.univ := by
    ext y; simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_univ, iff_true]; exact Subsingleton.elim _ _
  have hX1 : fs.base ⁻¹' {s₀} = Set.univ := by
    ext y; simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_univ, iff_true]; exact Subsingleton.elim _ _
  have eY : topologicalKrullDim ↥(gs.base ⁻¹' {s₀}) = topologicalKrullDim ↥(g.base ⁻¹' {s}) := by
    have h1 := IsHomeomorph.topologicalKrullDim_eq _ ((Homeomorph.setCongr hY1).trans (Homeomorph.Set.univ Ys)).isHomeomorph
    have h2 := IsHomeomorph.topologicalKrullDim_eq _ (g.fiberHomeo s).isHomeomorph
    exact h1.trans h2
  have eX : topologicalKrullDim ↥(fs.base ⁻¹' {s₀}) = topologicalKrullDim ↥(f.base ⁻¹' {s}) := by
    have h1 := IsHomeomorph.topologicalKrullDim_eq _ ((Homeomorph.setCongr hX1).trans (Homeomorph.Set.univ Xs)).isHomeomorph

    let e1 : Xs ≅ pullback (p ≫ g) ((Spec (CommRingCat.of S)).fromSpecResidueField s) :=
      pullbackRightPullbackFstIso g ((Spec (CommRingCat.of S)).fromSpecResidueField s) p
    let e2 : pullback (p ≫ g) ((Spec (CommRingCat.of S)).fromSpecResidueField s) ≅ f.fiber s :=
      pullback.congrHom hp rfl
    have h2 := IsHomeomorph.topologicalKrullDim_eq _ (Scheme.homeoOfIso (e1 ≪≫ e2)).isHomeomorph
    have h3 := IsHomeomorph.topologicalKrullDim_eq _ (f.fiberHomeo s).isHomeomorph
    exact h1.trans (h2.trans h3)
  rw [← eY, ← eX]; exact hfield

end QuotFwd

theorem solution
    {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} {N : ℕ} {S : Type u} [CommRing S]
    (E : FakeEllipticCurve Λ N S) {K : Scheme.{u}} (κ : K ⟶ E.A) [IsClosedImmersion κ]
    [IsFinite (κ ≫ E.f)] [Flat (κ ≫ E.f)] [LocallyOfFinitePresentation (κ ≫ E.f)]
    (hK_one : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of S)), FactorsThrough κ (E.L.one t))
    (hK_sub : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of S)) (P Q : SchemeHomOver t E.f),
      FactorsThrough κ P → FactorsThrough κ Q → FactorsThrough κ (E.L.mul t P Q) ∧ FactorsThrough κ (E.L.inv t P))
    (hK_stable : ∀ (x : ↥Λ) {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of S)) (P : SchemeHomOver t E.f),
      FactorsThrough κ P → FactorsThrough κ (pushPt (E.act x) (E.act_over x) P))
    (n : ℕ) (hn : 0 < n) (hone : (1 : ℍ[ℚ, a, b]) ∈ Λ)
    (hK_tors : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of S)) (P : SchemeHomOver t E.f),
      FactorsThrough κ P → nsmulPt E.L t n P = E.L.one t) :
    ∃ (A' : Scheme.{u}) (f' : A' ⟶ Spec (CommRingCat.of S)) (L' : RelativeGroupLaw S f')
      (act' : ↥Λ → (A' ⟶ A')) (act'_over : ∀ x : ↥Λ, act' x ≫ f' = f')
      (p : E.A ⟶ A') (hp : p ≫ f' = E.f) (ψ : A' ⟶ E.A) (hψ : ψ ≫ E.f = f')
      (w : pullback.snd (κ ≫ E.f) E.f ≫ p = E.L.action κ ≫ p),

      L'.IsCommutative ∧ AbelianSchemePropertyBundle S f' ∧
      (∀ s : ↥(Spec (CommRingCat.of S)), topologicalKrullDim ↥(f'.base ⁻¹' {s}) = 2) ∧

      (∀ (x : ↥Λ) {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of S)) (P Q : SchemeHomOver t f'),
        pushPt (act' x) (act'_over x) (L'.mul t P Q) =
          L'.mul t (pushPt (act' x) (act'_over x) P) (pushPt (act' x) (act'_over x) Q)) ∧
      (∀ h : (1 : ℍ[ℚ, a, b]) ∈ Λ, act' ⟨1, h⟩ = 𝟙 A') ∧
      (∀ (x y : ↥Λ) (h : (x : ℍ[ℚ, a, b]) * (y : ℍ[ℚ, a, b]) ∈ Λ),
        act' ⟨(x : ℍ[ℚ, a, b]) * (y : ℍ[ℚ, a, b]), h⟩ = act' y ≫ act' x) ∧
      (∀ (x y : ↥Λ) {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of S)) (P : SchemeHomOver t f'),
        pushPt (act' (x + y)) (act'_over (x + y)) P =
          L'.mul t (pushPt (act' x) (act'_over x) P) (pushPt (act' y) (act'_over y) P)) ∧

      (∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of S)) (P Q : SchemeHomOver t E.f),
        mapPt p hp (E.L.mul t P Q) = L'.mul t (mapPt p hp P) (mapPt p hp Q)) ∧
      (∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of S)) (P Q : SchemeHomOver t f'),
        mapPt ψ hψ (L'.mul t P Q) = E.L.mul t (mapPt ψ hψ P) (mapPt ψ hψ Q)) ∧
      (∀ x : ↥Λ, E.act x ≫ p = p ≫ act' x) ∧ (∀ x : ↥Λ, act' x ≫ ψ = ψ ≫ E.act x) ∧
      (∀ hn_mem : ((n : ℚ) : ℍ[ℚ, a, b]) ∈ Λ,
        p ≫ ψ = E.act ⟨((n : ℚ) : ℍ[ℚ, a, b]), hn_mem⟩ ∧ ψ ≫ p = act' ⟨((n : ℚ) : ℍ[ℚ, a, b]), hn_mem⟩) ∧
      (∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of S)) (P : SchemeHomOver t E.f),
        mapPt ψ hψ (mapPt p hp P) = nsmulPt E.L t n P) ∧
      (∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of S)) (Q : SchemeHomOver t f'),
        mapPt p hp (mapPt ψ hψ Q) = nsmulPt L' t n Q) ∧

      IsFinite p ∧ Flat p ∧ LocallyOfFinitePresentation p ∧ Surjective p ∧
      (∀ y : ↥A', p.finrank y = (κ ≫ E.f).finrank (f'.base y)) ∧
      (∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of S)) (P : SchemeHomOver t E.f),
        mapPt p hp P = L'.one t ↔ FactorsThrough κ P) ∧

      (∀ {X : Scheme.{u}} {gX : X ⟶ Spec (CommRingCat.of S)} (LX : RelativeGroupLaw S gX)
        (φ : E.A ⟶ X) (hφ : φ ≫ gX = E.f),
        (∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of S)) (P Q : SchemeHomOver t E.f),
          mapPt φ hφ (E.L.mul t P Q) = LX.mul t (mapPt φ hφ P) (mapPt φ hφ Q)) →
        (∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of S)) (P : SchemeHomOver t E.f),
          FactorsThrough κ P → mapPt φ hφ P = LX.one t) →
        ∃! χ : SchemeHomOver f' gX, p ≫ χ.1 = φ ∧
          ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of S)) (P Q : SchemeHomOver t f'),
            mapPt χ.1 χ.2 (L'.mul t P Q) = LX.mul t (mapPt χ.1 χ.2 P) (mapPt χ.1 χ.2 Q)) ∧

      CategoryTheory.IsPullback (pullback.snd (κ ≫ E.f) E.f) (E.L.action κ) p p ∧
        Nonempty (IsColimit (Cofork.ofπ p w)) := by
  classical

  have hmul : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of S)) (x y : SchemeHomOver t E.f),
      (∃ e₁ : T ⟶ K, e₁ ≫ κ = x.1) → (∃ e₂ : T ⟶ K, e₂ ≫ κ = y.1) → ∃ e : T ⟶ K, e ≫ κ = (E.L.mul t x y).1 :=
    fun t x y hx hy => (hK_sub t x y hx hy).1
  have hinv : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of S)) (x : SchemeHomOver t E.f),
      (∃ e₁ : T ⟶ K, e₁ ≫ κ = x.1) → ∃ e : T ⟶ K, e ≫ κ = (E.L.inv t x).1 :=
    fun t x hx => (hK_sub t x x hx hx).2
  have haff : ∀ x : E.A, ∃ U : E.A.Opens, IsAffineOpen U ∧
      ∀ r : ↑(pullback (κ ≫ E.f) E.f), (pullback.snd (κ ≫ E.f) E.f) r = x → (E.L.action κ) r ∈ U :=
    fun x => CerednikDrinfeld.QM.FakeEllipticCurve.exists_isAffineOpen_forall_action_mem_of_nsmulPt_eq_one
      E κ n hn (fun t P hP => hK_tors t P hP) x

  obtain ⟨P, g, LP, p, hg, w, hbundle, hcommP, hfin, hflat, hlfp, hsurj, hhom, hker, hpb, ⟨hcolim⟩⟩ :=
    GoodReductionJacobian.RelativeGroupLaw.exists_quotient_abelianSchemePropertyBundle_of_finiteFlat_subgroup_of_affineOrbit_of_commRing
      E.L E.bundle E.comm κ hK_one hmul hinv haff
  haveI := hfin
  haveI := hflat
  haveI := hlfp
  haveI := hsurj
  have hhom' : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of S)) (x y : SchemeHomOver t E.f),
      mapPt p hg (E.L.mul t x y) = LP.mul t (mapPt p hg x) (mapPt p hg y) := fun t x y => hhom t x y

  have hdesc_act : ∀ x : ↥Λ, ∃! ψ : SchemeHomOver g g, p ≫ ψ.1 = E.act x ≫ p ∧
      ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of S)) (u v : SchemeHomOver t g),
        (⟨(LP.mul t u v).1 ≫ ψ.1, by rw [Category.assoc, ψ.2, (LP.mul t u v).2]⟩ : SchemeHomOver t g) =
          LP.mul t ⟨u.1 ≫ ψ.1, by rw [Category.assoc, ψ.2, u.2]⟩ ⟨v.1 ≫ ψ.1, by rw [Category.assoc, ψ.2, v.2]⟩ := by
    intro x
    refine GoodReductionJacobian.RelativeGroupLaw.existsUnique_quotient_desc_hom_of_isColimit E.L κ p w hcolim hg LP
      hhom LP ⟨E.act x ≫ p, by rw [Category.assoc, hg, E.act_over]⟩ ?_ ?_
    · intro T t x' y'
      have h1 := congrArg (mapPt p hg) (E.act_hom x t x' y')
      rw [hhom'] at h1
      have e1 : ∀ (z : SchemeHomOver t E.f),
          (⟨z.1 ≫ (E.act x ≫ p), by rw [Category.assoc, Category.assoc, hg, E.act_over, z.2]⟩ : SchemeHomOver t g) =
            mapPt p hg (pushPt (E.act x) (E.act_over x) z) := by
        intro z; apply Subtype.ext; simp [mapPt, pushPt, Category.assoc]
      rw [e1, e1, e1]; exact h1
    · intro T t e he
      have hfac : FactorsThrough κ (pushPt (E.act x) (E.act_over x)
          (⟨e ≫ κ, by rw [Category.assoc]; exact he⟩ : SchemeHomOver t E.f)) :=
        hK_stable x t _ ⟨e, rfl⟩
      obtain ⟨e', he'⟩ := hfac
      have := (hker t (pushPt (E.act x) (E.act_over x)
        (⟨e ≫ κ, by rw [Category.assoc]; exact he⟩ : SchemeHomOver t E.f))).2 ⟨e', he'⟩
      refine Eq.trans ?_ this
      apply Subtype.ext; simp [mapPt, pushPt, Category.assoc]
  choose actP hactP using hdesc_act
  have hpact : ∀ x : ↥Λ, p ≫ (actP x).1 = E.act x ≫ p := fun x => (hactP x).1.1
  have hactP_hom : ∀ (x : ↥Λ) {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of S)) (u v : SchemeHomOver t g),
      (⟨(LP.mul t u v).1 ≫ (actP x).1, by rw [Category.assoc, (actP x).2, (LP.mul t u v).2]⟩ : SchemeHomOver t g) =
        LP.mul t ⟨u.1 ≫ (actP x).1, by rw [Category.assoc, (actP x).2, u.2]⟩
          ⟨v.1 ≫ (actP x).1, by rw [Category.assoc, (actP x).2, v.2]⟩ :=
    fun x => (hactP x).1.2
  have hactP_uniq : ∀ (x : ↥Λ) (ψ : SchemeHomOver g g), p ≫ ψ.1 = E.act x ≫ p →
      (∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of S)) (u v : SchemeHomOver t g),
        (⟨(LP.mul t u v).1 ≫ ψ.1, by rw [Category.assoc, ψ.2, (LP.mul t u v).2]⟩ : SchemeHomOver t g) =
          LP.mul t ⟨u.1 ≫ ψ.1, by rw [Category.assoc, ψ.2, u.2]⟩ ⟨v.1 ≫ ψ.1, by rw [Category.assoc, ψ.2, v.2]⟩) →
      ψ = actP x := fun x ψ h1 h2 => (hactP x).2 ψ ⟨h1, h2⟩

  have hnΛ : ((n : ℚ) : ℍ[ℚ, a, b]) ∈ Λ := by
    have : ((n : ℚ) : ℍ[ℚ, a, b]) = (n : ℤ) • (1 : ℍ[ℚ, a, b]) := by rw [zsmul_eq_mul, mul_one]; norm_cast
    rw [this]; exact Λ.smul_mem _ hone
  obtain ⟨ψ, ⟨hpψ, hψhom⟩, hψuniq⟩ :=
    GoodReductionJacobian.RelativeGroupLaw.existsUnique_quotient_desc_hom_of_isColimit E.L κ p w hcolim hg LP hhom
      E.L ⟨E.act ⟨_, hnΛ⟩, E.act_over _⟩ (fun t x y => E.act_hom ⟨_, hnΛ⟩ t x y) (by
        intro T t e he
        have h1 := CerednikDrinfeld.QM.FakeEllipticCurve.pushPt_act_natCast_eq_nsmulPt E hone n hnΛ t
          (⟨e ≫ κ, by rw [Category.assoc]; exact he⟩ : SchemeHomOver t E.f)
        have h2 := hK_tors t (⟨e ≫ κ, by rw [Category.assoc]; exact he⟩ : SchemeHomOver t E.f) ⟨e, rfl⟩
        exact (h1.trans h2))
  have hp_hom : QuotFwd.IsHom E.L LP ⟨p, hg⟩ := fun _ t x y => hhom' t x y
  have hψ_hom : QuotFwd.IsHom LP E.L ψ := fun _ t u v => hψhom t u v
  have hact_hom : ∀ x : ↥Λ, QuotFwd.IsHom LP LP (actP x) := fun x _ t u v => hactP_hom x t u v
  have hEact_hom : ∀ x : ↥Λ, QuotFwd.IsHom E.L E.L ⟨E.act x, E.act_over x⟩ := fun x _ t u v => E.act_hom x t u v
  have hact_one : ∀ h1 : (1 : ℍ[ℚ, a, b]) ∈ Λ, (actP ⟨1, h1⟩).1 = 𝟙 P := by
    intro h1
    have := hactP_uniq ⟨1, h1⟩ ⟨𝟙 P, Category.id_comp g⟩ (by rw [E.act_one h1]; simp) (by
      intro T t u v; apply Subtype.ext; simp)
    exact (congrArg Subtype.val this).symm
  have hact_mul : ∀ (x y : ↥Λ) (hxy : (x : ℍ[ℚ, a, b]) * (y : ℍ[ℚ, a, b]) ∈ Λ),
      (actP ⟨(x : ℍ[ℚ, a, b]) * (y : ℍ[ℚ, a, b]), hxy⟩).1 = (actP y).1 ≫ (actP x).1 := by
    intro x y hxy
    have hc := QuotFwd.IsHom.comp (hact_hom y) (hact_hom x)
    have hcand := hactP_uniq ⟨(x : ℍ[ℚ, a, b]) * y, hxy⟩ ⟨(actP y).1 ≫ (actP x).1, by rw [Category.assoc, (actP x).2, (actP y).2]⟩
      (by rw [← Category.assoc, hpact y, Category.assoc, hpact x, ← Category.assoc, ← E.act_mul x y hxy])
      (fun t u v => hc t u v)
    exact (congrArg Subtype.val hcand).symm
  have hact_add : ∀ (x y : ↥Λ) {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of S)) (P' : SchemeHomOver t g),
      pushPt (actP (x + y)).1 (actP (x + y)).2 P' = LP.mul t (pushPt (actP x).1 (actP x).2 P') (pushPt (actP y).1 (actP y).2 P') := by
    intro x y T t P'
    have hh : ∀ (z : ↥Λ) {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of S)) (u v : SchemeHomOver t g),
        pushPt (actP z).1 (actP z).2 (LP.mul t u v) = LP.mul t (pushPt (actP z).1 (actP z).2 u) (pushPt (actP z).1 (actP z).2 v) :=
      fun z _ t u v => hactP_hom z t u v
    have hsum : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of S)) (Q : SchemeHomOver t g),
        pushPt (LP.mul g (actP x) (actP y)).1 (LP.mul g (actP x) (actP y)).2 Q =
          LP.mul t (pushPt (actP x).1 (actP x).2 Q) (pushPt (actP y).1 (actP y).2 Q) :=
      fun t Q => LP.mul_natural g t Q.1 Q.2 (actP x) (actP y)
    have hσ : LP.mul g (actP x) (actP y) = actP (x + y) := by
      refine hactP_uniq (x + y) _ ?_ ?_
      · have h1 := LP.mul_natural g E.f p hg (actP x) (actP y)
        have h2 : ∀ z : ↥Λ, schemeHomOverComp p hg (actP z) = mapPt p hg ⟨E.act z, E.act_over z⟩ := by
          intro z; apply Subtype.ext; exact hpact z
        have h3 := E.act_add x y E.f ⟨𝟙 E.A, Category.id_comp _⟩
        have h4 : ∀ z : ↥Λ, pushPt (E.act z) (E.act_over z) (⟨𝟙 E.A, Category.id_comp _⟩ : SchemeHomOver E.f E.f) =
            ⟨E.act z, E.act_over z⟩ := by
          intro z; apply Subtype.ext; exact Category.id_comp _
        simp only [h4] at h3
        rw [h2, h2, ← hhom', ← h3] at h1
        exact congrArg Subtype.val h1
      · intro T t u v
        show pushPt (LP.mul g (actP x) (actP y)).1 (LP.mul g (actP x) (actP y)).2 (LP.mul t u v) =
          LP.mul t (pushPt (LP.mul g (actP x) (actP y)).1 (LP.mul g (actP x) (actP y)).2 u)
            (pushPt (LP.mul g (actP x) (actP y)).1 (LP.mul g (actP x) (actP y)).2 v)
        rw [hsum, hsum, hsum, hh x, hh y]
        letI : CommGroup (SchemeHomOver t g) := { (LP.pointGroup t) with mul_comm := hcommP t }
        exact mul_mul_mul_comm _ _ _ _
    show pushPt (actP (x + y)).1 (actP (x + y)).2 P' = LP.mul t (pushPt (actP x).1 (actP x).2 P') (pushPt (actP y).1 (actP y).2 P')
    rw [← hσ]
    exact hsum t P'
  have hψlin : ∀ x : ↥Λ, (actP x).1 ≫ ψ.1 = ψ.1 ≫ E.act x := by
    intro x
    have hnx : ((n : ℚ) : ℍ[ℚ, a, b]) * (x : ℍ[ℚ, a, b]) ∈ Λ := by
      rw [QuaternionAlgebra.coe_mul_eq_smul, Nat.cast_smul_eq_nsmul]; exact nsmul_mem x.2 n
    have hxn : (x : ℍ[ℚ, a, b]) * ((n : ℚ) : ℍ[ℚ, a, b]) ∈ Λ := by
      rw [QuaternionAlgebra.mul_coe_eq_smul, ← QuaternionAlgebra.coe_mul_eq_smul]; exact hnx
    have hcomm_xl : E.act x ≫ E.act ⟨_, hnΛ⟩ = E.act ⟨_, hnΛ⟩ ≫ E.act x := by
      have h1 := E.act_mul ⟨_, hnΛ⟩ x hnx
      have h2 := E.act_mul x ⟨_, hnΛ⟩ hxn
      have h3 : (⟨((n : ℚ) : ℍ[ℚ, a, b]) * (x : ℍ[ℚ, a, b]), hnx⟩ : ↥Λ) =
          ⟨(x : ℍ[ℚ, a, b]) * ((n : ℚ) : ℍ[ℚ, a, b]), hxn⟩ := by
        apply Subtype.ext
        show ((n : ℚ) : ℍ[ℚ, a, b]) * (x : ℍ[ℚ, a, b]) = (x : ℍ[ℚ, a, b]) * ((n : ℚ) : ℍ[ℚ, a, b])
        rw [QuaternionAlgebra.coe_mul_eq_smul, QuaternionAlgebra.mul_coe_eq_smul]
      rw [h3] at h1; rw [h1] at h2; exact h2
    obtain ⟨χ, -, hχuniq⟩ :=
      GoodReductionJacobian.RelativeGroupLaw.existsUnique_quotient_desc_hom_of_isColimit E.L κ p w hcolim hg LP hhom
        E.L ⟨E.act x ≫ E.act ⟨_, hnΛ⟩, by rw [Category.assoc, E.act_over, E.act_over]⟩
        (fun t u v => (QuotFwd.IsHom.comp (hEact_hom x) (hEact_hom ⟨_, hnΛ⟩)) t u v) (by
          intro T t e he
          have h1 := CerednikDrinfeld.QM.FakeEllipticCurve.pushPt_act_natCast_eq_nsmulPt E hone n hnΛ t
            (pushPt (E.act x) (E.act_over x) (⟨e ≫ κ, by rw [Category.assoc]; exact he⟩ : SchemeHomOver t E.f))
          have h2 := hK_tors t
            (pushPt (E.act x) (E.act_over x) (⟨e ≫ κ, by rw [Category.assoc]; exact he⟩ : SchemeHomOver t E.f))
            (hK_stable x t _ ⟨e, rfl⟩)
          refine Eq.trans ?_ (h1.trans h2)
          apply Subtype.ext; simp [pushPt, mapPt, Category.assoc])
    have hA : (⟨(actP x).1 ≫ ψ.1, by rw [Category.assoc, ψ.2, (actP x).2]⟩ : SchemeHomOver g E.f) = χ :=
      hχuniq _ ⟨by rw [← Category.assoc, hpact x, Category.assoc, hpψ], fun t u v => (QuotFwd.IsHom.comp (hact_hom x) hψ_hom) t u v⟩
    have hB : (⟨ψ.1 ≫ E.act x, by rw [Category.assoc, E.act_over, ψ.2]⟩ : SchemeHomOver g E.f) = χ :=
      hχuniq _ ⟨by rw [← Category.assoc, hpψ]; exact hcomm_xl.symm, fun t u v => (QuotFwd.IsHom.comp hψ_hom (hEact_hom x)) t u v⟩
    exact congrArg Subtype.val (hA.trans hB.symm)
  have hψp : ψ.1 ≫ p = (actP ⟨((n : ℚ) : ℍ[ℚ, a, b]), hnΛ⟩).1 := by
    have hcand := hactP_uniq ⟨_, hnΛ⟩ ⟨ψ.1 ≫ p, by rw [Category.assoc, hg, ψ.2]⟩
      (by rw [← Category.assoc, hpψ]) (fun t u v => (QuotFwd.IsHom.comp hψ_hom hp_hom) t u v)
    exact congrArg Subtype.val hcand

  have hnat : ∀ (m : ℕ) (hm : ((m : ℚ) : ℍ[ℚ, a, b]) ∈ Λ) {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of S)) (Q : SchemeHomOver t g),
      pushPt (actP ⟨((m : ℚ) : ℍ[ℚ, a, b]), hm⟩).1 (actP ⟨((m : ℚ) : ℍ[ℚ, a, b]), hm⟩).2 Q = nsmulPt LP t m Q := by
    intro m
    induction m with
    | zero =>
      intro hm T t Q
      have h0 : (⟨(((0 : ℕ) : ℚ) : ℍ[ℚ, a, b]), hm⟩ : ↥Λ) + ⟨(((0 : ℕ) : ℚ) : ℍ[ℚ, a, b]), hm⟩ = ⟨(((0 : ℕ) : ℚ) : ℍ[ℚ, a, b]), hm⟩ := by
        apply Subtype.ext; simp
      have h := hact_add ⟨_, hm⟩ ⟨_, hm⟩ t Q
      rw [h0] at h
      have := congrArg (LP.mul t (LP.inv t (pushPt (actP ⟨(((0 : ℕ) : ℚ) : ℍ[ℚ, a, b]), hm⟩).1 (actP ⟨(((0 : ℕ) : ℚ) : ℍ[ℚ, a, b]), hm⟩).2 Q))) h
      rw [← LP.mul_assoc, LP.inv_mul_cancel, LP.one_mul] at this
      exact this.symm
    | succ m ih =>
      intro hm T t Q
      have hm' : ((m : ℚ) : ℍ[ℚ, a, b]) ∈ Λ := by
        have : ((m : ℚ) : ℍ[ℚ, a, b]) = (m : ℤ) • (1 : ℍ[ℚ, a, b]) := by rw [zsmul_eq_mul, mul_one]; norm_cast
        rw [this]; exact Λ.smul_mem _ hone
      have e : (⟨(((m + 1 : ℕ) : ℚ) : ℍ[ℚ, a, b]), hm⟩ : ↥Λ) = ⟨((m : ℚ) : ℍ[ℚ, a, b]), hm'⟩ + ⟨1, hone⟩ := by
        apply Subtype.ext; push_cast; rfl
      rw [e, hact_add, ih hm']
      have h1' : pushPt (actP ⟨1, hone⟩).1 (actP ⟨1, hone⟩).2 Q = Q := by
        apply Subtype.ext
        show Q.1 ≫ (actP ⟨1, hone⟩).1 = Q.1
        rw [hact_one, Category.comp_id]
      rw [h1']
      rfl

  have hrank : ∀ y : ↥P, p.finrank y = (κ ≫ E.f).finrank (g.base y) := by
    intro y
    obtain ⟨x, rfl⟩ := hsurj.1 y
    have h1 := Scheme.Hom.finrank_of_isPullback _ _ _ _ hpb.flip x
    rw [← h1, Scheme.Hom.finrank_pullback_snd]
    congr 1
    show E.f.base x = g.base (p.base x)
    rw [← hg]; rfl
  refine ⟨P, g, LP, fun x => (actP x).1, fun x => (actP x).2, p, hg, ψ.1, ψ.2, w, hcommP, hbundle,
    fun s => (QuotFwd.topologicalKrullDim_fibre_eq E.f g p hg s).trans (E.dim_fibre s),
    fun x _ t P' Q' => hactP_hom x t P' Q', hact_one, hact_mul, fun x y _ t P' => hact_add x y t P',
    hhom', fun t u v => hψhom t u v, fun x => (hpact x).symm, hψlin,
    fun hn_mem => ⟨hpψ, hψp⟩, ?_, ?_, hfin, hflat, hlfp, hsurj, hrank, fun t P' => hker t P', ?_, hpb, ⟨hcolim⟩⟩
  ·
    intro T t P'
    have e : mapPt ψ.1 ψ.2 (mapPt p hg P') = pushPt (E.act ⟨_, hnΛ⟩) (E.act_over _) P' := by
      apply Subtype.ext
      show (P'.1 ≫ p) ≫ ψ.1 = P'.1 ≫ E.act ⟨_, hnΛ⟩
      rw [Category.assoc, hpψ]
    exact e.trans (CerednikDrinfeld.QM.FakeEllipticCurve.pushPt_act_natCast_eq_nsmulPt E hone n hnΛ t P')
  ·
    intro T t Q
    have e : mapPt p hg (mapPt ψ.1 ψ.2 Q) = pushPt (actP ⟨_, hnΛ⟩).1 (actP ⟨_, hnΛ⟩).2 Q := by
      apply Subtype.ext
      show (Q.1 ≫ ψ.1) ≫ p = Q.1 ≫ (actP ⟨_, hnΛ⟩).1
      rw [Category.assoc, hψp]
    exact e.trans (hnat n hnΛ t Q)
  ·
    intro X gX LX φ hφ hφhom hφK
    exact GoodReductionJacobian.RelativeGroupLaw.existsUnique_quotient_desc_hom_of_isColimit E.L κ p w hcolim hg LP hhom
      LX ⟨φ, hφ⟩ (fun t x y => hφhom t x y)
      (fun t e he => hφK t (⟨e ≫ κ, by rw [Category.assoc]; exact he⟩ : SchemeHomOver t E.f) ⟨e, rfl⟩)

end S_CerednikDrinfeld_QM_FakeEllipticCurve_exists_quotient_of_finiteFlat_stable_subgroup
end P2MW
export P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_exists_quotient_of_finiteFlat_stable_subgroup (solution)
