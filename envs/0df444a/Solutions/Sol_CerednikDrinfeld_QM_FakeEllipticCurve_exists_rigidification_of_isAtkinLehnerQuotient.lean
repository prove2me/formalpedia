-- Prove2me | solution 1 for CerednikDrinfeld.QM.FakeEllipticCurve.exists_rigidification_of_isAtkinLehnerQuotient
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.141142+00:00
-- url     : https://prove2.me/submissions/97d34a9d-4e2a-51b8-829a-d9e6967db43b

import Mathlib
import Definitions.Def_CerednikDrinfeld_QMRigidification
import Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_isFinite_flat_surjective_of_mapPt_mapPt_eq_nsmulPt
import Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_factorsThrough_lev_iff_exists_mapPt_eq_of_coprime
import Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_pushPt_act_natCast_eq_nsmulPt
import Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_factorsThrough_lev_of_exists_comp_eq_of_isPullback
import Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_exists_isPullback_levelIff
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_exists_rigidification_of_isAtkinLehnerQuotient
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
set_option maxHeartbeats 1600000

open scoped TensorProduct Quaternion NumberField
p2m_open "CategoryTheory CategoryTheory.Limits AlgebraicGeometry QuaternionAlgebra CerednikDrinfeld CerednikDrinfeld.QM NeronModelInfra~schemeHomOverComp~schemeHomOverComp_coe GoodReductionJacobian"

namespace M9Transport

open CerednikDrinfeld.QM.FakeEllipticCurve

section Square

variable {S S' : Type} [CommRing S] [CommRing S'] {φ : S →+* S'}
variable {A A' : Scheme.{0}} {f : A ⟶ Spec (CommRingCat.of S)} {f' : A' ⟶ Spec (CommRingCat.of S')} {g : A' ⟶ A}

def img (hg : IsPullback g f' f (Spec.map (CommRingCat.ofHom φ))) {T : Scheme.{0}}
    {t' : T ⟶ Spec (CommRingCat.of S')} (P : SchemeHomOver t' f') :
    SchemeHomOver (t' ≫ Spec.map (CommRingCat.ofHom φ)) f :=
  ⟨P.1 ≫ g, by rw [Category.assoc, hg.w, ← Category.assoc, P.2]⟩

@[scoped simp] theorem img_coe (hg : IsPullback g f' f (Spec.map (CommRingCat.ofHom φ))) {T : Scheme.{0}}
    {t' : T ⟶ Spec (CommRingCat.of S')} (P : SchemeHomOver t' f') : (img hg P).1 = P.1 ≫ g := rfl

theorem img_injective (hg : IsPullback g f' f (Spec.map (CommRingCat.ofHom φ))) {T : Scheme.{0}}
    {t' : T ⟶ Spec (CommRingCat.of S')} {P Q : SchemeHomOver t' f'} (h : img hg P = img hg Q) : P = Q := by
  apply Subtype.ext
  apply hg.hom_ext
  · exact congrArg Subtype.val h
  · rw [P.2, Q.2]

theorem img_one (hg : IsPullback g f' f (Spec.map (CommRingCat.ofHom φ)))
    (L : RelativeGroupLaw S f) (L' : RelativeGroupLaw S' f')
    (hg_mul : ∀ {T : Scheme.{0}} (t' : T ⟶ Spec (CommRingCat.of S')) (P Q : SchemeHomOver t' f'),
      (L'.mul t' P Q).1 ≫ g = (L.mul (t' ≫ Spec.map (CommRingCat.ofHom φ)) (img hg P) (img hg Q)).1)
    {T : Scheme.{0}} (t' : T ⟶ Spec (CommRingCat.of S')) :
    img hg (L'.one t') = L.one (t' ≫ Spec.map (CommRingCat.ofHom φ)) := by
  set x := img hg (L'.one t') with hx
  have hxx : L.mul _ x x = x := by
    apply Subtype.ext
    rw [hx, ← hg_mul, L'.one_mul]
    rfl
  letI := L.pointGroup (t' ≫ Spec.map (CommRingCat.ofHom φ))
  have h2 : x * x = x * 1 := by rw [mul_one]; exact hxx
  exact mul_left_cancel h2

theorem img_mul (hg : IsPullback g f' f (Spec.map (CommRingCat.ofHom φ)))
    (L : RelativeGroupLaw S f) (L' : RelativeGroupLaw S' f')
    (hg_mul : ∀ {T : Scheme.{0}} (t' : T ⟶ Spec (CommRingCat.of S')) (P Q : SchemeHomOver t' f'),
      (L'.mul t' P Q).1 ≫ g = (L.mul (t' ≫ Spec.map (CommRingCat.ofHom φ)) (img hg P) (img hg Q)).1)
    {T : Scheme.{0}} (t' : T ⟶ Spec (CommRingCat.of S')) (P Q : SchemeHomOver t' f') :
    img hg (L'.mul t' P Q) = L.mul _ (img hg P) (img hg Q) :=
  Subtype.ext (hg_mul t' P Q)

theorem img_pushPt (hg : IsPullback g f' f (Spec.map (CommRingCat.ofHom φ)))
    (e : A ⟶ A) (he : e ≫ f = f) (e' : A' ⟶ A') (he' : e' ≫ f' = f') (hcomm : e' ≫ g = g ≫ e)
    {T : Scheme.{0}} {t' : T ⟶ Spec (CommRingCat.of S')} (P : SchemeHomOver t' f') :
    img hg (pushPt e' he' P) = pushPt e he (img hg P) := by
  apply Subtype.ext
  simp only [img_coe, pushPt, mapPt_coe, Category.assoc, hcomm]

variable {A₁ A₁' : Scheme.{0}} {f₁ : A₁ ⟶ Spec (CommRingCat.of S)} {f₁' : A₁' ⟶ Spec (CommRingCat.of S')} {g₁ : A₁' ⟶ A₁}

theorem img_mapPt (hg : IsPullback g f' f (Spec.map (CommRingCat.ofHom φ)))
    (hg₁ : IsPullback g₁ f₁' f₁ (Spec.map (CommRingCat.ofHom φ)))
    (θ : A ⟶ A₁) (hθ : θ ≫ f₁ = f) (θ' : A' ⟶ A₁') (hθ' : θ' ≫ f₁' = f') (hcomm : θ' ≫ g₁ = g ≫ θ)
    {T : Scheme.{0}} {t' : T ⟶ Spec (CommRingCat.of S')} (P : SchemeHomOver t' f') :
    img hg₁ (mapPt θ' hθ' P) = mapPt θ hθ (img hg P) := by
  apply Subtype.ext
  simp only [img_coe, mapPt_coe, Category.assoc, hcomm]

end Square

section OneBase

variable {S : Type} [CommRing S] {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} {N : ℕ}

theorem mapPt_one {E E' : FakeEllipticCurve Λ N S} (φ : E.A ⟶ E'.A) (hφ : φ ≫ E'.f = E.f)
    (hmul : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of S)) (P Q : SchemeHomOver t E.f),
      mapPt φ hφ (E.L.mul t P Q) = E'.L.mul t (mapPt φ hφ P) (mapPt φ hφ Q))
    {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of S)) : mapPt φ hφ (E.L.one t) = E'.L.one t := by
  set x := mapPt φ hφ (E.L.one t) with hx
  have hxx : E'.L.mul t x x = x := by rw [hx, ← hmul, E.L.one_mul]
  letI := E'.L.pointGroup t
  have h2 : x * x = x * 1 := by rw [mul_one]; exact hxx
  exact mul_left_cancel h2

theorem mapPt_comp' {A A' A'' : Scheme.{0}} {f : A ⟶ Spec (CommRingCat.of S)} {f' : A' ⟶ Spec (CommRingCat.of S)}
    {f'' : A'' ⟶ Spec (CommRingCat.of S)} (θ : A ⟶ A') (hθ : θ ≫ f' = f)
    (θ' : A' ⟶ A'') (hθ' : θ' ≫ f'' = f') (h : (θ ≫ θ') ≫ f'' = f) {T : Scheme.{0}} {t : T ⟶ Spec (CommRingCat.of S)}
    (P : SchemeHomOver t f) :
    mapPt (θ ≫ θ') h P = mapPt θ' hθ' (mapPt θ hθ P) := by
  apply Subtype.ext; simp only [mapPt_coe, Category.assoc]

theorem mapPt_id' {A : Scheme.{0}} {f : A ⟶ Spec (CommRingCat.of S)} (h : 𝟙 A ≫ f = f)
    {T : Scheme.{0}} {t : T ⟶ Spec (CommRingCat.of S)} (P : SchemeHomOver t f) : mapPt (𝟙 A) h P = P := by
  apply Subtype.ext; simp only [mapPt_coe, Category.comp_id]

theorem pushPt_mapPt {A A' : Scheme.{0}} {f : A ⟶ Spec (CommRingCat.of S)} {f' : A' ⟶ Spec (CommRingCat.of S)}
    (θ : A ⟶ A') (hθ : θ ≫ f' = f) (e : A ⟶ A) (he : e ≫ f = f) (e' : A' ⟶ A') (he' : e' ≫ f' = f')
    (hcomm : e ≫ θ = θ ≫ e') {T : Scheme.{0}} {t : T ⟶ Spec (CommRingCat.of S)} (P : SchemeHomOver t f) :
    pushPt e' he' (mapPt θ hθ P) = mapPt θ hθ (pushPt e he P) := by
  apply Subtype.ext; simp only [mapPt_coe, pushPt, Category.assoc, hcomm]

theorem mapPt_schemeHomOverComp {E E' : FakeEllipticCurve Λ N S} (φ : E.A ⟶ E'.A) (hφ : φ ≫ E'.f = E.f)
    {T T' : Scheme.{0}} {t : T ⟶ Spec (CommRingCat.of S)} {t' : T' ⟶ Spec (CommRingCat.of S)} (ψ : T' ⟶ T)
    (hψ : ψ ≫ t = t') (P : SchemeHomOver t E.f) :
    mapPt φ hφ (schemeHomOverComp ψ hψ P) = schemeHomOverComp ψ hψ (mapPt φ hφ P) :=
  Subtype.ext (by simp only [mapPt_coe, schemeHomOverComp_coe, Category.assoc])

theorem comp_mul {E E' E'' : FakeEllipticCurve Λ N S} (θ : E.A ⟶ E'.A) (hθ : θ ≫ E'.f = E.f)
    (θ' : E'.A ⟶ E''.A) (hθ' : θ' ≫ E''.f = E'.f) (h : (θ ≫ θ') ≫ E''.f = E.f)
    (mθ : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of S)) (P Q : SchemeHomOver t E.f),
      mapPt θ hθ (E.L.mul t P Q) = E'.L.mul t (mapPt θ hθ P) (mapPt θ hθ Q))
    (mθ' : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of S)) (P Q : SchemeHomOver t E'.f),
      mapPt θ' hθ' (E'.L.mul t P Q) = E''.L.mul t (mapPt θ' hθ' P) (mapPt θ' hθ' Q))
    {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of S)) (P Q : SchemeHomOver t E.f) :
    mapPt (θ ≫ θ') h (E.L.mul t P Q) = E''.L.mul t (mapPt (θ ≫ θ') h P) (mapPt (θ ≫ θ') h Q) := by
  rw [mapPt_comp' θ hθ θ' hθ', mθ, mθ', ← mapPt_comp' θ hθ θ' hθ', ← mapPt_comp' θ hθ θ' hθ']

theorem act_comm_natCast (E : FakeEllipticCurve Λ N S) (x : ↥Λ) (n : ℕ) (hn : ((n : ℚ) : ℍ[ℚ, a, b]) ∈ Λ) :
    E.act x ≫ E.act ⟨((n : ℚ) : ℍ[ℚ, a, b]), hn⟩ = E.act ⟨((n : ℚ) : ℍ[ℚ, a, b]), hn⟩ ≫ E.act x := by
  have hm : ((n : ℚ) : ℍ[ℚ, a, b]) * (x : ℍ[ℚ, a, b]) ∈ Λ := by
    have : ((n : ℚ) : ℍ[ℚ, a, b]) * (x : ℍ[ℚ, a, b]) = (n : ℤ) • (x : ℍ[ℚ, a, b]) := by
      rw [zsmul_eq_mul]; push_cast; rfl
    rw [this]; exact Λ.smul_mem _ x.2
  have hm' : (x : ℍ[ℚ, a, b]) * ((n : ℚ) : ℍ[ℚ, a, b]) ∈ Λ := by rwa [← QuaternionAlgebra.coe_commutes]
  have h1 := E.act_mul ⟨((n : ℚ) : ℍ[ℚ, a, b]), hn⟩ x hm
  have h2 := E.act_mul x ⟨((n : ℚ) : ℍ[ℚ, a, b]), hn⟩ hm'
  have h3 : (⟨((n : ℚ) : ℍ[ℚ, a, b]) * (x : ℍ[ℚ, a, b]), hm⟩ : ↥Λ) = ⟨(x : ℍ[ℚ, a, b]) * ((n : ℚ) : ℍ[ℚ, a, b]), hm'⟩ :=
    Subtype.ext (QuaternionAlgebra.coe_commutes _ _)
  rw [← h1, h3, h2]

theorem act_natCast_comp (E : FakeEllipticCurve Λ N S) (m n : ℕ) (hm : ((m : ℚ) : ℍ[ℚ, a, b]) ∈ Λ)
    (hn : ((n : ℚ) : ℍ[ℚ, a, b]) ∈ Λ) (hnm : (((n * m : ℕ) : ℚ) : ℍ[ℚ, a, b]) ∈ Λ) :
    E.act ⟨((m : ℚ) : ℍ[ℚ, a, b]), hm⟩ ≫ E.act ⟨((n : ℚ) : ℍ[ℚ, a, b]), hn⟩ = E.act ⟨(((n * m : ℕ) : ℚ) : ℍ[ℚ, a, b]), hnm⟩ := by
  have e : (((n * m : ℕ) : ℚ) : ℍ[ℚ, a, b]) = ((n : ℚ) : ℍ[ℚ, a, b]) * ((m : ℚ) : ℍ[ℚ, a, b]) := by
    rw [Nat.cast_mul, QuaternionAlgebra.coe_mul]
  have h : ((n : ℚ) : ℍ[ℚ, a, b]) * ((m : ℚ) : ℍ[ℚ, a, b]) ∈ Λ := by rw [← e]; exact hnm
  rw [← E.act_mul ⟨((n : ℚ) : ℍ[ℚ, a, b]), hn⟩ ⟨((m : ℚ) : ℍ[ℚ, a, b]), hm⟩ h]
  congr 1; exact Subtype.ext e.symm

theorem act_congr (E : FakeEllipticCurve Λ N S) {x y : ℍ[ℚ, a, b]} (h : x = y) (hx : x ∈ Λ) (hy : y ∈ Λ) :
    E.act ⟨x, hx⟩ = E.act ⟨y, hy⟩ := by
  subst h; rfl

end OneBase

section Descent

variable {S : Type} [CommRing S] {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} {N : ℕ}

theorem coeq (A B C : FakeEllipticCurve Λ N S) (α : A.A ⟶ B.A) (hα : α ≫ B.f = A.f) (β : A.A ⟶ C.A) (hβ : β ≫ C.f = A.f)
    (mα : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of S)) (P Q : SchemeHomOver t A.f),
      mapPt α hα (A.L.mul t P Q) = B.L.mul t (mapPt α hα P) (mapPt α hα Q))
    (mβ : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of S)) (P Q : SchemeHomOver t A.f),
      mapPt β hβ (A.L.mul t P Q) = C.L.mul t (mapPt β hβ P) (mapPt β hβ Q))
    (hker : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of S)) (P : SchemeHomOver t A.f),
      mapPt α hα P = B.L.one t → mapPt β hβ P = C.L.one t)
    {Z : Scheme.{0}} (g₁ g₂ : Z ⟶ A.A) (hg : g₁ ≫ α = g₂ ≫ α) : g₁ ≫ β = g₂ ≫ β := by
  let t : Z ⟶ Spec (CommRingCat.of S) := g₁ ≫ A.f
  have hg₂ : g₂ ≫ A.f = t := by
    show g₂ ≫ A.f = g₁ ≫ A.f
    rw [← hα, ← Category.assoc, ← hg, Category.assoc]
  let P : SchemeHomOver t A.f := ⟨g₁, rfl⟩
  let Q : SchemeHomOver t A.f := ⟨g₂, hg₂⟩
  letI := A.L.pointGroup t; letI := B.L.pointGroup t; letI := C.L.pointGroup t
  let Fα : SchemeHomOver t A.f →* SchemeHomOver t B.f :=
    { toFun := mapPt α hα, map_one' := mapPt_one α hα mα t, map_mul' := fun X Y => mα t X Y }
  let Fβ : SchemeHomOver t A.f →* SchemeHomOver t C.f :=
    { toFun := mapPt β hβ, map_one' := mapPt_one β hβ mβ t, map_mul' := fun X Y => mβ t X Y }
  have hPQ : Fα P = Fα Q := Subtype.ext hg
  have h1 : Fα (P * Q⁻¹) = 1 := by rw [map_mul, map_inv, hPQ, mul_inv_cancel]
  have h2 : Fβ (P * Q⁻¹) = 1 := hker t _ h1
  have h3 : Fβ P = Fβ Q := by
    rw [map_mul, map_inv] at h2
    exact mul_inv_eq_one.1 h2
  exact congrArg Subtype.val h3

theorem desc_mul {A B C : FakeEllipticCurve Λ N S} (α : A.A ⟶ B.A) (hα : α ≫ B.f = A.f) [Flat α] [Surjective α]
    (mα : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of S)) (P Q : SchemeHomOver t A.f),
      mapPt α hα (A.L.mul t P Q) = B.L.mul t (mapPt α hα P) (mapPt α hα Q))
    (χ : B.A ⟶ C.A) (hχ : χ ≫ C.f = B.f) (β : A.A ⟶ C.A) (hβ : β ≫ C.f = A.f) (hfac : α ≫ χ = β)
    (mβ : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of S)) (P Q : SchemeHomOver t A.f),
      mapPt β hβ (A.L.mul t P Q) = C.L.mul t (mapPt β hβ P) (mapPt β hβ Q))
    {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of S)) (P Q : SchemeHomOver t B.f) :
    mapPt χ hχ (B.L.mul t P Q) = C.L.mul t (mapPt χ hχ P) (mapPt χ hχ Q) := by
  have tχ : ∀ {T : Scheme.{0}} {t : T ⟶ Spec (CommRingCat.of S)} (P : SchemeHomOver t A.f),
      mapPt χ hχ (mapPt α hα P) = mapPt β hβ P :=
    fun P => Subtype.ext (by simp only [mapPt_coe, Category.assoc, hfac])

  let T₁ := pullback P.1 α
  let π₁ : T₁ ⟶ T := pullback.fst P.1 α
  haveI : Flat π₁ := inferInstance
  haveI : Surjective π₁ := inferInstance

  let T₂ := pullback (π₁ ≫ Q.1) α
  let π₂ : T₂ ⟶ T₁ := pullback.fst (π₁ ≫ Q.1) α
  haveI : Flat π₂ := inferInstance
  haveI : Surjective π₂ := inferInstance
  let ψ : T₂ ⟶ T := π₂ ≫ π₁
  haveI : Epi π₁ := Flat.epi_of_flat_of_surjective π₁
  haveI : Epi π₂ := Flat.epi_of_flat_of_surjective π₂
  haveI : Epi ψ := epi_comp π₂ π₁
  have hψt : ψ ≫ t = ψ ≫ t := rfl
  let Pl : SchemeHomOver (ψ ≫ t) A.f := ⟨π₂ ≫ pullback.snd P.1 α, by
    show (π₂ ≫ pullback.snd P.1 α) ≫ A.f = (π₂ ≫ π₁) ≫ t
    rw [← hα]; simp only [Category.assoc]
    rw [← pullback.condition_assoc, P.2]⟩
  let Ql : SchemeHomOver (ψ ≫ t) A.f := ⟨pullback.snd (π₁ ≫ Q.1) α, by
    show pullback.snd (π₁ ≫ Q.1) α ≫ A.f = (π₂ ≫ π₁) ≫ t
    rw [← hα, ← pullback.condition_assoc]; simp only [Category.assoc]; rw [Q.2]⟩
  have hPl : mapPt α hα Pl = schemeHomOverComp ψ hψt P := by
    apply Subtype.ext
    show (π₂ ≫ pullback.snd P.1 α) ≫ α = (π₂ ≫ π₁) ≫ P.1
    simp only [Category.assoc]
    rw [pullback.condition]
  have hQl : mapPt α hα Ql = schemeHomOverComp ψ hψt Q := by
    apply Subtype.ext
    show pullback.snd (π₁ ≫ Q.1) α ≫ α = (π₂ ≫ π₁) ≫ Q.1
    rw [Category.assoc, ← pullback.condition]
  have key : schemeHomOverComp ψ hψt (mapPt χ hχ (B.L.mul t P Q)) =
      schemeHomOverComp ψ hψt (C.L.mul t (mapPt χ hχ P) (mapPt χ hχ Q)) := by
    rw [← mapPt_schemeHomOverComp, B.L.mul_natural t (ψ ≫ t) ψ hψt, ← hPl, ← hQl, ← mα, tχ, mβ, ← tχ, ← tχ, hPl, hQl,
      mapPt_schemeHomOverComp, mapPt_schemeHomOverComp, ← C.L.mul_natural t (ψ ≫ t) ψ hψt]
  apply Subtype.ext
  rw [← cancel_epi ψ]
  exact congrArg Subtype.val key

end Descent

section Lift

variable {S S' : Type} [CommRing S] [CommRing S'] {φ : S →+* S'} {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} {N : ℕ}

theorem lift_mul {E E₁ : FakeEllipticCurve Λ N S} {F F₁ : FakeEllipticCurve Λ N S'} {g : F.A ⟶ E.A} {g₁ : F₁.A ⟶ E₁.A}
    (hg : IsPullback g F.f E.f (Spec.map (CommRingCat.ofHom φ)))
    (hg₁ : IsPullback g₁ F₁.f E₁.f (Spec.map (CommRingCat.ofHom φ)))
    (mg : ∀ {T : Scheme.{0}} (t' : T ⟶ Spec (CommRingCat.of S')) (P Q : SchemeHomOver t' F.f),
      (F.L.mul t' P Q).1 ≫ g = (E.L.mul (t' ≫ Spec.map (CommRingCat.ofHom φ)) (img hg P) (img hg Q)).1)
    (mg₁ : ∀ {T : Scheme.{0}} (t' : T ⟶ Spec (CommRingCat.of S')) (P Q : SchemeHomOver t' F₁.f),
      (F₁.L.mul t' P Q).1 ≫ g₁ = (E₁.L.mul (t' ≫ Spec.map (CommRingCat.ofHom φ)) (img hg₁ P) (img hg₁ Q)).1)
    (θ : E.A ⟶ E₁.A) (hθ : θ ≫ E₁.f = E.f)
    (mθ : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of S)) (P Q : SchemeHomOver t E.f),
      mapPt θ hθ (E.L.mul t P Q) = E₁.L.mul t (mapPt θ hθ P) (mapPt θ hθ Q))
    (θ' : F.A ⟶ F₁.A) (hθ' : θ' ≫ F₁.f = F.f) (hcomm : θ' ≫ g₁ = g ≫ θ)
    {T : Scheme.{0}} (t' : T ⟶ Spec (CommRingCat.of S')) (P Q : SchemeHomOver t' F.f) :
    mapPt θ' hθ' (F.L.mul t' P Q) = F₁.L.mul t' (mapPt θ' hθ' P) (mapPt θ' hθ' Q) := by
  apply img_injective hg₁
  rw [img_mapPt hg hg₁ θ hθ θ' hθ' hcomm, img_mul hg E.L F.L mg, mθ, img_mul hg₁ E₁.L F₁.L mg₁,
    img_mapPt hg hg₁ θ hθ θ' hθ' hcomm, img_mapPt hg hg₁ θ hθ θ' hθ' hcomm]

end Lift

section PullbackId

variable {S : Type} [CommRing S] {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} {N : ℕ}

theorem spec_map_id : Spec.map (CommRingCat.ofHom (RingHom.id S)) = 𝟙 (Spec (CommRingCat.of S)) := by
  rw [CommRingCat.ofHom_id]; exact Spec.map_id _

theorem isPullbackVia_id (E : FakeEllipticCurve Λ N S) :
    FakeEllipticCurve.IsPullbackVia (RingHom.id S) E E (𝟙 E.A) := by
  have hS := (spec_map_id (S := S))
  have hg : IsPullback (𝟙 E.A) E.f E.f (Spec.map (CommRingCat.ofHom (RingHom.id S))) := by
    rw [hS]; exact IsPullback.of_horiz_isIso ⟨by simp⟩
  refine ⟨hg, ?_, ?_, ?_⟩
  · intro T t' P Q
    have ht : 𝟙 T ≫ (t' ≫ Spec.map (CommRingCat.ofHom (RingHom.id S))) = t' := by rw [hS]; simp
    have key := E.L.mul_natural (t' ≫ Spec.map (CommRingCat.ofHom (RingHom.id S))) t' (𝟙 T) ht (img hg P) (img hg Q)
    have hP : schemeHomOverComp (𝟙 T) ht (img hg P) = P := Subtype.ext (by simp [schemeHomOverComp_coe])
    have hQ : schemeHomOverComp (𝟙 T) ht (img hg Q) = Q := Subtype.ext (by simp [schemeHomOverComp_coe])
    rw [hP, hQ] at key
    have := congrArg Subtype.val key
    simp only [schemeHomOverComp_coe, Category.id_comp] at this
    rw [Category.comp_id]
    exact this.symm
  · intro x; simp
  · intro T t' P hP
    obtain ⟨P₀, h⟩ := hP
    exact ⟨P₀, by rw [h, Category.comp_id]⟩

end PullbackId

end M9Transport
p2m_reactivate "P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_exists_rigidification_of_isAtkinLehnerQuotient.M9Transport"

open M9Transport in
theorem solution
    {r rbar N : ℕ} [Fact r.Prime] [Fact rbar.Prime] [NeZero N] (hrbarN : ¬ rbar ∣ N)
    (𝒪 : Type) [CommRing 𝒪] (π : 𝒪) (Onr : Type) [CommRing Onr] [Algebra 𝒪 Onr]
    {a b : ℚ} (Λ : Submodule ℤ ℍ[ℚ, a, b]) (hΛℤ : ∀ m : ℤ, ((m : ℚ) : ℍ[ℚ, a, b]) ∈ Λ)
    (A₀ : FakeEllipticCurve Λ N (Onr ⧸ Ideal.span {algebraMap 𝒪 Onr π}))

    (A₀f : FakeEllipticCurve Λ N (Onr ⧸ Ideal.span {algebraMap 𝒪 Onr π}))
    (aw : A₀.A ⟶ A₀f.A) (haw : aw ≫ A₀f.f = A₀.f) (aw' : A₀f.A ⟶ A₀.A) (haw' : aw' ≫ A₀.f = A₀f.f)
    (hAL₀ : FakeEllipticCurve.IsAtkinLehnerQuotientVia rbar A₀ A₀f aw haw aw' haw')
    (dw : ℕ) (bw : A₀f.A ⟶ A₀.A) (hbw : bw ≫ A₀.f = A₀f.f) (bw' : A₀.A ⟶ A₀f.A)
    (hBW : FakeEllipticCurve.IsIsogenyPair (r ^ dw) A₀f A₀ bw bw') (hBWlev : FakeEllipticCurve.PreservesLevel A₀f A₀ bw hbw)

    (B : Type) [CommRing B] [Algebra 𝒪 B] (hB : IsNilpotent (algebraMap 𝒪 B π)) (ψ : Onr →ₐ[𝒪] B)

    (hrbarB : IsUnit ((rbar : ℕ) : B))
    (E Ef : FakeEllipticCurve Λ N B)
    (q : E.A ⟶ Ef.A) (hq : q ≫ Ef.f = E.f) (q' : Ef.A ⟶ E.A) (hq' : q' ≫ E.f = Ef.f)
    (hAL : FakeEllipticCurve.IsAtkinLehnerQuotientVia rbar E Ef q hq q' hq')
    (ρ : FakeEllipticCurve.Rigidification r π A₀ ψ E) :
    ∃ (ρf : FakeEllipticCurve.Rigidification r π A₀ ψ Ef)

      (qb : ρ.Eb.A ⟶ ρf.Eb.A) (_ : qb ≫ ρf.gb = ρ.gb ≫ q) (_ : qb ≫ ρf.Eb.f = ρ.Eb.f)
      (uA : ρf.Ab.A ⟶ ρ.Ab.A) (_ : FakeEllipticCurve.IsPullbackVia (RingHom.id _) ρ.Ab ρf.Ab uA) (_ : uA ≫ ρ.gA = ρf.gA)

      (ewb : ρ.Ab.A ⟶ ρ.Ab.A) (_ : ewb ≫ ρ.gA = ρ.gA ≫ (aw ≫ bw)) (_ : ewb ≫ ρ.Ab.f = ρ.Ab.f)
      (i j : ℕ),
      qb ≫ ρf.φ ≫ uA ≫ ρ.Ab.act ⟨(((r ^ i : ℕ) : ℤ) : ℚ), hΛℤ _⟩ = ρ.φ ≫ ewb ≫ ρ.Ab.act ⟨(((r ^ j : ℕ) : ℤ) : ℚ), hΛℤ _⟩ := by
  classical

  obtain ⟨mq, mq', aq, aq', cq, kq, lq⟩ := hAL
  obtain ⟨maw, maw', aaw, aaw', caw, kaw, law⟩ := hAL₀
  obtain ⟨hbw₁, hbw'₁, mbw, mbw', abw, abw', cbw⟩ := hBW
  obtain ⟨hgb, mgb, agb, lgb⟩ := ρ.isPullback_Eb
  obtain ⟨hgA, mgA, agA, lgA⟩ := ρ.isPullback_Ab
  obtain ⟨hφo, hφ'o, mφ, mφ', aφ, aφ', cφ⟩ := ρ.isIsogenyPair

  have h1 : (1 : ℍ[ℚ, a, b]) ∈ Λ := by simpa using hΛℤ 1
  have hnat : ∀ n : ℕ, ((n : ℚ) : ℍ[ℚ, a, b]) ∈ Λ := fun n => by
    have := hΛℤ (n : ℤ); rwa [Int.cast_natCast] at this
  have hrb : ((rbar : ℚ) : ℍ[ℚ, a, b]) ∈ Λ := hnat rbar
  have hrbp : rbar.Prime := Fact.out
  have hcop : Nat.Coprime rbar N := (Nat.Prime.coprime_iff_not_dvd hrbp).2 hrbarN

  obtain ⟨Ebf, gbf, hgbf, mgbf, agbf, lgbf, lgbf'⟩ :=
    CerednikDrinfeld.QM.FakeEllipticCurve.exists_isPullback_levelIff
      (Ideal.Quotient.mk (Ideal.span {algebraMap 𝒪 B π})) Ef

  let qb : ρ.Eb.A ⟶ Ebf.A := hgbf.lift (ρ.gb ≫ q) ρ.Eb.f (by rw [Category.assoc, hq]; exact hgb.w)
  have hqb_g : qb ≫ gbf = ρ.gb ≫ q := hgbf.lift_fst _ _ _
  have hqb : qb ≫ Ebf.f = ρ.Eb.f := hgbf.lift_snd _ _ _
  let qb' : Ebf.A ⟶ ρ.Eb.A := hgb.lift (gbf ≫ q') Ebf.f (by rw [Category.assoc, hq']; exact hgbf.w)
  have hqb'_g : qb' ≫ ρ.gb = gbf ≫ q' := hgb.lift_fst _ _ _
  have hqb' : qb' ≫ ρ.Eb.f = Ebf.f := hgb.lift_snd _ _ _
  have hc1 : qb ≫ qb' = ρ.Eb.act ⟨((rbar : ℚ) : ℍ[ℚ, a, b]), hrb⟩ := by
    apply hgb.hom_ext
    · simp only [Category.assoc, hqb'_g, reassoc_of% hqb_g, (cq hrb).1, agb]
    · simp only [Category.assoc, hqb', hqb, ρ.Eb.act_over]
  have hc2 : qb' ≫ qb = Ebf.act ⟨((rbar : ℚ) : ℍ[ℚ, a, b]), hrb⟩ := by
    apply hgbf.hom_ext
    · simp only [Category.assoc, hqb_g, reassoc_of% hqb'_g, (cq hrb).2, agbf]
    · simp only [Category.assoc, hqb, hqb', Ebf.act_over]
  have aqb : ∀ x : ↥Λ, ρ.Eb.act x ≫ qb = qb ≫ Ebf.act x := by
    intro x
    apply hgbf.hom_ext
    · simp only [Category.assoc, hqb_g, reassoc_of% hqb_g, agbf, reassoc_of% (agb x), aq]
    · simp only [Category.assoc, hqb, ρ.Eb.act_over, Ebf.act_over]
  have aqb' : ∀ x : ↥Λ, Ebf.act x ≫ qb' = qb' ≫ ρ.Eb.act x := by
    intro x
    apply hgb.hom_ext
    · simp only [Category.assoc, hqb'_g, reassoc_of% hqb'_g, agb, reassoc_of% (agbf x), aq']
    · simp only [Category.assoc, hqb', ρ.Eb.act_over, Ebf.act_over]
  have mqb := fun {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of (B ⧸ Ideal.span {algebraMap 𝒪 B π})))
      (P Q : SchemeHomOver t ρ.Eb.f) => lift_mul hgb hgbf mgb mgbf q hq mq qb hqb hqb_g t P Q
  have mqb' := fun {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of (B ⧸ Ideal.span {algebraMap 𝒪 B π})))
      (P Q : SchemeHomOver t Ebf.f) => lift_mul hgbf hgb mgbf mgb q' hq' mq' qb' hqb' hqb'_g t P Q
  have nqb : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of (B ⧸ Ideal.span {algebraMap 𝒪 B π})))
      (P : SchemeHomOver t ρ.Eb.f), mapPt qb' hqb' (mapPt qb hqb P) = nsmulPt ρ.Eb.L t rbar P := by
    intro T t P
    rw [← CerednikDrinfeld.QM.FakeEllipticCurve.pushPt_act_natCast_eq_nsmulPt ρ.Eb h1 rbar hrb t P]
    apply Subtype.ext; simp only [mapPt_coe, pushPt, Category.assoc, hc1]
  have nqb' : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of (B ⧸ Ideal.span {algebraMap 𝒪 B π})))
      (P : SchemeHomOver t Ebf.f), mapPt qb hqb (mapPt qb' hqb' P) = nsmulPt Ebf.L t rbar P := by
    intro T t P
    rw [← CerednikDrinfeld.QM.FakeEllipticCurve.pushPt_act_natCast_eq_nsmulPt Ebf h1 rbar hrb t P]
    apply Subtype.ext; simp only [mapPt_coe, pushPt, Category.assoc, hc2]
  obtain ⟨hfiq, hflq, -, hsuq⟩ :=
    CerednikDrinfeld.QM.FakeEllipticCurve.isFinite_flat_surjective_of_mapPt_mapPt_eq_nsmulPt
      ρ.Eb Ebf qb hqb mqb qb' hqb' rbar hrbp.pos nqb nqb'
  haveI := hfiq; haveI := hflq; haveI := hsuq
  haveI : EffectiveEpi qb := inferInstance

  have kqb : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of (B ⧸ Ideal.span {algebraMap 𝒪 B π})))
      (P : SchemeHomOver t ρ.Eb.f),
      mapPt qb hqb P = Ebf.L.one t ↔
        ∀ (m : ↥Λ) (n : ℤ), (m : ℍ[ℚ, a, b]) * star (m : ℍ[ℚ, a, b]) = (((rbar : ℤ) * n : ℚ) : ℍ[ℚ, a, b]) →
          pushPt (ρ.Eb.act m) (ρ.Eb.act_over m) P = ρ.Eb.L.one t := by
    intro T t P
    constructor
    · intro hP m n hmn
      apply img_injective hgb
      rw [img_pushPt hgb (E.act m) (E.act_over m) (ρ.Eb.act m) (ρ.Eb.act_over m) (agb m), img_one hgb E.L ρ.Eb.L mgb]
      refine (kq _ (img hgb P)).1 ?_ m n hmn
      rw [← img_mapPt hgb hgbf q hq qb hqb hqb_g, hP, img_one hgbf Ef.L Ebf.L mgbf]
    · intro hP
      apply img_injective hgbf
      rw [img_mapPt hgb hgbf q hq qb hqb hqb_g, img_one hgbf Ef.L Ebf.L mgbf]
      refine (kq _ (img hgb P)).2 ?_
      intro m n hmn
      rw [← img_pushPt hgb (E.act m) (E.act_over m) (ρ.Eb.act m) (ρ.Eb.act_over m) (agb m), hP m n hmn,
        img_one hgb E.L ρ.Eb.L mgb]

  let ewb : ρ.Ab.A ⟶ ρ.Ab.A := hgA.lift (ρ.gA ≫ aw ≫ bw) ρ.Ab.f
    (by rw [Category.assoc, Category.assoc, hbw, haw]; exact hgA.w)
  have hewb_g : ewb ≫ ρ.gA = ρ.gA ≫ aw ≫ bw := hgA.lift_fst _ _ _
  have hewb : ewb ≫ ρ.Ab.f = ρ.Ab.f := hgA.lift_snd _ _ _
  let ewb' : ρ.Ab.A ⟶ ρ.Ab.A := hgA.lift (ρ.gA ≫ bw' ≫ aw') ρ.Ab.f
    (by rw [Category.assoc, Category.assoc, haw', hbw'₁]; exact hgA.w)
  have hewb'_g : ewb' ≫ ρ.gA = ρ.gA ≫ bw' ≫ aw' := hgA.lift_fst _ _ _
  have hewb' : ewb' ≫ ρ.Ab.f = ρ.Ab.f := hgA.lift_snd _ _ _
  have hawbw : (aw ≫ bw) ≫ A₀.f = A₀.f := by rw [Category.assoc, hbw, haw]
  have hbwaw : (bw' ≫ aw') ≫ A₀.f = A₀.f := by rw [Category.assoc, haw', hbw'₁]
  have mawbw := fun {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of (Onr ⧸ Ideal.span {algebraMap 𝒪 Onr π}))) (P Q : SchemeHomOver t A₀.f) =>
    comp_mul aw haw bw hbw hawbw maw mbw t P Q
  have mbwaw := fun {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of (Onr ⧸ Ideal.span {algebraMap 𝒪 Onr π}))) (P Q : SchemeHomOver t A₀.f) =>
    comp_mul bw' hbw'₁ aw' haw' hbwaw mbw' maw' t P Q
  have mewb := fun {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of (B ⧸ Ideal.span {algebraMap 𝒪 B π})))
      (P Q : SchemeHomOver t ρ.Ab.f) => lift_mul hgA hgA mgA mgA (aw ≫ bw) hawbw mawbw ewb hewb hewb_g t P Q
  have mewb' := fun {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of (B ⧸ Ideal.span {algebraMap 𝒪 B π})))
      (P Q : SchemeHomOver t ρ.Ab.f) => lift_mul hgA hgA mgA mgA (bw' ≫ aw') hbwaw mbwaw ewb' hewb' hewb'_g t P Q
  have aewb : ∀ x : ↥Λ, ρ.Ab.act x ≫ ewb = ewb ≫ ρ.Ab.act x := by
    intro x
    apply hgA.hom_ext
    · simp only [Category.assoc, hewb_g, reassoc_of% hewb_g, agA, reassoc_of% (agA x), reassoc_of% (aaw x), abw]
    · simp only [Category.assoc, hewb, ρ.Ab.act_over]
  have aewb' : ∀ x : ↥Λ, ρ.Ab.act x ≫ ewb' = ewb' ≫ ρ.Ab.act x := by
    intro x
    apply hgA.hom_ext
    · simp only [Category.assoc, hewb'_g, reassoc_of% hewb'_g, agA, reassoc_of% (agA x), reassoc_of% (abw' x), aaw']
    · simp only [Category.assoc, hewb', ρ.Ab.act_over]
  have hrdw : (((r ^ dw : ℕ) : ℚ) : ℍ[ℚ, a, b]) ∈ Λ := hnat _

  have hee' : ewb ≫ ewb' = ρ.Ab.act ⟨((rbar : ℚ) : ℍ[ℚ, a, b]), hrb⟩ ≫ ρ.Ab.act ⟨(((r ^ dw : ℕ) : ℚ) : ℍ[ℚ, a, b]), hrdw⟩ := by
    apply hgA.hom_ext
    · simp only [Category.assoc, hewb'_g, reassoc_of% hewb_g, reassoc_of% (cbw hrdw).1, aaw',
        reassoc_of% (caw hrb).1, agA, reassoc_of% (agA _)]
    · simp only [Category.assoc, hewb', hewb, ρ.Ab.act_over]
  have he'e : ewb' ≫ ewb = ρ.Ab.act ⟨(((r ^ dw : ℕ) : ℚ) : ℍ[ℚ, a, b]), hrdw⟩ ≫ ρ.Ab.act ⟨((rbar : ℚ) : ℍ[ℚ, a, b]), hrb⟩ := by
    apply hgA.hom_ext
    · simp only [Category.assoc, hewb_g, reassoc_of% hewb'_g, reassoc_of% (caw hrb).2, abw,
        reassoc_of% (cbw hrdw).2, agA, reassoc_of% (agA _)]
    · simp only [Category.assoc, hewb', hewb, ρ.Ab.act_over]

  have hφe : (ρ.φ ≫ ewb) ≫ ρ.Ab.f = ρ.Eb.f := by rw [Category.assoc, hewb, hφo]
  have mφe := fun {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of (B ⧸ Ideal.span {algebraMap 𝒪 B π}))) (P Q : SchemeHomOver t ρ.Eb.f) =>
    comp_mul ρ.φ hφo ewb hewb hφe mφ mewb t P Q
  have k1 : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of (B ⧸ Ideal.span {algebraMap 𝒪 B π})))
      (P : SchemeHomOver t ρ.Eb.f), mapPt qb hqb P = Ebf.L.one t → mapPt (ρ.φ ≫ ewb) hφe P = ρ.Ab.L.one t := by
    intro T t P hP
    have hk := (kqb t P).1 hP

    have hkA : ∀ (m : ↥Λ) (n : ℤ), (m : ℍ[ℚ, a, b]) * star (m : ℍ[ℚ, a, b]) = (((rbar : ℤ) * n : ℚ) : ℍ[ℚ, a, b]) →
        pushPt (ρ.Ab.act m) (ρ.Ab.act_over m) (mapPt ρ.φ hφo P) = ρ.Ab.L.one t := by
      intro m n hmn
      rw [pushPt_mapPt ρ.φ hφo (ρ.Eb.act m) (ρ.Eb.act_over m) (ρ.Ab.act m) (ρ.Ab.act_over m) (aφ m), hk m n hmn,
        mapPt_one ρ.φ hφo mφ]

    have hY0 : mapPt aw haw (img hgA (mapPt ρ.φ hφo P)) = A₀f.L.one _ :=
      (kaw _ (img hgA (mapPt ρ.φ hφo P))).2 (fun m n hmn => by
        rw [← img_pushPt hgA (A₀.act m) (A₀.act_over m) (ρ.Ab.act m) (ρ.Ab.act_over m) (agA m), hkA m n hmn,
          img_one hgA A₀.L ρ.Ab.L mgA])
    have hY1 : mapPt (aw ≫ bw) hawbw (img hgA (mapPt ρ.φ hφo P)) = A₀.L.one _ := by
      rw [mapPt_comp' aw haw bw hbw, hY0, mapPt_one bw hbw mbw]
    rw [mapPt_comp' ρ.φ hφo ewb hewb]
    apply img_injective hgA
    rw [img_mapPt hgA hgA (aw ≫ bw) hawbw ewb hewb hewb_g, hY1, img_one hgA A₀.L ρ.Ab.L mgA]
  let χ : Ebf.A ⟶ ρ.Ab.A := EffectiveEpi.desc qb (ρ.φ ≫ ewb) (coeq ρ.Eb Ebf ρ.Ab qb hqb (ρ.φ ≫ ewb) hφe mqb mφe k1)
  have hfac : qb ≫ χ = ρ.φ ≫ ewb := EffectiveEpi.fac qb (ρ.φ ≫ ewb) _
  have hχ : χ ≫ ρ.Ab.f = Ebf.f := by
    rw [← cancel_epi qb, ← Category.assoc, hfac, hφe, hqb]
  have mχ := fun {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of (B ⧸ Ideal.span {algebraMap 𝒪 B π})))
      (P Q : SchemeHomOver t Ebf.f) => desc_mul qb hqb mqb χ hχ (ρ.φ ≫ ewb) hφe hfac mφe t P Q

  let α : ρ.Ab.A ⟶ ρ.Ab.A := ρ.Ab.act ⟨((rbar : ℚ) : ℍ[ℚ, a, b]), hrb⟩
  have hα : α ≫ ρ.Ab.f = ρ.Ab.f := ρ.Ab.act_over _
  have mα : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of (B ⧸ Ideal.span {algebraMap 𝒪 B π})))
      (P Q : SchemeHomOver t ρ.Ab.f), mapPt α hα (ρ.Ab.L.mul t P Q) = ρ.Ab.L.mul t (mapPt α hα P) (mapPt α hα Q) :=
    fun t P Q => ρ.Ab.act_hom _ t P Q
  have hid : 𝟙 ρ.Ab.A ≫ ρ.Ab.f = ρ.Ab.f := Category.id_comp _
  have nα : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of (B ⧸ Ideal.span {algebraMap 𝒪 B π})))
      (P : SchemeHomOver t ρ.Ab.f), mapPt (𝟙 _) hid (mapPt α hα P) = nsmulPt ρ.Ab.L t rbar P := by
    intro T t P
    rw [mapPt_id', ← CerednikDrinfeld.QM.FakeEllipticCurve.pushPt_act_natCast_eq_nsmulPt ρ.Ab h1 rbar hrb t P]
  have nα' : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of (B ⧸ Ideal.span {algebraMap 𝒪 B π})))
      (P : SchemeHomOver t ρ.Ab.f), mapPt α hα (mapPt (𝟙 _) hid P) = nsmulPt ρ.Ab.L t rbar P := by
    intro T t P
    rw [mapPt_id', ← CerednikDrinfeld.QM.FakeEllipticCurve.pushPt_act_natCast_eq_nsmulPt ρ.Ab h1 rbar hrb t P]
  obtain ⟨hfiα, hflα, -, hsuα⟩ :=
    CerednikDrinfeld.QM.FakeEllipticCurve.isFinite_flat_surjective_of_mapPt_mapPt_eq_nsmulPt
      ρ.Ab ρ.Ab α hα mα (𝟙 _) hid rbar hrbp.pos nα nα'
  haveI := hfiα; haveI := hflα; haveI := hsuα
  haveI : EffectiveEpi α := inferInstance
  have hβ : (ewb' ≫ ρ.φ' ≫ qb) ≫ Ebf.f = ρ.Ab.f := by rw [Category.assoc, Category.assoc, hqb, hφ'o, hewb']
  have hφ'q : (ρ.φ' ≫ qb) ≫ Ebf.f = ρ.Ab.f := by rw [Category.assoc, hqb, hφ'o]
  have mφ'q := fun {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of (B ⧸ Ideal.span {algebraMap 𝒪 B π}))) (P Q : SchemeHomOver t ρ.Ab.f) =>
    comp_mul ρ.φ' hφ'o qb hqb hφ'q mφ' mqb t P Q
  have mβ := fun {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of (B ⧸ Ideal.span {algebraMap 𝒪 B π}))) (P Q : SchemeHomOver t ρ.Ab.f) =>
    comp_mul ewb' hewb' (ρ.φ' ≫ qb) hφ'q hβ mewb' mφ'q t P Q
  have k2 : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of (B ⧸ Ideal.span {algebraMap 𝒪 B π})))
      (P : SchemeHomOver t ρ.Ab.f), mapPt α hα P = ρ.Ab.L.one t → mapPt (ewb' ≫ ρ.φ' ≫ qb) hβ P = Ebf.L.one t := by
    intro T t P hP
    rw [mapPt_comp' ewb' hewb' (ρ.φ' ≫ qb) hφ'q, mapPt_comp' ρ.φ' hφ'o qb hqb]
    apply (kqb t _).2
    intro m n hmn

    have hQ : mapPt aw haw (mapPt aw' haw' (mapPt bw' hbw'₁ (img hgA P))) = A₀f.L.one _ := by
      have e2 : mapPt aw haw (mapPt aw' haw' (mapPt bw' hbw'₁ (img hgA P))) =
          pushPt (A₀f.act ⟨((rbar : ℚ) : ℍ[ℚ, a, b]), hrb⟩) (A₀f.act_over _) (mapPt bw' hbw'₁ (img hgA P)) :=
        Subtype.ext (by simp only [mapPt_coe, pushPt, Category.assoc, (caw hrb).2])
      rw [e2, pushPt_mapPt bw' hbw'₁ (A₀.act _) (A₀.act_over _) (A₀f.act _) (A₀f.act_over _) (abw' _),
        ← img_pushPt hgA (A₀.act _) (A₀.act_over _) (ρ.Ab.act _) (ρ.Ab.act_over _) (agA _)]
      change mapPt bw' hbw'₁ (img hgA (mapPt α hα P)) = _
      rw [hP, img_one hgA A₀.L ρ.Ab.L mgA, mapPt_one bw' hbw'₁ mbw']
    have hm0 := (kaw _ _).1 hQ m n hmn
    have hX : pushPt (ρ.Ab.act m) (ρ.Ab.act_over m) (mapPt ewb' hewb' P) = ρ.Ab.L.one t := by
      apply img_injective hgA
      rw [img_pushPt hgA (A₀.act m) (A₀.act_over m) (ρ.Ab.act m) (ρ.Ab.act_over m) (agA m),
        img_mapPt hgA hgA (bw' ≫ aw') hbwaw ewb' hewb' hewb'_g, mapPt_comp' bw' hbw'₁ aw' haw', hm0,
        img_one hgA A₀.L ρ.Ab.L mgA]
    rw [pushPt_mapPt ρ.φ' hφ'o (ρ.Ab.act m) (ρ.Ab.act_over m) (ρ.Eb.act m) (ρ.Eb.act_over m) (aφ' m), hX,
      mapPt_one ρ.φ' hφ'o mφ']
  let χ' : ρ.Ab.A ⟶ Ebf.A := EffectiveEpi.desc α (ewb' ≫ ρ.φ' ≫ qb)
    (coeq ρ.Ab ρ.Ab Ebf α hα (ewb' ≫ ρ.φ' ≫ qb) hβ mα mβ k2)
  have hfac' : α ≫ χ' = ewb' ≫ ρ.φ' ≫ qb := EffectiveEpi.fac α (ewb' ≫ ρ.φ' ≫ qb) _
  have hχ'o : χ' ≫ Ebf.f = ρ.Ab.f := by
    rw [← cancel_epi α, ← Category.assoc, hfac', hβ, hα]
  have mχ' := fun {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of (B ⧸ Ideal.span {algebraMap 𝒪 B π})))
      (P Q : SchemeHomOver t ρ.Ab.f) => desc_mul α hα mα χ' hχ'o (ewb' ≫ ρ.φ' ≫ qb) hβ hfac' mβ t P Q

  have hrd : (((r ^ ρ.d : ℕ) : ℚ) : ℍ[ℚ, a, b]) ∈ Λ := hnat _
  have aχ : ∀ x : ↥Λ, Ebf.act x ≫ χ = χ ≫ ρ.Ab.act x := by
    intro x
    rw [← cancel_epi qb, ← Category.assoc, ← aqb, Category.assoc, hfac, ← Category.assoc qb, hfac,
      ← Category.assoc, aφ, Category.assoc, aewb, Category.assoc]
  have aχ' : ∀ x : ↥Λ, ρ.Ab.act x ≫ χ' = χ' ≫ Ebf.act x := by
    intro x
    rw [← cancel_epi α, ← Category.assoc,
      show α ≫ ρ.Ab.act x = ρ.Ab.act x ≫ α from (act_comm_natCast ρ.Ab x rbar hrb).symm,
      Category.assoc, hfac', reassoc_of% hfac', reassoc_of% (aewb' x), reassoc_of% (aφ' x), aqb]

  have heχ' : ewb ≫ χ' = ρ.Ab.act ⟨(((r ^ dw : ℕ) : ℚ) : ℍ[ℚ, a, b]), hrdw⟩ ≫ ρ.φ' ≫ qb := by
    rw [← cancel_epi α, ← Category.assoc, show α ≫ ewb = ewb ≫ α from (aewb _), Category.assoc, hfac',
      ← Category.assoc ewb, hee', Category.assoc]
  have hpair : FakeEllipticCurve.IsIsogenyPair (r ^ (ρ.d + dw)) Ebf ρ.Ab χ χ' := by
    refine ⟨hχ, hχ'o, mχ, mχ', aχ, aχ', ?_⟩
    intro hd
    constructor
    · rw [← cancel_epi qb, reassoc_of% hfac, heχ', ← reassoc_of% (aφ ⟨_, hrdw⟩), reassoc_of% (cφ hrd).1,
        aqb, reassoc_of% (aqb ⟨_, hrdw⟩), act_natCast_comp Ebf (r ^ dw) (r ^ ρ.d) hrdw hrd (hnat _)]
      congr 1
      exact act_congr Ebf (by rw [show (r ^ ρ.d * r ^ dw : ℕ) = r ^ (ρ.d + dw) by ring]) _ _
    · rw [← cancel_epi α, reassoc_of% hfac', hfac, reassoc_of% (cφ hrd).2, ← reassoc_of% (aewb' ⟨_, hrd⟩), he'e,
        ← Category.assoc, act_natCast_comp ρ.Ab (r ^ ρ.d) (r ^ dw) hrd hrdw (hnat _), act_comm_natCast ρ.Ab _ rbar hrb]
      congr 1
      exact act_congr ρ.Ab (by rw [show (r ^ dw * r ^ ρ.d : ℕ) = r ^ (ρ.d + dw) by ring]) _ _

  have lqb : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of (B ⧸ Ideal.span {algebraMap 𝒪 B π})))
      (P : SchemeHomOver t ρ.Eb.f), FactorsThrough ρ.Eb.lev P → FactorsThrough Ebf.lev (mapPt qb hqb P) := by
    intro T t P hP
    apply lgbf'
    obtain ⟨P₀, hP₀⟩ := lq _ (img hgb P) (lgb t P hP)
    exact ⟨P₀, by rw [hP₀]; simp only [mapPt_coe, img_coe, Category.assoc, hqb_g]⟩
  have hlev : FakeEllipticCurve.PreservesLevel Ebf ρ.Ab χ hχ := by
    intro T t R hR
    obtain ⟨P, hP, rfl⟩ :=
      (CerednikDrinfeld.QM.FakeEllipticCurve.factorsThrough_lev_iff_exists_mapPt_eq_of_coprime
        ρ.Eb Ebf qb hqb mqb qb' hqb' rbar hcop nqb lqb t R).1 hR
    have hY := ρ.preservesLevel t P hP
    rw [← mapPt_comp' qb hqb χ hχ (by rw [Category.assoc, hχ, hqb])]
    have e1 : mapPt (qb ≫ χ) (by rw [Category.assoc, hχ, hqb]) P = mapPt (ρ.φ ≫ ewb) hφe P :=
      Subtype.ext (by simp only [mapPt_coe, hfac])
    rw [e1, mapPt_comp' ρ.φ hφo ewb hewb]
    apply CerednikDrinfeld.QM.FakeEllipticCurve.factorsThrough_lev_of_exists_comp_eq_of_isPullback _ A₀ ρ.Ab ρ.gA
      hgA mgA lgA
    obtain ⟨P₀, hP₀⟩ := hBWlev _ _ (law _ (img hgA (mapPt ρ.φ hφo P)) (lgA t _ hY))
    exact ⟨P₀, by rw [hP₀]; simp only [mapPt_coe, img_coe, Category.assoc, hewb_g]⟩

  let ρf : FakeEllipticCurve.Rigidification r π A₀ ψ Ef :=
    { Eb := Ebf, gb := gbf, isPullback_Eb := ⟨hgbf, mgbf, agbf, lgbf⟩, Ab := ρ.Ab, gA := ρ.gA,
      isPullback_Ab := ρ.isPullback_Ab, d := ρ.d + dw, φ := χ, φ' := χ', φ_over := hχ, isIsogenyPair := hpair,
      preservesLevel := hlev }
  refine ⟨ρf, qb, hqb_g, hqb, 𝟙 _, isPullbackVia_id ρ.Ab, Category.id_comp _, ewb, hewb_g, hewb, 0, 0, ?_⟩
  show qb ≫ χ ≫ 𝟙 _ ≫ _ = ρ.φ ≫ ewb ≫ _
  rw [Category.id_comp, ← Category.assoc, hfac, Category.assoc]

end S_CerednikDrinfeld_QM_FakeEllipticCurve_exists_rigidification_of_isAtkinLehnerQuotient
end P2MW
export P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_exists_rigidification_of_isAtkinLehnerQuotient (solution)
