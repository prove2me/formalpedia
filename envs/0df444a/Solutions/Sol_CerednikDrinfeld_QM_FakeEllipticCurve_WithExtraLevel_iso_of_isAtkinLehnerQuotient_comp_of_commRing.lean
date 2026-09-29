-- Prove2me | solution 1 for CerednikDrinfeld.QM.FakeEllipticCurve.WithExtraLevel.iso_of_isAtkinLehnerQuotient_comp_of_commRing
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.837917+00:00
-- url     : https://prove2.me/submissions/57eff370-2dd5-5bde-89d9-14ca58279f1f

import Mathlib
import Definitions.Def_CerednikDrinfeld_QMModuliProps
import Definitions.Def_CerednikDrinfeld_FakeEllipticFrobenius
import Theorems.Thm_QuaternionAlgebra_IsOrder_exists_intCast_eq_nrd_and_exists_intCast_eq_trd
import Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_isFinite_flat_surjective_of_mapPt_mapPt_eq_nsmulPt
import Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_factorsThrough_lev_iff_exists_mapPt_eq_of_coprime
import Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_pushPt_act_natCast_eq_nsmulPt
import Theorems.Thm_QuaternionAlgebra_IsMaximalOrder_span_mul_ramifiedPrime_eq_of_isIndefiniteRamifiedExactlyAt
import Theorems.Thm_AlgebraicGeometry_isIso_of_isClosedImmersion_of_finrank_comp_eq
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_WithExtraLevel_iso_of_isAtkinLehnerQuotient_comp_of_commRing
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
p2m_attr_erase "simp" "AlgebraicGeometry.ProjSpace.twistGradeToObj_val AlgebraicGeometry.ProjSpace.twistObj.smul_val AlgebraicGeometry.ProjSpace.twistGradeEquiv_apply_val AlgebraicGeometry.ProjSpace.twistObj.mk.sizeOf_spec AlgebraicGeometry.schemeFibreEndo_snd AlgebraicGeometry.schemeFibreEndo_fst QuaternionAlgebra.ClassSet.map_mk QuaternionAlgebra.baseChangeRight_tmul QuaternionAlgebra.mapOfAlgebraMapEq_apply QuaternionAlgebra.baseChange_tmul"

set_option autoImplicit false

universe u

p2m_open "CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra~schemeHomOverComp~schemeHomOverComp_coe GoodReductionJacobian"
open CerednikDrinfeld.QM CerednikDrinfeld.QM.FakeEllipticCurve
open scoped Quaternion

namespace ALGlue

variable {S : Type u} [CommRing S]

section IsoPts

variable {A A' : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of S)} {f' : A' ⟶ Spec (CommRingCat.of S)}

theorem inv_over (e : A ≅ A') (he : e.hom ≫ f' = f) : e.inv ≫ f = f' := by
  rw [← he, Iso.inv_hom_id_assoc]

@[scoped simp] theorem mapPt_inv_hom (e : A ≅ A') (he : e.hom ≫ f' = f) {T : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of S)}
    (P : SchemeHomOver t f) : mapPt e.inv (inv_over e he) (mapPt e.hom he P) = P := by
  apply Subtype.ext; simp [mapPt_coe]

@[scoped simp] theorem mapPt_hom_inv (e : A ≅ A') (he : e.hom ≫ f' = f) {T : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of S)}
    (P : SchemeHomOver t f') : mapPt e.hom he (mapPt e.inv (inv_over e he) P) = P := by
  apply Subtype.ext; simp [mapPt_coe]

theorem mapPt_hom_injective (e : A ≅ A') (he : e.hom ≫ f' = f) {T : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of S)} :
    Function.Injective (mapPt (T := T) (t := t) e.hom he) := by
  intro P Q h
  rw [← mapPt_inv_hom e he P, h, mapPt_inv_hom]

theorem mapPt_comp {A'' : Scheme.{u}} {f'' : A'' ⟶ Spec (CommRingCat.of S)} (θ : A ⟶ A') (hθ : θ ≫ f' = f)
    (θ' : A' ⟶ A'') (hθ' : θ' ≫ f'' = f') {T : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of S)} (P : SchemeHomOver t f) :
    mapPt (θ ≫ θ') (by rw [Category.assoc, hθ', hθ]) P = mapPt θ' hθ' (mapPt θ hθ P) := by
  apply Subtype.ext; simp [mapPt_coe]

end IsoPts

variable {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} {N : ℕ}

theorem inv_mul {E E' : FakeEllipticCurve Λ N S} (e : E.A ≅ E'.A) (he : e.hom ≫ E'.f = E.f)
    (hmul : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of S)) (P Q : SchemeHomOver t E.f),
      mapPt e.hom he (E.L.mul t P Q) = E'.L.mul t (mapPt e.hom he P) (mapPt e.hom he Q))
    {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of S)) (P Q : SchemeHomOver t E'.f) :
    mapPt e.inv (inv_over e he) (E'.L.mul t P Q) = E.L.mul t (mapPt e.inv (inv_over e he) P) (mapPt e.inv (inv_over e he) Q) := by
  apply mapPt_hom_injective e he
  rw [mapPt_hom_inv, hmul, mapPt_hom_inv, mapPt_hom_inv]

theorem inv_act {E E' : FakeEllipticCurve Λ N S} (e : E.A ≅ E'.A)
    (hact : ∀ x : ↥Λ, E.act x ≫ e.hom = e.hom ≫ E'.act x) (x : ↥Λ) :
    E'.act x ≫ e.inv = e.inv ≫ E.act x := by
  rw [← cancel_epi e.hom, ← Category.assoc, ← hact x, Category.assoc, e.hom_inv_id, Category.comp_id, e.hom_inv_id_assoc]

theorem iso_symm {E E' : FakeEllipticCurve Λ N S} (h : FakeEllipticCurve.Iso E E') : FakeEllipticCurve.Iso E' E := by
  obtain ⟨e, he, hmul, hact, hlev⟩ := h
  refine ⟨e.symm, inv_over e he, ?_, ?_, ?_⟩
  · intro T t P Q; exact inv_mul e he hmul t P Q
  · intro x; exact inv_act e hact x
  · intro T t P
    change FactorsThrough E'.lev P ↔ FactorsThrough E.lev (mapPt e.inv (inv_over e he) P)
    rw [hlev t (mapPt e.inv (inv_over e he) P), mapPt_hom_inv]

theorem iso_trans {E E' E'' : FakeEllipticCurve Λ N S} (h : FakeEllipticCurve.Iso E E') (h' : FakeEllipticCurve.Iso E' E'') :
    FakeEllipticCurve.Iso E E'' := by
  obtain ⟨e, he, hmul, hact, hlev⟩ := h
  obtain ⟨e', he', hmul', hact', hlev'⟩ := h'
  have hee : (e ≪≫ e').hom ≫ E''.f = E.f := by rw [Iso.trans_hom, Category.assoc, he', he]
  have hpt : ∀ {T : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of S)} (P : SchemeHomOver t E.f),
      mapPt (e ≪≫ e').hom hee P = mapPt e'.hom he' (mapPt e.hom he P) := fun P => by
    apply Subtype.ext; simp [mapPt_coe]
  refine ⟨e ≪≫ e', hee, ?_, ?_, ?_⟩
  · intro T t P Q; rw [hpt, hpt, hpt, hmul, hmul']
  · intro x; rw [Iso.trans_hom, ← Category.assoc, hact, Category.assoc, hact', Category.assoc]
  · intro T t P; rw [hpt, hlev, hlev']

theorem iso_refl (E : FakeEllipticCurve Λ N S) : FakeEllipticCurve.Iso E E := by
  have h1 : (Iso.refl E.A).hom ≫ E.f = E.f := by simp
  have hid : ∀ {T : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of S)} (P : SchemeHomOver t E.f),
      mapPt (Iso.refl E.A).hom h1 P = P := fun P => Subtype.ext (by simp [mapPt_coe])
  refine ⟨Iso.refl _, h1, ?_, ?_, ?_⟩
  · intro T t P Q; rw [hid, hid, hid]
  · intro x; simp
  · intro T t P; rw [hid]

theorem isAtkinLehnerQuotient_congr (r : ℕ) {E E₁ F F₁ : FakeEllipticCurve Λ N S}
    (h : E.IsAtkinLehnerQuotient r E₁) (hE : FakeEllipticCurve.Iso E F) (hE₁ : FakeEllipticCurve.Iso E₁ F₁) :
    F.IsAtkinLehnerQuotient r F₁ := by
  obtain ⟨e, he, emul, eact, elev⟩ := hE
  obtain ⟨e₁, he₁, e₁mul, e₁act, e₁lev⟩ := hE₁
  obtain ⟨φr, hφr, ψr, hψr, hφhom, hψhom, hφlin, hψlin, hcomp, hker, hlev⟩ := h
  have hφ' : (e.inv ≫ φr ≫ e₁.hom) ≫ F₁.f = F.f := by
    rw [Category.assoc, Category.assoc, he₁, hφr, inv_over e he]
  have hψ' : (e₁.inv ≫ ψr ≫ e.hom) ≫ F.f = F₁.f := by
    rw [Category.assoc, Category.assoc, he, hψr, inv_over e₁ he₁]

  have tφ : ∀ {T : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of S)} (P : SchemeHomOver t F.f),
      mapPt (e.inv ≫ φr ≫ e₁.hom) hφ' P = mapPt e₁.hom he₁ (mapPt φr hφr (mapPt e.inv (inv_over e he) P)) :=
    fun P => Subtype.ext (by simp [mapPt_coe])
  have tψ : ∀ {T : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of S)} (P : SchemeHomOver t F₁.f),
      mapPt (e₁.inv ≫ ψr ≫ e.hom) hψ' P = mapPt e.hom he (mapPt ψr hψr (mapPt e₁.inv (inv_over e₁ he₁) P)) :=
    fun P => Subtype.ext (by simp [mapPt_coe])

  have one_e : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of S)), mapPt e.inv (inv_over e he) (F.L.one t) = E.L.one t := by
    intro T t
    set x := mapPt e.inv (inv_over e he) (F.L.one t) with hx
    have hxx : E.L.mul t x x = x := by rw [hx, ← inv_mul e he emul, F.L.one_mul]
    letI := E.L.pointGroup t
    have h2 : x * x = x * 1 := by rw [mul_one]; exact hxx
    exact mul_left_cancel h2
  have one_e₁ : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of S)), mapPt e₁.hom he₁ (E₁.L.one t) = F₁.L.one t := by
    intro T t
    set x := mapPt e₁.hom he₁ (E₁.L.one t) with hx
    have hxx : F₁.L.mul t x x = x := by rw [hx, ← e₁mul, E₁.L.one_mul]
    letI := F₁.L.pointGroup t
    have h2 : x * x = x * 1 := by rw [mul_one]; exact hxx
    exact mul_left_cancel h2
  refine ⟨e.inv ≫ φr ≫ e₁.hom, hφ', e₁.inv ≫ ψr ≫ e.hom, hψ', ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro T t P Q
    rw [tφ, tφ, tφ, inv_mul e he emul, hφhom, e₁mul]
  · intro T t P Q
    rw [tψ, tψ, tψ, inv_mul e₁ he₁ e₁mul, hψhom, emul]
  · intro x
    calc F.act x ≫ (e.inv ≫ φr ≫ e₁.hom) = (F.act x ≫ e.inv) ≫ φr ≫ e₁.hom := by simp only [Category.assoc]
      _ = e.inv ≫ (E.act x ≫ φr) ≫ e₁.hom := by rw [inv_act e eact x]; simp only [Category.assoc]
      _ = e.inv ≫ φr ≫ (E₁.act x ≫ e₁.hom) := by rw [hφlin x]; simp only [Category.assoc]
      _ = (e.inv ≫ φr ≫ e₁.hom) ≫ F₁.act x := by rw [e₁act x]; simp only [Category.assoc]
  · intro x
    calc F₁.act x ≫ (e₁.inv ≫ ψr ≫ e.hom) = (F₁.act x ≫ e₁.inv) ≫ ψr ≫ e.hom := by simp only [Category.assoc]
      _ = e₁.inv ≫ (E₁.act x ≫ ψr) ≫ e.hom := by rw [inv_act e₁ e₁act x]; simp only [Category.assoc]
      _ = e₁.inv ≫ ψr ≫ (E.act x ≫ e.hom) := by rw [hψlin x]; simp only [Category.assoc]
      _ = (e₁.inv ≫ ψr ≫ e.hom) ≫ F.act x := by rw [eact x]; simp only [Category.assoc]
  · intro hr
    obtain ⟨h1, h2⟩ := hcomp hr
    constructor
    · simp only [Category.assoc]
      rw [e₁.hom_inv_id_assoc, ← Category.assoc φr, h1, eact, e.inv_hom_id_assoc]
    · simp only [Category.assoc]
      rw [e.hom_inv_id_assoc, ← Category.assoc ψr, h2, e₁act, e₁.inv_hom_id_assoc]
  · intro T t P
    rw [tφ, ← one_e₁ t, (mapPt_hom_injective e₁ he₁).eq_iff, hker]
    refine forall_congr' fun m => forall_congr' fun n => forall_congr' fun _ => ?_

    have hconj : pushPt (E.act m) (E.act_over m) (mapPt e.inv (inv_over e he) P) =
        mapPt e.inv (inv_over e he) (pushPt (F.act m) (F.act_over m) P) := by
      apply Subtype.ext
      simp only [pushPt, mapPt_coe, Category.assoc, inv_act e eact m]
    rw [hconj, ← one_e t]
    constructor
    · intro hP
      have := congrArg (mapPt e.hom he) hP
      rwa [mapPt_hom_inv, mapPt_hom_inv] at this
    · intro hP; rw [hP]
  · intro T t P hP
    rw [tφ, ← e₁lev]
    apply hlev
    rw [elev, mapPt_hom_inv]
    exact hP

end ALGlue
p2m_reactivate "P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_WithExtraLevel_iso_of_isAtkinLehnerQuotient_comp_of_commRing.ALGlue"

p2m_open "CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra~schemeHomOverComp~schemeHomOverComp_coe GoodReductionJacobian"
open CerednikDrinfeld CerednikDrinfeld.QM CerednikDrinfeld.QM.FakeEllipticCurve QuaternionAlgebra
open scoped Quaternion

namespace ALComm

variable {S : Type u} [CommRing S] {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} {N : ℕ}

abbrev aP (E : FakeEllipticCurve Λ N S) (m : ↥Λ) {T : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of S)}
    (P : SchemeHomOver t E.f) : SchemeHomOver t E.f :=
  pushPt (E.act m) (E.act_over m) P

section Action

variable (E : FakeEllipticCurve Λ N S) {T : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of S)}

theorem aP_coe (m : ↥Λ) (P : SchemeHomOver t E.f) : (aP E m P).1 = P.1 ≫ E.act m := rfl

theorem aP_mul (x y : ↥Λ) (h : (x : ℍ[ℚ, a, b]) * (y : ℍ[ℚ, a, b]) ∈ Λ) (P : SchemeHomOver t E.f) :
    aP E x (aP E y P) = aP E ⟨(x : ℍ[ℚ, a, b]) * (y : ℍ[ℚ, a, b]), h⟩ P := by
  apply Subtype.ext
  simp only [aP_coe, Category.assoc, E.act_mul x y h]

theorem aP_congr {x y : ↥Λ} (h : (x : ℍ[ℚ, a, b]) = (y : ℍ[ℚ, a, b])) (P : SchemeHomOver t E.f) :
    aP E x P = aP E y P := by
  obtain rfl : x = y := Subtype.ext h; rfl

theorem aP_add (x y : ↥Λ) (P : SchemeHomOver t E.f) :
    aP E (x + y) P = E.L.mul t (aP E x P) (aP E y P) := E.act_add x y t P

theorem aP_hom (m : ↥Λ) (P Q : SchemeHomOver t E.f) :
    aP E m (E.L.mul t P Q) = E.L.mul t (aP E m P) (aP E m Q) := E.act_hom m t P Q

theorem aP_one (m : ↥Λ) : aP E m (E.L.one t) = E.L.one t := by
  set x := aP E m (E.L.one t) with hx
  have hxx : E.L.mul t x x = x := by rw [hx, ← aP_hom, E.L.one_mul]
  letI := E.L.pointGroup t
  have h2 : x * x = x * 1 := by rw [mul_one]; exact hxx
  exact mul_left_cancel h2

theorem aP_unit (h1 : (1 : ℍ[ℚ, a, b]) ∈ Λ) (P : SchemeHomOver t E.f) : aP E ⟨1, h1⟩ P = P := by
  apply Subtype.ext
  simp only [aP_coe, E.act_one h1, Category.comp_id]

theorem aP_zero (P : SchemeHomOver t E.f) : aP E 0 P = E.L.one t := by
  have h := aP_add E 0 0 P
  rw [add_zero] at h
  letI := E.L.pointGroup t
  have h2 : aP E 0 P * aP E 0 P = aP E 0 P * 1 := by rw [mul_one]; exact h.symm
  exact mul_left_cancel h2

end Action
p2m_reactivate "P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_WithExtraLevel_iso_of_isAtkinLehnerQuotient_comp_of_commRing.ALGlue"

section Arithmetic

theorem intCast_mem (hΛ : IsOrder Λ) (z : ℤ) : (((z : ℚ)) : ℍ[ℚ, a, b]) ∈ Λ := by
  have : (((z : ℚ)) : ℍ[ℚ, a, b]) = z • (1 : ℍ[ℚ, a, b]) := by
    rw [zsmul_eq_mul, mul_one, coe_intCast]
  rw [this]; exact Λ.smul_mem z hΛ.one_mem

theorem natCast_mem (hΛ : IsOrder Λ) (n : ℕ) : (((n : ℚ)) : ℍ[ℚ, a, b]) ∈ Λ := by
  have := intCast_mem hΛ (n : ℤ); push_cast at this; exact this

def PCond (r : ℕ) (m : ℍ[ℚ, a, b]) : Prop :=
  ∃ n : ℤ, m * star m = ((((r : ℤ) * n : ℚ)) : ℍ[ℚ, a, b])

theorem pcond_natCast (r : ℕ) : PCond (a := a) (b := b) r ((r : ℚ) : ℍ[ℚ, a, b]) :=
  ⟨r, by rw [star_coe, ← coe_mul]; exact congrArg (fun x : ℚ => (x : ℍ[ℚ, a, b])) (by norm_cast)⟩

theorem pcond_intCast_mul (r : ℕ) (z : ℤ) : PCond (a := a) (b := b) r (((z * r : ℤ) : ℚ) : ℍ[ℚ, a, b]) :=
  ⟨z * z * r, by rw [star_coe, ← coe_mul]; congr 1; push_cast; ring⟩

theorem pcond_mul (hΛ : IsOrder Λ) (r : ℕ) {m m' : ℍ[ℚ, a, b]} (hm : PCond r m) (hm' : m' ∈ Λ) :
    PCond r (m * m') := by
  obtain ⟨n, hn⟩ := hm
  obtain ⟨⟨k, hk⟩, -⟩ := QuaternionAlgebra.IsOrder.exists_intCast_eq_nrd_and_exists_intCast_eq_trd hΛ hm'
  refine ⟨n * k, ?_⟩
  calc m * m' * star (m * m') = m * (m' * star m') * star m := by rw [star_mul]; simp only [mul_assoc]
    _ = m * ((nrd m' : ℚ) : ℍ[ℚ, a, b]) * star m := by rw [mul_star_eq_coe_nrd, mul_assoc]
    _ = ((k : ℚ) : ℍ[ℚ, a, b]) * (m * star m) := by rw [← hk, ← coe_commutes, mul_assoc]
    _ = (((((r : ℤ) : ℚ) * ((n * k : ℤ) : ℚ) : ℚ)) : ℍ[ℚ, a, b]) := by
        rw [hn, ← coe_mul]; exact congrArg (fun x : ℚ => (x : ℍ[ℚ, a, b])) (by push_cast; ring)

end Arithmetic
p2m_reactivate "P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_WithExtraLevel_iso_of_isAtkinLehnerQuotient_comp_of_commRing.ALGlue"

section Kernel

variable (E : FakeEllipticCurve Λ N S) {T : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of S)}

def Kill (r : ℕ) (P : SchemeHomOver t E.f) : Prop :=
  ∀ (m : ↥Λ) (n : ℤ), (m : ℍ[ℚ, a, b]) * star (m : ℍ[ℚ, a, b]) = ((((r : ℤ) * n : ℚ)) : ℍ[ℚ, a, b]) →
    aP E m P = E.L.one t

theorem kill_iff (r : ℕ) (P : SchemeHomOver t E.f) :
    Kill E r P ↔ ∀ m : ↥Λ, PCond r (m : ℍ[ℚ, a, b]) → aP E m P = E.L.one t :=
  ⟨fun h m ⟨n, hn⟩ => h m n hn, fun h m n hn => h m ⟨n, hn⟩⟩

theorem swap (hΛ : IsOrder Λ) (q q' : ℕ) (hqq' : Nat.Coprime q q') (P : SchemeHomOver t E.f)
    (A1 : ∀ m : ↥Λ, PCond q' (m : ℍ[ℚ, a, b]) → Kill E q (aP E m P)) :
    ∀ m' : ↥Λ, PCond q (m' : ℍ[ℚ, a, b]) → Kill E q' (aP E m' P) := by
  classical

  obtain ⟨A, B, hAB⟩ := hqq'.isCoprime

  let e₁ : ↥Λ := ⟨(((A * q : ℤ) : ℚ) : ℍ[ℚ, a, b]), intCast_mem hΛ _⟩
  let e₂ : ↥Λ := ⟨(((B * q' : ℤ) : ℚ) : ℍ[ℚ, a, b]), intCast_mem hΛ _⟩
  have he : e₁ + e₂ = ⟨1, hΛ.one_mem⟩ := by
    apply Subtype.ext
    show (((A * q : ℤ) : ℚ) : ℍ[ℚ, a, b]) + (((B * q' : ℤ) : ℚ) : ℍ[ℚ, a, b]) = 1
    rw [← coe_add, ← coe_one]; congr 1; exact_mod_cast hAB
  let cq : ↥Λ := ⟨((q : ℚ) : ℍ[ℚ, a, b]), natCast_mem hΛ q⟩
  let cA : ↥Λ := ⟨((A : ℚ) : ℍ[ℚ, a, b]), intCast_mem hΛ A⟩

  have hP₁ : Kill E q' (aP E e₁ P) := by
    rw [kill_iff]
    intro m hm

    have h1 : aP E cq (aP E m P) = E.L.one t := by
      have := A1 m hm; rw [kill_iff] at this
      exact this cq (pcond_natCast q)
    have hmem : ((q : ℚ) : ℍ[ℚ, a, b]) * (m : ℍ[ℚ, a, b]) ∈ Λ := hΛ.mul_mem cq.2 m.2
    rw [aP_mul E cq m hmem] at h1
    have hmem2 : ((A : ℚ) : ℍ[ℚ, a, b]) * (((q : ℚ) : ℍ[ℚ, a, b]) * (m : ℍ[ℚ, a, b])) ∈ Λ := hΛ.mul_mem cA.2 hmem
    have h2 : aP E ⟨_, hmem2⟩ P = E.L.one t := by
      rw [← aP_mul E cA ⟨_, hmem⟩ hmem2, h1, aP_one]
    rw [aP_mul E m e₁ (hΛ.mul_mem m.2 e₁.2), ← h2]
    apply aP_congr
    show (m : ℍ[ℚ, a, b]) * (((A * q : ℤ) : ℚ) : ℍ[ℚ, a, b]) = ((A : ℚ) : ℍ[ℚ, a, b]) * (((q : ℚ) : ℍ[ℚ, a, b]) * (m : ℍ[ℚ, a, b]))
    simp only [mul_coe_eq_smul, coe_mul_eq_smul, smul_smul]
    congr 1
    push_cast
    ring

  have hP₂ : ∀ m' : ↥Λ, PCond q (m' : ℍ[ℚ, a, b]) → aP E m' (aP E e₂ P) = E.L.one t := by
    intro m' hm'
    have := A1 e₂ (pcond_intCast_mul (a := a) (b := b) q' B); rw [kill_iff] at this
    exact this m' hm'

  intro m' hm'
  rw [kill_iff]
  intro m hm
  have hsplit : P = E.L.mul t (aP E e₁ P) (aP E e₂ P) := by
    rw [← aP_add, he, aP_unit]
  rw [hsplit, aP_hom, hP₂ m' hm', E.L.mul_one, aP_mul E m m' (hΛ.mul_mem m.2 m'.2)]
  rw [kill_iff] at hP₁
  exact hP₁ _ (pcond_mul hΛ q' hm m'.2)

theorem swap_iff (hΛ : IsOrder Λ) (q q' : ℕ) (hqq' : Nat.Coprime q q') (P : SchemeHomOver t E.f) :
    (∀ m : ↥Λ, PCond q' (m : ℍ[ℚ, a, b]) → Kill E q (aP E m P)) ↔
      (∀ m' : ↥Λ, PCond q (m' : ℍ[ℚ, a, b]) → Kill E q' (aP E m' P)) :=
  ⟨swap E hΛ q q' hqq' P, swap E hΛ q' q hqq'.symm P⟩

end Kernel
p2m_reactivate "P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_WithExtraLevel_iso_of_isAtkinLehnerQuotient_comp_of_commRing.ALGlue"

section Composite

variable {E E₁ E₁₂ : FakeEllipticCurve Λ N S}

theorem comp_eq_one_iff (r r' : ℕ)
    (φ₁ : E.A ⟶ E₁.A) (hφ₁ : φ₁ ≫ E₁.f = E.f) (φ₁₂ : E₁.A ⟶ E₁₂.A) (hφ₁₂ : φ₁₂ ≫ E₁₂.f = E₁.f)
    (hlin₁ : ∀ x : ↥Λ, E.act x ≫ φ₁ = φ₁ ≫ E₁.act x)
    (hker₁ : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of S)) (P : SchemeHomOver t E.f),
      mapPt φ₁ hφ₁ P = E₁.L.one t ↔ Kill E r P)
    (hker₁₂ : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of S)) (Q : SchemeHomOver t E₁.f),
      mapPt φ₁₂ hφ₁₂ Q = E₁₂.L.one t ↔ Kill E₁ r' Q)
    {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of S)) (P : SchemeHomOver t E.f) :
    mapPt (φ₁ ≫ φ₁₂) (by rw [Category.assoc, hφ₁₂, hφ₁]) P = E₁₂.L.one t ↔
      ∀ m : ↥Λ, PCond r' (m : ℍ[ℚ, a, b]) → Kill E r (aP E m P) := by
  have hc : mapPt (φ₁ ≫ φ₁₂) (by rw [Category.assoc, hφ₁₂, hφ₁]) P = mapPt φ₁₂ hφ₁₂ (mapPt φ₁ hφ₁ P) :=
    Subtype.ext (by simp only [mapPt_coe, Category.assoc])
  rw [hc, hker₁₂, kill_iff]
  refine forall_congr' fun m => forall_congr' fun _ => ?_
  have hl : aP E₁ m (mapPt φ₁ hφ₁ P) = mapPt φ₁ hφ₁ (aP E m P) :=
    Subtype.ext (by simp only [mapPt_coe, Category.assoc, hlin₁ m])
  rw [hl, hker₁]

end Composite
p2m_reactivate "P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_WithExtraLevel_iso_of_isAtkinLehnerQuotient_comp_of_commRing.ALGlue"

end ALComm
p2m_reactivate "P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_WithExtraLevel_iso_of_isAtkinLehnerQuotient_comp_of_commRing.ALGlue"

namespace ALComm

section ActNat

variable {S : Type u} [CommRing S] {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} {N : ℕ}
  (E : FakeEllipticCurve Λ N S) {T : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of S)}

theorem aP_natCast (hΛ : IsOrder Λ) (n : ℕ) (P : SchemeHomOver t E.f) :
    aP E ⟨((n : ℚ) : ℍ[ℚ, a, b]), natCast_mem hΛ n⟩ P = nsmulPt E.L t n P := by
  induction n with
  | zero =>
    have h0 : (⟨(((0 : ℕ) : ℚ) : ℍ[ℚ, a, b]), natCast_mem hΛ 0⟩ : ↥Λ) = 0 := Subtype.ext (by push_cast; rfl)
    rw [h0, aP_zero]; rfl
  | succ n ih =>
    have hs : (⟨(((n + 1 : ℕ) : ℚ) : ℍ[ℚ, a, b]), natCast_mem hΛ (n + 1)⟩ : ↥Λ) =
        ⟨((n : ℚ) : ℍ[ℚ, a, b]), natCast_mem hΛ n⟩ + ⟨1, hΛ.one_mem⟩ := Subtype.ext (by push_cast; rfl)
    rw [hs, aP_add, ih, aP_unit]; rfl

theorem comp_dual_eq_nsmul (hΛ : IsOrder Λ) {E₁ E₁₂ : FakeEllipticCurve Λ N S} (r r' : ℕ)
    (φ₁ : E.A ⟶ E₁.A) (hφ₁ : φ₁ ≫ E₁.f = E.f) (ψ₁ : E₁.A ⟶ E.A) (hψ₁ : ψ₁ ≫ E.f = E₁.f)
    (φ₁₂ : E₁.A ⟶ E₁₂.A) (hφ₁₂ : φ₁₂ ≫ E₁₂.f = E₁.f) (ψ₁₂ : E₁₂.A ⟶ E₁.A) (hψ₁₂ : ψ₁₂ ≫ E₁.f = E₁₂.f)
    (hlin₁ : ∀ x : ↥Λ, E.act x ≫ φ₁ = φ₁ ≫ E₁.act x)
    (hc₁ : φ₁ ≫ ψ₁ = E.act ⟨((r : ℚ) : ℍ[ℚ, a, b]), natCast_mem hΛ r⟩)
    (hc₁₂ : φ₁₂ ≫ ψ₁₂ = E₁.act ⟨((r' : ℚ) : ℍ[ℚ, a, b]), natCast_mem hΛ r'⟩)
    (P : SchemeHomOver t E.f) :
    mapPt (ψ₁₂ ≫ ψ₁) (by rw [Category.assoc, hψ₁, hψ₁₂])
      (mapPt (φ₁ ≫ φ₁₂) (by rw [Category.assoc, hφ₁₂, hφ₁]) P) = nsmulPt E.L t (r * r') P := by
  have hrr : (⟨((((r * r' : ℕ) : ℚ)) : ℍ[ℚ, a, b]), natCast_mem hΛ (r * r')⟩ : ↥Λ) =
      ⟨((r : ℚ) : ℍ[ℚ, a, b]) * ((r' : ℚ) : ℍ[ℚ, a, b]), hΛ.mul_mem (natCast_mem hΛ r) (natCast_mem hΛ r')⟩ :=
    Subtype.ext (by simp only [Nat.cast_mul, coe_mul])
  rw [← aP_natCast E hΛ, hrr]
  apply Subtype.ext
  simp only [mapPt_coe, Category.assoc]
  rw [← Category.assoc φ₁₂ ψ₁₂ ψ₁, hc₁₂, ← Category.assoc φ₁, ← hlin₁, Category.assoc, hc₁,
    E.act_mul ⟨((r : ℚ) : ℍ[ℚ, a, b]), natCast_mem hΛ r⟩ ⟨((r' : ℚ) : ℍ[ℚ, a, b]), natCast_mem hΛ r'⟩]

end ActNat
p2m_reactivate "P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_WithExtraLevel_iso_of_isAtkinLehnerQuotient_comp_of_commRing.ALGlue"

end ALComm
p2m_reactivate "P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_WithExtraLevel_iso_of_isAtkinLehnerQuotient_comp_of_commRing.ALGlue"

namespace ALTSq
open ALComm

variable {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]}

theorem pcond_iff_nrd (r : ℕ) (m : ℍ[ℚ, a, b]) :
    PCond r m ↔ ∃ n : ℤ, nrd m = (r : ℚ) * n := by
  unfold PCond
  rw [mul_star_eq_coe_nrd]
  constructor
  · rintro ⟨n, hn⟩
    refine ⟨n, ?_⟩
    have h := QuaternionAlgebra.coe_injective hn
    exact_mod_cast h
  · rintro ⟨n, hn⟩
    refine ⟨n, ?_⟩
    rw [hn]
    norm_cast

end ALTSq
p2m_reactivate "P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_WithExtraLevel_iso_of_isAtkinLehnerQuotient_comp_of_commRing.ALGlue"

namespace LevelOnto

variable {S : Type u} [CommRing S]

section Pow

variable {A : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of S)} (L : RelativeGroupLaw S f)
  {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of S))

theorem nsmulPt_eq_pow (n : ℕ) (P : SchemeHomOver t f) :
    letI := L.pointGroup t
    nsmulPt L t n P = P ^ n := by
  letI := L.pointGroup t
  induction n with
  | zero => rfl
  | succ n ih =>
    show L.mul t (nsmulPt L t n P) P = P ^ (n + 1)
    rw [ih, pow_succ]; rfl

theorem nsmulPt_one' (n : ℕ) : nsmulPt L t n (L.one t) = L.one t := by
  letI := L.pointGroup t
  rw [nsmulPt_eq_pow]; exact one_pow n

end Pow
p2m_reactivate "P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_WithExtraLevel_iso_of_isAtkinLehnerQuotient_comp_of_commRing.ALGlue"

end LevelOnto
p2m_reactivate "P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_WithExtraLevel_iso_of_isAtkinLehnerQuotient_comp_of_commRing.ALGlue"

open LevelOnto in
theorem LevelOnto.levK_onto
    {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} {N ℓ : ℕ} {S : Type u} [CommRing S]
    (E E' : WithExtraLevel Λ N ℓ S)
    (φ : E.1.A ⟶ E'.1.A) (hφ : φ ≫ E'.1.f = E.1.f)
    (hφmul : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of S)) (P Q : SchemeHomOver t E.1.f),
      mapPt φ hφ (E.1.L.mul t P Q) = E'.1.L.mul t (mapPt φ hφ P) (mapPt φ hφ Q))
    (ψ : E'.1.A ⟶ E.1.A) (hψ : ψ ≫ E.1.f = E'.1.f) (n : ℕ) (hn : Nat.Coprime n ℓ)
    (hψφ : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of S)) (P : SchemeHomOver t E.1.f),
      mapPt ψ hψ (mapPt φ hφ P) = nsmulPt E.1.L t n P)
    (hlev : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of S)) (P : SchemeHomOver t E.1.f),
      FactorsThrough E.2.levK P → FactorsThrough E'.2.levK (mapPt φ hφ P)) :
    ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of S)) (Q : SchemeHomOver t E'.1.f),
      FactorsThrough E'.2.levK Q ↔ ∃ P : SchemeHomOver t E.1.f, FactorsThrough E.2.levK P ∧ mapPt φ hφ P = Q := by
  classical

  let P₀ : SchemeHomOver (E.2.levK ≫ E.1.f) E.1.f := ⟨E.2.levK, rfl⟩
  have hP₀ : FactorsThrough E.2.levK P₀ := ⟨𝟙 _, Category.id_comp _⟩
  obtain ⟨c, hc⟩ := hlev _ P₀ hP₀

  have hc' : c ≫ E'.2.levK = E.2.levK ≫ φ := by rw [hc]; rfl

  have hφone : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of S)), mapPt φ hφ (E.1.L.one t) = E'.1.L.one t := by
    intro T t
    set x := mapPt φ hφ (E.1.L.one t) with hx
    have hxx : E'.1.L.mul t x x = x := by rw [hx, ← hφmul, E.1.L.one_mul]
    letI := E'.1.L.pointGroup t
    have h2 : x * x = x * 1 := by rw [mul_one]; exact hxx
    exact mul_left_cancel h2

  have hinj : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of S)) (P P' : SchemeHomOver t E.1.f),
      FactorsThrough E.2.levK P → FactorsThrough E.2.levK P' → mapPt φ hφ P = mapPt φ hφ P' → P = P' := by
    intro T t P P' hP hP' h
    letI := E.1.L.pointGroup t
    letI := E'.1.L.pointGroup t

    have hD : FactorsThrough E.2.levK (E.1.L.mul t P (E.1.L.inv t P')) :=
      (E.2.levK_sub t P (E.1.L.inv t P') hP (E.2.levK_sub t P' P' hP' hP').2).1
    have hφhom : ∀ X Y : SchemeHomOver t E.1.f, mapPt φ hφ (X * Y) = mapPt φ hφ X * mapPt φ hφ Y := fun X Y => hφmul t X Y
    let Φ : SchemeHomOver t E.1.f →* SchemeHomOver t E'.1.f :=
      { toFun := mapPt φ hφ, map_one' := hφone t, map_mul' := hφhom }
    have hΦD : Φ (P * P'⁻¹) = 1 := by
      rw [map_mul, map_inv, show Φ P = Φ P' from h, mul_inv_cancel]

    have hnD : (P * P'⁻¹) ^ n = 1 := by
      rw [← nsmulPt_eq_pow, ← hψφ t]
      show mapPt ψ hψ (Φ (P * P'⁻¹)) = 1
      rw [hΦD]
      show mapPt ψ hψ (E'.1.L.one t) = E.1.L.one t
      rw [← hφone t, hψφ, nsmulPt_one']

    have hND : (P * P'⁻¹) ^ ℓ = 1 := by
      rw [← nsmulPt_eq_pow]; exact E.2.levK_torsion t _ hD
    have h1 : (P * P'⁻¹) ^ Nat.gcd n ℓ = 1 := (pow_gcd_eq_one).2 ⟨hnD, hND⟩
    rw [hn, pow_one] at h1
    exact mul_inv_eq_one.1 h1
  have hcomp' : c ≫ E'.2.levK ≫ E'.1.f = E.2.levK ≫ E.1.f := by rw [← Category.assoc, hc', Category.assoc, hφ]

  haveI : IsClosedImmersion E.2.levK := E.2.levK_closed
  haveI : IsClosedImmersion E'.2.levK := E'.2.levK_closed
  have hmono : Mono c := by
    refine ⟨fun {Z} u v huv => ?_⟩
    have hmE : Mono E.2.levK := ((IsClosedImmersion.iff_isFinite_and_mono E.2.levK).1 inferInstance).2
    rw [← cancel_mono E.2.levK]
    have ht : (v ≫ E.2.levK) ≫ E.1.f = (u ≫ E.2.levK) ≫ E.1.f := by
      have h1 : ∀ w : Z ⟶ E.2.K, (w ≫ E.2.levK) ≫ E.1.f = (w ≫ c) ≫ E'.2.levK ≫ E'.1.f := fun w => by
        simp only [Category.assoc, hcomp']
      rw [h1, h1, huv]
    have key := hinj ((u ≫ E.2.levK) ≫ E.1.f) ⟨u ≫ E.2.levK, rfl⟩ ⟨v ≫ E.2.levK, ht⟩ ⟨u, rfl⟩ ⟨v, rfl⟩
      (Subtype.ext (by
        simp only [mapPt_coe, Category.assoc]
        rw [← hc', ← Category.assoc, huv, Category.assoc]))
    exact congrArg Subtype.val key

  have hcomp : c ≫ (E'.2.levK ≫ E'.1.f) = E.2.levK ≫ E.1.f := hcomp'
  haveI : IsFinite (E'.2.levK ≫ E'.1.f) := E'.2.levK_finite
  haveI : IsFinite (E.2.levK ≫ E.1.f) := E.2.levK_finite
  haveI : IsFinite (c ≫ (E'.2.levK ≫ E'.1.f)) := by rw [hcomp]; infer_instance
  haveI : IsFinite c := IsFinite.of_comp c (E'.2.levK ≫ E'.1.f)
  haveI : IsClosedImmersion c := (IsClosedImmersion.iff_isFinite_and_mono c).2 ⟨inferInstance, hmono⟩

  haveI : Flat (E'.2.levK ≫ E'.1.f) := E'.2.levK_flat
  haveI : LocallyOfFinitePresentation (E'.2.levK ≫ E'.1.f) := E'.2.levK_finitePresentation
  haveI : Flat (E.2.levK ≫ E.1.f) := E.2.levK_flat
  haveI : LocallyOfFinitePresentation (E.2.levK ≫ E.1.f) := E.2.levK_finitePresentation
  haveI : IsIso c := AlgebraicGeometry.isIso_of_isClosedImmersion_of_finrank_comp_eq c (E'.2.levK ≫ E'.1.f) (E.2.levK ≫ E.1.f) hcomp
    (fun s => by rw [E.2.levK_rank s, E'.2.levK_rank s])

  intro T t Q
  constructor
  · rintro ⟨Q₀, hQ₀⟩
    refine ⟨⟨Q₀ ≫ inv c ≫ E.2.levK, ?_⟩, ⟨Q₀ ≫ inv c, by simp only [Category.assoc]⟩, ?_⟩
    · simp only [Category.assoc]
      rw [← hcomp', IsIso.inv_hom_id_assoc, ← Category.assoc, hQ₀]
      exact Q.2
    · apply Subtype.ext
      simp only [mapPt_coe, Category.assoc]
      rw [← hc', IsIso.inv_hom_id_assoc, hQ₀]
  · rintro ⟨P, hP, rfl⟩
    exact hlev t P hP

namespace ALQIsoKernelT
p2m_open "CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra~schemeHomOverComp~schemeHomOverComp_coe GoodReductionJacobian"
open CerednikDrinfeld CerednikDrinfeld.QM CerednikDrinfeld.QM.FakeEllipticCurve QuaternionAlgebra ALGlue
open scoped Quaternion

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

theorem mapPt_comp {E E' : FakeEllipticCurve Λ N S} (φ : E.A ⟶ E'.A) (hφ : φ ≫ E'.f = E.f)
    {T T' : Scheme.{0}} {t : T ⟶ Spec (CommRingCat.of S)} {t' : T' ⟶ Spec (CommRingCat.of S)} (ψ : T' ⟶ T) (hψ : ψ ≫ t = t')
    (P : SchemeHomOver t E.f) :
    mapPt φ hφ (schemeHomOverComp ψ hψ P) = schemeHomOverComp ψ hψ (mapPt φ hφ P) :=
  Subtype.ext (by simp only [mapPt_coe, schemeHomOverComp_coe, Category.assoc])

theorem iso_of_same_kernel {ℓ : ℕ}
    (E E' E'' : WithExtraLevel Λ N ℓ S)
    (φ' : E.1.A ⟶ E'.1.A) (hφ' : φ' ≫ E'.1.f = E.1.f)
    (mφ' : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of S)) (P Q : SchemeHomOver t E.1.f), mapPt φ' hφ' (E.1.L.mul t P Q) = E'.1.L.mul t (mapPt φ' hφ' P) (mapPt φ' hφ' Q))
    (aφ' : ∀ x : ↥Λ, E.1.act x ≫ φ' = φ' ≫ E'.1.act x)
    (ψ' : E'.1.A ⟶ E.1.A) (hψ' : ψ' ≫ E.1.f = E'.1.f) (n' : ℕ) (hn' : 0 < n') (hcop' : Nat.Coprime n' N)
    (hψφ' : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of S)) (P : SchemeHomOver t E.1.f), mapPt ψ' hψ' (mapPt φ' hφ' P) = nsmulPt E.1.L t n' P)
    (hφψ' : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of S)) (P : SchemeHomOver t E'.1.f), mapPt φ' hφ' (mapPt ψ' hψ' P) = nsmulPt E'.1.L t n' P)
    (l' : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of S)) (P : SchemeHomOver t E.1.f), FactorsThrough E.1.lev P → FactorsThrough E'.1.lev (mapPt φ' hφ' P))
    (lK' : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of S)) (P : SchemeHomOver t E.1.f), FactorsThrough E.2.levK P → FactorsThrough E'.2.levK (mapPt φ' hφ' P)) (hcopK' : Nat.Coprime n' ℓ)
    (φ'' : E.1.A ⟶ E''.1.A) (hφ'' : φ'' ≫ E''.1.f = E.1.f)
    (mφ'' : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of S)) (P Q : SchemeHomOver t E.1.f), mapPt φ'' hφ'' (E.1.L.mul t P Q) = E''.1.L.mul t (mapPt φ'' hφ'' P) (mapPt φ'' hφ'' Q))
    (aφ'' : ∀ x : ↥Λ, E.1.act x ≫ φ'' = φ'' ≫ E''.1.act x)
    (ψ'' : E''.1.A ⟶ E.1.A) (hψ'' : ψ'' ≫ E.1.f = E''.1.f) (n'' : ℕ) (hn'' : 0 < n'') (hcop'' : Nat.Coprime n'' N)
    (hψφ'' : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of S)) (P : SchemeHomOver t E.1.f), mapPt ψ'' hψ'' (mapPt φ'' hφ'' P) = nsmulPt E.1.L t n'' P)
    (hφψ'' : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of S)) (P : SchemeHomOver t E''.1.f), mapPt φ'' hφ'' (mapPt ψ'' hψ'' P) = nsmulPt E''.1.L t n'' P)
    (l'' : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of S)) (P : SchemeHomOver t E.1.f), FactorsThrough E.1.lev P → FactorsThrough E''.1.lev (mapPt φ'' hφ'' P))
    (lK'' : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of S)) (P : SchemeHomOver t E.1.f), FactorsThrough E.2.levK P → FactorsThrough E''.2.levK (mapPt φ'' hφ'' P)) (hcopK'' : Nat.Coprime n'' ℓ)
    (k12 : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of S)) (P : SchemeHomOver t E.1.f), mapPt φ' hφ' P = E'.1.L.one t → mapPt φ'' hφ'' P = E''.1.L.one t)
    (k21 : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of S)) (P : SchemeHomOver t E.1.f), mapPt φ'' hφ'' P = E''.1.L.one t → mapPt φ' hφ' P = E'.1.L.one t) :
    WithExtraLevel.Iso E' E'' := by
  classical

  obtain ⟨hfin', hfl', -, hsur'⟩ := CerednikDrinfeld.QM.FakeEllipticCurve.isFinite_flat_surjective_of_mapPt_mapPt_eq_nsmulPt
    E.1 E'.1 φ' hφ' mφ' ψ' hψ' n' hn' hψφ' hφψ'
  obtain ⟨hfin'', hfl'', -, hsur''⟩ := CerednikDrinfeld.QM.FakeEllipticCurve.isFinite_flat_surjective_of_mapPt_mapPt_eq_nsmulPt
    E.1 E''.1 φ'' hφ'' mφ'' ψ'' hψ'' n'' hn'' hψφ'' hφψ''
  haveI := hfin'; haveI := hfl'; haveI := hsur'; haveI := hfin''; haveI := hfl''; haveI := hsur''
  haveI : EffectiveEpi φ' := inferInstance
  haveI : EffectiveEpi φ'' := inferInstance

  have coeq : ∀ (A B C : FakeEllipticCurve Λ N S) (α : A.A ⟶ B.A) (hα : α ≫ B.f = A.f) (β : A.A ⟶ C.A) (hβ : β ≫ C.f = A.f)
      (mα : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of S)) (P Q : SchemeHomOver t A.f),
        mapPt α hα (A.L.mul t P Q) = B.L.mul t (mapPt α hα P) (mapPt α hα Q))
      (mβ : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of S)) (P Q : SchemeHomOver t A.f),
        mapPt β hβ (A.L.mul t P Q) = C.L.mul t (mapPt β hβ P) (mapPt β hβ Q))
      (hker : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of S)) (P : SchemeHomOver t A.f),
        mapPt α hα P = B.L.one t → mapPt β hβ P = C.L.one t)
      {Z : Scheme.{0}} (g₁ g₂ : Z ⟶ A.A), g₁ ≫ α = g₂ ≫ α → g₁ ≫ β = g₂ ≫ β := by
    intro A B C α hα β hβ mα mβ hker Z g₁ g₂ hg
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

  let χ : E'.1.A ⟶ E''.1.A := EffectiveEpi.desc φ' φ'' (coeq E.1 E'.1 E''.1 φ' hφ' φ'' hφ'' mφ' mφ'' k12)
  have hφχ : φ' ≫ χ = φ'' := EffectiveEpi.fac φ' φ'' _
  let χ' : E''.1.A ⟶ E'.1.A := EffectiveEpi.desc φ'' φ' (coeq E.1 E''.1 E'.1 φ'' hφ'' φ' hφ' mφ'' mφ' k21)
  have hφχ' : φ'' ≫ χ' = φ' := EffectiveEpi.fac φ'' φ' _
  have hχχ' : χ ≫ χ' = 𝟙 _ := by
    rw [← cancel_epi φ', ← Category.assoc, hφχ, hφχ', Category.comp_id]
  have hχ'χ : χ' ≫ χ = 𝟙 _ := by
    rw [← cancel_epi φ'', ← Category.assoc, hφχ', hφχ, Category.comp_id]
  have hχ : χ ≫ E''.1.f = E'.1.f := by
    rw [← cancel_epi φ', ← Category.assoc, hφχ, hφ'', hφ']
  let e : E'.1.A ≅ E''.1.A := ⟨χ, χ', hχχ', hχ'χ⟩

  have tχ : ∀ {T : Scheme.{0}} {t : T ⟶ Spec (CommRingCat.of S)} (P : SchemeHomOver t E.1.f),
      mapPt χ hχ (mapPt φ' hφ' P) = mapPt φ'' hφ'' P :=
    fun P => Subtype.ext (by simp only [mapPt_coe, Category.assoc, hφχ])
  refine ⟨e, hχ, ?_, ?_, ?_, ?_⟩
  ·
    intro T t P Q
    show mapPt χ hχ (E'.1.L.mul t P Q) = E''.1.L.mul t (mapPt χ hχ P) (mapPt χ hχ Q)

    let T₁ := pullback P.1 φ'
    let π₁ : T₁ ⟶ T := pullback.fst P.1 φ'
    haveI : Flat π₁ := inferInstance
    haveI : Surjective π₁ := inferInstance

    let T₂ := pullback (π₁ ≫ Q.1) φ'
    let π₂ : T₂ ⟶ T₁ := pullback.fst (π₁ ≫ Q.1) φ'
    haveI : Flat π₂ := inferInstance
    haveI : Surjective π₂ := inferInstance
    let ψ : T₂ ⟶ T := π₂ ≫ π₁
    haveI : Epi π₁ := Flat.epi_of_flat_of_surjective π₁
    haveI : Epi π₂ := Flat.epi_of_flat_of_surjective π₂
    haveI : Epi ψ := epi_comp π₂ π₁
    have hψt : ψ ≫ t = ψ ≫ t := rfl

    let Pl : SchemeHomOver (ψ ≫ t) E.1.f := ⟨π₂ ≫ pullback.snd P.1 φ', by
      show (π₂ ≫ pullback.snd P.1 φ') ≫ E.1.f = (π₂ ≫ π₁) ≫ t
      rw [← hφ']; simp only [Category.assoc]
      rw [← pullback.condition_assoc, P.2]⟩
    let Ql : SchemeHomOver (ψ ≫ t) E.1.f := ⟨pullback.snd (π₁ ≫ Q.1) φ', by
      show pullback.snd (π₁ ≫ Q.1) φ' ≫ E.1.f = (π₂ ≫ π₁) ≫ t
      rw [← hφ', ← pullback.condition_assoc]; simp only [Category.assoc]; rw [Q.2]⟩
    have hPl : mapPt φ' hφ' Pl = schemeHomOverComp ψ hψt P := by
      apply Subtype.ext
      show (π₂ ≫ pullback.snd P.1 φ') ≫ φ' = (π₂ ≫ π₁) ≫ P.1
      simp only [Category.assoc]
      rw [pullback.condition]
    have hQl : mapPt φ' hφ' Ql = schemeHomOverComp ψ hψt Q := by
      apply Subtype.ext
      show pullback.snd (π₁ ≫ Q.1) φ' ≫ φ' = (π₂ ≫ π₁) ≫ Q.1
      rw [Category.assoc, ← pullback.condition]

    have key : schemeHomOverComp ψ hψt (mapPt χ hχ (E'.1.L.mul t P Q)) =
        schemeHomOverComp ψ hψt (E''.1.L.mul t (mapPt χ hχ P) (mapPt χ hχ Q)) := by
      rw [← mapPt_comp, E'.1.L.mul_natural t (ψ ≫ t) ψ hψt, ← hPl, ← hQl, ← mφ', tχ, mφ'', ← tχ, ← tχ, hPl, hQl,
        mapPt_comp, mapPt_comp, ← E''.1.L.mul_natural t (ψ ≫ t) ψ hψt]
    apply Subtype.ext
    rw [← cancel_epi ψ]
    exact congrArg Subtype.val key
  ·
    intro x
    rw [← cancel_epi φ']
    show φ' ≫ E'.1.act x ≫ χ = φ' ≫ χ ≫ E''.1.act x
    rw [← Category.assoc, ← aφ' x, Category.assoc, hφχ, aφ'' x, ← Category.assoc φ' χ, hφχ]
  ·
    intro T t R
    show FactorsThrough E'.1.lev R ↔ FactorsThrough E''.1.lev (mapPt χ hχ R)
    have LO' := CerednikDrinfeld.QM.FakeEllipticCurve.factorsThrough_lev_iff_exists_mapPt_eq_of_coprime
      E.1 E'.1 φ' hφ' mφ' ψ' hψ' n' hcop' hψφ' l' t R
    have LO'' := fun (R'' : SchemeHomOver t E''.1.f) =>
      CerednikDrinfeld.QM.FakeEllipticCurve.factorsThrough_lev_iff_exists_mapPt_eq_of_coprime
        E.1 E''.1 φ'' hφ'' mφ'' ψ'' hψ'' n'' hcop'' hψφ'' l'' t R''
    have χinj : ∀ (X Y : SchemeHomOver t E'.1.f), mapPt χ hχ X = mapPt χ hχ Y → X = Y := by
      intro X Y hXY
      apply Subtype.ext
      haveI : IsIso χ := ⟨⟨χ', hχχ', hχ'χ⟩⟩
      rw [← cancel_mono χ]
      exact congrArg Subtype.val hXY
    constructor
    · intro hR
      obtain ⟨P, hP, rfl⟩ := LO'.1 hR
      show FactorsThrough E''.1.lev (mapPt χ hχ (mapPt φ' hφ' P))
      rw [tχ]; exact l'' t P hP
    · intro hR
      obtain ⟨P, hP, hPe⟩ := (LO'' (mapPt χ hχ R)).1 hR
      have : mapPt φ' hφ' P = R := χinj _ _ (by rw [tχ, hPe])
      rw [← this]; exact l' t P hP

  ·
    intro T t R
    show FactorsThrough E'.2.levK R ↔ FactorsThrough E''.2.levK (mapPt χ hχ R)
    have LO' := LevelOnto.levK_onto E E' φ' hφ' mφ' ψ' hψ' n' hcopK' hψφ' lK' t R
    have LO'' := fun (R'' : SchemeHomOver t E''.1.f) => LevelOnto.levK_onto E E'' φ'' hφ'' mφ'' ψ'' hψ'' n'' hcopK'' hψφ'' lK'' t R''
    have χinj : ∀ (X Y : SchemeHomOver t E'.1.f), mapPt χ hχ X = mapPt χ hχ Y → X = Y := by
      intro X Y hXY
      apply Subtype.ext
      haveI : IsIso χ := ⟨⟨χ', hχχ', hχ'χ⟩⟩
      rw [← cancel_mono χ]
      exact congrArg Subtype.val hXY
    constructor
    · intro hR
      obtain ⟨P, hP, rfl⟩ := LO'.1 hR
      show FactorsThrough E''.2.levK (mapPt χ hχ (mapPt φ' hφ' P))
      rw [tχ]; exact lK'' t P hP
    · intro hR
      obtain ⟨P, hP, hPe⟩ := (LO'' (mapPt χ hχ R)).1 hR
      have : mapPt φ' hφ' P = R := χinj _ _ (by rw [tχ, hPe])
      rw [← this]; exact lK' t P hP

end ALQIsoKernelT
p2m_reactivate "P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_WithExtraLevel_iso_of_isAtkinLehnerQuotient_comp_of_commRing.ALGlue"

open ALQIsoKernelT ALComm ALTSq CerednikDrinfeld CerednikDrinfeld.QM CerednikDrinfeld.QM.FakeEllipticCurve QuaternionAlgebra CategoryTheory in
theorem solution
    {q q' : ℕ} [Fact q.Prime] [Fact q'.Prime] (hqq' : q' ≠ q)
    {a b : ℚ} (hB : IsIndefiniteRamifiedExactlyAt a b q q')
    (Λ : Submodule ℤ ℍ[ℚ, a, b]) (hΛ : IsMaximalOrder Λ) {N : ℕ} [NeZero N] (hqN : ¬ q ∣ N) (hq'N : ¬ q' ∣ N)
    (r : ℕ) (hr : r = q ∨ r = q') (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓq : ℓ ≠ q) (hℓq' : ℓ ≠ q')
    (S : Type) [CommRing S] (u u' u'' : QM.FakeEllipticCurve.WithExtraLevel Λ N ℓ S)
    (h : QM.FakeEllipticCurve.WithExtraLevel.IsAtkinLehnerQuotient r u u')
    (h' : QM.FakeEllipticCurve.WithExtraLevel.IsAtkinLehnerQuotient r u' u'') :
    QM.FakeEllipticCurve.WithExtraLevel.Iso u u'' := by
  classical
  rename_i inst
  have hO : IsOrder Λ := hΛ.isOrder
  have hrp : r.Prime := by rcases hr with rfl | rfl <;> exact Fact.out
  have hrN : ¬ r ∣ N := by rcases hr with rfl | rfl <;> assumption
  have hcopN : Nat.Coprime r N := (Nat.Prime.coprime_iff_not_dvd hrp).2 hrN
  have hcopN2 : Nat.Coprime (r * r) N := Nat.Coprime.mul_left hcopN hcopN
  have hrℓ : r ≠ ℓ := by
    rcases hr with rfl | rfl
    · exact fun e => hℓq e.symm
    · exact fun e => hℓq' e.symm
  have hcopℓ : Nat.Coprime r ℓ := (Nat.coprime_primes hrp hℓ).2 hrℓ
  have hcopℓ2 : Nat.Coprime (r * r) ℓ := Nat.Coprime.mul_left hcopℓ hcopℓ
  have hrΛ : ((r : ℚ) : ℍ[ℚ, a, b]) ∈ Λ := natCast_mem hO r
  obtain ⟨φ₁, hφ₁, ψ₁, hψ₁, m₁, mψ₁, l₁, lψ₁, c₁, k₁, v₁, w₁⟩ := h
  obtain ⟨φ₂, hφ₂, ψ₂, hψ₂, m₂, mψ₂, l₂, lψ₂, c₂, k₂, v₂, w₂⟩ := h'
  obtain ⟨RAM1, RAM2⟩ := QuaternionAlgebra.IsMaximalOrder.span_mul_ramifiedPrime_eq_of_isIndefiniteRamifiedExactlyAt hB Λ hΛ r hr

  have hΦ : (φ₁ ≫ φ₂) ≫ u''.1.f = u.1.f := by rw [Category.assoc, hφ₂, hφ₁]
  have hΨ : (ψ₂ ≫ ψ₁) ≫ u.1.f = u''.1.f := by rw [Category.assoc, hψ₁, hψ₂]
  have mc : ∀ {A B C : Scheme.{0}} {fA : A ⟶ Spec (CommRingCat.of S)} {fB : B ⟶ Spec (CommRingCat.of S)}
      {fC : C ⟶ Spec (CommRingCat.of S)} (θ : A ⟶ B) (hθ : θ ≫ fB = fA) (θ' : B ⟶ C) (hθ' : θ' ≫ fC = fB)
      (hθθ' : (θ ≫ θ') ≫ fC = fA) {T : Scheme.{0}} {t : T ⟶ Spec (CommRingCat.of S)} (P : SchemeHomOver t fA),
      mapPt (θ ≫ θ') hθθ' P = mapPt θ' hθ' (mapPt θ hθ P) := by
    intro A B C fA fB fC θ hθ θ' hθ' hθθ' T t P
    exact Subtype.ext (by simp only [mapPt_coe, Category.assoc])
  have MΦ : ∀ {T : Scheme} (t : T ⟶ Spec (CommRingCat.of S)) (P Q : SchemeHomOver t u.1.f),
      mapPt (φ₁ ≫ φ₂) hΦ (u.1.L.mul t P Q) = u''.1.L.mul t (mapPt (φ₁ ≫ φ₂) hΦ P) (mapPt (φ₁ ≫ φ₂) hΦ Q) := by
    intro T t P Q; rw [mc φ₁ hφ₁ φ₂ hφ₂, mc φ₁ hφ₁ φ₂ hφ₂, mc φ₁ hφ₁ φ₂ hφ₂, m₁, m₂]
  have LΦ : ∀ x : ↥Λ, u.1.act x ≫ (φ₁ ≫ φ₂) = (φ₁ ≫ φ₂) ≫ u''.1.act x := by
    intro x; rw [← Category.assoc, l₁, Category.assoc, l₂, Category.assoc]
  have DΦ : ∀ {T : Scheme} (t : T ⟶ Spec (CommRingCat.of S)) (P : SchemeHomOver t u.1.f),
      mapPt (ψ₂ ≫ ψ₁) hΨ (mapPt (φ₁ ≫ φ₂) hΦ P) = nsmulPt u.1.L t (r * r) P :=
    fun t P => comp_dual_eq_nsmul u.1 hO r r φ₁ hφ₁ ψ₁ hψ₁ φ₂ hφ₂ ψ₂ hψ₂ l₁ (c₁ hrΛ).1 (c₂ hrΛ).1 P
  have DΦ' : ∀ {T : Scheme} (t : T ⟶ Spec (CommRingCat.of S)) (Q : SchemeHomOver t u''.1.f),
      mapPt (φ₁ ≫ φ₂) hΦ (mapPt (ψ₂ ≫ ψ₁) hΨ Q) = nsmulPt u''.1.L t (r * r) Q :=
    fun t Q => comp_dual_eq_nsmul u''.1 hO r r ψ₂ hψ₂ φ₂ hφ₂ ψ₁ hψ₁ φ₁ hφ₁ lψ₂ (c₂ hrΛ).2 (c₁ hrΛ).2 Q
  have VΦ : ∀ {T : Scheme} (t : T ⟶ Spec (CommRingCat.of S)) (P : SchemeHomOver t u.1.f), FactorsThrough u.1.lev P → FactorsThrough u''.1.lev (mapPt (φ₁ ≫ φ₂) hΦ P) := by
    intro T t P hP; rw [mc φ₁ hφ₁ φ₂ hφ₂]; exact v₂ t _ (v₁ t P hP)
  have WΦ : ∀ {T : Scheme} (t : T ⟶ Spec (CommRingCat.of S)) (P : SchemeHomOver t u.1.f), FactorsThrough u.2.levK P → FactorsThrough u''.2.levK (mapPt (φ₁ ≫ φ₂) hΦ P) := by
    intro T t P hP; rw [mc φ₁ hφ₁ φ₂ hφ₂]; exact w₂ t _ (w₁ t P hP)

  let ρ : u.1.A ⟶ u.1.A := u.1.act ⟨((r : ℚ) : ℍ[ℚ, a, b]), hrΛ⟩
  have hρ : ρ ≫ u.1.f = u.1.f := u.1.act_over _
  have hid : (𝟙 u.1.A) ≫ u.1.f = u.1.f := Category.id_comp _
  have ρpt : ∀ {T : Scheme} (t : T ⟶ Spec (CommRingCat.of S)) (P : SchemeHomOver t u.1.f), mapPt ρ hρ P = aP u.1 ⟨((r : ℚ) : ℍ[ℚ, a, b]), hrΛ⟩ P := fun t P => rfl
  have idpt : ∀ {T : Scheme} (t : T ⟶ Spec (CommRingCat.of S)) (P : SchemeHomOver t u.1.f), mapPt (𝟙 u.1.A) hid P = P :=
    fun t P => Subtype.ext (by simp only [mapPt_coe, Category.comp_id])
  have Mρ : ∀ {T : Scheme} (t : T ⟶ Spec (CommRingCat.of S)) (P Q : SchemeHomOver t u.1.f), mapPt ρ hρ (u.1.L.mul t P Q) = u.1.L.mul t (mapPt ρ hρ P) (mapPt ρ hρ Q) :=
    fun t P Q => aP_hom u.1 _ P Q
  have Lρ : ∀ x : ↥Λ, u.1.act x ≫ ρ = ρ ≫ u.1.act x := by
    intro x
    show u.1.act x ≫ u.1.act ⟨_, hrΛ⟩ = u.1.act ⟨_, hrΛ⟩ ≫ u.1.act x
    rw [← u.1.act_mul ⟨_, hrΛ⟩ x (hO.mul_mem hrΛ x.2), ← u.1.act_mul x ⟨_, hrΛ⟩ (hO.mul_mem x.2 hrΛ)]
    congr 1; apply Subtype.ext
    show ((r : ℚ) : ℍ[ℚ, a, b]) * (x : ℍ[ℚ, a, b]) = (x : ℍ[ℚ, a, b]) * ((r : ℚ) : ℍ[ℚ, a, b])
    rw [coe_commutes]
  have Dρ : ∀ {T : Scheme} (t : T ⟶ Spec (CommRingCat.of S)) (P : SchemeHomOver t u.1.f), mapPt (𝟙 u.1.A) hid (mapPt ρ hρ P) = nsmulPt u.1.L t r P := by
    intro T t P; rw [idpt, ρpt, aP_natCast u.1 hO]
  have Dρ' : ∀ {T : Scheme} (t : T ⟶ Spec (CommRingCat.of S)) (P : SchemeHomOver t u.1.f), mapPt ρ hρ (mapPt (𝟙 u.1.A) hid P) = nsmulPt u.1.L t r P := by
    intro T t P; rw [idpt, ρpt, aP_natCast u.1 hO]
  have Vρ : ∀ {T : Scheme} (t : T ⟶ Spec (CommRingCat.of S)) (P : SchemeHomOver t u.1.f), FactorsThrough u.1.lev P → FactorsThrough u.1.lev (mapPt ρ hρ P) :=
    fun t P hP => u.1.lev_stable _ t P hP
  have Wρ : ∀ {T : Scheme} (t : T ⟶ Spec (CommRingCat.of S)) (P : SchemeHomOver t u.1.f), FactorsThrough u.2.levK P → FactorsThrough u.2.levK (mapPt ρ hρ P) :=
    fun t P hP => u.2.levK_stable _ t P hP

  have K : ∀ {T : Scheme} (t : T ⟶ Spec (CommRingCat.of S)) (P : SchemeHomOver t u.1.f),
      mapPt ρ hρ P = u.1.L.one t ↔ mapPt (φ₁ ≫ φ₂) hΦ P = u''.1.L.one t := by
    intro T t P
    rw [comp_eq_one_iff r r φ₁ hφ₁ φ₂ hφ₂ l₁ k₁ k₂ t P, ρpt]
    constructor
    · intro hP m hm
      rw [kill_iff]
      intro m' hm'
      rw [aP_mul u.1 m' m (hO.mul_mem m'.2 m.2)]
      obtain ⟨y, hy, hxy⟩ := RAM1 (m' : ℍ[ℚ, a, b]) m'.2 (m : ℍ[ℚ, a, b]) m.2
        ((pcond_iff_nrd r _).1 hm') ((pcond_iff_nrd r _).1 hm)
      have heq : (⟨(m' : ℍ[ℚ, a, b]) * (m : ℍ[ℚ, a, b]), hO.mul_mem m'.2 m.2⟩ : ↥Λ) =
          ⟨(y : ℍ[ℚ, a, b]) * ((r : ℚ) : ℍ[ℚ, a, b]), hO.mul_mem hy hrΛ⟩ := by
        apply Subtype.ext
        show (m' : ℍ[ℚ, a, b]) * (m : ℍ[ℚ, a, b]) = y * ((r : ℚ) : ℍ[ℚ, a, b])
        rw [hxy, zsmul_eq_mul, ← coe_commutes]; push_cast; ring_nf
      rw [heq, ← aP_mul u.1 ⟨y, hy⟩ ⟨_, hrΛ⟩, hP, aP_one]
    · intro hP
      have gen : ∀ z ∈ Submodule.span ℤ {z : ℍ[ℚ, a, b] | ∃ x ∈ Λ, ∃ x' ∈ Λ,
            (∃ n : ℤ, nrd x = (r : ℚ) * n) ∧ (∃ n : ℤ, nrd x' = (r : ℚ) * n) ∧ z = x * x'},
          ∃ hz : z ∈ Λ, aP u.1 ⟨z, hz⟩ P = u.1.L.one t := by
        intro z hz
        induction hz using Submodule.span_induction with
        | mem z hz =>
          obtain ⟨x, hx, x', hx', hnx, hnx', rfl⟩ := hz
          refine ⟨hO.mul_mem hx hx', ?_⟩
          rw [← aP_mul u.1 ⟨x, hx⟩ ⟨x', hx'⟩]
          have := hP ⟨x', hx'⟩ ((pcond_iff_nrd r _).2 hnx')
          rw [kill_iff] at this
          exact this ⟨x, hx⟩ ((pcond_iff_nrd r _).2 hnx)
        | zero => exact ⟨Λ.zero_mem, aP_zero u.1 P⟩
        | add x y _ _ hx hy =>
          obtain ⟨hx, hxP⟩ := hx; obtain ⟨hy, hyP⟩ := hy
          refine ⟨Λ.add_mem hx hy, ?_⟩
          have : (⟨x + y, Λ.add_mem hx hy⟩ : ↥Λ) = ⟨x, hx⟩ + ⟨y, hy⟩ := rfl
          rw [this, aP_add, hxP, hyP, u.1.L.one_mul]
        | smul n x _ hx =>
          obtain ⟨hx, hxP⟩ := hx
          refine ⟨Λ.smul_mem n hx, ?_⟩
          have hmem : (((n : ℚ)) : ℍ[ℚ, a, b]) * x ∈ Λ := hO.mul_mem (intCast_mem hO n) hx
          have : (⟨n • x, Λ.smul_mem n hx⟩ : ↥Λ) = ⟨(((n : ℚ)) : ℍ[ℚ, a, b]) * x, hmem⟩ := by
            apply Subtype.ext; show n • x = (((n : ℚ)) : ℍ[ℚ, a, b]) * x
            rw [zsmul_eq_mul]; push_cast; rfl
          rw [this, ← aP_mul u.1 ⟨_, intCast_mem hO n⟩ ⟨x, hx⟩, hxP, aP_one]
      obtain ⟨h1, h1P⟩ := gen _ (RAM2 1 hO.one_mem)
      have : (⟨(r : ℤ) • (1 : ℍ[ℚ, a, b]), h1⟩ : ↥Λ) = ⟨((r : ℚ) : ℍ[ℚ, a, b]), hrΛ⟩ := by
        apply Subtype.ext; show (r : ℤ) • (1 : ℍ[ℚ, a, b]) = ((r : ℚ) : ℍ[ℚ, a, b])
        rw [zsmul_eq_mul, mul_one]; push_cast; rfl
      rw [← this]; exact h1P

  exact ALQIsoKernelT.iso_of_same_kernel u u u'' ρ hρ Mρ Lρ (𝟙 u.1.A) hid r hrp.pos hcopN Dρ Dρ' Vρ Wρ hcopℓ
    (φ₁ ≫ φ₂) hΦ MΦ LΦ (ψ₂ ≫ ψ₁) hΨ (r * r) (Nat.mul_pos hrp.pos hrp.pos) hcopN2 DΦ DΦ' VΦ WΦ hcopℓ2
    (fun t P => (K t P).1) (fun t P => (K t P).2)

end S_CerednikDrinfeld_QM_FakeEllipticCurve_WithExtraLevel_iso_of_isAtkinLehnerQuotient_comp_of_commRing
end P2MW
export P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_WithExtraLevel_iso_of_isAtkinLehnerQuotient_comp_of_commRing (solution)
