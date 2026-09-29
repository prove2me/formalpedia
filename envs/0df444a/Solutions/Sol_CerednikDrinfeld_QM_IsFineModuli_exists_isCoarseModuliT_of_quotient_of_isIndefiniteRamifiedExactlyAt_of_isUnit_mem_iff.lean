-- Prove2me | solution 1 for CerednikDrinfeld.QM.IsFineModuli.exists_isCoarseModuliT_of_quotient_of_isIndefiniteRamifiedExactlyAt_of_isUnit_mem_iff
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.141142+00:00
-- url     : https://prove2.me/submissions/a3fa7f51-1732-5b21-a69b-84360d4fd154

import Mathlib
import Definitions.Def_CerednikDrinfeld_QMFineModuli
import Theorems.Thm_CerednikDrinfeld_QM_exists_ptT_eq_ptF_comp_of_isFineModuli_of_forall_ptF_comp_eq
import Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_WithExtraLevel_exists_flat_surjective_withFullLevel_forall_factorsThrough_iff
import Theorems.Thm_CerednikDrinfeld_QM_IsLevelTwistAction_ptF_comp_eq_ptF_comp_of_forall_factorsThrough_levK_iff
import Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_FullLevel_exists_extraLevel_forall_factorsThrough_iff
import Theorems.Thm_CerednikDrinfeld_QM_IsFineModuli_existsUnique_hom_ptT_comp_eq
import Theorems.Thm_CerednikDrinfeld_QM_IsFineModuli_exists_opens_isClosed_range_subset_iff_forall_factorsThrough_lev_imp
import Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_ExtraLevel_factorsThrough_iff_of_forall_geomPoint
import Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_ExtraLevel_exists_fullLevel_forall_factorsThrough_iff
import Theorems.Thm_AlgebraicGeometry_Scheme_exists_opens_isClosed_preimage_eq_existsUnique_of_quotient
import Theorems.Thm_CerednikDrinfeld_QM_exists_eq_comp_autHom_of_comp_eq_of_isAlgClosed
import Theorems.Thm_AlgebraicGeometry_exists_comp_eq_of_isIntegralHom_of_surjective_of_isAlgClosed
import Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_WithExtraLevel_exists_isPullback
import Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_FullLevel_exists_forall_factorsThrough_iff_of_mul_mem
import Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_exists_extraLevel_forall_factorsThrough_mapPt_iff
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_QM_IsFineModuli_exists_isCoarseModuliT_of_quotient_of_isIndefiniteRamifiedExactlyAt_of_isUnit_mem_iff
p2m_attr_erase "instance" "GoodReductionJacobian.RelativeGroupLaw.isIso_endKerStr_schemeHomOverId AlgebraicGeometry.Scheme.PresheafOfModules.symmetricCategory SheafOfModules.instFaithfulRingSheafPModToPMod SheafOfModules.symmetricCategory AlgebraicGeometry.Scheme.PresheafOfModules.monoidalCategory AlgebraicGeometry.Scheme.PresheafOfModules.monoidalClosed SheafOfModules.instFullRingSheafPModToPMod SheafOfModules.monoidalCategory AlgebraicGeometry.Scheme.Modules.symmetricCategory SheafOfModules.monoidalClosed SheafOfModules.instIsLocalizationPModRingSheafSheafifyFunctorPresheafW SheafOfModules.sheafifyFunctor_monoidal AlgebraicGeometry.Scheme.Modules.monoidalClosed AlgebraicGeometry.instMonoidalPresheafOfModulesModulesSheafify AlgebraicGeometry.Scheme.Modules.monoidalCategory PresheafOfModules.instMonoidalClosed PresheafOfModules.InternalHom.instModuleCarrierObjOppositeCommRingCatSubtypePiFamilyMemAddSubgroupNaturalFamilies PresheafOfModules.InternalHom.instModuleCarrierObjOppositeRingCatCompCommRingCatForget₂RingHomCarrierCarrierAbPresheaf PresheafOfModules.InternalHom.instSMulCarrierObjOppositeCommRingCatSubtypePiFamilyMemAddSubgroupNaturalFamilies AlgebraicGeometry.Scheme.Hom.opensMapFinal AlgebraicGeometry.RelPicard.RigidifiedLineBundle.setoid AlgebraicGeometry.RelPicard.RigidifiedLineBundle.instInhabited AlgebraicGeometry.OModulePresheaf.isScalarTower AlgebraicGeometry.Scheme.OrderedAffineCover.instLinearOrder AlgebraicGeometry.OModulePresheaf.module AlgebraicGeometry.Scheme.OrderedAffineCover.instFintype AlgebraicGeometry.Scheme.OrderedAffineCover.instFintypeIdx AlgebraicGeometry.OModulePresheaf.addCommGroup AlgebraicGeometry.Scheme.OrderedAffineCover.instDecidableEqIdx AlgebraicGeometry.OModulePresheaf.moduleSections TwoChartCech.Sections.M0_moduleA TwoChartCech.Sections.M1_module TwoChartCech.Cover.A01_algebra TwoChartCech.Cover.A0_algebra TwoChartCech.Cover.A1_commRing TwoChartCech.Cover.A1_algebra TwoChartCech.Sections.M01_module TwoChartCech.Sections.M0_addCommGroup TwoChartCech.Sections.M0_tower TwoChartCech.Sections.M01_addCommGroup"
p2m_attr_erase "instance" "TwoChartCech.Cover.A0_commRing TwoChartCech.Sections.M1_tower TwoChartCech.Sections.M01_moduleA TwoChartCech.Sections.M0_module TwoChartCech.Sections.M1_moduleA TwoChartCech.Sections.M1_addCommGroup TwoChartCech.Cover.A01_commRing TwoChartCech.Sections.M01_tower CoherentBaseChange.TwoTermComplex.C0_module CoherentBaseChange.TwoTermComplex.C0_addCommGroup CoherentBaseChange.TwoTermComplex.C1_module CoherentBaseChange.TwoTermComplex.C1_addCommGroup CoherentBaseChange.TwoTermComplex.C0_free CoherentBaseChange.TwoTermComplex.C1_finite CoherentBaseChange.TwoTermComplex.C0_finite CoherentBaseChange.TwoTermComplex.C1_free AlgebraicGeometry.OModulePresheaf.instSubsingletonObjZero AlgebraicGeometry.Scheme.Modules.preservesBinaryProducts_opensMap AlgebraicGeometry.Scheme.Modules.pullback_monoidal AlgebraicGeometry.Scheme.Modules.sheafify_isLocalization' AlgebraicGeometry.Scheme.Modules.preservesTerminal_opensMap AlgebraicGeometry.Scheme.Modules.pullback₀_monoidal AlgebraicGeometry.Scheme.Modules.preservesFiniteProducts_opensMap AlgebraicGeometry.Scheme.Modules.instLiftingPresheafOfModulesSheafifyPresheafWOpensCarrierCarrierCommRingCatGrothendieckTopologyObjFunctorOppositeIsSheafSheafCompPullback₀Pullback PresheafOfModules.PullbackMonoidal.pullback_monoidal PresheafOfModules.PullbackMonoidal.isIso_δ PresheafOfModules.pushforward_laxMonoidal PresheafOfModules.PullbackMonoidal.isIso_η PresheafOfModules.free_monoidal PresheafOfModules.restrictScalars_laxMonoidal PresheafOfModules.PullbackMonoidal.isIso_δ_gS PresheafOfModules.pullback_oplaxMonoidal PresheafOfModules.PullbackMonoidal.instPreservesColimitsOfSizeCompOppositeCommRingCatRingCatForget₂RingHomCarrierCarrierPb PresheafOfModules.pullback_monoidal' AlgebraicGeometry.SmoothOfRelativeDimension.fiberToSpecResidueField AlgebraicGeometry.SmoothOfRelativeDimension.pullback_snd AlgebraicGeometry.SmoothOfRelativeDimension.pullback_fst AlgebraicGeometry.SmoothOfRelativeDimension.smooth_one AlgebraicGeometry.SmoothProperCurve.isIntegral_pullback_Spec_field AlgebraicGeometry.IsProper.fiberToSpecResidueField"
p2m_attr_erase "instance" "AlgebraicCurve.CurveModel.isProper AlgebraicCurve.CurveModel.isIntegral AlgebraicCurve.CurveModel.smooth AlgebraicGeometry.Scheme.LocalRepresentabilityULift.instIsLocallyInjectiveFunUliftYonedaGluedToSheaf AlgebraicGeometry.Scheme.LocalRepresentabilityULift.instIsLocallySurjectiveFunUliftYonedaGluedToSheafOfIsLocallySurjectiveZariskiTopologyDescFunctorOppositeType AlgebraicGeometry.Scheme.LocalRepresentabilityULift.instIsOpenImmersionToGlued AlgebraicGeometry.Scheme.LocalRepresentabilityULift.instIsIsoSheafZariskiTopologyTypeUliftYonedaGluedToSheaf AlgebraicGeometry.RelPicard.instIsOpenImmersionToGlued AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.instFundamentalIdentityOfSumRamificationInertia AlgebraicCurve.Place.instIsScalarTowerResidueFieldRestrictPushforward AlgebraicCurve.Place.instAlgebraResidueFieldRestrictPushforward AlgebraicCurve.Place.instIsLocalHomRestrictInclusion AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions PresheafOfModules.ExteriorPower.instModulePresheafAb AlgebraicGeometry.RelEffCartierDiv.subsingleton_of_degree_zero AlgebraicGeometry.RelEffCartierDiv.isIso_subschemeIota_snd_of_degree_one AlgebraicGeometry.isIso_ker_graphOver_subschemeIota_snd AlgebraicGeometry.isClosedImmersion_graphOver AlgebraicGeometry.FGSubalgebra.instIsDirectedLe AlgebraicGeometry.FGSubalgebra.instQuasiSeparatedSpaceCarrierCarrierCommRingCatObjOppositeSchemeSpecDiagram AlgebraicGeometry.FGSubalgebra.instIsCofilteredOpposite AlgebraicGeometry.FGSubalgebra.instIsAffineObjOppositeSchemeSpecDiagram AlgebraicGeometry.FGSubalgebra.instNonempty AlgebraicGeometry.FGSubalgebra.instNonemptySubtypeLeSubalgebraValFG AlgebraicGeometry.FGSubalgebra.instCompactSpaceCarrierCarrierCommRingCatObjOppositeSchemeSpecDiagram AlgebraicGeometry.FGSubalgebra.instIsDirectedSubtypeLeSubalgebraValFG AlgebraicGeometry.FGSubalgebra.instIsAffineHomMapOppositeSchemeSpecDiagram AlgebraicGeometry.FGSubalgebra.instIsFiltered AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instNeg AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instSMulInt AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instAddCommGroup AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instAdd AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instSub"
p2m_attr_erase "instance" "AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instModuleCarrierObjOppositeOpensCarrierCarrierCommRingCatPresheafOpOpensTop AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instSMulCarrierObjOppositeOpensCarrierCarrierCommRingCatPresheafOpOpensTop AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instSMulNat AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instZero AlgebraicCurve.instHasLocalResidue_of_hasCanonicalLocalResidueK AlgebraicCurve.instHasCanonicalLocalResidueK_of_hasCanonicalLocalResidueKStar AlgebraicCurve.Place.kw_ffgc_finiteDimensional_adicCompletion instAlgebraSubtypeMemValuationSubring_definitions AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersIntegersCompletion ModularCurve.KwF4gRRTate.instAlgebraKAdicCompletionIntegers AlgebraicCurve.Place.kw_ffgc_continuousSMul_adicCompletionComap AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersCompletionCompletion IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions AlgebraicCurve.instHasCanonicalLocalResidueK AlgebraicCurve.Place.instAlgebra_restrictResidueField AlgebraicCurve.Place.instIsScalarTower_restrictResidueField AlgebraicCurve.instHasLocalResidue AlgebraicCurve.HasSeparableResidue.of_perfectField_of_isCurveOver AlgebraicCurve.HasSeparableResidue.of_perfectField AlgebraicCurve.Place.instIsLocalHom_restrictSubringHom AlgebraicCurve.instHasCanonicalLocalResidueKStar ModularCurve.KwNo6Pin.isLocalRing_completion SheafOfModules.isIso_ihomModelToIhom AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instDecidableEqIdx AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instFintype AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instLinearOrder AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instFintypeIdx AlgebraicGeometry.OModulePresheaf.Leray.relAltC_scalarTower AlgebraicGeometry.OModulePresheaf.Leray.ker_relAltd_modΓ AlgebraicGeometry.OModulePresheaf.Leray.relAltC_modΓ AlgebraicGeometry.OModulePresheaf.Leray.biC_abGrp AlgebraicGeometry.OModulePresheaf.Leray.relAltH_modΓ AlgebraicGeometry.OModulePresheaf.Leray.ker_relAltd_smul AlgebraicGeometry.OModulePresheaf.Leray.relAltH_scalarTower AlgebraicGeometry.OModulePresheaf.Leray.relAltH_smul"
p2m_attr_erase "instance" "AlgebraicGeometry.OModulePresheaf.Leray.biC_module DoubleComplex.instModuleE₂I DoubleComplex.Bounded.modR DoubleComplex.instModuleE₂II DoubleComplex.instAddCommGroupE₂II DoubleComplex.Bounded.abGrp DoubleComplex.instAddCommGroupE₂I AlgebraicGeometry.ChowDatum.hι_closed AlgebraicGeometry.ChowDatumProj.hιN_closed AlgebraicGeometry.ChowDatumProj.hp_proper AlgebraicGeometry.ChowDatum.hp_isoU AlgebraicGeometry.ChowDatum.hp_proper AlgebraicGeometry.ProjSpace.algebraAway AlgebraicGeometry.ProjSpace.instIsProperProdOverπ AlgebraicGeometry.ChowDatumProj.hp_isoU AlgebraicGeometry.ProjSpace.isProper_π AlgebraicGeometry.ProjSpace.finiteType_mvPolynomial ProjSpaceCech.GradedModule.H.module ProjSpaceCech.GradedModule.H.addCommGroup ProjSpaceCech.GradedModule.sec.instAdd ProjSpaceCech.GradedModule.sec.instNeg ProjSpaceCech.GradedModule.acg ProjSpaceCech.GradedModule.Frac.setoid ProjSpaceCech.GradedModule.modR ProjSpaceCech.GradedModule.sec.instModule ProjSpaceCech.GradedModule.sec.instAddCommGroup ProjSpaceCech.GradedModule.sec.instZero ProjSpaceCech.GradedModule.Presentation.fJ ProjSpaceCech.GradedModule.sec.instSMul ProjSpaceCech.Twist.H.module ProjSpaceCech.Idx.instFintype ProjSpaceCech.Twist.H.addCommGroup ProjSpaceCech.Idx.instDecidableEq ProjSpaceCech.Twist.Mon.instDecidableEq ProjSpaceCech.Twist.cochain.instAddCommGroup ProjSpaceCech.Twist.cochain.instModule AlgebraicGeometry.FGSubalgebra.tensorStage_directedSystem AlgebraicGeometry.RelEffCartierDiv.isClosedImmersion_subschemeι_resProdMap AlgebraicGeometry.RelEffCartierDiv.isOpenImmersion_resProdMap AlgebraicCurve.CurveModel.locallyOfFiniteType_gluedToBase"
p2m_attr_erase "instance" "AlgebraicCurve.CurveModel.isFractionRing_overlap AlgebraicCurve.CurveModel.isLocallyNoetherian_glued AlgebraicCurve.CurveModel.jacobsonSpace_glued AlgebraicCurve.CurveModel.isOpenImmersion_ι₀ AlgebraicCurve.CurveModel.isIntegral_glued AlgebraicCurve.CurveModel.quasiSeparated_gluedToBase AlgebraicCurve.CurveModel.compactSpace_glued AlgebraicCurve.CurveModel.isIntegral_adjoin_chartRing AlgebraicCurve.CurveModel.isFractionRing_overlap_functionField AlgebraicCurve.CurveModel.isProper_gluedToBase AlgebraicCurve.CurveModel.isOpenImmersion_ιU AlgebraicCurve.CurveModel.isOpenImmersion_f₀ AlgebraicCurve.CurveModel.isOpenImmersion_fInf AlgebraicCurve.CurveModel.isOpenImmersion_ιInf AlgebraicCurve.CurveModel.algebra_overlap_functionField AlgebraicCurve.CurveModel.quasiCompact_gluedToBase AlgebraicCurve.CurveModel.algebraAdjoin AlgebraicCurve.CurveModel.isDedekindDomain_chartRing AlgebraicCurve.CurveModel.isIntegralClosure AlgebraicCurve.CurveModel.finite_chartRing AlgebraicCurve.CurveModel.centre_isPrime AlgebraicCurve.CurveModel.isFractionRing_chartRing AlgebraicCurve.CurveModel.finiteType_chartRing AlgebraicCurve.CurveModel.isNoetherianRing_chartRing AlgebraicCurve.CurveModel.isScalarTower_base_adjoin AlgebraicCurve.CurveModel.isScalarTower_adjoin AlgebraicCurve.CurveModel.chartRing_finitePresentation instTopologicallyFGOfFiniteType AlgebraicGeometry.ProjSpace.twistObj.addCommGroup AlgebraicGeometry.ProjSpace.twistFam.module AlgebraicGeometry.ProjSpace.twistObj.module AlgebraicGeometry.ProjSpace.twistObj.moduleSections AlgebraicGeometry.ProjSpace.twistFam.addCommGroup"
p2m_attr_erase "simp" "GoodReductionJacobian.RelativeGroupLaw.baseChangePointToBase_ofBase GoodReductionJacobian.RelativeGroupLaw.baseChangePointToBase_coe GoodReductionJacobian.RelativeGroupLaw.baseChangePointOfBase_coe GoodReductionJacobian.RelativeGroupLaw.baseChange_inv GoodReductionJacobian.RelativeGroupLaw.baseChangePointOfBase_toBase GoodReductionJacobian.RelativeGroupLaw.baseChange_mul GoodReductionJacobian.RelativeGroupLaw.baseChange_one GoodReductionJacobian.RelativeGroupLaw.nsmul_zero GoodReductionJacobian.RelativeGroupLaw.mem_torsionSubset GoodReductionJacobian.RelativeGroupLaw.nsmul_succ NeronModelInfra.NeronModelPropertyBundle.endExtensionEquiv_symm_restrict NeronModelInfra.schemeHomOverComp_id_left NeronModelInfra.schemeHomOverComp_id_right NeronModelInfra.schemeHomOverId_coe NeronModelInfra.NeronModelPropertyBundle.endExtensionEquiv_apply NeronModelInfra.NeronModelPropertyBundle.restrict_endExtensionEquiv_symm NeronModelInfra.schemeHomOverComp_coe NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_fst NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_snd NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_fst NeronSpecialFibreInfra.neronEndRestrictEquiv_apply NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_fst_assoc NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_snd NeronSpecialFibreInfra.neronEndExtension_genericFibreRestrict NeronSpecialFibreInfra.specClosedFibreInclusion_eq NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_fst_assoc NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_snd_assoc NeronSpecialFibreInfra.genericFibreRestrict_neronEndExtension NeronSpecialFibreInfra.homOverId_coe NeronSpecialFibreInfra.homOverComp_coe NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_snd_assoc GoodReductionJacobian.RelativeGroupLaw.fibre_inv GoodReductionJacobian.RelativeGroupLaw.fibrePointToBase_coe GoodReductionJacobian.RelativeGroupLaw.fibrePointOfBase_toBase GoodReductionJacobian.RelativeGroupLaw.fibre_mul GoodReductionJacobian.RelativeGroupLaw.fibrePointToBase_ofBase GoodReductionJacobian.RelativeGroupLaw.fibre_one GoodReductionJacobian.RelativeGroupLaw.fibrePointOfBase_coe AlgebraicGeometry.schemeFibreEndo_snd AlgebraicGeometry.schemeFibreEndo_fst"
p2m_attr_erase "simp" "RegularLocalRingQuotientAscent.dualNumberFst_apply NeronModelInfra.schemeHomOverNpow_succ NeronModelInfra.schemeHomOverNpow_zero GoodReductionJacobian.relativeGroupLawOfGrpObj_inv GoodReductionJacobian.relativeGroupLawOfGrpObj_mul GoodReductionJacobian.overHomEquivSchemeHomOver_apply_coe GoodReductionJacobian.relativeGroupLawOfGrpObj_one GoodReductionJacobian.overHomEquivSchemeHomOver_symm_apply_left SheafOfModules.tensorUnit_eq AlgebraicGeometry.Scheme.Modules.tensorUnit_eq PresheafOfModules.InternalHom.presheaf_map_apply PresheafOfModules.InternalHom.curryFamily_app PresheafOfModules.InternalHom.add_app PresheafOfModules.InternalHom.smul_app PresheafOfModules.InternalHom.zero_app PresheafOfModules.ihomObj_map_val PresheafOfModules.ihomFunctor_map PresheafOfModules.InternalHom.restrict_app PresheafOfModules.InternalHom.postcomp_app PresheafOfModules.InternalHom.neg_app PresheafOfModules.curry'_app_val PresheafOfModules.InternalHom.presheaf_obj PresheafOfModules.ihomFunctor_obj PresheafOfModules.ihomObj_obj PresheafOfModules.InternalHom.sub_app PresheafOfModules.ihomMap_app_val AlgebraicGeometry.Scheme.Modules.tensorPow_zero AlgebraicGeometry.Scheme.Modules.tensorPow_succ AlgebraicGeometry.RelPicard.RigidifiedLineBundle.mk.sizeOf_spec AlgebraicGeometry.RelPicard.RigidifiedLineBundle.mk.injEq AlgebraicGeometry.Scheme.OrderedAffineCover.mk.injEq AlgebraicGeometry.OModulePresheaf.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCover.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.mk.injEq AlgebraicGeometry.Scheme.TwoAffineOpenCover.mk.injEq AlgebraicGeometry.Scheme.TwoAffineOpenCover.mk.sizeOf_spec AlgebraicGeometry.Scheme.TwoAffineOpenCover.pullback_U1 AlgebraicGeometry.Scheme.TwoAffineOpenCover.pullback_U0 TwoChartCech.Sections.mk.injEq TwoChartCech.Cover.mk.injEq"
p2m_attr_erase "simp" "TwoChartCech.GrothendieckComplex.mk.injEq TwoChartCech.Sections.mk.sizeOf_spec TwoChartCech.Cover.mk.sizeOf_spec TwoChartCech.Cover.lineBundle_r0_apply TwoChartCech.GrothendieckComplex.mk.sizeOf_spec TwoChartCech.Cover.lineBundle_r1_apply CoherentBaseChange.TwoTermComplex.mk.sizeOf_spec CoherentBaseChange.TwoTermComplex.mk.injEq AlgebraicGeometry.OModulePresheaf.prod_obj AlgebraicGeometry.OModulePresheaf.restrOpen_obj AlgebraicGeometry.OModulePresheaf.DevissageStep.mk.injEq AlgebraicGeometry.OModulePresheaf.pushforward_obj AlgebraicGeometry.OModulePresheaf.im_obj AlgebraicGeometry.OModulePresheaf.pow_obj AlgebraicGeometry.OModulePresheaf.fstHom_app AlgebraicGeometry.OModulePresheaf.ker_obj AlgebraicGeometry.OModulePresheaf.coker_obj AlgebraicGeometry.OModulePresheaf.DevissageStep.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCover.preimage_U AlgebraicGeometry.OModulePresheaf.sndHom_app AlgebraicGeometry.OModulePresheaf.Hom.mk.injEq AlgebraicGeometry.OModulePresheaf.Hom.id_app AlgebraicGeometry.OModulePresheaf.AffHom.appSections_apply AlgebraicGeometry.OModulePresheaf.AffHom.comp_app AlgebraicGeometry.OModulePresheaf.AffSES.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.AffHom.kerMap_coe AlgebraicGeometry.OModulePresheaf.AffHom.id_app AlgebraicGeometry.OModulePresheaf.Hom.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.Hom.toAffHom_app AlgebraicGeometry.OModulePresheaf.SES.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.AffHom.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.Hom.comp_app AlgebraicGeometry.OModulePresheaf.SES.mk.injEq AlgebraicGeometry.OModulePresheaf.AffHom.mk.injEq AlgebraicGeometry.OModulePresheaf.Hom.appSections_apply AlgebraicGeometry.OModulePresheaf.AffSES.mk.injEq PresheafOfModules.freeεIso_hom_app PresheafOfModules.freeμIso_hom_app AlgebraicGeometry.RelPicard.RepresentsRelSubPic.mk.injEq AlgebraicGeometry.RelPicard.SubPicCondition.mk.injEq"
p2m_attr_erase "simp" "AlgebraicGeometry.RelPicard.SubPicCondition.mk.sizeOf_spec AlgebraicGeometry.RelPicard.RepresentsRelSubPic.mk.sizeOf_spec AlgebraicGeometry.SmoothProperCurve.sectionBaseChange_coe_snd AlgebraicGeometry.SmoothProperCurve.sectionBaseChange_coe_fst AlgebraicCurve.CurveModel.mk.injEq AlgebraicCurve.CurveModel.mk.sizeOf_spec AlgebraicCurve.mulAdele_apply AlgebraicCurve.residuePairing_apply_coe AlgebraicCurve.mem_adeleBdd AlgebraicCurve.weilSmul_one AlgebraicCurve.diagonalHom_apply AlgebraicCurve.weilSmul_apply AlgebraicCurve.adeleSpaceMul_coe AlgebraicCurve.mulAdele_one AlgebraicGeometry.SmoothProperCurve.FiniteMapData.twoAffineOpenCover_U1 AlgebraicGeometry.SmoothProperCurve.FiniteMapData.mk.injEq AlgebraicGeometry.SmoothProperCurve.FiniteMapData.mk.sizeOf_spec AlgebraicGeometry.SmoothProperCurve.FiniteMapData.twoAffineOpenCover_U0 AlgebraicGeometry.RelPicard.SubPicCondition.onClasses_mk AlgebraicGeometry.RelPicard.relSubPicPresheaf_map_coe CategoryTheory.Functor.OverTotal.ofFibre_fst CategoryTheory.Functor.overTotal_map_fst AlgebraicGeometry.Scheme.LocalRepresentabilityULift.glueData_J AlgebraicGeometry.Scheme.LocalRepresentabilityULift.uliftYoneda_toGlued_uliftYonedaGluedToSheaf AlgebraicGeometry.Scheme.LocalRepresentabilityULift.glueData_t' AlgebraicGeometry.Scheme.LocalRepresentabilityULift.uliftYoneda_toGlued_uliftYonedaGluedToSheaf_assoc AlgebraicGeometry.Scheme.LocalRepresentabilityULift.uliftYonedaGluedToSheaf_app_toGlued AlgebraicGeometry.Scheme.LocalRepresentabilityULift.glueData_openCover_map AlgebraicGeometry.Scheme.LocalRepresentabilityULift.uliftYonedaGluedToSheaf_app_comp AlgebraicGeometry.Scheme.LocalRepresentabilityULift.glueData_V AlgebraicGeometry.Scheme.LocalRepresentabilityULift.glueData_t AlgebraicGeometry.Scheme.LocalRepresentabilityULift.glueData_U AlgebraicGeometry.Scheme.LocalRepresentabilityULift.glueData_f AlgebraicGeometry.RelPicard.designationOfRepresentableBy_P AlgebraicGeometry.RelPicard.designationOfRepresentableBy_toBase AlgebraicGeometry.RelPicard.rigSection_snd AlgebraicGeometry.RelPicard.RigidifiedLineBundle.ofInvertible_L AlgebraicGeometry.RelPicard.rigSection_snd_assoc AlgebraicGeometry.RelPicard.SubPicGroupCondition.mk.injEq AlgebraicGeometry.RelPicard.SubPicGroupCondition.mk.sizeOf_spec"
p2m_attr_erase "simp" "AlgebraicCurve.coe_cechH0Equiv_apply AlgebraicCurve.cechH1ToH1_mk AlgebraicCurve.lSpaceOn_univ AlgebraicCurve.lSpaceOn_empty AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.Divisor.mapRestrict_single AlgebraicCurve.Divisor.pushforward_single AlgebraicCurve.Place.coe_restrictInclusion AlgebraicCurve.Place.mem_fiber AlgebraicCurve.Place.restrict_toValuationSubring AlgebraicCurve.Divisor.degree_pushforward AlgebraicCurve.Place.restrictResidueMap_residue AlgebraicCurve.Pic0.coe_pushforwardDegZeroHom AlgebraicCurve.Pic0.coe_pullbackDegZeroHom AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Divisor.degree_pushforwardAlong"
p2m_attr_erase "simp" "AlgebraicCurve.Pic0.coe_degZeroCorrespondence AlgebraicCurve.Place.mem_fiberAlong AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.jqNModC_one ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one AlgebraicCurve.Place.differentialCoeff_zero AlgebraicCurve.Place.differentialCoeff_dCoord AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.injEq AlgebraicCurve.TranscendenceTower.mk.injEq AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec AlgebraicCurve.PoleDivisorPackage.mk.injEq AlgebraicGeometry.RelPicard.thetaBundle_def AlgebraicGeometry.RelPicard.picardBundle_def AlgebraicGeometry.RelEffCartierDiv.toRelEffDivisor_ofRelEffDivisor AlgebraicGeometry.RelEffCartierDiv.toRelEffDivisor_I AlgebraicGeometry.mapOnProdOver_fst_assoc AlgebraicGeometry.RelEffCartierDiv.mk.sizeOf_spec AlgebraicGeometry.RelEffCartierDiv.mk.injEq AlgebraicGeometry.mapOnProdOver_snd AlgebraicGeometry.mapOnProdOver_fst AlgebraicGeometry.mapOnProdOver_snd_assoc AlgebraicGeometry.mapOnProdOver_id AlgebraicCurve.RelEffDivisor.mk.sizeOf_spec AlgebraicCurve.mapOnProd_fst"
p2m_attr_erase "simp" "AlgebraicCurve.mapOnProd_fst_assoc AlgebraicCurve.mapOnProd_snd AlgebraicCurve.UnivDivisorPack.mk.injEq AlgebraicCurve.RelEffDivisor.mk.injEq AlgebraicCurve.UnivDivisorPack.mk.sizeOf_spec AlgebraicCurve.mapOnProd_snd_assoc AlgebraicGeometry.Scheme.Modules.exteriorPower_obj PresheafOfModules.exteriorPower_map_ιMulti PresheafOfModules.ExteriorPower.appₗ_apply AlgebraicGeometry.prodKerGraph_one AlgebraicGeometry.fibrePowOver.proj_comp AlgebraicGeometry.prodKerGraph_zero AlgebraicGeometry.RelEffCartierDiv.empty_I AlgebraicGeometry.fibrePowOver.proj_comp_assoc AlgebraicGeometry.graphOver_fst_assoc AlgebraicGeometry.RelEffCartierDiv.toPoint_comp AlgebraicGeometry.RelEffCartierDiv.toPoint_comp_assoc AlgebraicGeometry.graphOver_fst AlgebraicGeometry.RelEffCartierDiv.ofPoint_I AlgebraicGeometry.graphOver_snd AlgebraicGeometry.graphOver_snd_assoc AlgebraicCurve.SymmetricPowerPackage.mk.sizeOf_spec AlgebraicCurve.SymmetricPowerPackage.mk.injEq AlgebraicGeometry.FGSubalgebra.cocone_ι_app_apply AlgebraicGeometry.RelPicard.fst_toProdSpec AlgebraicGeometry.RelPicard.toProdSpec_fst_assoc AlgebraicGeometry.RelPicard.pointsSubBasepointModule_cons AlgebraicGeometry.RelPicard.pointsSubBasepointModule_nil AlgebraicGeometry.RelPicard.fst_toProdSpec_assoc AlgebraicGeometry.RelPicard.toProdSpec_fst AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.sub_app AlgebraicGeometry.Scheme.IdealSheafData.sres_sresTop AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.add_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.mk.sizeOf_spec AlgebraicGeometry.Scheme.IdealSheafData.coe_resLE AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.smul_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.coe_ofLE_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.ideal_range AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.zero_app AlgebraicGeometry.Scheme.IdealSheafData.sres_sres"
p2m_attr_erase "simp" "AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.comp_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.neg_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.id_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.coe_mulRight_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.nsmul_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.mk.injEq AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.zsmul_app AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.sizeOf_spec AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.injEq AlgebraicCurve.adeleSingle_coe AlgebraicCurve.kaehlerResidueTermKFam_apply AlgebraicCurve.Place.LocalResidueData.mk.injEq AlgebraicCurve.Place.LocalResidueData.mk.sizeOf_spec AlgebraicCurve.Place.kw_ffgc_adicCompletionComapIntegers_coe AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.sizeOf_spec AlgebraicCurve.Place.mem_simplePoleSubmodule AlgebraicCurve.Place.coe_uniformizerSubring ModularCurve.Lg37.Lg37CompletionSection.mk.injEq AlgebraicCurve.Place.CoefficientFieldSection.mk.injEq AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.injEq ModularCurve.Lg37.Lg37CompletionSection.mk.sizeOf_spec AlgebraicCurve.Place.CoefficientFieldSection.mk.sizeOf_spec AlgebraicCurve.Place.poleSubmodule_one AlgebraicCurve.Place.mem_poleSubmodule AlgebraicGeometry.Scheme.Modules.toUnitSection_ofUnitSection AlgebraicGeometry.Scheme.Modules.pullbackSection_def AlgebraicGeometry.Scheme.Modules.ofUnitSection_toUnitSection PresheafOfModules.InternalHom.IsSheafAux.appAt_toPresheafHom SheafOfModules.ihomSectionsEquivFamily_unit AlgebraicGeometry.Scheme.Modules.restrictHomEquivFamily_apply SheafOfModules.ihomEval_unit_app AlgebraicGeometry.Scheme.Modules.ihomEval_zero_right AlgebraicGeometry.Scheme.Modules.ihomEval_zero_left AlgebraicGeometry.Scheme.Modules.homOfFamily_app_apply SheafOfModules.unit_ihomSectionsEquivFamily AlgebraicGeometry.Scheme.Modules.familyOfHom_app AlgebraicGeometry.Scheme.Modules.restrictUnitIso_hom_app_apply AlgebraicGeometry.Scheme.Modules.restrictUnitIso_inv_app_apply AlgebraicGeometry.Scheme.Modules.restrictHomOfFamily_app_apply AlgebraicGeometry.Scheme.Modules.restrictHomEquivFamily_symm_apply"
p2m_attr_erase "simp" "AlgebraicGeometry.Scheme.Modules.tensorSections_zero_right AlgebraicGeometry.Scheme.Modules.map_unitSection AlgebraicGeometry.Scheme.Modules.tensorSectionsBilin_apply AlgebraicGeometry.Scheme.Modules.tensorPowSection_zero AlgebraicGeometry.Scheme.Modules.tensorSections_zero_left AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_neg AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_zero AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_sub AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_add AlgebraicGeometry.Scheme.OrderedAffineCover.toCoverOf_U AlgebraicGeometry.Scheme.OrderedAffineCoverOf.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCoverOf.mk.injEq AlgebraicGeometry.Scheme.OrderedAffineCover.restrict_U AlgebraicGeometry.OModulePresheaf.Leray.restrictToPreimage_U DoubleComplex.Bounded.mk.injEq DoubleComplex.Bounded.mk.sizeOf_spec DoubleComplex.Convergence.mk.injEq DoubleComplex.Convergence.mk.sizeOf_spec DoubleComplex.SubQuot.mk.sizeOf_spec DoubleComplex.SubQuot.mk.injEq AlgebraicGeometry.ChowDatumProj.mk.sizeOf_spec AlgebraicGeometry.ChowDatum.mk.sizeOf_spec AlgebraicGeometry.ChowDatumProj.mk.injEq AlgebraicGeometry.ChowDatum.mk.injEq ProjSpaceCech.GradedModule.mk.injEq ProjSpaceCech.GradedModule.mk.sizeOf_spec ProjSpaceCech.GradedModule.Frac.mk.sizeOf_spec ProjSpaceCech.GradedModule.Presentation.mk.injEq ProjSpaceCech.GradedModule.Frac.mk.injEq ProjSpaceCech.GradedModule.Presentation.mk.sizeOf_spec ProjSpaceCech.GradedModule.Hom.shift_toLinearMap ProjSpaceCech.GradedModule.Hom.mk.sizeOf_spec ProjSpaceCech.GradedModule.Hom.mk.injEq TwoChartCech.Mumford.dK_apply TwoChartCech.Mumford.ι0_apply TwoChartCech.Mumford.ι1_apply TwoChartCech.KerCoprod.dK_apply TwoChartCech.KerCoprod.ι1_apply TwoChartCech.KerCoprod.ι0_apply AlgebraicGeometry.tilde.functorCompPullbackSpecIso_app"
p2m_attr_erase "simp" "AlgebraicGeometry.RelPicard.algEquivZeroGroupCut_toSubPicCondition AlgebraicGeometry.RelPicard.LFP.stageHom_val AlgebraicGeometry.RelPicard.BaseChange.relSubPicPresheafRestrictIso_hom_app_coe AlgebraicGeometry.RelPicard.BaseChange.relSubPicPresheafRestrictIso_inv_app_coe AlgebraicGeometry.RelPicard.BaseChange.restrict_P AlgebraicGeometry.RelEffCartierDiv.IsUniversal.lift_comp AlgebraicGeometry.RelEffCartierDiv.functor_map_fst AlgebraicGeometry.RelEffCartierDiv.IsUniversal.homEquiv_apply AlgebraicGeometry.RelEffCartierDiv.IsUniversal.lift_pullbackAlong AlgebraicGeometry.RelEffCartierDiv.IsUniversal.homEquiv_symm_apply AlgebraicGeometry.RelEffCartierDiv.IsUniversal.lift_comp_assoc AlgebraicGeometry.RelEffCartierDiv.supportedIn_top AlgebraicGeometry.RelEffCartierDiv.mem_supportedIn_iff AlgebraicGeometry.RelEffCartierDiv.supportedIn_top_eq AlgebraicGeometry.RelEffCartierDiv.restrictAlong_extendAlong AlgebraicGeometry.RelEffCartierDiv.extendAlong_I AlgebraicGeometry.RelEffCartierDiv.resProdMap_snd AlgebraicGeometry.RelEffCartierDiv.restrictAlong_I AlgebraicGeometry.RelEffCartierDiv.extendAlong_restrictAlong AlgebraicGeometry.RelEffCartierDiv.resProdMap_fst_assoc AlgebraicGeometry.RelEffCartierDiv.resProdMap_snd_assoc AlgebraicGeometry.RelEffCartierDiv.resProdMap_fst CoherentBaseChange.FibreH0Family.mk.sizeOf_spec CoherentBaseChange.FibreH0Family.mk.injEq AlgebraicGeometry.Scheme.Modules.ProjPresentation.mk.injEq AlgebraicGeometry.Scheme.Modules.ProjPresentation.mk.sizeOf_spec AlgebraicCurve.CurveModel.coe_gInf AlgebraicCurve.CurveModel.coe_tInvChart AlgebraicCurve.CurveModel.ιInf_gluedToBase_assoc AlgebraicCurve.CurveModel.ιInf_gluedToBase AlgebraicCurve.CurveModel.primeOfι₀_asIdeal AlgebraicCurve.CurveModel.coe_tChart AlgebraicCurve.CurveModel.ι₀_gluedToBase_assoc AlgebraicCurve.CurveModel.primeOfιInf_asIdeal AlgebraicCurve.CurveModel.ι₀_gluedToBase AlgebraicCurve.CurveModel.coe_tma AlgebraicCurve.CurveModel.coe_primeEquivChartPlaces AlgebraicGeometry.ProjSpace.twistObj.mk.injEq AlgebraicGeometry.ProjSpace.twistObj.zero_val AlgebraicGeometry.ProjSpace.twistObj.add_val"
p2m_attr_erase "simp" "AlgebraicGeometry.ProjSpace.twist_res_val AlgebraicGeometry.ProjSpace.twist_smul_val AlgebraicGeometry.ProjSpace.twistGradeToObj_val AlgebraicGeometry.ProjSpace.twistObj.smul_val AlgebraicGeometry.ProjSpace.twistGradeEquiv_apply_val AlgebraicGeometry.ProjSpace.twistObj.mk.sizeOf_spec QuaternionAlgebra.baseChangeRight_tmul QuaternionAlgebra.mapOfAlgebraMapEq_apply QuaternionAlgebra.baseChange_tmul QuaternionAlgebra.ClassSet.map_mk"

set_option autoImplicit false

open scoped TensorProduct Quaternion NumberField
p2m_open "CategoryTheory AlgebraicGeometry QuaternionAlgebra CerednikDrinfeld CerednikDrinfeld.QM NeronModelInfra~schemeHomOverComp_coe GoodReductionJacobian"

noncomputable section

namespace T3A

theorem isUnit_natCast_of_specHom {𝒪 S : Type} [CommRing 𝒪] [CommRing S] (m : ℕ) (hm : IsUnit ((m : ℕ) : 𝒪))
    (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of 𝒪)) : IsUnit ((m : ℕ) : S) := by
  have := hm.map (Spec.preimage s).hom
  simpa using this

theorem isPullback_fst_of_withExtraLevel_isPullback {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} {N ℓ : ℕ}
    {S S' : Type} [CommRing S] [CommRing S'] (φ : S →+* S')
    (u : FakeEllipticCurve.WithExtraLevel Λ N ℓ S) (u' : FakeEllipticCurve.WithExtraLevel Λ N ℓ S')
    (h : FakeEllipticCurve.WithExtraLevel.IsPullback φ u u') : FakeEllipticCurve.IsPullback φ u.1 u'.1 := by
  obtain ⟨g, hg, hmul, hact, hlev⟩ := h
  exact ⟨g, hg, hmul, hact, fun t' P hP => (hlev t' P).1 hP⟩

theorem disj_of_gen {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} {N m ℓ : ℕ} (L₀ : Submodule ℤ ℍ[ℚ, a, b])
    {S : Type} [CommRing S] (E : FakeEllipticCurve Λ N S) (P : E.FullLevel m) (K : E.ExtraLevel ℓ)
    (hK : ∀ (k : Type) [Field k] [IsAlgClosed k] (sk : S →+* k) (Q : SchemeHomOver (geomPoint k sk) E.f),
        FactorsThrough K.levK Q ↔
          ∃ x : ↥Λ, (x : ℍ[ℚ, a, b]) ∈ L₀ ∧
            pushPt (E.act x) (E.act_over x)
              (nsmulPt E.L (geomPoint k sk) (m / ℓ) (FakeEllipticCurve.sectionAt P.P k sk)) = Q) :
    ∀ (k : Type) [Field k] [IsAlgClosed k] (sk : S →+* k) (x : ↥Λ), (x : ℍ[ℚ, a, b]) ∈ L₀ →
        FactorsThrough E.lev
          (pushPt (E.act x) (E.act_over x)
            (nsmulPt E.L (geomPoint k sk) (m / ℓ) (FakeEllipticCurve.sectionAt P.P k sk))) →
        pushPt (E.act x) (E.act_over x)
            (nsmulPt E.L (geomPoint k sk) (m / ℓ) (FakeEllipticCurve.sectionAt P.P k sk)) = E.L.one (geomPoint k sk) := by
  intro k _ _ sk x hx hlev
  exact K.levK_disjoint _ _ ((hK k sk _).2 ⟨x, hx, rfl⟩) hlev

theorem comp_base_apply {X Y Z : Scheme.{0}} (f : X ⟶ Y) (g : Y ⟶ Z) (x : ↥X) :
    (f ≫ g).base x = g.base (f.base x) := rfl

theorem ι_base_mem {X : Scheme.{0}} (U : X.Opens) (x : ↥(U : Scheme.{0})) : U.ι.base x ∈ (U : Set ↥X) := by
  have : U.ι.base x ∈ Set.range U.ι.base := ⟨x, rfl⟩
  rwa [Scheme.Opens.range_ι] at this

theorem label_inv {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} {N m : ℕ} {𝒪 : Type} [CommRing 𝒪]
    {M : Scheme.{0}} {πM : M ⟶ Spec (CommRingCat.of 𝒪)}
    {ptF : ∀ (S : Type) [CommRing S] (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of 𝒪)),
      FakeEllipticCurve.WithFullLevel Λ N m S → SchemeHomOver s πM}
    {G : Type} [Group G] {ρ : G →* Aut M} {χ : G → ↥Λ}
    (hρ : IsLevelTwistAction Λ N m M πM ptF G ρ χ) (g h : G) (hgh : g * h = 1) :
    ∃ y : ↥Λ, (χ g : ℍ[ℚ, a, b]) * (χ h : ℍ[ℚ, a, b]) - 1 = (m : ℚ) • (y : ℍ[ℚ, a, b]) := by
  obtain ⟨y₁, hy₁⟩ := hρ.label_mul g h
  obtain ⟨y₀, hy₀⟩ := hρ.label_one
  rw [hgh] at hy₁
  refine ⟨⟨(y₀ : ℍ[ℚ, a, b]) - y₁, Λ.sub_mem y₀.2 y₁.2⟩, ?_⟩
  have : (χ g : ℍ[ℚ, a, b]) * (χ h : ℍ[ℚ, a, b]) - 1 = ((χ 1 : ℍ[ℚ, a, b]) - 1) - ((χ 1 : ℍ[ℚ, a, b]) - χ g * χ h) := by noncomm_ring
  rw [this, hy₀, hy₁, ← smul_sub]

section isoTransport
variable {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} {N : ℕ} {S : Type} [CommRing S]
  {E E' : FakeEllipticCurve Λ N S} (e : E.A ≅ E'.A) (he : e.hom ≫ E'.f = E.f)
  (hmul : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of S)) (P Q : SchemeHomOver t E.f),
    mapPt e.hom he (E.L.mul t P Q) = E'.L.mul t (mapPt e.hom he P) (mapPt e.hom he Q))
  (hact : ∀ x : ↥Λ, E.act x ≫ e.hom = e.hom ≫ E'.act x)

include he in
omit hmul hact in
theorem inv_over : e.inv ≫ E.f = E'.f := by rw [← he, Iso.inv_hom_id_assoc]

omit hmul hact in
theorem mapPt_inv_mapPt {T : Scheme.{0}} {t : T ⟶ Spec (CommRingCat.of S)} (Q : SchemeHomOver t E.f) :
    mapPt e.inv (inv_over e he) (mapPt e.hom he Q) = Q :=
  Subtype.ext (by simp only [mapPt_coe, Category.assoc, Iso.hom_inv_id, Category.comp_id])

omit hmul hact in
theorem mapPt_mapPt_inv {T : Scheme.{0}} {t : T ⟶ Spec (CommRingCat.of S)} (R : SchemeHomOver t E'.f) :
    mapPt e.hom he (mapPt e.inv (inv_over e he) R) = R :=
  Subtype.ext (by simp only [mapPt_coe, Category.assoc, Iso.inv_hom_id, Category.comp_id])

include hact in
omit hmul in
theorem mapPt_pushPt_act {T : Scheme.{0}} {t : T ⟶ Spec (CommRingCat.of S)} (x : ↥Λ) (Q : SchemeHomOver t E.f) :
    mapPt e.hom he (pushPt (E.act x) (E.act_over x) Q) = pushPt (E'.act x) (E'.act_over x) (mapPt e.hom he Q) :=
  Subtype.ext (by simp only [mapPt_coe, Category.assoc, hact x])

include hmul in
omit hact in
theorem mapPt_one {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of S)) : mapPt e.hom he (E.L.one t) = E'.L.one t := by
  have h := hmul t (E.L.one t) (E.L.one t)
  rw [E.L.one_mul] at h
  have := congrArg (E'.L.mul t (E'.L.inv t (mapPt e.hom he (E.L.one t)))) h
  rw [← E'.L.mul_assoc, E'.L.inv_mul_cancel, E'.L.one_mul] at this
  exact this.symm

include hmul in
omit hact in
theorem mapPt_nsmulPt {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of S)) (n : ℕ) (Q : SchemeHomOver t E.f) :
    mapPt e.hom he (nsmulPt E.L t n Q) = nsmulPt E'.L t n (mapPt e.hom he Q) := by
  induction n with
  | zero => exact mapPt_one e he hmul t
  | succ n ih =>
    show mapPt e.hom he (E.L.mul t (nsmulPt E.L t n Q) Q) = E'.L.mul t (nsmulPt E'.L t n (mapPt e.hom he Q)) _
    rw [hmul, ih]

omit hmul hact in
theorem mapPt_sectionAt (P : SchemeHomOver (𝟙 (Spec (CommRingCat.of S))) E.f) (k : Type) [Field k] (sk : S →+* k) :
    mapPt e.hom he (FakeEllipticCurve.sectionAt P k sk) = FakeEllipticCurve.sectionAt (mapPt e.hom he P) k sk :=
  Subtype.ext (by simp only [mapPt_coe, FakeEllipticCurve.sectionAt, GoodReductionJacobian.schemeHomOverComp_coe, Category.assoc])

end isoTransport

theorem eq_closedPoint (k : Type) [Field k] (y : ↥(Spec (CommRingCat.of k))) : y = IsLocalRing.closedPoint k :=
  Subsingleton.elim _ _

theorem mem_range_geomPoint {S : Type} [CommRing S] (y : ↥(Spec (CommRingCat.of S))) :
    y ∈ Set.range (geomPoint (AlgebraicClosure y.asIdeal.ResidueField)
      ((algebraMap y.asIdeal.ResidueField (AlgebraicClosure y.asIdeal.ResidueField)).comp (algebraMap S y.asIdeal.ResidueField))) := by
  refine ⟨⟨⊥, Ideal.isPrime_bot⟩, ?_⟩
  apply PrimeSpectrum.ext
  show Ideal.comap ((algebraMap y.asIdeal.ResidueField (AlgebraicClosure y.asIdeal.ResidueField)).comp
    (algebraMap S y.asIdeal.ResidueField)) ⊥ = y.asIdeal
  rw [← RingHom.ker_eq_comap_bot, RingHom.ker_comp_of_injective _
    (algebraMap y.asIdeal.ResidueField (AlgebraicClosure y.asIdeal.ResidueField)).injective,
    Ideal.ker_algebraMap_residueField]

end T3A

open T3A in
theorem solution
    {q q' : ℕ} [Fact q.Prime] [Fact q'.Prime] (hqq' : q' ≠ q)
    {a b : ℚ} (hB : IsIndefiniteRamifiedExactlyAt a b q q')
    (Λ : Submodule ℤ ℍ[ℚ, a, b]) (hΛ : IsMaximalOrder Λ) (N m : ℕ)
    {𝒪 : Type} [CommRing 𝒪] (hN : IsUnit ((N : ℕ) : 𝒪)) (hm' : IsUnit ((m : ℕ) : 𝒪))

    {M : Scheme.{0}} {πM : M ⟶ Spec (CommRingCat.of 𝒪)}
    {ptF : ∀ (S : Type) [CommRing S] (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of 𝒪)),
      FakeEllipticCurve.WithFullLevel Λ N m S → SchemeHomOver s πM}
    (hM : IsFineModuli Λ N m M πM ptF)
    {G : Type} [Group G] [Finite G] {ρ : G →* Aut M} {χ : G → ↥Λ}
    (hρ : IsLevelTwistAction Λ N m M πM ptF G ρ χ)

    {X : Scheme.{0}} {πX : X ⟶ Spec (CommRingCat.of 𝒪)} (π : M ⟶ X) (hπX : π ≫ πX = πM)
    {pt : ∀ (S : Type) [CommRing S] (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of 𝒪)),
      FakeEllipticCurve Λ N S → SchemeHomOver s πX}
    (hX : IsCoarseModuli Λ N X πX pt)
    (hpt : ∀ (S : Type) [CommRing S] (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of 𝒪))
      (u : FakeEllipticCurve.WithFullLevel Λ N m S), (pt S s u.1).1 = (ptF S s u).1 ≫ π)

    (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓm : ℓ ∣ m)
    (L₀ : Submodule ℤ ℍ[ℚ, a, b]) (hL₀ : L₀ ≤ Λ) (hℓL₀ : ∀ x : ↥Λ, (ℓ : ℚ) • (x : ℍ[ℚ, a, b]) ∈ L₀)
    (hL₀_left : ∀ (y : ↥Λ) (x : ℍ[ℚ, a, b]), x ∈ L₀ → (y : ℍ[ℚ, a, b]) * x ∈ L₀)
    (hL₀_index : L₀.toAddSubgroup.relIndex Λ.toAddSubgroup = ℓ ^ 2)
    (H : Subgroup G) (hH : ∀ g : G, g ∈ H ↔ ∀ x : ℍ[ℚ, a, b], x ∈ L₀ → x * (χ g : ℍ[ℚ, a, b]) ∈ L₀)

    (XH : Scheme.{0}) (πXH : XH ⟶ Spec (CommRingCat.of 𝒪)) (πH : M ⟶ XH) (hπHX : πH ≫ πXH = πM)
    (hπH : ∀ h : H, (ρ h).hom ≫ πH = πH)
    (hintH : IsIntegralHom πH) (haffH : IsAffineHom πH) (hsurjH : Function.Surjective πH.base)
    (horbitH : ∀ x x' : M, πH.base x = πH.base x' ↔ ∃ h : H, (ρ h).hom.base x = x')
    (hsecH : ∀ V : XH.Opens, Function.Injective (πH.app V))
    (hinvH : ∀ V : XH.Opens, Set.range (πH.app V) =
      {s | ∀ h : H, (ρ h).hom.appLE (πH ⁻¹ᵁ V) (πH ⁻¹ᵁ V) (by rw [← Scheme.Hom.comp_preimage, hπH h]) s = s})
    (hopenH : ∀ W : M.Opens, IsAffineOpen W → (∀ h : H, (ρ h).hom ⁻¹ᵁ W = W) → ∃ V : XH.Opens, IsAffineOpen V ∧ πH ⁻¹ᵁ V = W)
    (hcatH : ∀ (T : Scheme.{0}) (f : M ⟶ T), (∀ h : H, (ρ h).hom ≫ f = f) → ∃! f' : XH ⟶ T, πH ≫ f' = f)
    (d₀ : XH ⟶ X) (hd₀ : πH ≫ d₀ = π) :
    ∃ (U : XH.Opens)
      (ptT : ∀ (S : Type) [CommRing S] (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of 𝒪)),
        FakeEllipticCurve.WithExtraLevel Λ N ℓ S → SchemeHomOver s (U.ι ≫ πXH)),
      IsClosed (U : Set XH) ∧
      IsCoarseModuliT Λ N ℓ (U : Scheme.{0}) (U.ι ≫ πXH) ptT ∧

      (∀ (S : Type) [CommRing S] (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of 𝒪))
        (u : FakeEllipticCurve.WithFullLevel Λ N m S) (K : u.1.ExtraLevel ℓ),
        (∀ (k : Type) [Field k] [IsAlgClosed k] (sk : S →+* k) (Q : SchemeHomOver (geomPoint k sk) u.1.f),
          FactorsThrough K.levK Q ↔
            ∃ x : ↥Λ, (x : ℍ[ℚ, a, b]) ∈ L₀ ∧
              pushPt (u.1.act x) (u.1.act_over x)
                (nsmulPt u.1.L (geomPoint k sk) (m / ℓ) (FakeEllipticCurve.sectionAt u.2.P k sk)) = Q) →
        (ptT S s ⟨u.1, K⟩).1 ≫ U.ι = (ptF S s u).1 ≫ πH) ∧

      (∀ (S : Type) [CommRing S] (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of 𝒪))
        (v : FakeEllipticCurve.WithExtraLevel Λ N ℓ S), (ptT S s v).1 ≫ U.ι ≫ d₀ = (pt S s v.1).1) ∧

      (∀ (k' : Type) [Field k'] [IsAlgClosed k'] (sk : Spec (CommRingCat.of k') ⟶ Spec (CommRingCat.of 𝒪))
        (u : FakeEllipticCurve.WithFullLevel Λ N m k'),
        ((ptF k' sk u).1 ≫ πH).base (IsLocalRing.closedPoint k') ∈ (U : Set XH) ↔
          ∃ K : u.1.ExtraLevel ℓ,
            ∀ (k : Type) [Field k] [IsAlgClosed k] (sk' : k' →+* k) (Q : SchemeHomOver (geomPoint k sk') u.1.f),
              FactorsThrough K.levK Q ↔
                ∃ x : ↥Λ, (x : ℍ[ℚ, a, b]) ∈ L₀ ∧
                  pushPt (u.1.act x) (u.1.act_over x)
                    (nsmulPt u.1.L (geomPoint k sk') (m / ℓ) (FakeEllipticCurve.sectionAt u.2.P k sk')) = Q) ∧
      (¬ ℓ ∣ N → U = ⊤) := by
  classical
  have hord : IsOrder Λ := hΛ.isOrder

  obtain ⟨V, hVcl, hVchart, hVstab, hVtop⟩ :=
    CerednikDrinfeld.QM.IsFineModuli.exists_opens_isClosed_range_subset_iff_forall_factorsThrough_lev_imp hB Λ hΛ hN hm' hM hρ
      ℓ hℓ hℓm L₀ hL₀ hℓL₀ hL₀_left hL₀_index
  have hVH : ∀ h : H, (ρ (h : G)).hom ⁻¹ᵁ V = V := fun h => hVstab h ((hH h).1 h.2)

  obtain ⟨U, hUV, hUcl, hUimg, hUcat⟩ :=
    AlgebraicGeometry.Scheme.exists_opens_isClosed_preimage_eq_existsUnique_of_quotient (ρ.comp H.subtype) πH
      (fun h => hπH h) hintH hsurjH horbitH hcatH V hVcl hVH

  obtain ⟨ptT₀, hTiso, hTpb, hTcompat⟩ :=
    CerednikDrinfeld.QM.exists_ptT_eq_ptF_comp_of_isFineModuli_of_forall_ptF_comp_eq Λ N m ℓ L₀ hm' M πM ptF hM XH πXH πH hπHX
      (fun S _ s E K P P' hP hP' =>
        CerednikDrinfeld.QM.IsLevelTwistAction.ptF_comp_eq_ptF_comp_of_forall_factorsThrough_levK_iff hord hm' hM hρ ℓ hℓ hℓm
          L₀ hL₀ hℓL₀ H (fun g hg => (hH g).2 hg) πH hπH S s E K P P' hP hP')
      (fun S _ u hmS =>
        CerednikDrinfeld.QM.FakeEllipticCurve.WithExtraLevel.exists_flat_surjective_withFullLevel_forall_factorsThrough_iff hqq' hB Λ hΛ
          m ℓ hℓ hℓm L₀ hL₀ hℓL₀ hL₀_left hL₀_index S hmS u)

  have hland : ∀ (S : Type) [CommRing S] (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of 𝒪))
      (u : FakeEllipticCurve.WithExtraLevel Λ N ℓ S), Set.range (ptT₀ S s u).1 ⊆ (U : Set ↥XH) := by
    intro S _ s u
    rintro _ ⟨y, rfl⟩
    let κ₀ := y.asIdeal.ResidueField
    let k := AlgebraicClosure κ₀
    let sk : S →+* k := (algebraMap κ₀ k).comp (algebraMap S κ₀)
    obtain ⟨pt0, hpt0⟩ := mem_range_geomPoint y
    obtain ⟨⟨Ek, Kk⟩, huk⟩ := CerednikDrinfeld.QM.FakeEllipticCurve.WithExtraLevel.exists_isPullback sk u
    have hmk : ((m : ℕ) : k) ≠ 0 := by
      have h := (isUnit_natCast_of_specHom m hm' s).map sk
      rw [map_natCast] at h
      exact h.ne_zero
    obtain ⟨P, hP⟩ := CerednikDrinfeld.QM.FakeEllipticCurve.ExtraLevel.exists_fullLevel_forall_factorsThrough_iff hqq' hB Λ hΛ m ℓ hℓ hℓm
      L₀ hL₀ hℓL₀ hL₀_left hL₀_index k hmk Ek Kk
    have e1 := hTpb S k sk s (geomPoint k sk ≫ s) rfl u ⟨Ek, Kk⟩ huk
    have e2 := hTcompat k (geomPoint k sk ≫ s) ⟨Ek, P⟩ Kk hP
    have hV' : Set.range (ptF k (geomPoint k sk ≫ s) ⟨Ek, P⟩).1 ⊆ (V : Set ↥M) :=
      (hVchart k (geomPoint k sk ≫ s) ⟨Ek, P⟩).2 (disj_of_gen L₀ Ek P Kk hP)
    have h3 : (ptF k (geomPoint k sk ≫ s) ⟨Ek, P⟩).1.base pt0 ∈ (πH ⁻¹ᵁ U : Set ↥M) := by
      rw [hUV]; exact hV' ⟨pt0, rfl⟩
    have h4 : ((ptF k (geomPoint k sk ≫ s) ⟨Ek, P⟩).1 ≫ πH).base pt0 ∈ (U : Set ↥XH) := h3
    rw [← e2, e1] at h4
    rw [← hpt0]
    exact h4
  have hland' : ∀ (S : Type) [CommRing S] (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of 𝒪))
      (u : FakeEllipticCurve.WithExtraLevel Λ N ℓ S), Set.range (ptT₀ S s u).1 ⊆ Set.range U.ι := by
    intro S _ s u; rw [Scheme.Opens.range_ι]; exact hland S s u
  let ptT : ∀ (S : Type) [CommRing S] (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of 𝒪)),
      FakeEllipticCurve.WithExtraLevel Λ N ℓ S → SchemeHomOver s (U.ι ≫ πXH) := fun S _ s u =>
    ⟨IsOpenImmersion.lift U.ι (ptT₀ S s u).1 (hland' S s u), by
      rw [← Category.assoc, IsOpenImmersion.lift_fac]; exact (ptT₀ S s u).2⟩
  have hptTι : ∀ (S : Type) [CommRing S] (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of 𝒪))
      (u : FakeEllipticCurve.WithExtraLevel Λ N ℓ S), (ptT S s u).1 ≫ U.ι = (ptT₀ S s u).1 :=
    fun S _ s u => IsOpenImmersion.lift_fac _ _ _
  have hTpbU : ∀ (S S' : Type) [CommRing S] [CommRing S'] (φ : S →+* S')
      (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of 𝒪)) (s' : Spec (CommRingCat.of S') ⟶ Spec (CommRingCat.of 𝒪)),
      Spec.map (CommRingCat.ofHom φ) ≫ s = s' →
      ∀ (u : FakeEllipticCurve.WithExtraLevel Λ N ℓ S) (u' : FakeEllipticCurve.WithExtraLevel Λ N ℓ S'),
        FakeEllipticCurve.WithExtraLevel.IsPullback φ u u' → (ptT S' s' u').1 = Spec.map (CommRingCat.ofHom φ) ≫ (ptT S s u).1 := by
    intro S S' _ _ φ s s' hss' u u' huu'
    rw [← cancel_mono U.ι, Category.assoc, hptTι, hptTι]
    exact hTpb S S' φ s s' hss' u u' huu'
  refine ⟨U, ptT, hUcl, ⟨?_, ?_, ?_, ?_, ?_⟩, ?_, ?_, ?_, ?_⟩
  ·
    intro S _ s u u' huu'
    apply Subtype.ext
    rw [← cancel_mono U.ι, hptTι, hptTι, hTiso S s u u' huu']
  ·
    exact hTpbU
  ·
    intro k _ _ s y
    haveI := hintH
    obtain ⟨x, hx⟩ :=
      AlgebraicGeometry.exists_comp_eq_of_isIntegralHom_of_surjective_of_isAlgClosed πH hsurjH k (y.1 ≫ U.ι)
    have hxs : x ≫ πM = s := by
      rw [← hπHX, ← Category.assoc, hx, Category.assoc]; exact y.2
    obtain ⟨w, hw⟩ := hM.ptF_surjective k s ⟨x, hxs⟩
    have hw1 : (ptF k s w).1 = x := by rw [hw]
    have hmk : IsUnit ((m : ℕ) : k) := isUnit_natCast_of_specHom m hm' s
    have hV' : Set.range (ptF k s w).1 ⊆ (V : Set ↥M) := by
      rintro _ ⟨z, rfl⟩
      rw [hw1, ← hUV]
      show (x ≫ πH).base z ∈ (U : Set ↥XH)
      rw [hx, comp_base_apply]
      exact ι_base_mem U _
    obtain ⟨K, hK⟩ := CerednikDrinfeld.QM.FakeEllipticCurve.FullLevel.exists_extraLevel_forall_factorsThrough_iff hB Λ hΛ m ℓ hℓ hℓm
      L₀ hL₀ hℓL₀ hL₀_left hL₀_index hmk w.1 w.2 ((hVchart k s w).1 hV')
    refine ⟨⟨w.1, K⟩, Subtype.ext ?_⟩
    rw [← cancel_mono U.ι, hptTι, hTcompat k s w K hK, hw1, hx]
  ·
    intro k _ _ s u u' huu'
    have hmk : IsUnit ((m : ℕ) : k) := isUnit_natCast_of_specHom m hm' s
    have hmk' : ((m : ℕ) : k) ≠ 0 := hmk.ne_zero
    have hℓk : IsUnit ((ℓ : ℕ) : k) := by
      obtain ⟨c, hc⟩ := hℓm
      exact isUnit_of_mul_isUnit_left (by rw [← Nat.cast_mul, ← hc]; exact hmk)
    obtain ⟨E, K⟩ := u
    obtain ⟨E', K'⟩ := u'
    obtain ⟨P, hP⟩ := CerednikDrinfeld.QM.FakeEllipticCurve.ExtraLevel.exists_fullLevel_forall_factorsThrough_iff hqq' hB Λ hΛ m ℓ hℓ hℓm
      L₀ hL₀ hℓL₀ hL₀_left hL₀_index k hmk' E K
    obtain ⟨P', hP'⟩ := CerednikDrinfeld.QM.FakeEllipticCurve.ExtraLevel.exists_fullLevel_forall_factorsThrough_iff hqq' hB Λ hΛ m ℓ hℓ hℓm
      L₀ hL₀ hℓL₀ hL₀_left hL₀_index k hmk' E' K'
    have hππ : (ptF k s ⟨E, P⟩).1 ≫ πH = (ptF k s ⟨E', P'⟩).1 ≫ πH := by
      rw [← hTcompat k s ⟨E, P⟩ K hP, ← hTcompat k s ⟨E', P'⟩ K' hP', ← hptTι, ← hptTι]
      exact congrArg (fun z => z.1 ≫ U.ι) huu'
    obtain ⟨h, hh⟩ := CerednikDrinfeld.QM.exists_eq_comp_autHom_of_comp_eq_of_isAlgClosed (ρ.comp H.subtype) πH
      (fun h => hπH h) haffH hsecH hinvH k _ _ hππ

    have hcd := label_inv hρ (h : G) (h : G)⁻¹ (mul_inv_cancel _)
    have hdc := label_inv hρ (h : G)⁻¹ (h : G) (inv_mul_cancel _)
    have hmemH : ∀ x : ℍ[ℚ, a, b], x ∈ L₀ → x * (χ (h : G) : ℍ[ℚ, a, b]) ∈ L₀ := (hH (h : G)).1 h.2
    have hmemH' : ∀ x : ℍ[ℚ, a, b], x ∈ L₀ → x * (χ (h : G)⁻¹ : ℍ[ℚ, a, b]) ∈ L₀ := (hH _).1 (H.inv_mem h.2)
    obtain ⟨P₂, hP₂P, hP₂⟩ :=
      CerednikDrinfeld.QM.FakeEllipticCurve.FullLevel.exists_forall_factorsThrough_iff_of_mul_mem hord E P ℓ hℓm K L₀ L₀ hL₀ hL₀ hP
        (χ (h : G)) (χ (h : G)⁻¹) hcd hdc hmemH hmemH'
    have htw : FakeEllipticCurve.WithFullLevel.IsTwist (χ (h : G)) (⟨E, P⟩ : FakeEllipticCurve.WithFullLevel Λ N m k) ⟨E, P₂⟩ := by
      refine ⟨Iso.refl E.A, Category.id_comp E.f, ?_, ?_, ?_, ?_⟩
      · intro T t X Y
        have : ∀ Z : SchemeHomOver t E.f, mapPt (Iso.refl E.A).hom (Category.id_comp E.f) Z = Z :=
          fun Z => Subtype.ext (by simp only [mapPt_coe, Iso.refl_hom, Category.comp_id])
        rw [this, this, this]
      · intro y; simp only [Iso.refl_hom, Category.comp_id, Category.id_comp]
      · intro T t X
        have : mapPt (Iso.refl E.A).hom (Category.id_comp E.f) X = X :=
          Subtype.ext (by simp only [mapPt_coe, Iso.refl_hom, Category.comp_id])
        rw [this]
      · rw [hP₂P]
        exact Subtype.ext (by simp only [mapPt_coe, Iso.refl_hom, Category.comp_id])
    have htwist := hρ.twist (h : G) k s ⟨E, P⟩ ⟨E, P₂⟩ htw
    have heq : ptF k s ⟨E, P₂⟩ = ptF k s ⟨E', P'⟩ := Subtype.ext (by rw [htwist]; exact hh.symm)
    obtain ⟨e, he, hmul, hact, hlev, heP⟩ := hM.ptF_injective k s ⟨E, P₂⟩ ⟨E', P'⟩ heq
    obtain ⟨K₁, hK₁⟩ :=
      CerednikDrinfeld.QM.FakeEllipticCurve.exists_extraLevel_forall_factorsThrough_mapPt_iff ℓ E E' e he hmul hact hlev K
    have hK₁K' : ∀ (k'' : Type) [Field k''] [IsAlgClosed k''] (sk' : k →+* k'') (R : SchemeHomOver (geomPoint k'' sk') E'.f),
        FactorsThrough K₁.levK R ↔ FactorsThrough K'.levK R := by
      intro k'' _ _ sk' R
      rw [hP' k'' sk' R, ← mapPt_mapPt_inv e he R, hK₁, hP₂ k'' sk']
      constructor
      · rintro ⟨x, hx, hxe⟩
        refine ⟨x, hx, ?_⟩
        rw [← hxe, mapPt_pushPt_act e he hact, mapPt_nsmulPt e he hmul, mapPt_sectionAt e he]
        show _ = pushPt (E'.act x) (E'.act_over x) (nsmulPt E'.L _ (m / ℓ) (FakeEllipticCurve.sectionAt (mapPt e.hom he P₂.P) k'' sk'))
        rw [heP]
      · rintro ⟨x, hx, hxe⟩
        rw [mapPt_mapPt_inv e he] at hxe
        refine ⟨x, hx, ?_⟩
        apply_fun mapPt e.hom he
        · rw [mapPt_mapPt_inv e he, mapPt_pushPt_act e he hact, mapPt_nsmulPt e he hmul, mapPt_sectionAt e he]
          show pushPt (E'.act x) (E'.act_over x) (nsmulPt E'.L _ (m / ℓ) (FakeEllipticCurve.sectionAt (mapPt e.hom he P₂.P) k'' sk')) = _
          rw [heP]
          exact hxe
        · intro X Y hXY
          have := congrArg (mapPt e.inv (inv_over e he)) hXY
          rwa [mapPt_inv_mapPt e he, mapPt_inv_mapPt e he] at this
    refine ⟨e, he, hmul, hact, hlev, ?_⟩
    intro T t Q
    rw [← hK₁ t Q]
    exact CerednikDrinfeld.QM.FakeEllipticCurve.ExtraLevel.factorsThrough_iff_of_forall_geomPoint ℓ hℓ hℓk E' K₁ K' hK₁K' t _
  ·
    intro T πT pt' hiso' hpb'
    obtain ⟨Φ, ⟨hΦT, hΦ⟩, hΦuniq⟩ :=
      CerednikDrinfeld.QM.IsFineModuli.existsUnique_hom_ptT_comp_eq hB Λ hΛ hm' hM ℓ hℓ hℓm L₀ hL₀ hℓL₀ hL₀_left hL₀_index
        V (fun S _ s w => hVchart S s w) T πT pt' hiso' hpb'

    have hliftU : ∀ (S : Type) [CommRing S] (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of 𝒪))
        (w : FakeEllipticCurve.WithFullLevel Λ N m S) (K : w.1.ExtraLevel ℓ) (x : Spec (CommRingCat.of S) ⟶ (V : Scheme.{0})),
        x ≫ V.ι = (ptF S s w).1 →
        (∀ (k : Type) [Field k] [IsAlgClosed k] (sk : S →+* k) (Q : SchemeHomOver (geomPoint k sk) w.1.f),
        FactorsThrough K.levK Q ↔
          ∃ x : ↥Λ, (x : ℍ[ℚ, a, b]) ∈ L₀ ∧
            pushPt (w.1.act x) (w.1.act_over x)
              (nsmulPt w.1.L (geomPoint k sk) (m / ℓ) (FakeEllipticCurve.sectionAt w.2.P k sk)) = Q) →
        (ptT S s ⟨w.1, K⟩).1 = x ≫ πH.resLE U V (by rw [hUV]) := by
      intro S _ s w K x hx hGen
      rw [← cancel_mono U.ι, hptTι, hTcompat S s w K hGen, Category.assoc, Scheme.Hom.resLE_comp_ι, ← Category.assoc, hx]

    have hΦinv : ∀ h : H, ((ρ.comp H.subtype) h).hom.resLE V V (le_of_eq (hVH h).symm) ≫ Φ = Φ := by
      intro h
      apply hΦuniq
      refine ⟨?_, ?_⟩
      · rw [Category.assoc, hΦT, ← Category.assoc, Scheme.Hom.resLE_comp_ι, Category.assoc]
        show V.ι ≫ (ρ (h : G)).hom ≫ πM = V.ι ≫ πM
        rw [hρ.over_base]
      · intro S _ s w K x hx hGen
        have hcd := label_inv hρ (h : G) (h : G)⁻¹ (mul_inv_cancel _)
        have hdc := label_inv hρ (h : G)⁻¹ (h : G) (inv_mul_cancel _)
        have hmemH : ∀ y : ℍ[ℚ, a, b], y ∈ L₀ → y * (χ (h : G) : ℍ[ℚ, a, b]) ∈ L₀ := (hH (h : G)).1 h.2
        have hmemH' : ∀ y : ℍ[ℚ, a, b], y ∈ L₀ → y * (χ (h : G)⁻¹ : ℍ[ℚ, a, b]) ∈ L₀ := (hH _).1 (H.inv_mem h.2)
        obtain ⟨P₂, hP₂P, hP₂⟩ :=
          CerednikDrinfeld.QM.FakeEllipticCurve.FullLevel.exists_forall_factorsThrough_iff_of_mul_mem hord w.1 w.2 ℓ hℓm K L₀ L₀ hL₀ hL₀
            hGen (χ (h : G)) (χ (h : G)⁻¹) hcd hdc hmemH hmemH'
        have htw : FakeEllipticCurve.WithFullLevel.IsTwist (χ (h : G)) w ⟨w.1, P₂⟩ := by
          refine ⟨Iso.refl w.1.A, Category.id_comp w.1.f, ?_, ?_, ?_, ?_⟩
          · intro T' t X Y
            have : ∀ Z : SchemeHomOver t w.1.f, mapPt (Iso.refl w.1.A).hom (Category.id_comp w.1.f) Z = Z :=
              fun Z => Subtype.ext (by simp only [mapPt_coe, Iso.refl_hom, Category.comp_id])
            rw [this, this, this]
          · intro y; simp only [Iso.refl_hom, Category.comp_id, Category.id_comp]
          · intro T' t X
            have : mapPt (Iso.refl w.1.A).hom (Category.id_comp w.1.f) X = X :=
              Subtype.ext (by simp only [mapPt_coe, Iso.refl_hom, Category.comp_id])
            rw [this]
          · rw [hP₂P]
            exact Subtype.ext (by simp only [mapPt_coe, Iso.refl_hom, Category.comp_id])
        have htwist := hρ.twist (h : G) S s w ⟨w.1, P₂⟩ htw
        have hx' : (x ≫ ((ρ.comp H.subtype) h).hom.resLE V V (le_of_eq (hVH h).symm)) ≫ V.ι = (ptF S s ⟨w.1, P₂⟩).1 := by
          rw [Category.assoc, Scheme.Hom.resLE_comp_ι, ← Category.assoc, hx]
          exact htwist.symm
        have := hΦ S s ⟨w.1, P₂⟩ K _ hx' hP₂
        rw [Category.assoc] at this
        exact this
    obtain ⟨f', hf', hf'uniq⟩ := hUcat T Φ hΦinv
    refine ⟨f', ⟨?_, ?_⟩, ?_⟩
    ·
      obtain ⟨b₀, hb₀, hb₀uniq⟩ := hUcat (Spec (CommRingCat.of 𝒪)) (V.ι ≫ πM) (fun h => by
        rw [← Category.assoc, Scheme.Hom.resLE_comp_ι, Category.assoc]
        show V.ι ≫ (ρ (h : G)).hom ≫ πM = V.ι ≫ πM
        rw [hρ.over_base])
      have e1 : f' ≫ πT = b₀ := hb₀uniq _ (by show πH.resLE U V _ ≫ f' ≫ πT = V.ι ≫ πM; rw [← Category.assoc, hf', hΦT])
      have e2 : U.ι ≫ πXH = b₀ := hb₀uniq _ (by show πH.resLE U V _ ≫ U.ι ≫ πXH = V.ι ≫ πM; rw [← Category.assoc, Scheme.Hom.resLE_comp_ι, Category.assoc, hπHX])
      rw [e1, ← e2]
    ·
      intro S _ s v
      have hmS : IsUnit ((m : ℕ) : S) := isUnit_natCast_of_specHom m hm' s
      obtain ⟨S', instS', φ, hflat, hsurjφ, w', K', hPB, hGen⟩ :=
        CerednikDrinfeld.QM.FakeEllipticCurve.WithExtraLevel.exists_flat_surjective_withFullLevel_forall_factorsThrough_iff hqq' hB Λ hΛ
          m ℓ hℓ hℓm L₀ hL₀ hℓL₀ hL₀_left hL₀_index S hmS v
      haveI := hflat; haveI := hsurjφ
      haveI : Epi (Spec.map (CommRingCat.ofHom φ)) := Flat.epi_of_flat_of_surjective _
      rw [← cancel_epi (Spec.map (CommRingCat.ofHom φ))]
      have l1 := hpb' S S' φ s _ rfl v ⟨w'.1, K'⟩ hPB
      have l2 := hTpbU S S' φ s _ rfl v ⟨w'.1, K'⟩ hPB
      have hV' : Set.range (ptF S' (Spec.map (CommRingCat.ofHom φ) ≫ s) w').1 ⊆ Set.range V.ι := by
        rw [Scheme.Opens.range_ι]
        exact (hVchart S' _ w').2 (disj_of_gen L₀ w'.1 w'.2 K' hGen)
      have hx' : IsOpenImmersion.lift V.ι _ hV' ≫ V.ι = (ptF S' _ w').1 := IsOpenImmersion.lift_fac _ _ _
      have l3 := hΦ S' _ w' K' _ hx' hGen
      have l4 := hliftU S' _ w' K' _ hx' hGen
      calc Spec.map (CommRingCat.ofHom φ) ≫ (pt' S s v).1
          = (pt' S' _ ⟨w'.1, K'⟩).1 := l1.symm
        _ = IsOpenImmersion.lift V.ι _ hV' ≫ Φ := l3
        _ = (IsOpenImmersion.lift V.ι _ hV' ≫ πH.resLE U V (by rw [hUV])) ≫ f' := by rw [Category.assoc, hf']
        _ = (ptT S' _ ⟨w'.1, K'⟩).1 ≫ f' := by rw [← l4]
        _ = Spec.map (CommRingCat.ofHom φ) ≫ (ptT S s v).1 ≫ f' := by rw [l2, Category.assoc]
    ·
      rintro f'' ⟨hf''T, hf''pt⟩
      apply hf'uniq
      apply hΦuniq
      refine ⟨?_, ?_⟩
      · rw [Category.assoc, hf''T, ← Category.assoc, Scheme.Hom.resLE_comp_ι, Category.assoc, hπHX]
      · intro S _ s w K x hx hGen
        rw [hf''pt S s ⟨w.1, K⟩, hliftU S s w K x hx hGen, Category.assoc]
  ·
    intro S _ s u K hK
    rw [hptTι]
    exact hTcompat S s u K hK
  ·
    intro S _ s v
    have hmS : IsUnit ((m : ℕ) : S) := isUnit_natCast_of_specHom m hm' s
    obtain ⟨S', instS', φ, hflat, hsurjφ, w', K', hPB, hGen⟩ :=
      CerednikDrinfeld.QM.FakeEllipticCurve.WithExtraLevel.exists_flat_surjective_withFullLevel_forall_factorsThrough_iff hqq' hB Λ hΛ
        m ℓ hℓ hℓm L₀ hL₀ hℓL₀ hL₀_left hL₀_index S hmS v
    haveI := hflat; haveI := hsurjφ
    haveI : Epi (Spec.map (CommRingCat.ofHom φ)) := Flat.epi_of_flat_of_surjective _
    rw [← cancel_epi (Spec.map (CommRingCat.ofHom φ))]
    have l1 := hTpb S S' φ s (Spec.map (CommRingCat.ofHom φ) ≫ s) rfl v ⟨w'.1, K'⟩ hPB
    have l2 := hX.pt_pullback S S' φ s _ rfl v.1 w'.1 (isPullback_fst_of_withExtraLevel_isPullback φ v ⟨w'.1, K'⟩ hPB)
    have l3 := hTcompat S' (Spec.map (CommRingCat.ofHom φ) ≫ s) w' K' hGen
    calc Spec.map (CommRingCat.ofHom φ) ≫ ((ptT S s v).1 ≫ U.ι ≫ d₀)
        = (Spec.map (CommRingCat.ofHom φ) ≫ (ptT₀ S s v).1) ≫ d₀ := by
          rw [← hptTι S s v]; simp only [Category.assoc]
      _ = (ptT₀ S' _ ⟨w'.1, K'⟩).1 ≫ d₀ := by rw [l1]
      _ = (ptF S' _ w').1 ≫ πH ≫ d₀ := by rw [l3, Category.assoc]
      _ = (ptF S' _ w').1 ≫ π := by rw [hd₀]
      _ = (pt S' _ w'.1).1 := (hpt S' _ w').symm
      _ = Spec.map (CommRingCat.ofHom φ) ≫ (pt S s v.1).1 := l2
  ·
    intro k' _ _ sk u
    have hmk : IsUnit ((m : ℕ) : k') := isUnit_natCast_of_specHom m hm' sk
    constructor
    · intro hmem
      have hV' : Set.range (ptF k' sk u).1 ⊆ (V : Set ↥M) := by
        rintro _ ⟨y, rfl⟩
        rw [eq_closedPoint k' y, ← hUV]
        exact hmem
      obtain ⟨K, hK⟩ := CerednikDrinfeld.QM.FakeEllipticCurve.FullLevel.exists_extraLevel_forall_factorsThrough_iff hB Λ hΛ m ℓ hℓ hℓm
        L₀ hL₀ hℓL₀ hL₀_left hL₀_index hmk u.1 u.2 ((hVchart k' sk u).1 hV')
      exact ⟨K, hK⟩
    · rintro ⟨K, hK⟩
      have hV' := (hVchart k' sk u).2 (disj_of_gen L₀ u.1 u.2 K hK)
      have : (ptF k' sk u).1.base (IsLocalRing.closedPoint k') ∈ (πH ⁻¹ᵁ U : Set ↥M) := by
        rw [hUV]; exact hV' ⟨_, rfl⟩
      exact this
  ·
    intro hℓN
    have hV : V = ⊤ := hVtop hℓN
    apply TopologicalSpace.Opens.ext
    apply Set.eq_univ_of_forall
    intro x
    obtain ⟨y, rfl⟩ := hsurjH x
    have : y ∈ (πH ⁻¹ᵁ U : Set ↥M) := by rw [hUV, hV]; trivial
    exact this

end

end S_CerednikDrinfeld_QM_IsFineModuli_exists_isCoarseModuliT_of_quotient_of_isIndefiniteRamifiedExactlyAt_of_isUnit_mem_iff
end P2MW
export P2MW.S_CerednikDrinfeld_QM_IsFineModuli_exists_isCoarseModuliT_of_quotient_of_isIndefiniteRamifiedExactlyAt_of_isUnit_mem_iff (solution)
