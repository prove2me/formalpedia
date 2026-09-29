-- Prove2me | solution 1 for CerednikDrinfeld.mumfordEmbedding_readoff_of_functionField_equiv_of_ringHom_zero_one_of_two_mul_dvd
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.491319+00:00
-- url     : https://prove2.me/submissions/3215ab20-7460-5343-adf5-230586cd75b3

import Definitions.Def_CerednikDrinfeld_ShimuraCurve
import Definitions.Def_CerednikDrinfeld_HeckeTower
import Definitions.Def_CerednikDrinfeld_ClassSetGraph
import Definitions.Def_CerednikDrinfeld_MumfordQuotient
import Definitions.Def_CerednikDrinfeld_DrinfeldHolomorphic
import Definitions.Def_ValuationSubring_CompletionRatClosure
import Definitions.Def_ValuationSubring_CompletionDecompositionAction
import Definitions.Def_CerednikDrinfeld_CosetGraphAtPrime
import Definitions.Def_Submodule_LocalBox
import Definitions.Def_CerednikDrinfeld_DescentIntertwining_v2
import Definitions.Def_CerednikDrinfeld_DescentIntertwiningBase
import Definitions.Def_CerednikDrinfeld_QMModuli
import Definitions.Def_CerednikDrinfeld_QMModuliProps
import Definitions.Def_CerednikDrinfeld_QMModuliTower
import Definitions.Def_CerednikDrinfeld_QMModuliTowerD
import Definitions.Def_CerednikDrinfeld_QMCoarseModuli
import Definitions.Def_CerednikDrinfeld_FormalUpperHalfPlaneFunctor
import Definitions.Def_CerednikDrinfeld_SchemeNilpPoints
import Theorems.Thm_CerednikDrinfeld_exists_smul_psi_eq_psi_frobenius_pow_iff_parity_of_decompositionSubgroup
import Theorems.Thm_CerednikDrinfeld_QM_IsCoarseModuli_base_genericPoint_eq_of_comp_fst_eq_fst_comp_of_isAtkinLehnerQuotient_of_not_dvd
import Theorems.Thm_CerednikDrinfeld_QM_IsCoarseModuliT_base_genericPoint_eq_of_comp_fst_eq_fst_comp_degeneracy
import Theorems.Thm_CerednikDrinfeld_CosetGraph_atkinLehner_relations_levelGroups_place
import Theorems.Thm_CerednikDrinfeld_vdet_unitsMap_eq_padicValRat_nrd
import Theorems.Thm_ValuationSubring_isAlgClosed_completion_of_liesOverPrime
import Theorems.Thm_CerednikDrinfeld_FormalOmega_OmegaNr_isTwistedAct_laws
import Theorems.Thm_AlgebraicGeometry_base_genericPoint_eq_genericPoint_of_subset_range
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_mumfordEmbedding_readoff_of_functionField_equiv_of_ringHom_zero_one_of_two_mul_dvd
p2m_attr_erase "instance" "instTopologicallyFGOfFiniteType GoodReductionJacobian.RelativeGroupLaw.isIso_endKerStr_schemeHomOverId AlgebraicGeometry.Scheme.PresheafOfModules.symmetricCategory SheafOfModules.instFaithfulRingSheafPModToPMod SheafOfModules.symmetricCategory AlgebraicGeometry.Scheme.PresheafOfModules.monoidalCategory AlgebraicGeometry.Scheme.PresheafOfModules.monoidalClosed SheafOfModules.instFullRingSheafPModToPMod SheafOfModules.monoidalCategory AlgebraicGeometry.Scheme.Modules.symmetricCategory SheafOfModules.monoidalClosed SheafOfModules.instIsLocalizationPModRingSheafSheafifyFunctorPresheafW SheafOfModules.sheafifyFunctor_monoidal AlgebraicGeometry.Scheme.Modules.monoidalClosed AlgebraicGeometry.instMonoidalPresheafOfModulesModulesSheafify AlgebraicGeometry.Scheme.Modules.monoidalCategory PresheafOfModules.instMonoidalClosed PresheafOfModules.InternalHom.instModuleCarrierObjOppositeCommRingCatSubtypePiFamilyMemAddSubgroupNaturalFamilies PresheafOfModules.InternalHom.instModuleCarrierObjOppositeRingCatCompCommRingCatForget₂RingHomCarrierCarrierAbPresheaf PresheafOfModules.InternalHom.instSMulCarrierObjOppositeCommRingCatSubtypePiFamilyMemAddSubgroupNaturalFamilies AlgebraicGeometry.Scheme.Hom.opensMapFinal AlgebraicGeometry.RelPicard.RigidifiedLineBundle.setoid AlgebraicGeometry.RelPicard.RigidifiedLineBundle.instInhabited AlgebraicGeometry.OModulePresheaf.isScalarTower AlgebraicGeometry.Scheme.OrderedAffineCover.instLinearOrder AlgebraicGeometry.OModulePresheaf.module AlgebraicGeometry.Scheme.OrderedAffineCover.instFintype AlgebraicGeometry.Scheme.OrderedAffineCover.instFintypeIdx AlgebraicGeometry.OModulePresheaf.addCommGroup AlgebraicGeometry.Scheme.OrderedAffineCover.instDecidableEqIdx AlgebraicGeometry.OModulePresheaf.moduleSections TwoChartCech.Sections.M0_moduleA TwoChartCech.Sections.M1_module TwoChartCech.Cover.A01_algebra TwoChartCech.Cover.A0_algebra TwoChartCech.Cover.A1_commRing TwoChartCech.Cover.A1_algebra TwoChartCech.Sections.M01_module TwoChartCech.Sections.M0_addCommGroup TwoChartCech.Sections.M0_tower"
p2m_attr_erase "instance" "TwoChartCech.Sections.M01_addCommGroup TwoChartCech.Cover.A0_commRing TwoChartCech.Sections.M1_tower TwoChartCech.Sections.M01_moduleA TwoChartCech.Sections.M0_module TwoChartCech.Sections.M1_moduleA TwoChartCech.Sections.M1_addCommGroup TwoChartCech.Cover.A01_commRing TwoChartCech.Sections.M01_tower CoherentBaseChange.TwoTermComplex.C0_module CoherentBaseChange.TwoTermComplex.C0_addCommGroup CoherentBaseChange.TwoTermComplex.C1_module CoherentBaseChange.TwoTermComplex.C1_addCommGroup CoherentBaseChange.TwoTermComplex.C0_free CoherentBaseChange.TwoTermComplex.C1_finite CoherentBaseChange.TwoTermComplex.C0_finite CoherentBaseChange.TwoTermComplex.C1_free AlgebraicGeometry.OModulePresheaf.instSubsingletonObjZero AlgebraicGeometry.Scheme.Modules.preservesBinaryProducts_opensMap AlgebraicGeometry.Scheme.Modules.pullback_monoidal AlgebraicGeometry.Scheme.Modules.sheafify_isLocalization' AlgebraicGeometry.Scheme.Modules.preservesTerminal_opensMap AlgebraicGeometry.Scheme.Modules.pullback₀_monoidal AlgebraicGeometry.Scheme.Modules.preservesFiniteProducts_opensMap AlgebraicGeometry.Scheme.Modules.instLiftingPresheafOfModulesSheafifyPresheafWOpensCarrierCarrierCommRingCatGrothendieckTopologyObjFunctorOppositeIsSheafSheafCompPullback₀Pullback PresheafOfModules.PullbackMonoidal.pullback_monoidal PresheafOfModules.PullbackMonoidal.isIso_δ PresheafOfModules.pushforward_laxMonoidal PresheafOfModules.PullbackMonoidal.isIso_η PresheafOfModules.free_monoidal PresheafOfModules.restrictScalars_laxMonoidal PresheafOfModules.PullbackMonoidal.isIso_δ_gS PresheafOfModules.pullback_oplaxMonoidal PresheafOfModules.PullbackMonoidal.instPreservesColimitsOfSizeCompOppositeCommRingCatRingCatForget₂RingHomCarrierCarrierPb PresheafOfModules.pullback_monoidal' AlgebraicGeometry.SmoothOfRelativeDimension.fiberToSpecResidueField AlgebraicGeometry.SmoothOfRelativeDimension.pullback_snd AlgebraicGeometry.SmoothOfRelativeDimension.pullback_fst AlgebraicGeometry.SmoothOfRelativeDimension.smooth_one AlgebraicGeometry.SmoothProperCurve.isIntegral_pullback_Spec_field"
p2m_attr_erase "instance" "AlgebraicGeometry.IsProper.fiberToSpecResidueField AlgebraicGeometry.Scheme.LocalRepresentabilityULift.instIsLocallyInjectiveFunUliftYonedaGluedToSheaf AlgebraicGeometry.Scheme.LocalRepresentabilityULift.instIsLocallySurjectiveFunUliftYonedaGluedToSheafOfIsLocallySurjectiveZariskiTopologyDescFunctorOppositeType AlgebraicGeometry.Scheme.LocalRepresentabilityULift.instIsOpenImmersionToGlued AlgebraicGeometry.Scheme.LocalRepresentabilityULift.instIsIsoSheafZariskiTopologyTypeUliftYonedaGluedToSheaf AlgebraicGeometry.RelPicard.instIsOpenImmersionToGlued AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions PresheafOfModules.ExteriorPower.instModulePresheafAb AlgebraicGeometry.RelEffCartierDiv.subsingleton_of_degree_zero AlgebraicGeometry.RelEffCartierDiv.isIso_subschemeIota_snd_of_degree_one AlgebraicGeometry.isIso_ker_graphOver_subschemeIota_snd AlgebraicGeometry.isClosedImmersion_graphOver AlgebraicGeometry.FGSubalgebra.instIsDirectedLe AlgebraicGeometry.FGSubalgebra.instQuasiSeparatedSpaceCarrierCarrierCommRingCatObjOppositeSchemeSpecDiagram AlgebraicGeometry.FGSubalgebra.instIsCofilteredOpposite AlgebraicGeometry.FGSubalgebra.instIsAffineObjOppositeSchemeSpecDiagram AlgebraicGeometry.FGSubalgebra.instNonempty AlgebraicGeometry.FGSubalgebra.instNonemptySubtypeLeSubalgebraValFG AlgebraicGeometry.FGSubalgebra.instCompactSpaceCarrierCarrierCommRingCatObjOppositeSchemeSpecDiagram AlgebraicGeometry.FGSubalgebra.instIsDirectedSubtypeLeSubalgebraValFG AlgebraicGeometry.FGSubalgebra.instIsAffineHomMapOppositeSchemeSpecDiagram AlgebraicGeometry.FGSubalgebra.instIsFiltered AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instNeg AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instSMulInt AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instAddCommGroup AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instAdd AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instSub AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instModuleCarrierObjOppositeOpensCarrierCarrierCommRingCatPresheafOpOpensTop AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instSMulCarrierObjOppositeOpensCarrierCarrierCommRingCatPresheafOpOpensTop AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instSMulNat AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instZero AlgebraicCurve.instHasLocalResidue_of_hasCanonicalLocalResidueK AlgebraicCurve.instHasCanonicalLocalResidueK_of_hasCanonicalLocalResidueKStar"
p2m_attr_erase "instance" "AlgebraicCurve.Place.kw_ffgc_finiteDimensional_adicCompletion instAlgebraSubtypeMemValuationSubring_definitions AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersIntegersCompletion ModularCurve.KwF4gRRTate.instAlgebraKAdicCompletionIntegers AlgebraicCurve.Place.kw_ffgc_continuousSMul_adicCompletionComap AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersCompletionCompletion IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions AlgebraicCurve.instHasCanonicalLocalResidueK AlgebraicCurve.Place.instAlgebra_restrictResidueField AlgebraicCurve.Place.instIsScalarTower_restrictResidueField AlgebraicCurve.instHasLocalResidue AlgebraicCurve.HasSeparableResidue.of_perfectField_of_isCurveOver AlgebraicCurve.HasSeparableResidue.of_perfectField AlgebraicCurve.Place.instIsLocalHom_restrictSubringHom AlgebraicCurve.instHasCanonicalLocalResidueKStar ModularCurve.KwNo6Pin.isLocalRing_completion SheafOfModules.isIso_ihomModelToIhom AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instDecidableEqIdx AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instFintype AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instLinearOrder AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instFintypeIdx AlgebraicGeometry.OModulePresheaf.Leray.relAltC_scalarTower AlgebraicGeometry.OModulePresheaf.Leray.ker_relAltd_modΓ AlgebraicGeometry.OModulePresheaf.Leray.relAltC_modΓ AlgebraicGeometry.OModulePresheaf.Leray.biC_abGrp AlgebraicGeometry.OModulePresheaf.Leray.relAltH_modΓ AlgebraicGeometry.OModulePresheaf.Leray.ker_relAltd_smul AlgebraicGeometry.OModulePresheaf.Leray.relAltH_scalarTower AlgebraicGeometry.OModulePresheaf.Leray.relAltH_smul AlgebraicGeometry.OModulePresheaf.Leray.biC_module DoubleComplex.instModuleE₂I DoubleComplex.Bounded.modR DoubleComplex.instModuleE₂II DoubleComplex.instAddCommGroupE₂II DoubleComplex.Bounded.abGrp"
p2m_attr_erase "instance" "DoubleComplex.instAddCommGroupE₂I AlgebraicGeometry.ChowDatum.hι_closed AlgebraicGeometry.ChowDatumProj.hιN_closed AlgebraicGeometry.ChowDatumProj.hp_proper AlgebraicGeometry.ChowDatum.hp_isoU AlgebraicGeometry.ChowDatum.hp_proper AlgebraicGeometry.ProjSpace.algebraAway AlgebraicGeometry.ProjSpace.instIsProperProdOverπ AlgebraicGeometry.ChowDatumProj.hp_isoU AlgebraicGeometry.ProjSpace.isProper_π AlgebraicGeometry.ProjSpace.finiteType_mvPolynomial ProjSpaceCech.GradedModule.H.module ProjSpaceCech.GradedModule.H.addCommGroup ProjSpaceCech.GradedModule.sec.instAdd ProjSpaceCech.GradedModule.sec.instNeg ProjSpaceCech.GradedModule.acg ProjSpaceCech.GradedModule.Frac.setoid ProjSpaceCech.GradedModule.modR ProjSpaceCech.GradedModule.sec.instModule ProjSpaceCech.GradedModule.sec.instAddCommGroup ProjSpaceCech.GradedModule.sec.instZero ProjSpaceCech.GradedModule.Presentation.fJ ProjSpaceCech.GradedModule.sec.instSMul ProjSpaceCech.Twist.H.module ProjSpaceCech.Idx.instFintype ProjSpaceCech.Twist.H.addCommGroup ProjSpaceCech.Idx.instDecidableEq ProjSpaceCech.Twist.Mon.instDecidableEq ProjSpaceCech.Twist.cochain.instAddCommGroup ProjSpaceCech.Twist.cochain.instModule AlgebraicGeometry.FGSubalgebra.tensorStage_directedSystem AlgebraicGeometry.RelEffCartierDiv.isClosedImmersion_subschemeι_resProdMap AlgebraicGeometry.RelEffCartierDiv.isOpenImmersion_resProdMap AlgebraicCurve.CurveModel.locallyOfFiniteType_gluedToBase AlgebraicCurve.CurveModel.isFractionRing_overlap AlgebraicCurve.CurveModel.isLocallyNoetherian_glued AlgebraicCurve.CurveModel.jacobsonSpace_glued AlgebraicCurve.CurveModel.isOpenImmersion_ι₀ AlgebraicCurve.CurveModel.isIntegral_glued AlgebraicCurve.CurveModel.quasiSeparated_gluedToBase"
p2m_attr_erase "instance" "AlgebraicCurve.CurveModel.compactSpace_glued AlgebraicCurve.CurveModel.isIntegral_adjoin_chartRing AlgebraicCurve.CurveModel.isFractionRing_overlap_functionField AlgebraicCurve.CurveModel.isProper_gluedToBase AlgebraicCurve.CurveModel.isOpenImmersion_ιU AlgebraicCurve.CurveModel.isOpenImmersion_f₀ AlgebraicCurve.CurveModel.isOpenImmersion_fInf AlgebraicCurve.CurveModel.isOpenImmersion_ιInf AlgebraicCurve.CurveModel.algebra_overlap_functionField AlgebraicCurve.CurveModel.quasiCompact_gluedToBase AlgebraicCurve.CurveModel.algebraAdjoin AlgebraicCurve.CurveModel.isDedekindDomain_chartRing AlgebraicCurve.CurveModel.isIntegralClosure AlgebraicCurve.CurveModel.finite_chartRing AlgebraicCurve.CurveModel.centre_isPrime AlgebraicCurve.CurveModel.isFractionRing_chartRing AlgebraicCurve.CurveModel.finiteType_chartRing AlgebraicCurve.CurveModel.isNoetherianRing_chartRing AlgebraicCurve.CurveModel.isScalarTower_base_adjoin AlgebraicCurve.CurveModel.isScalarTower_adjoin AlgebraicCurve.CurveModel.chartRing_finitePresentation AlgebraicGeometry.ProjSpace.twistObj.addCommGroup AlgebraicGeometry.ProjSpace.twistFam.module AlgebraicGeometry.ProjSpace.twistObj.module AlgebraicGeometry.ProjSpace.twistObj.moduleSections AlgebraicGeometry.ProjSpace.twistFam.addCommGroup kmfloorsGlue_int_three_isPrime kmfloorsGlue_int_bot_isPrime"
p2m_attr_erase "simp" "QuaternionAlgebra.baseChangeRight_tmul QuaternionAlgebra.mapOfAlgebraMapEq_apply QuaternionAlgebra.baseChange_tmul RegularLocalRingQuotientAscent.dualNumberFst_apply GoodReductionJacobian.RelativeGroupLaw.fibre_inv GoodReductionJacobian.RelativeGroupLaw.fibrePointToBase_coe GoodReductionJacobian.RelativeGroupLaw.fibrePointOfBase_toBase GoodReductionJacobian.RelativeGroupLaw.fibre_mul GoodReductionJacobian.RelativeGroupLaw.fibrePointToBase_ofBase GoodReductionJacobian.RelativeGroupLaw.fibre_one GoodReductionJacobian.RelativeGroupLaw.fibrePointOfBase_coe GoodReductionJacobian.RelativeGroupLaw.nsmul_zero GoodReductionJacobian.RelativeGroupLaw.mem_torsionSubset GoodReductionJacobian.RelativeGroupLaw.nsmul_succ GoodReductionJacobian.RelativeGroupLaw.baseChangePointToBase_ofBase GoodReductionJacobian.RelativeGroupLaw.baseChangePointToBase_coe GoodReductionJacobian.RelativeGroupLaw.baseChangePointOfBase_coe GoodReductionJacobian.RelativeGroupLaw.baseChange_inv GoodReductionJacobian.RelativeGroupLaw.baseChangePointOfBase_toBase GoodReductionJacobian.RelativeGroupLaw.baseChange_mul GoodReductionJacobian.RelativeGroupLaw.baseChange_one NeronModelInfra.NeronModelPropertyBundle.endExtensionEquiv_symm_restrict NeronModelInfra.schemeHomOverComp_id_left NeronModelInfra.schemeHomOverComp_id_right NeronModelInfra.schemeHomOverId_coe NeronModelInfra.NeronModelPropertyBundle.endExtensionEquiv_apply NeronModelInfra.NeronModelPropertyBundle.restrict_endExtensionEquiv_symm NeronModelInfra.schemeHomOverComp_coe NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_fst NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_snd NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_fst NeronSpecialFibreInfra.neronEndRestrictEquiv_apply NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_fst_assoc NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_snd NeronSpecialFibreInfra.neronEndExtension_genericFibreRestrict NeronSpecialFibreInfra.specClosedFibreInclusion_eq NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_fst_assoc NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_snd_assoc NeronSpecialFibreInfra.genericFibreRestrict_neronEndExtension NeronSpecialFibreInfra.homOverId_coe"
p2m_attr_erase "simp" "NeronSpecialFibreInfra.homOverComp_coe NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_snd_assoc NeronModelInfra.schemeHomOverNpow_succ NeronModelInfra.schemeHomOverNpow_zero GoodReductionJacobian.relativeGroupLawOfGrpObj_inv GoodReductionJacobian.relativeGroupLawOfGrpObj_mul GoodReductionJacobian.overHomEquivSchemeHomOver_apply_coe GoodReductionJacobian.relativeGroupLawOfGrpObj_one GoodReductionJacobian.overHomEquivSchemeHomOver_symm_apply_left SheafOfModules.tensorUnit_eq AlgebraicGeometry.Scheme.Modules.tensorUnit_eq PresheafOfModules.InternalHom.presheaf_map_apply PresheafOfModules.InternalHom.curryFamily_app PresheafOfModules.InternalHom.add_app PresheafOfModules.InternalHom.smul_app PresheafOfModules.InternalHom.zero_app PresheafOfModules.ihomObj_map_val PresheafOfModules.ihomFunctor_map PresheafOfModules.InternalHom.restrict_app PresheafOfModules.InternalHom.postcomp_app PresheafOfModules.InternalHom.neg_app PresheafOfModules.curry'_app_val PresheafOfModules.InternalHom.presheaf_obj PresheafOfModules.ihomFunctor_obj PresheafOfModules.ihomObj_obj PresheafOfModules.InternalHom.sub_app PresheafOfModules.ihomMap_app_val AlgebraicGeometry.Scheme.Modules.tensorPow_zero AlgebraicGeometry.Scheme.Modules.tensorPow_succ AlgebraicGeometry.RelPicard.RigidifiedLineBundle.mk.sizeOf_spec AlgebraicGeometry.RelPicard.RigidifiedLineBundle.mk.injEq AlgebraicGeometry.Scheme.OrderedAffineCover.mk.injEq AlgebraicGeometry.OModulePresheaf.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCover.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.mk.injEq AlgebraicGeometry.Scheme.TwoAffineOpenCover.mk.injEq AlgebraicGeometry.Scheme.TwoAffineOpenCover.mk.sizeOf_spec AlgebraicGeometry.Scheme.TwoAffineOpenCover.pullback_U1 AlgebraicGeometry.Scheme.TwoAffineOpenCover.pullback_U0 TwoChartCech.Sections.mk.injEq"
p2m_attr_erase "simp" "TwoChartCech.Cover.mk.injEq TwoChartCech.GrothendieckComplex.mk.injEq TwoChartCech.Sections.mk.sizeOf_spec TwoChartCech.Cover.mk.sizeOf_spec TwoChartCech.Cover.lineBundle_r0_apply TwoChartCech.GrothendieckComplex.mk.sizeOf_spec TwoChartCech.Cover.lineBundle_r1_apply CoherentBaseChange.TwoTermComplex.mk.sizeOf_spec CoherentBaseChange.TwoTermComplex.mk.injEq AlgebraicGeometry.OModulePresheaf.prod_obj AlgebraicGeometry.OModulePresheaf.restrOpen_obj AlgebraicGeometry.OModulePresheaf.DevissageStep.mk.injEq AlgebraicGeometry.OModulePresheaf.pushforward_obj AlgebraicGeometry.OModulePresheaf.im_obj AlgebraicGeometry.OModulePresheaf.pow_obj AlgebraicGeometry.OModulePresheaf.fstHom_app AlgebraicGeometry.OModulePresheaf.ker_obj AlgebraicGeometry.OModulePresheaf.coker_obj AlgebraicGeometry.OModulePresheaf.DevissageStep.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCover.preimage_U AlgebraicGeometry.OModulePresheaf.sndHom_app AlgebraicGeometry.OModulePresheaf.Hom.mk.injEq AlgebraicGeometry.OModulePresheaf.Hom.id_app AlgebraicGeometry.OModulePresheaf.AffHom.appSections_apply AlgebraicGeometry.OModulePresheaf.AffHom.comp_app AlgebraicGeometry.OModulePresheaf.AffSES.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.AffHom.kerMap_coe AlgebraicGeometry.OModulePresheaf.AffHom.id_app AlgebraicGeometry.OModulePresheaf.Hom.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.Hom.toAffHom_app AlgebraicGeometry.OModulePresheaf.SES.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.AffHom.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.Hom.comp_app AlgebraicGeometry.OModulePresheaf.SES.mk.injEq AlgebraicGeometry.OModulePresheaf.AffHom.mk.injEq AlgebraicGeometry.OModulePresheaf.Hom.appSections_apply AlgebraicGeometry.OModulePresheaf.AffSES.mk.injEq PresheafOfModules.freeεIso_hom_app PresheafOfModules.freeμIso_hom_app AlgebraicGeometry.RelPicard.RepresentsRelSubPic.mk.injEq"
p2m_attr_erase "simp" "AlgebraicGeometry.RelPicard.SubPicCondition.mk.injEq AlgebraicGeometry.RelPicard.SubPicCondition.mk.sizeOf_spec AlgebraicGeometry.RelPicard.RepresentsRelSubPic.mk.sizeOf_spec AlgebraicGeometry.SmoothProperCurve.sectionBaseChange_coe_snd AlgebraicGeometry.SmoothProperCurve.sectionBaseChange_coe_fst AlgebraicCurve.mulAdele_apply AlgebraicCurve.residuePairing_apply_coe AlgebraicCurve.mem_adeleBdd AlgebraicCurve.weilSmul_one AlgebraicCurve.diagonalHom_apply AlgebraicCurve.weilSmul_apply AlgebraicCurve.adeleSpaceMul_coe AlgebraicCurve.mulAdele_one AlgebraicGeometry.SmoothProperCurve.FiniteMapData.twoAffineOpenCover_U1 AlgebraicGeometry.SmoothProperCurve.FiniteMapData.mk.injEq AlgebraicGeometry.SmoothProperCurve.FiniteMapData.mk.sizeOf_spec AlgebraicGeometry.SmoothProperCurve.FiniteMapData.twoAffineOpenCover_U0 AlgebraicGeometry.RelPicard.SubPicCondition.onClasses_mk AlgebraicGeometry.RelPicard.relSubPicPresheaf_map_coe CategoryTheory.Functor.OverTotal.ofFibre_fst CategoryTheory.Functor.overTotal_map_fst AlgebraicGeometry.Scheme.LocalRepresentabilityULift.glueData_J AlgebraicGeometry.Scheme.LocalRepresentabilityULift.uliftYoneda_toGlued_uliftYonedaGluedToSheaf AlgebraicGeometry.Scheme.LocalRepresentabilityULift.glueData_t' AlgebraicGeometry.Scheme.LocalRepresentabilityULift.uliftYoneda_toGlued_uliftYonedaGluedToSheaf_assoc AlgebraicGeometry.Scheme.LocalRepresentabilityULift.uliftYonedaGluedToSheaf_app_toGlued AlgebraicGeometry.Scheme.LocalRepresentabilityULift.glueData_openCover_map AlgebraicGeometry.Scheme.LocalRepresentabilityULift.uliftYonedaGluedToSheaf_app_comp AlgebraicGeometry.Scheme.LocalRepresentabilityULift.glueData_V AlgebraicGeometry.Scheme.LocalRepresentabilityULift.glueData_t AlgebraicGeometry.Scheme.LocalRepresentabilityULift.glueData_U AlgebraicGeometry.Scheme.LocalRepresentabilityULift.glueData_f AlgebraicGeometry.RelPicard.designationOfRepresentableBy_P AlgebraicGeometry.RelPicard.designationOfRepresentableBy_toBase AlgebraicGeometry.RelPicard.rigSection_snd AlgebraicGeometry.RelPicard.RigidifiedLineBundle.ofInvertible_L AlgebraicGeometry.RelPicard.rigSection_snd_assoc AlgebraicGeometry.RelPicard.SubPicGroupCondition.mk.injEq AlgebraicGeometry.RelPicard.SubPicGroupCondition.mk.sizeOf_spec AlgebraicCurve.coe_cechH0Equiv_apply"
p2m_attr_erase "simp" "AlgebraicCurve.cechH1ToH1_mk AlgebraicCurve.lSpaceOn_univ AlgebraicCurve.lSpaceOn_empty AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.jqNModC_one ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring"
p2m_attr_erase "simp" "AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none AlgebraicCurve.Place.differentialCoeff_zero AlgebraicCurve.Place.differentialCoeff_dCoord AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.injEq AlgebraicCurve.TranscendenceTower.mk.injEq AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec AlgebraicCurve.PoleDivisorPackage.mk.injEq AlgebraicGeometry.RelPicard.thetaBundle_def AlgebraicGeometry.RelPicard.picardBundle_def AlgebraicGeometry.RelEffCartierDiv.toRelEffDivisor_ofRelEffDivisor AlgebraicGeometry.RelEffCartierDiv.toRelEffDivisor_I AlgebraicGeometry.mapOnProdOver_fst_assoc AlgebraicGeometry.RelEffCartierDiv.mk.sizeOf_spec AlgebraicGeometry.RelEffCartierDiv.mk.injEq AlgebraicGeometry.mapOnProdOver_snd AlgebraicGeometry.mapOnProdOver_fst AlgebraicGeometry.mapOnProdOver_snd_assoc AlgebraicGeometry.mapOnProdOver_id AlgebraicCurve.RelEffDivisor.mk.sizeOf_spec AlgebraicCurve.mapOnProd_fst AlgebraicCurve.mapOnProd_fst_assoc AlgebraicCurve.mapOnProd_snd AlgebraicCurve.UnivDivisorPack.mk.injEq AlgebraicCurve.RelEffDivisor.mk.injEq AlgebraicCurve.UnivDivisorPack.mk.sizeOf_spec AlgebraicCurve.mapOnProd_snd_assoc AlgebraicGeometry.Scheme.Modules.exteriorPower_obj PresheafOfModules.exteriorPower_map_ιMulti PresheafOfModules.ExteriorPower.appₗ_apply AlgebraicGeometry.prodKerGraph_one AlgebraicGeometry.fibrePowOver.proj_comp AlgebraicGeometry.prodKerGraph_zero AlgebraicGeometry.RelEffCartierDiv.empty_I AlgebraicGeometry.fibrePowOver.proj_comp_assoc AlgebraicGeometry.graphOver_fst_assoc"
p2m_attr_erase "simp" "AlgebraicGeometry.RelEffCartierDiv.toPoint_comp AlgebraicGeometry.RelEffCartierDiv.toPoint_comp_assoc AlgebraicGeometry.graphOver_fst AlgebraicGeometry.RelEffCartierDiv.ofPoint_I AlgebraicGeometry.graphOver_snd AlgebraicGeometry.graphOver_snd_assoc AlgebraicCurve.SymmetricPowerPackage.mk.sizeOf_spec AlgebraicCurve.SymmetricPowerPackage.mk.injEq AlgebraicGeometry.FGSubalgebra.cocone_ι_app_apply AlgebraicGeometry.RelPicard.fst_toProdSpec AlgebraicGeometry.RelPicard.toProdSpec_fst_assoc AlgebraicGeometry.RelPicard.pointsSubBasepointModule_cons AlgebraicGeometry.RelPicard.pointsSubBasepointModule_nil AlgebraicGeometry.RelPicard.fst_toProdSpec_assoc AlgebraicGeometry.RelPicard.toProdSpec_fst AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.sub_app AlgebraicGeometry.Scheme.IdealSheafData.sres_sresTop AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.add_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.mk.sizeOf_spec AlgebraicGeometry.Scheme.IdealSheafData.coe_resLE AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.smul_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.coe_ofLE_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.ideal_range AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.zero_app AlgebraicGeometry.Scheme.IdealSheafData.sres_sres AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.comp_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.neg_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.id_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.coe_mulRight_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.nsmul_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.mk.injEq AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.zsmul_app AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.sizeOf_spec AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.injEq AlgebraicCurve.adeleSingle_coe AlgebraicCurve.kaehlerResidueTermKFam_apply AlgebraicCurve.Place.LocalResidueData.mk.injEq AlgebraicCurve.Place.LocalResidueData.mk.sizeOf_spec AlgebraicCurve.Place.kw_ffgc_adicCompletionComapIntegers_coe AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.sizeOf_spec"
p2m_attr_erase "simp" "AlgebraicCurve.Place.mem_simplePoleSubmodule AlgebraicCurve.Place.coe_uniformizerSubring ModularCurve.Lg37.Lg37CompletionSection.mk.injEq AlgebraicCurve.Place.CoefficientFieldSection.mk.injEq AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.injEq ModularCurve.Lg37.Lg37CompletionSection.mk.sizeOf_spec AlgebraicCurve.Place.CoefficientFieldSection.mk.sizeOf_spec AlgebraicCurve.Place.poleSubmodule_one AlgebraicCurve.Place.mem_poleSubmodule AlgebraicGeometry.Scheme.Modules.toUnitSection_ofUnitSection AlgebraicGeometry.Scheme.Modules.pullbackSection_def AlgebraicGeometry.Scheme.Modules.ofUnitSection_toUnitSection PresheafOfModules.InternalHom.IsSheafAux.appAt_toPresheafHom SheafOfModules.ihomSectionsEquivFamily_unit AlgebraicGeometry.Scheme.Modules.restrictHomEquivFamily_apply SheafOfModules.ihomEval_unit_app AlgebraicGeometry.Scheme.Modules.ihomEval_zero_right AlgebraicGeometry.Scheme.Modules.ihomEval_zero_left AlgebraicGeometry.Scheme.Modules.homOfFamily_app_apply SheafOfModules.unit_ihomSectionsEquivFamily AlgebraicGeometry.Scheme.Modules.familyOfHom_app AlgebraicGeometry.Scheme.Modules.restrictUnitIso_hom_app_apply AlgebraicGeometry.Scheme.Modules.restrictUnitIso_inv_app_apply AlgebraicGeometry.Scheme.Modules.restrictHomOfFamily_app_apply AlgebraicGeometry.Scheme.Modules.restrictHomEquivFamily_symm_apply AlgebraicGeometry.Scheme.Modules.tensorSections_zero_right AlgebraicGeometry.Scheme.Modules.map_unitSection AlgebraicGeometry.Scheme.Modules.tensorSectionsBilin_apply AlgebraicGeometry.Scheme.Modules.tensorPowSection_zero AlgebraicGeometry.Scheme.Modules.tensorSections_zero_left AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_neg AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_zero AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_sub AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_add AlgebraicGeometry.Scheme.OrderedAffineCover.toCoverOf_U AlgebraicGeometry.Scheme.OrderedAffineCoverOf.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCoverOf.mk.injEq AlgebraicGeometry.Scheme.OrderedAffineCover.restrict_U AlgebraicGeometry.OModulePresheaf.Leray.restrictToPreimage_U DoubleComplex.Bounded.mk.injEq"
p2m_attr_erase "simp" "DoubleComplex.Bounded.mk.sizeOf_spec DoubleComplex.Convergence.mk.injEq DoubleComplex.Convergence.mk.sizeOf_spec DoubleComplex.SubQuot.mk.sizeOf_spec DoubleComplex.SubQuot.mk.injEq AlgebraicGeometry.ChowDatumProj.mk.sizeOf_spec AlgebraicGeometry.ChowDatum.mk.sizeOf_spec AlgebraicGeometry.ChowDatumProj.mk.injEq AlgebraicGeometry.ChowDatum.mk.injEq ProjSpaceCech.GradedModule.mk.injEq ProjSpaceCech.GradedModule.mk.sizeOf_spec ProjSpaceCech.GradedModule.Frac.mk.sizeOf_spec ProjSpaceCech.GradedModule.Presentation.mk.injEq ProjSpaceCech.GradedModule.Frac.mk.injEq ProjSpaceCech.GradedModule.Presentation.mk.sizeOf_spec ProjSpaceCech.GradedModule.Hom.shift_toLinearMap ProjSpaceCech.GradedModule.Hom.mk.sizeOf_spec ProjSpaceCech.GradedModule.Hom.mk.injEq TwoChartCech.Mumford.dK_apply TwoChartCech.Mumford.ι0_apply TwoChartCech.Mumford.ι1_apply TwoChartCech.KerCoprod.dK_apply TwoChartCech.KerCoprod.ι1_apply TwoChartCech.KerCoprod.ι0_apply AlgebraicGeometry.tilde.functorCompPullbackSpecIso_app AlgebraicGeometry.RelPicard.algEquivZeroGroupCut_toSubPicCondition AlgebraicGeometry.RelPicard.LFP.stageHom_val AlgebraicGeometry.RelPicard.BaseChange.relSubPicPresheafRestrictIso_hom_app_coe AlgebraicGeometry.RelPicard.BaseChange.relSubPicPresheafRestrictIso_inv_app_coe AlgebraicGeometry.RelPicard.BaseChange.restrict_P AlgebraicGeometry.RelEffCartierDiv.IsUniversal.lift_comp AlgebraicGeometry.RelEffCartierDiv.functor_map_fst AlgebraicGeometry.RelEffCartierDiv.IsUniversal.homEquiv_apply AlgebraicGeometry.RelEffCartierDiv.IsUniversal.lift_pullbackAlong AlgebraicGeometry.RelEffCartierDiv.IsUniversal.homEquiv_symm_apply AlgebraicGeometry.RelEffCartierDiv.IsUniversal.lift_comp_assoc AlgebraicGeometry.RelEffCartierDiv.supportedIn_top AlgebraicGeometry.RelEffCartierDiv.mem_supportedIn_iff AlgebraicGeometry.RelEffCartierDiv.supportedIn_top_eq AlgebraicGeometry.RelEffCartierDiv.restrictAlong_extendAlong"
p2m_attr_erase "simp" "AlgebraicGeometry.RelEffCartierDiv.extendAlong_I AlgebraicGeometry.RelEffCartierDiv.resProdMap_snd AlgebraicGeometry.RelEffCartierDiv.restrictAlong_I AlgebraicGeometry.RelEffCartierDiv.extendAlong_restrictAlong AlgebraicGeometry.RelEffCartierDiv.resProdMap_fst_assoc AlgebraicGeometry.RelEffCartierDiv.resProdMap_snd_assoc AlgebraicGeometry.RelEffCartierDiv.resProdMap_fst CoherentBaseChange.FibreH0Family.mk.sizeOf_spec CoherentBaseChange.FibreH0Family.mk.injEq AlgebraicGeometry.Scheme.Modules.ProjPresentation.mk.injEq AlgebraicGeometry.Scheme.Modules.ProjPresentation.mk.sizeOf_spec AlgebraicCurve.CurveModel.coe_gInf AlgebraicCurve.CurveModel.coe_tInvChart AlgebraicCurve.CurveModel.ιInf_gluedToBase_assoc AlgebraicCurve.CurveModel.ιInf_gluedToBase AlgebraicCurve.CurveModel.primeOfι₀_asIdeal AlgebraicCurve.CurveModel.coe_tChart AlgebraicCurve.CurveModel.ι₀_gluedToBase_assoc AlgebraicCurve.CurveModel.primeOfιInf_asIdeal AlgebraicCurve.CurveModel.ι₀_gluedToBase AlgebraicCurve.CurveModel.coe_tma AlgebraicCurve.CurveModel.coe_primeEquivChartPlaces AlgebraicGeometry.ProjSpace.twistObj.mk.injEq AlgebraicGeometry.ProjSpace.twistObj.zero_val AlgebraicGeometry.ProjSpace.twistObj.add_val AlgebraicGeometry.ProjSpace.twist_res_val AlgebraicGeometry.ProjSpace.twist_smul_val AlgebraicGeometry.ProjSpace.twistGradeToObj_val AlgebraicGeometry.ProjSpace.twistObj.smul_val AlgebraicGeometry.ProjSpace.twistGradeEquiv_apply_val AlgebraicGeometry.ProjSpace.twistObj.mk.sizeOf_spec AlgebraicGeometry.schemeFibreEndo_snd AlgebraicGeometry.schemeFibreEndo_fst GoodReductionJacobian.RelativeGroupLaw.actionSndPoint_coe GoodReductionJacobian.RelativeGroupLaw.actionFstPoint_coe LocalGL2.swapUnit_val"

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 160000000
set_option synthInstance.maxHeartbeats 1600000

open scoped TensorProduct Quaternion NumberField MatrixGroups
open IsDedekindDomain QuaternionAlgebra CerednikDrinfeld ModularCurve AlgebraicCurve
open CerednikDrinfeld.Mumford CerednikDrinfeld.Omega
open scoped Classical
open CategoryTheory AlgebraicGeometry CerednikDrinfeld.QM NeronModelInfra

theorem rdoff_twist_exists {X : Scheme.{0}} {R C : Type} [CommRing R] [CommRing C]
    (f : X ⟶ Spec (CommRingCat.of R)) (b : R →+* C) (σ : C ≃+* C) (hσ : (σ : C →+* C).comp b = b)
    [IsIntegral (Limits.pullback f (Spec.map (CommRingCat.ofHom b)))] :
    ∃ t : Limits.pullback f (Spec.map (CommRingCat.ofHom b)) ⟶ Limits.pullback f (Spec.map (CommRingCat.ofHom b)),
      t ≫ Limits.pullback.fst f (Spec.map (CommRingCat.ofHom b)) = Limits.pullback.fst f (Spec.map (CommRingCat.ofHom b)) ∧
      t ≫ Limits.pullback.snd f (Spec.map (CommRingCat.ofHom b)) =
        Limits.pullback.snd f (Spec.map (CommRingCat.ofHom b)) ≫ Spec.map (CommRingCat.ofHom (σ : C →+* C)) ∧
      t.base (genericPoint ((Limits.pullback f (Spec.map (CommRingCat.ofHom b))) : Scheme.{0})) =
        genericPoint ((Limits.pullback f (Spec.map (CommRingCat.ofHom b))) : Scheme.{0}) := by
  have hσ' : (σ.symm : C →+* C).comp b = b := by
    ext x
    have h : σ (b x) = b x := RingHom.congr_fun hσ x
    exact (congrArg σ.symm h.symm).trans (σ.symm_apply_apply (b x))
  have hc : ∀ (τ : C ≃+* C), (τ : C →+* C).comp b = b →
      Spec.map (CommRingCat.ofHom (τ : C →+* C)) ≫ Spec.map (CommRingCat.ofHom b) = Spec.map (CommRingCat.ofHom b) := by
    intro τ hτ
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, hτ]
  let mk : ∀ (τ : C ≃+* C), (τ : C →+* C).comp b = b →
      (Limits.pullback f (Spec.map (CommRingCat.ofHom b)) ⟶ Limits.pullback f (Spec.map (CommRingCat.ofHom b))) :=
    fun τ hτ => Limits.pullback.lift (Limits.pullback.fst f _) (Limits.pullback.snd f _ ≫ Spec.map (CommRingCat.ofHom (τ : C →+* C)))
      (by rw [Category.assoc, hc τ hτ]; exact Limits.pullback.condition)
  have hmk : ∀ (τ : C ≃+* C) (hτ : (τ : C →+* C).comp b = b) (τ' : C ≃+* C) (hτ' : (τ' : C →+* C).comp b = b),
      (τ : C →+* C).comp (τ' : C →+* C) = RingHom.id C → mk τ hτ ≫ mk τ' hτ' = 𝟙 _ := by
    intro τ hτ τ' hτ' h
    apply Limits.pullback.hom_ext
    · simp only [mk, Category.assoc, Limits.pullback.lift_fst, Category.id_comp]
    · simp only [mk, Category.assoc, Limits.pullback.lift_snd, Category.id_comp]
      rw [Limits.pullback.lift_snd_assoc, Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp, h,
        CommRingCat.ofHom_id, Spec.map_id, Category.comp_id]
  have h1 : mk σ hσ ≫ mk σ.symm hσ' = 𝟙 _ := hmk σ hσ σ.symm hσ' (by ext x; simp)
  have h2 : mk σ.symm hσ' ≫ mk σ hσ = 𝟙 _ := hmk σ.symm hσ' σ hσ (by ext x; simp)
  haveI : IsIso (mk σ hσ) := ⟨⟨mk σ.symm hσ', h1, h2⟩⟩
  refine ⟨mk σ hσ, Limits.pullback.lift_fst _ _ _, Limits.pullback.lift_snd _ _ _, ?_⟩
  exact genericPoint_eq_of_isOpenImmersion (mk σ hσ)

theorem rdoff_inv_smul_eq_smul {G α : Type} [Group G] [MulAction G α] (w : G) (y : α) (h : (w * w) • y = y) :
    w⁻¹ • y = w • y := by
  conv_lhs => rw [← h]
  rw [← mul_smul, inv_mul_cancel_left]

theorem solution
    {N q q' : ℕ} [NeZero N] (hN : Squarefree N) [Fact q.Prime] [Fact q'.Prime]
    (hqN : ¬ q ∣ N) (hq'N : ¬ q' ∣ N) (hqq' : q' ≠ q)
    (D : ℕ) [NeZero D] (hD : 2 * N * q * q' ∣ D)
    (hq5 : 5 ≤ q) (hq'5 : 5 ≤ q')
    (A₂ : ValuationSubring (AlgebraicClosure ℚ)) (hA₂ : A₂.LiesOverPrime q)

    {a₁ b₁ : ℚ} (hdef₁ : IsDefiniteRamifiedExactlyAt (a := a₁) (b := b₁) q')
    (Λ₁ R₁ : Submodule ℤ ℍ[ℚ, a₁, b₁]) (hΛ₁ : IsMaximalOrder Λ₁) (hR₁ : IsEichlerOrder R₁ N) (hRΛ₁ : R₁ ≤ Λ₁)
    (n₁ : (ℍ[ℚ, a₁, b₁] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) (hn₁ : n₁ ∈ primeHeckeSet R₁ q)
    (hS₁ : IsEichlerOrder (meetOrder R₁ n₁) (N * q))
    (hnorm₁ : Submodule.conjByFiniteIdele (meetOrder R₁ n₁) n₁ = meetOrder R₁ n₁)
    (hsq₁ : ∀ x : ClassSet (Submodule.finiteIdeleStabilizer (meetOrder R₁ n₁)),
      classSetShift _ n₁ (classSetShift _ n₁ x) = x)
    [Fintype (ClassSet (Submodule.finiteIdeleStabilizer (meetOrder R₁ n₁)))]
    [Fintype (ClassSet (Submodule.finiteIdeleStabilizer R₁))]
    [DecidableEq (ClassSet (Submodule.finiteIdeleStabilizer R₁))]
    (hlaws₁ : ClassSetHeckeLaws N q Λ₁ R₁ n₁)

    {a b : ℚ} (hB : IsIndefiniteRamifiedExactlyAt a b q q')
    (Λ : Submodule ℤ ℍ[ℚ, a, b]) (hΛ : IsMaximalOrder Λ)

    (Fbar : Type) [Field Fbar] [Algebra (AlgebraicClosure ℚ) Fbar]
    [IsCurveOver (AlgebraicClosure ℚ) Fbar] [Algebra.EssFiniteType (AlgebraicClosure ℚ) Fbar]
    (X : Scheme.{0}) (πX : X ⟶ Spec (CommRingCat.of (Localization.Away ((D : ℕ) : ℤ))))
    (sbar : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ Spec (CommRingCat.of (Localization.Away ((D : ℕ) : ℤ))))
    (pt : ∀ (S : Type) [CommRing S] (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of (Localization.Away ((D : ℕ) : ℤ)))),
      FakeEllipticCurve Λ N S → SchemeHomOver s πX)
    (pt_iso : ∀ (S : Type) [CommRing S] (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of (Localization.Away ((D : ℕ) : ℤ))))
      (E E' : FakeEllipticCurve Λ N S), FakeEllipticCurve.Iso E E' → pt S s E = pt S s E')
    (pt_pullback : ∀ (S S' : Type) [CommRing S] [CommRing S'] (φ : S →+* S')
      (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of (Localization.Away ((D : ℕ) : ℤ))))
      (s' : Spec (CommRingCat.of S') ⟶ Spec (CommRingCat.of (Localization.Away ((D : ℕ) : ℤ)))),
      Spec.map (CommRingCat.ofHom φ) ≫ s = s' → ∀ (E : FakeEllipticCurve Λ N S) (E' : FakeEllipticCurve Λ N S'),
      FakeEllipticCurve.IsPullback φ E E' → (pt S' s' E').1 = Spec.map (CommRingCat.ofHom φ) ≫ (pt S s E).1)
    (pt_surjective : ∀ (k : Type) [Field k] [IsAlgClosed k] (s : Spec (CommRingCat.of k) ⟶ Spec (CommRingCat.of (Localization.Away ((D : ℕ) : ℤ))))
      (x : SchemeHomOver s πX), ∃ E : FakeEllipticCurve Λ N k, pt k s E = x)
    (pt_injective : ∀ (k : Type) [Field k] [IsAlgClosed k] (s : Spec (CommRingCat.of k) ⟶ Spec (CommRingCat.of (Localization.Away ((D : ℕ) : ℤ))))
      (E E' : FakeEllipticCurve Λ N k), pt k s E = pt k s E' → FakeEllipticCurve.Iso E E')

    (𝔐 : AlgebraicCurve.CurveModel (AlgebraicClosure ℚ) Fbar)
    (e𝔐 : 𝔐.C ⟶ CategoryTheory.Limits.pullback πX sbar) [CategoryTheory.IsIso e𝔐]
    (he𝔐 : e𝔐 ≫ CategoryTheory.Limits.pullback.snd πX sbar = 𝔐.toBase)
    (gal : ((AlgebraicClosure ℚ) ≃ₐ[ℚ] (AlgebraicClosure ℚ)) →* SemilinearAut (AlgebraicClosure ℚ) Fbar)

    (𝕋 : HeckeTower.TowerData q q' Fbar)
    (galT : ∀ ℓ : HeckeTower.AwayPrime q q', ((AlgebraicClosure ℚ) ≃ₐ[ℚ] (AlgebraicClosure ℚ)) →* SemilinearAut (AlgebraicClosure ℚ) (𝕋.F ℓ))
    (W : Fin 2 → SemilinearAut (AlgebraicClosure ℚ) Fbar)
    (WT : ∀ ℓ : HeckeTower.AwayPrime q q', Fin 2 → SemilinearAut (AlgebraicClosure ℚ) (𝕋.F ℓ))
    (tw : ModuliTowerWitnessD Λ N q q' D Fbar X πX sbar pt 𝔐 e𝔐 gal 𝕋 galT W WT)

    [hiso₂ : Fact (A₂.DecompositionIsometric ℚ)]
    (v₂ : HeightOneSpectrum (𝓞 ℚ)) (hv₂ : ((q : ℕ) : 𝓞 ℚ) ∈ v₂.asIdeal)

    (ι₂ : ℍ[ℚ, a₁, b₁] →ₐ[ℚ] Matrix (Fin 2) (Fin 2) ↥(ValuationSubring.ratClosure A₂)) (hι₂ : Function.Injective ι₂)
    (ρ₂ : (ℍ[ℚ, a₁, b₁])ˣ →* PGL(2, ↥(ValuationSubring.ratClosure A₂)))
    (hρ₂ : ∀ x : (ℍ[ℚ, a₁, b₁])ˣ, ρ₂ x = Matrix.ProjGenLinGroup.mk (Units.map (ι₂ : ℍ[ℚ, a₁, b₁] →* Matrix (Fin 2) (Fin 2) ↥(ValuationSubring.ratClosure A₂)) x))

    (ϖ₂ : Omega.PseudoUniformizer ↥(ValuationSubring.ratClosure A₂) A₂.valuation.Completion)
    (hϖ₂ : algebraMap ↥(ValuationSubring.ratClosure A₂) A₂.valuation.Completion ϖ₂.ϖ = ((q : AlgebraicClosure ℚ) : A₂.valuation.Completion))
    [hdom₂ : IsDomain (Omega.HolRingOf ϖ₂ ρ₂)]

    (s₂ : HeckeTower.AwayPrime q q' → (ℍ[ℚ, a₁, b₁])ˣ)
    (sf₂ : HeckeTower.AwayPrime q q' → (ℍ[ℚ, a₁, b₁] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ)
    (hs₂ : ∀ ℓ : HeckeTower.AwayPrime q q',
      (∀ u : HeightOneSpectrum (𝓞 ℚ), ((q : ℕ) : 𝓞 ℚ) ∉ u.asIdeal →
        Submodule.finiteAdeleEvalAt ℍ[ℚ, a₁, b₁] u (sf₂ ℓ : ℍ[ℚ, a₁, b₁] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ) =
          (s₂ ℓ : ℍ[ℚ, a₁, b₁]) ⊗ₜ[ℚ] (1 : u.adicCompletion ℚ)) ∧
      (∀ u : HeightOneSpectrum (𝓞 ℚ), ((q : ℕ) : 𝓞 ℚ) ∈ u.asIdeal →
        Submodule.finiteAdeleEvalAt ℍ[ℚ, a₁, b₁] u (sf₂ ℓ : ℍ[ℚ, a₁, b₁] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ) = 1) ∧
      Submodule.finiteIdeleDiagonal ℍ[ℚ, a₁, b₁]
          (Units.map (algebraMap ℚ ℍ[ℚ, a₁, b₁]).toMonoidHom
            (Units.mk0 ((ℓ.1 : ℕ) : ℚ) (Nat.cast_ne_zero.mpr ℓ.1.prop.ne_zero))) * (sf₂ ℓ)⁻¹ ∈
        (if (ℓ.1 : ℕ) ∣ N then levelHeckeUSet Λ₁ (meetOrder R₁ n₁) (ℓ.1 : ℕ)
          else primeHeckeSet (meetOrder R₁ n₁) (ℓ.1 : ℕ)) ∧
      nrd (s₂ ℓ : ℍ[ℚ, a₁, b₁]) = ((ℓ.1 : ℕ) : ℚ))

    (Γ₂ : HeckeTower.Obj q q' → Subgroup (ℍ[ℚ, a₁, b₁])ˣ)
    (hΓ₂0 : ∀ x : (ℍ[ℚ, a₁, b₁])ˣ, x ∈ Γ₂ none ↔
      x ∈ CerednikDrinfeld.CosetGraph.awayUnits R₁ v₂ ∧ Even (padicValRat q (nrd (x : ℍ[ℚ, a₁, b₁]))))
    (hΓ₂ℓ : ∀ ℓ : HeckeTower.AwayPrime q q', Γ₂ (some ℓ) = Γ₂ none ⊓ (Γ₂ none).map (MulAut.conj (s₂ ℓ)).toMonoidHom)

    (w₂ wbar₂ : HeckeTower.Obj q q' → (ℍ[ℚ, a₁, b₁])ˣ)
    (hw₂ : (w₂ none ∈ CerednikDrinfeld.CosetGraph.awayUnits R₁ v₂ ∧ nrd (w₂ none : ℍ[ℚ, a₁, b₁]) = (q : ℚ)) ∧
      ∀ ℓ : HeckeTower.AwayPrime q q',
        w₂ (some ℓ) ∈ CerednikDrinfeld.CosetGraph.awayUnits (meetOrder R₁ (sf₂ ℓ)) v₂ ∧ nrd (w₂ (some ℓ) : ℍ[ℚ, a₁, b₁]) = (q : ℚ))
    (hwbar₂ :
      (nrd (wbar₂ none : ℍ[ℚ, a₁, b₁]) = (q' : ℚ) ∧
        (∀ u : HeightOneSpectrum (𝓞 ℚ), u ≠ v₂ → ((q' : ℕ) : 𝓞 ℚ) ∉ u.asIdeal →
          CosetGraph.toLoc u (wbar₂ none) ∈ Submodule.localBoxUnits R₁ u) ∧
        (∀ u : HeightOneSpectrum (𝓞 ℚ), u ≠ v₂ → ∀ x : CosetGraph.Loc a₁ b₁ u,
          ((((CosetGraph.toLoc u (wbar₂ none))⁻¹ : (CosetGraph.Loc a₁ b₁ u)ˣ) : CosetGraph.Loc a₁ b₁ u) * x *
              ((CosetGraph.toLoc u (wbar₂ none) : (CosetGraph.Loc a₁ b₁ u)ˣ) : CosetGraph.Loc a₁ b₁ u) ∈ Submodule.localBox R₁ u ↔
            x ∈ Submodule.localBox R₁ u) ∧
          ((((CosetGraph.toLoc u (wbar₂ none))⁻¹ : (CosetGraph.Loc a₁ b₁ u)ˣ) : CosetGraph.Loc a₁ b₁ u) * x *
              ((CosetGraph.toLoc u (wbar₂ none) : (CosetGraph.Loc a₁ b₁ u)ˣ) : CosetGraph.Loc a₁ b₁ u) ∈ Submodule.localBox Λ₁ u ↔
            x ∈ Submodule.localBox Λ₁ u))) ∧
      ∀ ℓ : HeckeTower.AwayPrime q q',
        (nrd (wbar₂ (some ℓ) : ℍ[ℚ, a₁, b₁]) = (q' : ℚ) ∧
          (∀ u : HeightOneSpectrum (𝓞 ℚ), u ≠ v₂ → ((q' : ℕ) : 𝓞 ℚ) ∉ u.asIdeal →
            CosetGraph.toLoc u (wbar₂ (some ℓ)) ∈ Submodule.localBoxUnits (meetOrder R₁ (sf₂ ℓ)) u) ∧
          (∀ u : HeightOneSpectrum (𝓞 ℚ), u ≠ v₂ → ∀ x : CosetGraph.Loc a₁ b₁ u,
            ((((CosetGraph.toLoc u (wbar₂ (some ℓ)))⁻¹ : (CosetGraph.Loc a₁ b₁ u)ˣ) : CosetGraph.Loc a₁ b₁ u) * x *
                ((CosetGraph.toLoc u (wbar₂ (some ℓ)) : (CosetGraph.Loc a₁ b₁ u)ˣ) : CosetGraph.Loc a₁ b₁ u) ∈ Submodule.localBox (meetOrder R₁ (sf₂ ℓ)) u ↔
              x ∈ Submodule.localBox (meetOrder R₁ (sf₂ ℓ)) u) ∧
            ((((CosetGraph.toLoc u (wbar₂ (some ℓ)))⁻¹ : (CosetGraph.Loc a₁ b₁ u)ˣ) : CosetGraph.Loc a₁ b₁ u) * x *
                ((CosetGraph.toLoc u (wbar₂ (some ℓ)) : (CosetGraph.Loc a₁ b₁ u)ˣ) : CosetGraph.Loc a₁ b₁ u) ∈ Submodule.localBox Λ₁ u ↔
              x ∈ Submodule.localBox Λ₁ u))))

    (dIso₂ : ↥(A₂.decompositionSubgroup ℚ) →* Omega.IsometricAut ↥(ValuationSubring.ratClosure A₂) A₂.valuation.Completion)
    (hdIso₂ : ∀ (τ : ↥(A₂.decompositionSubgroup ℚ)) (x : A₂.valuation.Completion), (dIso₂ τ).toRingEquiv x = τ • x)

    (χ : ↥(A₂.decompositionSubgroup ℚ) →* Multiplicative (ZMod 2))
    (hχ₁ : ∀ τ : ↥(A₂.decompositionSubgroup ℚ), (τ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) ∈ A₂.inertiaSubgroupIn ℚ → χ τ = 1)
    (hχ₂ : ∀ φ : ↥(A₂.decompositionSubgroup ℚ), A₂.IsFrobeniusAt (φ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) q → χ φ ≠ 1)
    (hχ₃ : ∀ τ : ↥(A₂.decompositionSubgroup ℚ), χ τ = 1 ↔ ∀ x : IsLocalRing.ResidueField ↥A₂, x ^ (q ^ 2) = x → τ • x = x)

    (𝒪₀ : Type) [CommRing 𝒪₀] [IsDomain 𝒪₀] [CharZero 𝒪₀] (hdvr₀ : IsDiscreteValuationRing 𝒪₀)
    (π : 𝒪₀) (hπ : Irreducible π) (hcpl : IsAdicComplete (Ideal.span {π}) 𝒪₀) (hres : Nat.card (𝒪₀ ⧸ Ideal.span {π}) = q)
    (hunr : Ideal.span {((q : ℕ) : 𝒪₀)} = Ideal.span {π})
    [Algebra 𝒪₀ ↥(ValuationSubring.ratClosure A₂)] [IsFractionRing 𝒪₀ ↥(ValuationSubring.ratClosure A₂)]
    (Onr : Type) [CommRing Onr] [IsDomain Onr] [CharZero Onr] [Algebra 𝒪₀ Onr] (Fr : Onr ≃ₐ[𝒪₀] Onr)
    (hOc : IsAdicComplete (Ideal.span {algebraMap 𝒪₀ Onr π}) Onr)
    (hOm : (Ideal.span {algebraMap 𝒪₀ Onr π}).IsMaximal)
    (hOa : ∀ x : Onr, ∃ p : Polynomial 𝒪₀, p.Monic ∧ Polynomial.aeval x p ∈ Ideal.span {algebraMap 𝒪₀ Onr π})
    (hOcl : ∀ p : Polynomial Onr, p.Monic → 0 < p.natDegree → ∃ x : Onr, Polynomial.eval x p ∈ Ideal.span {algebraMap 𝒪₀ Onr π})
    (hFr : ∀ x : Onr, Fr x - x ^ q ∈ Ideal.span {algebraMap 𝒪₀ Onr π})
    (vdet : Matrix.GeneralLinearGroup (Fin 2) ↥(ValuationSubring.ratClosure A₂) →* Multiplicative ℤ)
    (hvdet : ∀ (g : Matrix.GeneralLinearGroup (Fin 2) ↥(ValuationSubring.ratClosure A₂)) (n : ℤ), vdet g = Multiplicative.ofAdd n ↔
      ∃ u : 𝒪₀ˣ, (Matrix.GeneralLinearGroup.det g : ↥(ValuationSubring.ratClosure A₂)) = algebraMap 𝒪₀ ↥(ValuationSubring.ratClosure A₂) (u : 𝒪₀) * (algebraMap 𝒪₀ ↥(ValuationSubring.ratClosure A₂) π) ^ n)
    (ψ₀ : Onr →+* A₂.valuation.Completion)
    (hπϖ : algebraMap 𝒪₀ ↥(ValuationSubring.ratClosure A₂) π = ϖ₂.ϖ) (hN₀ : IsUnit ((N : ℕ) : 𝒪₀))
    (h𝒪₀ : ∀ x : ↥(ValuationSubring.ratClosure A₂), x ∈ Set.range (algebraMap 𝒪₀ ↥(ValuationSubring.ratClosure A₂)) ↔ Valued.v (algebraMap ↥(ValuationSubring.ratClosure A₂) A₂.valuation.Completion x) ≤ 1)
    (hψ₀ : ∀ y : Onr, Valued.v (ψ₀ y) ≤ 1)
    (hψ₀𝒪 : ψ₀.comp (algebraMap 𝒪₀ Onr) = (algebraMap ↥(ValuationSubring.ratClosure A₂) A₂.valuation.Completion).comp (algebraMap 𝒪₀ ↥(ValuationSubring.ratClosure A₂)))
    (hrk : ∀ x y : A₂.valuation.Completion, Valued.v x < 1 → y ≠ 0 → ∃ n : ℕ, Valued.v x ^ n ≤ Valued.v y)

    (𝒳₀ : Scheme.{0}) (f₀ : 𝒳₀ ⟶ Spec (CommRingCat.of 𝒪₀))
    (pt₀ : ∀ (S : Type) [CommRing S] (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of 𝒪₀)), FakeEllipticCurve Λ N S → SchemeHomOver s f₀)
    (h𝒳₀ : IsCoarseModuli Λ N 𝒳₀ f₀ pt₀) [IsIntegral 𝒳₀] [Flat f₀] [IsSeparated f₀] [LocallyOfFiniteType f₀] [QuasiCompact f₀]
    (𝒴₀ : HeckeTower.AwayPrime q q' → Scheme.{0}) (g₀ : ∀ ℓ : HeckeTower.AwayPrime q q', 𝒴₀ ℓ ⟶ Spec (CommRingCat.of 𝒪₀))
    (ptT₀ : ∀ (ℓ : HeckeTower.AwayPrime q q') (S : Type) [CommRing S] (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of 𝒪₀)),
      FakeEllipticCurve.WithExtraLevel Λ N (ℓ.1 : ℕ) S → SchemeHomOver s (g₀ ℓ))
    (h𝒴₀ : ∀ ℓ : HeckeTower.AwayPrime q q', IsCoarseModuliT Λ N (ℓ.1 : ℕ) (𝒴₀ ℓ) (g₀ ℓ) (ptT₀ ℓ))
    (d₀₀ d₁₀ : ∀ ℓ : HeckeTower.AwayPrime q q', 𝒴₀ ℓ ⟶ 𝒳₀)
    (hd₀f : ∀ ℓ, d₀₀ ℓ ≫ f₀ = g₀ ℓ) (hd₁f : ∀ ℓ, d₁₀ ℓ ≫ f₀ = g₀ ℓ)
    (hd₀ : ∀ (ℓ : HeckeTower.AwayPrime q q') (S : Type) [CommRing S] (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of 𝒪₀))
      (u : FakeEllipticCurve.WithExtraLevel Λ N (ℓ.1 : ℕ) S), (ptT₀ ℓ S s u).1 ≫ d₀₀ ℓ = (pt₀ S s u.1).1)
    (hd₁ : ∀ (ℓ : HeckeTower.AwayPrime q q') (S : Type) [CommRing S] (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of 𝒪₀))
      (u : FakeEllipticCurve.WithExtraLevel Λ N (ℓ.1 : ℕ) S) (d : FakeEllipticCurve Λ N S),
      FakeEllipticCurve.IsLevelIsogeny (ℓ.1 : ℕ) u d → (ptT₀ ℓ S s u).1 ≫ d₁₀ ℓ = (pt₀ S s d).1)

    (ar arbar : 𝒳₀ ⟶ 𝒳₀) (harf : ar ≫ f₀ = f₀) (harbarf : arbar ≫ f₀ = f₀)
    (har : ∀ (S : Type) [CommRing S] (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of 𝒪₀)) (E E' : FakeEllipticCurve Λ N S),
      FakeEllipticCurve.IsAtkinLehnerQuotient q E E' → (pt₀ S s E).1 ≫ ar = (pt₀ S s E').1)
    (harbar : ∀ (S : Type) [CommRing S] (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of 𝒪₀)) (E E' : FakeEllipticCurve Λ N S),
      FakeEllipticCurve.IsAtkinLehnerQuotient q' E E' → (pt₀ S s E).1 ≫ arbar = (pt₀ S s E').1)

    (Θ : ∀ (B : Type) [CommRing B] [Algebra 𝒪₀ B], IsNilpotent (algebraMap 𝒪₀ B π) → (FormalOmega.AlgFunctor.prod (FormalOmega.AlgFunctor.corep Onr) (FormalOmega.Omega ↥(ValuationSubring.ratClosure A₂) π)).obj B → (Scheme.nilpPoints f₀).obj B)
    (ΘT : ∀ ℓ : HeckeTower.AwayPrime q q', ∀ (B : Type) [CommRing B] [Algebra 𝒪₀ B], IsNilpotent (algebraMap 𝒪₀ B π) → (FormalOmega.AlgFunctor.prod (FormalOmega.AlgFunctor.corep Onr) (FormalOmega.Omega ↥(ValuationSubring.ratClosure A₂) π)).obj B → (Scheme.nilpPoints (g₀ ℓ)).obj B)
    (hCD :

      (∀ (B : Type) [CommRing B] [Algebra 𝒪₀ B] (B' : Type) [CommRing B'] [Algebra 𝒪₀ B'] (hB : IsNilpotent (algebraMap 𝒪₀ B π)) (hB' : IsNilpotent (algebraMap 𝒪₀ B' π))
          (φ : B →ₐ[𝒪₀] B') (x : (FormalOmega.AlgFunctor.prod (FormalOmega.AlgFunctor.corep Onr) (FormalOmega.Omega ↥(ValuationSubring.ratClosure A₂) π)).obj B), Θ B' hB' ((FormalOmega.AlgFunctor.prod (FormalOmega.AlgFunctor.corep Onr) (FormalOmega.Omega ↥(ValuationSubring.ratClosure A₂) π)).map φ x) = (Scheme.nilpPoints f₀).map φ (Θ B hB x)) ∧
      (∀ ℓ : HeckeTower.AwayPrime q q', (∀ (B : Type) [CommRing B] [Algebra 𝒪₀ B] (B' : Type) [CommRing B'] [Algebra 𝒪₀ B'] (hB : IsNilpotent (algebraMap 𝒪₀ B π)) (hB' : IsNilpotent (algebraMap 𝒪₀ B' π))
          (φ : B →ₐ[𝒪₀] B') (x : (FormalOmega.AlgFunctor.prod (FormalOmega.AlgFunctor.corep Onr) (FormalOmega.Omega ↥(ValuationSubring.ratClosure A₂) π)).obj B), ΘT ℓ B' hB' ((FormalOmega.AlgFunctor.prod (FormalOmega.AlgFunctor.corep Onr) (FormalOmega.Omega ↥(ValuationSubring.ratClosure A₂) π)).map φ x) = (Scheme.nilpPoints (g₀ ℓ)).map φ (ΘT ℓ B hB x))) ∧

      (∀ (B : Type) [CommRing B] [Algebra 𝒪₀ B] (hB : IsNilpotent (algebraMap 𝒪₀ B π)) (γ : (ℍ[ℚ, a₁, b₁])ˣ), γ ∈ CerednikDrinfeld.CosetGraph.awayUnits R₁ v₂ →
          ∀ x x' : (FormalOmega.AlgFunctor.prod (FormalOmega.AlgFunctor.corep Onr) (FormalOmega.Omega ↥(ValuationSubring.ratClosure A₂) π)).obj B, FormalOmega.OmegaNr.IsTwistedAct π Onr Fr vdet B ((Units.map (ι₂ : ℍ[ℚ, a₁, b₁] →* Matrix (Fin 2) (Fin 2) ↥(ValuationSubring.ratClosure A₂))) γ) x x' → Θ B hB x' = Θ B hB x) ∧
      (∀ ℓ : HeckeTower.AwayPrime q q', (∀ (B : Type) [CommRing B] [Algebra 𝒪₀ B] (hB : IsNilpotent (algebraMap 𝒪₀ B π)) (γ : (ℍ[ℚ, a₁, b₁])ˣ), γ ∈ (CerednikDrinfeld.CosetGraph.awayUnits R₁ v₂ ⊓ (CerednikDrinfeld.CosetGraph.awayUnits R₁ v₂).map (MulAut.conj (s₂ ℓ)).toMonoidHom) →
          ∀ x x' : (FormalOmega.AlgFunctor.prod (FormalOmega.AlgFunctor.corep Onr) (FormalOmega.Omega ↥(ValuationSubring.ratClosure A₂) π)).obj B, FormalOmega.OmegaNr.IsTwistedAct π Onr Fr vdet B ((Units.map (ι₂ : ℍ[ℚ, a₁, b₁] →* Matrix (Fin 2) (Fin 2) ↥(ValuationSubring.ratClosure A₂))) γ) x x' → ΘT ℓ B hB x' = ΘT ℓ B hB x)) ∧

      (∀ (k : Type) [Field k] [IsAlgClosed k] [Algebra 𝒪₀ k] (hk : IsNilpotent (algebraMap 𝒪₀ k π)) (ψ : Onr →ₐ[𝒪₀] k),
          (∀ y : (Scheme.nilpPoints f₀).obj k, ∃ P : (FormalOmega.Omega ↥(ValuationSubring.ratClosure A₂) π).obj k, Θ k hk (ψ, P) = y) ∧
          ∀ P P' : (FormalOmega.Omega ↥(ValuationSubring.ratClosure A₂) π).obj k, Θ k hk (ψ, P) = Θ k hk (ψ, P') ↔
            ∃ γ ∈ CerednikDrinfeld.CosetGraph.awayUnits R₁ v₂, FormalOmega.OmegaNr.IsTwistedAct π Onr Fr vdet k ((Units.map (ι₂ : ℍ[ℚ, a₁, b₁] →* Matrix (Fin 2) (Fin 2) ↥(ValuationSubring.ratClosure A₂))) γ) (ψ, P) (ψ, P')) ∧
      (∀ ℓ : HeckeTower.AwayPrime q q', (∀ (k : Type) [Field k] [IsAlgClosed k] [Algebra 𝒪₀ k] (hk : IsNilpotent (algebraMap 𝒪₀ k π)) (ψ : Onr →ₐ[𝒪₀] k),
          (∀ y : (Scheme.nilpPoints (g₀ ℓ)).obj k, ∃ P : (FormalOmega.Omega ↥(ValuationSubring.ratClosure A₂) π).obj k, ΘT ℓ k hk (ψ, P) = y) ∧
          ∀ P P' : (FormalOmega.Omega ↥(ValuationSubring.ratClosure A₂) π).obj k, ΘT ℓ k hk (ψ, P) = ΘT ℓ k hk (ψ, P') ↔
            ∃ γ ∈ (CerednikDrinfeld.CosetGraph.awayUnits R₁ v₂ ⊓ (CerednikDrinfeld.CosetGraph.awayUnits R₁ v₂).map (MulAut.conj (s₂ ℓ)).toMonoidHom), FormalOmega.OmegaNr.IsTwistedAct π Onr Fr vdet k ((Units.map (ι₂ : ℍ[ℚ, a₁, b₁] →* Matrix (Fin 2) (Fin 2) ↥(ValuationSubring.ratClosure A₂))) γ) (ψ, P) (ψ, P'))) ∧

      (∀ (T : Scheme.{0}) (t : T ⟶ Spec (CommRingCat.of 𝒪₀))
          (ρ : ∀ (B : Type) [CommRing B] [Algebra 𝒪₀ B], IsNilpotent (algebraMap 𝒪₀ B π) → (FormalOmega.AlgFunctor.prod (FormalOmega.AlgFunctor.corep Onr) (FormalOmega.Omega ↥(ValuationSubring.ratClosure A₂) π)).obj B → (Scheme.nilpPoints t).obj B),
          (∀ (B : Type) [CommRing B] [Algebra 𝒪₀ B] (B' : Type) [CommRing B'] [Algebra 𝒪₀ B'] (hB : IsNilpotent (algebraMap 𝒪₀ B π)) (hB' : IsNilpotent (algebraMap 𝒪₀ B' π))
            (φ : B →ₐ[𝒪₀] B') (x : (FormalOmega.AlgFunctor.prod (FormalOmega.AlgFunctor.corep Onr) (FormalOmega.Omega ↥(ValuationSubring.ratClosure A₂) π)).obj B), ρ B' hB' ((FormalOmega.AlgFunctor.prod (FormalOmega.AlgFunctor.corep Onr) (FormalOmega.Omega ↥(ValuationSubring.ratClosure A₂) π)).map φ x) = (Scheme.nilpPoints t).map φ (ρ B hB x)) →
          (∀ (B : Type) [CommRing B] [Algebra 𝒪₀ B] (hB : IsNilpotent (algebraMap 𝒪₀ B π)) (γ : (ℍ[ℚ, a₁, b₁])ˣ), γ ∈ CerednikDrinfeld.CosetGraph.awayUnits R₁ v₂ →
            ∀ x x' : (FormalOmega.AlgFunctor.prod (FormalOmega.AlgFunctor.corep Onr) (FormalOmega.Omega ↥(ValuationSubring.ratClosure A₂) π)).obj B, FormalOmega.OmegaNr.IsTwistedAct π Onr Fr vdet B ((Units.map (ι₂ : ℍ[ℚ, a₁, b₁] →* Matrix (Fin 2) (Fin 2) ↥(ValuationSubring.ratClosure A₂))) γ) x x' → ρ B hB x' = ρ B hB x) →
          ∃ u : ∀ (B : Type) [CommRing B] [Algebra 𝒪₀ B], IsNilpotent (algebraMap 𝒪₀ B π) → (Scheme.nilpPoints f₀).obj B → (Scheme.nilpPoints t).obj B,
            (∀ (B : Type) [CommRing B] [Algebra 𝒪₀ B] (B' : Type) [CommRing B'] [Algebra 𝒪₀ B'] (hB : IsNilpotent (algebraMap 𝒪₀ B π)) (hB' : IsNilpotent (algebraMap 𝒪₀ B' π))
              (φ : B →ₐ[𝒪₀] B') (y : (Scheme.nilpPoints f₀).obj B), u B' hB' ((Scheme.nilpPoints f₀).map φ y) = (Scheme.nilpPoints t).map φ (u B hB y)) ∧
            (∀ (B : Type) [CommRing B] [Algebra 𝒪₀ B] (hB : IsNilpotent (algebraMap 𝒪₀ B π)) (x : (FormalOmega.AlgFunctor.prod (FormalOmega.AlgFunctor.corep Onr) (FormalOmega.Omega ↥(ValuationSubring.ratClosure A₂) π)).obj B), u B hB (Θ B hB x) = ρ B hB x) ∧
            ∀ u' : ∀ (B : Type) [CommRing B] [Algebra 𝒪₀ B], IsNilpotent (algebraMap 𝒪₀ B π) → (Scheme.nilpPoints f₀).obj B → (Scheme.nilpPoints t).obj B,
              (∀ (B : Type) [CommRing B] [Algebra 𝒪₀ B] (B' : Type) [CommRing B'] [Algebra 𝒪₀ B'] (hB : IsNilpotent (algebraMap 𝒪₀ B π)) (hB' : IsNilpotent (algebraMap 𝒪₀ B' π))
                (φ : B →ₐ[𝒪₀] B') (y : (Scheme.nilpPoints f₀).obj B), u' B' hB' ((Scheme.nilpPoints f₀).map φ y) = (Scheme.nilpPoints t).map φ (u' B hB y)) →
              (∀ (B : Type) [CommRing B] [Algebra 𝒪₀ B] (hB : IsNilpotent (algebraMap 𝒪₀ B π)) (x : (FormalOmega.AlgFunctor.prod (FormalOmega.AlgFunctor.corep Onr) (FormalOmega.Omega ↥(ValuationSubring.ratClosure A₂) π)).obj B), u' B hB (Θ B hB x) = ρ B hB x) →
              ∀ (B : Type) [CommRing B] [Algebra 𝒪₀ B] (hB : IsNilpotent (algebraMap 𝒪₀ B π)) (y : (Scheme.nilpPoints f₀).obj B), u' B hB y = u B hB y) ∧
      (∀ ℓ : HeckeTower.AwayPrime q q', (∀ (T : Scheme.{0}) (t : T ⟶ Spec (CommRingCat.of 𝒪₀))
          (ρ : ∀ (B : Type) [CommRing B] [Algebra 𝒪₀ B], IsNilpotent (algebraMap 𝒪₀ B π) → (FormalOmega.AlgFunctor.prod (FormalOmega.AlgFunctor.corep Onr) (FormalOmega.Omega ↥(ValuationSubring.ratClosure A₂) π)).obj B → (Scheme.nilpPoints t).obj B),
          (∀ (B : Type) [CommRing B] [Algebra 𝒪₀ B] (B' : Type) [CommRing B'] [Algebra 𝒪₀ B'] (hB : IsNilpotent (algebraMap 𝒪₀ B π)) (hB' : IsNilpotent (algebraMap 𝒪₀ B' π))
            (φ : B →ₐ[𝒪₀] B') (x : (FormalOmega.AlgFunctor.prod (FormalOmega.AlgFunctor.corep Onr) (FormalOmega.Omega ↥(ValuationSubring.ratClosure A₂) π)).obj B), ρ B' hB' ((FormalOmega.AlgFunctor.prod (FormalOmega.AlgFunctor.corep Onr) (FormalOmega.Omega ↥(ValuationSubring.ratClosure A₂) π)).map φ x) = (Scheme.nilpPoints t).map φ (ρ B hB x)) →
          (∀ (B : Type) [CommRing B] [Algebra 𝒪₀ B] (hB : IsNilpotent (algebraMap 𝒪₀ B π)) (γ : (ℍ[ℚ, a₁, b₁])ˣ), γ ∈ (CerednikDrinfeld.CosetGraph.awayUnits R₁ v₂ ⊓ (CerednikDrinfeld.CosetGraph.awayUnits R₁ v₂).map (MulAut.conj (s₂ ℓ)).toMonoidHom) →
            ∀ x x' : (FormalOmega.AlgFunctor.prod (FormalOmega.AlgFunctor.corep Onr) (FormalOmega.Omega ↥(ValuationSubring.ratClosure A₂) π)).obj B, FormalOmega.OmegaNr.IsTwistedAct π Onr Fr vdet B ((Units.map (ι₂ : ℍ[ℚ, a₁, b₁] →* Matrix (Fin 2) (Fin 2) ↥(ValuationSubring.ratClosure A₂))) γ) x x' → ρ B hB x' = ρ B hB x) →
          ∃ u : ∀ (B : Type) [CommRing B] [Algebra 𝒪₀ B], IsNilpotent (algebraMap 𝒪₀ B π) → (Scheme.nilpPoints (g₀ ℓ)).obj B → (Scheme.nilpPoints t).obj B,
            (∀ (B : Type) [CommRing B] [Algebra 𝒪₀ B] (B' : Type) [CommRing B'] [Algebra 𝒪₀ B'] (hB : IsNilpotent (algebraMap 𝒪₀ B π)) (hB' : IsNilpotent (algebraMap 𝒪₀ B' π))
              (φ : B →ₐ[𝒪₀] B') (y : (Scheme.nilpPoints (g₀ ℓ)).obj B), u B' hB' ((Scheme.nilpPoints (g₀ ℓ)).map φ y) = (Scheme.nilpPoints t).map φ (u B hB y)) ∧
            (∀ (B : Type) [CommRing B] [Algebra 𝒪₀ B] (hB : IsNilpotent (algebraMap 𝒪₀ B π)) (x : (FormalOmega.AlgFunctor.prod (FormalOmega.AlgFunctor.corep Onr) (FormalOmega.Omega ↥(ValuationSubring.ratClosure A₂) π)).obj B), u B hB (ΘT ℓ B hB x) = ρ B hB x) ∧
            ∀ u' : ∀ (B : Type) [CommRing B] [Algebra 𝒪₀ B], IsNilpotent (algebraMap 𝒪₀ B π) → (Scheme.nilpPoints (g₀ ℓ)).obj B → (Scheme.nilpPoints t).obj B,
              (∀ (B : Type) [CommRing B] [Algebra 𝒪₀ B] (B' : Type) [CommRing B'] [Algebra 𝒪₀ B'] (hB : IsNilpotent (algebraMap 𝒪₀ B π)) (hB' : IsNilpotent (algebraMap 𝒪₀ B' π))
                (φ : B →ₐ[𝒪₀] B') (y : (Scheme.nilpPoints (g₀ ℓ)).obj B), u' B' hB' ((Scheme.nilpPoints (g₀ ℓ)).map φ y) = (Scheme.nilpPoints t).map φ (u' B hB y)) →
              (∀ (B : Type) [CommRing B] [Algebra 𝒪₀ B] (hB : IsNilpotent (algebraMap 𝒪₀ B π)) (x : (FormalOmega.AlgFunctor.prod (FormalOmega.AlgFunctor.corep Onr) (FormalOmega.Omega ↥(ValuationSubring.ratClosure A₂) π)).obj B), u' B hB (ΘT ℓ B hB x) = ρ B hB x) →
              ∀ (B : Type) [CommRing B] [Algebra 𝒪₀ B] (hB : IsNilpotent (algebraMap 𝒪₀ B π)) (y : (Scheme.nilpPoints (g₀ ℓ)).obj B), u' B hB y = u B hB y)) ∧

      (∀ (ℓ : HeckeTower.AwayPrime q q') (B : Type) [CommRing B] [Algebra 𝒪₀ B] (hB : IsNilpotent (algebraMap 𝒪₀ B π)) (x : (FormalOmega.AlgFunctor.prod (FormalOmega.AlgFunctor.corep Onr) (FormalOmega.Omega ↥(ValuationSubring.ratClosure A₂) π)).obj B),
        (Scheme.nilpPoints.mapHom (g₀ ℓ) f₀ (d₀₀ ℓ) (hd₀f ℓ)).app B (ΘT ℓ B hB x) = Θ B hB x) ∧
      (∀ (ℓ : HeckeTower.AwayPrime q q') (B : Type) [CommRing B] [Algebra 𝒪₀ B] (hB : IsNilpotent (algebraMap 𝒪₀ B π)) (x x' : (FormalOmega.AlgFunctor.prod (FormalOmega.AlgFunctor.corep Onr) (FormalOmega.Omega ↥(ValuationSubring.ratClosure A₂) π)).obj B),
        FormalOmega.OmegaNr.IsTwistedAct π Onr Fr vdet B ((Units.map (ι₂ : ℍ[ℚ, a₁, b₁] →* Matrix (Fin 2) (Fin 2) ↥(ValuationSubring.ratClosure A₂))) (s₂ ℓ)) x' x →
        (Scheme.nilpPoints.mapHom (g₀ ℓ) f₀ (d₁₀ ℓ) (hd₁f ℓ)).app B (ΘT ℓ B hB x) = Θ B hB x') ∧

      (∀ (B : Type) [CommRing B] [Algebra 𝒪₀ B] (hB : IsNilpotent (algebraMap 𝒪₀ B π)) (x : (FormalOmega.AlgFunctor.prod (FormalOmega.AlgFunctor.corep Onr) (FormalOmega.Omega ↥(ValuationSubring.ratClosure A₂) π)).obj B),
        (Scheme.nilpPoints.mapHom f₀ f₀ ar harf).app B (Θ B hB x) = Θ B hB (FormalOmega.frobTwist Onr Fr 1 x.1, x.2)) ∧
      (∀ (B : Type) [CommRing B] [Algebra 𝒪₀ B] (hB : IsNilpotent (algebraMap 𝒪₀ B π)) (x x' : (FormalOmega.AlgFunctor.prod (FormalOmega.AlgFunctor.corep Onr) (FormalOmega.Omega ↥(ValuationSubring.ratClosure A₂) π)).obj B), FormalOmega.OmegaNr.IsTwistedAct π Onr Fr vdet B ((Units.map (ι₂ : ℍ[ℚ, a₁, b₁] →* Matrix (Fin 2) (Fin 2) ↥(ValuationSubring.ratClosure A₂))) (wbar₂ none)) x x' →
        (Scheme.nilpPoints.mapHom f₀ f₀ arbar harbarf).app B (Θ B hB x) = Θ B hB x'))
    [hXCint : IsIntegral (Limits.pullback f₀ (Spec.map (CommRingCat.ofHom ((algebraMap ↥(ValuationSubring.ratClosure A₂) A₂.valuation.Completion).comp (algebraMap 𝒪₀ ↥(ValuationSubring.ratClosure A₂))))))]
    [hYCint : ∀ ℓ : HeckeTower.AwayPrime q q', IsIntegral (Limits.pullback (g₀ ℓ) (Spec.map (CommRingCat.ofHom ((algebraMap ↥(ValuationSubring.ratClosure A₂) A₂.valuation.Completion).comp (algebraMap 𝒪₀ ↥(ValuationSubring.ratClosure A₂))))))]
    (hGF :
    ∃ _ : IsIntegral (Limits.pullback f₀ (Spec.map (CommRingCat.ofHom ((algebraMap ↥(ValuationSubring.ratClosure A₂) A₂.valuation.Completion).comp (algebraMap 𝒪₀ ↥(ValuationSubring.ratClosure A₂)))))),
    ∃ e : ↑(Limits.pullback f₀ (Spec.map (CommRingCat.ofHom ((algebraMap ↥(ValuationSubring.ratClosure A₂) A₂.valuation.Completion).comp (algebraMap 𝒪₀ ↥(ValuationSubring.ratClosure A₂)))))).functionField ≃+* ↥(Mumford.invariantFieldOf A₂.valuation.Completion (ℍ[ℚ, a₁, b₁])ˣ (Omega.HolRingOf ϖ₂ ρ₂) (Γ₂ none)),

      (∀ c : A₂.valuation.Completion, e (AlgebraicCurve.baseToFunctionField (Limits.pullback.snd f₀ (Spec.map (CommRingCat.ofHom ((algebraMap ↥(ValuationSubring.ratClosure A₂) A₂.valuation.Completion).comp (algebraMap 𝒪₀ ↥(ValuationSubring.ratClosure A₂)))))) c) =
        algebraMap A₂.valuation.Completion ↥(Mumford.invariantFieldOf A₂.valuation.Completion (ℍ[ℚ, a₁, b₁])ˣ (Omega.HolRingOf ϖ₂ ρ₂) (Γ₂ none)) c) ∧

      (∀ (aX : 𝒳₀ ⟶ 𝒳₀) (haX : aX ≫ f₀ = f₀) (g : (ℍ[ℚ, a₁, b₁])ˣ), vdet ((Units.map (ι₂ : ℍ[ℚ, a₁, b₁] →* Matrix (Fin 2) (Fin 2) ↥(ValuationSubring.ratClosure A₂))) g) = 1 →
        (∀ (B : Type) [CommRing B] [Algebra 𝒪₀ B] (hB : IsNilpotent (algebraMap 𝒪₀ B π))
            (x x' : (CerednikDrinfeld.FormalOmega.AlgFunctor.prod (CerednikDrinfeld.FormalOmega.AlgFunctor.corep Onr) (CerednikDrinfeld.FormalOmega.Omega ↥(ValuationSubring.ratClosure A₂) π)).obj B),
            CerednikDrinfeld.FormalOmega.OmegaNr.IsTwistedAct π Onr Fr vdet B ((Units.map (ι₂ : ℍ[ℚ, a₁, b₁] →* Matrix (Fin 2) (Fin 2) ↥(ValuationSubring.ratClosure A₂))) g) x x' → (Scheme.nilpPoints.mapHom f₀ f₀ aX haX).app B (Θ B hB x) = Θ B hB x') →
        ∀ (aXC : Limits.pullback f₀ (Spec.map (CommRingCat.ofHom ((algebraMap ↥(ValuationSubring.ratClosure A₂) A₂.valuation.Completion).comp (algebraMap 𝒪₀ ↥(ValuationSubring.ratClosure A₂))))) ⟶ Limits.pullback f₀ (Spec.map (CommRingCat.ofHom ((algebraMap ↥(ValuationSubring.ratClosure A₂) A₂.valuation.Completion).comp (algebraMap 𝒪₀ ↥(ValuationSubring.ratClosure A₂)))))),
          aXC ≫ Limits.pullback.fst f₀ (Spec.map (CommRingCat.ofHom ((algebraMap ↥(ValuationSubring.ratClosure A₂) A₂.valuation.Completion).comp (algebraMap 𝒪₀ ↥(ValuationSubring.ratClosure A₂))))) = Limits.pullback.fst f₀ (Spec.map (CommRingCat.ofHom ((algebraMap ↥(ValuationSubring.ratClosure A₂) A₂.valuation.Completion).comp (algebraMap 𝒪₀ ↥(ValuationSubring.ratClosure A₂))))) ≫ aX → aXC ≫ Limits.pullback.snd f₀ (Spec.map (CommRingCat.ofHom ((algebraMap ↥(ValuationSubring.ratClosure A₂) A₂.valuation.Completion).comp (algebraMap 𝒪₀ ↥(ValuationSubring.ratClosure A₂))))) = Limits.pullback.snd f₀ (Spec.map (CommRingCat.ofHom ((algebraMap ↥(ValuationSubring.ratClosure A₂) A₂.valuation.Completion).comp (algebraMap 𝒪₀ ↥(ValuationSubring.ratClosure A₂))))) →
        ∀ (U : (Limits.pullback f₀ (Spec.map (CommRingCat.ofHom ((algebraMap ↥(ValuationSubring.ratClosure A₂) A₂.valuation.Completion).comp (algebraMap 𝒪₀ ↥(ValuationSubring.ratClosure A₂)))))).Opens) (hU : genericPoint (Limits.pullback f₀ (Spec.map (CommRingCat.ofHom ((algebraMap ↥(ValuationSubring.ratClosure A₂) A₂.valuation.Completion).comp (algebraMap 𝒪₀ ↥(ValuationSubring.ratClosure A₂))))) : Scheme.{0}) ∈ U)
          (hU' : genericPoint (Limits.pullback f₀ (Spec.map (CommRingCat.ofHom ((algebraMap ↥(ValuationSubring.ratClosure A₂) A₂.valuation.Completion).comp (algebraMap 𝒪₀ ↥(ValuationSubring.ratClosure A₂))))) : Scheme.{0}) ∈ aXC ⁻¹ᵁ U) (s : (Limits.pullback f₀ (Spec.map (CommRingCat.ofHom ((algebraMap ↥(ValuationSubring.ratClosure A₂) A₂.valuation.Completion).comp (algebraMap 𝒪₀ ↥(ValuationSubring.ratClosure A₂)))))).presheaf.obj (Opposite.op U)),
          ((e (((Limits.pullback f₀ (Spec.map (CommRingCat.ofHom ((algebraMap ↥(ValuationSubring.ratClosure A₂) A₂.valuation.Completion).comp (algebraMap 𝒪₀ ↥(ValuationSubring.ratClosure A₂)))))).presheaf.germ (aXC ⁻¹ᵁ U) (genericPoint (Limits.pullback f₀ (Spec.map (CommRingCat.ofHom ((algebraMap ↥(ValuationSubring.ratClosure A₂) A₂.valuation.Completion).comp (algebraMap 𝒪₀ ↥(ValuationSubring.ratClosure A₂))))) : Scheme.{0})) hU').hom ((aXC.app U).hom s)) :
              ↥(Mumford.invariantFieldOf A₂.valuation.Completion (ℍ[ℚ, a₁, b₁])ˣ (Omega.HolRingOf ϖ₂ ρ₂) (Γ₂ none))) : FractionRing (Omega.HolRingOf ϖ₂ ρ₂)) =
            g⁻¹ • ((e (((Limits.pullback f₀ (Spec.map (CommRingCat.ofHom ((algebraMap ↥(ValuationSubring.ratClosure A₂) A₂.valuation.Completion).comp (algebraMap 𝒪₀ ↥(ValuationSubring.ratClosure A₂)))))).presheaf.germ U (genericPoint (Limits.pullback f₀ (Spec.map (CommRingCat.ofHom ((algebraMap ↥(ValuationSubring.ratClosure A₂) A₂.valuation.Completion).comp (algebraMap 𝒪₀ ↥(ValuationSubring.ratClosure A₂))))) : Scheme.{0})) hU).hom s) :
              ↥(Mumford.invariantFieldOf A₂.valuation.Completion (ℍ[ℚ, a₁, b₁])ˣ (Omega.HolRingOf ϖ₂ ρ₂) (Γ₂ none))) : FractionRing (Omega.HolRingOf ϖ₂ ρ₂))) ∧

      (∀ (bX : 𝒳₀ ⟶ 𝒳₀) (hbX : bX ≫ f₀ = f₀),
        (∀ (B : Type) [CommRing B] [Algebra 𝒪₀ B] (hB : IsNilpotent (algebraMap 𝒪₀ B π))
            (x : (CerednikDrinfeld.FormalOmega.AlgFunctor.prod (CerednikDrinfeld.FormalOmega.AlgFunctor.corep Onr) (CerednikDrinfeld.FormalOmega.Omega ↥(ValuationSubring.ratClosure A₂) π)).obj B),
            (Scheme.nilpPoints.mapHom f₀ f₀ bX hbX).app B (Θ B hB x) = Θ B hB (CerednikDrinfeld.FormalOmega.frobTwist Onr Fr 1 x.1, x.2)) →
        ∀ (bXC : Limits.pullback f₀ (Spec.map (CommRingCat.ofHom ((algebraMap ↥(ValuationSubring.ratClosure A₂) A₂.valuation.Completion).comp (algebraMap 𝒪₀ ↥(ValuationSubring.ratClosure A₂))))) ⟶ Limits.pullback f₀ (Spec.map (CommRingCat.ofHom ((algebraMap ↥(ValuationSubring.ratClosure A₂) A₂.valuation.Completion).comp (algebraMap 𝒪₀ ↥(ValuationSubring.ratClosure A₂)))))),
          bXC ≫ Limits.pullback.fst f₀ (Spec.map (CommRingCat.ofHom ((algebraMap ↥(ValuationSubring.ratClosure A₂) A₂.valuation.Completion).comp (algebraMap 𝒪₀ ↥(ValuationSubring.ratClosure A₂))))) = Limits.pullback.fst f₀ (Spec.map (CommRingCat.ofHom ((algebraMap ↥(ValuationSubring.ratClosure A₂) A₂.valuation.Completion).comp (algebraMap 𝒪₀ ↥(ValuationSubring.ratClosure A₂))))) ≫ bX → bXC ≫ Limits.pullback.snd f₀ (Spec.map (CommRingCat.ofHom ((algebraMap ↥(ValuationSubring.ratClosure A₂) A₂.valuation.Completion).comp (algebraMap 𝒪₀ ↥(ValuationSubring.ratClosure A₂))))) = Limits.pullback.snd f₀ (Spec.map (CommRingCat.ofHom ((algebraMap ↥(ValuationSubring.ratClosure A₂) A₂.valuation.Completion).comp (algebraMap 𝒪₀ ↥(ValuationSubring.ratClosure A₂))))) →
        ∀ (w : (ℍ[ℚ, a₁, b₁])ˣ), w ∈ (CerednikDrinfeld.CosetGraph.awayUnits R₁ v₂) → vdet ((Units.map (ι₂ : ℍ[ℚ, a₁, b₁] →* Matrix (Fin 2) (Fin 2) ↥(ValuationSubring.ratClosure A₂))) w) = Multiplicative.ofAdd (1 : ℤ) →
        ∀ (U : (Limits.pullback f₀ (Spec.map (CommRingCat.ofHom ((algebraMap ↥(ValuationSubring.ratClosure A₂) A₂.valuation.Completion).comp (algebraMap 𝒪₀ ↥(ValuationSubring.ratClosure A₂)))))).Opens) (hU : genericPoint (Limits.pullback f₀ (Spec.map (CommRingCat.ofHom ((algebraMap ↥(ValuationSubring.ratClosure A₂) A₂.valuation.Completion).comp (algebraMap 𝒪₀ ↥(ValuationSubring.ratClosure A₂))))) : Scheme.{0}) ∈ U)
          (hU' : genericPoint (Limits.pullback f₀ (Spec.map (CommRingCat.ofHom ((algebraMap ↥(ValuationSubring.ratClosure A₂) A₂.valuation.Completion).comp (algebraMap 𝒪₀ ↥(ValuationSubring.ratClosure A₂))))) : Scheme.{0}) ∈ bXC ⁻¹ᵁ U) (s : (Limits.pullback f₀ (Spec.map (CommRingCat.ofHom ((algebraMap ↥(ValuationSubring.ratClosure A₂) A₂.valuation.Completion).comp (algebraMap 𝒪₀ ↥(ValuationSubring.ratClosure A₂)))))).presheaf.obj (Opposite.op U)),
          ((e (((Limits.pullback f₀ (Spec.map (CommRingCat.ofHom ((algebraMap ↥(ValuationSubring.ratClosure A₂) A₂.valuation.Completion).comp (algebraMap 𝒪₀ ↥(ValuationSubring.ratClosure A₂)))))).presheaf.germ (bXC ⁻¹ᵁ U) (genericPoint (Limits.pullback f₀ (Spec.map (CommRingCat.ofHom ((algebraMap ↥(ValuationSubring.ratClosure A₂) A₂.valuation.Completion).comp (algebraMap 𝒪₀ ↥(ValuationSubring.ratClosure A₂))))) : Scheme.{0})) hU').hom ((bXC.app U).hom s)) :
              ↥(Mumford.invariantFieldOf A₂.valuation.Completion (ℍ[ℚ, a₁, b₁])ˣ (Omega.HolRingOf ϖ₂ ρ₂) (Γ₂ none))) : FractionRing (Omega.HolRingOf ϖ₂ ρ₂)) =
            w⁻¹ • ((e (((Limits.pullback f₀ (Spec.map (CommRingCat.ofHom ((algebraMap ↥(ValuationSubring.ratClosure A₂) A₂.valuation.Completion).comp (algebraMap 𝒪₀ ↥(ValuationSubring.ratClosure A₂)))))).presheaf.germ U (genericPoint (Limits.pullback f₀ (Spec.map (CommRingCat.ofHom ((algebraMap ↥(ValuationSubring.ratClosure A₂) A₂.valuation.Completion).comp (algebraMap 𝒪₀ ↥(ValuationSubring.ratClosure A₂))))) : Scheme.{0})) hU).hom s) :
              ↥(Mumford.invariantFieldOf A₂.valuation.Completion (ℍ[ℚ, a₁, b₁])ˣ (Omega.HolRingOf ϖ₂ ρ₂) (Γ₂ none))) : FractionRing (Omega.HolRingOf ϖ₂ ρ₂))) ∧

      (∀ (s : Omega.IsometricAut ↥(ValuationSubring.ratClosure A₂) A₂.valuation.Completion) (n : ℤ),
        (∀ y : Onr, Fr (Fr y) = y → s.toRingEquiv (ψ₀ y) = ψ₀ ((Fr ^ n : Onr ≃ₐ[𝒪₀] Onr) y)) →
        ∀ (tC : Limits.pullback f₀ (Spec.map (CommRingCat.ofHom ((algebraMap ↥(ValuationSubring.ratClosure A₂) A₂.valuation.Completion).comp (algebraMap 𝒪₀ ↥(ValuationSubring.ratClosure A₂))))) ⟶ Limits.pullback f₀ (Spec.map (CommRingCat.ofHom ((algebraMap ↥(ValuationSubring.ratClosure A₂) A₂.valuation.Completion).comp (algebraMap 𝒪₀ ↥(ValuationSubring.ratClosure A₂)))))),
          tC ≫ Limits.pullback.fst f₀ (Spec.map (CommRingCat.ofHom ((algebraMap ↥(ValuationSubring.ratClosure A₂) A₂.valuation.Completion).comp (algebraMap 𝒪₀ ↥(ValuationSubring.ratClosure A₂))))) = Limits.pullback.fst f₀ (Spec.map (CommRingCat.ofHom ((algebraMap ↥(ValuationSubring.ratClosure A₂) A₂.valuation.Completion).comp (algebraMap 𝒪₀ ↥(ValuationSubring.ratClosure A₂))))) →
          tC ≫ Limits.pullback.snd f₀ (Spec.map (CommRingCat.ofHom ((algebraMap ↥(ValuationSubring.ratClosure A₂) A₂.valuation.Completion).comp (algebraMap 𝒪₀ ↥(ValuationSubring.ratClosure A₂))))) = Limits.pullback.snd f₀ (Spec.map (CommRingCat.ofHom ((algebraMap ↥(ValuationSubring.ratClosure A₂) A₂.valuation.Completion).comp (algebraMap 𝒪₀ ↥(ValuationSubring.ratClosure A₂))))) ≫ Spec.map (CommRingCat.ofHom (s.toRingEquiv : A₂.valuation.Completion →+* A₂.valuation.Completion)) →
        ∀ (w : (ℍ[ℚ, a₁, b₁])ˣ), w ∈ (CerednikDrinfeld.CosetGraph.awayUnits R₁ v₂) → vdet ((Units.map (ι₂ : ℍ[ℚ, a₁, b₁] →* Matrix (Fin 2) (Fin 2) ↥(ValuationSubring.ratClosure A₂))) w) = Multiplicative.ofAdd (1 : ℤ) →
        ∀ (U : (Limits.pullback f₀ (Spec.map (CommRingCat.ofHom ((algebraMap ↥(ValuationSubring.ratClosure A₂) A₂.valuation.Completion).comp (algebraMap 𝒪₀ ↥(ValuationSubring.ratClosure A₂)))))).Opens) (hU : genericPoint (Limits.pullback f₀ (Spec.map (CommRingCat.ofHom ((algebraMap ↥(ValuationSubring.ratClosure A₂) A₂.valuation.Completion).comp (algebraMap 𝒪₀ ↥(ValuationSubring.ratClosure A₂))))) : Scheme.{0}) ∈ U)
          (hU' : genericPoint (Limits.pullback f₀ (Spec.map (CommRingCat.ofHom ((algebraMap ↥(ValuationSubring.ratClosure A₂) A₂.valuation.Completion).comp (algebraMap 𝒪₀ ↥(ValuationSubring.ratClosure A₂))))) : Scheme.{0}) ∈ tC ⁻¹ᵁ U) (sec : (Limits.pullback f₀ (Spec.map (CommRingCat.ofHom ((algebraMap ↥(ValuationSubring.ratClosure A₂) A₂.valuation.Completion).comp (algebraMap 𝒪₀ ↥(ValuationSubring.ratClosure A₂)))))).presheaf.obj (Opposite.op U)),
          ((e (((Limits.pullback f₀ (Spec.map (CommRingCat.ofHom ((algebraMap ↥(ValuationSubring.ratClosure A₂) A₂.valuation.Completion).comp (algebraMap 𝒪₀ ↥(ValuationSubring.ratClosure A₂)))))).presheaf.germ (tC ⁻¹ᵁ U) (genericPoint (Limits.pullback f₀ (Spec.map (CommRingCat.ofHom ((algebraMap ↥(ValuationSubring.ratClosure A₂) A₂.valuation.Completion).comp (algebraMap 𝒪₀ ↥(ValuationSubring.ratClosure A₂))))) : Scheme.{0})) hU').hom ((tC.app U).hom sec)) :
              ↥(Mumford.invariantFieldOf A₂.valuation.Completion (ℍ[ℚ, a₁, b₁])ˣ (Omega.HolRingOf ϖ₂ ρ₂) (Γ₂ none))) : FractionRing (Omega.HolRingOf ϖ₂ ρ₂)) =
            w ^ n • Mumford.AmbientSemilinearAut.fracMap (Omega.toAmbientOf ϖ₂ ρ₂ s)
              ((e (((Limits.pullback f₀ (Spec.map (CommRingCat.ofHom ((algebraMap ↥(ValuationSubring.ratClosure A₂) A₂.valuation.Completion).comp (algebraMap 𝒪₀ ↥(ValuationSubring.ratClosure A₂)))))).presheaf.germ U (genericPoint (Limits.pullback f₀ (Spec.map (CommRingCat.ofHom ((algebraMap ↥(ValuationSubring.ratClosure A₂) A₂.valuation.Completion).comp (algebraMap 𝒪₀ ↥(ValuationSubring.ratClosure A₂))))) : Scheme.{0})) hU).hom sec) :
                ↥(Mumford.invariantFieldOf A₂.valuation.Completion (ℍ[ℚ, a₁, b₁])ˣ (Omega.HolRingOf ϖ₂ ρ₂) (Γ₂ none))) : FractionRing (Omega.HolRingOf ϖ₂ ρ₂))) ∧

      (∀ i : (HeckeTower.AwayPrime q q'), ∃ _ : IsIntegral (Limits.pullback (g₀ i) (Spec.map (CommRingCat.ofHom ((algebraMap ↥(ValuationSubring.ratClosure A₂) A₂.valuation.Completion).comp (algebraMap 𝒪₀ ↥(ValuationSubring.ratClosure A₂)))))),
        ∃ eY : ↑(Limits.pullback (g₀ i) (Spec.map (CommRingCat.ofHom ((algebraMap ↥(ValuationSubring.ratClosure A₂) A₂.valuation.Completion).comp (algebraMap 𝒪₀ ↥(ValuationSubring.ratClosure A₂)))))).functionField ≃+* ↥(Mumford.invariantFieldOf A₂.valuation.Completion (ℍ[ℚ, a₁, b₁])ˣ (Omega.HolRingOf ϖ₂ ρ₂) ((fun ℓ => Γ₂ (some ℓ)) i)),
          (∀ c : A₂.valuation.Completion, eY (AlgebraicCurve.baseToFunctionField (Limits.pullback.snd (g₀ i) (Spec.map (CommRingCat.ofHom ((algebraMap ↥(ValuationSubring.ratClosure A₂) A₂.valuation.Completion).comp (algebraMap 𝒪₀ ↥(ValuationSubring.ratClosure A₂)))))) c) =
            algebraMap A₂.valuation.Completion ↥(Mumford.invariantFieldOf A₂.valuation.Completion (ℍ[ℚ, a₁, b₁])ˣ (Omega.HolRingOf ϖ₂ ρ₂) ((fun ℓ => Γ₂ (some ℓ)) i)) c) ∧
          (∀ (h : 𝒴₀ i ⟶ 𝒳₀) (hhf : h ≫ f₀ = g₀ i) (g : (ℍ[ℚ, a₁, b₁])ˣ), vdet ((Units.map (ι₂ : ℍ[ℚ, a₁, b₁] →* Matrix (Fin 2) (Fin 2) ↥(ValuationSubring.ratClosure A₂))) g) = 1 →
            (∀ (B : Type) [CommRing B] [Algebra 𝒪₀ B] (hB : IsNilpotent (algebraMap 𝒪₀ B π))
                (x x' : (CerednikDrinfeld.FormalOmega.AlgFunctor.prod (CerednikDrinfeld.FormalOmega.AlgFunctor.corep Onr) (CerednikDrinfeld.FormalOmega.Omega ↥(ValuationSubring.ratClosure A₂) π)).obj B),
                CerednikDrinfeld.FormalOmega.OmegaNr.IsTwistedAct π Onr Fr vdet B ((Units.map (ι₂ : ℍ[ℚ, a₁, b₁] →* Matrix (Fin 2) (Fin 2) ↥(ValuationSubring.ratClosure A₂))) g) x x' →
                  (Scheme.nilpPoints.mapHom (g₀ i) f₀ h hhf).app B (ΘT i B hB x) = Θ B hB x') →
            ∀ (hC : Limits.pullback (g₀ i) (Spec.map (CommRingCat.ofHom ((algebraMap ↥(ValuationSubring.ratClosure A₂) A₂.valuation.Completion).comp (algebraMap 𝒪₀ ↥(ValuationSubring.ratClosure A₂))))) ⟶ Limits.pullback f₀ (Spec.map (CommRingCat.ofHom ((algebraMap ↥(ValuationSubring.ratClosure A₂) A₂.valuation.Completion).comp (algebraMap 𝒪₀ ↥(ValuationSubring.ratClosure A₂)))))),
              hC ≫ Limits.pullback.fst f₀ (Spec.map (CommRingCat.ofHom ((algebraMap ↥(ValuationSubring.ratClosure A₂) A₂.valuation.Completion).comp (algebraMap 𝒪₀ ↥(ValuationSubring.ratClosure A₂))))) = Limits.pullback.fst (g₀ i) (Spec.map (CommRingCat.ofHom ((algebraMap ↥(ValuationSubring.ratClosure A₂) A₂.valuation.Completion).comp (algebraMap 𝒪₀ ↥(ValuationSubring.ratClosure A₂))))) ≫ h →
              hC ≫ Limits.pullback.snd f₀ (Spec.map (CommRingCat.ofHom ((algebraMap ↥(ValuationSubring.ratClosure A₂) A₂.valuation.Completion).comp (algebraMap 𝒪₀ ↥(ValuationSubring.ratClosure A₂))))) = Limits.pullback.snd (g₀ i) (Spec.map (CommRingCat.ofHom ((algebraMap ↥(ValuationSubring.ratClosure A₂) A₂.valuation.Completion).comp (algebraMap 𝒪₀ ↥(ValuationSubring.ratClosure A₂))))) →
            ∀ (U : (Limits.pullback f₀ (Spec.map (CommRingCat.ofHom ((algebraMap ↥(ValuationSubring.ratClosure A₂) A₂.valuation.Completion).comp (algebraMap 𝒪₀ ↥(ValuationSubring.ratClosure A₂)))))).Opens) (hU : genericPoint (Limits.pullback f₀ (Spec.map (CommRingCat.ofHom ((algebraMap ↥(ValuationSubring.ratClosure A₂) A₂.valuation.Completion).comp (algebraMap 𝒪₀ ↥(ValuationSubring.ratClosure A₂))))) : Scheme.{0}) ∈ U)
              (hU' : genericPoint (Limits.pullback (g₀ i) (Spec.map (CommRingCat.ofHom ((algebraMap ↥(ValuationSubring.ratClosure A₂) A₂.valuation.Completion).comp (algebraMap 𝒪₀ ↥(ValuationSubring.ratClosure A₂))))) : Scheme.{0}) ∈ hC ⁻¹ᵁ U)
              (sec : (Limits.pullback f₀ (Spec.map (CommRingCat.ofHom ((algebraMap ↥(ValuationSubring.ratClosure A₂) A₂.valuation.Completion).comp (algebraMap 𝒪₀ ↥(ValuationSubring.ratClosure A₂)))))).presheaf.obj (Opposite.op U)),
              ((eY (((Limits.pullback (g₀ i) (Spec.map (CommRingCat.ofHom ((algebraMap ↥(ValuationSubring.ratClosure A₂) A₂.valuation.Completion).comp (algebraMap 𝒪₀ ↥(ValuationSubring.ratClosure A₂)))))).presheaf.germ (hC ⁻¹ᵁ U) (genericPoint (Limits.pullback (g₀ i) (Spec.map (CommRingCat.ofHom ((algebraMap ↥(ValuationSubring.ratClosure A₂) A₂.valuation.Completion).comp (algebraMap 𝒪₀ ↥(ValuationSubring.ratClosure A₂))))) : Scheme.{0})) hU').hom
                  ((hC.app U).hom sec)) : ↥(Mumford.invariantFieldOf A₂.valuation.Completion (ℍ[ℚ, a₁, b₁])ˣ (Omega.HolRingOf ϖ₂ ρ₂) ((fun ℓ => Γ₂ (some ℓ)) i))) : FractionRing (Omega.HolRingOf ϖ₂ ρ₂)) =
                g⁻¹ • ((e (((Limits.pullback f₀ (Spec.map (CommRingCat.ofHom ((algebraMap ↥(ValuationSubring.ratClosure A₂) A₂.valuation.Completion).comp (algebraMap 𝒪₀ ↥(ValuationSubring.ratClosure A₂)))))).presheaf.germ U (genericPoint (Limits.pullback f₀ (Spec.map (CommRingCat.ofHom ((algebraMap ↥(ValuationSubring.ratClosure A₂) A₂.valuation.Completion).comp (algebraMap 𝒪₀ ↥(ValuationSubring.ratClosure A₂))))) : Scheme.{0})) hU).hom sec) :
                  ↥(Mumford.invariantFieldOf A₂.valuation.Completion (ℍ[ℚ, a₁, b₁])ˣ (Omega.HolRingOf ϖ₂ ρ₂) (Γ₂ none))) : FractionRing (Omega.HolRingOf ϖ₂ ρ₂)))))

    (j : Fbar →+* ↑(Limits.pullback f₀ (Spec.map (CommRingCat.ofHom ((algebraMap ↥(ValuationSubring.ratClosure A₂) A₂.valuation.Completion).comp (algebraMap 𝒪₀ ↥(ValuationSubring.ratClosure A₂)))))).functionField)
    (hj :

      (∀ z : AlgebraicClosure ℚ, j (algebraMap (AlgebraicClosure ℚ) Fbar z) = (AlgebraicCurve.baseToFunctionField (Limits.pullback.snd f₀ (Spec.map (CommRingCat.ofHom ((algebraMap ↥(ValuationSubring.ratClosure A₂) A₂.valuation.Completion).comp (algebraMap 𝒪₀ ↥(ValuationSubring.ratClosure A₂))))))) ((z : AlgebraicClosure ℚ) : A₂.valuation.Completion)) ∧

      (Subfield.closure (Set.range (AlgebraicCurve.baseToFunctionField (Limits.pullback.snd f₀ (Spec.map (CommRingCat.ofHom ((algebraMap ↥(ValuationSubring.ratClosure A₂) A₂.valuation.Completion).comp (algebraMap 𝒪₀ ↥(ValuationSubring.ratClosure A₂))))))) ∪ Set.range j) = ⊤) ∧

      (∀ (t : Finset Fbar), LinearIndependent (AlgebraicClosure ℚ) (fun x : t => (x : Fbar)) →
        ∀ c : t → A₂.valuation.Completion, (∑ x : t, (AlgebraicCurve.baseToFunctionField (Limits.pullback.snd f₀ (Spec.map (CommRingCat.ofHom ((algebraMap ↥(ValuationSubring.ratClosure A₂) A₂.valuation.Completion).comp (algebraMap 𝒪₀ ↥(ValuationSubring.ratClosure A₂))))))) (c x) * j (x : Fbar)) = 0 → ∀ x : t, c x = 0) ∧

      (∀ (aXC : (Limits.pullback f₀ (Spec.map (CommRingCat.ofHom ((algebraMap ↥(ValuationSubring.ratClosure A₂) A₂.valuation.Completion).comp (algebraMap 𝒪₀ ↥(ValuationSubring.ratClosure A₂)))))) ⟶ (Limits.pullback f₀ (Spec.map (CommRingCat.ofHom ((algebraMap ↥(ValuationSubring.ratClosure A₂) A₂.valuation.Completion).comp (algebraMap 𝒪₀ ↥(ValuationSubring.ratClosure A₂))))))), aXC ≫ Limits.pullback.fst f₀ (Spec.map (CommRingCat.ofHom ((algebraMap ↥(ValuationSubring.ratClosure A₂) A₂.valuation.Completion).comp (algebraMap 𝒪₀ ↥(ValuationSubring.ratClosure A₂))))) = Limits.pullback.fst f₀ (Spec.map (CommRingCat.ofHom ((algebraMap ↥(ValuationSubring.ratClosure A₂) A₂.valuation.Completion).comp (algebraMap 𝒪₀ ↥(ValuationSubring.ratClosure A₂))))) ≫ ar →
        aXC ≫ Limits.pullback.snd f₀ (Spec.map (CommRingCat.ofHom ((algebraMap ↥(ValuationSubring.ratClosure A₂) A₂.valuation.Completion).comp (algebraMap 𝒪₀ ↥(ValuationSubring.ratClosure A₂))))) = Limits.pullback.snd f₀ (Spec.map (CommRingCat.ofHom ((algebraMap ↥(ValuationSubring.ratClosure A₂) A₂.valuation.Completion).comp (algebraMap 𝒪₀ ↥(ValuationSubring.ratClosure A₂))))) →
        ∀ x : Fbar, ∀ (U : (Limits.pullback f₀ (Spec.map (CommRingCat.ofHom ((algebraMap ↥(ValuationSubring.ratClosure A₂) A₂.valuation.Completion).comp (algebraMap 𝒪₀ ↥(ValuationSubring.ratClosure A₂)))))).Opens) (hU : (genericPoint ((Limits.pullback f₀ (Spec.map (CommRingCat.ofHom ((algebraMap ↥(ValuationSubring.ratClosure A₂) A₂.valuation.Completion).comp (algebraMap 𝒪₀ ↥(ValuationSubring.ratClosure A₂)))))) : Scheme.{0})) ∈ U) (hU' : (genericPoint ((Limits.pullback f₀ (Spec.map (CommRingCat.ofHom ((algebraMap ↥(ValuationSubring.ratClosure A₂) A₂.valuation.Completion).comp (algebraMap 𝒪₀ ↥(ValuationSubring.ratClosure A₂)))))) : Scheme.{0})) ∈ aXC ⁻¹ᵁ U) (sec : (Limits.pullback f₀ (Spec.map (CommRingCat.ofHom ((algebraMap ↥(ValuationSubring.ratClosure A₂) A₂.valuation.Completion).comp (algebraMap 𝒪₀ ↥(ValuationSubring.ratClosure A₂)))))).presheaf.obj (Opposite.op U)),
            ((Limits.pullback f₀ (Spec.map (CommRingCat.ofHom ((algebraMap ↥(ValuationSubring.ratClosure A₂) A₂.valuation.Completion).comp (algebraMap 𝒪₀ ↥(ValuationSubring.ratClosure A₂)))))).presheaf.germ U (genericPoint ((Limits.pullback f₀ (Spec.map (CommRingCat.ofHom ((algebraMap ↥(ValuationSubring.ratClosure A₂) A₂.valuation.Completion).comp (algebraMap 𝒪₀ ↥(ValuationSubring.ratClosure A₂)))))) : Scheme.{0})) hU).hom sec = j x →
            ((Limits.pullback f₀ (Spec.map (CommRingCat.ofHom ((algebraMap ↥(ValuationSubring.ratClosure A₂) A₂.valuation.Completion).comp (algebraMap 𝒪₀ ↥(ValuationSubring.ratClosure A₂)))))).presheaf.germ (aXC ⁻¹ᵁ U) (genericPoint ((Limits.pullback f₀ (Spec.map (CommRingCat.ofHom ((algebraMap ↥(ValuationSubring.ratClosure A₂) A₂.valuation.Completion).comp (algebraMap 𝒪₀ ↥(ValuationSubring.ratClosure A₂)))))) : Scheme.{0})) hU').hom ((aXC.app U).hom sec) = j (W 0 • x)) ∧

      (∀ (aXC : (Limits.pullback f₀ (Spec.map (CommRingCat.ofHom ((algebraMap ↥(ValuationSubring.ratClosure A₂) A₂.valuation.Completion).comp (algebraMap 𝒪₀ ↥(ValuationSubring.ratClosure A₂)))))) ⟶ (Limits.pullback f₀ (Spec.map (CommRingCat.ofHom ((algebraMap ↥(ValuationSubring.ratClosure A₂) A₂.valuation.Completion).comp (algebraMap 𝒪₀ ↥(ValuationSubring.ratClosure A₂))))))), aXC ≫ Limits.pullback.fst f₀ (Spec.map (CommRingCat.ofHom ((algebraMap ↥(ValuationSubring.ratClosure A₂) A₂.valuation.Completion).comp (algebraMap 𝒪₀ ↥(ValuationSubring.ratClosure A₂))))) = Limits.pullback.fst f₀ (Spec.map (CommRingCat.ofHom ((algebraMap ↥(ValuationSubring.ratClosure A₂) A₂.valuation.Completion).comp (algebraMap 𝒪₀ ↥(ValuationSubring.ratClosure A₂))))) ≫ arbar →
        aXC ≫ Limits.pullback.snd f₀ (Spec.map (CommRingCat.ofHom ((algebraMap ↥(ValuationSubring.ratClosure A₂) A₂.valuation.Completion).comp (algebraMap 𝒪₀ ↥(ValuationSubring.ratClosure A₂))))) = Limits.pullback.snd f₀ (Spec.map (CommRingCat.ofHom ((algebraMap ↥(ValuationSubring.ratClosure A₂) A₂.valuation.Completion).comp (algebraMap 𝒪₀ ↥(ValuationSubring.ratClosure A₂))))) →
        ∀ x : Fbar, ∀ (U : (Limits.pullback f₀ (Spec.map (CommRingCat.ofHom ((algebraMap ↥(ValuationSubring.ratClosure A₂) A₂.valuation.Completion).comp (algebraMap 𝒪₀ ↥(ValuationSubring.ratClosure A₂)))))).Opens) (hU : (genericPoint ((Limits.pullback f₀ (Spec.map (CommRingCat.ofHom ((algebraMap ↥(ValuationSubring.ratClosure A₂) A₂.valuation.Completion).comp (algebraMap 𝒪₀ ↥(ValuationSubring.ratClosure A₂)))))) : Scheme.{0})) ∈ U) (hU' : (genericPoint ((Limits.pullback f₀ (Spec.map (CommRingCat.ofHom ((algebraMap ↥(ValuationSubring.ratClosure A₂) A₂.valuation.Completion).comp (algebraMap 𝒪₀ ↥(ValuationSubring.ratClosure A₂)))))) : Scheme.{0})) ∈ aXC ⁻¹ᵁ U) (sec : (Limits.pullback f₀ (Spec.map (CommRingCat.ofHom ((algebraMap ↥(ValuationSubring.ratClosure A₂) A₂.valuation.Completion).comp (algebraMap 𝒪₀ ↥(ValuationSubring.ratClosure A₂)))))).presheaf.obj (Opposite.op U)),
            ((Limits.pullback f₀ (Spec.map (CommRingCat.ofHom ((algebraMap ↥(ValuationSubring.ratClosure A₂) A₂.valuation.Completion).comp (algebraMap 𝒪₀ ↥(ValuationSubring.ratClosure A₂)))))).presheaf.germ U (genericPoint ((Limits.pullback f₀ (Spec.map (CommRingCat.ofHom ((algebraMap ↥(ValuationSubring.ratClosure A₂) A₂.valuation.Completion).comp (algebraMap 𝒪₀ ↥(ValuationSubring.ratClosure A₂)))))) : Scheme.{0})) hU).hom sec = j x →
            ((Limits.pullback f₀ (Spec.map (CommRingCat.ofHom ((algebraMap ↥(ValuationSubring.ratClosure A₂) A₂.valuation.Completion).comp (algebraMap 𝒪₀ ↥(ValuationSubring.ratClosure A₂)))))).presheaf.germ (aXC ⁻¹ᵁ U) (genericPoint ((Limits.pullback f₀ (Spec.map (CommRingCat.ofHom ((algebraMap ↥(ValuationSubring.ratClosure A₂) A₂.valuation.Completion).comp (algebraMap 𝒪₀ ↥(ValuationSubring.ratClosure A₂)))))) : Scheme.{0})) hU').hom ((aXC.app U).hom sec) = j (W 1 • x)) ∧

      (∀ (τ : ↥(A₂.decompositionSubgroup ℚ)) (tC : (Limits.pullback f₀ (Spec.map (CommRingCat.ofHom ((algebraMap ↥(ValuationSubring.ratClosure A₂) A₂.valuation.Completion).comp (algebraMap 𝒪₀ ↥(ValuationSubring.ratClosure A₂)))))) ⟶ (Limits.pullback f₀ (Spec.map (CommRingCat.ofHom ((algebraMap ↥(ValuationSubring.ratClosure A₂) A₂.valuation.Completion).comp (algebraMap 𝒪₀ ↥(ValuationSubring.ratClosure A₂))))))),
        tC ≫ Limits.pullback.fst f₀ (Spec.map (CommRingCat.ofHom ((algebraMap ↥(ValuationSubring.ratClosure A₂) A₂.valuation.Completion).comp (algebraMap 𝒪₀ ↥(ValuationSubring.ratClosure A₂))))) = Limits.pullback.fst f₀ (Spec.map (CommRingCat.ofHom ((algebraMap ↥(ValuationSubring.ratClosure A₂) A₂.valuation.Completion).comp (algebraMap 𝒪₀ ↥(ValuationSubring.ratClosure A₂))))) →
        tC ≫ Limits.pullback.snd f₀ (Spec.map (CommRingCat.ofHom ((algebraMap ↥(ValuationSubring.ratClosure A₂) A₂.valuation.Completion).comp (algebraMap 𝒪₀ ↥(ValuationSubring.ratClosure A₂))))) = Limits.pullback.snd f₀ (Spec.map (CommRingCat.ofHom ((algebraMap ↥(ValuationSubring.ratClosure A₂) A₂.valuation.Completion).comp (algebraMap 𝒪₀ ↥(ValuationSubring.ratClosure A₂))))) ≫ Spec.map (CommRingCat.ofHom ((dIso₂ τ).toRingEquiv : A₂.valuation.Completion →+* A₂.valuation.Completion)) →
        ∀ x : Fbar, ∀ (U : (Limits.pullback f₀ (Spec.map (CommRingCat.ofHom ((algebraMap ↥(ValuationSubring.ratClosure A₂) A₂.valuation.Completion).comp (algebraMap 𝒪₀ ↥(ValuationSubring.ratClosure A₂)))))).Opens) (hU : (genericPoint ((Limits.pullback f₀ (Spec.map (CommRingCat.ofHom ((algebraMap ↥(ValuationSubring.ratClosure A₂) A₂.valuation.Completion).comp (algebraMap 𝒪₀ ↥(ValuationSubring.ratClosure A₂)))))) : Scheme.{0})) ∈ U) (hU' : (genericPoint ((Limits.pullback f₀ (Spec.map (CommRingCat.ofHom ((algebraMap ↥(ValuationSubring.ratClosure A₂) A₂.valuation.Completion).comp (algebraMap 𝒪₀ ↥(ValuationSubring.ratClosure A₂)))))) : Scheme.{0})) ∈ tC ⁻¹ᵁ U) (sec : (Limits.pullback f₀ (Spec.map (CommRingCat.ofHom ((algebraMap ↥(ValuationSubring.ratClosure A₂) A₂.valuation.Completion).comp (algebraMap 𝒪₀ ↥(ValuationSubring.ratClosure A₂)))))).presheaf.obj (Opposite.op U)),
            ((Limits.pullback f₀ (Spec.map (CommRingCat.ofHom ((algebraMap ↥(ValuationSubring.ratClosure A₂) A₂.valuation.Completion).comp (algebraMap 𝒪₀ ↥(ValuationSubring.ratClosure A₂)))))).presheaf.germ U (genericPoint ((Limits.pullback f₀ (Spec.map (CommRingCat.ofHom ((algebraMap ↥(ValuationSubring.ratClosure A₂) A₂.valuation.Completion).comp (algebraMap 𝒪₀ ↥(ValuationSubring.ratClosure A₂)))))) : Scheme.{0})) hU).hom sec = j x →
            ((Limits.pullback f₀ (Spec.map (CommRingCat.ofHom ((algebraMap ↥(ValuationSubring.ratClosure A₂) A₂.valuation.Completion).comp (algebraMap 𝒪₀ ↥(ValuationSubring.ratClosure A₂)))))).presheaf.germ (tC ⁻¹ᵁ U) (genericPoint ((Limits.pullback f₀ (Spec.map (CommRingCat.ofHom ((algebraMap ↥(ValuationSubring.ratClosure A₂) A₂.valuation.Completion).comp (algebraMap 𝒪₀ ↥(ValuationSubring.ratClosure A₂)))))) : Scheme.{0})) hU').hom ((tC.app U).hom sec) = j ((gal.comp (A₂.decompositionSubgroup ℚ).subtype) τ • x)) ∧

      (∀ ℓ : HeckeTower.AwayPrime q q', ∃ jℓ : 𝕋.F ℓ →+* ↑(Limits.pullback (g₀ ℓ) (Spec.map (CommRingCat.ofHom ((algebraMap ↥(ValuationSubring.ratClosure A₂) A₂.valuation.Completion).comp (algebraMap 𝒪₀ ↥(ValuationSubring.ratClosure A₂)))))).functionField,
        ∀ (k : Fin 2) (dC : (Limits.pullback (g₀ ℓ) (Spec.map (CommRingCat.ofHom ((algebraMap ↥(ValuationSubring.ratClosure A₂) A₂.valuation.Completion).comp (algebraMap 𝒪₀ ↥(ValuationSubring.ratClosure A₂)))))) ⟶ (Limits.pullback f₀ (Spec.map (CommRingCat.ofHom ((algebraMap ↥(ValuationSubring.ratClosure A₂) A₂.valuation.Completion).comp (algebraMap 𝒪₀ ↥(ValuationSubring.ratClosure A₂))))))),
          dC ≫ Limits.pullback.fst f₀ (Spec.map (CommRingCat.ofHom ((algebraMap ↥(ValuationSubring.ratClosure A₂) A₂.valuation.Completion).comp (algebraMap 𝒪₀ ↥(ValuationSubring.ratClosure A₂))))) = Limits.pullback.fst (g₀ ℓ) (Spec.map (CommRingCat.ofHom ((algebraMap ↥(ValuationSubring.ratClosure A₂) A₂.valuation.Completion).comp (algebraMap 𝒪₀ ↥(ValuationSubring.ratClosure A₂))))) ≫ (if k = 0 then d₀₀ ℓ else d₁₀ ℓ) →
          dC ≫ Limits.pullback.snd f₀ (Spec.map (CommRingCat.ofHom ((algebraMap ↥(ValuationSubring.ratClosure A₂) A₂.valuation.Completion).comp (algebraMap 𝒪₀ ↥(ValuationSubring.ratClosure A₂))))) = Limits.pullback.snd (g₀ ℓ) (Spec.map (CommRingCat.ofHom ((algebraMap ↥(ValuationSubring.ratClosure A₂) A₂.valuation.Completion).comp (algebraMap 𝒪₀ ↥(ValuationSubring.ratClosure A₂))))) →
          ∀ x : Fbar, ∀ (U : (Limits.pullback f₀ (Spec.map (CommRingCat.ofHom ((algebraMap ↥(ValuationSubring.ratClosure A₂) A₂.valuation.Completion).comp (algebraMap 𝒪₀ ↥(ValuationSubring.ratClosure A₂)))))).Opens) (hU : (genericPoint ((Limits.pullback f₀ (Spec.map (CommRingCat.ofHom ((algebraMap ↥(ValuationSubring.ratClosure A₂) A₂.valuation.Completion).comp (algebraMap 𝒪₀ ↥(ValuationSubring.ratClosure A₂)))))) : Scheme.{0})) ∈ U) (hU' : (genericPoint ((Limits.pullback (g₀ ℓ) (Spec.map (CommRingCat.ofHom ((algebraMap ↥(ValuationSubring.ratClosure A₂) A₂.valuation.Completion).comp (algebraMap 𝒪₀ ↥(ValuationSubring.ratClosure A₂)))))) : Scheme.{0})) ∈ dC ⁻¹ᵁ U) (sec : (Limits.pullback f₀ (Spec.map (CommRingCat.ofHom ((algebraMap ↥(ValuationSubring.ratClosure A₂) A₂.valuation.Completion).comp (algebraMap 𝒪₀ ↥(ValuationSubring.ratClosure A₂)))))).presheaf.obj (Opposite.op U)),
            ((Limits.pullback f₀ (Spec.map (CommRingCat.ofHom ((algebraMap ↥(ValuationSubring.ratClosure A₂) A₂.valuation.Completion).comp (algebraMap 𝒪₀ ↥(ValuationSubring.ratClosure A₂)))))).presheaf.germ U (genericPoint ((Limits.pullback f₀ (Spec.map (CommRingCat.ofHom ((algebraMap ↥(ValuationSubring.ratClosure A₂) A₂.valuation.Completion).comp (algebraMap 𝒪₀ ↥(ValuationSubring.ratClosure A₂)))))) : Scheme.{0})) hU).hom sec = j x →
            ((Limits.pullback (g₀ ℓ) (Spec.map (CommRingCat.ofHom ((algebraMap ↥(ValuationSubring.ratClosure A₂) A₂.valuation.Completion).comp (algebraMap 𝒪₀ ↥(ValuationSubring.ratClosure A₂)))))).presheaf.germ (dC ⁻¹ᵁ U) (genericPoint ((Limits.pullback (g₀ ℓ) (Spec.map (CommRingCat.ofHom ((algebraMap ↥(ValuationSubring.ratClosure A₂) A₂.valuation.Completion).comp (algebraMap 𝒪₀ ↥(ValuationSubring.ratClosure A₂)))))) : Scheme.{0})) hU').hom ((dC.app U).hom sec) = jℓ (𝕋.φ (ℓ, k) x)))
    :
    ∃ ι₀ : Fbar →+* FractionRing (Omega.HolRingOf ϖ₂ ρ₂),
      (∀ z : AlgebraicClosure ℚ, ι₀ (algebraMap (AlgebraicClosure ℚ) Fbar z) =
          algebraMap A₂.valuation.Completion (FractionRing (Omega.HolRingOf ϖ₂ ρ₂)) ((z : AlgebraicClosure ℚ) : A₂.valuation.Completion)) ∧
      (Subfield.closure (Set.range (algebraMap A₂.valuation.Completion (FractionRing (Omega.HolRingOf ϖ₂ ρ₂))) ∪ Set.range ι₀) =
          Mumford.invariantFieldOf A₂.valuation.Completion (ℍ[ℚ, a₁, b₁])ˣ (Omega.HolRingOf ϖ₂ ρ₂) (Γ₂ none)) ∧
      (∀ t : Finset Fbar, LinearIndependent (AlgebraicClosure ℚ) (fun x : t => (x : Fbar)) →
          LinearIndependent A₂.valuation.Completion (fun x : t => ι₀ (x : Fbar))) ∧
      (∀ (τ : ↥(A₂.decompositionSubgroup ℚ)) (x : Fbar),
          ι₀ ((gal.comp (A₂.decompositionSubgroup ℚ).subtype) τ • x) =
            (if χ τ = 1 then (1 : (ℍ[ℚ, a₁, b₁])ˣ) else w₂ none) •
              Mumford.AmbientSemilinearAut.fracMap (Omega.toAmbientOf ϖ₂ ρ₂ (dIso₂ τ)) (ι₀ x)) ∧
      (∀ x : Fbar, ι₀ (W 0 • x) = w₂ none • ι₀ x) ∧
      (∀ x : Fbar, ι₀ (W 1 • x) = wbar₂ none • ι₀ x) ∧
      (∀ ℓ : HeckeTower.AwayPrime q q', ∃ ιℓ : 𝕋.F ℓ →+* FractionRing (Omega.HolRingOf ϖ₂ ρ₂),
      (∀ x : Fbar, ιℓ (𝕋.φ (ℓ, 0) x) = ι₀ x) ∧ (∀ x : Fbar, ιℓ (𝕋.φ (ℓ, 1) x) = (s₂ ℓ) • ι₀ x)) := by

  classical
  obtain ⟨_, e, he0, he1, he2, he3, he4⟩ := hGF
  obtain ⟨hj0, hja, hjb, hjc0, hjc1, hjd, hje⟩ := hj
  obtain ⟨hnat, hnatT, hinv, hinvT, hiia, hiiaT, hiib, hiibT, hiv0, hiv1, hv1, hv2⟩ := hCD
  haveI hCac : IsAlgClosed A₂.valuation.Completion :=
    ValuationSubring.isAlgClosed_completion_of_liesOverPrime q Fact.out A₂ hA₂

  have LAWS := CerednikDrinfeld.FormalOmega.OmegaNr.isTwistedAct_laws (𝒪 := 𝒪₀) (K₀ := ↥(ValuationSubring.ratClosure A₂)) π Onr Fr vdet

  have hnatq : ((q : AlgebraicClosure ℚ) : A₂.valuation.Completion) = ((q : ℕ) : A₂.valuation.Completion) := by
    show (UniformSpace.Completion.coeRingHom : WithVal A₂.valuation →+* A₂.valuation.Completion)
        ((WithVal.equiv A₂.valuation).symm ((q : ℕ) : AlgebraicClosure ℚ)) = _
    rw [map_natCast, map_natCast]
  have hπq : algebraMap 𝒪₀ ↥(ValuationSubring.ratClosure A₂) π = ((q : ℕ) : ↥(ValuationSubring.ratClosure A₂)) := by
    rw [hπϖ]
    apply (algebraMap ↥(ValuationSubring.ratClosure A₂) A₂.valuation.Completion).injective
    rw [hϖ₂, hnatq, map_natCast]
  have hvd : ∀ x : (ℍ[ℚ, a₁, b₁])ˣ, vdet ((Units.map (ι₂ : ℍ[ℚ, a₁, b₁] →* Matrix (Fin 2) (Fin 2) ↥(ValuationSubring.ratClosure A₂))) x) = Multiplicative.ofAdd (padicValRat q (nrd (x : ℍ[ℚ, a₁, b₁]))) :=
    fun x => CerednikDrinfeld.vdet_unitsMap_eq_padicValRat_nrd q A₂ hA₂ 𝒪₀ π hπq h𝒪₀ vdet hvdet ι₂ hι₂ x
  have hq'1 : 1 < q := (Fact.out : q.Prime).one_lt
  have hvw : vdet ((Units.map (ι₂ : ℍ[ℚ, a₁, b₁] →* Matrix (Fin 2) (Fin 2) ↥(ValuationSubring.ratClosure A₂))) (w₂ none)) = Multiplicative.ofAdd (1 : ℤ) := by
    rw [hvd, hw₂.1.2, padicValRat.self hq'1]
  have hvwbar : vdet ((Units.map (ι₂ : ℍ[ℚ, a₁, b₁] →* Matrix (Fin 2) (Fin 2) ↥(ValuationSubring.ratClosure A₂))) (wbar₂ none)) = 1 := by
    rw [hvd, hwbar₂.1.1]
    have : padicValRat q (q' : ℚ) = 0 := by
      rw [padicValRat.of_nat, Nat.cast_eq_zero]
      exact padicValNat.eq_zero_of_not_dvd (fun h => hqq' (((Nat.prime_dvd_prime_iff_eq Fact.out Fact.out).1 h).symm))
    rw [this]; rfl

  have hrel := CerednikDrinfeld.CosetGraph.atkinLehner_relations_levelGroups_place hN hqN hq'N hqq' hq5 hq'5 q q' hqN hq'N
    hqq' hdef₁ Λ₁ R₁ hΛ₁ hR₁ hRΛ₁ n₁ hn₁ v₂ hv₂ s₂ sf₂ hs₂ Γ₂ hΓ₂0 hΓ₂ℓ w₂ wbar₂ hw₂ hwbar₂ none

  have hcent : ∀ (u : ℚˣ) (y : FractionRing (Omega.HolRingOf ϖ₂ ρ₂)), (Units.map (algebraMap ℚ ℍ[ℚ, a₁, b₁]).toMonoidHom u) • y = y := by
    intro u y
    have hρ : ρ₂ (Units.map (algebraMap ℚ ℍ[ℚ, a₁, b₁]).toMonoidHom u) = 1 := by
      rw [hρ₂, Matrix.ProjGenLinGroup.mk_eq_one, Subgroup.mem_center_iff]
      intro g
      ext : 1
      rw [Units.val_mul, Units.val_mul, Units.coe_map, Units.coe_map]
      show (g : Matrix (Fin 2) (Fin 2) ↥(ValuationSubring.ratClosure A₂)) * ι₂ (algebraMap ℚ ℍ[ℚ, a₁, b₁] (u : ℚ)) = ι₂ (algebraMap ℚ ℍ[ℚ, a₁, b₁] (u : ℚ)) * (g : Matrix (Fin 2) (Fin 2) ↥(ValuationSubring.ratClosure A₂))
      rw [ι₂.commutes]
      exact (Algebra.commutes _ _).symm
    have hM : ∀ m : Omega.HolRingOf ϖ₂ ρ₂, (Units.map (algebraMap ℚ ℍ[ℚ, a₁, b₁]).toMonoidHom u) • m = m := fun m => by
      rw [Omega.HolRingOf.smul_def, hρ, one_smul]
    have hfa : Mumford.fracAct (ℍ[ℚ, a₁, b₁])ˣ (Omega.HolRingOf ϖ₂ ρ₂) (Units.map (algebraMap ℚ ℍ[ℚ, a₁, b₁]).toMonoidHom u) = RingEquiv.refl _ := by
      apply RingEquiv.toRingHom_injective
      refine IsLocalization.ringHom_ext (nonZeroDivisors (Omega.HolRingOf ϖ₂ ρ₂)) (RingHom.ext fun m => ?_)
      simp only [RingHom.coe_comp, Function.comp_apply, RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom]
      rw [Mumford.fracAct_algebraMap, hM]; rfl
    rw [Mumford.frac_smul_def, hfa]; rfl
  have T3c : ∀ y : FractionRing (Omega.HolRingOf ϖ₂ ρ₂), (1 : (ℍ[ℚ, a₁, b₁])ˣ)⁻¹ • y = y := fun y =>
    (congrArg (fun g : (ℍ[ℚ, a₁, b₁])ˣ => g • y) inv_one).trans (one_smul _ y)
  have T5 : ∀ (g : (ℍ[ℚ, a₁, b₁])ˣ) (y : FractionRing (Omega.HolRingOf ϖ₂ ρ₂)), (g⁻¹)⁻¹ • y = g • y := fun g y =>
    congrArg (fun g : (ℍ[ℚ, a₁, b₁])ˣ => g • y) (inv_inv g)

  have hfixw : ∀ y : ↥(Mumford.invariantFieldOf A₂.valuation.Completion (ℍ[ℚ, a₁, b₁])ˣ (Omega.HolRingOf ϖ₂ ρ₂) (Γ₂ none)), (w₂ none * w₂ none) • (y : FractionRing (Omega.HolRingOf ϖ₂ ρ₂)) = y := fun y =>
    (Mumford.mem_invariantFieldOf_iff _ _ _ _ _).1 y.2 _ hrel.2.2.1
  have hfixwbar : ∀ y : ↥(Mumford.invariantFieldOf A₂.valuation.Completion (ℍ[ℚ, a₁, b₁])ˣ (Omega.HolRingOf ϖ₂ ρ₂) (Γ₂ none)), (wbar₂ none * wbar₂ none) • (y : FractionRing (Omega.HolRingOf ϖ₂ ρ₂)) = y := by
    intro y
    have h := (Mumford.mem_invariantFieldOf_iff _ _ _ _ _).1 y.2 _ hrel.2.2.2.2.1
    rw [mul_smul, inv_smul_eq_iff, hcent] at h
    exact h

  have hgerm : ∀ x : Fbar, ∃ (U : (Limits.pullback f₀ (Spec.map (CommRingCat.ofHom ((algebraMap ↥(ValuationSubring.ratClosure A₂) A₂.valuation.Completion).comp (algebraMap 𝒪₀ ↥(ValuationSubring.ratClosure A₂)))))).Opens) (hU : genericPoint ((Limits.pullback f₀ (Spec.map (CommRingCat.ofHom ((algebraMap ↥(ValuationSubring.ratClosure A₂) A₂.valuation.Completion).comp (algebraMap 𝒪₀ ↥(ValuationSubring.ratClosure A₂)))))) : Scheme.{0}) ∈ U) (sec : (Limits.pullback f₀ (Spec.map (CommRingCat.ofHom ((algebraMap ↥(ValuationSubring.ratClosure A₂) A₂.valuation.Completion).comp (algebraMap 𝒪₀ ↥(ValuationSubring.ratClosure A₂)))))).presheaf.obj (Opposite.op U)),
      ((Limits.pullback f₀ (Spec.map (CommRingCat.ofHom ((algebraMap ↥(ValuationSubring.ratClosure A₂) A₂.valuation.Completion).comp (algebraMap 𝒪₀ ↥(ValuationSubring.ratClosure A₂)))))).presheaf.germ U (genericPoint ((Limits.pullback f₀ (Spec.map (CommRingCat.ofHom ((algebraMap ↥(ValuationSubring.ratClosure A₂) A₂.valuation.Completion).comp (algebraMap 𝒪₀ ↥(ValuationSubring.ratClosure A₂)))))) : Scheme.{0})) hU).hom sec = j x :=
    fun x => TopCat.Presheaf.exists_germ_eq (Limits.pullback f₀ (Spec.map (CommRingCat.ofHom ((algebraMap ↥(ValuationSubring.ratClosure A₂) A₂.valuation.Completion).comp (algebraMap 𝒪₀ ↥(ValuationSubring.ratClosure A₂)))))).presheaf (j x)

  have mkLift : ∀ (a : 𝒳₀ ⟶ 𝒳₀), a ≫ f₀ = f₀ → ∃ aC : (Limits.pullback f₀ (Spec.map (CommRingCat.ofHom ((algebraMap ↥(ValuationSubring.ratClosure A₂) A₂.valuation.Completion).comp (algebraMap 𝒪₀ ↥(ValuationSubring.ratClosure A₂)))))) ⟶ (Limits.pullback f₀ (Spec.map (CommRingCat.ofHom ((algebraMap ↥(ValuationSubring.ratClosure A₂) A₂.valuation.Completion).comp (algebraMap 𝒪₀ ↥(ValuationSubring.ratClosure A₂)))))),
      aC ≫ Limits.pullback.fst f₀ (Spec.map (CommRingCat.ofHom ((algebraMap ↥(ValuationSubring.ratClosure A₂) A₂.valuation.Completion).comp (algebraMap 𝒪₀ ↥(ValuationSubring.ratClosure A₂))))) = Limits.pullback.fst f₀ (Spec.map (CommRingCat.ofHom ((algebraMap ↥(ValuationSubring.ratClosure A₂) A₂.valuation.Completion).comp (algebraMap 𝒪₀ ↥(ValuationSubring.ratClosure A₂))))) ≫ a ∧
      aC ≫ Limits.pullback.snd f₀ (Spec.map (CommRingCat.ofHom ((algebraMap ↥(ValuationSubring.ratClosure A₂) A₂.valuation.Completion).comp (algebraMap 𝒪₀ ↥(ValuationSubring.ratClosure A₂))))) = Limits.pullback.snd f₀ (Spec.map (CommRingCat.ofHom ((algebraMap ↥(ValuationSubring.ratClosure A₂) A₂.valuation.Completion).comp (algebraMap 𝒪₀ ↥(ValuationSubring.ratClosure A₂))))) := fun a ha =>
    ⟨Limits.pullback.lift (Limits.pullback.fst f₀ _ ≫ a) (Limits.pullback.snd f₀ _)
        (by rw [Category.assoc, ha]; exact Limits.pullback.condition),
      Limits.pullback.lift_fst _ _ _, Limits.pullback.lift_snd _ _ _⟩

  have hdomA := CerednikDrinfeld.QM.IsCoarseModuli.base_genericPoint_eq_of_comp_fst_eq_fst_comp_of_isAtkinLehnerQuotient_of_not_dvd
    hB Λ hΛ q (Or.inl rfl) hqN hqq' hqN hq'N 𝒪₀ 𝒳₀ f₀ pt₀ h𝒳₀ ar har A₂.valuation.Completion (Spec.map (CommRingCat.ofHom ((algebraMap ↥(ValuationSubring.ratClosure A₂) A₂.valuation.Completion).comp (algebraMap 𝒪₀ ↥(ValuationSubring.ratClosure A₂)))))
  have hdomAbar := CerednikDrinfeld.QM.IsCoarseModuli.base_genericPoint_eq_of_comp_fst_eq_fst_comp_of_isAtkinLehnerQuotient_of_not_dvd
    hB Λ hΛ q' (Or.inr rfl) hq'N hqq' hqN hq'N 𝒪₀ 𝒳₀ f₀ pt₀ h𝒳₀ arbar harbar A₂.valuation.Completion (Spec.map (CommRingCat.ofHom ((algebraMap ↥(ValuationSubring.ratClosure A₂) A₂.valuation.Completion).comp (algebraMap 𝒪₀ ↥(ValuationSubring.ratClosure A₂)))))
  refine ⟨((Mumford.invariantFieldOf A₂.valuation.Completion (ℍ[ℚ, a₁, b₁])ˣ (Omega.HolRingOf ϖ₂ ρ₂) (Γ₂ none))).subtype.comp (e.toRingHom.comp j), ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  ·
    intro z
    show (e (j (algebraMap (AlgebraicClosure ℚ) Fbar z))).1 = _
    rw [hj0 z, he0]
    rfl
  ·
    apply le_antisymm
    · rw [Subfield.closure_le]
      rintro y (⟨c, rfl⟩ | ⟨x, rfl⟩)
      · exact (algebraMap A₂.valuation.Completion ↥(Mumford.invariantFieldOf A₂.valuation.Completion (ℍ[ℚ, a₁, b₁])ˣ (Omega.HolRingOf ϖ₂ ρ₂) (Γ₂ none)) c).2
      · exact (e (j x)).2
    · intro y hy
      have hk : e.symm ⟨y, hy⟩ ∈ Subfield.closure (Set.range (AlgebraicCurve.baseToFunctionField (Limits.pullback.snd f₀ (Spec.map (CommRingCat.ofHom ((algebraMap ↥(ValuationSubring.ratClosure A₂) A₂.valuation.Completion).comp (algebraMap 𝒪₀ ↥(ValuationSubring.ratClosure A₂))))))) ∪ Set.range j) := by
        rw [hja]; trivial
      have hy' : y = (((Mumford.invariantFieldOf A₂.valuation.Completion (ℍ[ℚ, a₁, b₁])ˣ (Omega.HolRingOf ϖ₂ ρ₂) (Γ₂ none))).subtype.comp e.toRingHom) (e.symm ⟨y, hy⟩) := by
        simp only [RingHom.coe_comp, Function.comp_apply, RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom,
          RingEquiv.apply_symm_apply, Subfield.coe_subtype]
      rw [hy']
      have hmem : (((Mumford.invariantFieldOf A₂.valuation.Completion (ℍ[ℚ, a₁, b₁])ˣ (Omega.HolRingOf ϖ₂ ρ₂) (Γ₂ none))).subtype.comp e.toRingHom) (e.symm ⟨y, hy⟩) ∈
          (Subfield.closure (Set.range (AlgebraicCurve.baseToFunctionField (Limits.pullback.snd f₀ (Spec.map (CommRingCat.ofHom ((algebraMap ↥(ValuationSubring.ratClosure A₂) A₂.valuation.Completion).comp (algebraMap 𝒪₀ ↥(ValuationSubring.ratClosure A₂))))))) ∪ Set.range j)).map
            (((Mumford.invariantFieldOf A₂.valuation.Completion (ℍ[ℚ, a₁, b₁])ˣ (Omega.HolRingOf ϖ₂ ρ₂) (Γ₂ none))).subtype.comp e.toRingHom) :=
        Subfield.mem_map.2 ⟨_, hk, rfl⟩
      rw [RingHom.map_field_closure] at hmem
      refine Subfield.closure_mono ?_ hmem
      rintro _ ⟨u, hu, rfl⟩
      rcases hu with ⟨c, rfl⟩ | ⟨x, rfl⟩
      · left
        refine ⟨c, ?_⟩
        show _ = (e (AlgebraicCurve.baseToFunctionField _ c)).1
        rw [he0]; rfl
      · right; exact ⟨x, rfl⟩
  ·
    intro t ht
    rw [Fintype.linearIndependent_iff]
    intro c hc
    have hinj : Function.Injective (((Mumford.invariantFieldOf A₂.valuation.Completion (ℍ[ℚ, a₁, b₁])ˣ (Omega.HolRingOf ϖ₂ ρ₂) (Γ₂ none))).subtype.comp e.toRingHom) :=
      fun a b h => e.injective (Subtype.val_injective h)
    refine hjb t ht c (hinj ?_)
    rw [map_zero]
    refine Eq.trans ?_ hc
    rw [map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_mul, Algebra.smul_def]
    refine congrArg₂ (· * ·) ?_ rfl
    show (e (AlgebraicCurve.baseToFunctionField _ (c i))).1 = algebraMap A₂.valuation.Completion (FractionRing (Omega.HolRingOf ϖ₂ ρ₂)) (c i)
    rw [he0]; rfl
  ·
    intro τ x
    obtain ⟨n, hn01, hnrel, hn0⟩ :=
      CerednikDrinfeld.exists_smul_psi_eq_psi_frobenius_pow_iff_parity_of_decompositionSubgroup (q := q) A₂ hA₂ χ hχ₃
        𝒪₀ hdvr₀ π hπ hcpl hres hunr Onr Fr hOc hOm hOcl hFr ψ₀ hψ₀𝒪 τ
    obtain ⟨U, hU, sec, hsec⟩ := hgerm x
    obtain ⟨tC, htC1, htC2, htCdom⟩ := rdoff_twist_exists f₀ ((algebraMap ↥(ValuationSubring.ratClosure A₂) A₂.valuation.Completion).comp (algebraMap 𝒪₀ ↥(ValuationSubring.ratClosure A₂))) (dIso₂ τ).toRingEquiv
      (RingHom.ext fun a => (dIso₂ τ).fix (algebraMap 𝒪₀ ↥(ValuationSubring.ratClosure A₂) a))
    have hU' : genericPoint ((Limits.pullback f₀ (Spec.map (CommRingCat.ofHom ((algebraMap ↥(ValuationSubring.ratClosure A₂) A₂.valuation.Completion).comp (algebraMap 𝒪₀ ↥(ValuationSubring.ratClosure A₂)))))) : Scheme.{0}) ∈ tC ⁻¹ᵁ U :=
      (Scheme.Hom.mem_preimage tC).2 (by rw [htCdom]; exact hU)
    have hd := hjd τ tC htC1 htC2 x U hU hU' sec hsec
    have h3 := he3 (dIso₂ τ) n (fun y hy => by rw [hdIso₂]; exact hnrel y hy) tC htC1 htC2 (w₂ none) hw₂.1.1 hvw U hU hU' sec
    have hA := congrArg (fun t => (e t).1) hd
    have hB := congrArg (fun t => (e t).1) hsec
    show (e (j ((gal.comp (A₂.decompositionSubgroup ℚ).subtype) τ • x))).1 =
      (if χ τ = 1 then (1 : (ℍ[ℚ, a₁, b₁])ˣ) else w₂ none) •
        Mumford.AmbientSemilinearAut.fracMap (Omega.toAmbientOf ϖ₂ ρ₂ (dIso₂ τ)) (e (j x)).1
    refine hA.symm.trans (h3.trans ((congrArg (fun z => (w₂ none) ^ n •
        Mumford.AmbientSemilinearAut.fracMap (Omega.toAmbientOf ϖ₂ ρ₂ (dIso₂ τ)) z) hB).trans ?_))
    rcases hn01 with rfl | rfl
    · rw [if_pos (hn0.1 rfl), zpow_zero]
    · have : ¬ χ τ = 1 := fun h => by have := hn0.2 h; omega
      rw [if_neg this, zpow_one]
  ·
    intro x
    obtain ⟨U, hU, sec, hsec⟩ := hgerm x
    obtain ⟨aC, haC1, haC2⟩ := mkLift ar harf
    have hU' : genericPoint ((Limits.pullback f₀ (Spec.map (CommRingCat.ofHom ((algebraMap ↥(ValuationSubring.ratClosure A₂) A₂.valuation.Completion).comp (algebraMap 𝒪₀ ↥(ValuationSubring.ratClosure A₂)))))) : Scheme.{0}) ∈ aC ⁻¹ᵁ U :=
      (Scheme.Hom.mem_preimage aC).2 (by rw [hdomA aC haC1 haC2]; exact hU)
    have hc := hjc0 aC haC1 haC2 x U hU hU' sec hsec
    have h2 := he2 ar harf hv1 aC haC1 haC2 (w₂ none) hw₂.1.1 hvw U hU hU' sec
    have hA := congrArg (fun t => (e t).1) hc
    have hB := congrArg (fun t => (e t).1) hsec
    show (e (j (W 0 • x))).1 = w₂ none • (e (j x)).1
    exact hA.symm.trans (h2.trans ((congrArg (fun z => (w₂ none)⁻¹ • z) hB).trans (rdoff_inv_smul_eq_smul _ _ (hfixw _))))
  ·
    intro x
    obtain ⟨U, hU, sec, hsec⟩ := hgerm x
    obtain ⟨aC, haC1, haC2⟩ := mkLift arbar harbarf
    have hU' : genericPoint ((Limits.pullback f₀ (Spec.map (CommRingCat.ofHom ((algebraMap ↥(ValuationSubring.ratClosure A₂) A₂.valuation.Completion).comp (algebraMap 𝒪₀ ↥(ValuationSubring.ratClosure A₂)))))) : Scheme.{0}) ∈ aC ⁻¹ᵁ U :=
      (Scheme.Hom.mem_preimage aC).2 (by rw [hdomAbar aC haC1 haC2]; exact hU)
    have hc := hjc1 aC haC1 haC2 x U hU hU' sec hsec
    have h1 := he1 arbar harbarf (wbar₂ none) hvwbar hv2 aC haC1 haC2 U hU hU' sec
    have hA := congrArg (fun t => (e t).1) hc
    have hB := congrArg (fun t => (e t).1) hsec
    show (e (j (W 1 • x))).1 = wbar₂ none • (e (j x)).1
    exact hA.symm.trans (h1.trans ((congrArg (fun z => (wbar₂ none)⁻¹ • z) hB).trans (rdoff_inv_smul_eq_smul _ _ (hfixwbar _))))
  ·
    intro ℓ
    obtain ⟨jℓ, hjℓ⟩ := hje ℓ
    obtain ⟨_, eY, heY0, heY⟩ := he4 ℓ
    haveI : Fact ((ℓ.1 : ℕ).Prime) := ⟨ℓ.1.prop⟩
    have hdomD := CerednikDrinfeld.QM.IsCoarseModuliT.base_genericPoint_eq_of_comp_fst_eq_fst_comp_degeneracy hqq' hB Λ hΛ
      (ℓ.1 : ℕ) ℓ.2.1 ℓ.2.2 𝒪₀ 𝒳₀ f₀ pt₀ h𝒳₀ (𝒴₀ ℓ) (g₀ ℓ)
      (ptT₀ ℓ) (h𝒴₀ ℓ) (d₀₀ ℓ) (d₁₀ ℓ)
      (hd₀ ℓ) (hd₁ ℓ) A₂.valuation.Completion (Spec.map (CommRingCat.ofHom ((algebraMap ↥(ValuationSubring.ratClosure A₂) A₂.valuation.Completion).comp (algebraMap 𝒪₀ ↥(ValuationSubring.ratClosure A₂)))))
    refine ⟨(Mumford.invariantFieldOf A₂.valuation.Completion (ℍ[ℚ, a₁, b₁])ˣ (Omega.HolRingOf ϖ₂ ρ₂) _).subtype.comp (eY.toRingHom.comp jℓ), ?_, ?_⟩
    ·
      intro x
      obtain ⟨U, hU, sec, hsec⟩ := hgerm x
      obtain ⟨dC, hdC1, hdC2⟩ : ∃ dC : (Limits.pullback (g₀ ℓ) (Spec.map (CommRingCat.ofHom ((algebraMap ↥(ValuationSubring.ratClosure A₂) A₂.valuation.Completion).comp (algebraMap 𝒪₀ ↥(ValuationSubring.ratClosure A₂)))))) ⟶ (Limits.pullback f₀ (Spec.map (CommRingCat.ofHom ((algebraMap ↥(ValuationSubring.ratClosure A₂) A₂.valuation.Completion).comp (algebraMap 𝒪₀ ↥(ValuationSubring.ratClosure A₂)))))),
          dC ≫ Limits.pullback.fst f₀ (Spec.map (CommRingCat.ofHom ((algebraMap ↥(ValuationSubring.ratClosure A₂) A₂.valuation.Completion).comp (algebraMap 𝒪₀ ↥(ValuationSubring.ratClosure A₂))))) = Limits.pullback.fst (g₀ ℓ) (Spec.map (CommRingCat.ofHom ((algebraMap ↥(ValuationSubring.ratClosure A₂) A₂.valuation.Completion).comp (algebraMap 𝒪₀ ↥(ValuationSubring.ratClosure A₂))))) ≫ d₀₀ ℓ ∧
          dC ≫ Limits.pullback.snd f₀ (Spec.map (CommRingCat.ofHom ((algebraMap ↥(ValuationSubring.ratClosure A₂) A₂.valuation.Completion).comp (algebraMap 𝒪₀ ↥(ValuationSubring.ratClosure A₂))))) = Limits.pullback.snd (g₀ ℓ) (Spec.map (CommRingCat.ofHom ((algebraMap ↥(ValuationSubring.ratClosure A₂) A₂.valuation.Completion).comp (algebraMap 𝒪₀ ↥(ValuationSubring.ratClosure A₂))))) :=
        ⟨Limits.pullback.lift (Limits.pullback.fst (g₀ ℓ) (Spec.map (CommRingCat.ofHom ((algebraMap ↥(ValuationSubring.ratClosure A₂) A₂.valuation.Completion).comp (algebraMap 𝒪₀ ↥(ValuationSubring.ratClosure A₂))))) ≫ d₀₀ ℓ) (Limits.pullback.snd (g₀ ℓ) (Spec.map (CommRingCat.ofHom ((algebraMap ↥(ValuationSubring.ratClosure A₂) A₂.valuation.Completion).comp (algebraMap 𝒪₀ ↥(ValuationSubring.ratClosure A₂))))))
            (by rw [Category.assoc, hd₀f]; exact Limits.pullback.condition),
          Limits.pullback.lift_fst _ _ _, Limits.pullback.lift_snd _ _ _⟩
      have hdC1' : dC ≫ Limits.pullback.fst f₀ (Spec.map (CommRingCat.ofHom ((algebraMap ↥(ValuationSubring.ratClosure A₂) A₂.valuation.Completion).comp (algebraMap 𝒪₀ ↥(ValuationSubring.ratClosure A₂))))) =
          Limits.pullback.fst (g₀ ℓ) (Spec.map (CommRingCat.ofHom ((algebraMap ↥(ValuationSubring.ratClosure A₂) A₂.valuation.Completion).comp (algebraMap 𝒪₀ ↥(ValuationSubring.ratClosure A₂))))) ≫ (if (0 : Fin 2) = 0 then d₀₀ ℓ else d₁₀ ℓ) := by
        rw [if_pos rfl]; exact hdC1
      have hU' : genericPoint ((Limits.pullback (g₀ ℓ) (Spec.map (CommRingCat.ofHom ((algebraMap ↥(ValuationSubring.ratClosure A₂) A₂.valuation.Completion).comp (algebraMap 𝒪₀ ↥(ValuationSubring.ratClosure A₂)))))) : Scheme.{0}) ∈ dC ⁻¹ᵁ U :=
        (Scheme.Hom.mem_preimage dC).2 (by rw [hdomD 0 dC hdC1' hdC2]; exact hU)
      have he_ := hjℓ 0 dC hdC1' hdC2 x U hU hU' sec hsec
      have h4 := heY (d₀₀ ℓ) (hd₀f _) 1 (by rw [map_one, map_one])
        (fun B _ _ hB y y' hyy' => by
          rw [map_one] at hyy'
          have := LAWS.1 B 1 y y' y hyy' (LAWS.2.2.1 B y)
          rw [this]
          exact hiv0 _ B hB y)
        dC hdC1 hdC2 U hU hU' sec
      have hA := congrArg (fun t => (eY t).1) he_
      have hB := congrArg (fun t => (e t).1) hsec
      show (eY (jℓ (𝕋.φ (ℓ, 0) x))).1 = (e (j x)).1
      exact hA.symm.trans (h4.trans ((congrArg (fun z => (1 : (ℍ[ℚ, a₁, b₁])ˣ)⁻¹ • z) hB).trans (T3c _)))
    ·
      intro x
      obtain ⟨U, hU, sec, hsec⟩ := hgerm x
      obtain ⟨dC, hdC1, hdC2⟩ : ∃ dC : (Limits.pullback (g₀ ℓ) (Spec.map (CommRingCat.ofHom ((algebraMap ↥(ValuationSubring.ratClosure A₂) A₂.valuation.Completion).comp (algebraMap 𝒪₀ ↥(ValuationSubring.ratClosure A₂)))))) ⟶ (Limits.pullback f₀ (Spec.map (CommRingCat.ofHom ((algebraMap ↥(ValuationSubring.ratClosure A₂) A₂.valuation.Completion).comp (algebraMap 𝒪₀ ↥(ValuationSubring.ratClosure A₂)))))),
          dC ≫ Limits.pullback.fst f₀ (Spec.map (CommRingCat.ofHom ((algebraMap ↥(ValuationSubring.ratClosure A₂) A₂.valuation.Completion).comp (algebraMap 𝒪₀ ↥(ValuationSubring.ratClosure A₂))))) = Limits.pullback.fst (g₀ ℓ) (Spec.map (CommRingCat.ofHom ((algebraMap ↥(ValuationSubring.ratClosure A₂) A₂.valuation.Completion).comp (algebraMap 𝒪₀ ↥(ValuationSubring.ratClosure A₂))))) ≫ d₁₀ ℓ ∧
          dC ≫ Limits.pullback.snd f₀ (Spec.map (CommRingCat.ofHom ((algebraMap ↥(ValuationSubring.ratClosure A₂) A₂.valuation.Completion).comp (algebraMap 𝒪₀ ↥(ValuationSubring.ratClosure A₂))))) = Limits.pullback.snd (g₀ ℓ) (Spec.map (CommRingCat.ofHom ((algebraMap ↥(ValuationSubring.ratClosure A₂) A₂.valuation.Completion).comp (algebraMap 𝒪₀ ↥(ValuationSubring.ratClosure A₂))))) :=
        ⟨Limits.pullback.lift (Limits.pullback.fst (g₀ ℓ) (Spec.map (CommRingCat.ofHom ((algebraMap ↥(ValuationSubring.ratClosure A₂) A₂.valuation.Completion).comp (algebraMap 𝒪₀ ↥(ValuationSubring.ratClosure A₂))))) ≫ d₁₀ ℓ) (Limits.pullback.snd (g₀ ℓ) (Spec.map (CommRingCat.ofHom ((algebraMap ↥(ValuationSubring.ratClosure A₂) A₂.valuation.Completion).comp (algebraMap 𝒪₀ ↥(ValuationSubring.ratClosure A₂))))))
            (by rw [Category.assoc, hd₁f]; exact Limits.pullback.condition),
          Limits.pullback.lift_fst _ _ _, Limits.pullback.lift_snd _ _ _⟩
      have hdC1' : dC ≫ Limits.pullback.fst f₀ (Spec.map (CommRingCat.ofHom ((algebraMap ↥(ValuationSubring.ratClosure A₂) A₂.valuation.Completion).comp (algebraMap 𝒪₀ ↥(ValuationSubring.ratClosure A₂))))) =
          Limits.pullback.fst (g₀ ℓ) (Spec.map (CommRingCat.ofHom ((algebraMap ↥(ValuationSubring.ratClosure A₂) A₂.valuation.Completion).comp (algebraMap 𝒪₀ ↥(ValuationSubring.ratClosure A₂))))) ≫ (if (1 : Fin 2) = 0 then d₀₀ ℓ else d₁₀ ℓ) := by
        rw [if_neg (by decide)]; exact hdC1
      have hU' : genericPoint ((Limits.pullback (g₀ ℓ) (Spec.map (CommRingCat.ofHom ((algebraMap ↥(ValuationSubring.ratClosure A₂) A₂.valuation.Completion).comp (algebraMap 𝒪₀ ↥(ValuationSubring.ratClosure A₂)))))) : Scheme.{0}) ∈ dC ⁻¹ᵁ U :=
        (Scheme.Hom.mem_preimage dC).2 (by rw [hdomD 1 dC hdC1' hdC2]; exact hU)
      have he_ := hjℓ 1 dC hdC1' hdC2 x U hU hU' sec hsec
      have hvs : vdet ((Units.map (ι₂ : ℍ[ℚ, a₁, b₁] →* Matrix (Fin 2) (Fin 2) ↥(ValuationSubring.ratClosure A₂))) (s₂ ℓ)⁻¹) = 1 := by
        rw [map_inv, map_inv, hvd, (hs₂ ℓ).2.2.2, padicValRat.of_nat]
        have : padicValNat q (ℓ.1 : ℕ) = 0 :=
          padicValNat.eq_zero_of_not_dvd (fun h => ℓ.2.1 (((Nat.prime_dvd_prime_iff_eq Fact.out ℓ.1.prop).1 h).symm))
        rw [this]; rfl
      have h4 := heY (d₁₀ ℓ) (hd₁f _) (s₂ ℓ)⁻¹ hvs
        (fun B _ _ hB y y' hyy' => by
          apply hiv1 _ B hB y y'
          rw [map_inv] at hyy'
          obtain ⟨y'', hy''⟩ := LAWS.2.1 B ((Units.map (ι₂ : ℍ[ℚ, a₁, b₁] →* Matrix (Fin 2) (Fin 2) ↥(ValuationSubring.ratClosure A₂))) (s₂ ℓ)) y'
          have hcomp := LAWS.2.2.2.1 B _ _ y y' y'' hyy' hy''
          rw [mul_inv_cancel] at hcomp
          have := LAWS.1 B 1 y y'' y hcomp (LAWS.2.2.1 B y)
          rw [this] at hy''
          exact hy'')
        dC hdC1 hdC2 U hU hU' sec
      have hA := congrArg (fun t => (eY t).1) he_
      have hB := congrArg (fun t => (e t).1) hsec
      show (eY (jℓ (𝕋.φ (ℓ, 1) x))).1 = (s₂ ℓ) • (e (j x)).1
      exact hA.symm.trans (h4.trans ((congrArg (fun z => ((s₂ ℓ)⁻¹)⁻¹ • z) hB).trans (T5 _ _)))

end S_CerednikDrinfeld_mumfordEmbedding_readoff_of_functionField_equiv_of_ringHom_zero_one_of_two_mul_dvd
end P2MW
export P2MW.S_CerednikDrinfeld_mumfordEmbedding_readoff_of_functionField_equiv_of_ringHom_zero_one_of_two_mul_dvd (solution)
