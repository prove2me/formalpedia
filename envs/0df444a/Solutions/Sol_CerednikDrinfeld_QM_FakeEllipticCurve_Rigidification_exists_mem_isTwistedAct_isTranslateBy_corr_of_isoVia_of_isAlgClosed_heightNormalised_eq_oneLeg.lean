-- Prove2me | solution 1 for CerednikDrinfeld.QM.FakeEllipticCurve.Rigidification.exists_mem_isTwistedAct_isTranslateBy_corr_of_isoVia_of_isAlgClosed_heightNormalised_eq_oneLeg
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.837917+00:00
-- url     : https://prove2.me/submissions/fc4213a2-0c04-53a4-a7b8-c0bbb7c643dc

import Mathlib
import Definitions.Def_CerednikDrinfeld_AlgFunctorConst
import Definitions.Def_CerednikDrinfeld_ClassSetGraph
import Definitions.Def_CerednikDrinfeld_CosetGraphAtPrime
import Definitions.Def_CerednikDrinfeld_FakeEllipticFrobenius
import Definitions.Def_CerednikDrinfeld_FormalUpperHalfPlaneFunctor
import Definitions.Def_CerednikDrinfeld_HeckeTower
import Definitions.Def_CerednikDrinfeld_QMCoarseModuli
import Definitions.Def_CerednikDrinfeld_QMFineModuli
import Definitions.Def_CerednikDrinfeld_QMFineModuliT
import Definitions.Def_CerednikDrinfeld_QMIsogeny
import Definitions.Def_CerednikDrinfeld_QMRigidification
import Definitions.Def_CerednikDrinfeld_QMRigidificationLevel
import Definitions.Def_CerednikDrinfeld_SchemeNilpPoints
import Definitions.Def_CerednikDrinfeld_SpecialFormalFunctorG
import Definitions.Def_QuaternionAlgebra_EichlerOrder
import Theorems.Thm_AlgebraicGeometry_isIso_of_isClosedImmersion_of_finrank_comp_eq
import Theorems.Thm_CerednikDrinfeld_CosetGraph_mem_awayUnits_iff_exists_pow_smul_mem_of_forall_localBox_eq
import Theorems.Thm_CerednikDrinfeld_FormalOmega_OmegaNr_isTwistedAct_laws
import Theorems.Thm_CerednikDrinfeld_isUnit_natCast_of_not_dvd_of_card_quotient
import Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_exists_isPullbackVia_id_comp_eq_of_isPullbackVia_of_isPullbackVia_of_isUnit
import Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_isFinite_flat_surjective_of_mapPt_mapPt_eq_nsmulPt
import Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_Rigidification_exists_isTranslateBy_of_isIsogenyPair
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_Rigidification_exists_mem_isTwistedAct_isTranslateBy_corr_of_isoVia_of_isAlgClosed_heightNormalised_eq_oneLeg
p2m_attr_erase "instance" "instTopologicallyFGOfFiniteType GoodReductionJacobian.RelativeGroupLaw.isIso_endKerStr_schemeHomOverId AlgebraicGeometry.Scheme.PresheafOfModules.symmetricCategory SheafOfModules.instFaithfulRingSheafPModToPMod SheafOfModules.symmetricCategory AlgebraicGeometry.Scheme.PresheafOfModules.monoidalCategory AlgebraicGeometry.Scheme.PresheafOfModules.monoidalClosed SheafOfModules.instFullRingSheafPModToPMod SheafOfModules.monoidalCategory AlgebraicGeometry.Scheme.Modules.symmetricCategory SheafOfModules.monoidalClosed SheafOfModules.instIsLocalizationPModRingSheafSheafifyFunctorPresheafW SheafOfModules.sheafifyFunctor_monoidal AlgebraicGeometry.Scheme.Modules.monoidalClosed AlgebraicGeometry.instMonoidalPresheafOfModulesModulesSheafify AlgebraicGeometry.Scheme.Modules.monoidalCategory PresheafOfModules.instMonoidalClosed PresheafOfModules.InternalHom.instModuleCarrierObjOppositeCommRingCatSubtypePiFamilyMemAddSubgroupNaturalFamilies PresheafOfModules.InternalHom.instModuleCarrierObjOppositeRingCatCompCommRingCatForget₂RingHomCarrierCarrierAbPresheaf PresheafOfModules.InternalHom.instSMulCarrierObjOppositeCommRingCatSubtypePiFamilyMemAddSubgroupNaturalFamilies AlgebraicGeometry.Scheme.Hom.opensMapFinal AlgebraicGeometry.RelPicard.RigidifiedLineBundle.setoid AlgebraicGeometry.RelPicard.RigidifiedLineBundle.instInhabited AlgebraicGeometry.OModulePresheaf.isScalarTower AlgebraicGeometry.Scheme.OrderedAffineCover.instLinearOrder AlgebraicGeometry.OModulePresheaf.module AlgebraicGeometry.Scheme.OrderedAffineCover.instFintype AlgebraicGeometry.Scheme.OrderedAffineCover.instFintypeIdx AlgebraicGeometry.OModulePresheaf.addCommGroup AlgebraicGeometry.Scheme.OrderedAffineCover.instDecidableEqIdx AlgebraicGeometry.OModulePresheaf.moduleSections TwoChartCech.Sections.M0_moduleA TwoChartCech.Sections.M1_module TwoChartCech.Cover.A01_algebra TwoChartCech.Cover.A0_algebra TwoChartCech.Cover.A1_commRing TwoChartCech.Cover.A1_algebra TwoChartCech.Sections.M01_module TwoChartCech.Sections.M0_addCommGroup TwoChartCech.Sections.M0_tower"
p2m_attr_erase "instance" "TwoChartCech.Sections.M01_addCommGroup TwoChartCech.Cover.A0_commRing TwoChartCech.Sections.M1_tower TwoChartCech.Sections.M01_moduleA TwoChartCech.Sections.M0_module TwoChartCech.Sections.M1_moduleA TwoChartCech.Sections.M1_addCommGroup TwoChartCech.Cover.A01_commRing TwoChartCech.Sections.M01_tower CoherentBaseChange.TwoTermComplex.C0_module CoherentBaseChange.TwoTermComplex.C0_addCommGroup CoherentBaseChange.TwoTermComplex.C1_module CoherentBaseChange.TwoTermComplex.C1_addCommGroup CoherentBaseChange.TwoTermComplex.C0_free CoherentBaseChange.TwoTermComplex.C1_finite CoherentBaseChange.TwoTermComplex.C0_finite CoherentBaseChange.TwoTermComplex.C1_free AlgebraicGeometry.OModulePresheaf.instSubsingletonObjZero AlgebraicGeometry.Scheme.Modules.preservesBinaryProducts_opensMap AlgebraicGeometry.Scheme.Modules.pullback_monoidal AlgebraicGeometry.Scheme.Modules.sheafify_isLocalization' AlgebraicGeometry.Scheme.Modules.preservesTerminal_opensMap AlgebraicGeometry.Scheme.Modules.pullback₀_monoidal AlgebraicGeometry.Scheme.Modules.preservesFiniteProducts_opensMap AlgebraicGeometry.Scheme.Modules.instLiftingPresheafOfModulesSheafifyPresheafWOpensCarrierCarrierCommRingCatGrothendieckTopologyObjFunctorOppositeIsSheafSheafCompPullback₀Pullback PresheafOfModules.PullbackMonoidal.pullback_monoidal PresheafOfModules.PullbackMonoidal.isIso_δ PresheafOfModules.pushforward_laxMonoidal PresheafOfModules.PullbackMonoidal.isIso_η PresheafOfModules.free_monoidal PresheafOfModules.restrictScalars_laxMonoidal PresheafOfModules.PullbackMonoidal.isIso_δ_gS PresheafOfModules.pullback_oplaxMonoidal PresheafOfModules.PullbackMonoidal.instPreservesColimitsOfSizeCompOppositeCommRingCatRingCatForget₂RingHomCarrierCarrierPb PresheafOfModules.pullback_monoidal' AlgebraicGeometry.SmoothOfRelativeDimension.fiberToSpecResidueField AlgebraicGeometry.SmoothOfRelativeDimension.pullback_snd AlgebraicGeometry.SmoothOfRelativeDimension.pullback_fst AlgebraicGeometry.SmoothOfRelativeDimension.smooth_one AlgebraicGeometry.SmoothProperCurve.isIntegral_pullback_Spec_field"
p2m_attr_erase "instance" "AlgebraicGeometry.IsProper.fiberToSpecResidueField AlgebraicCurve.CurveModel.isProper AlgebraicCurve.CurveModel.isIntegral AlgebraicCurve.CurveModel.smooth AlgebraicGeometry.Scheme.LocalRepresentabilityULift.instIsLocallyInjectiveFunUliftYonedaGluedToSheaf AlgebraicGeometry.Scheme.LocalRepresentabilityULift.instIsLocallySurjectiveFunUliftYonedaGluedToSheafOfIsLocallySurjectiveZariskiTopologyDescFunctorOppositeType AlgebraicGeometry.Scheme.LocalRepresentabilityULift.instIsOpenImmersionToGlued AlgebraicGeometry.Scheme.LocalRepresentabilityULift.instIsIsoSheafZariskiTopologyTypeUliftYonedaGluedToSheaf AlgebraicGeometry.RelPicard.instIsOpenImmersionToGlued AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions PresheafOfModules.ExteriorPower.instModulePresheafAb AlgebraicGeometry.RelEffCartierDiv.subsingleton_of_degree_zero AlgebraicGeometry.RelEffCartierDiv.isIso_subschemeIota_snd_of_degree_one AlgebraicGeometry.isIso_ker_graphOver_subschemeIota_snd AlgebraicGeometry.isClosedImmersion_graphOver AlgebraicGeometry.FGSubalgebra.instIsDirectedLe AlgebraicGeometry.FGSubalgebra.instQuasiSeparatedSpaceCarrierCarrierCommRingCatObjOppositeSchemeSpecDiagram AlgebraicGeometry.FGSubalgebra.instIsCofilteredOpposite AlgebraicGeometry.FGSubalgebra.instIsAffineObjOppositeSchemeSpecDiagram AlgebraicGeometry.FGSubalgebra.instNonempty AlgebraicGeometry.FGSubalgebra.instNonemptySubtypeLeSubalgebraValFG AlgebraicGeometry.FGSubalgebra.instCompactSpaceCarrierCarrierCommRingCatObjOppositeSchemeSpecDiagram AlgebraicGeometry.FGSubalgebra.instIsDirectedSubtypeLeSubalgebraValFG AlgebraicGeometry.FGSubalgebra.instIsAffineHomMapOppositeSchemeSpecDiagram AlgebraicGeometry.FGSubalgebra.instIsFiltered AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instNeg AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instSMulInt AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instAddCommGroup AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instAdd AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instSub AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instModuleCarrierObjOppositeOpensCarrierCarrierCommRingCatPresheafOpOpensTop AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instSMulCarrierObjOppositeOpensCarrierCarrierCommRingCatPresheafOpOpensTop AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instSMulNat"
p2m_attr_erase "instance" "AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instZero AlgebraicCurve.instHasLocalResidue_of_hasCanonicalLocalResidueK AlgebraicCurve.instHasCanonicalLocalResidueK_of_hasCanonicalLocalResidueKStar AlgebraicCurve.Place.kw_ffgc_finiteDimensional_adicCompletion instAlgebraSubtypeMemValuationSubring_definitions AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersIntegersCompletion ModularCurve.KwF4gRRTate.instAlgebraKAdicCompletionIntegers AlgebraicCurve.Place.kw_ffgc_continuousSMul_adicCompletionComap AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersCompletionCompletion IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions AlgebraicCurve.instHasCanonicalLocalResidueK AlgebraicCurve.Place.instAlgebra_restrictResidueField AlgebraicCurve.Place.instIsScalarTower_restrictResidueField AlgebraicCurve.instHasLocalResidue AlgebraicCurve.HasSeparableResidue.of_perfectField_of_isCurveOver AlgebraicCurve.HasSeparableResidue.of_perfectField AlgebraicCurve.Place.instIsLocalHom_restrictSubringHom AlgebraicCurve.instHasCanonicalLocalResidueKStar ModularCurve.KwNo6Pin.isLocalRing_completion SheafOfModules.isIso_ihomModelToIhom AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instDecidableEqIdx AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instFintype AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instLinearOrder AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instFintypeIdx AlgebraicGeometry.OModulePresheaf.Leray.relAltC_scalarTower AlgebraicGeometry.OModulePresheaf.Leray.ker_relAltd_modΓ AlgebraicGeometry.OModulePresheaf.Leray.relAltC_modΓ AlgebraicGeometry.OModulePresheaf.Leray.biC_abGrp AlgebraicGeometry.OModulePresheaf.Leray.relAltH_modΓ AlgebraicGeometry.OModulePresheaf.Leray.ker_relAltd_smul AlgebraicGeometry.OModulePresheaf.Leray.relAltH_scalarTower AlgebraicGeometry.OModulePresheaf.Leray.relAltH_smul AlgebraicGeometry.OModulePresheaf.Leray.biC_module DoubleComplex.instModuleE₂I DoubleComplex.Bounded.modR"
p2m_attr_erase "instance" "DoubleComplex.instModuleE₂II DoubleComplex.instAddCommGroupE₂II DoubleComplex.Bounded.abGrp DoubleComplex.instAddCommGroupE₂I AlgebraicGeometry.ChowDatum.hι_closed AlgebraicGeometry.ChowDatumProj.hιN_closed AlgebraicGeometry.ChowDatumProj.hp_proper AlgebraicGeometry.ChowDatum.hp_isoU AlgebraicGeometry.ChowDatum.hp_proper AlgebraicGeometry.ProjSpace.algebraAway AlgebraicGeometry.ProjSpace.instIsProperProdOverπ AlgebraicGeometry.ChowDatumProj.hp_isoU AlgebraicGeometry.ProjSpace.isProper_π AlgebraicGeometry.ProjSpace.finiteType_mvPolynomial ProjSpaceCech.GradedModule.H.module ProjSpaceCech.GradedModule.H.addCommGroup ProjSpaceCech.GradedModule.sec.instAdd ProjSpaceCech.GradedModule.sec.instNeg ProjSpaceCech.GradedModule.acg ProjSpaceCech.GradedModule.Frac.setoid ProjSpaceCech.GradedModule.modR ProjSpaceCech.GradedModule.sec.instModule ProjSpaceCech.GradedModule.sec.instAddCommGroup ProjSpaceCech.GradedModule.sec.instZero ProjSpaceCech.GradedModule.Presentation.fJ ProjSpaceCech.GradedModule.sec.instSMul ProjSpaceCech.Twist.H.module ProjSpaceCech.Idx.instFintype ProjSpaceCech.Twist.H.addCommGroup ProjSpaceCech.Idx.instDecidableEq ProjSpaceCech.Twist.Mon.instDecidableEq ProjSpaceCech.Twist.cochain.instAddCommGroup ProjSpaceCech.Twist.cochain.instModule AlgebraicGeometry.FGSubalgebra.tensorStage_directedSystem AlgebraicGeometry.RelEffCartierDiv.isClosedImmersion_subschemeι_resProdMap AlgebraicGeometry.RelEffCartierDiv.isOpenImmersion_resProdMap AlgebraicCurve.CurveModel.locallyOfFiniteType_gluedToBase AlgebraicCurve.CurveModel.isFractionRing_overlap AlgebraicCurve.CurveModel.isLocallyNoetherian_glued AlgebraicCurve.CurveModel.jacobsonSpace_glued"
p2m_attr_erase "instance" "AlgebraicCurve.CurveModel.isOpenImmersion_ι₀ AlgebraicCurve.CurveModel.isIntegral_glued AlgebraicCurve.CurveModel.quasiSeparated_gluedToBase AlgebraicCurve.CurveModel.compactSpace_glued AlgebraicCurve.CurveModel.isIntegral_adjoin_chartRing AlgebraicCurve.CurveModel.isFractionRing_overlap_functionField AlgebraicCurve.CurveModel.isProper_gluedToBase AlgebraicCurve.CurveModel.isOpenImmersion_ιU AlgebraicCurve.CurveModel.isOpenImmersion_f₀ AlgebraicCurve.CurveModel.isOpenImmersion_fInf AlgebraicCurve.CurveModel.isOpenImmersion_ιInf AlgebraicCurve.CurveModel.algebra_overlap_functionField AlgebraicCurve.CurveModel.quasiCompact_gluedToBase AlgebraicCurve.CurveModel.algebraAdjoin AlgebraicCurve.CurveModel.isDedekindDomain_chartRing AlgebraicCurve.CurveModel.isIntegralClosure AlgebraicCurve.CurveModel.finite_chartRing AlgebraicCurve.CurveModel.centre_isPrime AlgebraicCurve.CurveModel.isFractionRing_chartRing AlgebraicCurve.CurveModel.finiteType_chartRing AlgebraicCurve.CurveModel.isNoetherianRing_chartRing AlgebraicCurve.CurveModel.isScalarTower_base_adjoin AlgebraicCurve.CurveModel.isScalarTower_adjoin AlgebraicCurve.CurveModel.chartRing_finitePresentation AlgebraicGeometry.ProjSpace.twistObj.addCommGroup AlgebraicGeometry.ProjSpace.twistFam.module AlgebraicGeometry.ProjSpace.twistObj.module AlgebraicGeometry.ProjSpace.twistObj.moduleSections AlgebraicGeometry.ProjSpace.twistFam.addCommGroup"
p2m_attr_erase "simp" "GoodReductionJacobian.RelativeGroupLaw.nsmul_zero GoodReductionJacobian.RelativeGroupLaw.mem_torsionSubset GoodReductionJacobian.RelativeGroupLaw.nsmul_succ GoodReductionJacobian.RelativeGroupLaw.baseChangePointToBase_ofBase GoodReductionJacobian.RelativeGroupLaw.baseChangePointToBase_coe GoodReductionJacobian.RelativeGroupLaw.baseChangePointOfBase_coe GoodReductionJacobian.RelativeGroupLaw.baseChange_inv GoodReductionJacobian.RelativeGroupLaw.baseChangePointOfBase_toBase GoodReductionJacobian.RelativeGroupLaw.baseChange_mul GoodReductionJacobian.RelativeGroupLaw.baseChange_one NeronModelInfra.NeronModelPropertyBundle.endExtensionEquiv_symm_restrict NeronModelInfra.schemeHomOverComp_id_left NeronModelInfra.schemeHomOverComp_id_right NeronModelInfra.schemeHomOverId_coe NeronModelInfra.NeronModelPropertyBundle.endExtensionEquiv_apply NeronModelInfra.NeronModelPropertyBundle.restrict_endExtensionEquiv_symm NeronModelInfra.schemeHomOverComp_coe NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_fst NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_snd NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_fst NeronSpecialFibreInfra.neronEndRestrictEquiv_apply NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_fst_assoc NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_snd NeronSpecialFibreInfra.neronEndExtension_genericFibreRestrict NeronSpecialFibreInfra.specClosedFibreInclusion_eq NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_fst_assoc NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_snd_assoc NeronSpecialFibreInfra.genericFibreRestrict_neronEndExtension NeronSpecialFibreInfra.homOverId_coe NeronSpecialFibreInfra.homOverComp_coe NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_snd_assoc GoodReductionJacobian.RelativeGroupLaw.fibre_inv GoodReductionJacobian.RelativeGroupLaw.fibrePointToBase_coe GoodReductionJacobian.RelativeGroupLaw.fibrePointOfBase_toBase GoodReductionJacobian.RelativeGroupLaw.fibre_mul GoodReductionJacobian.RelativeGroupLaw.fibrePointToBase_ofBase GoodReductionJacobian.RelativeGroupLaw.fibre_one GoodReductionJacobian.RelativeGroupLaw.fibrePointOfBase_coe RegularLocalRingQuotientAscent.dualNumberFst_apply NeronModelInfra.schemeHomOverNpow_succ"
p2m_attr_erase "simp" "NeronModelInfra.schemeHomOverNpow_zero GoodReductionJacobian.relativeGroupLawOfGrpObj_inv GoodReductionJacobian.relativeGroupLawOfGrpObj_mul GoodReductionJacobian.overHomEquivSchemeHomOver_apply_coe GoodReductionJacobian.relativeGroupLawOfGrpObj_one GoodReductionJacobian.overHomEquivSchemeHomOver_symm_apply_left SheafOfModules.tensorUnit_eq AlgebraicGeometry.Scheme.Modules.tensorUnit_eq PresheafOfModules.InternalHom.presheaf_map_apply PresheafOfModules.InternalHom.curryFamily_app PresheafOfModules.InternalHom.add_app PresheafOfModules.InternalHom.smul_app PresheafOfModules.InternalHom.zero_app PresheafOfModules.ihomObj_map_val PresheafOfModules.ihomFunctor_map PresheafOfModules.InternalHom.restrict_app PresheafOfModules.InternalHom.postcomp_app PresheafOfModules.InternalHom.neg_app PresheafOfModules.curry'_app_val PresheafOfModules.InternalHom.presheaf_obj PresheafOfModules.ihomFunctor_obj PresheafOfModules.ihomObj_obj PresheafOfModules.InternalHom.sub_app PresheafOfModules.ihomMap_app_val AlgebraicGeometry.Scheme.Modules.tensorPow_zero AlgebraicGeometry.Scheme.Modules.tensorPow_succ AlgebraicGeometry.RelPicard.RigidifiedLineBundle.mk.sizeOf_spec AlgebraicGeometry.RelPicard.RigidifiedLineBundle.mk.injEq AlgebraicGeometry.Scheme.OrderedAffineCover.mk.injEq AlgebraicGeometry.OModulePresheaf.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCover.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.mk.injEq AlgebraicGeometry.Scheme.TwoAffineOpenCover.mk.injEq AlgebraicGeometry.Scheme.TwoAffineOpenCover.mk.sizeOf_spec AlgebraicGeometry.Scheme.TwoAffineOpenCover.pullback_U1 AlgebraicGeometry.Scheme.TwoAffineOpenCover.pullback_U0 TwoChartCech.Sections.mk.injEq TwoChartCech.Cover.mk.injEq TwoChartCech.GrothendieckComplex.mk.injEq TwoChartCech.Sections.mk.sizeOf_spec"
p2m_attr_erase "simp" "TwoChartCech.Cover.mk.sizeOf_spec TwoChartCech.Cover.lineBundle_r0_apply TwoChartCech.GrothendieckComplex.mk.sizeOf_spec TwoChartCech.Cover.lineBundle_r1_apply CoherentBaseChange.TwoTermComplex.mk.sizeOf_spec CoherentBaseChange.TwoTermComplex.mk.injEq AlgebraicGeometry.OModulePresheaf.prod_obj AlgebraicGeometry.OModulePresheaf.restrOpen_obj AlgebraicGeometry.OModulePresheaf.DevissageStep.mk.injEq AlgebraicGeometry.OModulePresheaf.pushforward_obj AlgebraicGeometry.OModulePresheaf.im_obj AlgebraicGeometry.OModulePresheaf.pow_obj AlgebraicGeometry.OModulePresheaf.fstHom_app AlgebraicGeometry.OModulePresheaf.ker_obj AlgebraicGeometry.OModulePresheaf.coker_obj AlgebraicGeometry.OModulePresheaf.DevissageStep.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCover.preimage_U AlgebraicGeometry.OModulePresheaf.sndHom_app AlgebraicGeometry.OModulePresheaf.Hom.mk.injEq AlgebraicGeometry.OModulePresheaf.Hom.id_app AlgebraicGeometry.OModulePresheaf.AffHom.appSections_apply AlgebraicGeometry.OModulePresheaf.AffHom.comp_app AlgebraicGeometry.OModulePresheaf.AffSES.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.AffHom.kerMap_coe AlgebraicGeometry.OModulePresheaf.AffHom.id_app AlgebraicGeometry.OModulePresheaf.Hom.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.Hom.toAffHom_app AlgebraicGeometry.OModulePresheaf.SES.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.AffHom.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.Hom.comp_app AlgebraicGeometry.OModulePresheaf.SES.mk.injEq AlgebraicGeometry.OModulePresheaf.AffHom.mk.injEq AlgebraicGeometry.OModulePresheaf.Hom.appSections_apply AlgebraicGeometry.OModulePresheaf.AffSES.mk.injEq PresheafOfModules.freeεIso_hom_app PresheafOfModules.freeμIso_hom_app AlgebraicGeometry.RelPicard.RepresentsRelSubPic.mk.injEq AlgebraicGeometry.RelPicard.SubPicCondition.mk.injEq AlgebraicGeometry.RelPicard.SubPicCondition.mk.sizeOf_spec AlgebraicGeometry.RelPicard.RepresentsRelSubPic.mk.sizeOf_spec"
p2m_attr_erase "simp" "AlgebraicGeometry.SmoothProperCurve.sectionBaseChange_coe_snd AlgebraicGeometry.SmoothProperCurve.sectionBaseChange_coe_fst AlgebraicCurve.CurveModel.mk.injEq AlgebraicCurve.CurveModel.mk.sizeOf_spec AlgebraicCurve.mulAdele_apply AlgebraicCurve.residuePairing_apply_coe AlgebraicCurve.mem_adeleBdd AlgebraicCurve.weilSmul_one AlgebraicCurve.diagonalHom_apply AlgebraicCurve.weilSmul_apply AlgebraicCurve.adeleSpaceMul_coe AlgebraicCurve.mulAdele_one AlgebraicGeometry.SmoothProperCurve.FiniteMapData.twoAffineOpenCover_U1 AlgebraicGeometry.SmoothProperCurve.FiniteMapData.mk.injEq AlgebraicGeometry.SmoothProperCurve.FiniteMapData.mk.sizeOf_spec AlgebraicGeometry.SmoothProperCurve.FiniteMapData.twoAffineOpenCover_U0 AlgebraicGeometry.RelPicard.SubPicCondition.onClasses_mk AlgebraicGeometry.RelPicard.relSubPicPresheaf_map_coe CategoryTheory.Functor.OverTotal.ofFibre_fst CategoryTheory.Functor.overTotal_map_fst AlgebraicGeometry.Scheme.LocalRepresentabilityULift.glueData_J AlgebraicGeometry.Scheme.LocalRepresentabilityULift.uliftYoneda_toGlued_uliftYonedaGluedToSheaf AlgebraicGeometry.Scheme.LocalRepresentabilityULift.glueData_t' AlgebraicGeometry.Scheme.LocalRepresentabilityULift.uliftYoneda_toGlued_uliftYonedaGluedToSheaf_assoc AlgebraicGeometry.Scheme.LocalRepresentabilityULift.uliftYonedaGluedToSheaf_app_toGlued AlgebraicGeometry.Scheme.LocalRepresentabilityULift.glueData_openCover_map AlgebraicGeometry.Scheme.LocalRepresentabilityULift.uliftYonedaGluedToSheaf_app_comp AlgebraicGeometry.Scheme.LocalRepresentabilityULift.glueData_V AlgebraicGeometry.Scheme.LocalRepresentabilityULift.glueData_t AlgebraicGeometry.Scheme.LocalRepresentabilityULift.glueData_U AlgebraicGeometry.Scheme.LocalRepresentabilityULift.glueData_f AlgebraicGeometry.RelPicard.designationOfRepresentableBy_P AlgebraicGeometry.RelPicard.designationOfRepresentableBy_toBase AlgebraicGeometry.RelPicard.rigSection_snd AlgebraicGeometry.RelPicard.RigidifiedLineBundle.ofInvertible_L AlgebraicGeometry.RelPicard.rigSection_snd_assoc AlgebraicGeometry.RelPicard.SubPicGroupCondition.mk.injEq AlgebraicGeometry.RelPicard.SubPicGroupCondition.mk.sizeOf_spec AlgebraicCurve.coe_cechH0Equiv_apply AlgebraicCurve.cechH1ToH1_mk"
p2m_attr_erase "simp" "AlgebraicCurve.lSpaceOn_univ AlgebraicCurve.lSpaceOn_empty AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.jqNModC_one ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty"
p2m_attr_erase "simp" "AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one AlgebraicCurve.Place.differentialCoeff_zero AlgebraicCurve.Place.differentialCoeff_dCoord AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.injEq AlgebraicCurve.TranscendenceTower.mk.injEq AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec AlgebraicCurve.PoleDivisorPackage.mk.injEq AlgebraicGeometry.RelPicard.thetaBundle_def AlgebraicGeometry.RelPicard.picardBundle_def AlgebraicGeometry.RelEffCartierDiv.toRelEffDivisor_ofRelEffDivisor AlgebraicGeometry.RelEffCartierDiv.toRelEffDivisor_I AlgebraicGeometry.mapOnProdOver_fst_assoc AlgebraicGeometry.RelEffCartierDiv.mk.sizeOf_spec AlgebraicGeometry.RelEffCartierDiv.mk.injEq AlgebraicGeometry.mapOnProdOver_snd AlgebraicGeometry.mapOnProdOver_fst AlgebraicGeometry.mapOnProdOver_snd_assoc AlgebraicGeometry.mapOnProdOver_id AlgebraicCurve.RelEffDivisor.mk.sizeOf_spec AlgebraicCurve.mapOnProd_fst AlgebraicCurve.mapOnProd_fst_assoc AlgebraicCurve.mapOnProd_snd AlgebraicCurve.UnivDivisorPack.mk.injEq AlgebraicCurve.RelEffDivisor.mk.injEq AlgebraicCurve.UnivDivisorPack.mk.sizeOf_spec AlgebraicCurve.mapOnProd_snd_assoc AlgebraicGeometry.Scheme.Modules.exteriorPower_obj PresheafOfModules.exteriorPower_map_ιMulti PresheafOfModules.ExteriorPower.appₗ_apply AlgebraicGeometry.prodKerGraph_one AlgebraicGeometry.fibrePowOver.proj_comp AlgebraicGeometry.prodKerGraph_zero AlgebraicGeometry.RelEffCartierDiv.empty_I AlgebraicGeometry.fibrePowOver.proj_comp_assoc"
p2m_attr_erase "simp" "AlgebraicGeometry.graphOver_fst_assoc AlgebraicGeometry.RelEffCartierDiv.toPoint_comp AlgebraicGeometry.RelEffCartierDiv.toPoint_comp_assoc AlgebraicGeometry.graphOver_fst AlgebraicGeometry.RelEffCartierDiv.ofPoint_I AlgebraicGeometry.graphOver_snd AlgebraicGeometry.graphOver_snd_assoc AlgebraicCurve.SymmetricPowerPackage.mk.sizeOf_spec AlgebraicCurve.SymmetricPowerPackage.mk.injEq AlgebraicGeometry.FGSubalgebra.cocone_ι_app_apply AlgebraicGeometry.RelPicard.fst_toProdSpec AlgebraicGeometry.RelPicard.toProdSpec_fst_assoc AlgebraicGeometry.RelPicard.pointsSubBasepointModule_cons AlgebraicGeometry.RelPicard.pointsSubBasepointModule_nil AlgebraicGeometry.RelPicard.fst_toProdSpec_assoc AlgebraicGeometry.RelPicard.toProdSpec_fst AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.sub_app AlgebraicGeometry.Scheme.IdealSheafData.sres_sresTop AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.add_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.mk.sizeOf_spec AlgebraicGeometry.Scheme.IdealSheafData.coe_resLE AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.smul_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.coe_ofLE_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.ideal_range AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.zero_app AlgebraicGeometry.Scheme.IdealSheafData.sres_sres AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.comp_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.neg_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.id_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.coe_mulRight_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.nsmul_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.mk.injEq AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.zsmul_app AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.sizeOf_spec AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.injEq AlgebraicCurve.adeleSingle_coe AlgebraicCurve.kaehlerResidueTermKFam_apply AlgebraicCurve.Place.LocalResidueData.mk.injEq AlgebraicCurve.Place.LocalResidueData.mk.sizeOf_spec AlgebraicCurve.Place.kw_ffgc_adicCompletionComapIntegers_coe"
p2m_attr_erase "simp" "AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.sizeOf_spec AlgebraicCurve.Place.mem_simplePoleSubmodule AlgebraicCurve.Place.coe_uniformizerSubring ModularCurve.Lg37.Lg37CompletionSection.mk.injEq AlgebraicCurve.Place.CoefficientFieldSection.mk.injEq AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.injEq ModularCurve.Lg37.Lg37CompletionSection.mk.sizeOf_spec AlgebraicCurve.Place.CoefficientFieldSection.mk.sizeOf_spec AlgebraicCurve.Place.poleSubmodule_one AlgebraicCurve.Place.mem_poleSubmodule AlgebraicGeometry.Scheme.Modules.toUnitSection_ofUnitSection AlgebraicGeometry.Scheme.Modules.pullbackSection_def AlgebraicGeometry.Scheme.Modules.ofUnitSection_toUnitSection PresheafOfModules.InternalHom.IsSheafAux.appAt_toPresheafHom SheafOfModules.ihomSectionsEquivFamily_unit AlgebraicGeometry.Scheme.Modules.restrictHomEquivFamily_apply SheafOfModules.ihomEval_unit_app AlgebraicGeometry.Scheme.Modules.ihomEval_zero_right AlgebraicGeometry.Scheme.Modules.ihomEval_zero_left AlgebraicGeometry.Scheme.Modules.homOfFamily_app_apply SheafOfModules.unit_ihomSectionsEquivFamily AlgebraicGeometry.Scheme.Modules.familyOfHom_app AlgebraicGeometry.Scheme.Modules.restrictUnitIso_hom_app_apply AlgebraicGeometry.Scheme.Modules.restrictUnitIso_inv_app_apply AlgebraicGeometry.Scheme.Modules.restrictHomOfFamily_app_apply AlgebraicGeometry.Scheme.Modules.restrictHomEquivFamily_symm_apply AlgebraicGeometry.Scheme.Modules.tensorSections_zero_right AlgebraicGeometry.Scheme.Modules.map_unitSection AlgebraicGeometry.Scheme.Modules.tensorSectionsBilin_apply AlgebraicGeometry.Scheme.Modules.tensorPowSection_zero AlgebraicGeometry.Scheme.Modules.tensorSections_zero_left AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_neg AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_zero AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_sub AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_add AlgebraicGeometry.Scheme.OrderedAffineCover.toCoverOf_U AlgebraicGeometry.Scheme.OrderedAffineCoverOf.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCoverOf.mk.injEq AlgebraicGeometry.Scheme.OrderedAffineCover.restrict_U AlgebraicGeometry.OModulePresheaf.Leray.restrictToPreimage_U"
p2m_attr_erase "simp" "DoubleComplex.Bounded.mk.injEq DoubleComplex.Bounded.mk.sizeOf_spec DoubleComplex.Convergence.mk.injEq DoubleComplex.Convergence.mk.sizeOf_spec DoubleComplex.SubQuot.mk.sizeOf_spec DoubleComplex.SubQuot.mk.injEq AlgebraicGeometry.ChowDatumProj.mk.sizeOf_spec AlgebraicGeometry.ChowDatum.mk.sizeOf_spec AlgebraicGeometry.ChowDatumProj.mk.injEq AlgebraicGeometry.ChowDatum.mk.injEq ProjSpaceCech.GradedModule.mk.injEq ProjSpaceCech.GradedModule.mk.sizeOf_spec ProjSpaceCech.GradedModule.Frac.mk.sizeOf_spec ProjSpaceCech.GradedModule.Presentation.mk.injEq ProjSpaceCech.GradedModule.Frac.mk.injEq ProjSpaceCech.GradedModule.Presentation.mk.sizeOf_spec ProjSpaceCech.GradedModule.Hom.shift_toLinearMap ProjSpaceCech.GradedModule.Hom.mk.sizeOf_spec ProjSpaceCech.GradedModule.Hom.mk.injEq TwoChartCech.Mumford.dK_apply TwoChartCech.Mumford.ι0_apply TwoChartCech.Mumford.ι1_apply TwoChartCech.KerCoprod.dK_apply TwoChartCech.KerCoprod.ι1_apply TwoChartCech.KerCoprod.ι0_apply AlgebraicGeometry.tilde.functorCompPullbackSpecIso_app AlgebraicGeometry.RelPicard.algEquivZeroGroupCut_toSubPicCondition AlgebraicGeometry.RelPicard.LFP.stageHom_val AlgebraicGeometry.RelPicard.BaseChange.relSubPicPresheafRestrictIso_hom_app_coe AlgebraicGeometry.RelPicard.BaseChange.relSubPicPresheafRestrictIso_inv_app_coe AlgebraicGeometry.RelPicard.BaseChange.restrict_P AlgebraicGeometry.RelEffCartierDiv.IsUniversal.lift_comp AlgebraicGeometry.RelEffCartierDiv.functor_map_fst AlgebraicGeometry.RelEffCartierDiv.IsUniversal.homEquiv_apply AlgebraicGeometry.RelEffCartierDiv.IsUniversal.lift_pullbackAlong AlgebraicGeometry.RelEffCartierDiv.IsUniversal.homEquiv_symm_apply AlgebraicGeometry.RelEffCartierDiv.IsUniversal.lift_comp_assoc AlgebraicGeometry.RelEffCartierDiv.supportedIn_top AlgebraicGeometry.RelEffCartierDiv.mem_supportedIn_iff AlgebraicGeometry.RelEffCartierDiv.supportedIn_top_eq"
p2m_attr_erase "simp" "AlgebraicGeometry.RelEffCartierDiv.restrictAlong_extendAlong AlgebraicGeometry.RelEffCartierDiv.extendAlong_I AlgebraicGeometry.RelEffCartierDiv.resProdMap_snd AlgebraicGeometry.RelEffCartierDiv.restrictAlong_I AlgebraicGeometry.RelEffCartierDiv.extendAlong_restrictAlong AlgebraicGeometry.RelEffCartierDiv.resProdMap_fst_assoc AlgebraicGeometry.RelEffCartierDiv.resProdMap_snd_assoc AlgebraicGeometry.RelEffCartierDiv.resProdMap_fst CoherentBaseChange.FibreH0Family.mk.sizeOf_spec CoherentBaseChange.FibreH0Family.mk.injEq AlgebraicGeometry.Scheme.Modules.ProjPresentation.mk.injEq AlgebraicGeometry.Scheme.Modules.ProjPresentation.mk.sizeOf_spec AlgebraicCurve.CurveModel.coe_gInf AlgebraicCurve.CurveModel.coe_tInvChart AlgebraicCurve.CurveModel.ιInf_gluedToBase_assoc AlgebraicCurve.CurveModel.ιInf_gluedToBase AlgebraicCurve.CurveModel.primeOfι₀_asIdeal AlgebraicCurve.CurveModel.coe_tChart AlgebraicCurve.CurveModel.ι₀_gluedToBase_assoc AlgebraicCurve.CurveModel.primeOfιInf_asIdeal AlgebraicCurve.CurveModel.ι₀_gluedToBase AlgebraicCurve.CurveModel.coe_tma AlgebraicCurve.CurveModel.coe_primeEquivChartPlaces AlgebraicGeometry.ProjSpace.twistObj.mk.injEq AlgebraicGeometry.ProjSpace.twistObj.zero_val AlgebraicGeometry.ProjSpace.twistObj.add_val AlgebraicGeometry.ProjSpace.twist_res_val AlgebraicGeometry.ProjSpace.twist_smul_val AlgebraicGeometry.ProjSpace.twistGradeToObj_val AlgebraicGeometry.ProjSpace.twistObj.smul_val AlgebraicGeometry.ProjSpace.twistGradeEquiv_apply_val AlgebraicGeometry.ProjSpace.twistObj.mk.sizeOf_spec AlgebraicGeometry.schemeFibreEndo_snd AlgebraicGeometry.schemeFibreEndo_fst"

set_option autoImplicit false

section
open scoped TensorProduct Quaternion NumberField
open CategoryTheory AlgebraicGeometry IsDedekindDomain CerednikDrinfeld CerednikDrinfeld.QM CerednikDrinfeld.FormalOmega NeronModelInfra QuaternionAlgebra

namespace G3Aux

theorem isTwistedAct_inv
    {𝒪 : Type} [CommRing 𝒪] {K₀ : Type} [Field K₀] [Algebra 𝒪 K₀] (π : 𝒪)
    (Onr : Type) [CommRing Onr] [Algebra 𝒪 Onr] (Fr : Onr ≃ₐ[𝒪] Onr)
    (vdet : Matrix.GeneralLinearGroup (Fin 2) K₀ →* Multiplicative ℤ)
    (B : Type) [CommRing B] [Algebra 𝒪 B] (g : Matrix.GeneralLinearGroup (Fin 2) K₀)
    (x y : (AlgFunctor.prod (AlgFunctor.corep Onr) (Omega K₀ π)).obj B)
    (h : OmegaNr.IsTwistedAct π Onr Fr vdet B g x y) :
    OmegaNr.IsTwistedAct π Onr Fr vdet B g⁻¹ y x := by
  obtain ⟨hfun, hex, hone, hcomp, -⟩ := OmegaNr.isTwistedAct_laws (K₀ := K₀) π Onr Fr vdet
  obtain ⟨z, hz⟩ := hex B g⁻¹ y
  have hxz : OmegaNr.IsTwistedAct π Onr Fr vdet B (g⁻¹ * g) x z := hcomp B g g⁻¹ x y z h hz
  rw [inv_mul_cancel] at hxz
  have hzx : z = x := hfun B 1 x z x hxz (hone B x)
  exact hzx ▸ hz

theorem isTwistedAct_assembly
    {𝒪 : Type} [CommRing 𝒪] {K₀ : Type} [Field K₀] [Algebra 𝒪 K₀] (π : 𝒪)
    (Onr : Type) [CommRing Onr] [Algebra 𝒪 Onr] (Fr : Onr ≃ₐ[𝒪] Onr)
    (vdet : Matrix.GeneralLinearGroup (Fin 2) K₀ →* Multiplicative ℤ)
    (B : Type) [CommRing B] [Algebra 𝒪 B] (g₀ S M : Matrix.GeneralLinearGroup (Fin 2) K₀)
    (hS : ∀ h : Matrix.GeneralLinearGroup (Fin 2) K₀, S * h = h * S)
    (X X' Y Y' : (AlgFunctor.prod (AlgFunctor.corep Onr) (Omega K₀ π)).obj B)
    (h1 : OmegaNr.IsTwistedAct π Onr Fr vdet B g₀⁻¹ X Y)
    (h2 : OmegaNr.IsTwistedAct π Onr Fr vdet B g₀⁻¹ X' Y')
    (h3 : OmegaNr.IsTwistedAct π Onr Fr vdet B (S * (g₀ * M * g₀⁻¹)) X X') :
    OmegaNr.IsTwistedAct π Onr Fr vdet B (S * M) Y Y' := by
  obtain ⟨hfun, hex, hone, hcomp, -⟩ := OmegaNr.isTwistedAct_laws (K₀ := K₀) π Onr Fr vdet
  have a := isTwistedAct_inv π Onr Fr vdet B g₀⁻¹ X Y h1
  rw [inv_inv] at a
  have b := hcomp B _ _ Y X X' a h3
  have c := hcomp B _ _ Y X' Y' b h2
  have key : g₀⁻¹ * (S * (g₀ * M * g₀⁻¹) * g₀) = S * M := by
    calc g₀⁻¹ * (S * (g₀ * M * g₀⁻¹) * g₀) = g₀⁻¹ * S * g₀ * M := by group
      _ = g₀⁻¹ * g₀ * S * M := by rw [mul_assoc g₀⁻¹ S g₀, hS g₀, ← mul_assoc]
      _ = S * M := by simp
  rwa [key] at c

end G3Aux

namespace G3Aux
theorem exists_center_r
    {r : ℕ} [Fact r.Prime] {K₀ : Type} [Field K₀] [CharZero K₀]
    {a₁ b₁ : ℚ} (R₁ : Submodule ℤ ℍ[ℚ, a₁, b₁]) {N : ℕ} (hR₁ : IsEichlerOrder R₁ N)
    (ι₀ : ℍ[ℚ, a₁, b₁] →ₐ[ℚ] Matrix (Fin 2) (Fin 2) K₀)
    (v : HeightOneSpectrum (𝓞 ℚ)) (hv : ((r : ℕ) : 𝓞 ℚ) ∈ v.asIdeal)
    (Γt : Subgroup (ℍ[ℚ, a₁, b₁])ˣ) (hΓt : ∀ x : (ℍ[ℚ, a₁, b₁])ˣ, x ∈ Γt ↔ x ∈ CerednikDrinfeld.CosetGraph.awayUnits R₁ v) :
    ∃ (z : (ℍ[ℚ, a₁, b₁])ˣ) (_ : z ∈ Γt),
      (Units.map (ι₀ : ℍ[ℚ, a₁, b₁] →* Matrix (Fin 2) (Fin 2) K₀)) z =
        (Units.map (algebraMap K₀ (Matrix (Fin 2) (Fin 2) K₀)).toMonoidHom (Units.mk0 (r : K₀) (Nat.cast_ne_zero.mpr (Fact.out : r.Prime).ne_zero))) ∧
      (z : ℍ[ℚ, a₁, b₁]) = (r : ℍ[ℚ, a₁, b₁]) := by
  have hr0 : (r : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (Fact.out : r.Prime).ne_zero
  let z : (ℍ[ℚ, a₁, b₁])ˣ := Units.map (algebraMap ℚ ℍ[ℚ, a₁, b₁]).toMonoidHom (Units.mk0 (r : ℚ) hr0)
  have hzval : (z : ℍ[ℚ, a₁, b₁]) = (r : ℍ[ℚ, a₁, b₁]) := by
    simp [z]
  have hzinv : ((z⁻¹ : (ℍ[ℚ, a₁, b₁])ˣ) : ℍ[ℚ, a₁, b₁]) = (r : ℚ)⁻¹ • (1 : ℍ[ℚ, a₁, b₁]) := by
    rw [← Algebra.algebraMap_eq_smul_one]
    rfl
  have hO : IsOrder R₁ := hR₁.isOrder
  have hmem := (CerednikDrinfeld.CosetGraph.mem_awayUnits_iff_exists_pow_smul_mem_of_forall_localBox_eq R₁ R₁ hO hO r v hv
    (fun _ _ => rfl)).1 z
  refine ⟨z, (hΓt z).2 (hmem.2 ⟨0, 1, ?_, ?_⟩), ?_, hzval⟩
  · rw [hzval]
    simp only [pow_zero, Nat.cast_one, one_smul]
    have h1 : ((r : ℤ) • (1 : ℍ[ℚ, a₁, b₁])) ∈ R₁ := R₁.smul_mem (r : ℤ) hO.one_mem
    rwa [zsmul_one, Int.cast_natCast] at h1
  · rw [hzinv]
    simpa [hr0] using hO.one_mem
  · ext
    simp [z]

end G3Aux

namespace G3Aux

open CerednikDrinfeld.QM.FakeEllipticCurve in

theorem isIsogenyPair_trans {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} {N : ℕ} {S : Type} [CommRing S]
    (hΛℤ : ∀ m : ℤ, ((m : ℚ) : ℍ[ℚ, a, b]) ∈ Λ)
    {E E' E'' : FakeEllipticCurve Λ N S} {d₁ d₂ : ℕ}
    {φ₁ : E.A ⟶ E'.A} {ψ₁ : E'.A ⟶ E.A} {φ₂ : E'.A ⟶ E''.A} {ψ₂ : E''.A ⟶ E'.A}
    (h₁ : IsIsogenyPair d₁ E E' φ₁ ψ₁) (h₂ : IsIsogenyPair d₂ E' E'' φ₂ ψ₂) :
    IsIsogenyPair (d₁ * d₂) E E'' (φ₁ ≫ φ₂) (ψ₂ ≫ ψ₁) := by
  obtain ⟨hφ₁, hψ₁, hm₁, hm₁', ha₁, ha₁', hc₁⟩ := h₁
  obtain ⟨hφ₂, hψ₂, hm₂, hm₂', ha₂, ha₂', hc₂⟩ := h₂
  have hd₁ : ((d₁ : ℚ) : ℍ[ℚ, a, b]) ∈ Λ := by simpa using hΛℤ d₁
  have hd₂ : ((d₂ : ℚ) : ℍ[ℚ, a, b]) ∈ Λ := by simpa using hΛℤ d₂
  have hφ : (φ₁ ≫ φ₂) ≫ E''.f = E.f := by rw [Category.assoc, hφ₂, hφ₁]
  have hψ : (ψ₂ ≫ ψ₁) ≫ E.f = E''.f := by rw [Category.assoc, hψ₁, hψ₂]
  have eφ : ∀ {T : Scheme.{0}} {t : T ⟶ Spec (CommRingCat.of S)} (R : SchemeHomOver t E.f),
      mapPt (φ₁ ≫ φ₂) hφ R = mapPt φ₂ hφ₂ (mapPt φ₁ hφ₁ R) := fun R => Subtype.ext (by simp [mapPt])
  have eψ : ∀ {T : Scheme.{0}} {t : T ⟶ Spec (CommRingCat.of S)} (R : SchemeHomOver t E''.f),
      mapPt (ψ₂ ≫ ψ₁) hψ R = mapPt ψ₁ hψ₁ (mapPt ψ₂ hψ₂ R) := fun R => Subtype.ext (by simp [mapPt])
  refine ⟨hφ, hψ, ?_, ?_, ?_, ?_, ?_⟩
  · intro T t P Q
    rw [eφ, eφ, eφ, hm₁, hm₂]
  · intro T t P Q
    rw [eψ, eψ, eψ, hm₂', hm₁']
  · intro x
    rw [← Category.assoc, ha₁, Category.assoc, ha₂, Category.assoc]
  · intro x
    rw [← Category.assoc, ha₂', Category.assoc, ha₁', Category.assoc]
  · intro hd
    obtain ⟨c₁, c₁'⟩ := hc₁ hd₁
    obtain ⟨c₂, c₂'⟩ := hc₂ hd₂
    have e₂₁ : ((d₂ : ℚ) : ℍ[ℚ, a, b]) * ((d₁ : ℚ) : ℍ[ℚ, a, b]) = (((d₁ * d₂ : ℕ) : ℚ) : ℍ[ℚ, a, b]) := by
      rw [← QuaternionAlgebra.coe_mul]; congr 1; push_cast; ring
    have e₁₂ : ((d₁ : ℚ) : ℍ[ℚ, a, b]) * ((d₂ : ℚ) : ℍ[ℚ, a, b]) = (((d₁ * d₂ : ℕ) : ℚ) : ℍ[ℚ, a, b]) := by
      rw [← QuaternionAlgebra.coe_mul]; congr 1; push_cast; ring
    have hprod : ((d₂ : ℚ) : ℍ[ℚ, a, b]) * ((d₁ : ℚ) : ℍ[ℚ, a, b]) ∈ Λ := e₂₁ ▸ hd
    have hprod' : ((d₁ : ℚ) : ℍ[ℚ, a, b]) * ((d₂ : ℚ) : ℍ[ℚ, a, b]) ∈ Λ := e₁₂ ▸ hd
    have key : (⟨(((d₁ * d₂ : ℕ) : ℚ) : ℍ[ℚ, a, b]), hd⟩ : ↥Λ) =
        ⟨((d₂ : ℚ) : ℍ[ℚ, a, b]) * ((d₁ : ℚ) : ℍ[ℚ, a, b]), hprod⟩ := Subtype.ext e₂₁.symm
    have key' : (⟨(((d₁ * d₂ : ℕ) : ℚ) : ℍ[ℚ, a, b]), hd⟩ : ↥Λ) =
        ⟨((d₁ : ℚ) : ℍ[ℚ, a, b]) * ((d₂ : ℚ) : ℍ[ℚ, a, b]), hprod'⟩ := Subtype.ext e₁₂.symm
    constructor
    · calc (φ₁ ≫ φ₂) ≫ ψ₂ ≫ ψ₁ = φ₁ ≫ (φ₂ ≫ ψ₂) ≫ ψ₁ := by simp only [Category.assoc]
        _ = φ₁ ≫ E'.act ⟨((d₂ : ℚ) : ℍ[ℚ, a, b]), hd₂⟩ ≫ ψ₁ := by rw [c₂]
        _ = φ₁ ≫ ψ₁ ≫ E.act ⟨((d₂ : ℚ) : ℍ[ℚ, a, b]), hd₂⟩ := by rw [ha₁']
        _ = E.act ⟨((d₁ : ℚ) : ℍ[ℚ, a, b]), hd₁⟩ ≫ E.act ⟨((d₂ : ℚ) : ℍ[ℚ, a, b]), hd₂⟩ := by
            rw [← Category.assoc, c₁]
        _ = E.act ⟨(((d₁ * d₂ : ℕ) : ℚ) : ℍ[ℚ, a, b]), hd⟩ := by
            rw [key, E.act_mul ⟨((d₂ : ℚ) : ℍ[ℚ, a, b]), hd₂⟩ ⟨((d₁ : ℚ) : ℍ[ℚ, a, b]), hd₁⟩ hprod]
    · calc (ψ₂ ≫ ψ₁) ≫ φ₁ ≫ φ₂ = ψ₂ ≫ (ψ₁ ≫ φ₁) ≫ φ₂ := by simp only [Category.assoc]
        _ = ψ₂ ≫ E'.act ⟨((d₁ : ℚ) : ℍ[ℚ, a, b]), hd₁⟩ ≫ φ₂ := by rw [c₁']
        _ = ψ₂ ≫ φ₂ ≫ E''.act ⟨((d₁ : ℚ) : ℍ[ℚ, a, b]), hd₁⟩ := by rw [ha₂]
        _ = E''.act ⟨((d₂ : ℚ) : ℍ[ℚ, a, b]), hd₂⟩ ≫ E''.act ⟨((d₁ : ℚ) : ℍ[ℚ, a, b]), hd₁⟩ := by
            rw [← Category.assoc, c₂']
        _ = E''.act ⟨(((d₁ * d₂ : ℕ) : ℚ) : ℍ[ℚ, a, b]), hd⟩ := by
            rw [key', E''.act_mul ⟨((d₁ : ℚ) : ℍ[ℚ, a, b]), hd₁⟩ ⟨((d₂ : ℚ) : ℍ[ℚ, a, b]), hd₂⟩ hprod']

end G3Aux

namespace G3Aux

theorem mapPt_hom_inv {R : Type} [CommRing R] {A A' : Scheme.{0}} {f : A ⟶ Spec (CommRingCat.of R)} {f' : A' ⟶ Spec (CommRingCat.of R)}
    (i : A ≅ A') (hi : i.hom ≫ f' = f) (hi' : i.inv ≫ f = f') {T : Scheme.{0}} {t : T ⟶ Spec (CommRingCat.of R)}
    (P : SchemeHomOver t f) : mapPt i.inv hi' (mapPt i.hom hi P) = P :=
  Subtype.ext (by simp [mapPt])

theorem mapPt_inv_hom {R : Type} [CommRing R] {A A' : Scheme.{0}} {f : A ⟶ Spec (CommRingCat.of R)} {f' : A' ⟶ Spec (CommRingCat.of R)}
    (i : A ≅ A') (hi : i.hom ≫ f' = f) (hi' : i.inv ≫ f = f') {T : Scheme.{0}} {t : T ⟶ Spec (CommRingCat.of R)}
    (P : SchemeHomOver t f') : mapPt i.hom hi (mapPt i.inv hi' P) = P :=
  Subtype.ext (by simp [mapPt])

open CerednikDrinfeld.QM.FakeEllipticCurve in

theorem isIsogenyPair_one_of_isoVia {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} {N : ℕ} {S : Type} [CommRing S]
    {E E' : FakeEllipticCurve Λ N S} (i : E.A ≅ E'.A) (hi : i.hom ≫ E'.f = E.f) (h : IsoVia E E' i hi) :
    IsIsogenyPair 1 E E' i.hom i.inv := by
  obtain ⟨hm, ha, -⟩ := h
  have hi' : i.inv ≫ E.f = E'.f := by rw [← hi, Iso.inv_hom_id_assoc]
  refine ⟨hi, hi', hm, ?_, ha, ?_, ?_⟩
  · intro T t P Q
    have := hm t (mapPt i.inv hi' P) (mapPt i.inv hi' Q)
    rw [mapPt_inv_hom, mapPt_inv_hom] at this
    rw [← this, mapPt_hom_inv]
  · intro x
    rw [Iso.eq_inv_comp, ← Category.assoc, ← ha, Category.assoc, Iso.hom_inv_id, Category.comp_id]
  · intro hd
    have h1 : (⟨(((1 : ℕ) : ℚ) : ℍ[ℚ, a, b]), hd⟩ : ↥Λ) = ⟨1, by simpa using hd⟩ := Subtype.ext (by simp)
    rw [h1, E.act_one, E'.act_one]
    exact ⟨i.hom_inv_id, i.inv_hom_id⟩

end G3Aux

namespace G3Aux

theorem scalar_central {K₀ : Type} [Field K₀] (u : K₀ˣ) (c : ℤ) (h : Matrix.GeneralLinearGroup (Fin 2) K₀) :
    (Units.map (algebraMap K₀ (Matrix (Fin 2) (Fin 2) K₀)).toMonoidHom u) ^ c * h =
      h * (Units.map (algebraMap K₀ (Matrix (Fin 2) (Fin 2) K₀)).toMonoidHom u) ^ c := by
  have h1 : Commute ((Units.map (algebraMap K₀ (Matrix (Fin 2) (Fin 2) K₀)).toMonoidHom u)) h := by
    rw [Commute, SemiconjBy]
    ext
    simp [Algebra.commutes]
  exact (h1.zpow_left c).eq
end G3Aux

end

section
open scoped Quaternion
open CategoryTheory AlgebraicGeometry CerednikDrinfeld CerednikDrinfeld.QM NeronModelInfra

namespace G3Aux

theorem mapPt_hom_inv' {R : Type} [CommRing R] {A A' : Scheme.{0}} {f : A ⟶ Spec (CommRingCat.of R)} {f' : A' ⟶ Spec (CommRingCat.of R)}
    (i : A ≅ A') (hi : i.hom ≫ f' = f) (hi' : i.inv ≫ f = f') {T : Scheme.{0}} {t : T ⟶ Spec (CommRingCat.of R)}
    (P : SchemeHomOver t f) : mapPt i.inv hi' (mapPt i.hom hi P) = P :=
  Subtype.ext (by simp [mapPt])

theorem mapPt_inv_hom' {R : Type} [CommRing R] {A A' : Scheme.{0}} {f : A ⟶ Spec (CommRingCat.of R)} {f' : A' ⟶ Spec (CommRingCat.of R)}
    (i : A ≅ A') (hi : i.hom ≫ f' = f) (hi' : i.inv ≫ f = f') {T : Scheme.{0}} {t : T ⟶ Spec (CommRingCat.of R)}
    (P : SchemeHomOver t f') : mapPt i.hom hi (mapPt i.inv hi' P) = P :=
  Subtype.ext (by simp [mapPt])

open CerednikDrinfeld.QM.FakeEllipticCurve in

theorem isIsogenyPair_one_of_iso {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} {N : ℕ} {S : Type} [CommRing S]
    {E E' : FakeEllipticCurve Λ N S} (i : E.A ≅ E'.A) (hi : i.hom ≫ E'.f = E.f)
    (hm : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of S)) (P Q : SchemeHomOver t E.f),
      mapPt i.hom hi (E.L.mul t P Q) = E'.L.mul t (mapPt i.hom hi P) (mapPt i.hom hi Q))
    (ha : ∀ x : ↥Λ, E.act x ≫ i.hom = i.hom ≫ E'.act x) :
    IsIsogenyPair 1 E E' i.hom i.inv := by
  have hi' : i.inv ≫ E.f = E'.f := by rw [← hi, Iso.inv_hom_id_assoc]
  refine ⟨hi, hi', hm, ?_, ha, ?_, ?_⟩
  · intro T t P Q
    have := hm t (mapPt i.inv hi' P) (mapPt i.inv hi' Q)
    rw [mapPt_inv_hom', mapPt_inv_hom'] at this
    rw [← this, mapPt_hom_inv']
  · intro x
    rw [Iso.eq_inv_comp, ← Category.assoc, ← ha, Category.assoc, Iso.hom_inv_id, Category.comp_id]
  · intro hd
    have h1 : (⟨(((1 : ℕ) : ℚ) : ℍ[ℚ, a, b]), hd⟩ : ↥Λ) = ⟨1, by simpa using hd⟩ := Subtype.ext (by simp)
    rw [h1, E.act_one, E'.act_one]
    exact ⟨i.hom_inv_id, i.inv_hom_id⟩

theorem mul_val_congr {S : Type} [CommRing S] {A : Scheme.{0}} {f : A ⟶ Spec (CommRingCat.of S)}
    (L : GoodReductionJacobian.RelativeGroupLaw S f) {T : Scheme.{0}} (t t' : T ⟶ Spec (CommRingCat.of S)) (h : t = t')
    (P Q : SchemeHomOver t f) (P' Q' : SchemeHomOver t' f) (hP : P.1 = P'.1) (hQ : Q.1 = Q'.1) :
    (L.mul t P Q).1 = (L.mul t' P' Q').1 := by
  subst h
  rw [Subtype.ext hP, Subtype.ext hQ]

open CerednikDrinfeld.QM.FakeEllipticCurve in

theorem exists_iso_of_isPullbackVia_id {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} {N : ℕ} {S : Type} [CommRing S]
    {E₁ E₂ : FakeEllipticCurve Λ N S} (u : E₂.A ⟶ E₁.A) (hu : IsPullbackVia (RingHom.id S) E₁ E₂ u) :
    ∃ (i : E₂.A ≅ E₁.A) (hi : i.hom ≫ E₁.f = E₂.f), i.hom = u ∧
      IsIsogenyPair 1 E₂ E₁ i.hom i.inv ∧ PreservesLevel E₂ E₁ i.hom hi := by
  obtain ⟨hg, hmul, hact, hlev⟩ := hu
  have hid : Spec.map (CommRingCat.ofHom (RingHom.id S)) = 𝟙 _ := by
    rw [CommRingCat.ofHom_id, Spec.map_id]
  have hw : u ≫ E₁.f = E₂.f := by simpa [hid] using hg.w
  haveI : IsIso u := hg.isIso_fst_of_isIso (inst := by rw [hid]; infer_instance)
  refine ⟨asIso u, hw, rfl, ?_, ?_⟩
  · refine isIsogenyPair_one_of_iso (asIso u) hw ?_ hact
    intro T t P Q
    apply Subtype.ext
    simp only [mapPt, asIso_hom]
    rw [hmul t P Q]
    exact mul_val_congr E₁.L _ _ (by rw [hid, Category.comp_id]) _ _ _ _ rfl rfl
  · intro T t P hP
    obtain ⟨P₀, hP₀⟩ := hlev t P hP
    exact ⟨P₀, hP₀⟩

end G3Aux

end

section
open scoped Quaternion
open CategoryTheory AlgebraicGeometry CerednikDrinfeld CerednikDrinfeld.QM NeronModelInfra

namespace G3Aux

theorem mapPt_hom_inv'' {R : Type} [CommRing R] {A A' : Scheme.{0}} {f : A ⟶ Spec (CommRingCat.of R)} {f' : A' ⟶ Spec (CommRingCat.of R)}
    (i : A ≅ A') (hi : i.hom ≫ f' = f) (hi' : i.inv ≫ f = f') {T : Scheme.{0}} {t : T ⟶ Spec (CommRingCat.of R)}
    (P : SchemeHomOver t f) : mapPt i.inv hi' (mapPt i.hom hi P) = P :=
  Subtype.ext (by simp [mapPt])

theorem mapPt_inv_hom'' {R : Type} [CommRing R] {A A' : Scheme.{0}} {f : A ⟶ Spec (CommRingCat.of R)} {f' : A' ⟶ Spec (CommRingCat.of R)}
    (i : A ≅ A') (hi : i.hom ≫ f' = f) (hi' : i.inv ≫ f = f') {T : Scheme.{0}} {t : T ⟶ Spec (CommRingCat.of R)}
    (P : SchemeHomOver t f') : mapPt i.hom hi (mapPt i.inv hi' P) = P :=
  Subtype.ext (by simp [mapPt])

theorem mul_val_congr' {S : Type} [CommRing S] {A : Scheme.{0}} {f : A ⟶ Spec (CommRingCat.of S)}
    (L : GoodReductionJacobian.RelativeGroupLaw S f) {T : Scheme.{0}} (t t' : T ⟶ Spec (CommRingCat.of S)) (h : t = t')
    (P Q : SchemeHomOver t f) (P' Q' : SchemeHomOver t' f) (hP : P.1 = P'.1) (hQ : Q.1 = Q'.1) :
    (L.mul t P Q).1 = (L.mul t' P' Q').1 := by
  subst h
  rw [Subtype.ext hP, Subtype.ext hQ]

open CerednikDrinfeld.QM.FakeEllipticCurve in

theorem isPullbackVia_comp_inv_of_isoVia {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} {N : ℕ}
    {B B' : Type} [CommRing B] [CommRing B'] (φ : B →+* B')
    {E E' : FakeEllipticCurve Λ N B} (i : E.A ≅ E'.A) (hi : i.hom ≫ E'.f = E.f) (hvia : IsoVia E E' i hi)
    {X : FakeEllipticCurve Λ N B'} (g : X.A ⟶ E'.A) (hg : IsPullbackVia φ E' X g) :
    IsPullbackVia φ E X (g ≫ i.inv) := by
  obtain ⟨hpb, hmul, hact, hlev⟩ := hg
  obtain ⟨him, hia, hil⟩ := hvia
  have hi' : i.inv ≫ E.f = E'.f := by rw [← hi, Iso.inv_hom_id_assoc]
  have sq2 : IsPullback i.inv E'.f E.f (𝟙 _) := IsPullback.of_horiz_isIso ⟨by simp [hi']⟩
  have hpb' : IsPullback (g ≫ i.inv) X.f E.f (Spec.map (CommRingCat.ofHom φ)) := by
    simpa using hpb.paste_horiz sq2
  have hinv : ∀ {T : Scheme.{0}} (s : T ⟶ Spec (CommRingCat.of B)) (A' B'' : SchemeHomOver s E'.f),
      mapPt i.inv hi' (E'.L.mul s A' B'') = E.L.mul s (mapPt i.inv hi' A') (mapPt i.inv hi' B'') := by
    intro T s A' B''
    have := him s (mapPt i.inv hi' A') (mapPt i.inv hi' B'')
    rw [mapPt_inv_hom'', mapPt_inv_hom''] at this
    rw [← this, mapPt_hom_inv'']
  refine ⟨hpb', ?_, ?_, ?_⟩
  · intro T t P Q
    have h1 := hmul t P Q
    have h2 := congrArg Subtype.val (hinv (t ≫ Spec.map (CommRingCat.ofHom φ))
      ⟨P.1 ≫ g, by rw [Category.assoc, hpb.w, ← Category.assoc, P.2]⟩
      ⟨Q.1 ≫ g, by rw [Category.assoc, hpb.w, ← Category.assoc, Q.2]⟩)
    simp only [mapPt] at h2
    rw [← Category.assoc, h1, h2]
    exact mul_val_congr' E.L _ _ rfl _ _ _ _ (by simp) (by simp)
  · intro x
    have hia' : E'.act x ≫ i.inv = i.inv ≫ E.act x := by
      rw [Iso.eq_inv_comp, ← Category.assoc, ← hia, Category.assoc, Iso.hom_inv_id, Category.comp_id]
    rw [← Category.assoc, hact, Category.assoc, hia', Category.assoc]
  · intro T t P hP
    obtain ⟨P₁, hP₁⟩ := hlev t P hP
    have pf : (P.1 ≫ g) ≫ E'.f = t ≫ Spec.map (CommRingCat.ofHom φ) := by
      rw [Category.assoc, hpb.w, ← Category.assoc, P.2]
    have hQ : FactorsThrough E'.lev (⟨P.1 ≫ g, pf⟩ : SchemeHomOver _ E'.f) := ⟨P₁, hP₁⟩
    have h3 := (hil _ (mapPt i.inv hi' ⟨P.1 ≫ g, pf⟩)).2 (by rwa [mapPt_inv_hom''])
    obtain ⟨P₀, hP₀⟩ := h3
    exact ⟨P₀, by rw [hP₀]; simp [mapPt]⟩

end G3Aux

end

section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian QuaternionAlgebra CerednikDrinfeld CerednikDrinfeld.QM
open CerednikDrinfeld.QM.FakeEllipticCurve
open scoped Quaternion

namespace G3Dual

variable {k : Type} [Field k] {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} {N : ℕ} (E : FakeEllipticCurve Λ N k)

theorem intCast_mem_of_one_mem (h1 : (1 : ℍ[ℚ, a, b]) ∈ Λ) (m : ℤ) : ((m : ℚ) : ℍ[ℚ, a, b]) ∈ Λ := by
  have e : ((m : ℚ) : ℍ[ℚ, a, b]) = m • (1 : ℍ[ℚ, a, b]) := by
    rw [zsmul_eq_mul, mul_one]; push_cast; rfl
  rw [e]; exact Λ.smul_mem m h1

theorem mapPt_one {E' : FakeEllipticCurve Λ N k} (φ : E.A ⟶ E'.A) (hφ : φ ≫ E'.f = E.f)
    (hmul : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of k)) (P Q : SchemeHomOver t E.f),
      mapPt φ hφ (E.L.mul t P Q) = E'.L.mul t (mapPt φ hφ P) (mapPt φ hφ Q))
    {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of k)) : mapPt φ hφ (E.L.one t) = E'.L.one t := by
  set x := mapPt φ hφ (E.L.one t) with hx
  have hxx : E'.L.mul t x x = x := by rw [hx, ← hmul, E.L.one_mul]
  letI := E'.L.pointGroup t
  have h2 : x * x = x * 1 := by rw [mul_one]; exact hxx
  exact mul_left_cancel h2

theorem nsmulPt_eq_pow {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of k)) (n : ℕ) (P : SchemeHomOver t E.f) :
    letI := E.L.pointGroup t
    nsmulPt E.L t n P = P ^ n := by
  letI := E.L.pointGroup t
  induction n with
  | zero => rw [pow_zero]; rfl
  | succ n ih =>
    rw [pow_succ, ← ih]
    rfl

theorem factorsThrough_nsmulPt {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of k)) (n : ℕ) (P : SchemeHomOver t E.f)
    (hP : FactorsThrough E.lev P) : FactorsThrough E.lev (nsmulPt E.L t n P) := by
  induction n with
  | zero => exact E.lev_one t
  | succ n ih => exact (E.lev_sub t _ _ ih hP).1

theorem pushPt_act_zero (h0 : (0 : ℍ[ℚ, a, b]) ∈ Λ) {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of k)) (P : SchemeHomOver t E.f) :
    pushPt (E.act ⟨0, h0⟩) (E.act_over _) P = E.L.one t := by
  letI := E.L.pointGroup t
  have h := E.act_add ⟨0, h0⟩ ⟨0, h0⟩ t P
  have e : (⟨0, h0⟩ : ↥Λ) + ⟨0, h0⟩ = ⟨0, h0⟩ := by apply Subtype.ext; simp
  rw [e] at h
  have h' : (pushPt (E.act ⟨0, h0⟩) (E.act_over _) P : SchemeHomOver t E.f) =
      pushPt (E.act ⟨0, h0⟩) (E.act_over _) P * pushPt (E.act ⟨0, h0⟩) (E.act_over _) P := h
  exact mul_eq_left.mp h'.symm

theorem pushPt_act_natCast (hΛℤ : ∀ m : ℤ, ((m : ℚ) : ℍ[ℚ, a, b]) ∈ Λ) (m : ℕ)
    {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of k)) (P : SchemeHomOver t E.f) :
    pushPt (E.act ⟨((m : ℤ) : ℚ), hΛℤ m⟩) (E.act_over _) P = nsmulPt E.L t m P := by
  induction m with
  | zero =>
    have e : (⟨(((0 : ℕ) : ℤ) : ℚ), hΛℤ 0⟩ : ↥Λ) = ⟨0, by simpa using hΛℤ 0⟩ := by apply Subtype.ext; simp
    rw [e, pushPt_act_zero]
    rfl
  | succ m ih =>
    have e : (⟨(((m + 1 : ℕ) : ℤ) : ℚ), hΛℤ (m + 1 : ℕ)⟩ : ↥Λ) =
        ⟨((m : ℤ) : ℚ), hΛℤ m⟩ + ⟨((1 : ℤ) : ℚ), hΛℤ 1⟩ := by
      apply Subtype.ext; push_cast; simp
    rw [e, E.act_add, ih]
    show E.L.mul t (nsmulPt E.L t m P) _ = E.L.mul t (nsmulPt E.L t m P) P
    congr 1
    have e1 : (⟨((1 : ℤ) : ℚ), hΛℤ 1⟩ : ↥Λ) = ⟨1, by simpa using hΛℤ 1⟩ := by apply Subtype.ext; simp
    rw [e1]
    apply Subtype.ext; rw [mapPt_coe, E.act_one]; exact Category.comp_id _

theorem mapPt_mapPt_eq_nsmulPt_of_comp_eq_act (hΛℤ : ∀ m : ℤ, ((m : ℚ) : ℍ[ℚ, a, b]) ∈ Λ)
    {A' : Scheme.{0}} {f' : A' ⟶ Spec (CommRingCat.of k)}
    (φ : E.A ⟶ A') (hφ : φ ≫ f' = E.f) (ψ : A' ⟶ E.A) (hψ : ψ ≫ E.f = f') (n : ℕ)
    (hmem : ((n : ℚ) : ℍ[ℚ, a, b]) ∈ Λ) (hcomp : φ ≫ ψ = E.act ⟨((n : ℚ) : ℍ[ℚ, a, b]), hmem⟩)
    {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of k)) (P : SchemeHomOver t E.f) :
    mapPt ψ hψ (mapPt φ hφ P) = nsmulPt E.L t n P := by
  have e : (⟨((n : ℚ) : ℍ[ℚ, a, b]), hmem⟩ : ↥Λ) = ⟨(((n : ℕ) : ℤ) : ℚ), hΛℤ n⟩ := by
    apply Subtype.ext; push_cast; rfl
  rw [← pushPt_act_natCast E hΛℤ n t P]
  apply Subtype.ext
  simp only [mapPt_coe, Category.assoc, hcomp, e]

theorem preservesLevel_symm_of_isIsogenyPair_of_coprime
    {N d : ℕ} {k₀ : Type} [Field k₀] (hdN : Nat.Coprime d N)
    {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} (hΛ : IsOrder Λ)
    (E E' : FakeEllipticCurve Λ N k₀)
    (φ : E.A ⟶ E'.A) (ψ : E'.A ⟶ E.A) (hφ : φ ≫ E'.f = E.f) (hψ : ψ ≫ E.f = E'.f)
    (hpair : FakeEllipticCurve.IsIsogenyPair d E E' φ ψ)
    (hlev : FakeEllipticCurve.PreservesLevel E E' φ hφ) :
    FakeEllipticCurve.PreservesLevel E' E ψ hψ := by
  classical
  obtain ⟨hφ', hψ', hφmul, hψmul, -, -, hdeg⟩ := hpair
  have hΛℤ : ∀ m : ℤ, ((m : ℚ) : ℍ[ℚ, a, b]) ∈ Λ := intCast_mem_of_one_mem hΛ.one_mem
  have hdΛ : ((d : ℚ) : ℍ[ℚ, a, b]) ∈ Λ := by
    have h := hΛℤ d
    rwa [Int.cast_natCast] at h
  obtain ⟨hφψ, hψφ⟩ := hdeg hdΛ
  have hψφ_pt : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of k₀)) (P : SchemeHomOver t E.f),
      mapPt ψ hψ (mapPt φ hφ P) = nsmulPt E.L t d P :=
    fun t P => mapPt_mapPt_eq_nsmulPt_of_comp_eq_act E hΛℤ φ hφ ψ hψ d hdΛ hφψ t P
  have hφψ_pt : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of k₀)) (Q : SchemeHomOver t E'.f),
      mapPt φ hφ (mapPt ψ hψ Q) = nsmulPt E'.L t d Q :=
    fun t Q => mapPt_mapPt_eq_nsmulPt_of_comp_eq_act E' hΛℤ ψ hψ φ hφ d hdΛ hψφ t Q
  intro T₁ t₁ Q₁ hQ₁
  by_cases hN1 : N = 1
  · subst hN1
    letI := E'.L.pointGroup t₁
    have hQ1 : Q₁ = E'.L.one t₁ := by
      have h := E'.lev_torsion t₁ Q₁ hQ₁
      rw [nsmulPt_eq_pow, pow_one] at h
      exact h
    rw [hQ1, mapPt_one E' ψ hψ hψmul]
    exact E.lev_one t₁
  have hd0 : 0 < d := Nat.pos_of_ne_zero (by rintro rfl; exact hN1 ((Nat.coprime_zero_left _).1 hdN))
  obtain ⟨hfinφ, -, -, -⟩ := CerednikDrinfeld.QM.FakeEllipticCurve.isFinite_flat_surjective_of_mapPt_mapPt_eq_nsmulPt
    E E' φ hφ hφmul ψ hψ d hd0 hψφ_pt hφψ_pt
  haveI := hfinφ
  haveI : IsClosedImmersion E.lev := E.lev_closed
  haveI : IsClosedImmersion E'.lev := E'.lev_closed
  let j : E.C ⟶ E'.A := E.lev ≫ φ
  haveI : IsFinite j := inferInstance
  haveI : Mono j := by
    refine ⟨fun {Z} g₁ g₂ hg => ?_⟩
    rw [← cancel_mono E.lev]
    let t : Z ⟶ Spec (CommRingCat.of k₀) := (g₁ ≫ E.lev) ≫ E.f
    have hg' : (g₁ ≫ E.lev) ≫ φ = (g₂ ≫ E.lev) ≫ φ := by simpa only [Category.assoc] using hg
    have hg₂ : (g₂ ≫ E.lev) ≫ E.f = t := by
      show (g₂ ≫ E.lev) ≫ E.f = (g₁ ≫ E.lev) ≫ E.f
      rw [← hφ, ← Category.assoc, ← hg', Category.assoc]
    let P : SchemeHomOver t E.f := ⟨g₁ ≫ E.lev, rfl⟩
    let Q : SchemeHomOver t E.f := ⟨g₂ ≫ E.lev, hg₂⟩
    have hPC : FactorsThrough E.lev P := ⟨g₁, rfl⟩
    have hQC : FactorsThrough E.lev Q := ⟨g₂, rfl⟩
    letI := E.L.pointGroup t
    letI := E'.L.pointGroup t
    let F : SchemeHomOver t E.f →* SchemeHomOver t E'.f :=
      { toFun := mapPt φ hφ, map_one' := mapPt_one E φ hφ hφmul t, map_mul' := fun X Y => hφmul t X Y }
    have hPQ : F P = F Q := Subtype.ext hg'
    have h1 : F (P * Q⁻¹) = 1 := by rw [map_mul, map_inv, hPQ, mul_inv_cancel]
    have hCPQ : FactorsThrough E.lev (P * Q⁻¹) := by
      have hQinv : FactorsThrough E.lev Q⁻¹ := (E.lev_sub t Q Q hQC hQC).2
      exact (E.lev_sub t P Q⁻¹ hPC hQinv).1
    have hXd : (P * Q⁻¹) ^ d = 1 := by
      rw [← nsmulPt_eq_pow, ← hψφ_pt t (P * Q⁻¹)]
      have h1' : mapPt φ hφ (P * Q⁻¹) = E'.L.one t := h1
      rw [h1', mapPt_one E' ψ hψ hψmul]
      rfl
    have hXN : (P * Q⁻¹) ^ N = 1 := by
      rw [← nsmulPt_eq_pow]
      exact E.lev_torsion t _ hCPQ
    have hone : P * Q⁻¹ = 1 := by
      have h : (P * Q⁻¹) ^ Nat.gcd d N = 1 := pow_gcd_eq_one.2 ⟨hXd, hXN⟩
      rwa [Nat.Coprime.gcd_eq_one hdN, pow_one] at h
    have hPQ' : P = Q := mul_inv_eq_one.1 hone
    exact congrArg Subtype.val hPQ'
  haveI : IsClosedImmersion j := (IsClosedImmersion.iff_isFinite_and_mono j).2 ⟨inferInstance, inferInstance⟩
  obtain ⟨c, hc⟩ : ∃ c : E.C ⟶ E'.C, c ≫ E'.lev = j := by
    have h := hlev (E.lev ≫ E.f) ⟨E.lev, rfl⟩ ⟨𝟙 _, Category.id_comp _⟩
    obtain ⟨c, hc⟩ := h
    exact ⟨c, hc⟩
  haveI : IsClosedImmersion (c ≫ E'.lev) := by rw [hc]; infer_instance
  haveI : IsClosedImmersion c := IsClosedImmersion.of_comp c E'.lev
  haveI : IsFinite (E'.lev ≫ E'.f) := E'.lev_finite
  haveI : Flat (E'.lev ≫ E'.f) := E'.lev_flat
  haveI : LocallyOfFinitePresentation (E'.lev ≫ E'.f) := E'.lev_finitePresentation
  haveI : Flat (E.lev ≫ E.f) := E.lev_flat
  haveI : LocallyOfFinitePresentation (E.lev ≫ E.f) := E.lev_finitePresentation
  have w : c ≫ (E'.lev ≫ E'.f) = E.lev ≫ E.f := by
    rw [← Category.assoc, hc]
    show (E.lev ≫ φ) ≫ E'.f = E.lev ≫ E.f
    rw [Category.assoc, hφ]
  haveI : IsIso c := AlgebraicGeometry.isIso_of_isClosedImmersion_of_finrank_comp_eq c (E'.lev ≫ E'.f) (E.lev ≫ E.f) w
    (fun s => by rw [E.lev_rank, E'.lev_rank])
  obtain ⟨Q₀, hQ₀⟩ := hQ₁
  have hPf : ((Q₀ ≫ inv c) ≫ E.lev) ≫ E.f = t₁ := by
    rw [Category.assoc, ← w, Category.assoc, IsIso.inv_hom_id_assoc, ← Category.assoc, hQ₀]
    exact Q₁.2
  let P₁ : SchemeHomOver t₁ E.f := ⟨(Q₀ ≫ inv c) ≫ E.lev, hPf⟩
  have hP₁ : FactorsThrough E.lev P₁ := ⟨Q₀ ≫ inv c, rfl⟩
  have hPQ : mapPt φ hφ P₁ = Q₁ := by
    apply Subtype.ext
    show ((Q₀ ≫ inv c) ≫ E.lev) ≫ φ = Q₁.1
    rw [Category.assoc, Category.assoc, show E.lev ≫ φ = c ≫ E'.lev from hc.symm, IsIso.inv_hom_id_assoc, hQ₀]
  rw [← hPQ, hψφ_pt]
  exact factorsThrough_nsmulPt E t₁ d P₁ hP₁

end G3Dual

end

section
open scoped Quaternion
open CategoryTheory AlgebraicGeometry CerednikDrinfeld CerednikDrinfeld.QM NeronModelInfra QuaternionAlgebra

namespace G3Aux

open CerednikDrinfeld.QM.FakeEllipticCurve in
theorem isIsogenyPair_swap {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} {N : ℕ} {S : Type} [CommRing S]
    {E E' : FakeEllipticCurve Λ N S} {d : ℕ} {φ : E.A ⟶ E'.A} {ψ : E'.A ⟶ E.A}
    (h : IsIsogenyPair d E E' φ ψ) : IsIsogenyPair d E' E ψ φ := by
  obtain ⟨hφ, hψ, hm, hm', ha, ha', hc⟩ := h
  exact ⟨hψ, hφ, hm', hm, ha', ha, fun hd => ⟨(hc hd).2, (hc hd).1⟩⟩

open CerednikDrinfeld.QM.FakeEllipticCurve in
theorem preservesLevel_comp {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} {N : ℕ} {S : Type} [CommRing S]
    {E E' E'' : FakeEllipticCurve Λ N S} {φ : E.A ⟶ E'.A} {ψ : E'.A ⟶ E''.A}
    (hφ : φ ≫ E'.f = E.f) (hψ : ψ ≫ E''.f = E'.f) (hφψ : (φ ≫ ψ) ≫ E''.f = E.f)
    (h₁ : PreservesLevel E E' φ hφ) (h₂ : PreservesLevel E' E'' ψ hψ) : PreservesLevel E E'' (φ ≫ ψ) hφψ := by
  intro T t P hP
  have e : mapPt (φ ≫ ψ) hφψ P = mapPt ψ hψ (mapPt φ hφ P) := Subtype.ext (by simp [mapPt])
  rw [e]
  exact h₂ t _ (h₁ t P hP)

open CerednikDrinfeld.QM.FakeEllipticCurve in
theorem preservesLevel_congr {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} {N : ℕ} {S : Type} [CommRing S]
    {E E' : FakeEllipticCurve Λ N S} {φ ψ : E.A ⟶ E'.A} {hφ : φ ≫ E'.f = E.f} {hψ : ψ ≫ E'.f = E.f}
    (e : φ = ψ) (h : PreservesLevel E E' φ hφ) : PreservesLevel E E' ψ hψ := by
  subst e
  exact h

open CerednikDrinfeld.QM.FakeEllipticCurve in

theorem exists_comparison_composite_pair
    {r : ℕ} [Fact r.Prime] {𝒪 : Type} [CommRing 𝒪] {π : 𝒪} {Onr : Type} [CommRing Onr] [Algebra 𝒪 Onr]
    {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} {N : ℕ} (hΛ : IsOrder Λ) (hΛℤ : ∀ m : ℤ, ((m : ℚ) : ℍ[ℚ, a, b]) ∈ Λ) (hrN : ¬ r ∣ N)
    {A₀ : FakeEllipticCurve Λ N (Onr ⧸ Ideal.span {algebraMap 𝒪 Onr π})}
    {k : Type} [Field k] [Algebra 𝒪 k] (hk : IsNilpotent (algebraMap 𝒪 k π))
    (hNk : IsUnit ((N : ℕ) : k ⧸ Ideal.span {algebraMap 𝒪 k π}))
    {ψ : Onr →ₐ[𝒪] k} {E E' : FakeEllipticCurve Λ N k}
    (i : E.A ≅ E'.A) (hi : i.hom ≫ E'.f = E.f) (hvia : IsoVia E E' i hi)
    (ϱ : Rigidification r π A₀ ψ E) (ϱ' : Rigidification r π A₀ ψ E') :
    ∃ (ib : ϱ.Eb.A ⟶ ϱ'.Eb.A) (_ : ib ≫ ϱ'.gb = ϱ.gb ≫ i.hom) (_ : ib ≫ ϱ'.Eb.f = ϱ.Eb.f)
      (_ : IsPullbackVia (RingHom.id _) ϱ'.Eb ϱ.Eb ib)
      (uA : ϱ'.Ab.A ⟶ ϱ.Ab.A) (_ : IsPullbackVia (RingHom.id _) ϱ.Ab ϱ'.Ab uA) (_ : uA ≫ ϱ.gA = ϱ'.gA)
      (Ψ : ϱ.Ab.A ⟶ ϱ.Ab.A) (hΦ : (ϱ.φ' ≫ ib ≫ ϱ'.φ ≫ uA) ≫ ϱ.Ab.f = ϱ.Ab.f),
      IsIsogenyPair (r ^ (ϱ.d + ϱ'.d)) ϱ.Ab ϱ.Ab (ϱ.φ' ≫ ib ≫ ϱ'.φ ≫ uA) Ψ ∧
      PreservesLevel ϱ.Ab ϱ.Ab (ϱ.φ' ≫ ib ≫ ϱ'.φ ≫ uA) hΦ := by
  classical

  have hπ0 : algebraMap 𝒪 k π = 0 := hk.eq_zero
  have hI : Ideal.span {algebraMap 𝒪 k π} = ⊥ := Ideal.span_singleton_eq_bot.mpr hπ0
  haveI hImax : (Ideal.span {algebraMap 𝒪 k π}).IsMaximal := by rw [hI]; exact Ideal.bot_isMaximal
  letI instF : Field (k ⧸ Ideal.span {algebraMap 𝒪 k π}) := Ideal.Quotient.field _

  have hpb' : IsPullbackVia (Ideal.Quotient.mk (Ideal.span {algebraMap 𝒪 k π})) E ϱ'.Eb (ϱ'.gb ≫ i.inv) :=
    isPullbackVia_comp_inv_of_isoVia _ i hi hvia ϱ'.gb ϱ'.isPullback_Eb
  obtain ⟨ib, hib1, hib2, hib3⟩ :=
    CerednikDrinfeld.QM.FakeEllipticCurve.exists_isPullbackVia_id_comp_eq_of_isPullbackVia_of_isPullbackVia_of_isUnit
      (Ideal.Quotient.mk (Ideal.span {algebraMap 𝒪 k π})) hNk E ϱ'.Eb (ϱ'.gb ≫ i.inv) hpb' ϱ.Eb ϱ.gb ϱ.isPullback_Eb
  obtain ⟨jb, hjb, hjbe, hjbpair, hjblev⟩ := exists_iso_of_isPullbackVia_id ib hib3
  subst hjbe

  obtain ⟨uA, huA1, huA2, huA3⟩ :=
    CerednikDrinfeld.QM.FakeEllipticCurve.exists_isPullbackVia_id_comp_eq_of_isPullbackVia_of_isPullbackVia_of_isUnit
      _ hNk A₀ ϱ.Ab ϱ.gA ϱ.isPullback_Ab ϱ'.Ab ϱ'.gA ϱ'.isPullback_Ab
  obtain ⟨jA, hjA, hjAe, hjApair, hjAlev⟩ := exists_iso_of_isPullbackVia_id uA huA3
  subst hjAe

  have p1 : IsIsogenyPair (r ^ ϱ.d) ϱ.Ab ϱ.Eb ϱ.φ' ϱ.φ := isIsogenyPair_swap ϱ.isIsogenyPair
  have p3 : IsIsogenyPair (r ^ ϱ'.d) ϱ'.Eb ϱ'.Ab ϱ'.φ ϱ'.φ' := ϱ'.isIsogenyPair
  have p12 := isIsogenyPair_trans hΛℤ p1 hjbpair
  have p123 := isIsogenyPair_trans hΛℤ p12 p3
  have p1234 := isIsogenyPair_trans hΛℤ p123 hjApair
  have hdeg : r ^ ϱ.d * 1 * r ^ ϱ'.d * 1 = r ^ (ϱ.d + ϱ'.d) := by ring
  rw [hdeg] at p1234
  simp only [Category.assoc] at p1234
  obtain ⟨hΦ, -, -⟩ := id p1234
  refine ⟨jb.hom, ?_, hib2, hib3, jA.hom, huA3, huA1, _, hΦ, p1234, ?_⟩
  · rw [← hib1, Category.assoc, Category.assoc, Iso.inv_hom_id, Category.comp_id]
  ·
    have hcop : Nat.Coprime (r ^ ϱ.d) N :=
      Nat.Coprime.pow_left _ (((Fact.out : r.Prime).coprime_iff_not_dvd).mpr hrN)
    obtain ⟨hφo, hφ'o, -⟩ := id ϱ.isIsogenyPair
    have lφ' : PreservesLevel ϱ.Ab ϱ.Eb ϱ.φ' hφ'o :=
      G3Dual.preservesLevel_symm_of_isIsogenyPair_of_coprime hcop hΛ ϱ.Eb ϱ.Ab ϱ.φ ϱ.φ' hφo hφ'o
        ϱ.isIsogenyPair (fun t P hP => ϱ.preservesLevel t P hP)
    obtain ⟨hφo', -, -⟩ := id ϱ'.isIsogenyPair
    have lφ : PreservesLevel ϱ'.Eb ϱ'.Ab ϱ'.φ hφo' := fun t P hP => ϱ'.preservesLevel t P hP
    have e12 : (ϱ.φ' ≫ jb.hom) ≫ ϱ'.Eb.f = ϱ.Ab.f := by rw [Category.assoc, hjb, hφ'o]
    have l12 : PreservesLevel ϱ.Ab ϱ'.Eb (ϱ.φ' ≫ jb.hom) e12 := preservesLevel_comp hφ'o hjb e12 lφ' hjblev
    have e123 : ((ϱ.φ' ≫ jb.hom) ≫ ϱ'.φ) ≫ ϱ'.Ab.f = ϱ.Ab.f := by rw [Category.assoc, hφo', e12]
    have l123 : PreservesLevel ϱ.Ab ϱ'.Ab ((ϱ.φ' ≫ jb.hom) ≫ ϱ'.φ) e123 := preservesLevel_comp e12 hφo' e123 l12 lφ
    have e1234 : (((ϱ.φ' ≫ jb.hom) ≫ ϱ'.φ) ≫ jA.hom) ≫ ϱ.Ab.f = ϱ.Ab.f := by rw [Category.assoc, hjA, e123]
    have l1234 : PreservesLevel ϱ.Ab ϱ.Ab (((ϱ.φ' ≫ jb.hom) ≫ ϱ'.φ) ≫ jA.hom) e1234 :=
      preservesLevel_comp e123 hjA e1234 l123 hjAlev
    intro T t P hP
    exact (preservesLevel_congr (hψ := hΦ) (by simp only [Category.assoc]) l1234) t P hP

end G3Aux

end

section
open scoped Quaternion
open CategoryTheory AlgebraicGeometry CerednikDrinfeld CerednikDrinfeld.QM NeronModelInfra QuaternionAlgebra

namespace G3Aux

open CerednikDrinfeld.QM.FakeEllipticCurve in

theorem act_rpow_comp {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} {N : ℕ} {S : Type} [CommRing S]
    (hΛℤ : ∀ m : ℤ, ((m : ℚ) : ℍ[ℚ, a, b]) ∈ Λ) (E : FakeEllipticCurve Λ N S) (r m n : ℕ) :
    E.act ⟨(((r ^ m : ℕ) : ℤ) : ℚ), hΛℤ _⟩ ≫ E.act ⟨(((r ^ n : ℕ) : ℤ) : ℚ), hΛℤ _⟩ =
      E.act ⟨(((r ^ (m + n) : ℕ) : ℤ) : ℚ), hΛℤ _⟩ := by
  have e : ((((r ^ n : ℕ) : ℤ) : ℚ) : ℍ[ℚ, a, b]) * ((((r ^ m : ℕ) : ℤ) : ℚ) : ℍ[ℚ, a, b]) =
      ((((r ^ (m + n) : ℕ) : ℤ) : ℚ) : ℍ[ℚ, a, b]) := by
    rw [← QuaternionAlgebra.coe_mul]; congr 1; push_cast; ring
  have hmem : ((((r ^ n : ℕ) : ℤ) : ℚ) : ℍ[ℚ, a, b]) * ((((r ^ m : ℕ) : ℤ) : ℚ) : ℍ[ℚ, a, b]) ∈ Λ := e ▸ hΛℤ _
  rw [← E.act_mul ⟨(((r ^ n : ℕ) : ℤ) : ℚ), hΛℤ _⟩ ⟨(((r ^ m : ℕ) : ℤ) : ℚ), hΛℤ _⟩ hmem]
  congr 1
  exact Subtype.ext e

open CerednikDrinfeld.QM.FakeEllipticCurve in

theorem exists_corr_of_conj_of_isTranslateBy
    {r : ℕ} {𝒪 : Type} [CommRing 𝒪] {π : 𝒪} {Onr : Type} [CommRing Onr] [Algebra 𝒪 Onr]
    {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} {N : ℕ} (hΛℤ : ∀ m : ℤ, ((m : ℚ) : ℍ[ℚ, a, b]) ∈ Λ)
    {A₀ : FakeEllipticCurve Λ N (Onr ⧸ Ideal.span {algebraMap 𝒪 Onr π})}
    {B : Type} [CommRing B] [Algebra 𝒪 B] {ψ : Onr →ₐ[𝒪] B}
    (hNB : IsUnit ((N : ℕ) : B ⧸ Ideal.span {algebraMap 𝒪 B π}))
    {E E' : FakeEllipticCurve Λ N B} (i : E.A ≅ E'.A)
    (ϱ : Rigidification r π A₀ ψ E) (ϱ' : Rigidification r π A₀ ψ E') (ρ₂ : Rigidification r π A₀ ψ E)
    (ib : ϱ.Eb.A ⟶ ϱ'.Eb.A) (hib : ib ≫ ϱ'.gb = ϱ.gb ≫ i.hom) (hibf : ib ≫ ϱ'.Eb.f = ϱ.Eb.f)
    (hibv : IsPullbackVia (RingHom.id _) ϱ'.Eb ϱ.Eb ib)
    (uA : ϱ'.Ab.A ⟶ ϱ.Ab.A) (huA : IsPullbackVia (RingHom.id _) ϱ.Ab ϱ'.Ab uA) (huAg : uA ≫ ϱ.gA = ϱ'.gA)
    (eγ : A₀.A ⟶ A₀.A) (i₀ j₀ : ℕ)
    (hconj : (ϱ.φ' ≫ ib ≫ ϱ'.φ ≫ uA) ≫ ϱ.Ab.act ⟨(((r ^ i₀ : ℕ) : ℤ) : ℚ), hΛℤ _⟩ ≫ ϱ.gA =
      ϱ.gA ≫ eγ ≫ A₀.act ⟨(((r ^ j₀ : ℕ) : ℤ) : ℚ), hΛℤ _⟩)
    (htr : Rigidification.IsTranslateBy hΛℤ eγ ϱ ρ₂) :
    ∃ (ib' : ρ₂.Eb.A ⟶ ϱ'.Eb.A) (_ : ib' ≫ ϱ'.gb = ρ₂.gb ≫ i.hom) (_ : ib' ≫ ϱ'.Eb.f = ρ₂.Eb.f)
      (uA' : ϱ'.Ab.A ⟶ ρ₂.Ab.A) (_ : IsPullbackVia (RingHom.id _) ρ₂.Ab ϱ'.Ab uA') (_ : uA' ≫ ρ₂.gA = ϱ'.gA)
      (i₁ j₁ : ℕ),
      ib' ≫ ϱ'.φ ≫ uA' ≫ ρ₂.Ab.act ⟨(((r ^ i₁ : ℕ) : ℤ) : ℚ), hΛℤ _⟩ = ρ₂.φ ≫ ρ₂.Ab.act ⟨(((r ^ j₁ : ℕ) : ℤ) : ℚ), hΛℤ _⟩ := by
  have hid : Spec.map (CommRingCat.ofHom (RingHom.id (B ⧸ Ideal.span {algebraMap 𝒪 B π}))) = 𝟙 _ := by
    rw [CommRingCat.ofHom_id, Spec.map_id]
  obtain ⟨u, uA₂, ⟨hu_pb, hu_g, huA₂_pb, huA₂_g⟩, eγb, heγb, heγbf, i₂, j₂, htr⟩ := htr

  obtain ⟨uA', huA'g, huA'f, huA'v⟩ :=
    CerednikDrinfeld.QM.FakeEllipticCurve.exists_isPullbackVia_id_comp_eq_of_isPullbackVia_of_isPullbackVia_of_isUnit
      _ hNB A₀ ρ₂.Ab ρ₂.gA ρ₂.isPullback_Ab ϱ'.Ab ϱ'.gA ϱ'.isPullback_Ab
  obtain ⟨hpbA, -, hactA, -⟩ := id ϱ.isPullback_Ab
  obtain ⟨huA₂w, -, huA₂act, -⟩ := id huA₂_pb
  obtain ⟨huAw, -, huAact, -⟩ := id huA
  obtain ⟨hibw, -, hibact, -⟩ := id hibv
  obtain ⟨huw, -, -, -⟩ := id hu_pb
  have huniq : uA' ≫ uA₂ = uA := by
    apply hpbA.hom_ext
    · rw [Category.assoc, huA₂_g, huA'g, huAg]
    · rw [Category.assoc]
      have h1 := huA₂w.w; have h2 := huAw.w; have h3 := huA'v.1.w
      simp only [hid, Category.comp_id] at h1 h2 h3
      rw [h1, h3, h2]

  obtain ⟨jA₂, -, hjA₂e, -, -⟩ := exists_iso_of_isPullbackVia_id uA₂ huA₂_pb

  obtain ⟨hφo, hφ'o, -, -, hφact, hφ'act, hcomp⟩ := id ϱ.isIsogenyPair
  obtain ⟨hφo', -, -, -, hφact', -, -⟩ := id ϱ'.isIsogenyPair
  have hA : (ϱ.φ' ≫ ib ≫ ϱ'.φ ≫ uA) ≫ ϱ.Ab.act ⟨(((r ^ i₀ : ℕ) : ℤ) : ℚ), hΛℤ _⟩ =
      eγb ≫ ϱ.Ab.act ⟨(((r ^ j₀ : ℕ) : ℤ) : ℚ), hΛℤ _⟩ := by
    apply hpbA.hom_ext
    · rw [Category.assoc, hconj, Category.assoc, hactA, ← Category.assoc eγb, heγb, Category.assoc]
    · have h2 := huAw.w; have h3 := hibw.w
      simp only [hid, Category.comp_id] at h2 h3
      simp only [Category.assoc, ϱ.Ab.act_over, heγbf, h2, hφo', h3, hφ'o]

  have hd : (((r ^ ϱ.d : ℕ) : ℚ) : ℍ[ℚ, a, b]) ∈ Λ := by simpa using hΛℤ (r ^ ϱ.d)
  have hdd : ϱ.φ ≫ ϱ.φ' = ϱ.Eb.act ⟨(((r ^ ϱ.d : ℕ) : ℤ) : ℚ), hΛℤ _⟩ := by
    have := (hcomp hd).1
    rw [this]
    congr 1
  have hB : ib ≫ ϱ'.φ ≫ uA ≫ ϱ.Ab.act ⟨(((r ^ ϱ.d : ℕ) : ℤ) : ℚ), hΛℤ _⟩ ≫ ϱ.Ab.act ⟨(((r ^ i₀ : ℕ) : ℤ) : ℚ), hΛℤ _⟩ =
      ϱ.φ ≫ eγb ≫ ϱ.Ab.act ⟨(((r ^ j₀ : ℕ) : ℤ) : ℚ), hΛℤ _⟩ := by
    have h0 := congrArg (fun x => ϱ.φ ≫ x) hA
    simp only [Category.assoc] at h0
    rw [← h0, ← Category.assoc ϱ.φ ϱ.φ', hdd]
    rw [← Category.assoc (ϱ.Eb.act _) ib, hibact, Category.assoc, ← Category.assoc (ϱ'.Eb.act _) ϱ'.φ, hφact',
      Category.assoc, ← Category.assoc (ϱ'.Ab.act _) uA, huAact, Category.assoc]

  have hC : u ≫ ib ≫ ϱ'.φ ≫ uA ≫ ϱ.Ab.act ⟨(((r ^ (ϱ.d + i₀ + i₂) : ℕ) : ℤ) : ℚ), hΛℤ _⟩ =
      ρ₂.φ ≫ uA₂ ≫ ϱ.Ab.act ⟨(((r ^ (j₂ + j₀) : ℕ) : ℤ) : ℚ), hΛℤ _⟩ := by
    rw [← act_rpow_comp hΛℤ ϱ.Ab r (ϱ.d + i₀) i₂, ← act_rpow_comp hΛℤ ϱ.Ab r ϱ.d i₀, ← act_rpow_comp hΛℤ ϱ.Ab r j₂ j₀]
    simp only [Category.assoc]
    have h1 := congrArg (fun x => u ≫ x ≫ ϱ.Ab.act ⟨(((r ^ i₂ : ℕ) : ℤ) : ℚ), hΛℤ _⟩) hB
    simp only [Category.assoc] at h1
    have e2 : ϱ.Ab.act ⟨(((r ^ j₀ : ℕ) : ℤ) : ℚ), hΛℤ _⟩ ≫ ϱ.Ab.act ⟨(((r ^ i₂ : ℕ) : ℤ) : ℚ), hΛℤ _⟩ =
        ϱ.Ab.act ⟨(((r ^ i₂ : ℕ) : ℤ) : ℚ), hΛℤ _⟩ ≫ ϱ.Ab.act ⟨(((r ^ j₀ : ℕ) : ℤ) : ℚ), hΛℤ _⟩ := by
      rw [act_rpow_comp, act_rpow_comp, Nat.add_comm]
    have htr' := congrArg (fun x => x ≫ ϱ.Ab.act ⟨(((r ^ j₀ : ℕ) : ℤ) : ℚ), hΛℤ _⟩) htr
    simp only [Category.assoc] at htr'
    rw [h1, e2, htr']

  haveI : IsIso uA₂ := by rw [← hjA₂e]; infer_instance
  refine ⟨u ≫ ib, ?_, ?_, uA', huA'v, huA'g, ϱ.d + i₀ + i₂, j₂ + j₀, ?_⟩
  · rw [Category.assoc, hib, ← Category.assoc, hu_g]
  · rw [Category.assoc, hibf]
    have h := huw.w; simp only [hid, Category.comp_id] at h; exact h
  · rw [← cancel_mono uA₂]
    simp only [Category.assoc]
    rw [huA₂act, huA₂act, ← Category.assoc uA' uA₂, huniq]
    exact hC

end G3Aux

end

section
open scoped Quaternion
open CategoryTheory AlgebraicGeometry CerednikDrinfeld CerednikDrinfeld.QM NeronModelInfra QuaternionAlgebra

namespace G3Aux

open CerednikDrinfeld.QM.FakeEllipticCurve in

theorem exists_e_mul_comp_act_eq
    {r : ℕ} {𝒪 : Type} [CommRing 𝒪] {π : 𝒪} {Onr : Type} [CommRing Onr] [Algebra 𝒪 Onr]
    {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} {N : ℕ} (hΛℤ : ∀ m : ℤ, ((m : ℚ) : ℍ[ℚ, a, b]) ∈ Λ)
    {A₀ : FakeEllipticCurve Λ N (Onr ⧸ Ideal.span {algebraMap 𝒪 Onr π})}
    {a₁ b₁ : ℚ} {Γt : Subgroup (ℍ[ℚ, a₁, b₁])ˣ} (e : ↥Γt → (A₀.A ⟶ A₀.A))
    (hcomm : ∀ (γ : ↥Γt) (x : ↥Λ), A₀.act x ≫ e γ = e γ ≫ A₀.act x)
    (hE1mul : ∀ γ γ' : ↥Γt, ∃ i j : ℕ,
      e (γ * γ') ≫ A₀.act ⟨(((r ^ i : ℕ) : ℤ) : ℚ), hΛℤ _⟩ = e γ' ≫ e γ ≫ A₀.act ⟨(((r ^ j : ℕ) : ℤ) : ℚ), hΛℤ _⟩)
    (ζ γ : ↥Γt) (p q : ℕ)
    (hζ : e ζ ≫ A₀.act ⟨(((r ^ p : ℕ) : ℤ) : ℚ), hΛℤ _⟩ = A₀.act ⟨(((r ^ q : ℕ) : ℤ) : ℚ), hΛℤ _⟩) :
    ∃ a' b' : ℕ, e (ζ * γ) ≫ A₀.act ⟨(((r ^ a' : ℕ) : ℤ) : ℚ), hΛℤ _⟩ = e γ ≫ A₀.act ⟨(((r ^ b' : ℕ) : ℤ) : ℚ), hΛℤ _⟩ := by
  obtain ⟨i, j, hij⟩ := hE1mul ζ γ
  refine ⟨i + p, q + j, ?_⟩
  rw [← act_rpow_comp hΛℤ A₀ r i p, ← Category.assoc, hij, Category.assoc, Category.assoc, act_rpow_comp,
    Nat.add_comm j p, ← act_rpow_comp hΛℤ A₀ r p j, ← Category.assoc (e ζ), hζ, act_rpow_comp]

open CerednikDrinfeld.QM.FakeEllipticCurve in

theorem exists_e_zpow_comp_act_eq
    {r : ℕ} {𝒪 : Type} [CommRing 𝒪] {π : 𝒪} {Onr : Type} [CommRing Onr] [Algebra 𝒪 Onr]
    {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} {N : ℕ} (hΛℤ : ∀ m : ℤ, ((m : ℚ) : ℍ[ℚ, a, b]) ∈ Λ)
    {A₀ : FakeEllipticCurve Λ N (Onr ⧸ Ideal.span {algebraMap 𝒪 Onr π})}
    {a₁ b₁ : ℚ} {Γt : Subgroup (ℍ[ℚ, a₁, b₁])ˣ} (e : ↥Γt → (A₀.A ⟶ A₀.A))
    (hcomm : ∀ (γ : ↥Γt) (x : ↥Λ), A₀.act x ≫ e γ = e γ ≫ A₀.act x)
    (hE1mul : ∀ γ γ' : ↥Γt, ∃ i j : ℕ,
      e (γ * γ') ≫ A₀.act ⟨(((r ^ i : ℕ) : ℤ) : ℚ), hΛℤ _⟩ = e γ' ≫ e γ ≫ A₀.act ⟨(((r ^ j : ℕ) : ℤ) : ℚ), hΛℤ _⟩)
    (hE1sc : ∀ (γ : ↥Γt) (c : ℤ), ((γ : (ℍ[ℚ, a₁, b₁])ˣ) : ℍ[ℚ, a₁, b₁]) = (c : ℚ) • (1 : ℍ[ℚ, a₁, b₁]) →
      ∃ i : ℕ, e γ ≫ A₀.act ⟨(((r ^ i : ℕ) : ℤ) : ℚ), hΛℤ _⟩ = A₀.act ⟨((c * ((r ^ i : ℕ) : ℤ) : ℤ) : ℚ), hΛℤ _⟩)
    (z : (ℍ[ℚ, a₁, b₁])ˣ) (hzΓ : z ∈ Γt) (hzval : (z : ℍ[ℚ, a₁, b₁]) = (r : ℍ[ℚ, a₁, b₁])) (c : ℤ) :
    ∃ p q : ℕ, e ⟨z ^ c, Γt.zpow_mem hzΓ c⟩ ≫ A₀.act ⟨(((r ^ p : ℕ) : ℤ) : ℚ), hΛℤ _⟩ =
      A₀.act ⟨(((r ^ q : ℕ) : ℤ) : ℚ), hΛℤ _⟩ := by

  have hnat : ∀ m : ℕ, ∃ p q : ℕ, e ⟨z ^ (m : ℤ), Γt.zpow_mem hzΓ m⟩ ≫ A₀.act ⟨(((r ^ p : ℕ) : ℤ) : ℚ), hΛℤ _⟩ =
      A₀.act ⟨(((r ^ q : ℕ) : ℤ) : ℚ), hΛℤ _⟩ := by
    intro m
    have hv : (((⟨z ^ (m : ℤ), Γt.zpow_mem hzΓ m⟩ : ↥Γt) : (ℍ[ℚ, a₁, b₁])ˣ) : ℍ[ℚ, a₁, b₁]) =
        (((r ^ m : ℕ) : ℤ) : ℚ) • (1 : ℍ[ℚ, a₁, b₁]) := by
      simp only [zpow_natCast, Units.val_pow_eq_pow_val, hzval]
      rw [← Algebra.algebraMap_eq_smul_one]; push_cast; simp
    obtain ⟨i, hi⟩ := hE1sc _ _ hv
    refine ⟨i, m + i, ?_⟩
    rw [hi]; congr 1; apply Subtype.ext; push_cast; rw [← pow_add]
  obtain ⟨m, rfl | rfl⟩ := Int.eq_nat_or_neg c
  · exact hnat m
  ·
    obtain ⟨p, q, hpq⟩ := hnat m
    obtain ⟨i, j, hij⟩ := hE1mul ⟨z ^ (-(m : ℤ)), Γt.zpow_mem hzΓ _⟩ ⟨z ^ (m : ℤ), Γt.zpow_mem hzΓ m⟩
    have h1 : (⟨z ^ (-(m : ℤ)), Γt.zpow_mem hzΓ _⟩ : ↥Γt) * ⟨z ^ (m : ℤ), Γt.zpow_mem hzΓ m⟩ =
        ⟨z ^ ((0 : ℕ) : ℤ), Γt.zpow_mem hzΓ (0 : ℕ)⟩ := by
      apply Subtype.ext; simp [← zpow_add]
    rw [h1] at hij
    obtain ⟨p₀, q₀, h0⟩ := hnat 0

    have h2 : e ⟨z ^ (m : ℤ), Γt.zpow_mem hzΓ m⟩ ≫ e ⟨z ^ (-(m : ℤ)), Γt.zpow_mem hzΓ _⟩ ≫
        A₀.act ⟨(((r ^ (j + p₀) : ℕ) : ℤ) : ℚ), hΛℤ _⟩ = A₀.act ⟨(((r ^ (q₀ + i) : ℕ) : ℤ) : ℚ), hΛℤ _⟩ := by
      have hij' := congrArg (fun x => x ≫ A₀.act ⟨(((r ^ p₀ : ℕ) : ℤ) : ℚ), hΛℤ _⟩) hij
      simp only [Category.assoc] at hij'
      rw [← act_rpow_comp hΛℤ A₀ r j p₀, ← hij', act_rpow_comp, Nat.add_comm i p₀, ← act_rpow_comp hΛℤ A₀ r p₀ i,
        ← Category.assoc, h0, act_rpow_comp]
    have h3 := congrArg (fun x => x ≫ A₀.act ⟨(((r ^ p : ℕ) : ℤ) : ℚ), hΛℤ _⟩) h2
    simp only [Category.assoc, act_rpow_comp] at h3

    refine ⟨q + (j + p₀ + p), (q₀ + i + p) + p, ?_⟩
    have h3' := congrArg (fun x => x ≫ A₀.act ⟨(((r ^ p : ℕ) : ℤ) : ℚ), hΛℤ _⟩) h3
    simp only [Category.assoc, act_rpow_comp] at h3'

    calc e ⟨z ^ (-(m : ℤ)), Γt.zpow_mem hzΓ _⟩ ≫ A₀.act ⟨(((r ^ (q + (j + p₀ + p)) : ℕ) : ℤ) : ℚ), hΛℤ _⟩
        = e ⟨z ^ (-(m : ℤ)), Γt.zpow_mem hzΓ _⟩ ≫ A₀.act ⟨(((r ^ q : ℕ) : ℤ) : ℚ), hΛℤ _⟩ ≫
            A₀.act ⟨(((r ^ (j + p₀ + p) : ℕ) : ℤ) : ℚ), hΛℤ _⟩ := by rw [act_rpow_comp]
      _ = A₀.act ⟨(((r ^ q : ℕ) : ℤ) : ℚ), hΛℤ _⟩ ≫ e ⟨z ^ (-(m : ℤ)), Γt.zpow_mem hzΓ _⟩ ≫
            A₀.act ⟨(((r ^ (j + p₀ + p) : ℕ) : ℤ) : ℚ), hΛℤ _⟩ := by rw [← Category.assoc, ← hcomm, Category.assoc]
      _ = e ⟨z ^ (m : ℤ), Γt.zpow_mem hzΓ m⟩ ≫ A₀.act ⟨(((r ^ p : ℕ) : ℤ) : ℚ), hΛℤ _⟩ ≫
            e ⟨z ^ (-(m : ℤ)), Γt.zpow_mem hzΓ _⟩ ≫ A₀.act ⟨(((r ^ (j + p₀ + p) : ℕ) : ℤ) : ℚ), hΛℤ _⟩ := by
          rw [← hpq, Category.assoc]
      _ = e ⟨z ^ (m : ℤ), Γt.zpow_mem hzΓ m⟩ ≫ e ⟨z ^ (-(m : ℤ)), Γt.zpow_mem hzΓ _⟩ ≫
            A₀.act ⟨(((r ^ p : ℕ) : ℤ) : ℚ), hΛℤ _⟩ ≫ A₀.act ⟨(((r ^ (j + p₀ + p) : ℕ) : ℤ) : ℚ), hΛℤ _⟩ := by
          rw [← Category.assoc (A₀.act _) (e _), hcomm, Category.assoc]
      _ = A₀.act ⟨(((r ^ (q₀ + i + p + p) : ℕ) : ℤ) : ℚ), hΛℤ _⟩ := by
          rw [act_rpow_comp, Nat.add_comm p (j + p₀ + p), h3']

open CerednikDrinfeld.QM.FakeEllipticCurve in

theorem isTranslateBy_of_comp_act_eq
    {r : ℕ} {𝒪 : Type} [CommRing 𝒪] {π : 𝒪} {Onr : Type} [CommRing Onr] [Algebra 𝒪 Onr]
    {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} {N : ℕ} (hΛℤ : ∀ m : ℤ, ((m : ℚ) : ℍ[ℚ, a, b]) ∈ Λ)
    {A₀ : FakeEllipticCurve Λ N (Onr ⧸ Ideal.span {algebraMap 𝒪 Onr π})}
    {B : Type} [CommRing B] [Algebra 𝒪 B] {ψ : Onr →ₐ[𝒪] B} {E : FakeEllipticCurve Λ N B}
    (ϱ ρ₂ : Rigidification r π A₀ ψ E) (f f' : A₀.A ⟶ A₀.A) (hf' : f' ≫ A₀.f = A₀.f) (a' b' : ℕ)
    (hff' : f' ≫ A₀.act ⟨(((r ^ a' : ℕ) : ℤ) : ℚ), hΛℤ _⟩ = f ≫ A₀.act ⟨(((r ^ b' : ℕ) : ℤ) : ℚ), hΛℤ _⟩)
    (h : Rigidification.IsTranslateBy hΛℤ f ϱ ρ₂) : Rigidification.IsTranslateBy hΛℤ f' ϱ ρ₂ := by
  obtain ⟨u, uA₂, hcmp, fb, hfb, hfbf, i, j, rel⟩ := h
  obtain ⟨hpbA, -, hactA, -⟩ := id ϱ.isPullback_Ab
  have w : (ϱ.gA ≫ f') ≫ A₀.f = ϱ.Ab.f ≫ Spec.map (CommRingCat.ofHom
      (Ideal.quotientMap (Ideal.span {algebraMap 𝒪 B π}) (ψ : Onr →+* B)
        (Ideal.span_le.mpr (Set.singleton_subset_iff.mpr (Ideal.mem_comap.mpr
          (by rw [show (ψ : Onr →+* B) (algebraMap 𝒪 Onr π) = algebraMap 𝒪 B π from ψ.commutes π]
              exact Ideal.subset_span rfl)))))) := by
    rw [Category.assoc, hf']; exact hpbA.w
  let f'b : ϱ.Ab.A ⟶ ϱ.Ab.A := hpbA.lift (ϱ.gA ≫ f') ϱ.Ab.f w
  have hf'b : f'b ≫ ϱ.gA = ϱ.gA ≫ f' := hpbA.lift_fst _ _ w
  have hf'bf : f'b ≫ ϱ.Ab.f = ϱ.Ab.f := hpbA.lift_snd _ _ w
  have key : f'b ≫ ϱ.Ab.act ⟨(((r ^ a' : ℕ) : ℤ) : ℚ), hΛℤ _⟩ = fb ≫ ϱ.Ab.act ⟨(((r ^ b' : ℕ) : ℤ) : ℚ), hΛℤ _⟩ := by
    apply hpbA.hom_ext
    · rw [Category.assoc, hactA, ← Category.assoc, hf'b, Category.assoc, hff', Category.assoc, hactA, ← Category.assoc fb ϱ.gA,
        hfb, Category.assoc]
    · simp only [Category.assoc, ϱ.Ab.act_over, hf'bf, hfbf]
  refine ⟨u, uA₂, hcmp, f'b, hf'b, hf'bf, a' + i, j + b', ?_⟩
  rw [← act_rpow_comp hΛℤ ϱ.Ab r a' i, ← Category.assoc f'b, key, Category.assoc, act_rpow_comp, Nat.add_comm b' i,
    ← act_rpow_comp hΛℤ ϱ.Ab r i b', ← act_rpow_comp hΛℤ ϱ.Ab r j b']
  have rel' := congrArg (fun x => x ≫ ϱ.Ab.act ⟨(((r ^ b' : ℕ) : ℤ) : ℚ), hΛℤ _⟩) rel
  simpa only [Category.assoc] using rel'

end G3Aux

end

section
open scoped TensorProduct Quaternion NumberField
open CategoryTheory AlgebraicGeometry QuaternionAlgebra IsDedekindDomain CerednikDrinfeld CerednikDrinfeld.QM CerednikDrinfeld.FormalOmega CerednikDrinfeld.SpecialFormal NeronModelInfra GoodReductionJacobian

theorem solution

    {r rbar N : ℕ} [Fact r.Prime] [Fact rbar.Prime] [NeZero N] (hrr : rbar ≠ r) (hrN : ¬ r ∣ N) (hrbarN : ¬ rbar ∣ N) (hN : Squarefree N)

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
    (vdet : Matrix.GeneralLinearGroup (Fin 2) K₀ →* Multiplicative ℤ)
    (hvdet : ∀ (g : Matrix.GeneralLinearGroup (Fin 2) K₀) (n : ℤ), vdet g = Multiplicative.ofAdd n ↔
      ∃ u : 𝒪ˣ, (Matrix.GeneralLinearGroup.det g : K₀) = algebraMap 𝒪 K₀ (u : 𝒪) * (algebraMap 𝒪 K₀ π) ^ n)

    {a b : ℚ} (hB : IsIndefiniteRamifiedExactlyAt a b r rbar)
    (Λ : Submodule ℤ ℍ[ℚ, a, b]) (hΛ : IsMaximalOrder Λ)
    (𝒳 : Scheme.{0}) (f : 𝒳 ⟶ Spec (CommRingCat.of 𝒪))
    (pt : ∀ (S : Type) [CommRing S] (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of 𝒪)), FakeEllipticCurve Λ N S → SchemeHomOver s f)
    (h𝒳 : IsCoarseModuli Λ N 𝒳 f pt)

    (n : ℕ) (hn : 3 ≤ n) (hrn : ¬ r ∣ n) (hrbarn : ¬ rbar ∣ n) (hnN : Nat.Coprime n N)
    (M : Scheme.{0}) (fM : M ⟶ Spec (CommRingCat.of 𝒪))
    (ptF : ∀ (S : Type) [CommRing S] (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of 𝒪)),
      FakeEllipticCurve.WithFullLevel Λ N n S → SchemeHomOver s fM)
    (hM : IsFineModuli Λ N n M fM ptF)
    (G : Type) [Group G] (ρ : G →* Aut M) (χ : G → ↥Λ) (hρ : IsLevelTwistAction Λ N n M fM ptF G ρ χ)

    (p : M ⟶ 𝒳) (hp : p ≫ f = fM) (hρp : ∀ h : G, (ρ h).hom ≫ p = p)
    (hp_pt : ∀ (S : Type) [CommRing S] (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of 𝒪)) (u : FakeEllipticCurve.WithFullLevel Λ N n S),
      (ptF S s u).1 ≫ p = (pt S s u.1).1)
    (𝒴 : HeckeTower.AwayPrime r rbar → Scheme.{0}) (g : ∀ ℓ : HeckeTower.AwayPrime r rbar, 𝒴 ℓ ⟶ Spec (CommRingCat.of 𝒪))
    (ptT : ∀ (ℓ : HeckeTower.AwayPrime r rbar) (S : Type) [CommRing S] (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of 𝒪)),
      FakeEllipticCurve.WithExtraLevel Λ N (ℓ.1 : ℕ) S → SchemeHomOver s (g ℓ))
    (h𝒴 : ∀ ℓ : HeckeTower.AwayPrime r rbar, IsCoarseModuliT Λ N (ℓ.1 : ℕ) (𝒴 ℓ) (g ℓ) (ptT ℓ))
    (d₀ d₁ : ∀ ℓ : HeckeTower.AwayPrime r rbar, 𝒴 ℓ ⟶ 𝒳) (hd₀f : ∀ ℓ, d₀ ℓ ≫ f = g ℓ) (hd₁f : ∀ ℓ, d₁ ℓ ≫ f = g ℓ)
    (hd₀ : ∀ (ℓ : HeckeTower.AwayPrime r rbar) (S : Type) [CommRing S] (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of 𝒪))
      (u : FakeEllipticCurve.WithExtraLevel Λ N (ℓ.1 : ℕ) S), (ptT ℓ S s u).1 ≫ d₀ ℓ = (pt S s u.1).1)
    (hd₁ : ∀ (ℓ : HeckeTower.AwayPrime r rbar) (S : Type) [CommRing S] (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of 𝒪))
      (u : FakeEllipticCurve.WithExtraLevel Λ N (ℓ.1 : ℕ) S) (d : FakeEllipticCurve Λ N S),
      FakeEllipticCurve.IsLevelIsogeny (ℓ.1 : ℕ) u d → (ptT ℓ S s u).1 ≫ d₁ ℓ = (pt S s d).1)

    (ar arbar : 𝒳 ⟶ 𝒳) (harf : ar ≫ f = f) (harbarf : arbar ≫ f = f)
    (har : ∀ (S : Type) [CommRing S] (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of 𝒪)) (E E' : FakeEllipticCurve Λ N S),
      FakeEllipticCurve.IsAtkinLehnerQuotient r E E' → (pt S s E).1 ≫ ar = (pt S s E').1)
    (harbar : ∀ (S : Type) [CommRing S] (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of 𝒪)) (E E' : FakeEllipticCurve Λ N S),
      FakeEllipticCurve.IsAtkinLehnerQuotient rbar E E' → (pt S s E).1 ≫ arbar = (pt S s E').1)

    {a₁ b₁ : ℚ} (hdef : IsDefiniteRamifiedExactlyAt (a := a₁) (b := b₁) rbar)
    (Λ₁ R₁ : Submodule ℤ ℍ[ℚ, a₁, b₁]) (hΛ₁ : IsMaximalOrder Λ₁) (hR₁ : IsEichlerOrder R₁ N) (hRΛ₁ : R₁ ≤ Λ₁)
    (n₁ : (ℍ[ℚ, a₁, b₁] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) (hn₁ : n₁ ∈ primeHeckeSet R₁ r)
    (hS₁ : IsEichlerOrder (meetOrder R₁ n₁) (N * r))
    (ι₀ : ℍ[ℚ, a₁, b₁] →ₐ[ℚ] Matrix (Fin 2) (Fin 2) K₀) (hι₀ : Function.Injective ι₀)
    (v : HeightOneSpectrum (𝓞 ℚ)) (hv : ((r : ℕ) : 𝓞 ℚ) ∈ v.asIdeal)

    (Γt : Subgroup (ℍ[ℚ, a₁, b₁])ˣ) (hΓt : ∀ x : (ℍ[ℚ, a₁, b₁])ˣ, x ∈ Γt ↔ x ∈ CerednikDrinfeld.CosetGraph.awayUnits R₁ v)
    (s : HeckeTower.AwayPrime r rbar → (ℍ[ℚ, a₁, b₁])ˣ)
    (sf : HeckeTower.AwayPrime r rbar → (ℍ[ℚ, a₁, b₁] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ)
    (hs : ∀ ℓ : HeckeTower.AwayPrime r rbar,
      (∀ u : HeightOneSpectrum (𝓞 ℚ), ((r : ℕ) : 𝓞 ℚ) ∉ u.asIdeal →
        Submodule.finiteAdeleEvalAt ℍ[ℚ, a₁, b₁] u (sf ℓ : ℍ[ℚ, a₁, b₁] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ) =
          (s ℓ : ℍ[ℚ, a₁, b₁]) ⊗ₜ[ℚ] (1 : u.adicCompletion ℚ)) ∧
      (∀ u : HeightOneSpectrum (𝓞 ℚ), ((r : ℕ) : 𝓞 ℚ) ∈ u.asIdeal →
        Submodule.finiteAdeleEvalAt ℍ[ℚ, a₁, b₁] u (sf ℓ : ℍ[ℚ, a₁, b₁] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ) = 1) ∧
      Submodule.finiteIdeleDiagonal ℍ[ℚ, a₁, b₁]
          (Units.map (algebraMap ℚ ℍ[ℚ, a₁, b₁]).toMonoidHom
            (Units.mk0 ((ℓ.1 : ℕ) : ℚ) (Nat.cast_ne_zero.mpr ℓ.1.prop.ne_zero))) * (sf ℓ)⁻¹ ∈
        (if (ℓ.1 : ℕ) ∣ N then levelHeckeUSet Λ₁ (meetOrder R₁ n₁) (ℓ.1 : ℕ)
          else primeHeckeSet (meetOrder R₁ n₁) (ℓ.1 : ℕ)) ∧
      nrd (s ℓ : ℍ[ℚ, a₁, b₁]) = ((ℓ.1 : ℕ) : ℚ))
    (Γtℓ : HeckeTower.AwayPrime r rbar → Subgroup (ℍ[ℚ, a₁, b₁])ˣ) (hΓtℓ : ∀ ℓ : HeckeTower.AwayPrime r rbar, Γtℓ ℓ = Γt ⊓ Γt.map (MulAut.conj (s ℓ)).toMonoidHom)

    (wbar : (ℍ[ℚ, a₁, b₁])ˣ) (hwbar : nrd (wbar : ℍ[ℚ, a₁, b₁]) = ((rbar : ℕ) : ℚ) ∧ ∀ x : (ℍ[ℚ, a₁, b₁])ˣ, x ∈ Γt → wbar * x * wbar⁻¹ ∈ Γt)

    (hΛℤ : ∀ m : ℤ, ((m : ℚ) : ℍ[ℚ, a, b]) ∈ Λ)
    (coord : ↥Λ → Zp2 r × Zp2 r) (hcoord : IsOrderCoord Λ r coord)

    (A₀ : FakeEllipticCurve Λ N (Onr ⧸ Ideal.span {algebraMap 𝒪 Onr π}))
    (X₀ : FormalODModule r (Onr ⧸ Ideal.span {algebraMap 𝒪 Onr π}))
    (θ₀ : RelativeGroupLaw.FormalCoordinates A₀.f 2)
    (e e' : ↥Γt → (A₀.A ⟶ A₀.A)) (he : ∀ γ, e γ ≫ A₀.f = A₀.f) (deg : ↥Γt → ℕ)

    (hX₀ : X₀.HasHeight 4) (hA₀ : A₀.IsFormalModuleVia coord X₀ θ₀)

    (hE1 :
      (∀ γ : ↥Γt, FakeEllipticCurve.IsIsogenyPair (r ^ deg γ) A₀ A₀ (e γ) (e' γ) ∧ FakeEllipticCurve.PreservesLevel A₀ A₀ (e γ) (he γ)))
    (hE1mul :
      (∀ γ γ' : ↥Γt, ∃ i j : ℕ,
          e (γ * γ') ≫ A₀.act ⟨(((r ^ i : ℕ) : ℤ) : ℚ), hΛℤ _⟩ = e γ' ≫ e γ ≫ A₀.act ⟨(((r ^ j : ℕ) : ℤ) : ℚ), hΛℤ _⟩))
    (hE1sc :
      (∀ (γ : ↥Γt) (c : ℤ), ((γ : (ℍ[ℚ, a₁, b₁])ˣ) : ℍ[ℚ, a₁, b₁]) = (c : ℚ) • (1 : ℍ[ℚ, a₁, b₁]) →
          ∃ i : ℕ, e γ ≫ A₀.act ⟨(((r ^ i : ℕ) : ℤ) : ℚ), hΛℤ _⟩ = A₀.act ⟨((c * ((r ^ i : ℕ) : ℤ) : ℤ) : ℚ), hΛℤ _⟩))

    (hE1' :
      (∀ (γ : ↥Γt), (∃ (i c : ℕ), 0 < c ∧ e γ ≫ A₀.act ⟨(((r ^ i : ℕ) : ℤ) : ℚ), hΛℤ _⟩ = A₀.act ⟨((c : ℤ) : ℚ), hΛℤ _⟩) →
          ∃ c : ℚ, ((γ : (ℍ[ℚ, a₁, b₁])ˣ) : ℍ[ℚ, a₁, b₁]) = c • (1 : ℍ[ℚ, a₁, b₁])))

    (hE2 :
      (∀ E₀ : ↥(Subring.centralizer (Set.range X₀.actEnd ∪ {X₀.varpiEnd})) →+* Matrix (Fin 2) (Fin 2) K₀, Function.Injective E₀ →
        ∃ g : Matrix.GeneralLinearGroup (Fin 2) K₀, ∀ γ : ↥Γt, ∃ (ε : ↥(Subring.centralizer (Set.range X₀.actEnd ∪ {X₀.varpiEnd}))) (kγ : ℤ),
          (∀ (B' : Type) [CommRing B'] [Algebra (Onr ⧸ Ideal.span {algebraMap 𝒪 Onr π}) B'] (J : Ideal B') (m : ℕ),
              J ^ (m + 1) = ⊥ → ∀ s : Fin 2 → B', (∀ i, s i ∈ J) →
              θ₀ B' (fun i => MvFormalGroup.nilEval m ((ε : MvFormalGroup.End X₀.F).toPowerSeries i) s) =
                mapPt (e γ) (he γ) (θ₀ B' s)) ∧
          E₀ ε = ((r : K₀) ^ kγ) • ((g : Matrix (Fin 2) (Fin 2) K₀) * ι₀ ((γ : (ℍ[ℚ, a₁, b₁])ˣ) : ℍ[ℚ, a₁, b₁]) *
            ((g⁻¹ : Matrix.GeneralLinearGroup (Fin 2) K₀) : Matrix (Fin 2) (Fin 2) K₀))))

    (hE3 :
      (∀ P₀ : A₀.FullLevel n, ∃ lab : ↥Γt → ↥Λ,
        (∀ γ : ↥Γt, mapPt (e γ) (he γ) P₀.P = pushPt (A₀.act (lab γ)) (A₀.act_over (lab γ)) P₀.P) ∧
        (∀ γ γ' : ↥Γt, ∃ y : ↥Λ, (lab (γ * γ') : ℍ[ℚ, a, b]) - (lab γ' : ℍ[ℚ, a, b]) * (lab γ : ℍ[ℚ, a, b]) = (n : ℚ) • (y : ℍ[ℚ, a, b])) ∧
        (∀ (γ : ↥Γt) (c : ℤ), ((γ : (ℍ[ℚ, a₁, b₁])ˣ) : ℍ[ℚ, a₁, b₁]) = (c : ℚ) • (1 : ℍ[ℚ, a₁, b₁]) →
            ∃ y : ↥Λ, (lab γ : ℍ[ℚ, a, b]) - (c : ℚ) • (1 : ℍ[ℚ, a, b]) = (n : ℚ) • (y : ℍ[ℚ, a, b]))))

    (hE4 :
      (∀ (k : Type) [Field k] [IsAlgClosed k] [Algebra (Onr ⧸ Ideal.span {algebraMap 𝒪 Onr π}) k]
          (A : FakeEllipticCurve Λ N k) (gA : A.A ⟶ A₀.A),
          FakeEllipticCurve.IsPullbackVia (algebraMap (Onr ⧸ Ideal.span {algebraMap 𝒪 Onr π}) k) A₀ A gA →
          (∀ (φ ψ : A.A ⟶ A.A) (d : ℕ) (hφ : φ ≫ A.f = A.f),
              FakeEllipticCurve.IsIsogenyPair (r ^ d) A A φ ψ → FakeEllipticCurve.PreservesLevel A A φ hφ →
              ∃ (γ : ↥Γt) (i j : ℕ), φ ≫ A.act ⟨(((r ^ i : ℕ) : ℤ) : ℚ), hΛℤ _⟩ ≫ gA = gA ≫ e γ ≫ A₀.act ⟨(((r ^ j : ℕ) : ℤ) : ℚ), hΛℤ _⟩)))

    (R₂ : Submodule ℤ ℍ[ℚ, a₁, b₁]) (hR₂ : R₂ ≤ R₁) (hR₂o : IsOrder R₂)
          (hR₂r : ∀ x : ↥R₁, ∃ c : ℕ, ((r ^ c : ℕ) : ℚ) • (x : ℍ[ℚ, a₁, b₁]) ∈ R₂)
          (ê : ↥R₂ → (A₀.A ⟶ A₀.A)) (hê : ∀ x, ê x ≫ A₀.f = A₀.f)

        (hE5a : ∀ x : ↥R₂,
          (∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of (Onr ⧸ Ideal.span {algebraMap 𝒪 Onr π}))) (P Q : SchemeHomOver t A₀.f),
              mapPt (ê x) (hê x) (A₀.L.mul t P Q) = A₀.L.mul t (mapPt (ê x) (hê x) P) (mapPt (ê x) (hê x) Q)) ∧
          (∀ m : ↥Λ, A₀.act m ≫ ê x = ê x ≫ A₀.act m) ∧
          FakeEllipticCurve.PreservesLevel A₀ A₀ (ê x) (hê x))

        (hE5b1 : ∀ h : (1 : ℍ[ℚ, a₁, b₁]) ∈ R₂, ê ⟨1, h⟩ = 𝟙 A₀.A)
        (hE5b2 : ∀ (x y : ↥R₂) (h : (x : ℍ[ℚ, a₁, b₁]) * (y : ℍ[ℚ, a₁, b₁]) ∈ R₂),
            ê ⟨(x : ℍ[ℚ, a₁, b₁]) * (y : ℍ[ℚ, a₁, b₁]), h⟩ = ê y ≫ ê x)
        (hE5b3 : ∀ (m : ℤ) (h : ((m : ℚ) : ℍ[ℚ, a₁, b₁]) ∈ R₂), ê ⟨((m : ℚ) : ℍ[ℚ, a₁, b₁]), h⟩ = A₀.act ⟨((m : ℤ) : ℚ), hΛℤ m⟩)

        (hE5c : ∀ (x y : ↥R₂) (nx : ℤ), (y : ℍ[ℚ, a₁, b₁]) = star (x : ℍ[ℚ, a₁, b₁]) → nrd (x : ℍ[ℚ, a₁, b₁]) = (nx : ℚ) →
            ê y ≫ ê x = A₀.act ⟨((nx : ℤ) : ℚ), hΛℤ nx⟩)

        (hE5d : ∀ (γ : ↥Γt) (x : ↥R₂) (k : ℕ),
            (x : ℍ[ℚ, a₁, b₁]) = ((r ^ k : ℕ) : ℚ) • ((γ : (ℍ[ℚ, a₁, b₁])ˣ) : ℍ[ℚ, a₁, b₁]) →
            ∃ i j : ℕ, e γ ≫ A₀.act ⟨(((r ^ i : ℕ) : ℤ) : ℚ), hΛℤ _⟩ = ê x ≫ A₀.act ⟨(((r ^ j : ℕ) : ℤ) : ℚ), hΛℤ _⟩)

        (hE5e : ∀ E₀ : ↥(Subring.centralizer (Set.range X₀.actEnd ∪ {X₀.varpiEnd})) →+* Matrix (Fin 2) (Fin 2) K₀, Function.Injective E₀ →
          ∃ g : Matrix.GeneralLinearGroup (Fin 2) K₀,
            (∀ γ : ↥Γt, ∃ (ε : ↥(Subring.centralizer (Set.range X₀.actEnd ∪ {X₀.varpiEnd}))) (kγ : ℤ),
              (∀ (B' : Type) [CommRing B'] [Algebra (Onr ⧸ Ideal.span {algebraMap 𝒪 Onr π}) B'] (J : Ideal B') (m : ℕ),
                  J ^ (m + 1) = ⊥ → ∀ s : Fin 2 → B', (∀ i, s i ∈ J) →
                  θ₀ B' (fun i => MvFormalGroup.nilEval m ((ε : MvFormalGroup.End X₀.F).toPowerSeries i) s) =
                    mapPt (e γ) (he γ) (θ₀ B' s)) ∧
              E₀ ε = ((r : K₀) ^ kγ) • ((g : Matrix (Fin 2) (Fin 2) K₀) * ι₀ ((γ : (ℍ[ℚ, a₁, b₁])ˣ) : ℍ[ℚ, a₁, b₁]) *
                ((g⁻¹ : Matrix.GeneralLinearGroup (Fin 2) K₀) : Matrix (Fin 2) (Fin 2) K₀))) ∧
            (∀ x : ↥R₂, ∃ (ε : ↥(Subring.centralizer (Set.range X₀.actEnd ∪ {X₀.varpiEnd}))) (kx : ℤ),
              (∀ (B' : Type) [CommRing B'] [Algebra (Onr ⧸ Ideal.span {algebraMap 𝒪 Onr π}) B'] (J : Ideal B') (m : ℕ),
                  J ^ (m + 1) = ⊥ → ∀ s : Fin 2 → B', (∀ i, s i ∈ J) →
                  θ₀ B' (fun i => MvFormalGroup.nilEval m ((ε : MvFormalGroup.End X₀.F).toPowerSeries i) s) =
                    mapPt (ê x) (hê x) (θ₀ B' s)) ∧
              E₀ ε = ((r : K₀) ^ kx) • ((g : Matrix (Fin 2) (Fin 2) K₀) * ι₀ (x : ℍ[ℚ, a₁, b₁]) *
                ((g⁻¹ : Matrix.GeneralLinearGroup (Fin 2) K₀) : Matrix (Fin 2) (Fin 2) K₀))))

    (ι : Zp2 r →+* Onr)
    (Φ : FormalODModule r (Onr ⧸ pIdeal r Onr))
    (hΦ : Φ.IsSpecial ((Ideal.Quotient.mk (pIdeal r Onr)).comp ι))
    (hΦ4 : Φ.HasHeight 4)
    (MD : ModuliPackage.{0, 0} r Onr) (hMD : MD.IsZariskiSheaf)
    (η : ∀ (B : Type) [CommRing B] (ψ : Onr →+* B) (hB : IsNilpotent (r : B)),
      Rigidified r Φ B → MD.obj B ψ hB)
    (hη : (∀ (B : Type) [CommRing B] [IsNoetherianRing B] (ψ : Onr →+* B) (hB : IsNilpotent (r : B))
          (t t' : Rigidified r Φ B), t.IsAdmissible ι ψ → t'.IsAdmissible ι ψ →
          (η B ψ hB t = η B ψ hB t' ↔ t.IsIsomorphic t')) ∧
      (∀ (B B' : Type) [CommRing B] [CommRing B'] [IsNoetherianRing B] [IsNoetherianRing B'] (ψ : Onr →+* B) (ψ' : Onr →+* B')
          (hB : IsNilpotent (r : B)) (hB' : IsNilpotent (r : B')) (f : B →+* B')
          (hf : f.comp ψ = ψ') (t : Rigidified r Φ B), t.IsAdmissible ι ψ →
          η B' ψ' hB' (t.map f) = MD.map hB hB' f hf (η B ψ hB t)) ∧
      (∀ (B : Type) [CommRing B] [IsNoetherianRing B] (ψ : Onr →+* B) (hB : IsNilpotent (r : B)) (m : MD.obj B ψ hB),
          ∃ (n : ℕ) (f : Fin n → B), Ideal.span (Set.range f) = ⊤ ∧
            ∀ (i : Fin n) (L : Type) [CommRing L] [IsNoetherianRing L] [Algebra B L] [IsLocalization.Away (f i) L]
              (hL : IsNilpotent (r : L)),
              ∃ t : Rigidified r Φ L, t.IsAdmissible ι ((algebraMap B L).comp ψ) ∧
                η L ((algebraMap B L).comp ψ) hL t =
                  MD.map (ψ' := (algebraMap B L).comp ψ) hB hL (algebraMap B L) rfl m))
    (E₀ : Subring.centralizer (Set.range Φ.actEnd ∪ {Φ.varpiEnd}) →+* Matrix (Fin 2) (Fin 2) K₀)
    (hE₀ : Function.Injective E₀ ∧
      ∃ m : ℕ,
        (∀ A : Matrix (Fin 2) (Fin 2) 𝒪, ∃ e, E₀ e = (r : K₀) ^ m • A.map (algebraMap 𝒪 K₀)) ∧
        (∀ e, ∃ A : Matrix (Fin 2) (Fin 2) 𝒪, (r : K₀) ^ m • E₀ e = A.map (algebraMap 𝒪 K₀)))

      (eD : ∀ (B : Type) [CommRing B] [IsNoetherianRing B] [Algebra 𝒪 B], IsNilpotent (algebraMap 𝒪 B π) → (ModuliPackage.G 𝒪 MD).obj B → (AlgFunctor.prod (AlgFunctor.corep Onr) (Omega K₀ π)).obj B)

      (hnatD : ∀ (B : Type) [CommRing B] [IsNoetherianRing B] [Algebra 𝒪 B] (B' : Type) [CommRing B'] [IsNoetherianRing B'] [Algebra 𝒪 B'] (hB : IsNilpotent (algebraMap 𝒪 B π)) (hB' : IsNilpotent (algebraMap 𝒪 B' π))
          (φ : B →ₐ[𝒪] B') (x : (ModuliPackage.G 𝒪 MD).obj B), eD B' hB' ((ModuliPackage.G 𝒪 MD).map φ x) = (AlgFunctor.prod (AlgFunctor.corep Onr) (Omega K₀ π)).map φ (eD B hB x))

      (hbijD : ∀ (B : Type) [CommRing B] [IsNoetherianRing B] [Algebra 𝒪 B] (hB : IsNilpotent (algebraMap 𝒪 B π)), Function.Bijective (eD B hB))

      (hfstD : ∀ (B : Type) [CommRing B] [IsNoetherianRing B] [Algebra 𝒪 B] (hB : IsNilpotent (algebraMap 𝒪 B π)) (x : (ModuliPackage.G 𝒪 MD).obj B), (eD B hB x).1 = x.ψ)

      (hGLD : ∀ (B : Type) [CommRing B] [IsNoetherianRing B] [Algebra 𝒪 B] (hB : IsNilpotent (algebraMap 𝒪 B π)) (g : Matrix.GeneralLinearGroup (Fin 2) K₀) (x x' : (ModuliPackage.G 𝒪 MD).obj B),
          ModuliPackage.G.IsActBy ι Φ η Fr E₀ g x x' ↔ OmegaNr.IsTwistedAct π Onr Fr vdet B g (eD B hB x) (eD B hB x'))

      (hPiD : ∀ (B : Type) [CommRing B] [IsNoetherianRing B] [Algebra 𝒪 B] (hB : IsNilpotent (algebraMap 𝒪 B π)) (x x' : (ModuliPackage.G 𝒪 MD).obj B),
          ModuliPackage.G.IsPiTranslate ι Φ η Fr x x' → eD B hB x' = (frobTwist Onr Fr 1 (eD B hB x).1, (eD B hB x).2))

      (hPiexD : ∀ (B : Type) [CommRing B] [IsNoetherianRing B] [Algebra 𝒪 B] (x : (ModuliPackage.G 𝒪 MD).obj B), ∃ x' : (ModuliPackage.G 𝒪 MD).obj B, ModuliPackage.G.IsPiTranslate ι Φ η Fr x x')

    (κ : (Onr ⧸ Ideal.span {algebraMap 𝒪 Onr π}) →+* (Onr ⧸ pIdeal r Onr))
    (hκ : κ.comp (Ideal.Quotient.mk (Ideal.span {algebraMap 𝒪 Onr π})) = Ideal.Quotient.mk (pIdeal r Onr))
    (n₀ : ℕ) (β₀ : Series (Onr ⧸ pIdeal r Onr)) (hβ₀ : FormalODModule.IsIsogenyOfHeight Φ (X₀.map κ) β₀ (4 * n₀))

    (P₀ : A₀.FullLevel n)

    (A₀w : FakeEllipticCurve Λ N (Onr ⧸ Ideal.span {algebraMap 𝒪 Onr π}))
    (aw : A₀.A ⟶ A₀w.A) (haw : aw ≫ A₀w.f = A₀.f) (aw' : A₀w.A ⟶ A₀.A) (haw' : aw' ≫ A₀.f = A₀w.f)
    (kw : ℕ) (bw : A₀w.A ⟶ A₀.A) (hbw : bw ≫ A₀.f = A₀w.f) (bw' : A₀.A ⟶ A₀w.A) (habw : (aw ≫ bw) ≫ A₀.f = A₀.f)
    (hALw : FakeEllipticCurve.IsAtkinLehnerQuotientVia rbar A₀ A₀w aw haw aw' haw')
    (hBSw : FakeEllipticCurve.IsIsogenyPair (r ^ kw) A₀w A₀ bw bw') (hBSwlev : FakeEllipticCurve.PreservesLevel A₀w A₀ bw hbw)
    (hJOINTw :
      (∀ E₀ : ↥(Subring.centralizer (Set.range X₀.actEnd ∪ {X₀.varpiEnd})) →+* Matrix (Fin 2) (Fin 2) K₀, Function.Injective E₀ →
        ∃ g : Matrix.GeneralLinearGroup (Fin 2) K₀,
          (∀ γ : ↥Γt, ∃ (ε : ↥(Subring.centralizer (Set.range X₀.actEnd ∪ {X₀.varpiEnd}))) (kγ : ℤ),
          (∀ (B' : Type) [CommRing B'] [Algebra (Onr ⧸ Ideal.span {algebraMap 𝒪 Onr π}) B'] (J : Ideal B') (m : ℕ),
              J ^ (m + 1) = ⊥ → ∀ s : Fin 2 → B', (∀ i, s i ∈ J) →
              θ₀ B' (fun i => MvFormalGroup.nilEval m ((ε : MvFormalGroup.End X₀.F).toPowerSeries i) s) =
                mapPt (e γ) (he γ) (θ₀ B' s)) ∧
          E₀ ε = ((r : K₀) ^ kγ) • ((g : Matrix (Fin 2) (Fin 2) K₀) * ι₀ ((γ : (ℍ[ℚ, a₁, b₁])ˣ) : ℍ[ℚ, a₁, b₁]) *
            ((g⁻¹ : Matrix.GeneralLinearGroup (Fin 2) K₀) : Matrix (Fin 2) (Fin 2) K₀))) ∧

          (∃ (εw : ↥(Subring.centralizer (Set.range X₀.actEnd ∪ {X₀.varpiEnd}))) (k_w : ℤ),
              (∀ (B' : Type) [CommRing B'] [Algebra (Onr ⧸ Ideal.span {algebraMap 𝒪 Onr π}) B'] (J : Ideal B') (m : ℕ),
                J ^ (m + 1) = ⊥ → ∀ v : Fin 2 → B', (∀ i, v i ∈ J) →
                θ₀ B' (fun i => MvFormalGroup.nilEval m ((εw : MvFormalGroup.End X₀.F).toPowerSeries i) v) =
                  mapPt (aw ≫ bw) habw (θ₀ B' v)) ∧
              E₀ εw = ((r : K₀) ^ k_w) • ((g : Matrix (Fin 2) (Fin 2) K₀) * ι₀ ((wbar : (ℍ[ℚ, a₁, b₁])ˣ) : ℍ[ℚ, a₁, b₁]) *
                ((g⁻¹ : Matrix.GeneralLinearGroup (Fin 2) K₀) : Matrix (Fin 2) (Fin 2) K₀)))))

    (Ξ : ∀ (B : Type) [CommRing B] [IsNoetherianRing B] [Algebra 𝒪 B] (ψ : Onr →ₐ[𝒪] B),
        IsNilpotent (algebraMap 𝒪 B π) → FakeEllipticCurve.RigidifiedCurve r π A₀ B ψ → ModuliPackage.GPoint 𝒪 MD B)

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

    (g₀ : Matrix.GeneralLinearGroup (Fin 2) K₀)

      (heqΓ : ∀ (B : Type) [CommRing B] [IsNoetherianRing B] [Algebra 𝒪 B] (ψ : Onr →ₐ[𝒪] B) (hB : IsNilpotent (algebraMap 𝒪 B π))
          (hconn : ∀ e : B, IsIdempotentElem e → e = 0 ∨ e = 1)
          (E : FakeEllipticCurve Λ N B) (ρ ρ' : FakeEllipticCurve.Rigidification r π A₀ ψ E) (γ : ↥Γt),
          FakeEllipticCurve.Rigidification.IsTranslateBy hΛℤ (e γ) ρ ρ' →
            ∃ c : ℤ,
              ModuliPackage.G.IsActBy ι Φ η Fr E₀
                ((Units.map (algebraMap K₀ (Matrix (Fin 2) (Fin 2) K₀)).toMonoidHom
                  (Units.mk0 (r : K₀) (Nat.cast_ne_zero.mpr (Fact.out : r.Prime).ne_zero))) ^ c *
                  (g₀ * Units.map (ι₀ : ℍ[ℚ, a₁, b₁] →* Matrix (Fin 2) (Fin 2) K₀) (γ : (ℍ[ℚ, a₁, b₁])ˣ) * g₀⁻¹))
                (Ξ B ψ hB ⟨E, ρ⟩) (Ξ B ψ hB ⟨E, ρ'⟩))

      (heqW : ∀ (B : Type) [CommRing B] [IsNoetherianRing B] [Algebra 𝒪 B] (ψ : Onr →ₐ[𝒪] B) (hB : IsNilpotent (algebraMap 𝒪 B π))
          (hconn : ∀ e : B, IsIdempotentElem e → e = 0 ∨ e = 1)
          (hrbarB : IsUnit ((rbar : ℕ) : B))
          (E Ef : FakeEllipticCurve Λ N B)
          (q : E.A ⟶ Ef.A) (hq : q ≫ Ef.f = E.f) (q' : Ef.A ⟶ E.A) (hq' : q' ≫ E.f = Ef.f),
          FakeEllipticCurve.IsAtkinLehnerQuotientVia rbar E Ef q hq q' hq' →
          ∀ (ρ : FakeEllipticCurve.Rigidification r π A₀ ψ E) (ρf : FakeEllipticCurve.Rigidification r π A₀ ψ Ef),
          (∃ (qb : ρ.Eb.A ⟶ ρf.Eb.A) (_ : qb ≫ ρf.gb = ρ.gb ≫ q) (_ : qb ≫ ρf.Eb.f = ρ.Eb.f)
            (uA : ρf.Ab.A ⟶ ρ.Ab.A) (_ : FakeEllipticCurve.IsPullbackVia (RingHom.id _) ρ.Ab ρf.Ab uA) (_ : uA ≫ ρ.gA = ρf.gA)
            (ewb : ρ.Ab.A ⟶ ρ.Ab.A) (_ : ewb ≫ ρ.gA = ρ.gA ≫ (aw ≫ bw)) (_ : ewb ≫ ρ.Ab.f = ρ.Ab.f)
            (i j : ℕ),
            qb ≫ ρf.φ ≫ uA ≫ ρ.Ab.act ⟨(((r ^ i : ℕ) : ℤ) : ℚ), hΛℤ _⟩ = ρ.φ ≫ ewb ≫ ρ.Ab.act ⟨(((r ^ j : ℕ) : ℤ) : ℚ), hΛℤ _⟩) →
            ∃ c : ℤ,
              ModuliPackage.G.IsActBy ι Φ η Fr E₀
                ((Units.map (algebraMap K₀ (Matrix (Fin 2) (Fin 2) K₀)).toMonoidHom
                  (Units.mk0 (r : K₀) (Nat.cast_ne_zero.mpr (Fact.out : r.Prime).ne_zero))) ^ c *
                  (g₀ * Units.map (ι₀ : ℍ[ℚ, a₁, b₁] →* Matrix (Fin 2) (Fin 2) K₀) wbar * g₀⁻¹))
                (Ξ B ψ hB ⟨E, ρ⟩) (Ξ B ψ hB ⟨Ef, ρf⟩))

      (hK1 : ∀ (B : Type) [CommRing B] [IsNoetherianRing B] [Algebra 𝒪 B] (hB : IsNilpotent (algebraMap 𝒪 B π))
          (hconn : ∀ e : B, IsIdempotentElem e → e = 0 ∨ e = 1) (ψ : Onr →ₐ[𝒪] B) (P : (Omega K₀ π).obj B),
          ∃ (E : FakeEllipticCurve Λ N B) (ϱ : FakeEllipticCurve.Rigidification r π A₀ (frobTwist Onr Fr (- Multiplicative.toAdd (vdet g₀)) ψ) E),
            (Ξ B (frobTwist Onr Fr (- Multiplicative.toAdd (vdet g₀)) ψ) hB ⟨E, ϱ⟩).ψ = (frobTwist Onr Fr (- Multiplicative.toAdd (vdet g₀)) ψ) ∧
            OmegaNr.IsTwistedAct π Onr Fr vdet B g₀⁻¹ (eD B hB (Ξ B (frobTwist Onr Fr (- Multiplicative.toAdd (vdet g₀)) ψ) hB ⟨E, ϱ⟩)) (ψ, P))

      (hK2 : ∀ (B : Type) [CommRing B] [IsNoetherianRing B] [Algebra 𝒪 B] (hB : IsNilpotent (algebraMap 𝒪 B π))
          (hconn : ∀ e : B, IsIdempotentElem e → e = 0 ∨ e = 1) (ψ : Onr →ₐ[𝒪] B) (P : (Omega K₀ π).obj B)
          (E : FakeEllipticCurve Λ N B) (ϱ : FakeEllipticCurve.Rigidification r π A₀ (frobTwist Onr Fr (- Multiplicative.toAdd (vdet g₀)) ψ) E) (E' : FakeEllipticCurve Λ N B) (ϱ' : FakeEllipticCurve.Rigidification r π A₀ (frobTwist Onr Fr (- Multiplicative.toAdd (vdet g₀)) ψ) E'),
          (Ξ B (frobTwist Onr Fr (- Multiplicative.toAdd (vdet g₀)) ψ) hB ⟨E, ϱ⟩).ψ = (frobTwist Onr Fr (- Multiplicative.toAdd (vdet g₀)) ψ) → OmegaNr.IsTwistedAct π Onr Fr vdet B g₀⁻¹ (eD B hB (Ξ B (frobTwist Onr Fr (- Multiplicative.toAdd (vdet g₀)) ψ) hB ⟨E, ϱ⟩)) (ψ, P) →
          (Ξ B (frobTwist Onr Fr (- Multiplicative.toAdd (vdet g₀)) ψ) hB ⟨E', ϱ'⟩).ψ = (frobTwist Onr Fr (- Multiplicative.toAdd (vdet g₀)) ψ) → OmegaNr.IsTwistedAct π Onr Fr vdet B g₀⁻¹ (eD B hB (Ξ B (frobTwist Onr Fr (- Multiplicative.toAdd (vdet g₀)) ψ) hB ⟨E', ϱ'⟩)) (ψ, P) →
            ∃ (i : E.A ≅ E'.A) (hi : i.hom ≫ E'.f = E.f), FakeEllipticCurve.IsoVia E E' i hi ∧
              (∃ (ib : ϱ.Eb.A ⟶ ϱ'.Eb.A) (_ : ib ≫ ϱ'.gb = ϱ.gb ≫ i.hom) (_ : ib ≫ ϱ'.Eb.f = ϱ.Eb.f)
                (uA : ϱ'.Ab.A ⟶ ϱ.Ab.A) (_ : FakeEllipticCurve.IsPullbackVia (RingHom.id _) ϱ.Ab ϱ'.Ab uA) (_ : uA ≫ ϱ.gA = ϱ'.gA)
                (i₁ j₁ : ℕ),
                ib ≫ ϱ'.φ ≫ uA ≫ ϱ.Ab.act ⟨(((r ^ i₁ : ℕ) : ℤ) : ℚ), hΛℤ _⟩ = ϱ.φ ≫ ϱ.Ab.act ⟨(((r ^ j₁ : ℕ) : ℤ) : ℚ), hΛℤ _⟩))

      (hK3 : ∀ (B : Type) [CommRing B] [IsNoetherianRing B] [Algebra 𝒪 B] (hB : IsNilpotent (algebraMap 𝒪 B π))
          (B' : Type) [CommRing B'] [IsNoetherianRing B'] [Algebra 𝒪 B'] (hB' : IsNilpotent (algebraMap 𝒪 B' π)) (φ : B →ₐ[𝒪] B')
          (ψ : Onr →ₐ[𝒪] B) (P : (Omega K₀ π).obj B) (E : FakeEllipticCurve Λ N B) (ϱ : FakeEllipticCurve.Rigidification r π A₀ (frobTwist Onr Fr (- Multiplicative.toAdd (vdet g₀)) ψ) E),
          (Ξ B (frobTwist Onr Fr (- Multiplicative.toAdd (vdet g₀)) ψ) hB ⟨E, ϱ⟩).ψ = (frobTwist Onr Fr (- Multiplicative.toAdd (vdet g₀)) ψ) → OmegaNr.IsTwistedAct π Onr Fr vdet B g₀⁻¹ (eD B hB (Ξ B (frobTwist Onr Fr (- Multiplicative.toAdd (vdet g₀)) ψ) hB ⟨E, ϱ⟩)) (ψ, P) →
            ∃ (E' : FakeEllipticCurve Λ N B') (g : E'.A ⟶ E.A) (hg : FakeEllipticCurve.IsPullbackVia (φ : B →+* B') E E' g)
              (ϱ' : FakeEllipticCurve.Rigidification r π A₀ (frobTwist Onr Fr (- Multiplicative.toAdd (vdet g₀)) (φ.comp ψ)) E'),
              FakeEllipticCurve.Rigidification.IsPullbackVia φ g hg ϱ ϱ' ∧
              (Ξ B' (frobTwist Onr Fr (- Multiplicative.toAdd (vdet g₀)) (φ.comp ψ)) hB' ⟨E', ϱ'⟩).ψ = (frobTwist Onr Fr (- Multiplicative.toAdd (vdet g₀)) (φ.comp ψ)) ∧ OmegaNr.IsTwistedAct π Onr Fr vdet B' g₀⁻¹ (eD B' hB' (Ξ B' (frobTwist Onr Fr (- Multiplicative.toAdd (vdet g₀)) (φ.comp ψ)) hB' ⟨E', ϱ'⟩)) ((φ.comp ψ), ((Omega K₀ π).map φ P)))

      (hK4 : ∀ (B : Type) [CommRing B] [IsNoetherianRing B] [Algebra 𝒪 B] (B₀ : Type) [CommRing B₀] [IsNoetherianRing B₀] [Algebra 𝒪 B₀] (p : B →ₐ[𝒪] B₀)
          (hB : IsNilpotent (algebraMap 𝒪 B π)) (hB₀ : IsNilpotent (algebraMap 𝒪 B₀ π)),
          Function.Surjective p → (∀ s t : B, p s = 0 → p t = 0 → s * t = 0) →
          ∀ (ψ : Onr →ₐ[𝒪] B) (E : FakeEllipticCurve Λ N B) (E₀ : FakeEllipticCurve Λ N B₀) (g : E₀.A ⟶ E.A)
            (hg : FakeEllipticCurve.IsPullbackVia (p : B →+* B₀) E E₀ g) (ϱ₀ : FakeEllipticCurve.Rigidification r π A₀ (frobTwist Onr Fr (- Multiplicative.toAdd (vdet g₀)) (p.comp ψ)) E₀),
            (Ξ B₀ (frobTwist Onr Fr (- Multiplicative.toAdd (vdet g₀)) (p.comp ψ)) hB₀ ⟨E₀, ϱ₀⟩).ψ = (frobTwist Onr Fr (- Multiplicative.toAdd (vdet g₀)) (p.comp ψ)) →
            ∃ (ϱ : FakeEllipticCurve.Rigidification r π A₀ (frobTwist Onr Fr (- Multiplicative.toAdd (vdet g₀)) ψ) E) (ϱ₀' : FakeEllipticCurve.Rigidification r π A₀ (frobTwist Onr Fr (- Multiplicative.toAdd (vdet g₀)) (p.comp ψ)) E₀),
              FakeEllipticCurve.Rigidification.IsPullbackVia p g hg ϱ ϱ₀' ∧ (Ξ B (frobTwist Onr Fr (- Multiplicative.toAdd (vdet g₀)) ψ) hB ⟨E, ϱ⟩).ψ = (frobTwist Onr Fr (- Multiplicative.toAdd (vdet g₀)) ψ) ∧
              ∀ P₀' : (Omega K₀ π).obj B₀,
                OmegaNr.IsTwistedAct π Onr Fr vdet B₀ g₀⁻¹ (eD B₀ hB₀ (Ξ B₀ (frobTwist Onr Fr (- Multiplicative.toAdd (vdet g₀)) (p.comp ψ)) hB₀ ⟨E₀, ϱ₀⟩)) ((p.comp ψ), P₀') ↔
                  OmegaNr.IsTwistedAct π Onr Fr vdet B₀ g₀⁻¹ (eD B₀ hB₀ (Ξ B₀ (frobTwist Onr Fr (- Multiplicative.toAdd (vdet g₀)) (p.comp ψ)) hB₀ ⟨E₀, ϱ₀'⟩)) ((p.comp ψ), P₀'))

      (hC0e : ∀ (B : Type) [CommRing B] [IsNoetherianRing B] [Algebra 𝒪 B] (hB : IsNilpotent (algebraMap 𝒪 B π))
          (hconn : ∀ e : B, IsIdempotentElem e → e = 0 ∨ e = 1) (ψ : Onr →ₐ[𝒪] B)
          (E : FakeEllipticCurve Λ N B) (ϱ : FakeEllipticCurve.Rigidification r π A₀ (frobTwist Onr Fr (- Multiplicative.toAdd (vdet g₀)) ψ) E)
          (X : FormalODModule r B) (θ : RelativeGroupLaw.FormalCoordinates E.f 2), E.IsFormalModuleVia coord X θ →
          ∃ Pn : E.FullLevel n, FakeEllipticCurve.Rigidification.IsNormLevelTransport Fr θ₀ κ β₀ Φ ι coord P₀ ϱ Pn)

      (hC0u : ∀ (B : Type) [CommRing B] [IsNoetherianRing B] [Algebra 𝒪 B] (hB : IsNilpotent (algebraMap 𝒪 B π)) (ψ : Onr →ₐ[𝒪] B)
          (E : FakeEllipticCurve Λ N B) (ϱ : FakeEllipticCurve.Rigidification r π A₀ (frobTwist Onr Fr (- Multiplicative.toAdd (vdet g₀)) ψ) E) (Pn Pn' : E.FullLevel n),
          FakeEllipticCurve.Rigidification.IsNormLevelTransport Fr θ₀ κ β₀ Φ ι coord P₀ ϱ Pn → FakeEllipticCurve.Rigidification.IsNormLevelTransport Fr θ₀ κ β₀ Φ ι coord P₀ ϱ Pn' → Pn.P = Pn'.P)

      (Θf : ∀ (B : Type) [CommRing B] [IsNoetherianRing B] [Algebra 𝒪 B], IsNilpotent (algebraMap 𝒪 B π) → (AlgFunctor.prod (AlgFunctor.prod (AlgFunctor.corep Onr) (Omega K₀ π)) (AlgFunctor.const G)).obj B → (Scheme.nilpPoints fM).obj B)

      (hnat : ∀ (B : Type) [CommRing B] [IsNoetherianRing B] [Algebra 𝒪 B] (B' : Type) [CommRing B'] [IsNoetherianRing B'] [Algebra 𝒪 B'] (hB : IsNilpotent (algebraMap 𝒪 B π))
          (hB' : IsNilpotent (algebraMap 𝒪 B' π)) (φ : B →ₐ[𝒪] B') (x : (AlgFunctor.prod (AlgFunctor.prod (AlgFunctor.corep Onr) (Omega K₀ π)) (AlgFunctor.const G)).obj B),
          Θf B' hB' ((AlgFunctor.prod (AlgFunctor.prod (AlgFunctor.corep Onr) (Omega K₀ π)) (AlgFunctor.const G)).map φ x) = (Scheme.nilpPoints fM).map φ (Θf B hB x))

      (hG : ∀ (B : Type) [CommRing B] [IsNoetherianRing B] [Algebra 𝒪 B] (hB : IsNilpotent (algebraMap 𝒪 B π)) (x : (AlgFunctor.prod (AlgFunctor.corep Onr) (Omega K₀ π)).obj B) (g h : G),
          (Scheme.nilpPoints.mapHom fM fM (ρ h).hom (hρ.over_base h)).app B (Θf B hB (x, g * h)) = Θf B hB (x, g))

      (hC2 : ∀ (B : Type) [CommRing B] [IsNoetherianRing B] [Algebra 𝒪 B] (hB : IsNilpotent (algebraMap 𝒪 B π)) (ψ : Onr →ₐ[𝒪] B) (P : (Omega K₀ π).obj B)
          (E : FakeEllipticCurve Λ N B) (ϱ : FakeEllipticCurve.Rigidification r π A₀ (frobTwist Onr Fr (- Multiplicative.toAdd (vdet g₀)) ψ) E) (Pn : E.FullLevel n),
          (Ξ B (frobTwist Onr Fr (- Multiplicative.toAdd (vdet g₀)) ψ) hB ⟨E, ϱ⟩).ψ = (frobTwist Onr Fr (- Multiplicative.toAdd (vdet g₀)) ψ) → OmegaNr.IsTwistedAct π Onr Fr vdet B g₀⁻¹ (eD B hB (Ξ B (frobTwist Onr Fr (- Multiplicative.toAdd (vdet g₀)) ψ) hB ⟨E, ϱ⟩)) (ψ, P) → FakeEllipticCurve.Rigidification.IsNormLevelTransport Fr θ₀ κ β₀ Φ ι coord P₀ ϱ Pn →
            (Θf B hB ((ψ, P), (1 : G))).1 = (ptF B (Spec.map (CommRingCat.ofHom (algebraMap 𝒪 B))) ⟨E, Pn⟩).1)

    (hC2c : ∀ (B : Type) [CommRing B] [IsNoetherianRing B] [Algebra 𝒪 B] (hB : IsNilpotent (algebraMap 𝒪 B π)) (ψ : Onr →ₐ[𝒪] B) (P : (Omega K₀ π).obj B)
          (E : FakeEllipticCurve Λ N B) (ϱ : FakeEllipticCurve.Rigidification r π A₀ (frobTwist Onr Fr (- Multiplicative.toAdd (vdet g₀)) ψ) E),
          (Ξ B (frobTwist Onr Fr (- Multiplicative.toAdd (vdet g₀)) ψ) hB ⟨E, ϱ⟩).ψ = (frobTwist Onr Fr (- Multiplicative.toAdd (vdet g₀)) ψ) → OmegaNr.IsTwistedAct π Onr Fr vdet B g₀⁻¹ (eD B hB (Ξ B (frobTwist Onr Fr (- Multiplicative.toAdd (vdet g₀)) ψ) hB ⟨E, ϱ⟩)) (ψ, P) →
            (Θf B hB ((ψ, P), (1 : G))).1 ≫ p = (pt B (Spec.map (CommRingCat.ofHom (algebraMap 𝒪 B))) E).1)

    (θt : ↥Γt →* G)

    (hC3 : ∀ (B : Type) [CommRing B] [IsNoetherianRing B] [Algebra 𝒪 B] (hB : IsNilpotent (algebraMap 𝒪 B π))
          (hconn : ∀ e : B, IsIdempotentElem e → e = 0 ∨ e = 1) (ψ : Onr →ₐ[𝒪] B) (P : (Omega K₀ π).obj B) (E : FakeEllipticCurve Λ N B) (ϱ : FakeEllipticCurve.Rigidification r π A₀ (frobTwist Onr Fr (- Multiplicative.toAdd (vdet g₀)) ψ) E),
          (Ξ B (frobTwist Onr Fr (- Multiplicative.toAdd (vdet g₀)) ψ) hB ⟨E, ϱ⟩).ψ = (frobTwist Onr Fr (- Multiplicative.toAdd (vdet g₀)) ψ) → OmegaNr.IsTwistedAct π Onr Fr vdet B g₀⁻¹ (eD B hB (Ξ B (frobTwist Onr Fr (- Multiplicative.toAdd (vdet g₀)) ψ) hB ⟨E, ϱ⟩)) (ψ, P) →
          ∀ (γ : (ℍ[ℚ, a₁, b₁])ˣ) (hγ : γ ∈ Γt) (ψ' : Onr →ₐ[𝒪] B) (P' : (Omega K₀ π).obj B),
            OmegaNr.IsTwistedAct π Onr Fr vdet B ((Units.map (ι₀ : ℍ[ℚ, a₁, b₁] →* Matrix (Fin 2) (Fin 2) K₀)) γ) (ψ, P) (ψ', P') →
            ∃ ϱ' : FakeEllipticCurve.Rigidification r π A₀ (frobTwist Onr Fr (- Multiplicative.toAdd (vdet g₀)) ψ') E,
              (Ξ B (frobTwist Onr Fr (- Multiplicative.toAdd (vdet g₀)) ψ') hB ⟨E, ϱ'⟩).ψ = (frobTwist Onr Fr (- Multiplicative.toAdd (vdet g₀)) ψ') ∧ OmegaNr.IsTwistedAct π Onr Fr vdet B g₀⁻¹ (eD B hB (Ξ B (frobTwist Onr Fr (- Multiplicative.toAdd (vdet g₀)) ψ') hB ⟨E, ϱ'⟩)) (ψ', P') ∧
              (∀ (Pn Pn' : E.FullLevel n), FakeEllipticCurve.Rigidification.IsNormLevelTransport Fr θ₀ κ β₀ Φ ι coord P₀ ϱ Pn → FakeEllipticCurve.Rigidification.IsNormLevelTransport Fr θ₀ κ β₀ Φ ι coord P₀ ϱ' Pn' →
                  Pn'.P = pushPt (E.act (χ (θt ⟨γ, hγ⟩))) (E.act_over (χ (θt ⟨γ, hγ⟩))) Pn.P) ∧
              (∀ (ℓ : ℕ) [Fact ℓ.Prime], ℓ ≠ r → IsUnit ((ℓ : ℕ) : B) → ∀ (K₀ : A₀.ExtraLevel ℓ),
                  (∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of (Onr ⧸ Ideal.span {algebraMap 𝒪 Onr π}))) (R : SchemeHomOver t A₀.f),
                      FactorsThrough K₀.levK R → FactorsThrough K₀.levK (mapPt (e ⟨γ, hγ⟩) (he ⟨γ, hγ⟩) R)) →
                  ∀ (C C' : E.ExtraLevel ℓ), (∀ {T : Scheme.{0}} (t' : T ⟶ Spec (CommRingCat.of (B ⧸ Ideal.span {algebraMap 𝒪 B π}))) (R : SchemeHomOver t' ϱ.Eb.f),
                  (∃ R₀ : T ⟶ C.K, R₀ ≫ C.levK = R.1 ≫ ϱ.gb) → ∃ Q₀ : T ⟶ K₀.K, Q₀ ≫ K₀.levK = (R.1 ≫ ϱ.φ) ≫ ϱ.gA) → (∀ {T : Scheme.{0}} (t' : T ⟶ Spec (CommRingCat.of (B ⧸ Ideal.span {algebraMap 𝒪 B π}))) (R : SchemeHomOver t' ϱ'.Eb.f),
                  (∃ R₀ : T ⟶ C'.K, R₀ ≫ C'.levK = R.1 ≫ ϱ'.gb) → ∃ Q₀ : T ⟶ K₀.K, Q₀ ≫ K₀.levK = (R.1 ≫ ϱ'.φ) ≫ ϱ'.gA) →
                    ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of B)) (R : SchemeHomOver t E.f),
                      FactorsThrough C.levK R ↔ FactorsThrough C'.levK R))

    (k : Type) [Field k] [IsAlgClosed k] [Algebra 𝒪 k] (hk : IsNilpotent (algebraMap 𝒪 k π))
    (ψ : Onr →ₐ[𝒪] k) (P P' : (Omega K₀ π).obj k)
    (E : FakeEllipticCurve Λ N k) (ϱ : FakeEllipticCurve.Rigidification r π A₀ (frobTwist Onr Fr (- Multiplicative.toAdd (vdet g₀)) ψ) E) (E' : FakeEllipticCurve Λ N k) (ϱ' : FakeEllipticCurve.Rigidification r π A₀ (frobTwist Onr Fr (- Multiplicative.toAdd (vdet g₀)) ψ) E')
    (hΞψ : (Ξ k (frobTwist Onr Fr (- Multiplicative.toAdd (vdet g₀)) ψ) hk ⟨E, ϱ⟩).ψ = (frobTwist Onr Fr (- Multiplicative.toAdd (vdet g₀)) ψ)) (hev : OmegaNr.IsTwistedAct π Onr Fr vdet k g₀⁻¹ (eD k hk (Ξ k (frobTwist Onr Fr (- Multiplicative.toAdd (vdet g₀)) ψ) hk ⟨E, ϱ⟩)) (ψ, P))
    (hΞψ' : (Ξ k (frobTwist Onr Fr (- Multiplicative.toAdd (vdet g₀)) ψ) hk ⟨E', ϱ'⟩).ψ = (frobTwist Onr Fr (- Multiplicative.toAdd (vdet g₀)) ψ)) (hev' : OmegaNr.IsTwistedAct π Onr Fr vdet k g₀⁻¹ (eD k hk (Ξ k (frobTwist Onr Fr (- Multiplicative.toAdd (vdet g₀)) ψ) hk ⟨E', ϱ'⟩)) (ψ, P'))
    (i : E.A ≅ E'.A) (hi : i.hom ≫ E'.f = E.f) (hvia : FakeEllipticCurve.IsoVia E E' i hi)
    :
      ∃ (γ : (ℍ[ℚ, a₁, b₁])ˣ) (hγ : γ ∈ Γt),
        OmegaNr.IsTwistedAct π Onr Fr vdet k ((Units.map (ι₀ : ℍ[ℚ, a₁, b₁] →* Matrix (Fin 2) (Fin 2) K₀)) γ) (ψ, P) (ψ, P') ∧
        ∃ ϱ'' : FakeEllipticCurve.Rigidification r π A₀ (frobTwist Onr Fr (- Multiplicative.toAdd (vdet g₀)) ψ) E,
          ((Ξ k (frobTwist Onr Fr (- Multiplicative.toAdd (vdet g₀)) ψ) hk ⟨E, ϱ''⟩).ψ = (frobTwist Onr Fr (- Multiplicative.toAdd (vdet g₀)) ψ) ∧ OmegaNr.IsTwistedAct π Onr Fr vdet k g₀⁻¹ (eD k hk (Ξ k (frobTwist Onr Fr (- Multiplicative.toAdd (vdet g₀)) ψ) hk ⟨E, ϱ''⟩)) (ψ, P')) ∧
          FakeEllipticCurve.Rigidification.IsTranslateBy hΛℤ (e ⟨γ, hγ⟩) ϱ ϱ'' ∧
          (∃ (ib : ϱ''.Eb.A ⟶ ϱ'.Eb.A) (_ : ib ≫ ϱ'.gb = ϱ''.gb ≫ i.hom) (_ : ib ≫ ϱ'.Eb.f = ϱ''.Eb.f)
                (uA : ϱ'.Ab.A ⟶ ϱ''.Ab.A) (_ : FakeEllipticCurve.IsPullbackVia (RingHom.id _) ϱ''.Ab ϱ'.Ab uA) (_ : uA ≫ ϱ''.gA = ϱ'.gA)
                (i₁ j₁ : ℕ),
                ib ≫ ϱ'.φ ≫ uA ≫ ϱ''.Ab.act ⟨(((r ^ i₁ : ℕ) : ℤ) : ℚ), hΛℤ _⟩ = ϱ''.φ ≫ ϱ''.Ab.act ⟨(((r ^ j₁ : ℕ) : ℤ) : ℚ), hΛℤ _⟩)
:= by
  classical

  have hπ0 : algebraMap 𝒪 k π = 0 := hk.eq_zero
  have hI : Ideal.span {algebraMap 𝒪 k π} = ⊥ := Ideal.span_singleton_eq_bot.mpr hπ0
  haveI hImax : (Ideal.span {algebraMap 𝒪 k π}).IsMaximal := by rw [hI]; exact Ideal.bot_isMaximal
  letI instF : Field (k ⧸ Ideal.span {algebraMap 𝒪 k π}) := Ideal.Quotient.field _
  haveI instAC : IsAlgClosed (k ⧸ Ideal.span {algebraMap 𝒪 k π}) :=
    IsAlgClosed.of_ringEquiv (k := k) (k ⧸ Ideal.span {algebraMap 𝒪 k π})
      ((RingEquiv.quotientBot k).symm.trans (Ideal.quotEquivOfEq hI.symm))
  letI instA : Algebra (Onr ⧸ Ideal.span {algebraMap 𝒪 Onr π}) (k ⧸ Ideal.span {algebraMap 𝒪 k π}) :=
    (FakeEllipticCurve.Rigidification.residueLeg π (frobTwist Onr Fr (- Multiplicative.toAdd (vdet g₀)) ψ)).toAlgebra
  have hNk : IsUnit ((N : ℕ) : k ⧸ Ideal.span {algebraMap 𝒪 k π}) := by
    have h := (CerednikDrinfeld.isUnit_natCast_of_not_dvd_of_card_quotient 𝒪 π hcomplete hres hunr N hrN).map
      ((Ideal.Quotient.mk (Ideal.span {algebraMap 𝒪 k π})).comp (algebraMap 𝒪 k))
    simpa using h
  have hconn : ∀ e : k, IsIdempotentElem e → e = 0 ∨ e = 1 := fun e he => IsIdempotentElem.iff_eq_zero_or_one.mp he

  obtain ⟨ib, hib, hibf, hibv, uA, huA, huAg, Ψ, hΦ, hpair, hlev⟩ :=
    G3Aux.exists_comparison_composite_pair hΛ.isOrder hΛℤ hrN hk hNk i hi hvia ϱ ϱ'

  obtain ⟨γ₀, i₀, j₀, hconj⟩ :=
    hE4 (k ⧸ Ideal.span {algebraMap 𝒪 k π}) ϱ.Ab ϱ.gA ϱ.isPullback_Ab _ Ψ (ϱ.d + ϱ'.d) hΦ hpair hlev

  obtain ⟨ρ₂, htr, hell₂⟩ :=
    CerednikDrinfeld.QM.FakeEllipticCurve.Rigidification.exists_isTranslateBy_of_isIsogenyPair hΛℤ
      (e γ₀) (e' γ₀) (he γ₀) (deg γ₀) (hE1 γ₀).1 (hE1 γ₀).2 ϱ

  obtain ⟨ib', hib', hibf', uA', huA', huAg', i₁, j₁, hcorr⟩ :=
    G3Aux.exists_corr_of_conj_of_isTranslateBy hΛℤ hNk i ϱ ϱ' ρ₂ ib hib hibf hibv uA huA huAg (e γ₀) i₀ j₀ hconj htr

  have hΞeq : Ξ k (frobTwist Onr Fr (- Multiplicative.toAdd (vdet g₀)) ψ) hk ⟨E, ρ₂⟩ = Ξ k (frobTwist Onr Fr (- Multiplicative.toAdd (vdet g₀)) ψ) hk ⟨E', ϱ'⟩ :=
    hΞiso k (frobTwist Onr Fr (- Multiplicative.toAdd (vdet g₀)) ψ) hk ⟨E, ρ₂⟩ ⟨E', ϱ'⟩ i hi hvia ⟨ib', hib', hibf', uA', huA', huAg', i₁, j₁, hcorr⟩

  obtain ⟨c, hact3⟩ := heqΓ k (frobTwist Onr Fr (- Multiplicative.toAdd (vdet g₀)) ψ) hk hconn E ϱ ρ₂ γ₀ htr
  rw [hΞeq] at hact3
  have h3 := (hGLD k hk _ _ _).1 hact3

  obtain ⟨z, hzΓ, hzS, hzval⟩ := G3Aux.exists_center_r R₁ hR₁ ι₀ v hv Γt hΓt
  have htw : OmegaNr.IsTwistedAct π Onr Fr vdet k
      ((Units.map (ι₀ : ℍ[ℚ, a₁, b₁] →* Matrix (Fin 2) (Fin 2) K₀)) (z ^ c * (γ₀ : (ℍ[ℚ, a₁, b₁])ˣ))) (ψ, P) (ψ, P') := by
    have := G3Aux.isTwistedAct_assembly π Onr Fr vdet k g₀ _ _ (G3Aux.scalar_central _ c) _ _ _ _ hev hev' h3
    rwa [map_mul, map_zpow, hzS]
  have hγ : z ^ c * (γ₀ : (ℍ[ℚ, a₁, b₁])ˣ) ∈ Γt := Γt.mul_mem (Γt.zpow_mem hzΓ c) γ₀.2

  have hcommE : ∀ (γ : ↥Γt) (x : ↥Λ), A₀.act x ≫ e γ = e γ ≫ A₀.act x := by
    intro γ x; obtain ⟨-, -, -, -, ha, -, -⟩ := (hE1 γ).1; exact ha x
  obtain ⟨p, q, hpq⟩ := G3Aux.exists_e_zpow_comp_act_eq hΛℤ e hcommE hE1mul hE1sc z hzΓ hzval c
  obtain ⟨a', b', hab⟩ := G3Aux.exists_e_mul_comp_act_eq hΛℤ e hcommE hE1mul ⟨z ^ c, Γt.zpow_mem hzΓ c⟩ γ₀ p q hpq
  have hsub : (⟨z ^ c, Γt.zpow_mem hzΓ c⟩ * γ₀ : ↥Γt) = ⟨z ^ c * (γ₀ : (ℍ[ℚ, a₁, b₁])ˣ), hγ⟩ := rfl
  rw [hsub] at hab
  have htrγ : FakeEllipticCurve.Rigidification.IsTranslateBy hΛℤ (e ⟨z ^ c * (γ₀ : (ℍ[ℚ, a₁, b₁])ˣ), hγ⟩) ϱ ρ₂ :=
    G3Aux.isTranslateBy_of_comp_act_eq hΛℤ ϱ ρ₂ (e γ₀) (e ⟨_, hγ⟩) (he _) a' b' hab htr
  refine ⟨z ^ c * (γ₀ : (ℍ[ℚ, a₁, b₁])ˣ), hγ, htw, ρ₂, ?_, htrγ, ⟨ib', hib', hibf', uA', huA', huAg', i₁, j₁, hcorr⟩⟩

  rw [hΞeq]; exact ⟨hΞψ', hev'⟩

end

end S_CerednikDrinfeld_QM_FakeEllipticCurve_Rigidification_exists_mem_isTwistedAct_isTranslateBy_corr_of_isoVia_of_isAlgClosed_heightNormalised_eq_oneLeg
end P2MW
export P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_Rigidification_exists_mem_isTwistedAct_isTranslateBy_corr_of_isoVia_of_isAlgClosed_heightNormalised_eq_oneLeg (solution)
