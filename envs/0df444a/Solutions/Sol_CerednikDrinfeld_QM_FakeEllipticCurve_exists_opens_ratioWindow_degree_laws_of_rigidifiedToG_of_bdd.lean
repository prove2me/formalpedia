-- Prove2me | solution 1 for CerednikDrinfeld.QM.FakeEllipticCurve.exists_opens_ratioWindow_degree_laws_of_rigidifiedToG_of_bdd
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.141142+00:00
-- url     : https://prove2.me/submissions/4777bc03-23cd-5c41-a911-181942caf4b5

import Definitions.Def_CerednikDrinfeld_QMCoarseModuli
import Definitions.Def_CerednikDrinfeld_QMFineModuli
import Definitions.Def_CerednikDrinfeld_QMFineModuliT
import Definitions.Def_CerednikDrinfeld_AlgFunctorConst
import Definitions.Def_CerednikDrinfeld_FormalUpperHalfPlaneFunctor
import Definitions.Def_CerednikDrinfeld_FormalUpperHalfPlanePoints
import Definitions.Def_CerednikDrinfeld_SchemeNilpPoints
import Definitions.Def_CerednikDrinfeld_CosetGraphAtPrime
import Definitions.Def_CerednikDrinfeld_HeckeTower
import Definitions.Def_CerednikDrinfeld_ClassSetGraph
import Definitions.Def_CerednikDrinfeld_QMRigidification
import Definitions.Def_CerednikDrinfeld_QMRigidificationLevel
import Definitions.Def_CerednikDrinfeld_SpecialFormalFunctorG
import Mathlib
import Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_Rigidification_finrank_mul_finrank_act_pow_eq_of_corr
import Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_one_lt_finrank_act_pow_of_isFinite_of_flat
import Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_isLocallyConstant_finrank_one
import Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_isFinite_flat_surjective_of_isIsogenyPair
import Theorems.Thm_AlgebraicGeometry_Scheme_Hom_finrank_comp_of_finrank_eq_const
import Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_Rigidification_comp_phi_comp_eq_phi_of_comp_act_pow_eq
import Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_exists_isPullback_levelIff
import Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_FullLevel_exists_comp_eq_specMap_comp_of_isPullbackVia
import Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_Rigidification_exists_isPullbackVia_of_isPullbackVia
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_exists_opens_ratioWindow_degree_laws_of_rigidifiedToG_of_bdd
p2m_attr_erase "instance" "instTopologicallyFGOfFiniteType GoodReductionJacobian.RelativeGroupLaw.isIso_endKerStr_schemeHomOverId AlgebraicGeometry.Scheme.PresheafOfModules.symmetricCategory SheafOfModules.instFaithfulRingSheafPModToPMod SheafOfModules.symmetricCategory AlgebraicGeometry.Scheme.PresheafOfModules.monoidalCategory AlgebraicGeometry.Scheme.PresheafOfModules.monoidalClosed SheafOfModules.instFullRingSheafPModToPMod SheafOfModules.monoidalCategory AlgebraicGeometry.Scheme.Modules.symmetricCategory SheafOfModules.monoidalClosed SheafOfModules.instIsLocalizationPModRingSheafSheafifyFunctorPresheafW SheafOfModules.sheafifyFunctor_monoidal AlgebraicGeometry.Scheme.Modules.monoidalClosed AlgebraicGeometry.instMonoidalPresheafOfModulesModulesSheafify AlgebraicGeometry.Scheme.Modules.monoidalCategory PresheafOfModules.instMonoidalClosed PresheafOfModules.InternalHom.instModuleCarrierObjOppositeCommRingCatSubtypePiFamilyMemAddSubgroupNaturalFamilies PresheafOfModules.InternalHom.instModuleCarrierObjOppositeRingCatCompCommRingCatForget₂RingHomCarrierCarrierAbPresheaf PresheafOfModules.InternalHom.instSMulCarrierObjOppositeCommRingCatSubtypePiFamilyMemAddSubgroupNaturalFamilies AlgebraicGeometry.Scheme.Hom.opensMapFinal AlgebraicGeometry.RelPicard.RigidifiedLineBundle.setoid AlgebraicGeometry.RelPicard.RigidifiedLineBundle.instInhabited AlgebraicGeometry.OModulePresheaf.isScalarTower AlgebraicGeometry.Scheme.OrderedAffineCover.instLinearOrder AlgebraicGeometry.OModulePresheaf.module AlgebraicGeometry.Scheme.OrderedAffineCover.instFintype AlgebraicGeometry.Scheme.OrderedAffineCover.instFintypeIdx AlgebraicGeometry.OModulePresheaf.addCommGroup AlgebraicGeometry.Scheme.OrderedAffineCover.instDecidableEqIdx AlgebraicGeometry.OModulePresheaf.moduleSections TwoChartCech.Sections.M0_moduleA TwoChartCech.Sections.M1_module TwoChartCech.Cover.A01_algebra TwoChartCech.Cover.A0_algebra TwoChartCech.Cover.A1_commRing TwoChartCech.Cover.A1_algebra TwoChartCech.Sections.M01_module TwoChartCech.Sections.M0_addCommGroup TwoChartCech.Sections.M0_tower"
p2m_attr_erase "instance" "TwoChartCech.Sections.M01_addCommGroup TwoChartCech.Cover.A0_commRing TwoChartCech.Sections.M1_tower TwoChartCech.Sections.M01_moduleA TwoChartCech.Sections.M0_module TwoChartCech.Sections.M1_moduleA TwoChartCech.Sections.M1_addCommGroup TwoChartCech.Cover.A01_commRing TwoChartCech.Sections.M01_tower CoherentBaseChange.TwoTermComplex.C0_module CoherentBaseChange.TwoTermComplex.C0_addCommGroup CoherentBaseChange.TwoTermComplex.C1_module CoherentBaseChange.TwoTermComplex.C1_addCommGroup CoherentBaseChange.TwoTermComplex.C0_free CoherentBaseChange.TwoTermComplex.C1_finite CoherentBaseChange.TwoTermComplex.C0_finite CoherentBaseChange.TwoTermComplex.C1_free AlgebraicGeometry.OModulePresheaf.instSubsingletonObjZero AlgebraicGeometry.Scheme.Modules.preservesBinaryProducts_opensMap AlgebraicGeometry.Scheme.Modules.pullback_monoidal AlgebraicGeometry.Scheme.Modules.sheafify_isLocalization' AlgebraicGeometry.Scheme.Modules.preservesTerminal_opensMap AlgebraicGeometry.Scheme.Modules.pullback₀_monoidal AlgebraicGeometry.Scheme.Modules.preservesFiniteProducts_opensMap AlgebraicGeometry.Scheme.Modules.instLiftingPresheafOfModulesSheafifyPresheafWOpensCarrierCarrierCommRingCatGrothendieckTopologyObjFunctorOppositeIsSheafSheafCompPullback₀Pullback PresheafOfModules.PullbackMonoidal.pullback_monoidal PresheafOfModules.PullbackMonoidal.isIso_δ PresheafOfModules.pushforward_laxMonoidal PresheafOfModules.PullbackMonoidal.isIso_η PresheafOfModules.free_monoidal PresheafOfModules.restrictScalars_laxMonoidal PresheafOfModules.PullbackMonoidal.isIso_δ_gS PresheafOfModules.pullback_oplaxMonoidal PresheafOfModules.PullbackMonoidal.instPreservesColimitsOfSizeCompOppositeCommRingCatRingCatForget₂RingHomCarrierCarrierPb PresheafOfModules.pullback_monoidal' AlgebraicGeometry.SmoothOfRelativeDimension.fiberToSpecResidueField AlgebraicGeometry.SmoothOfRelativeDimension.pullback_snd AlgebraicGeometry.SmoothOfRelativeDimension.pullback_fst AlgebraicGeometry.SmoothOfRelativeDimension.smooth_one AlgebraicGeometry.SmoothProperCurve.isIntegral_pullback_Spec_field"
p2m_attr_erase "instance" "AlgebraicGeometry.IsProper.fiberToSpecResidueField AlgebraicCurve.CurveModel.isProper AlgebraicCurve.CurveModel.isIntegral AlgebraicCurve.CurveModel.smooth AlgebraicGeometry.Scheme.LocalRepresentabilityULift.instIsLocallyInjectiveFunUliftYonedaGluedToSheaf AlgebraicGeometry.Scheme.LocalRepresentabilityULift.instIsLocallySurjectiveFunUliftYonedaGluedToSheafOfIsLocallySurjectiveZariskiTopologyDescFunctorOppositeType AlgebraicGeometry.Scheme.LocalRepresentabilityULift.instIsOpenImmersionToGlued AlgebraicGeometry.Scheme.LocalRepresentabilityULift.instIsIsoSheafZariskiTopologyTypeUliftYonedaGluedToSheaf AlgebraicGeometry.RelPicard.instIsOpenImmersionToGlued AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions PresheafOfModules.ExteriorPower.instModulePresheafAb AlgebraicGeometry.RelEffCartierDiv.subsingleton_of_degree_zero AlgebraicGeometry.RelEffCartierDiv.isIso_subschemeIota_snd_of_degree_one AlgebraicGeometry.isIso_ker_graphOver_subschemeIota_snd AlgebraicGeometry.isClosedImmersion_graphOver AlgebraicGeometry.FGSubalgebra.instIsDirectedLe AlgebraicGeometry.FGSubalgebra.instQuasiSeparatedSpaceCarrierCarrierCommRingCatObjOppositeSchemeSpecDiagram AlgebraicGeometry.FGSubalgebra.instIsCofilteredOpposite AlgebraicGeometry.FGSubalgebra.instIsAffineObjOppositeSchemeSpecDiagram AlgebraicGeometry.FGSubalgebra.instNonempty AlgebraicGeometry.FGSubalgebra.instNonemptySubtypeLeSubalgebraValFG AlgebraicGeometry.FGSubalgebra.instCompactSpaceCarrierCarrierCommRingCatObjOppositeSchemeSpecDiagram AlgebraicGeometry.FGSubalgebra.instIsDirectedSubtypeLeSubalgebraValFG AlgebraicGeometry.FGSubalgebra.instIsAffineHomMapOppositeSchemeSpecDiagram AlgebraicGeometry.FGSubalgebra.instIsFiltered AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instNeg AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instSMulInt AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instAddCommGroup AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instAdd AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instSub AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instModuleCarrierObjOppositeOpensCarrierCarrierCommRingCatPresheafOpOpensTop AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instSMulCarrierObjOppositeOpensCarrierCarrierCommRingCatPresheafOpOpensTop AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instSMulNat"
p2m_attr_erase "instance" "AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instZero AlgebraicCurve.instHasLocalResidue_of_hasCanonicalLocalResidueK AlgebraicCurve.instHasCanonicalLocalResidueK_of_hasCanonicalLocalResidueKStar AlgebraicCurve.Place.kw_ffgc_finiteDimensional_adicCompletion instAlgebraSubtypeMemValuationSubring_definitions AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersIntegersCompletion ModularCurve.KwF4gRRTate.instAlgebraKAdicCompletionIntegers AlgebraicCurve.Place.kw_ffgc_continuousSMul_adicCompletionComap AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersCompletionCompletion IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions AlgebraicCurve.instHasCanonicalLocalResidueK AlgebraicCurve.Place.instAlgebra_restrictResidueField AlgebraicCurve.Place.instIsScalarTower_restrictResidueField AlgebraicCurve.instHasLocalResidue AlgebraicCurve.HasSeparableResidue.of_perfectField_of_isCurveOver AlgebraicCurve.HasSeparableResidue.of_perfectField AlgebraicCurve.Place.instIsLocalHom_restrictSubringHom AlgebraicCurve.instHasCanonicalLocalResidueKStar ModularCurve.KwNo6Pin.isLocalRing_completion SheafOfModules.isIso_ihomModelToIhom AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instDecidableEqIdx AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instFintype AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instLinearOrder AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instFintypeIdx AlgebraicGeometry.OModulePresheaf.Leray.relAltC_scalarTower AlgebraicGeometry.OModulePresheaf.Leray.ker_relAltd_modΓ AlgebraicGeometry.OModulePresheaf.Leray.relAltC_modΓ AlgebraicGeometry.OModulePresheaf.Leray.biC_abGrp AlgebraicGeometry.OModulePresheaf.Leray.relAltH_modΓ AlgebraicGeometry.OModulePresheaf.Leray.ker_relAltd_smul AlgebraicGeometry.OModulePresheaf.Leray.relAltH_scalarTower AlgebraicGeometry.OModulePresheaf.Leray.relAltH_smul AlgebraicGeometry.OModulePresheaf.Leray.biC_module DoubleComplex.instModuleE₂I DoubleComplex.Bounded.modR"
p2m_attr_erase "instance" "DoubleComplex.instModuleE₂II DoubleComplex.instAddCommGroupE₂II DoubleComplex.Bounded.abGrp DoubleComplex.instAddCommGroupE₂I AlgebraicGeometry.ChowDatum.hι_closed AlgebraicGeometry.ChowDatumProj.hιN_closed AlgebraicGeometry.ChowDatumProj.hp_proper AlgebraicGeometry.ChowDatum.hp_isoU AlgebraicGeometry.ChowDatum.hp_proper AlgebraicGeometry.ProjSpace.algebraAway AlgebraicGeometry.ProjSpace.instIsProperProdOverπ AlgebraicGeometry.ChowDatumProj.hp_isoU AlgebraicGeometry.ProjSpace.isProper_π AlgebraicGeometry.ProjSpace.finiteType_mvPolynomial ProjSpaceCech.GradedModule.H.module ProjSpaceCech.GradedModule.H.addCommGroup ProjSpaceCech.GradedModule.sec.instAdd ProjSpaceCech.GradedModule.sec.instNeg ProjSpaceCech.GradedModule.acg ProjSpaceCech.GradedModule.Frac.setoid ProjSpaceCech.GradedModule.modR ProjSpaceCech.GradedModule.sec.instModule ProjSpaceCech.GradedModule.sec.instAddCommGroup ProjSpaceCech.GradedModule.sec.instZero ProjSpaceCech.GradedModule.Presentation.fJ ProjSpaceCech.GradedModule.sec.instSMul ProjSpaceCech.Twist.H.module ProjSpaceCech.Idx.instFintype ProjSpaceCech.Twist.H.addCommGroup ProjSpaceCech.Idx.instDecidableEq ProjSpaceCech.Twist.Mon.instDecidableEq ProjSpaceCech.Twist.cochain.instAddCommGroup ProjSpaceCech.Twist.cochain.instModule AlgebraicGeometry.FGSubalgebra.tensorStage_directedSystem AlgebraicGeometry.RelEffCartierDiv.isClosedImmersion_subschemeι_resProdMap AlgebraicGeometry.RelEffCartierDiv.isOpenImmersion_resProdMap AlgebraicCurve.CurveModel.locallyOfFiniteType_gluedToBase AlgebraicCurve.CurveModel.isFractionRing_overlap AlgebraicCurve.CurveModel.isLocallyNoetherian_glued AlgebraicCurve.CurveModel.jacobsonSpace_glued"
p2m_attr_erase "instance" "AlgebraicCurve.CurveModel.isOpenImmersion_ι₀ AlgebraicCurve.CurveModel.isIntegral_glued AlgebraicCurve.CurveModel.quasiSeparated_gluedToBase AlgebraicCurve.CurveModel.compactSpace_glued AlgebraicCurve.CurveModel.isIntegral_adjoin_chartRing AlgebraicCurve.CurveModel.isFractionRing_overlap_functionField AlgebraicCurve.CurveModel.isProper_gluedToBase AlgebraicCurve.CurveModel.isOpenImmersion_ιU AlgebraicCurve.CurveModel.isOpenImmersion_f₀ AlgebraicCurve.CurveModel.isOpenImmersion_fInf AlgebraicCurve.CurveModel.isOpenImmersion_ιInf AlgebraicCurve.CurveModel.algebra_overlap_functionField AlgebraicCurve.CurveModel.quasiCompact_gluedToBase AlgebraicCurve.CurveModel.algebraAdjoin AlgebraicCurve.CurveModel.isDedekindDomain_chartRing AlgebraicCurve.CurveModel.isIntegralClosure AlgebraicCurve.CurveModel.finite_chartRing AlgebraicCurve.CurveModel.centre_isPrime AlgebraicCurve.CurveModel.isFractionRing_chartRing AlgebraicCurve.CurveModel.finiteType_chartRing AlgebraicCurve.CurveModel.isNoetherianRing_chartRing AlgebraicCurve.CurveModel.isScalarTower_base_adjoin AlgebraicCurve.CurveModel.isScalarTower_adjoin AlgebraicCurve.CurveModel.chartRing_finitePresentation AlgebraicGeometry.ProjSpace.twistObj.addCommGroup AlgebraicGeometry.ProjSpace.twistFam.module AlgebraicGeometry.ProjSpace.twistObj.module AlgebraicGeometry.ProjSpace.twistObj.moduleSections AlgebraicGeometry.ProjSpace.twistFam.addCommGroup"
p2m_attr_erase "simp" "RegularLocalRingQuotientAscent.dualNumberFst_apply GoodReductionJacobian.RelativeGroupLaw.fibre_inv GoodReductionJacobian.RelativeGroupLaw.fibrePointToBase_coe GoodReductionJacobian.RelativeGroupLaw.fibrePointOfBase_toBase GoodReductionJacobian.RelativeGroupLaw.fibre_mul GoodReductionJacobian.RelativeGroupLaw.fibrePointToBase_ofBase GoodReductionJacobian.RelativeGroupLaw.fibre_one GoodReductionJacobian.RelativeGroupLaw.fibrePointOfBase_coe GoodReductionJacobian.RelativeGroupLaw.nsmul_zero GoodReductionJacobian.RelativeGroupLaw.mem_torsionSubset GoodReductionJacobian.RelativeGroupLaw.nsmul_succ GoodReductionJacobian.RelativeGroupLaw.baseChangePointToBase_ofBase GoodReductionJacobian.RelativeGroupLaw.baseChangePointToBase_coe GoodReductionJacobian.RelativeGroupLaw.baseChangePointOfBase_coe GoodReductionJacobian.RelativeGroupLaw.baseChange_inv GoodReductionJacobian.RelativeGroupLaw.baseChangePointOfBase_toBase GoodReductionJacobian.RelativeGroupLaw.baseChange_mul GoodReductionJacobian.RelativeGroupLaw.baseChange_one NeronModelInfra.NeronModelPropertyBundle.endExtensionEquiv_symm_restrict NeronModelInfra.schemeHomOverComp_id_left NeronModelInfra.schemeHomOverComp_id_right NeronModelInfra.schemeHomOverId_coe NeronModelInfra.NeronModelPropertyBundle.endExtensionEquiv_apply NeronModelInfra.NeronModelPropertyBundle.restrict_endExtensionEquiv_symm NeronModelInfra.schemeHomOverComp_coe NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_fst NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_snd NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_fst NeronSpecialFibreInfra.neronEndRestrictEquiv_apply NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_fst_assoc NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_snd NeronSpecialFibreInfra.neronEndExtension_genericFibreRestrict NeronSpecialFibreInfra.specClosedFibreInclusion_eq NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_fst_assoc NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_snd_assoc NeronSpecialFibreInfra.genericFibreRestrict_neronEndExtension NeronSpecialFibreInfra.homOverId_coe NeronSpecialFibreInfra.homOverComp_coe NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_snd_assoc NeronModelInfra.schemeHomOverNpow_succ"
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

open scoped TensorProduct Quaternion NumberField
p2m_open "CategoryTheory AlgebraicGeometry QuaternionAlgebra IsDedekindDomain CerednikDrinfeld P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_exists_opens_ratioWindow_degree_laws_of_rigidifiedToG_of_bdd.CerednikDrinfeld CerednikDrinfeld.QM P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_exists_opens_ratioWindow_degree_laws_of_rigidifiedToG_of_bdd.CerednikDrinfeld.QM CerednikDrinfeld.FormalOmega CerednikDrinfeld.SpecialFormal NeronModelInfra~schemeHomOverComp_coe GoodReductionJacobian"

open LT.LatticeTree (FullLattice)

namespace Ws16WC

namespace Clopen

open Set Topology

variable {X : Type*} {Y : Type*} [TopologicalSpace X]

theorem isClopen_preimage {f : X → Y} (hf : IsLocallyConstant f) (s : Set Y) : IsClopen (f ⁻¹' s) := by
  refine ⟨?_, hf s⟩
  rw [← isOpen_compl_iff, ← Set.preimage_compl]
  exact hf sᶜ

theorem isClopen_setOf_eq {f g : X → Y} (hf : IsLocallyConstant f) (hg : IsLocallyConstant g) :
    IsClopen {x | f x = g x} := by
  have hfib : ∀ y, IsOpen {x | f x = y} := fun y => (hf.isClopen_fiber y).isOpen
  have hgib : ∀ y, IsOpen {x | g x = y} := fun y => (hg.isClopen_fiber y).isOpen
  refine ⟨?_, ?_⟩
  · rw [← isOpen_compl_iff]
    have : {x | f x = g x}ᶜ = ⋃ y, ({x | f x = y} ∩ (g ⁻¹' ({y}ᶜ))) := by
      ext x
      simp only [mem_compl_iff, mem_setOf_eq, mem_iUnion, mem_inter_iff, mem_preimage, mem_singleton_iff]
      exact ⟨fun h => ⟨f x, rfl, fun h' => h h'.symm⟩, fun ⟨y, hy, hy'⟩ h => hy' (h ▸ hy)⟩
    rw [this]
    exact isOpen_iUnion fun y => (hfib y).inter (hg _)
  · have : {x | f x = g x} = ⋃ y, ({x | f x = y} ∩ {x | g x = y}) := by
      ext x
      simp only [mem_setOf_eq, mem_iUnion, mem_inter_iff]
      exact ⟨fun h => ⟨g x, h, rfl⟩, fun ⟨y, hy, hy'⟩ => hy.trans hy'.symm⟩
    rw [this]
    exact isOpen_iUnion fun y => (hfib y).inter (hgib y)

theorem isOpen_setOf_eq {f g : X → Y} (hf : IsLocallyConstant f) (hg : IsLocallyConstant g) :
    IsOpen {x | f x = g x} := (isClopen_setOf_eq hf hg).isOpen

theorem isClosed_setOf_eq {f g : X → Y} (hf : IsLocallyConstant f) (hg : IsLocallyConstant g) :
    IsClosed {x | f x = g x} := (isClopen_setOf_eq hf hg).isClosed

theorem isOpen_setOf_eq_inter {f g : X → Y} (hf : IsLocallyConstant f) (hg : IsLocallyConstant g)
    {V : Set X} (hV : IsOpen V) : IsOpen ({x | f x = g x} ∩ V) :=
  (isOpen_setOf_eq hf hg).inter hV

theorem isOpen_setOf_eq_inter_preimage {Z : Type*} [TopologicalSpace Z] {f g : X → Y}
    (hf : IsLocallyConstant f) (hg : IsLocallyConstant g) {θ : X → Z} (hθ : Continuous θ)
    {V : Set Z} (hV : IsOpen V) : IsOpen ({x | f x = g x} ∩ θ ⁻¹' V) :=
  (isOpen_setOf_eq hf hg).inter (hV.preimage hθ)

theorem isClopen_setOf_mem {f : X → Y} (hf : IsLocallyConstant f) (S : Set Y) :
    IsClopen {x | f x ∈ S} := isClopen_preimage hf S

theorem isClopen_of_cover {ι : Type*} (U : ι → Set X) (hU : ∀ x, ∃ i, x ∈ U i)
    (Z : Set X) (h₁ : ∀ i, IsOpen (Z ∩ U i)) (h₂ : ∀ i, IsOpen (Zᶜ ∩ U i)) : IsClopen Z := by
  have cover : ∀ W : Set X, W = ⋃ i, (W ∩ U i) := fun W => by
    ext x
    simp only [mem_iUnion, mem_inter_iff]
    exact ⟨fun hx => (hU x).imp fun i hi => ⟨hx, hi⟩, fun ⟨i, hx, _⟩ => hx⟩
  refine ⟨?_, ?_⟩
  · rw [← isOpen_compl_iff, cover Zᶜ]
    exact isOpen_iUnion h₂
  · rw [cover Z]
    exact isOpen_iUnion h₁

theorem isClopen_of_locallyConstant_cover {ι : Type*} (U : ι → Set X) (hUo : ∀ i, IsOpen (U i))
    (hU : ∀ x, ∃ i, x ∈ U i) (Z : Set X)
    (f g : ∀ i, U i → Y) (hf : ∀ i, IsLocallyConstant (f i)) (hg : ∀ i, IsLocallyConstant (g i))
    (hZ : ∀ (i) (x : U i), (x : X) ∈ Z ↔ f i x = g i x) : IsClopen Z := by
  refine isClopen_of_cover U hU Z (fun i => ?_) (fun i => ?_)
  · have : Z ∩ U i = Subtype.val '' {x : U i | f i x = g i x} := by
      ext x
      simp only [mem_inter_iff, mem_image, mem_setOf_eq]
      exact ⟨fun ⟨hz, hu⟩ => ⟨⟨x, hu⟩, (hZ i ⟨x, hu⟩).1 hz, rfl⟩,
        fun ⟨y, hy, hyx⟩ => hyx ▸ ⟨(hZ i y).2 hy, y.2⟩⟩
    rw [this]
    exact (hUo i).isOpenMap_subtype_val _ (isOpen_setOf_eq (hf i) (hg i))
  · have : Zᶜ ∩ U i = Subtype.val '' {x : U i | f i x = g i x}ᶜ := by
      ext x
      simp only [mem_inter_iff, mem_compl_iff, mem_image, mem_setOf_eq]
      exact ⟨fun ⟨hz, hu⟩ => ⟨⟨x, hu⟩, fun h => hz ((hZ i ⟨x, hu⟩).2 h), rfl⟩,
        fun ⟨y, hy, hyx⟩ => hyx ▸ ⟨fun h => hy ((hZ i y).1 h), y.2⟩⟩
    rw [this]
    exact (hUo i).isOpenMap_subtype_val _ (isClosed_setOf_eq (hf i) (hg i)).isOpen_compl

theorem eq_of_preconnectedSpace [PreconnectedSpace X] {f g : X → Y} (hf : IsLocallyConstant f)
    (hg : IsLocallyConstant g) {x₀ : X} (h : f x₀ = g x₀) (x : X) : f x = g x := by
  rw [hf.apply_eq_of_preconnectedSpace x x₀, hg.apply_eq_of_preconnectedSpace x x₀, h]

end Clopen

namespace Clopen
open CategoryTheory AlgebraicGeometry

def balancedOpens (X : Scheme) {Y : Type*} (f g : X → Y) (hf : IsLocallyConstant f)
    (hg : IsLocallyConstant g) (V : X.Opens) : X.Opens :=
  ⟨{x | f x = g x} ∩ (V : Set X), isOpen_setOf_eq_inter hf hg V.isOpen⟩

theorem mem_balancedOpens (X : Scheme) {Y : Type*} (f g : X → Y) (hf : IsLocallyConstant f)
    (hg : IsLocallyConstant g) (V : X.Opens) (x : X) :
    x ∈ balancedOpens X f g hf hg V ↔ f x = g x ∧ x ∈ V := Iff.rfl

theorem isOpenImmersion_balancedOpens_ι (X : Scheme) {Y : Type*} (f g : X → Y) (hf : IsLocallyConstant f)
    (hg : IsLocallyConstant g) (V : X.Opens) : IsOpenImmersion (balancedOpens X f g hf hg V).ι :=
  inferInstance

def coincidenceOpens (X : Scheme) {Y : Type*} (f g : X → Y) (hf : IsLocallyConstant f)
    (hg : IsLocallyConstant g) : X.Opens :=
  ⟨{x | f x = g x}, isOpen_setOf_eq hf hg⟩

theorem isClopen_coincidenceOpens (X : Scheme) {Y : Type*} (f g : X → Y) (hf : IsLocallyConstant f)
    (hg : IsLocallyConstant g) : IsClopen ((coincidenceOpens X f g hf hg : X.Opens) : Set X) :=
  isClopen_setOf_eq hf hg

theorem isClopen_of_openCover (X : Scheme) (𝒰 : X.OpenCover) {Y : Type*} (Z : Set X)
    (f g : ∀ j : 𝒰.I₀, ↥(𝒰.X j) → Y)
    (hf : ∀ j, IsLocallyConstant (f j)) (hg : ∀ j, IsLocallyConstant (g j))
    (hZ : ∀ (j) (u : ↥(𝒰.X j)), (𝒰.f j).base u ∈ Z ↔ f j u = g j u) : IsClopen Z := by
  refine isClopen_of_cover (fun j : 𝒰.I₀ => Set.range (𝒰.f j).base) (fun x => ⟨𝒰.idx x, 𝒰.covers x⟩) Z
    (fun j => ?_) (fun j => ?_)
  · have : Z ∩ Set.range (𝒰.f j).base = (𝒰.f j).base '' {u | f j u = g j u} := by
      ext x
      simp only [Set.mem_inter_iff, Set.mem_range, Set.mem_image, Set.mem_setOf_eq]
      exact ⟨fun ⟨hz, u, hu⟩ => ⟨u, (hZ j u).1 (hu ▸ hz), hu⟩, fun ⟨u, hu, hux⟩ => ⟨hux ▸ (hZ j u).2 hu, u, hux⟩⟩
    rw [this]
    exact (𝒰.f j).isOpenEmbedding.isOpenMap _ (isOpen_setOf_eq (hf j) (hg j))
  · have : Zᶜ ∩ Set.range (𝒰.f j).base = (𝒰.f j).base '' {u | f j u = g j u}ᶜ := by
      ext x
      simp only [Set.mem_inter_iff, Set.mem_compl_iff, Set.mem_range, Set.mem_image, Set.mem_setOf_eq]
      exact ⟨fun ⟨hz, u, hu⟩ => ⟨u, fun h => hz (hu ▸ (hZ j u).2 h), hu⟩,
        fun ⟨u, hu, hux⟩ => ⟨fun h => hu ((hZ j u).1 (hux ▸ h)), u, hux⟩⟩
    rw [this]
    exact (𝒰.f j).isOpenEmbedding.isOpenMap _ (isClosed_setOf_eq (hf j) (hg j)).isOpen_compl

def opensOfClopen (X : Scheme) (Z : Set X) (hZ : IsClopen Z) : X.Opens := ⟨Z, hZ.isOpen⟩

@[scoped simp] theorem coe_opensOfClopen (X : Scheme) (Z : Set X) (hZ : IsClopen Z) :
    ((opensOfClopen X Z hZ : X.Opens) : Set X) = Z := rfl

theorem mem_opensOfClopen (X : Scheme) (Z : Set X) (hZ : IsClopen Z) (x : X) :
    x ∈ opensOfClopen X Z hZ ↔ x ∈ Z := Iff.rfl

theorem isClosed_opensOfClopen (X : Scheme) (Z : Set X) (hZ : IsClopen Z) :
    IsClosed ((opensOfClopen X Z hZ : X.Opens) : Set X) := hZ.isClosed

def balancedOpensOfOpenCover (X : Scheme) (𝒰 : X.OpenCover) {Y : Type*} (Z : Set X)
    (f g : ∀ j : 𝒰.I₀, ↥(𝒰.X j) → Y)
    (hf : ∀ j, IsLocallyConstant (f j)) (hg : ∀ j, IsLocallyConstant (g j))
    (hZ : ∀ (j) (u : ↥(𝒰.X j)), (𝒰.f j).base u ∈ Z ↔ f j u = g j u) : X.Opens :=
  opensOfClopen X Z (isClopen_of_openCover X 𝒰 Z f g hf hg hZ)

theorem coe_balancedOpensOfOpenCover (X : Scheme) (𝒰 : X.OpenCover) {Y : Type*} (Z : Set X)
    (f g : ∀ j : 𝒰.I₀, ↥(𝒰.X j) → Y)
    (hf : ∀ j, IsLocallyConstant (f j)) (hg : ∀ j, IsLocallyConstant (g j))
    (hZ : ∀ (j) (u : ↥(𝒰.X j)), (𝒰.f j).base u ∈ Z ↔ f j u = g j u) :
    ((balancedOpensOfOpenCover X 𝒰 Z f g hf hg hZ : X.Opens) : Set X) = Z := rfl

theorem mem_balancedOpensOfOpenCover (X : Scheme) (𝒰 : X.OpenCover) {Y : Type*} (Z : Set X)
    (f g : ∀ j : 𝒰.I₀, ↥(𝒰.X j) → Y)
    (hf : ∀ j, IsLocallyConstant (f j)) (hg : ∀ j, IsLocallyConstant (g j))
    (hZ : ∀ (j) (u : ↥(𝒰.X j)), (𝒰.f j).base u ∈ Z ↔ f j u = g j u) (j : 𝒰.I₀) (u : ↥(𝒰.X j)) :
    (𝒰.f j).base u ∈ balancedOpensOfOpenCover X 𝒰 Z f g hf hg hZ ↔ f j u = g j u := hZ j u

theorem isClosed_balancedOpensOfOpenCover (X : Scheme) (𝒰 : X.OpenCover) {Y : Type*} (Z : Set X)
    (f g : ∀ j : 𝒰.I₀, ↥(𝒰.X j) → Y)
    (hf : ∀ j, IsLocallyConstant (f j)) (hg : ∀ j, IsLocallyConstant (g j))
    (hZ : ∀ (j) (u : ↥(𝒰.X j)), (𝒰.f j).base u ∈ Z ↔ f j u = g j u) :
    IsClosed ((balancedOpensOfOpenCover X 𝒰 Z f g hf hg hZ : X.Opens) : Set X) :=
  (isClopen_of_openCover X 𝒰 Z f g hf hg hZ).isClosed

theorem isClosed_coincidenceOpens (X : Scheme) {Y : Type*} (f g : X → Y) (hf : IsLocallyConstant f)
    (hg : IsLocallyConstant g) : IsClosed ((coincidenceOpens X f g hf hg : X.Opens) : Set X) :=
  isClosed_setOf_eq hf hg

theorem mem_coincidenceOpens (X : Scheme) {Y : Type*} (f g : X → Y) (hf : IsLocallyConstant f)
    (hg : IsLocallyConstant g) (x : X) : x ∈ coincidenceOpens X f g hf hg ↔ f x = g x := Iff.rfl

end Clopen
p2m_reactivate "P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_exists_opens_ratioWindow_degree_laws_of_rigidifiedToG_of_bdd.Ws16WC.Clopen"

namespace Arith

theorem pow_right_injective' {r : ℕ} (hr : 1 < r) {m n : ℕ} (h : r ^ m = r ^ n) : m = n :=
  Nat.pow_right_injective (le_refl _ |>.trans hr) h

theorem eq_pow_two_mul_of_balanced {r d e e' : ℕ} (hpair : e * e' = r ^ (4 * d)) (hbal : e = e') :
    e = r ^ (2 * d) := by
  subst hbal
  have h : e * e = r ^ (2 * d) * r ^ (2 * d) := by rw [hpair, ← pow_add]; ring_nf
  exact Nat.mul_self_inj.mp h

theorem pad_injective {r e a a' : ℕ} (hr : 1 < r) (he : e ≠ 0)
    (h : e * r ^ (4 * a) = e * r ^ (4 * a')) : a = a' := by
  have h' : r ^ (4 * a) = r ^ (4 * a') := Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero he) h
  have := pow_right_injective' hr h'
  omega

theorem pad_eq_of_balanced {r d : ℕ} (hr : 1 < r) {e e' e₁ e₁' a b a' b' : ℕ}
    (hpair : e * e' = r ^ (4 * d)) (hbal : e = e') (hpair₁ : e₁ * e₁' = r ^ (4 * d)) (hbal₁ : e₁ = e₁')
    (hφ : e * r ^ (4 * a) = e₁ * r ^ (4 * a')) (hφ' : e' * r ^ (4 * b) = e₁' * r ^ (4 * b')) :
    a = a' ∧ b = b' := by
  have he : e = r ^ (2 * d) := eq_pow_two_mul_of_balanced hpair hbal
  have he₁ : e₁ = r ^ (2 * d) := eq_pow_two_mul_of_balanced hpair₁ hbal₁
  have hne : r ^ (2 * d) ≠ 0 := pow_ne_zero _ (by omega)
  subst hbal hbal₁
  rw [he] at hφ hφ'; rw [he₁] at hφ hφ'
  exact ⟨pad_injective hr hne hφ, pad_injective hr hne hφ'⟩

theorem even_add_of_balanced {r d d₁ : ℕ} (hr : 1 < r) {e e' e₁ e₁' a a' : ℕ}
    (hpair : e * e' = r ^ (4 * d)) (hbal : e = e') (hpair₁ : e₁ * e₁' = r ^ (4 * d₁)) (hbal₁ : e₁ = e₁')
    (hφ : e * r ^ (4 * a) = e₁ * r ^ (4 * a')) :
    Even (d + d₁) := by
  have he : e = r ^ (2 * d) := eq_pow_two_mul_of_balanced hpair hbal
  have he₁ : e₁ = r ^ (2 * d₁) := eq_pow_two_mul_of_balanced hpair₁ hbal₁
  rw [he, he₁, ← pow_add, ← pow_add] at hφ
  have := pow_right_injective' hr hφ
  exact ⟨d₁ + a' - a, by omega⟩

theorem exponent_eq_of_balanced_of_window {r d d₁ D : ℕ} (hr : 1 < r) {e e' e₁ e₁' a a' : ℕ}
    (hpair : e * e' = r ^ (4 * d)) (hbal : e = e') (hpair₁ : e₁ * e₁' = r ^ (4 * d₁)) (hbal₁ : e₁ = e₁')
    (hφ : e * r ^ (4 * a) = e₁ * r ^ (4 * a'))
    (hd : d = D ∨ d = D + 1) (hd₁ : d₁ = D ∨ d₁ = D + 1) : d = d₁ := by
  have hev := even_add_of_balanced hr hpair hbal hpair₁ hbal₁ hφ
  obtain ⟨k, hk⟩ := hev
  omega

theorem eq_of_balanced_of_window {r d d₁ D : ℕ} (hr : 1 < r) {e e' e₁ e₁' a b a' b' : ℕ}
    (hpair : e * e' = r ^ (4 * d)) (hbal : e = e') (hpair₁ : e₁ * e₁' = r ^ (4 * d₁)) (hbal₁ : e₁ = e₁')
    (hφ : e * r ^ (4 * a) = e₁ * r ^ (4 * a')) (hφ' : e' * r ^ (4 * b) = e₁' * r ^ (4 * b'))
    (hd : d = D ∨ d = D + 1) (hd₁ : d₁ = D ∨ d₁ = D + 1) : d = d₁ ∧ a = a' ∧ b = b' := by
  have hdd := exponent_eq_of_balanced_of_window hr hpair hbal hpair₁ hbal₁ hφ hd hd₁
  subst hdd
  exact ⟨rfl, pad_eq_of_balanced hr hpair hbal hpair₁ hbal₁ hφ hφ'⟩

theorem pad_eq_of_balanced_exp {d α β α₁ β₁ a b a' b' : ℕ}
    (hpair : α + β = 4 * d) (hbal : α = β) (hpair₁ : α₁ + β₁ = 4 * d) (hbal₁ : α₁ = β₁)
    (hφ : α + 4 * a = α₁ + 4 * a') (hφ' : β + 4 * b = β₁ + 4 * b') : a = a' ∧ b = b' := by
  omega

theorem eq_of_balanced_of_window_exp {d d₁ D α β α₁ β₁ a b a' b' : ℕ}
    (hpair : α + β = 4 * d) (hbal : α = β) (hpair₁ : α₁ + β₁ = 4 * d₁) (hbal₁ : α₁ = β₁)
    (hφ : α + 4 * a = α₁ + 4 * a') (hφ' : β + 4 * b = β₁ + 4 * b')
    (hd : d = D ∨ d = D + 1) (hd₁ : d₁ = D ∨ d₁ = D + 1) : d = d₁ ∧ a = a' ∧ b = b' := by
  omega

theorem exists_balanced_pad_exp {d α β : ℕ} (hpair : α + β = 4 * d) (hα : Even α) :
    ∃ a b : ℕ, α + 4 * a = β + 4 * b ∧ d + a + b ≤ 2 * d ∧ (a = 0 ∨ b = 0) := by
  obtain ⟨i, hi⟩ := hα
  rcases le_total α β with h | h
  · refine ⟨(β - α) / 4, 0, ?_, ?_, Or.inr rfl⟩ <;> omega
  · refine ⟨0, (α - β) / 4, ?_, ?_, Or.inl rfl⟩ <;> omega

theorem exists_window_of_le {d₀ D : ℕ} (h : d₀ ≤ D) : ∃ k : ℕ, d₀ + 2 * k = D ∨ d₀ + 2 * k = D + 1 := by
  refine ⟨(D + 1 - d₀) / 2, ?_⟩
  omega

theorem pair_pad_pad {r d₀ k e e' : ℕ} (hpair : e * e' = r ^ (4 * d₀)) :
    (e * r ^ (4 * k)) * (e' * r ^ (4 * k)) = r ^ (4 * (d₀ + 2 * k)) := by
  rw [mul_mul_mul_comm, hpair, ← pow_add, ← pow_add]
  ring_nf

end Arith
p2m_reactivate "P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_exists_opens_ratioWindow_degree_laws_of_rigidifiedToG_of_bdd.Ws16WC.Clopen"

namespace FEC

open scoped TensorProduct Quaternion NumberField
p2m_open "CategoryTheory AlgebraicGeometry CerednikDrinfeld P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_exists_opens_ratioWindow_degree_laws_of_rigidifiedToG_of_bdd.CerednikDrinfeld CerednikDrinfeld.QM P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_exists_opens_ratioWindow_degree_laws_of_rigidifiedToG_of_bdd.CerednikDrinfeld.QM"

variable {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} {N : ℕ}

noncomputable def degOnBase (S : Type) [CommRing S] (E A : FakeEllipticCurve Λ N S) (φ : E.A ⟶ A.A) :
    ↥(Spec (CommRingCat.of S)) → ℕ :=
  fun s => φ.finrank ((A.L.one (𝟙 (Spec (CommRingCat.of S)))).1.base s)

theorem degOnBase_apply (S : Type) [CommRing S] (E A : FakeEllipticCurve Λ N S) (φ : E.A ⟶ A.A)
    (s : ↥(Spec (CommRingCat.of S))) :
    degOnBase S E A φ s = φ.finrank ((A.L.one (𝟙 (Spec (CommRingCat.of S)))).1.base s) := rfl

theorem isLocallyConstant_degOnBase (S : Type) [CommRing S] (E A : FakeEllipticCurve Λ N S)
    (φ : E.A ⟶ A.A) [IsFinite φ] [Flat φ] [LocallyOfFinitePresentation φ] :
    IsLocallyConstant (degOnBase S E A φ) :=
  (Scheme.Hom.isLocallyConstant_finrank φ).comp_continuous
    (A.L.one (𝟙 (Spec (CommRingCat.of S)))).1.continuous

theorem isLocallyConstant_degOnBase' (S : Type) [CommRing S] (E A : FakeEllipticCurve Λ N S)
    (φ : E.A ⟶ A.A) (h : IsFinite φ ∧ Flat φ ∧ LocallyOfFinitePresentation φ ∧ Surjective φ) :
    IsLocallyConstant (degOnBase S E A φ) := by
  obtain ⟨h1, h2, h3, _⟩ := h
  exact isLocallyConstant_degOnBase S E A φ

theorem isClopen_balanced (S : Type) [CommRing S] (E A : FakeEllipticCurve Λ N S)
    (φ : E.A ⟶ A.A) (φ' : A.A ⟶ E.A) [IsFinite φ] [Flat φ] [LocallyOfFinitePresentation φ]
    [IsFinite φ'] [Flat φ'] [LocallyOfFinitePresentation φ'] :
    IsClopen {s : ↥(Spec (CommRingCat.of S)) | degOnBase S E A φ s = degOnBase S A E φ' s} :=
  Clopen.isClopen_setOf_eq (isLocallyConstant_degOnBase S E A φ) (isLocallyConstant_degOnBase S A E φ')

noncomputable def balancedLocus (S : Type) [CommRing S] (E A : FakeEllipticCurve Λ N S)
    (φ : E.A ⟶ A.A) (φ' : A.A ⟶ E.A) [IsFinite φ] [Flat φ] [LocallyOfFinitePresentation φ]
    [IsFinite φ'] [Flat φ'] [LocallyOfFinitePresentation φ'] : (Spec (CommRingCat.of S)).Opens :=
  Clopen.opensOfClopen _ _ (isClopen_balanced S E A φ φ')

theorem mem_balancedLocus (S : Type) [CommRing S] (E A : FakeEllipticCurve Λ N S)
    (φ : E.A ⟶ A.A) (φ' : A.A ⟶ E.A) [IsFinite φ] [Flat φ] [LocallyOfFinitePresentation φ]
    [IsFinite φ'] [Flat φ'] [LocallyOfFinitePresentation φ'] (s : ↥(Spec (CommRingCat.of S))) :
    s ∈ balancedLocus S E A φ φ' ↔
      φ.finrank ((A.L.one (𝟙 (Spec (CommRingCat.of S)))).1.base s) =
        φ'.finrank ((E.L.one (𝟙 (Spec (CommRingCat.of S)))).1.base s) := Iff.rfl

theorem isClosed_balancedLocus (S : Type) [CommRing S] (E A : FakeEllipticCurve Λ N S)
    (φ : E.A ⟶ A.A) (φ' : A.A ⟶ E.A) [IsFinite φ] [Flat φ] [LocallyOfFinitePresentation φ]
    [IsFinite φ'] [Flat φ'] [LocallyOfFinitePresentation φ'] :
    IsClosed (balancedLocus S E A φ φ' : Set ↥(Spec (CommRingCat.of S))) :=
  (isClopen_balanced S E A φ φ').isClosed

theorem degOnBase_eq_of_preconnectedSpace (S : Type) [CommRing S] (E A : FakeEllipticCurve Λ N S)
    (φ : E.A ⟶ A.A) [IsFinite φ] [Flat φ] [LocallyOfFinitePresentation φ]
    [PreconnectedSpace ↥(Spec (CommRingCat.of S))] (s s₀ : ↥(Spec (CommRingCat.of S))) :
    degOnBase S E A φ s = degOnBase S E A φ s₀ :=
  (isLocallyConstant_degOnBase S E A φ).apply_eq_of_preconnectedSpace s s₀

end FEC
p2m_reactivate "P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_exists_opens_ratioWindow_degree_laws_of_rigidifiedToG_of_bdd.Ws16WC.Clopen"

namespace Clopen

open Set Topology

variable {X : Type*} [TopologicalSpace X]

theorem isClopen_setOf_pred₁ {Y₁ : Type*} {f : X → Y₁} (hf : IsLocallyConstant f) (P : Y₁ → Prop) :
    IsClopen {x | P (f x)} :=
  isClopen_preimage hf {p | P p}

theorem isClopen_setOf_pred₂ {Y₁ Y₂ : Type*} {f : X → Y₁} {g : X → Y₂} (hf : IsLocallyConstant f)
    (hg : IsLocallyConstant g) (P : Y₁ → Y₂ → Prop) : IsClopen {x | P (f x) (g x)} :=
  isClopen_preimage (hf.prodMk hg) {p | P p.1 p.2}

theorem isClopen_setOf_pred₃ {Y₁ Y₂ Y₃ : Type*} {f : X → Y₁} {g : X → Y₂} {h : X → Y₃}
    (hf : IsLocallyConstant f) (hg : IsLocallyConstant g) (hh : IsLocallyConstant h)
    (P : Y₁ → Y₂ → Y₃ → Prop) : IsClopen {x | P (f x) (g x) (h x)} :=
  isClopen_preimage (hf.prodMk (hg.prodMk hh)) {p | P p.1 p.2.1 p.2.2}

theorem isClopen_ratioWindow {f g c : X → ℕ} (hf : IsLocallyConstant f) (hg : IsLocallyConstant g)
    (hc : IsLocallyConstant c) (w : ℕ) : IsClopen {x | f x ≤ g x ∧ g x < c x ^ w * f x} :=
  isClopen_setOf_pred₃ hf hg hc (fun p q s => p ≤ q ∧ q < s ^ w * p)

theorem isOpen_ratioWindow_inter {f g c : X → ℕ} (hf : IsLocallyConstant f) (hg : IsLocallyConstant g)
    (hc : IsLocallyConstant c) (w : ℕ) {V : Set X} (hV : IsOpen V) :
    IsOpen ({x | f x ≤ g x ∧ g x < c x ^ w * f x} ∩ V) :=
  (isClopen_ratioWindow hf hg hc w).isOpen.inter hV

end Clopen
p2m_reactivate "P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_exists_opens_ratioWindow_degree_laws_of_rigidifiedToG_of_bdd.Ws16WC.Clopen"

namespace Clopen
open CategoryTheory AlgebraicGeometry

def ratioWindowOpens (X : Scheme) (f g c : X → ℕ) (hf : IsLocallyConstant f) (hg : IsLocallyConstant g)
    (hc : IsLocallyConstant c) (w : ℕ) : X.Opens :=
  opensOfClopen X _ (isClopen_ratioWindow hf hg hc w)

theorem mem_ratioWindowOpens (X : Scheme) (f g c : X → ℕ) (hf : IsLocallyConstant f)
    (hg : IsLocallyConstant g) (hc : IsLocallyConstant c) (w : ℕ) (x : X) :
    x ∈ ratioWindowOpens X f g c hf hg hc w ↔ f x ≤ g x ∧ g x < c x ^ w * f x := Iff.rfl

theorem isClosed_ratioWindowOpens (X : Scheme) (f g c : X → ℕ) (hf : IsLocallyConstant f)
    (hg : IsLocallyConstant g) (hc : IsLocallyConstant c) (w : ℕ) :
    IsClosed ((ratioWindowOpens X f g c hf hg hc w : X.Opens) : Set X) :=
  (isClopen_ratioWindow hf hg hc w).isClosed

theorem isClopen_of_openCover' (X : Scheme) (𝒰 : X.OpenCover) (Z : Set X) (S : ∀ j : 𝒰.I₀, Set ↥(𝒰.X j))
    (hS : ∀ j, IsClopen (S j)) (hZ : ∀ (j) (u : ↥(𝒰.X j)), (𝒰.f j).base u ∈ Z ↔ u ∈ S j) : IsClopen Z := by
  refine isClopen_of_cover (fun j : 𝒰.I₀ => Set.range (𝒰.f j).base) (fun x => ⟨𝒰.idx x, 𝒰.covers x⟩) Z
    (fun j => ?_) (fun j => ?_)
  · have : Z ∩ Set.range (𝒰.f j).base = (𝒰.f j).base '' S j := by
      ext x
      simp only [Set.mem_inter_iff, Set.mem_range, Set.mem_image]
      exact ⟨fun ⟨hz, u, hu⟩ => ⟨u, (hZ j u).1 (hu ▸ hz), hu⟩, fun ⟨u, hu, hux⟩ => ⟨hux ▸ (hZ j u).2 hu, u, hux⟩⟩
    rw [this]
    exact (𝒰.f j).isOpenEmbedding.isOpenMap _ (hS j).isOpen
  · have : Zᶜ ∩ Set.range (𝒰.f j).base = (𝒰.f j).base '' (S j)ᶜ := by
      ext x
      simp only [Set.mem_inter_iff, Set.mem_compl_iff, Set.mem_range, Set.mem_image]
      exact ⟨fun ⟨hz, u, hu⟩ => ⟨u, fun h => hz (hu ▸ (hZ j u).2 h), hu⟩,
        fun ⟨u, hu, hux⟩ => ⟨fun h => hu ((hZ j u).1 (hux ▸ h)), u, hux⟩⟩
    rw [this]
    exact (𝒰.f j).isOpenEmbedding.isOpenMap _ (hS j).isClosed.isOpen_compl

def opensOfOpenCover' (X : Scheme) (𝒰 : X.OpenCover) (Z : Set X) (S : ∀ j : 𝒰.I₀, Set ↥(𝒰.X j))
    (hS : ∀ j, IsClopen (S j)) (hZ : ∀ (j) (u : ↥(𝒰.X j)), (𝒰.f j).base u ∈ Z ↔ u ∈ S j) : X.Opens :=
  opensOfClopen X Z (isClopen_of_openCover' X 𝒰 Z S hS hZ)

theorem mem_opensOfOpenCover' (X : Scheme) (𝒰 : X.OpenCover) (Z : Set X) (S : ∀ j : 𝒰.I₀, Set ↥(𝒰.X j))
    (hS : ∀ j, IsClopen (S j)) (hZ : ∀ (j) (u : ↥(𝒰.X j)), (𝒰.f j).base u ∈ Z ↔ u ∈ S j)
    (j : 𝒰.I₀) (u : ↥(𝒰.X j)) : (𝒰.f j).base u ∈ opensOfOpenCover' X 𝒰 Z S hS hZ ↔ u ∈ S j := hZ j u

theorem isClosed_opensOfOpenCover' (X : Scheme) (𝒰 : X.OpenCover) (Z : Set X) (S : ∀ j : 𝒰.I₀, Set ↥(𝒰.X j))
    (hS : ∀ j, IsClopen (S j)) (hZ : ∀ (j) (u : ↥(𝒰.X j)), (𝒰.f j).base u ∈ Z ↔ u ∈ S j) :
    IsClosed ((opensOfOpenCover' X 𝒰 Z S hS hZ : X.Opens) : Set X) :=
  (isClopen_of_openCover' X 𝒰 Z S hS hZ).isClosed

end Clopen
p2m_reactivate "P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_exists_opens_ratioWindow_degree_laws_of_rigidifiedToG_of_bdd.Ws16WC.Clopen"

namespace FEC

open scoped TensorProduct Quaternion NumberField
p2m_open "CategoryTheory AlgebraicGeometry CerednikDrinfeld P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_exists_opens_ratioWindow_degree_laws_of_rigidifiedToG_of_bdd.CerednikDrinfeld CerednikDrinfeld.QM P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_exists_opens_ratioWindow_degree_laws_of_rigidifiedToG_of_bdd.CerednikDrinfeld.QM"

variable {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} {N : ℕ}

private theorem _root_.Ws16WC.FEC.isClopen_ratioWindow (S : Type) [CommRing S] (E A : FakeEllipticCurve Λ N S)
    (φ : E.A ⟶ A.A) (φ' : A.A ⟶ E.A) [IsFinite φ] [Flat φ] [LocallyOfFinitePresentation φ]
    [IsFinite φ'] [Flat φ'] [LocallyOfFinitePresentation φ']
    (c : ↥(Spec (CommRingCat.of S)) → ℕ) (hc : IsLocallyConstant c) (w : ℕ) :
    IsClopen {s : ↥(Spec (CommRingCat.of S)) |
      degOnBase S E A φ s ≤ degOnBase S A E φ' s ∧ degOnBase S A E φ' s < c s ^ w * degOnBase S E A φ s} :=
  Clopen.isClopen_ratioWindow (isLocallyConstant_degOnBase S E A φ) (isLocallyConstant_degOnBase S A E φ') hc w

p2m_export "Ws16WC.FEC" "isClopen_ratioWindow"

noncomputable def ratioWindowLocus (S : Type) [CommRing S] (E A : FakeEllipticCurve Λ N S)
    (φ : E.A ⟶ A.A) (φ' : A.A ⟶ E.A) [IsFinite φ] [Flat φ] [LocallyOfFinitePresentation φ]
    [IsFinite φ'] [Flat φ'] [LocallyOfFinitePresentation φ']
    (c : ↥(Spec (CommRingCat.of S)) → ℕ) (hc : IsLocallyConstant c) (w : ℕ) : (Spec (CommRingCat.of S)).Opens :=
  Clopen.opensOfClopen _ _ (isClopen_ratioWindow S E A φ φ' c hc w)

theorem mem_ratioWindowLocus (S : Type) [CommRing S] (E A : FakeEllipticCurve Λ N S)
    (φ : E.A ⟶ A.A) (φ' : A.A ⟶ E.A) [IsFinite φ] [Flat φ] [LocallyOfFinitePresentation φ]
    [IsFinite φ'] [Flat φ'] [LocallyOfFinitePresentation φ']
    (c : ↥(Spec (CommRingCat.of S)) → ℕ) (hc : IsLocallyConstant c) (w : ℕ) (s : ↥(Spec (CommRingCat.of S))) :
    s ∈ ratioWindowLocus S E A φ φ' c hc w ↔
      φ.finrank ((A.L.one (𝟙 (Spec (CommRingCat.of S)))).1.base s) ≤
          φ'.finrank ((E.L.one (𝟙 (Spec (CommRingCat.of S)))).1.base s) ∧
        φ'.finrank ((E.L.one (𝟙 (Spec (CommRingCat.of S)))).1.base s) <
          c s ^ w * φ.finrank ((A.L.one (𝟙 (Spec (CommRingCat.of S)))).1.base s) := Iff.rfl

theorem isClosed_ratioWindowLocus (S : Type) [CommRing S] (E A : FakeEllipticCurve Λ N S)
    (φ : E.A ⟶ A.A) (φ' : A.A ⟶ E.A) [IsFinite φ] [Flat φ] [LocallyOfFinitePresentation φ]
    [IsFinite φ'] [Flat φ'] [LocallyOfFinitePresentation φ']
    (c : ↥(Spec (CommRingCat.of S)) → ℕ) (hc : IsLocallyConstant c) (w : ℕ) :
    IsClosed (ratioWindowLocus S E A φ φ' c hc w : Set ↥(Spec (CommRingCat.of S))) :=
  (isClopen_ratioWindow S E A φ φ' c hc w).isClosed

end FEC
p2m_reactivate "P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_exists_opens_ratioWindow_degree_laws_of_rigidifiedToG_of_bdd.Ws16WC.Clopen"

namespace RatioArith

def InWindow (c w A B : ℕ) : Prop := A ≤ B ∧ B < c ^ w * A

theorem inWindow_iff (c w A B : ℕ) : InWindow c w A B ↔ A ≤ B ∧ B < c ^ w * A := Iff.rfl

theorem two_mul_lt_of_le_of_lt {c w x y k : ℕ} (hc : 1 < c) (_hx : 0 < x)
    (h1 : x * c ^ k ≤ y) (h2 : y * c ^ k < c ^ w * x) : 2 * k < w := by
  have h3 : x * c ^ (2 * k) < x * c ^ w := by
    calc x * c ^ (2 * k) = x * c ^ k * c ^ k := by rw [two_mul, pow_add, mul_assoc]
      _ ≤ y * c ^ k := Nat.mul_le_mul_right _ h1
      _ < c ^ w * x := h2
      _ = x * c ^ w := mul_comm _ _
  have h4 : c ^ (2 * k) < c ^ w := Nat.lt_of_mul_lt_mul_left h3
  exact (Nat.pow_lt_pow_iff_right hc).1 h4

theorem inWindow_pad {c w A B a b : ℕ} (hc : 1 < c) (h : InWindow c w (A * c ^ a) (B * c ^ b)) (k : ℕ) :
    InWindow c w (A * c ^ (a + k)) (B * c ^ (b + k)) := by
  obtain ⟨h1, h2⟩ := h
  refine ⟨?_, ?_⟩
  · calc A * c ^ (a + k) = A * c ^ a * c ^ k := by rw [pow_add, mul_assoc]
      _ ≤ B * c ^ b * c ^ k := Nat.mul_le_mul_right _ h1
      _ = B * c ^ (b + k) := by rw [pow_add, mul_assoc]
  · calc B * c ^ (b + k) = B * c ^ b * c ^ k := by rw [pow_add, mul_assoc]
      _ < c ^ w * (A * c ^ a) * c ^ k := Nat.mul_lt_mul_of_lt_of_le h2 le_rfl (pow_pos (by omega) _)
      _ = c ^ w * (A * c ^ (a + k)) := by rw [pow_add]; ring

theorem inWindow_two_of_inWindow_one_shift {c A B a b : ℕ} (hc : 1 < c)
    (h : InWindow c 1 (A * c ^ a) (B * c ^ b)) : InWindow c 2 (A * c ^ a) (B * c ^ (b + 1)) := by
  obtain ⟨h1, h2⟩ := h
  refine ⟨?_, ?_⟩
  · calc A * c ^ a ≤ B * c ^ b := h1
      _ ≤ B * c ^ b * c := Nat.le_mul_of_pos_right _ (by omega)
      _ = B * c ^ (b + 1) := by rw [pow_succ, mul_assoc]
  · calc B * c ^ (b + 1) = B * c ^ b * c := by rw [pow_succ, mul_assoc]
      _ < c ^ 1 * (A * c ^ a) * c := Nat.mul_lt_mul_of_lt_of_le h2 le_rfl (by omega)
      _ = c ^ 2 * (A * c ^ a) := by ring

theorem inWindow_mono {c w w' A B : ℕ} (hc : 1 < c) (hw : w ≤ w') (h : InWindow c w A B) : InWindow c w' A B :=
  ⟨h.1, h.2.trans_le (Nat.mul_le_mul_right _ (Nat.pow_le_pow_right (by omega) hw))⟩

theorem pad_eq_of_inWindow_of_add_eq {c w A B a b a' b' : ℕ} (hc : 1 < c) (hA : 0 < A) (hw : w ≤ 2)
    (hs : a + b = a' + b')
    (h : InWindow c w (A * c ^ a) (B * c ^ b)) (h' : InWindow c w (A * c ^ a') (B * c ^ b')) :
    a = a' ∧ b = b' := by
  rcases le_total a a' with hle | hle
  · obtain ⟨k, rfl⟩ : ∃ k, a' = a + k := ⟨a' - a, by omega⟩
    have hb : b = b' + k := by omega
    subst hb
    have h1 : A * c ^ a * c ^ k ≤ B * c ^ b' := by
      simpa [pow_add, mul_assoc] using h'.1
    have h2 : B * c ^ b' * c ^ k < c ^ w * (A * c ^ a) := by
      simpa [pow_add, mul_assoc] using h.2
    have := two_mul_lt_of_le_of_lt hc (Nat.mul_pos hA (pow_pos (by omega) _)) h1 h2
    constructor <;> omega
  · obtain ⟨k, rfl⟩ : ∃ k, a = a' + k := ⟨a - a', by omega⟩
    have hb : b' = b + k := by omega
    subst hb
    have h1 : A * c ^ a' * c ^ k ≤ B * c ^ b := by
      simpa [pow_add, mul_assoc] using h.1
    have h2 : B * c ^ b * c ^ k < c ^ w * (A * c ^ a') := by
      simpa [pow_add, mul_assoc] using h'.2
    have := two_mul_lt_of_le_of_lt hc (Nat.mul_pos hA (pow_pos (by omega) _)) h1 h2
    constructor <;> omega

theorem skew_eq_of_inWindow_one {c A B a b a' b' : ℕ} (hc : 1 < c) (_hA : 0 < A)
    (h : InWindow c 1 (A * c ^ a) (B * c ^ b)) (h' : InWindow c 1 (A * c ^ a') (B * c ^ b')) :
    a + b' = a' + b := by

  have key : ∀ {a b a' b' : ℕ}, A * c ^ a' ≤ B * c ^ b' → B * c ^ b < c ^ 1 * (A * c ^ a) →
      a' + b ≤ a + b' := by
    intro a b a' b' h1 h2
    have h3 : A * c ^ (a' + b) < A * c ^ (a + b' + 1) := by
      calc A * c ^ (a' + b) = A * c ^ a' * c ^ b := by rw [pow_add, mul_assoc]
        _ ≤ B * c ^ b' * c ^ b := Nat.mul_le_mul_right _ h1
        _ = B * c ^ b * c ^ b' := by ring
        _ < c ^ 1 * (A * c ^ a) * c ^ b' := Nat.mul_lt_mul_of_lt_of_le h2 le_rfl (pow_pos (by omega) _)
        _ = A * c ^ (a + b' + 1) := by rw [pow_add, pow_add]; ring
    have h4 : c ^ (a' + b) < c ^ (a + b' + 1) := Nat.lt_of_mul_lt_mul_left h3
    have := (Nat.pow_lt_pow_iff_right hc).1 h4
    omega
  have h₁ := key h'.1 h.2
  have h₂ := key h.1 h'.2
  omega

theorem pad_eq_of_inWindow_one_of_window {c A B a b a' b' d₀ D : ℕ} (hc : 1 < c) (hA : 0 < A)
    (h : InWindow c 1 (A * c ^ a) (B * c ^ b)) (h' : InWindow c 1 (A * c ^ a') (B * c ^ b'))
    (hd : d₀ + a + b = D ∨ d₀ + a + b = D + 1) (hd' : d₀ + a' + b' = D ∨ d₀ + a' + b' = D + 1) :
    a = a' ∧ b = b' := by
  have hk := skew_eq_of_inWindow_one hc hA h h'
  constructor <;> omega

theorem even_add_of_inWindow_one {c A B a b a' b' : ℕ} (hc : 1 < c) (hA : 0 < A)
    (h : InWindow c 1 (A * c ^ a) (B * c ^ b)) (h' : InWindow c 1 (A * c ^ a') (B * c ^ b')) :
    Even ((a + b) + (a' + b')) := by
  have hk := skew_eq_of_inWindow_one hc hA h h'
  exact ⟨a + b', by omega⟩

theorem exists_inWindow_one {c A B n : ℕ} (hc : 1 < c) (hA : 0 < A) (hB : 0 < B)
    (hAn : A ≤ c ^ n) (hBn : B ≤ c ^ n) :
    ∃ a b : ℕ, InWindow c 1 (A * c ^ a) (B * c ^ b) ∧ a + b ≤ n ∧ (a = 0 ∨ b = 0) := by
  classical
  rcases le_or_gt A B with hAB | hAB
  ·
    have hlt : B < A * c ^ (n + 1) :=
      lt_of_le_of_lt hBn (lt_of_lt_of_le (Nat.pow_lt_pow_right hc (Nat.lt_succ_self n)) (Nat.le_mul_of_pos_left _ hA))
    have hex : ∃ a, B < A * c ^ (a + 1) := ⟨n, hlt⟩
    refine ⟨Nat.find hex, 0, ⟨?_, ?_⟩, ?_, Or.inr rfl⟩
    · rcases Nat.eq_zero_or_pos (Nat.find hex) with h0 | hpos
      · rw [h0]; simpa using hAB
      · obtain ⟨m, hm⟩ : ∃ m, Nat.find hex = m + 1 := ⟨Nat.find hex - 1, by omega⟩
        have hmin : ¬ B < A * c ^ (m + 1) := Nat.find_min hex (by omega)
        rw [hm]; simpa using not_lt.1 hmin
    · have hspec : B < A * c ^ (Nat.find hex + 1) := Nat.find_spec hex
      simpa [pow_succ, mul_comm, mul_assoc, mul_left_comm] using hspec
    · have : Nat.find hex ≤ n := Nat.find_le hlt
      omega
  ·
    have hex : ∃ b, A ≤ B * c ^ b := ⟨n, hAn.trans (Nat.le_mul_of_pos_left _ hB)⟩
    have hpos : 0 < Nat.find hex := (Nat.find_pos hex).2 (by simpa using hAB)
    obtain ⟨m, hm⟩ : ∃ m, Nat.find hex = m + 1 := ⟨Nat.find hex - 1, by omega⟩
    refine ⟨0, Nat.find hex, ⟨?_, ?_⟩, ?_, Or.inl rfl⟩
    · simpa using (Nat.find_spec hex)
    · have hmin : ¬ A ≤ B * c ^ m := Nat.find_min hex (by omega)
      rw [hm, pow_succ]
      have : B * c ^ m < A := not_le.1 hmin
      calc B * (c ^ m * c) = B * c ^ m * c := by rw [mul_assoc]
        _ < A * c := Nat.mul_lt_mul_of_lt_of_le this le_rfl (by omega)
        _ = c ^ 1 * (A * c ^ 0) := by ring
    · have : Nat.find hex ≤ n := Nat.find_le (hAn.trans (Nat.le_mul_of_pos_left _ hB))
      omega

theorem le_pow_of_mul_eq_pow {c A B d₀ : ℕ} (hA : 0 < A) (hB : 0 < B) (h : A * B = c ^ d₀) :
    A ≤ c ^ d₀ ∧ B ≤ c ^ d₀ :=
  ⟨h ▸ Nat.le_mul_of_pos_right _ hB, h ▸ Nat.le_mul_of_pos_left _ hA⟩

theorem exists_inWindow_one_exponent_mem {c A B n d₀ D : ℕ} (hc : 1 < c) (hA : 0 < A) (hB : 0 < B)
    (hAn : A ≤ c ^ n) (hBn : B ≤ c ^ n) (hD : d₀ + n ≤ D) :
    ∃ a b : ℕ, InWindow c 1 (A * c ^ a) (B * c ^ b) ∧ (d₀ + a + b = D ∨ d₀ + a + b = D + 1) := by
  obtain ⟨a, b, hw, hab, -⟩ := exists_inWindow_one hc hA hB hAn hBn
  refine ⟨a + (D + 1 - (d₀ + a + b)) / 2, b + (D + 1 - (d₀ + a + b)) / 2, inWindow_pad hc hw _, ?_⟩
  omega

theorem exists_inWindow_two_exponent_eq {c A B n d₀ D : ℕ} (hc : 1 < c) (hA : 0 < A) (hB : 0 < B)
    (hAn : A ≤ c ^ n) (hBn : B ≤ c ^ n) (hD : d₀ + n ≤ D) :
    ∃ a b : ℕ, InWindow c 2 (A * c ^ a) (B * c ^ b) ∧ d₀ + a + b = D := by
  obtain ⟨a, b, hw, hab, -⟩ := exists_inWindow_one hc hA hB hAn hBn
  rcases Nat.even_or_odd (D - (d₀ + a + b)) with ⟨k, hk⟩ | ⟨k, hk⟩
  · exact ⟨a + k, b + k, inWindow_pad hc (inWindow_mono hc (by omega) hw) k, by omega⟩
  · refine ⟨a + k, b + 1 + k, inWindow_pad hc (inWindow_two_of_inWindow_one_shift hc hw) k, by omega⟩

theorem exists_inWindow_two_exponent_eq' {c A B d₀ D : ℕ} (hc : 1 < c) (hA : 0 < A) (hB : 0 < B)
    (hAB : A * B = c ^ d₀) (hD : 2 * d₀ ≤ D) :
    ∃ a b : ℕ, InWindow c 2 (A * c ^ a) (B * c ^ b) ∧ d₀ + a + b = D := by
  obtain ⟨hAn, hBn⟩ := le_pow_of_mul_eq_pow hA hB hAB
  exact exists_inWindow_two_exponent_eq hc hA hB hAn hBn (by omega)

theorem exists_inWindow_one_exponent_mem' {c A B d₀ D : ℕ} (hc : 1 < c) (hA : 0 < A) (hB : 0 < B)
    (hAB : A * B = c ^ d₀) (hD : 2 * d₀ ≤ D) :
    ∃ a b : ℕ, InWindow c 1 (A * c ^ a) (B * c ^ b) ∧ (d₀ + a + b = D ∨ d₀ + a + b = D + 1) := by
  obtain ⟨hAn, hBn⟩ := le_pow_of_mul_eq_pow hA hB hAB
  exact exists_inWindow_one_exponent_mem hc hA hB hAn hBn (by omega)

end RatioArith
p2m_reactivate "P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_exists_opens_ratioWindow_degree_laws_of_rigidifiedToG_of_bdd.Ws16WC.Clopen"

namespace Clopen
open CategoryTheory AlgebraicGeometry

theorem forall_mem_ratioWindowOpens_iff_forall (X : Scheme) (f g c : X → ℕ) (hf : IsLocallyConstant f)
    (hg : IsLocallyConstant g) (hc : IsLocallyConstant c) (w : ℕ) {P : Sort*} (x : P → X)
    (dρ dρ' cρ : P → ℕ) (hfx : ∀ p, f (x p) = dρ p) (hgx : ∀ p, g (x p) = dρ' p) (hcx : ∀ p, c (x p) = cρ p) :
    (∀ p, x p ∈ ratioWindowOpens X f g c hf hg hc w) ↔ ∀ p, dρ p ≤ dρ' p ∧ dρ' p < cρ p ^ w * dρ p := by
  refine forall_congr' fun p => ?_
  rw [mem_ratioWindowOpens, hfx, hgx, hcx]

theorem forall_mem_ratioWindowOpens_iff (X : Scheme) (f g c : X → ℕ) (hf : IsLocallyConstant f)
    (hg : IsLocallyConstant g) (hc : IsLocallyConstant c) (w : ℕ) {P : Sort*} [Nonempty P] (x : P → X)
    (dρ dρ' cρ : ℕ) (hfx : ∀ p, f (x p) = dρ) (hgx : ∀ p, g (x p) = dρ') (hcx : ∀ p, c (x p) = cρ) :
    (∀ p, x p ∈ ratioWindowOpens X f g c hf hg hc w) ↔ (dρ ≤ dρ' ∧ dρ' < cρ ^ w * dρ) := by
  rw [forall_mem_ratioWindowOpens_iff_forall X f g c hf hg hc w x (fun _ => dρ) (fun _ => dρ') (fun _ => cρ)
    hfx hgx hcx]
  exact ⟨fun h => h (Classical.arbitrary P), fun h _ => h⟩

theorem forall_mem_ratioWindowOpens_of (X : Scheme) (f g c : X → ℕ) (hf : IsLocallyConstant f)
    (hg : IsLocallyConstant g) (hc : IsLocallyConstant c) (w : ℕ) {P : Sort*} (x : P → X)
    (dρ dρ' cρ : ℕ) (hfx : ∀ p, f (x p) = dρ) (hgx : ∀ p, g (x p) = dρ') (hcx : ∀ p, c (x p) = cρ)
    (h : dρ ≤ dρ' ∧ dρ' < cρ ^ w * dρ) : ∀ p, x p ∈ ratioWindowOpens X f g c hf hg hc w :=
  (forall_mem_ratioWindowOpens_iff_forall X f g c hf hg hc w x (fun _ => dρ) (fun _ => dρ') (fun _ => cρ)
    hfx hgx hcx).2 fun _ => h

theorem window_of_mem_ratioWindowOpens (X : Scheme) (f g c : X → ℕ) (hf : IsLocallyConstant f)
    (hg : IsLocallyConstant g) (hc : IsLocallyConstant c) (w : ℕ) {P : Sort*} (x : P → X) (p : P)
    (dρ dρ' cρ : ℕ) (hfx : f (x p) = dρ) (hgx : g (x p) = dρ') (hcx : c (x p) = cρ)
    (h : x p ∈ ratioWindowOpens X f g c hf hg hc w) : dρ ≤ dρ' ∧ dρ' < cρ ^ w * dρ := by
  rw [mem_ratioWindowOpens, hfx, hgx, hcx] at h
  exact h

theorem forall_mem_opensOfClopen_iff (X : Scheme) (Z : Set X) (hZ : IsClopen Z) {P : Sort*} (x : P → X)
    (W : P → Prop) (hZx : ∀ p, x p ∈ Z ↔ W p) :
    (∀ p, x p ∈ opensOfClopen X Z hZ) ↔ ∀ p, W p :=
  forall_congr' fun p => hZx p

theorem forall_mem_opensOfClopen_iff_const (X : Scheme) (Z : Set X) (hZ : IsClopen Z) {P : Sort*} [Nonempty P]
    (x : P → X) (W : Prop) (hZx : ∀ p, x p ∈ Z ↔ W) :
    (∀ p, x p ∈ opensOfClopen X Z hZ) ↔ W :=
  (forall_mem_opensOfClopen_iff X Z hZ x (fun _ => W) hZx).trans
    ⟨fun h => h (Classical.arbitrary P), fun h _ => h⟩

end Clopen
p2m_reactivate "P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_exists_opens_ratioWindow_degree_laws_of_rigidifiedToG_of_bdd.Ws16WC.Clopen"

namespace RatioArith

theorem shift_eq_of_inWindow_of_descend {c w dρ dρ' dσ dσ' i i' j j' : ℕ} (hc : 1 < c) (hρ : 0 < dρ) (hσ : 0 < dσ)
    (hw : w ≤ 2) (hW : InWindow c w dρ dρ') (hW' : InWindow c w dσ dσ')
    (h1 : dσ * c ^ i = dρ * c ^ j) (h2 : dσ' * c ^ i' = dρ' * c ^ j') (hs : i + i' = j + j') :
    i = j ∧ i' = j' := by
  have hcpos : 0 < c := by omega
  rcases le_total i j with hle | hle
  · obtain ⟨k, rfl⟩ : ∃ k, j = i + k := ⟨j - i, by omega⟩
    have hi' : i' = j' + k := by omega
    subst hi'

    have e1 : dσ = dρ * c ^ k := by
      have : dσ * c ^ i = dρ * c ^ k * c ^ i := by rw [h1, pow_add]; ring
      exact Nat.eq_of_mul_eq_mul_right (pow_pos hcpos _) this
    have e2 : dσ' * c ^ k = dρ' := by
      have : dσ' * c ^ k * c ^ j' = dρ' * c ^ j' := by rw [← h2, pow_add]; ring
      exact Nat.eq_of_mul_eq_mul_right (pow_pos hcpos _) this

    have h3 : dρ * c ^ k ≤ dσ' := e1 ▸ hW'.1
    have h4 : dσ' * c ^ k < c ^ w * dρ := e2 ▸ hW.2
    have := two_mul_lt_of_le_of_lt hc hρ h3 h4
    constructor <;> omega
  · obtain ⟨k, rfl⟩ : ∃ k, i = j + k := ⟨i - j, by omega⟩
    have hj' : j' = i' + k := by omega
    subst hj'
    have e1 : dσ * c ^ k = dρ := by
      have : dσ * c ^ k * c ^ j = dρ * c ^ j := by rw [← h1, pow_add]; ring
      exact Nat.eq_of_mul_eq_mul_right (pow_pos hcpos _) this
    have e2 : dσ' = dρ' * c ^ k := by
      have : dσ' * c ^ i' = dρ' * c ^ k * c ^ i' := by rw [h2, pow_add]; ring
      exact Nat.eq_of_mul_eq_mul_right (pow_pos hcpos _) this
    have h3 : dσ * c ^ k ≤ dρ' := e1 ▸ hW.1
    have h4 : dρ' * c ^ k < c ^ w * dσ := e2 ▸ hW'.2
    have := two_mul_lt_of_le_of_lt hc hσ h3 h4
    constructor <;> omega

theorem eq_zero_of_inWindow_shift {c w dρ dρ' k : ℕ} (hc : 1 < c) (hρ : 0 < dρ) (hw : w ≤ 2)
    (hW : InWindow c w dρ dρ') (hW' : InWindow c w (dρ * c ^ (2 * k)) dρ') : k = 0 := by
  have h3 : dρ * c ^ k * c ^ k ≤ dρ' := by simpa [two_mul, pow_add, mul_assoc] using hW'.1
  have h4 : dρ' < c ^ w * dρ := hW.2
  have h5 : dρ' * c ^ k < c ^ w * (dρ * c ^ k) := by
    calc dρ' * c ^ k < c ^ w * dρ * c ^ k := Nat.mul_lt_mul_of_lt_of_le h4 le_rfl (pow_pos (by omega) _)
      _ = c ^ w * (dρ * c ^ k) := by ring
  have := two_mul_lt_of_le_of_lt hc (Nat.mul_pos hρ (pow_pos (by omega) _)) h3 h5
  omega

end RatioArith
p2m_reactivate "P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_exists_opens_ratioWindow_degree_laws_of_rigidifiedToG_of_bdd.Ws16WC.Clopen"

namespace Clopen
open CategoryTheory AlgebraicGeometry Set Topology

theorem isLocallyConstant_of_cover {X : Type*} [TopologicalSpace X] {Y : Type*} {ι : Type*} (U : ι → Set X)
    (hUo : ∀ i, IsOpen (U i)) (hU : ∀ x, ∃ i, x ∈ U i) (val : X → Y)
    (f : ∀ i, U i → Y) (hf : ∀ i, IsLocallyConstant (f i)) (h : ∀ (i) (u : U i), val u = f i u) :
    IsLocallyConstant val := by
  intro s
  have : val ⁻¹' s = ⋃ i, Subtype.val '' ((f i) ⁻¹' s) := by
    ext x
    simp only [mem_preimage, mem_iUnion, mem_image]
    constructor
    · intro hx
      obtain ⟨i, hi⟩ := hU x
      exact ⟨i, ⟨x, hi⟩, by rw [← h i ⟨x, hi⟩]; exact hx, rfl⟩
    · rintro ⟨i, u, hu, rfl⟩
      rw [h i u]; exact hu
  rw [this]
  exact isOpen_iUnion fun i => (hUo i).isOpenMap_subtype_val _ (hf i s)

theorem isLocallyConstant_of_openCover (X : Scheme) (𝒰 : X.OpenCover) {Y : Type*} (val : X → Y)
    (f : ∀ j : 𝒰.I₀, ↥(𝒰.X j) → Y) (hf : ∀ j, IsLocallyConstant (f j))
    (h : ∀ (j) (u : ↥(𝒰.X j)), val ((𝒰.f j).base u) = f j u) : IsLocallyConstant val := by
  intro s
  have : val ⁻¹' s = ⋃ j, (𝒰.f j).base '' ((f j) ⁻¹' s) := by
    ext x
    simp only [Set.mem_preimage, Set.mem_iUnion, Set.mem_image]
    constructor
    · intro hx
      obtain ⟨j, u, hu⟩ := 𝒰.exists_eq x
      exact ⟨j, u, by rw [← h j u]; exact (hu ▸ hx : val ((𝒰.f j).base u) ∈ s), hu⟩
    · rintro ⟨j, u, hu, rfl⟩
      rw [h j u]; exact hu
  rw [this]
  exact isOpen_iUnion fun j => (𝒰.f j).isOpenEmbedding.isOpenMap _ (hf j s)

theorem isLocallyConstant_comp_of_openCover (X : Scheme) (𝒰 : X.OpenCover) {Y : Type*} (val : X → Y)
    (f : ∀ j : 𝒰.I₀, ↥(𝒰.X j) → Y) (hf : ∀ j, IsLocallyConstant (f j))
    (h : ∀ (j) (u : ↥(𝒰.X j)), val ((𝒰.f j).base u) = f j u) {P : Type*} [TopologicalSpace P]
    (x : P → X) (hx : Continuous x) : IsLocallyConstant (val ∘ x) :=
  (isLocallyConstant_of_openCover X 𝒰 val f hf h).comp_continuous hx

theorem apply_eq_of_openCover_of_preconnectedSpace (X : Scheme) (𝒰 : X.OpenCover) {Y : Type*} (val : X → Y)
    (f : ∀ j : 𝒰.I₀, ↥(𝒰.X j) → Y) (hf : ∀ j, IsLocallyConstant (f j))
    (h : ∀ (j) (u : ↥(𝒰.X j)), val ((𝒰.f j).base u) = f j u) {P : Type*} [TopologicalSpace P]
    [PreconnectedSpace P] (x : P → X) (hx : Continuous x) (p q : P) : val (x p) = val (x q) :=
  (isLocallyConstant_comp_of_openCover X 𝒰 val f hf h x hx).apply_eq_of_preconnectedSpace p q

end Clopen
p2m_reactivate "P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_exists_opens_ratioWindow_degree_laws_of_rigidifiedToG_of_bdd.Ws16WC.Clopen"

namespace DEGb

open CategoryTheory AlgebraicGeometry Topology

structure DegreeMaps (X : Scheme) where

  f : X → ℕ

  g : X → ℕ

  c : X → ℕ
  hf : IsLocallyConstant f
  hg : IsLocallyConstant g
  hc : IsLocallyConstant c

def DegreeMaps.ofOpenCover (X : Scheme) (𝒰 : X.OpenCover) (f g c : X → ℕ)
    (fj gj cj : ∀ j : 𝒰.I₀, ↥(𝒰.X j) → ℕ)
    (hfj : ∀ j, IsLocallyConstant (fj j)) (hgj : ∀ j, IsLocallyConstant (gj j)) (hcj : ∀ j, IsLocallyConstant (cj j))
    (hf : ∀ (j) (u : ↥(𝒰.X j)), f ((𝒰.f j).base u) = fj j u)
    (hg : ∀ (j) (u : ↥(𝒰.X j)), g ((𝒰.f j).base u) = gj j u)
    (hc : ∀ (j) (u : ↥(𝒰.X j)), c ((𝒰.f j).base u) = cj j u) : DegreeMaps X where
  f := f
  g := g
  c := c
  hf := Clopen.isLocallyConstant_of_openCover X 𝒰 f fj hfj hf
  hg := Clopen.isLocallyConstant_of_openCover X 𝒰 g gj hgj hg
  hc := Clopen.isLocallyConstant_of_openCover X 𝒰 c cj hcj hc

@[scoped simp] theorem DegreeMaps.ofOpenCover_f (X : Scheme) (𝒰 : X.OpenCover) (f g c : X → ℕ) (fj gj cj hfj hgj hcj hf hg hc) :
    (DegreeMaps.ofOpenCover X 𝒰 f g c fj gj cj hfj hgj hcj hf hg hc).f = f := rfl
p2m_reactivate "P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_exists_opens_ratioWindow_degree_laws_of_rigidifiedToG_of_bdd.Ws16WC.Clopen P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_exists_opens_ratioWindow_degree_laws_of_rigidifiedToG_of_bdd.Ws16WC.DEGb.DegreeMaps"
@[scoped simp] theorem DegreeMaps.ofOpenCover_g (X : Scheme) (𝒰 : X.OpenCover) (f g c : X → ℕ) (fj gj cj hfj hgj hcj hf hg hc) :
    (DegreeMaps.ofOpenCover X 𝒰 f g c fj gj cj hfj hgj hcj hf hg hc).g = g := rfl
p2m_reactivate "P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_exists_opens_ratioWindow_degree_laws_of_rigidifiedToG_of_bdd.Ws16WC.Clopen P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_exists_opens_ratioWindow_degree_laws_of_rigidifiedToG_of_bdd.Ws16WC.DEGb.DegreeMaps"
@[scoped simp] theorem DegreeMaps.ofOpenCover_c (X : Scheme) (𝒰 : X.OpenCover) (f g c : X → ℕ) (fj gj cj hfj hgj hcj hf hg hc) :
    (DegreeMaps.ofOpenCover X 𝒰 f g c fj gj cj hfj hgj hcj hf hg hc).c = c := rfl

p2m_reactivate "P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_exists_opens_ratioWindow_degree_laws_of_rigidifiedToG_of_bdd.Ws16WC.Clopen P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_exists_opens_ratioWindow_degree_laws_of_rigidifiedToG_of_bdd.Ws16WC.DEGb.DegreeMaps"
variable {X : Scheme}

def B (δ : DegreeMaps X) : X.Opens := Clopen.ratioWindowOpens X δ.f δ.g δ.c δ.hf δ.hg δ.hc 2

theorem isClosed_B (δ : DegreeMaps X) : IsClosed (B δ : Set X) :=
  Clopen.isClosed_ratioWindowOpens X δ.f δ.g δ.c δ.hf δ.hg δ.hc 2

theorem isClopen_B (δ : DegreeMaps X) : IsClopen (B δ : Set X) := ⟨isClosed_B δ, (B δ).isOpen⟩

theorem mem_B_iff (δ : DegreeMaps X) (x : X) : x ∈ B δ ↔ RatioArith.InWindow (δ.c x) 2 (δ.f x) (δ.g x) := Iff.rfl

theorem mem_B_iff' (δ : DegreeMaps X) (x : X) : x ∈ B δ ↔ δ.f x ≤ δ.g x ∧ δ.g x < δ.c x ^ 2 * δ.f x := Iff.rfl

def W (δ : DegreeMaps X) (U : X.Opens) : X.Opens := U ⊓ B δ

theorem mem_W_iff (δ : DegreeMaps X) (U : X.Opens) (x : X) : x ∈ W δ U ↔ x ∈ U ∧ x ∈ B δ := Iff.rfl

theorem isOpenImmersion_W_ι (δ : DegreeMaps X) (U : X.Opens) : IsOpenImmersion (W δ U).ι := inferInstance

section TPoint

variable (δ : DegreeMaps X) {T : Type} [CommRing T] (xT : Spec (CommRingCat.of T) ⟶ X)
  (dρ dρ' cT : ↥(Spec (CommRingCat.of T)) → ℕ)

theorem forall_mem_B_iff_forall (hfT : ∀ p, δ.f (xT.base p) = dρ p) (hgT : ∀ p, δ.g (xT.base p) = dρ' p) (hcT : ∀ p, δ.c (xT.base p) = cT p) :
    (∀ p, xT.base p ∈ B δ) ↔ ∀ p, RatioArith.InWindow (cT p) 2 (dρ p) (dρ' p) :=
  Clopen.forall_mem_ratioWindowOpens_iff_forall X δ.f δ.g δ.c δ.hf δ.hg δ.hc 2 xT.base dρ dρ' cT hfT hgT hcT

theorem deg_apply_eq_of_preconnectedSpace (hfT : ∀ p, δ.f (xT.base p) = dρ p) (hgT : ∀ p, δ.g (xT.base p) = dρ' p) (hcT : ∀ p, δ.c (xT.base p) = cT p) [PreconnectedSpace ↥(Spec (CommRingCat.of T))]
    (p q : ↥(Spec (CommRingCat.of T))) : dρ p = dρ q ∧ dρ' p = dρ' q ∧ cT p = cT q := by
  refine ⟨?_, ?_, ?_⟩
  · rw [← hfT p, ← hfT q]
    exact (δ.hf.comp_continuous xT.continuous).apply_eq_of_preconnectedSpace p q
  · rw [← hgT p, ← hgT q]
    exact (δ.hg.comp_continuous xT.continuous).apply_eq_of_preconnectedSpace p q
  · rw [← hcT p, ← hcT q]
    exact (δ.hc.comp_continuous xT.continuous).apply_eq_of_preconnectedSpace p q

theorem forall_mem_B_iff_inWindow (hfT : ∀ p, δ.f (xT.base p) = dρ p) (hgT : ∀ p, δ.g (xT.base p) = dρ' p) (hcT : ∀ p, δ.c (xT.base p) = cT p)
    [PreconnectedSpace ↥(Spec (CommRingCat.of T))] (p₀ : ↥(Spec (CommRingCat.of T))) :
    (∀ p, xT.base p ∈ B δ) ↔ RatioArith.InWindow (cT p₀) 2 (dρ p₀) (dρ' p₀) := by
  rw [forall_mem_B_iff_forall δ xT dρ dρ' cT hfT hgT hcT]
  refine ⟨fun h => h p₀, fun h p => ?_⟩
  obtain ⟨e1, e2, e3⟩ := deg_apply_eq_of_preconnectedSpace δ xT dρ dρ' cT hfT hgT hcT p p₀
  rw [e1, e2, e3]; exact h

theorem forall_mem_B_iff_inWindow_const [Nonempty ↥(Spec (CommRingCat.of T))] (a a' k : ℕ)
    (hfT : ∀ p, δ.f (xT.base p) = a) (hgT : ∀ p, δ.g (xT.base p) = a') (hcT : ∀ p, δ.c (xT.base p) = k) :
    (∀ p, xT.base p ∈ B δ) ↔ RatioArith.InWindow k 2 a a' :=
  Clopen.forall_mem_ratioWindowOpens_iff X δ.f δ.g δ.c δ.hf δ.hg δ.hc 2 xT.base a a' k hfT hgT hcT

theorem forall_mem_B_of_inWindow (a a' k : ℕ)
    (hfT : ∀ p, δ.f (xT.base p) = a) (hgT : ∀ p, δ.g (xT.base p) = a') (hcT : ∀ p, δ.c (xT.base p) = k)
    (h : RatioArith.InWindow k 2 a a') : ∀ p, xT.base p ∈ B δ :=
  Clopen.forall_mem_ratioWindowOpens_of X δ.f δ.g δ.c δ.hf δ.hg δ.hc 2 xT.base a a' k hfT hgT hcT h

theorem inWindow_of_mem_B (hfT : ∀ p, δ.f (xT.base p) = dρ p) (hgT : ∀ p, δ.g (xT.base p) = dρ' p) (hcT : ∀ p, δ.c (xT.base p) = cT p)
    (p : ↥(Spec (CommRingCat.of T))) (h : xT.base p ∈ B δ) :
    RatioArith.InWindow (cT p) 2 (dρ p) (dρ' p) :=
  Clopen.window_of_mem_ratioWindowOpens X δ.f δ.g δ.c δ.hf δ.hg δ.hc 2 xT.base p _ _ _ (hfT p) (hgT p) (hcT p) h

end TPoint
p2m_reactivate "P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_exists_opens_ratioWindow_degree_laws_of_rigidifiedToG_of_bdd.Ws16WC.Clopen P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_exists_opens_ratioWindow_degree_laws_of_rigidifiedToG_of_bdd.Ws16WC.DEGb.DegreeMaps"

theorem range_subset_W_iff (δ : DegreeMaps X) (U : X.Opens) {T : Type} [CommRing T]
    (xT : Spec (CommRingCat.of T) ⟶ X) :
    Set.range xT.base ⊆ (W δ U : Set X) ↔ ∀ p, xT.base p ∈ U ∧ xT.base p ∈ B δ := by
  constructor
  · intro h p; exact h ⟨p, rfl⟩
  · rintro h _ ⟨p, rfl⟩; exact h p

end DEGb
p2m_reactivate "P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_exists_opens_ratioWindow_degree_laws_of_rigidifiedToG_of_bdd.Ws16WC.Clopen P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_exists_opens_ratioWindow_degree_laws_of_rigidifiedToG_of_bdd.Ws16WC.DEGb.DegreeMaps P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_exists_opens_ratioWindow_degree_laws_of_rigidifiedToG_of_bdd.Ws16WC.DEGb"

end Ws16WC
p2m_reactivate "P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_exists_opens_ratioWindow_degree_laws_of_rigidifiedToG_of_bdd.Ws16WC.Clopen P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_exists_opens_ratioWindow_degree_laws_of_rigidifiedToG_of_bdd.Ws16WC.DEGb.DegreeMaps P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_exists_opens_ratioWindow_degree_laws_of_rigidifiedToG_of_bdd.Ws16WC.DEGb P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_exists_opens_ratioWindow_degree_laws_of_rigidifiedToG_of_bdd.Ws16WC"

set_option autoImplicit false

open scoped TensorProduct Quaternion NumberField
p2m_open "CategoryTheory AlgebraicGeometry QuaternionAlgebra CerednikDrinfeld P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_exists_opens_ratioWindow_degree_laws_of_rigidifiedToG_of_bdd.CerednikDrinfeld CerednikDrinfeld.QM P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_exists_opens_ratioWindow_degree_laws_of_rigidifiedToG_of_bdd.CerednikDrinfeld.QM NeronModelInfra~schemeHomOverComp_coe GoodReductionJacobian"

namespace DEG44

theorem isPullback_of_isPullback_over {X X' Y Y' S S' : Scheme.{0}}
    (gX : X' ⟶ X) (gY : Y' ⟶ Y) (s : S' ⟶ S)
    (pX : X ⟶ S) (pX' : X' ⟶ S') (pY : Y ⟶ S) (pY' : Y' ⟶ S')
    (hX : IsPullback gX pX' pX s) (hY : IsPullback gY pY' pY s)
    (φ : X ⟶ Y) (φ' : X' ⟶ Y') (hφ : φ ≫ pY = pX) (hφ' : φ' ≫ pY' = pX') (comm : gX ≫ φ = φ' ≫ gY) :
    IsPullback gX φ' φ gY := by
  have big : IsPullback gX (φ' ≫ pY') (φ ≫ pY) s := by rw [hφ', hφ]; exact hX
  exact IsPullback.of_bot big comm hY

section FEC
variable {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} {N : ℕ}

theorem isIsogenyPair_symm {S : Type} [CommRing S] (d : ℕ) (E E' : FakeEllipticCurve Λ N S)
    (φ : E.A ⟶ E'.A) (ψ : E'.A ⟶ E.A) (h : FakeEllipticCurve.IsIsogenyPair d E E' φ ψ) :
    FakeEllipticCurve.IsIsogenyPair d E' E ψ φ := by
  obtain ⟨hφ, hψ, h1, h2, h3, h4, h5⟩ := h
  exact ⟨hψ, hφ, h2, h1, h4, h3, fun hd => ⟨(h5 hd).2, (h5 hd).1⟩⟩

theorem isPullback_of_isPullbackVia {S S' : Type} [CommRing S] [CommRing S'] (φ : S →+* S')
    (E : FakeEllipticCurve Λ N S) (E' : FakeEllipticCurve Λ N S') (gE : E'.A ⟶ E.A)
    (hE : FakeEllipticCurve.IsPullbackVia φ E E' gE)
    (A : FakeEllipticCurve Λ N S) (A' : FakeEllipticCurve Λ N S') (gA : A'.A ⟶ A.A)
    (hA : FakeEllipticCurve.IsPullbackVia φ A A' gA)
    (ψ : E.A ⟶ A.A) (hψ : ψ ≫ A.f = E.f) (ψ' : E'.A ⟶ A'.A) (hψ' : ψ' ≫ A'.f = E'.f)
    (comm : gE ≫ ψ = ψ' ≫ gA) :
    IsPullback gE ψ' ψ gA := by
  obtain ⟨hgE, -⟩ := hE
  obtain ⟨hgA, -⟩ := hA
  exact isPullback_of_isPullback_over gE gA _ E.f E'.f A.f A'.f hgE hgA ψ ψ' hψ hψ' comm

theorem finrank_eq_of_isPullbackVia {S S' : Type} [CommRing S] [CommRing S'] (φ : S →+* S')
    (E : FakeEllipticCurve Λ N S) (E' : FakeEllipticCurve Λ N S') (gE : E'.A ⟶ E.A)
    (hE : FakeEllipticCurve.IsPullbackVia φ E E' gE)
    (A : FakeEllipticCurve Λ N S) (A' : FakeEllipticCurve Λ N S') (gA : A'.A ⟶ A.A)
    (hA : FakeEllipticCurve.IsPullbackVia φ A A' gA)
    (ψ : E.A ⟶ A.A) (hψ : ψ ≫ A.f = E.f) (ψ' : E'.A ⟶ A'.A) (hψ' : ψ' ≫ A'.f = E'.f)
    (comm : gE ≫ ψ = ψ' ≫ gA) [IsFinite ψ] [Flat ψ] (y' : ↥A'.A) :
    ψ'.finrank y' = ψ.finrank (gA.base y') :=
  Scheme.Hom.finrank_of_isPullback gE ψ' ψ gA
    (isPullback_of_isPullbackVia φ E E' gE hE A A' gA hA ψ hψ ψ' hψ' comm) y'

theorem finrank_act_eq_of_isPullbackVia {S S' : Type} [CommRing S] [CommRing S'] (φ : S →+* S')
    (E : FakeEllipticCurve Λ N S) (E' : FakeEllipticCurve Λ N S') (g : E'.A ⟶ E.A)
    (hE : FakeEllipticCurve.IsPullbackVia φ E E' g) (x : ↥Λ)
    [IsFinite (E.act x)] [Flat (E.act x)] (y' : ↥E'.A) :
    (E'.act x).finrank y' = (E.act x).finrank (g.base y') := by
  obtain ⟨hg, hmul, hact, hlev⟩ := hE
  have hE' : FakeEllipticCurve.IsPullbackVia φ E E' g := ⟨hg, hmul, hact, hlev⟩
  exact finrank_eq_of_isPullbackVia φ E E' g hE' E E' g hE' (E.act x) (E.act_over x) (E'.act x) (E'.act_over x)
    (hact x).symm y'

private theorem _root_.DEG44.finrank_eq_one_of_isIso {X Y : Scheme.{0}} (f : X ⟶ Y) [IsIso f] (y : ↥Y) : f.finrank y = 1 := by
  rw [Scheme.Hom.finrank_eq_one_of_isIso]; rfl

p2m_export "DEG44" "finrank_eq_one_of_isIso"
end FEC
p2m_reactivate "P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_exists_opens_ratioWindow_degree_laws_of_rigidifiedToG_of_bdd.Ws16WC.Clopen P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_exists_opens_ratioWindow_degree_laws_of_rigidifiedToG_of_bdd.Ws16WC.DEGb.DegreeMaps P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_exists_opens_ratioWindow_degree_laws_of_rigidifiedToG_of_bdd.Ws16WC.DEGb P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_exists_opens_ratioWindow_degree_laws_of_rigidifiedToG_of_bdd.Ws16WC"

section Unit
variable {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} {N : ℕ}

theorem one_comp_eq_specMap_comp_one {S S' : Type} [CommRing S] [CommRing S'] (φ : S →+* S')
    (A : FakeEllipticCurve Λ N S) (A' : FakeEllipticCurve Λ N S') (g : A'.A ⟶ A.A)
    (hA : FakeEllipticCurve.IsPullbackVia φ A A' g) :
    (A'.L.one (𝟙 (Spec (CommRingCat.of S')))).1 ≫ g =
      Spec.map (CommRingCat.ofHom φ) ≫ (A.L.one (𝟙 (Spec (CommRingCat.of S)))).1 := by
  obtain ⟨hg, hmul, -, -⟩ := hA
  set o' := A'.L.one (𝟙 (Spec (CommRingCat.of S'))) with ho'

  let Q : SchemeHomOver (𝟙 (Spec (CommRingCat.of S')) ≫ Spec.map (CommRingCat.ofHom φ)) A.f :=
    ⟨o'.1 ≫ g, by rw [Category.assoc, hg.w, ← Category.assoc, o'.2]⟩
  have hQQ : A.L.mul _ Q Q = Q := by
    apply Subtype.ext
    have h := hmul (𝟙 _) o' o'
    rw [A'.L.one_mul] at h
    exact h.symm

  have hQ1 : Q = A.L.one _ := by
    calc Q = A.L.mul _ (A.L.one _) Q := (A.L.one_mul _ _).symm
      _ = A.L.mul _ (A.L.mul _ (A.L.inv _ Q) Q) Q := by rw [A.L.inv_mul_cancel]
      _ = A.L.mul _ (A.L.inv _ Q) (A.L.mul _ Q Q) := by rw [A.L.mul_assoc]
      _ = A.L.mul _ (A.L.inv _ Q) Q := by rw [hQQ]
      _ = A.L.one _ := A.L.inv_mul_cancel _ _

  have hnat := A.L.one_natural (𝟙 (Spec (CommRingCat.of S)))
    (𝟙 (Spec (CommRingCat.of S')) ≫ Spec.map (CommRingCat.ofHom φ)) (Spec.map (CommRingCat.ofHom φ))
    (by rw [Category.comp_id, Category.id_comp])
  have := congrArg Subtype.val (hQ1.trans hnat.symm)
  simpa only [GoodReductionJacobian.schemeHomOverComp_coe] using this

theorem finrank_one_eq_of_isPullbackVia {S S' : Type} [CommRing S] [CommRing S'] (φ : S →+* S')
    (E : FakeEllipticCurve Λ N S) (E' : FakeEllipticCurve Λ N S') (gE : E'.A ⟶ E.A)
    (hE : FakeEllipticCurve.IsPullbackVia φ E E' gE)
    (A : FakeEllipticCurve Λ N S) (A' : FakeEllipticCurve Λ N S') (gA : A'.A ⟶ A.A)
    (hA : FakeEllipticCurve.IsPullbackVia φ A A' gA)
    (ψ : E.A ⟶ A.A) (hψ : ψ ≫ A.f = E.f) (ψ' : E'.A ⟶ A'.A) (hψ' : ψ' ≫ A'.f = E'.f)
    (comm : gE ≫ ψ = ψ' ≫ gA) [IsFinite ψ] [Flat ψ] (s' : ↥(Spec (CommRingCat.of S'))) :
    ψ'.finrank ((A'.L.one (𝟙 (Spec (CommRingCat.of S')))).1.base s') =
      ψ.finrank ((A.L.one (𝟙 (Spec (CommRingCat.of S)))).1.base ((Spec.map (CommRingCat.ofHom φ)).base s')) := by
  rw [finrank_eq_of_isPullbackVia φ E E' gE hE A A' gA hA ψ hψ ψ' hψ' comm]
  congr 1
  have h := one_comp_eq_specMap_comp_one φ A A' gA hA
  have := congrArg (fun k : Spec (CommRingCat.of S') ⟶ A.A => k.base s') h
  simpa only [Scheme.Hom.comp_base, TopCat.comp_app] using this

end Unit
p2m_reactivate "P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_exists_opens_ratioWindow_degree_laws_of_rigidifiedToG_of_bdd.Ws16WC.Clopen P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_exists_opens_ratioWindow_degree_laws_of_rigidifiedToG_of_bdd.Ws16WC.DEGb.DegreeMaps P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_exists_opens_ratioWindow_degree_laws_of_rigidifiedToG_of_bdd.Ws16WC.DEGb P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_exists_opens_ratioWindow_degree_laws_of_rigidifiedToG_of_bdd.Ws16WC"

section Rig
variable {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} {N : ℕ}
  (hΛℤ : ∀ m : ℤ, ((m : ℚ) : ℍ[ℚ, a, b]) ∈ Λ)
  {r : ℕ} [Fact r.Prime] {𝒪 : Type} [CommRing 𝒪] {π : 𝒪} {Onr : Type} [CommRing Onr] [Algebra 𝒪 Onr]
  {A₀ : FakeEllipticCurve Λ N (Onr ⧸ Ideal.span {algebraMap 𝒪 Onr π})}
  {B : Type} [CommRing B] [Algebra 𝒪 B] {ψ : Onr →ₐ[𝒪] B} {E : FakeEllipticCurve Λ N B}

include hΛℤ in

theorem isFinite_flat_φ (ρ : FakeEllipticCurve.Rigidification r π A₀ ψ E) :
    IsFinite ρ.φ ∧ Flat ρ.φ ∧ LocallyOfFinitePresentation ρ.φ ∧ Surjective ρ.φ :=
  FakeEllipticCurve.isFinite_flat_surjective_of_isIsogenyPair hΛℤ r ρ.d _ ρ.Eb ρ.Ab ρ.φ ρ.φ' ρ.isIsogenyPair

include hΛℤ in

theorem isFinite_flat_φ' (ρ : FakeEllipticCurve.Rigidification r π A₀ ψ E) :
    IsFinite ρ.φ' ∧ Flat ρ.φ' ∧ LocallyOfFinitePresentation ρ.φ' ∧ Surjective ρ.φ' :=
  FakeEllipticCurve.isFinite_flat_surjective_of_isIsogenyPair hΛℤ r ρ.d _ ρ.Ab ρ.Eb ρ.φ' ρ.φ
    (isIsogenyPair_symm _ _ _ _ _ ρ.isIsogenyPair)

include hΛℤ in

theorem Rigidification.exists_finrank_eq_of_isPullbackVia {B' : Type} [CommRing B'] [Algebra 𝒪 B'] (f : B →ₐ[𝒪] B')
    {E' : FakeEllipticCurve Λ N B'} (g : E'.A ⟶ E.A) (hE' : FakeEllipticCurve.IsPullbackVia (f : B →+* B') E E' g)
    (ρ : FakeEllipticCurve.Rigidification r π A₀ ψ E) (ρ' : FakeEllipticCurve.Rigidification r π A₀ (f.comp ψ) E')
    (h : FakeEllipticCurve.Rigidification.IsPullbackVia f g hE' ρ ρ') :
    ∃ (ub : ρ'.Eb.A ⟶ ρ.Eb.A) (uA : ρ'.Ab.A ⟶ ρ.Ab.A),
      ub ≫ ρ.gb = ρ'.gb ≫ g ∧ uA ≫ ρ.gA = ρ'.gA ∧ ρ'.d = ρ.d ∧ ub ≫ ρ.φ = ρ'.φ ≫ uA ∧
      IsPullback ub ρ'.φ ρ.φ uA ∧
      (∀ y' : ↥ρ'.Ab.A, ρ'.φ.finrank y' = ρ.φ.finrank (uA.base y')) := by
  obtain ⟨ub, uA, hEb, hgb, hAb, hgA, hd, hcomm⟩ := h
  have sq := isPullback_of_isPullbackVia _ ρ.Eb ρ'.Eb ub hEb ρ.Ab ρ'.Ab uA hAb ρ.φ ρ.φ_over ρ'.φ ρ'.φ_over hcomm
  haveI : IsFinite ρ.φ := (isFinite_flat_φ hΛℤ ρ).1
  haveI : Flat ρ.φ := (isFinite_flat_φ hΛℤ ρ).2.1
  exact ⟨ub, uA, hgb, hgA, hd, hcomm, sq, fun y' => Scheme.Hom.finrank_of_isPullback ub ρ'.φ ρ.φ uA sq y'⟩

end Rig
p2m_reactivate "P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_exists_opens_ratioWindow_degree_laws_of_rigidifiedToG_of_bdd.Ws16WC.Clopen P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_exists_opens_ratioWindow_degree_laws_of_rigidifiedToG_of_bdd.Ws16WC.DEGb.DegreeMaps P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_exists_opens_ratioWindow_degree_laws_of_rigidifiedToG_of_bdd.Ws16WC.DEGb P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_exists_opens_ratioWindow_degree_laws_of_rigidifiedToG_of_bdd.Ws16WC"

section More
variable {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} {N : ℕ}

theorem act_intCast_comm {S : Type} [CommRing S] (E : FakeEllipticCurve Λ N S) (m : ℤ)
    (hm : ((m : ℚ) : ℍ[ℚ, a, b]) ∈ Λ) (y : ↥Λ) :
    E.act y ≫ E.act ⟨((m : ℚ) : ℍ[ℚ, a, b]), hm⟩ = E.act ⟨((m : ℚ) : ℍ[ℚ, a, b]), hm⟩ ≫ E.act y := by
  have hxy : ((m : ℚ) : ℍ[ℚ, a, b]) * (y : ℍ[ℚ, a, b]) ∈ Λ := by
    rw [QuaternionAlgebra.coe_intCast, ← zsmul_eq_mul]; exact Λ.smul_mem _ y.2
  have hyx : (y : ℍ[ℚ, a, b]) * ((m : ℚ) : ℍ[ℚ, a, b]) ∈ Λ := by
    rw [← QuaternionAlgebra.coe_commutes]; exact hxy
  have hc : (⟨_, hxy⟩ : ↥Λ) = ⟨_, hyx⟩ := Subtype.ext (QuaternionAlgebra.coe_commutes _ _)
  have h1 := E.act_mul ⟨((m : ℚ) : ℍ[ℚ, a, b]), hm⟩ y hxy
  have h2 := E.act_mul y ⟨((m : ℚ) : ℍ[ℚ, a, b]), hm⟩ hyx
  rw [← h1, ← h2, hc]

theorem isIsogenyPair_act_id (hΛℤ : ∀ m : ℤ, ((m : ℚ) : ℍ[ℚ, a, b]) ∈ Λ) {S : Type} [CommRing S]
    (E : FakeEllipticCurve Λ N S) (n : ℕ) :
    FakeEllipticCurve.IsIsogenyPair n E E (E.act ⟨(((n : ℕ) : ℤ) : ℚ), hΛℤ _⟩) (𝟙 E.A) := by
  have hψ : 𝟙 E.A ≫ E.f = E.f := Category.id_comp _
  have hid : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of S)) (R : SchemeHomOver t E.f), mapPt (𝟙 E.A) hψ R = R :=
    fun t R => Subtype.ext (by simp only [mapPt_coe, Category.comp_id])
  refine ⟨E.act_over _, hψ, ?_, ?_, ?_, ?_, ?_⟩
  · intro T t P Q; exact E.act_hom _ t P Q
  · intro T t P Q; rw [hid, hid, hid]
  · intro y; exact act_intCast_comm E (n : ℤ) (hΛℤ _) y
  · intro y; simp only [Category.id_comp, Category.comp_id]
  · intro hd
    have he : (⟨(((n : ℕ) : ℤ) : ℚ), hΛℤ _⟩ : ↥Λ) = ⟨(((n : ℕ) : ℚ) : ℍ[ℚ, a, b]), hd⟩ :=
      Subtype.ext (by simp only [Int.cast_natCast])
    rw [Category.comp_id, Category.id_comp, ← he]; exact ⟨rfl, rfl⟩

theorem preconnectedSpace_primeSpectrum_of_isIdempotentElem {R : Type} [CommRing R]
    (h : ∀ e : R, IsIdempotentElem e → e = 0 ∨ e = 1) : PreconnectedSpace (PrimeSpectrum R) := by
  rw [preconnectedSpace_iff_clopen]
  intro s hs
  have hb := PrimeSpectrum.basicOpen_isIdempotentElemEquivClopens_symm (R := R) ⟨s, hs⟩
  have hbs : ((PrimeSpectrum.basicOpen ((PrimeSpectrum.isIdempotentElemEquivClopens (R := R)).symm ⟨s, hs⟩).1 :
      TopologicalSpace.Opens (PrimeSpectrum R)) : Set (PrimeSpectrum R)) = s := by rw [hb]; rfl
  rcases h _ ((PrimeSpectrum.isIdempotentElemEquivClopens (R := R)).symm ⟨s, hs⟩).2 with h0 | h1
  · left; rw [← hbs, h0]; simp
  · right; rw [← hbs, h1]; simp

theorem isIdempotentElem_quotient_of_eq_zero {T : Type} [CommRing T] (t : T) (ht : t = 0)
    (h : ∀ e : T, IsIdempotentElem e → e = 0 ∨ e = 1) :
    ∀ e : T ⧸ Ideal.span {t}, IsIdempotentElem e → e = 0 ∨ e = 1 := by
  subst ht
  intro e he
  obtain ⟨e, rfl⟩ := Ideal.Quotient.mk_surjective e
  have hmem : e * e - e ∈ Ideal.span ({0} : Set T) := by
    rw [← Ideal.Quotient.eq, map_mul]; exact he
  have hbot : Ideal.span ({0} : Set T) = ⊥ := by simp
  rw [hbot, Ideal.mem_bot, sub_eq_zero] at hmem
  rcases h e hmem with h0 | h1
  · exact Or.inl (by simp [h0])
  · exact Or.inr (by simp [h1])

theorem primeSpectrum_quotient_subsingleton {R : Type} [CommRing R] (m : Ideal R) (hm : m.IsMaximal)
    (p q : PrimeSpectrum (R ⧸ m)) : p = q := by
  have hbot : (⊥ : Ideal (R ⧸ m)).IsMaximal := (Ideal.bot_quotient_isMaximal_iff m).mpr hm
  have hp : p.asIdeal = ⊥ := (hbot.eq_of_le p.isPrime.ne_top bot_le).symm
  have hq : q.asIdeal = ⊥ := (hbot.eq_of_le q.isPrime.ne_top bot_le).symm
  exact PrimeSpectrum.ext (hp.trans hq.symm)

end More
p2m_reactivate "P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_exists_opens_ratioWindow_degree_laws_of_rigidifiedToG_of_bdd.Ws16WC.Clopen P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_exists_opens_ratioWindow_degree_laws_of_rigidifiedToG_of_bdd.Ws16WC.DEGb.DegreeMaps P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_exists_opens_ratioWindow_degree_laws_of_rigidifiedToG_of_bdd.Ws16WC.DEGb P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_exists_opens_ratioWindow_degree_laws_of_rigidifiedToG_of_bdd.Ws16WC"

end DEG44
p2m_reactivate "P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_exists_opens_ratioWindow_degree_laws_of_rigidifiedToG_of_bdd.Ws16WC.Clopen P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_exists_opens_ratioWindow_degree_laws_of_rigidifiedToG_of_bdd.Ws16WC.DEGb.DegreeMaps P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_exists_opens_ratioWindow_degree_laws_of_rigidifiedToG_of_bdd.Ws16WC.DEGb P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_exists_opens_ratioWindow_degree_laws_of_rigidifiedToG_of_bdd.Ws16WC"

namespace CerednikDrinfeld
p2m_export "CerednikDrinfeld" "QM.FakeEllipticCurve FormalOmega.AlgFunctor tree Zp2 FormalODModule FormalODModule.IsIsogenyOfHeight CosetGraph.awayUnits HeckeTower.AwayPrime meetOrder levelHeckeUSet QM.FakeEllipticCurve.Rigidification QM.FakeEllipticCurve.Rigidification.finrank_mul_finrank_act_pow_eq_of_corr QM.FakeEllipticCurve.isLocallyConstant_finrank_one QM.FakeEllipticCurve.isFinite_flat_surjective_of_isIsogenyPair QM.FakeEllipticCurve.Rigidification.comp_phi_comp_eq_phi_of_comp_act_pow_eq"
namespace QM
p2m_export "CerednikDrinfeld.QM" "IsCoarseModuli IsCoarseModuliT FakeEllipticCurve.WithExtraLevel FakeEllipticCurve.IsLevelIsogeny FakeEllipticCurve.IsAtkinLehnerQuotient mapPt mapPt_coe pushPt FakeEllipticCurve FakeEllipticCurve.FullLevel FakeEllipticCurve.WithFullLevel IsFineModuli IsLevelTwistAction FakeEllipticCurve.WithFullLevel.IsoVia IsOrderCoord FakeEllipticCurve.IsPullbackVia FakeEllipticCurve.IsoVia FakeEllipticCurve.IsAtkinLehnerQuotientVia FakeEllipticCurve.Rigidification FakeEllipticCurve.Rigidification.IsTranslateBy FakeEllipticCurve.Rigidification.IsPullbackVia FakeEllipticCurve.Rigidification.IsRigTransport FakeEllipticCurve.RigidifiedCurve FakeEllipticCurve.IsIsogenyPair FakeEllipticCurve.PreservesLevel FakeEllipticCurve.Rigidification.finrank_mul_finrank_act_pow_eq_of_corr FakeEllipticCurve.one_lt_finrank_act_pow_of_isFinite_of_flat FakeEllipticCurve.isLocallyConstant_finrank_one FakeEllipticCurve.isFinite_flat_surjective_of_isIsogenyPair FakeEllipticCurve.Rigidification.comp_phi_comp_eq_phi_of_comp_act_pow_eq FakeEllipticCurve.exists_isPullback_levelIff FakeEllipticCurve.FullLevel.exists_comp_eq_specMap_comp_of_isPullbackVia FakeEllipticCurve.Rigidification.exists_isPullbackVia_of_isPullbackVia"
namespace FakeEllipticCurve
p2m_export "CerednikDrinfeld.QM.FakeEllipticCurve" "WithExtraLevel IsLevelIsogeny IsAtkinLehnerQuotient IsPullback A f mk act_hom comm act act_one L act_mul C act_over FullLevel WithFullLevel WithFullLevel.IsoVia IsPullbackVia IsFormalModuleVia IsoVia IsAtkinLehnerQuotientVia Rigidification Rigidification.IsTranslateBy Rigidification.IsPullbackVia Rigidification.IsRigTransport RigidifiedCurve IsIsogenyPair PreservesLevel Rigidification.finrank_mul_finrank_act_pow_eq_of_corr one_lt_finrank_act_pow_of_isFinite_of_flat isLocallyConstant_finrank_one isFinite_flat_surjective_of_isIsogenyPair Rigidification.comp_phi_comp_eq_phi_of_comp_act_pow_eq exists_isPullback_levelIff FullLevel.exists_comp_eq_specMap_comp_of_isPullbackVia Rigidification.exists_isPullbackVia_of_isPullbackVia"
namespace Rigidification
p2m_export "CerednikDrinfeld.QM.FakeEllipticCurve.Rigidification" "IsTranslateBy IsPullbackVia IsRigTransport φ' isIsogenyPair mk Eb d Ab φ isPullback_Ab gA φ_over gb finrank_mul_finrank_act_pow_eq_of_corr comp_phi_comp_eq_phi_of_comp_act_pow_eq exists_isPullbackVia_of_isPullbackVia"
namespace W7Aux
p2m_open "CerednikDrinfeld.QM.FakeEllipticCurve.Rigidification CerednikDrinfeld.QM.FakeEllipticCurve CerednikDrinfeld.QM CerednikDrinfeld"

universe u

theorem finrank_morphismRestrict {X Y : Scheme.{u}} (f : X ⟶ Y) [IsFinite f] [Flat f] (U : Y.Opens) (y : ↥U) :
    (f ∣_ U).finrank y = f.finrank y.1 := by
  rw [Scheme.Hom.finrank_of_isPullback _ _ _ _ (isPullback_morphismRestrict f U).flip y]
  rfl

theorem finrank_comp_of_finrank_eq_on {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    [IsFinite f] [Flat f] [IsFinite g] [Flat g]
    (W : Z.Opens) (m : ℕ) (hf : ∀ y : ↥Y, g.base y ∈ W → f.finrank y = m) (z : ↥Z) (hz : z ∈ W) :
    (f ≫ g).finrank z = m * g.finrank z := by
  have sq : CategoryTheory.IsPullback (f ⁻¹ᵁ (g ⁻¹ᵁ W)).ι (f ∣_ (g ⁻¹ᵁ W) ≫ g ∣_ W) (f ≫ g) W.ι :=
    (isPullback_morphismRestrict f (g ⁻¹ᵁ W)).flip.paste_vert (isPullback_morphismRestrict g W).flip
  have h3 : ∀ v : ↥(g ⁻¹ᵁ W), (f ∣_ (g ⁻¹ᵁ W)).finrank v = m := fun v =>
    (finrank_morphismRestrict f _ v).trans (hf _ v.2)
  have key := Scheme.Hom.finrank_comp_of_finrank_eq_const (f ∣_ (g ⁻¹ᵁ W)) (g ∣_ W) m h3 ⟨z, hz⟩
  rw [Scheme.Hom.finrank_of_isPullback _ _ _ _ sq, finrank_morphismRestrict] at key
  exact key

theorem isIso_of_isPullback_of_isIso {P X Y Z : Scheme.{u}} (fst : P ⟶ X) (snd : P ⟶ Y) (f : X ⟶ Z) (g : Y ⟶ Z)
    (h : CategoryTheory.IsPullback fst snd f g) [IsIso g] : IsIso fst := by
  refine ⟨⟨h.lift (𝟙 X) (f ≫ inv g) (by simp), ?_, by simp⟩⟩
  apply h.hom_ext
  · simp
  · simp only [Category.assoc, IsPullback.lift_snd, Category.id_comp]
    rw [← cancel_mono g, Category.assoc, Category.assoc, IsIso.inv_hom_id, Category.comp_id, h.w]

variable {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} {N : ℕ} {S : Type} [CommRing S]

theorem act_rpow_zero (hΛℤ : ∀ m : ℤ, ((m : ℚ) : ℍ[ℚ, a, b]) ∈ Λ) (A : FakeEllipticCurve Λ N S) (r : ℕ) :
    A.act ⟨(((r ^ 0 : ℕ) : ℤ) : ℚ), hΛℤ _⟩ = 𝟙 A.A := by
  have h1 : (1 : ℍ[ℚ, a, b]) ∈ Λ := by exact_mod_cast hΛℤ 1
  rw [← A.act_one h1]
  congr 1 <;> first | rfl | exact Subtype.ext (by push_cast; norm_num)

theorem act_rpow_succ (hΛℤ : ∀ m : ℤ, ((m : ℚ) : ℍ[ℚ, a, b]) ∈ Λ) (A : FakeEllipticCurve Λ N S) (r k : ℕ) :
    A.act ⟨(((r ^ (k + 1) : ℕ) : ℤ) : ℚ), hΛℤ _⟩ =
      A.act ⟨(((r ^ k : ℕ) : ℤ) : ℚ), hΛℤ _⟩ ≫ A.act ⟨(((r ^ 1 : ℕ) : ℤ) : ℚ), hΛℤ _⟩ := by
  have hmem : ((((r ^ 1 : ℕ) : ℤ) : ℚ) : ℍ[ℚ, a, b]) * ((((r ^ k : ℕ) : ℤ) : ℚ) : ℍ[ℚ, a, b]) ∈ Λ := by
    rw [← coe_mul]; exact_mod_cast hΛℤ ((r ^ 1 : ℕ) * (r ^ k : ℕ) : ℕ)
  rw [← A.act_mul ⟨_, hΛℤ _⟩ ⟨_, hΛℤ _⟩ hmem]
  congr 1
  apply Subtype.ext
  show ((((r ^ (k + 1) : ℕ) : ℤ) : ℚ) : ℍ[ℚ, a, b]) = (((r ^ 1 : ℕ) : ℤ) : ℚ) * ((((r ^ k : ℕ) : ℤ) : ℚ) : ℍ[ℚ, a, b])
  rw [← coe_mul]
  congr 1
  push_cast
  ring

theorem act_comm_act_rpow (hΛℤ : ∀ m : ℤ, ((m : ℚ) : ℍ[ℚ, a, b]) ∈ Λ) (A : FakeEllipticCurve Λ N S) (r k : ℕ) (x : ↥Λ) :
    A.act x ≫ A.act ⟨(((r ^ k : ℕ) : ℤ) : ℚ), hΛℤ _⟩ = A.act ⟨(((r ^ k : ℕ) : ℤ) : ℚ), hΛℤ _⟩ ≫ A.act x := by
  have hmem : ((((r ^ k : ℕ) : ℤ) : ℚ) : ℍ[ℚ, a, b]) * (x : ℍ[ℚ, a, b]) ∈ Λ := by
    rw [coe_mul_eq_smul, Int.cast_smul_eq_zsmul]
    exact Λ.smul_mem _ x.2
  have hmem' : (x : ℍ[ℚ, a, b]) * ((((r ^ k : ℕ) : ℤ) : ℚ) : ℍ[ℚ, a, b]) ∈ Λ := by
    rw [← coe_commutes]; exact hmem
  rw [← A.act_mul _ _ hmem, ← A.act_mul _ _ hmem']
  congr 1
  exact Subtype.ext (coe_commutes _ _)

theorem isIsogenyPair_act_rpow (hΛℤ : ∀ m : ℤ, ((m : ℚ) : ℍ[ℚ, a, b]) ∈ Λ) (A : FakeEllipticCurve Λ N S) (r k : ℕ) :
    FakeEllipticCurve.IsIsogenyPair (r ^ (2 * k)) A A
      (A.act ⟨(((r ^ k : ℕ) : ℤ) : ℚ), hΛℤ _⟩) (A.act ⟨(((r ^ k : ℕ) : ℤ) : ℚ), hΛℤ _⟩) := by
  refine ⟨A.act_over _, A.act_over _, fun t P Q => A.act_hom _ t P Q, fun t P Q => A.act_hom _ t P Q,
    fun x => act_comm_act_rpow hΛℤ A r k x, fun x => act_comm_act_rpow hΛℤ A r k x, fun hd => ?_⟩
  have hmem : ((((r ^ k : ℕ) : ℤ) : ℚ) : ℍ[ℚ, a, b]) * ((((r ^ k : ℕ) : ℤ) : ℚ) : ℍ[ℚ, a, b]) ∈ Λ := by
    rw [← coe_mul]; exact_mod_cast hΛℤ ((r ^ k : ℕ) * (r ^ k : ℕ) : ℕ)
  have heq : A.act ⟨(((r ^ k : ℕ) : ℤ) : ℚ), hΛℤ _⟩ ≫ A.act ⟨(((r ^ k : ℕ) : ℤ) : ℚ), hΛℤ _⟩ =
      A.act ⟨((r ^ (2 * k) : ℕ) : ℚ), hd⟩ := by
    rw [← A.act_mul _ _ hmem]
    congr 1
    apply Subtype.ext
    show (((r ^ k : ℕ) : ℤ) : ℚ) * ((((r ^ k : ℕ) : ℤ) : ℚ) : ℍ[ℚ, a, b]) = (((r ^ (2 * k) : ℕ) : ℚ) : ℍ[ℚ, a, b])
    rw [← coe_mul]
    congr 1
    push_cast
    ring
  exact ⟨heq, heq⟩

end CerednikDrinfeld.QM.FakeEllipticCurve.Rigidification.W7Aux
p2m_reactivate "P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_exists_opens_ratioWindow_degree_laws_of_rigidifiedToG_of_bdd.Ws16WC.Clopen P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_exists_opens_ratioWindow_degree_laws_of_rigidifiedToG_of_bdd.Ws16WC.DEGb.DegreeMaps P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_exists_opens_ratioWindow_degree_laws_of_rigidifiedToG_of_bdd.Ws16WC.DEGb P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_exists_opens_ratioWindow_degree_laws_of_rigidifiedToG_of_bdd.Ws16WC"
p2m_reactivate "P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_exists_opens_ratioWindow_degree_laws_of_rigidifiedToG_of_bdd.Ws16WC.Clopen P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_exists_opens_ratioWindow_degree_laws_of_rigidifiedToG_of_bdd.Ws16WC.DEGb.DegreeMaps P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_exists_opens_ratioWindow_degree_laws_of_rigidifiedToG_of_bdd.Ws16WC.DEGb P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_exists_opens_ratioWindow_degree_laws_of_rigidifiedToG_of_bdd.Ws16WC"
p2m_reactivate "P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_exists_opens_ratioWindow_degree_laws_of_rigidifiedToG_of_bdd.Ws16WC.Clopen P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_exists_opens_ratioWindow_degree_laws_of_rigidifiedToG_of_bdd.Ws16WC.DEGb.DegreeMaps P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_exists_opens_ratioWindow_degree_laws_of_rigidifiedToG_of_bdd.Ws16WC.DEGb P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_exists_opens_ratioWindow_degree_laws_of_rigidifiedToG_of_bdd.Ws16WC"
p2m_reactivate "P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_exists_opens_ratioWindow_degree_laws_of_rigidifiedToG_of_bdd.Ws16WC.Clopen P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_exists_opens_ratioWindow_degree_laws_of_rigidifiedToG_of_bdd.Ws16WC.DEGb.DegreeMaps P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_exists_opens_ratioWindow_degree_laws_of_rigidifiedToG_of_bdd.Ws16WC.DEGb P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_exists_opens_ratioWindow_degree_laws_of_rigidifiedToG_of_bdd.Ws16WC"
p2m_reactivate "P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_exists_opens_ratioWindow_degree_laws_of_rigidifiedToG_of_bdd.Ws16WC.Clopen P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_exists_opens_ratioWindow_degree_laws_of_rigidifiedToG_of_bdd.Ws16WC.DEGb.DegreeMaps P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_exists_opens_ratioWindow_degree_laws_of_rigidifiedToG_of_bdd.Ws16WC.DEGb P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_exists_opens_ratioWindow_degree_laws_of_rigidifiedToG_of_bdd.Ws16WC"

namespace DEG2
p2m_open "CerednikDrinfeld.QM.FakeEllipticCurve.Rigidification P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_exists_opens_ratioWindow_degree_laws_of_rigidifiedToG_of_bdd.CerednikDrinfeld.QM.FakeEllipticCurve.Rigidification"

variable {r N : ℕ} [Fact r.Prime] {𝒪 : Type} [CommRing 𝒪] {π : 𝒪} {Onr : Type} [CommRing Onr] [Algebra 𝒪 Onr]
  {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]}

theorem finrank_φ'_mul_finrank_φ_eq_pow (hΛℤ : ∀ m : ℤ, ((m : ℚ) : ℍ[ℚ, a, b]) ∈ Λ)
    (A₀ : FakeEllipticCurve Λ N (Onr ⧸ Ideal.span {algebraMap 𝒪 Onr π}))
    (L : Type) [CommRing L] [Algebra 𝒪 L] (ψL : Onr →ₐ[𝒪] L) (E : FakeEllipticCurve Λ N L)
    (ϱ : FakeEllipticCurve.Rigidification r π A₀ ψL E) (y : ↥ϱ.Ab.A) :
    ϱ.φ'.finrank ((ϱ.Eb.L.one (𝟙 (Spec (CommRingCat.of (L ⧸ Ideal.span {algebraMap 𝒪 L π}))))).1.base (ϱ.Ab.f.base y)) *
        ϱ.φ.finrank y =
      ((ϱ.Ab.act ⟨(((r ^ 1 : ℕ) : ℤ) : ℚ), hΛℤ _⟩).finrank y) ^ ϱ.d := by
  classical
  obtain ⟨hφfin, hφfl, hφlfp, -⟩ := FakeEllipticCurve.isFinite_flat_surjective_of_isIsogenyPair hΛℤ r ϱ.d _
    ϱ.Eb ϱ.Ab ϱ.φ ϱ.φ' ϱ.isIsogenyPair

  have hpair' : FakeEllipticCurve.IsIsogenyPair (r ^ ϱ.d) ϱ.Ab ϱ.Eb ϱ.φ' ϱ.φ := by
    obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := ϱ.isIsogenyPair
    exact ⟨h2, h1, h4, h3, h6, h5, fun hd => ⟨(h7 hd).2, (h7 hd).1⟩⟩
  obtain ⟨hφ'fin, hφ'fl, hφ'lfp, -⟩ := FakeEllipticCurve.isFinite_flat_surjective_of_isIsogenyPair hΛℤ r ϱ.d _
    ϱ.Ab ϱ.Eb ϱ.φ' ϱ.φ hpair'
  have hr : ∀ k : ℕ, IsFinite (ϱ.Ab.act ⟨(((r ^ k : ℕ) : ℤ) : ℚ), hΛℤ _⟩) ∧ Flat (ϱ.Ab.act ⟨(((r ^ k : ℕ) : ℤ) : ℚ), hΛℤ _⟩) ∧
      LocallyOfFinitePresentation (ϱ.Ab.act ⟨(((r ^ k : ℕ) : ℤ) : ℚ), hΛℤ _⟩) := fun k =>
    let h := FakeEllipticCurve.isFinite_flat_surjective_of_isIsogenyPair hΛℤ r (2 * k) _ ϱ.Ab ϱ.Ab _ _
      (W7Aux.isIsogenyPair_act_rpow hΛℤ ϱ.Ab r k)
    ⟨h.1, h.2.1, h.2.2.1⟩
  haveI := (hr 1).1; haveI := (hr 1).2.1; haveI := (hr 1).2.2

  obtain ⟨hφ'over, -⟩ := hpair'

  obtain ⟨hm1, hm2⟩ := FakeEllipticCurve.isLocallyConstant_finrank_one _ ϱ.Ab ϱ.Eb ϱ.φ' hφ'over
  obtain ⟨hc1, hc2⟩ := FakeEllipticCurve.isLocallyConstant_finrank_one _ ϱ.Ab ϱ.Ab
    (ϱ.Ab.act ⟨(((r ^ 1 : ℕ) : ℤ) : ℚ), hΛℤ _⟩) (ϱ.Ab.act_over _)
  obtain ⟨nm, hnm⟩ : ∃ n : ↥(Spec (CommRingCat.of (L ⧸ Ideal.span {algebraMap 𝒪 L π}))) → ℕ,
      n = fun t => ϱ.φ'.finrank ((ϱ.Eb.L.one (𝟙 (Spec (CommRingCat.of (L ⧸ Ideal.span {algebraMap 𝒪 L π}))))).1.base t) := ⟨_, rfl⟩
  obtain ⟨nc, hnc⟩ : ∃ n : ↥(Spec (CommRingCat.of (L ⧸ Ideal.span {algebraMap 𝒪 L π}))) → ℕ,
      n = fun t => (ϱ.Ab.act ⟨(((r ^ 1 : ℕ) : ℤ) : ℚ), hΛℤ _⟩).finrank
        ((ϱ.Ab.L.one (𝟙 (Spec (CommRingCat.of (L ⧸ Ideal.span {algebraMap 𝒪 L π}))))).1.base t) := ⟨_, rfl⟩
  rw [← hnm] at hm2; rw [← hnc] at hc2
  have em : ∀ w, ϱ.φ'.finrank w = nm (ϱ.Eb.f.base w) := fun w => by rw [hnm]; exact hm1 w
  have ec : ∀ z, (ϱ.Ab.act ⟨(((r ^ 1 : ℕ) : ℤ) : ℚ), hΛℤ _⟩).finrank z = nc (ϱ.Ab.f.base z) := fun z => by
    rw [hnc]; exact hc1 z
  have hact : ∀ (x : ↥Λ) (z : ↥ϱ.Ab.A), ϱ.Ab.f.base ((ϱ.Ab.act x).base z) = ϱ.Ab.f.base z := fun x z => by
    have h2 := congrArg (fun h => h.base z) (ϱ.Ab.act_over x)
    simpa using h2
  have hφbase : ∀ w : ↥ϱ.Eb.A, ϱ.Ab.f.base (ϱ.φ.base w) = ϱ.Eb.f.base w := fun w => by
    have h2 := congrArg (fun h => h.base w) ϱ.φ_over
    simpa using h2
  obtain ⟨s, hs⟩ : ∃ s, s = ϱ.Ab.f.base y := ⟨_, rfl⟩
  let U : (Spec (CommRingCat.of (L ⧸ Ideal.span {algebraMap 𝒪 L π}))).Opens :=
    ⟨nm ⁻¹' {nm s} ∩ nc ⁻¹' {nc s}, (hm2 _).inter (hc2 _)⟩
  have hyU : ϱ.Ab.f.base y ∈ U := by rw [← hs]; exact ⟨rfl, rfl⟩

  have hpow : ∀ (j : ℕ) (z : ↥ϱ.Ab.A), ϱ.Ab.f.base z ∈ U →
      (ϱ.Ab.act ⟨(((r ^ j : ℕ) : ℤ) : ℚ), hΛℤ _⟩).finrank z = nc s ^ j := by
    intro j
    induction j with
    | zero =>
      intro z _
      rw [W7Aux.act_rpow_zero hΛℤ ϱ.Ab r, Scheme.Hom.finrank_eq_one_of_isIso, pow_zero]
      rfl
    | succ j ih =>
      intro z hz
      haveI := (hr j).1; haveI := (hr j).2.1
      rw [W7Aux.act_rpow_succ hΛℤ ϱ.Ab r j,
        W7Aux.finrank_comp_of_finrank_eq_on _ _ (ϱ.Ab.f ⁻¹ᵁ U) (nc s ^ j) ?_ z hz, ec z, pow_succ (nc s) j]
      · have h3 : nc (ϱ.Ab.f.base z) = nc s := hz.2
        rw [h3]
      · intro w hw
        apply ih
        have hw' : ϱ.Ab.f.base ((ϱ.Ab.act ⟨(((r ^ 1 : ℕ) : ℤ) : ℚ), hΛℤ _⟩).base w) ∈ U := hw
        rwa [hact] at hw'

  haveI := hφ'fin; haveI := hφ'fl; haveI := hφfin; haveI := hφfl
  have hL : (ϱ.φ' ≫ ϱ.φ).finrank y = nm s * ϱ.φ.finrank y := by
    rw [W7Aux.finrank_comp_of_finrank_eq_on ϱ.φ' ϱ.φ (ϱ.Ab.f ⁻¹ᵁ U) (nm s) ?_ y hyU]
    intro w hw
    have hw' : ϱ.Ab.f.base (ϱ.φ.base w) ∈ U := hw
    rw [hφbase] at hw'
    rw [em w]
    exact hw'.1

  have hd : (((r ^ ϱ.d : ℕ) : ℚ) : ℍ[ℚ, a, b]) ∈ Λ := by exact_mod_cast hΛℤ (r ^ ϱ.d : ℕ)
  obtain ⟨-, -, -, -, -, -, h7⟩ := ϱ.isIsogenyPair
  have hcomp : ϱ.φ' ≫ ϱ.φ = ϱ.Ab.act ⟨(((r ^ ϱ.d : ℕ) : ℤ) : ℚ), hΛℤ _⟩ := by
    rw [(h7 hd).2]
    congr 1
    all_goals exact Subtype.ext (by push_cast)
  have key : (ϱ.φ' ≫ ϱ.φ).finrank y = nc s ^ ϱ.d := by rw [hcomp]; exact hpow ϱ.d y hyU
  rw [hL] at key
  have hsec : ∀ t, ϱ.Eb.f.base (((ϱ.Eb.L.one (𝟙 _))).1.base t) = t := fun t => by
    have h2 := congrArg (fun h => h.base t) (ϱ.Eb.L.one (𝟙 (Spec (CommRingCat.of (L ⧸ Ideal.span {algebraMap 𝒪 L π}))))).2
    simpa using h2
  rw [em, hsec, ec y, ← hs]
  exact key

theorem finrank_φ'_mul_pow_eq_of_corr (hΛℤ : ∀ m : ℤ, ((m : ℚ) : ℍ[ℚ, a, b]) ∈ Λ)
    (A₀ : FakeEllipticCurve Λ N (Onr ⧸ Ideal.span {algebraMap 𝒪 Onr π}))
    (L : Type) [CommRing L] [Algebra 𝒪 L] (ψL : Onr →ₐ[𝒪] L) (E E' : FakeEllipticCurve Λ N L)
    (ϱ : FakeEllipticCurve.Rigidification r π A₀ ψL E) (ϱ' : FakeEllipticCurve.Rigidification r π A₀ ψL E')
    (hd : ϱ'.d = ϱ.d)
    (i₀ : E.A ≅ E'.A) (hi : i₀.hom ≫ E'.f = E.f)
    (ib : ϱ.Eb.A ⟶ ϱ'.Eb.A) (hib : ib ≫ ϱ'.gb = ϱ.gb ≫ i₀.hom) (hibf : ib ≫ ϱ'.Eb.f = ϱ.Eb.f)
    (uA : ϱ'.Ab.A ⟶ ϱ.Ab.A) (huA : FakeEllipticCurve.IsPullbackVia (RingHom.id _) ϱ.Ab ϱ'.Ab uA) (huAg : uA ≫ ϱ.gA = ϱ'.gA)
    (i₁ j₁ : ℕ)
    (hrel : ib ≫ ϱ'.φ ≫ uA ≫ ϱ.Ab.act ⟨(((r ^ i₁ : ℕ) : ℤ) : ℚ), hΛℤ _⟩ = ϱ.φ ≫ ϱ.Ab.act ⟨(((r ^ j₁ : ℕ) : ℤ) : ℚ), hΛℤ _⟩)
    (y' : ↥ϱ'.Ab.A) :
    ϱ'.φ'.finrank ((ϱ'.Eb.L.one (𝟙 (Spec (CommRingCat.of (L ⧸ Ideal.span {algebraMap 𝒪 L π}))))).1.base (ϱ'.Ab.f.base y')) *
        ((ϱ.Ab.act ⟨(((r ^ 1 : ℕ) : ℤ) : ℚ), hΛℤ _⟩).finrank (uA.base y')) ^ j₁ =
      ϱ.φ'.finrank ((ϱ.Eb.L.one (𝟙 (Spec (CommRingCat.of (L ⧸ Ideal.span {algebraMap 𝒪 L π}))))).1.base (ϱ.Ab.f.base (uA.base y'))) *
        ((ϱ.Ab.act ⟨(((r ^ 1 : ℕ) : ℤ) : ℚ), hΛℤ _⟩).finrank (uA.base y')) ^ i₁ := by
  classical
  have hr1 := FakeEllipticCurve.isFinite_flat_surjective_of_isIsogenyPair hΛℤ r (2 * 1) _ ϱ.Ab ϱ.Ab _ _
      (W7Aux.isIsogenyPair_act_rpow hΛℤ ϱ.Ab r 1)
  haveI := hr1.1; haveI := hr1.2.1; haveI := hr1.2.2.1
  have P := finrank_φ'_mul_finrank_φ_eq_pow hΛℤ A₀ L ψL E ϱ (uA.base y')
  have P' := finrank_φ'_mul_finrank_φ_eq_pow hΛℤ A₀ L ψL E' ϱ' y'
  have hc' : (ϱ'.Ab.act ⟨(((r ^ 1 : ℕ) : ℤ) : ℚ), hΛℤ _⟩).finrank y' = (ϱ.Ab.act ⟨(((r ^ 1 : ℕ) : ℤ) : ℚ), hΛℤ _⟩).finrank (uA.base y') :=
    DEG44.finrank_act_eq_of_isPullbackVia _ ϱ.Ab ϱ'.Ab uA huA ⟨(((r ^ 1 : ℕ) : ℤ) : ℚ), hΛℤ _⟩ y'
  have SL := CerednikDrinfeld.QM.FakeEllipticCurve.Rigidification.finrank_mul_finrank_act_pow_eq_of_corr 𝒪 π Onr Λ hΛℤ A₀
    L ψL E E' ϱ ϱ' i₀ hi ib hib hibf uA huA huAg i₁ j₁ hrel y'
  have hc0 : 0 < (ϱ.Ab.act ⟨(((r ^ 1 : ℕ) : ℤ) : ℚ), hΛℤ _⟩).finrank (uA.base y') :=
    lt_trans Nat.zero_lt_one
      (FakeEllipticCurve.one_lt_finrank_act_pow_of_isFinite_of_flat hΛℤ r _ ϱ.Ab 1 Nat.one_pos hr1.1 hr1.2.1 _)
  rw [hc', hd] at P'

  generalize hm : ϱ.φ'.finrank _ = m at P ⊢
  generalize hm' : ϱ'.φ'.finrank _ = m' at P' ⊢
  generalize hn : ϱ.φ.finrank (uA.base y') = n at P SL
  generalize hn' : ϱ'.φ.finrank y' = n' at P' SL
  generalize hc : (ϱ.Ab.act ⟨(((r ^ 1 : ℕ) : ℤ) : ℚ), hΛℤ _⟩).finrank (uA.base y') = c at P P' SL hc0 ⊢
  have key : (m' * c ^ j₁) * c ^ ϱ.d = (m * c ^ i₁) * c ^ ϱ.d := by
    calc (m' * c ^ j₁) * c ^ ϱ.d = (m' * c ^ j₁) * (m * n) := by rw [P]
      _ = m * m' * (n * c ^ j₁) := by ring
      _ = m * m' * (n' * c ^ i₁) := by rw [SL]
      _ = (m * c ^ i₁) * (m' * n') := by ring
      _ = (m * c ^ i₁) * c ^ ϱ.d := by rw [P']
  exact Nat.eq_of_mul_eq_mul_right (pow_pos hc0 _) key

end DEG2
p2m_reactivate "P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_exists_opens_ratioWindow_degree_laws_of_rigidifiedToG_of_bdd.Ws16WC.Clopen P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_exists_opens_ratioWindow_degree_laws_of_rigidifiedToG_of_bdd.Ws16WC.DEGb.DegreeMaps P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_exists_opens_ratioWindow_degree_laws_of_rigidifiedToG_of_bdd.Ws16WC.DEGb P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_exists_opens_ratioWindow_degree_laws_of_rigidifiedToG_of_bdd.Ws16WC"

namespace DEG
p2m_open "CerednikDrinfeld.QM.FakeEllipticCurve.Rigidification P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_exists_opens_ratioWindow_degree_laws_of_rigidifiedToG_of_bdd.CerednikDrinfeld.QM.FakeEllipticCurve.Rigidification"

variable {r N : ℕ} [Fact r.Prime] {𝒪 : Type} [CommRing 𝒪] {π : 𝒪} {Onr : Type} [CommRing Onr] [Algebra 𝒪 Onr]
  {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]}

noncomputable def cdeg (hΛℤ : ∀ m : ℤ, ((m : ℚ) : ℍ[ℚ, a, b]) ∈ Λ)
    (A₀ : FakeEllipticCurve Λ N (Onr ⧸ Ideal.span {algebraMap 𝒪 Onr π})) : ℕ :=
  by
    classical
    exact if h : Nonempty ↥A₀.A then (A₀.act ⟨(((r ^ 1 : ℕ) : ℤ) : ℚ), hΛℤ _⟩).finrank (Classical.choice h) else 2

noncomputable def degφ (A₀ : FakeEllipticCurve Λ N (Onr ⧸ Ideal.span {algebraMap 𝒪 Onr π}))
    (T : Type) [CommRing T] [Algebra 𝒪 T] (ψT : Onr →ₐ[𝒪] T) (E : FakeEllipticCurve Λ N T)
    (ρ : FakeEllipticCurve.Rigidification r π A₀ ψT E) : ℕ :=
  by
    classical
    exact if h : Nonempty ↥ρ.Ab.A then ρ.φ.finrank (Classical.choice h) else 0

noncomputable def degφ' (A₀ : FakeEllipticCurve Λ N (Onr ⧸ Ideal.span {algebraMap 𝒪 Onr π}))
    (T : Type) [CommRing T] [Algebra 𝒪 T] (ψT : Onr →ₐ[𝒪] T) (E : FakeEllipticCurve Λ N T)
    (ρ : FakeEllipticCurve.Rigidification r π A₀ ψT E) : ℕ :=
  by
    classical
    exact if h : Nonempty ↥ρ.Eb.A then ρ.φ'.finrank (Classical.choice h) else 0

theorem one_lt_cdeg (hΛℤ : ∀ m : ℤ, ((m : ℚ) : ℍ[ℚ, a, b]) ∈ Λ)
    (A₀ : FakeEllipticCurve Λ N (Onr ⧸ Ideal.span {algebraMap 𝒪 Onr π})) : 1 < cdeg (r := r) hΛℤ A₀ := by
  classical
  unfold cdeg
  split_ifs with h
  · obtain ⟨hfin, hfl, -, -⟩ := FakeEllipticCurve.isFinite_flat_surjective_of_isIsogenyPair hΛℤ r 1 _ A₀ A₀ _ _
      (DEG44.isIsogenyPair_act_id hΛℤ A₀ (r ^ 1))
    exact FakeEllipticCurve.one_lt_finrank_act_pow_of_isFinite_of_flat hΛℤ r _ A₀ 1 Nat.one_pos hfin hfl _
  · exact Nat.one_lt_two

theorem finrank_act_Ab_eq_cdeg (hΛℤ : ∀ m : ℤ, ((m : ℚ) : ℍ[ℚ, a, b]) ∈ Λ)
    (hOnr_max : (Ideal.span {algebraMap 𝒪 Onr π}).IsMaximal)
    (A₀ : FakeEllipticCurve Λ N (Onr ⧸ Ideal.span {algebraMap 𝒪 Onr π}))
    (T : Type) [CommRing T] [Algebra 𝒪 T] (ψT : Onr →ₐ[𝒪] T) (E : FakeEllipticCurve Λ N T)
    (ρ : FakeEllipticCurve.Rigidification r π A₀ ψT E) (y : ↥ρ.Ab.A) :
    (ρ.Ab.act ⟨(((r ^ 1 : ℕ) : ℤ) : ℚ), hΛℤ _⟩).finrank y = cdeg (r := r) hΛℤ A₀ := by
  classical
  obtain ⟨hfin, hfl, hlfp, -⟩ := FakeEllipticCurve.isFinite_flat_surjective_of_isIsogenyPair hΛℤ r 1 _ A₀ A₀ _ _
    (DEG44.isIsogenyPair_act_id hΛℤ A₀ (r ^ 1))
  haveI := hfin; haveI := hfl; haveI := hlfp
  have h1 := DEG44.finrank_act_eq_of_isPullbackVia _ A₀ ρ.Ab ρ.gA ρ.isPullback_Ab ⟨(((r ^ 1 : ℕ) : ℤ) : ℚ), hΛℤ _⟩ y
  have hne : Nonempty ↥A₀.A := ⟨ρ.gA.base y⟩
  unfold cdeg
  rw [dif_pos hne, h1]
  obtain ⟨hc1, -⟩ := FakeEllipticCurve.isLocallyConstant_finrank_one _ A₀ A₀
    (A₀.act ⟨(((r ^ 1 : ℕ) : ℤ) : ℚ), hΛℤ _⟩) (A₀.act_over _)
  rw [hc1 (ρ.gA.base y), hc1 (Classical.choice hne)]
  have hpt : A₀.f.base (ρ.gA.base y) = A₀.f.base (Classical.choice hne) :=
    DEG44.primeSpectrum_quotient_subsingleton _ hOnr_max _ _
  rw [hpt]

theorem finrank_φ_eq (hΛℤ : ∀ m : ℤ, ((m : ℚ) : ℍ[ℚ, a, b]) ∈ Λ)
    (A₀ : FakeEllipticCurve Λ N (Onr ⧸ Ideal.span {algebraMap 𝒪 Onr π}))
    (T : Type) [CommRing T] [IsNoetherianRing T] [Algebra 𝒪 T] (hTc : ∀ e : T, IsIdempotentElem e → e = 0 ∨ e = 1)
    (h0 : algebraMap 𝒪 T π = 0)
    (ψT : Onr →ₐ[𝒪] T) (E : FakeEllipticCurve Λ N T)
    (ρ : FakeEllipticCurve.Rigidification r π A₀ ψT E) (y y' : ↥ρ.Ab.A) :
    ρ.φ.finrank y = ρ.φ.finrank y' := by
  obtain ⟨hfin, hfl, hlfp, -⟩ := DEG44.isFinite_flat_φ hΛℤ ρ
  haveI := hfin; haveI := hfl; haveI := hlfp
  obtain ⟨h1, h2⟩ := FakeEllipticCurve.isLocallyConstant_finrank_one _ ρ.Eb ρ.Ab ρ.φ ρ.φ_over
  rw [h1 y, h1 y']
  haveI : PreconnectedSpace ↥(Spec (CommRingCat.of (T ⧸ Ideal.span {algebraMap 𝒪 T π}))) :=
    DEG44.preconnectedSpace_primeSpectrum_of_isIdempotentElem (DEG44.isIdempotentElem_quotient_of_eq_zero _ h0 hTc)
  exact h2.apply_eq_of_preconnectedSpace _ _

theorem finrank_φ'_eq (hΛℤ : ∀ m : ℤ, ((m : ℚ) : ℍ[ℚ, a, b]) ∈ Λ)
    (A₀ : FakeEllipticCurve Λ N (Onr ⧸ Ideal.span {algebraMap 𝒪 Onr π}))
    (T : Type) [CommRing T] [IsNoetherianRing T] [Algebra 𝒪 T] (hTc : ∀ e : T, IsIdempotentElem e → e = 0 ∨ e = 1)
    (h0 : algebraMap 𝒪 T π = 0)
    (ψT : Onr →ₐ[𝒪] T) (E : FakeEllipticCurve Λ N T)
    (ρ : FakeEllipticCurve.Rigidification r π A₀ ψT E) (y y' : ↥ρ.Eb.A) :
    ρ.φ'.finrank y = ρ.φ'.finrank y' := by
  obtain ⟨hfin, hfl, hlfp, -⟩ := DEG44.isFinite_flat_φ' hΛℤ ρ
  haveI := hfin; haveI := hfl; haveI := hlfp
  obtain ⟨_, hψ, -⟩ := ρ.isIsogenyPair
  obtain ⟨h1, h2⟩ := FakeEllipticCurve.isLocallyConstant_finrank_one _ ρ.Ab ρ.Eb ρ.φ' hψ
  rw [h1 y, h1 y']
  haveI : PreconnectedSpace ↥(Spec (CommRingCat.of (T ⧸ Ideal.span {algebraMap 𝒪 T π}))) :=
    DEG44.preconnectedSpace_primeSpectrum_of_isIdempotentElem (DEG44.isIdempotentElem_quotient_of_eq_zero _ h0 hTc)
  exact h2.apply_eq_of_preconnectedSpace _ _

theorem comp_eq_of_comp_act_pow_eq (hΛℤ : ∀ m : ℤ, ((m : ℚ) : ℍ[ℚ, a, b]) ∈ Λ)
    (A₀ : FakeEllipticCurve Λ N (Onr ⧸ Ideal.span {algebraMap 𝒪 Onr π}))
    (T : Type) [CommRing T] [Algebra 𝒪 T] (ψT : Onr →ₐ[𝒪] T) (E E' : FakeEllipticCurve Λ N T)
    (ρ : FakeEllipticCurve.Rigidification r π A₀ ψT E) (ρ' : FakeEllipticCurve.Rigidification r π A₀ ψT E')
    (i₀ : E.A ≅ E'.A) (hi : i₀.hom ≫ E'.f = E.f) (hI : FakeEllipticCurve.IsoVia E E' i₀ hi)
    (ib : ρ.Eb.A ⟶ ρ'.Eb.A) (hib : ib ≫ ρ'.gb = ρ.gb ≫ i₀.hom) (hibf : ib ≫ ρ'.Eb.f = ρ.Eb.f)
    (uA : ρ'.Ab.A ⟶ ρ.Ab.A) (huA : FakeEllipticCurve.IsPullbackVia (RingHom.id _) ρ.Ab ρ'.Ab uA) (huAg : uA ≫ ρ.gA = ρ'.gA)
    (i₁ : ℕ)
    (hrel : ib ≫ ρ'.φ ≫ uA ≫ ρ.Ab.act ⟨(((r ^ i₁ : ℕ) : ℤ) : ℚ), hΛℤ _⟩ = ρ.φ ≫ ρ.Ab.act ⟨(((r ^ i₁ : ℕ) : ℤ) : ℚ), hΛℤ _⟩) :
    ib ≫ ρ'.φ ≫ uA = ρ.φ :=
  CerednikDrinfeld.QM.FakeEllipticCurve.Rigidification.comp_phi_comp_eq_phi_of_comp_act_pow_eq 𝒪 π Onr Λ hΛℤ A₀
    T ψT E E' ρ ρ' i₀ hi hI ib hib hibf uA huA huAg i₁ hrel

theorem degpack_inst (hΛℤ : ∀ m : ℤ, ((m : ℚ) : ℍ[ℚ, a, b]) ∈ Λ)
    (hOnr_max : (Ideal.span {algebraMap 𝒪 Onr π}).IsMaximal)
    (A₀ : FakeEllipticCurve Λ N (Onr ⧸ Ideal.span {algebraMap 𝒪 Onr π})) (n : ℕ) :
    ∃ (c : ℕ) (degφ degφ' : (∀ (T : Type) [CommRing T] [Algebra 𝒪 T] (ψT : Onr →ₐ[𝒪] T) (E : FakeEllipticCurve Λ N T),
          FakeEllipticCurve.Rigidification r π A₀ ψT E → ℕ)), 1 < c ∧
        (∀ (T : Type) [CommRing T] [IsNoetherianRing T] [Algebra 𝒪 T]
            (hTc : ∀ e : T, IsIdempotentElem e → e = 0 ∨ e = 1) (h0 : algebraMap 𝒪 T π = 0) (ψT : Onr →ₐ[𝒪] T)
            (u u' : FakeEllipticCurve.WithFullLevel Λ N n T)
            (ρ : FakeEllipticCurve.Rigidification r π A₀ ψT u.1) (ρ' : FakeEllipticCurve.Rigidification r π A₀ ψT u'.1)
            (_ : ρ'.d = ρ.d)
            (i : u.1.A ≅ u'.1.A) (hi : i.hom ≫ u'.1.f = u.1.f) (hI : FakeEllipticCurve.WithFullLevel.IsoVia u u' i hi)
            (ib : ρ.Eb.A ⟶ ρ'.Eb.A) (_ : ib ≫ ρ'.gb = ρ.gb ≫ i.hom) (_ : ib ≫ ρ'.Eb.f = ρ.Eb.f)
            (uA : ρ'.Ab.A ⟶ ρ.Ab.A) (_ : FakeEllipticCurve.IsPullbackVia (RingHom.id _) ρ.Ab ρ'.Ab uA) (_ : uA ≫ ρ.gA = ρ'.gA)
            (i₁ j₁ : ℕ),
            ib ≫ ρ'.φ ≫ uA ≫ ρ.Ab.act ⟨(((r ^ i₁ : ℕ) : ℤ) : ℚ), hΛℤ _⟩ = ρ.φ ≫ ρ.Ab.act ⟨(((r ^ j₁ : ℕ) : ℤ) : ℚ), hΛℤ _⟩ →
              degφ T ψT u'.1 ρ' * c ^ i₁ = degφ T ψT u.1 ρ * c ^ j₁ ∧
              degφ' T ψT u'.1 ρ' * c ^ j₁ = degφ' T ψT u.1 ρ * c ^ i₁) ∧
        (∀ (T : Type) [CommRing T] [IsNoetherianRing T] [Algebra 𝒪 T]
            (hTc : ∀ e : T, IsIdempotentElem e → e = 0 ∨ e = 1) (h0 : algebraMap 𝒪 T π = 0) (ψT : Onr →ₐ[𝒪] T)
            (u u' : FakeEllipticCurve.WithFullLevel Λ N n T)
            (ρ : FakeEllipticCurve.Rigidification r π A₀ ψT u.1) (ρ' : FakeEllipticCurve.Rigidification r π A₀ ψT u'.1)
            (i : u.1.A ≅ u'.1.A) (hi : i.hom ≫ u'.1.f = u.1.f) (hI : FakeEllipticCurve.WithFullLevel.IsoVia u u' i hi)
            (ib : ρ.Eb.A ⟶ ρ'.Eb.A) (_ : ib ≫ ρ'.gb = ρ.gb ≫ i.hom) (_ : ib ≫ ρ'.Eb.f = ρ.Eb.f)
            (uA : ρ'.Ab.A ⟶ ρ.Ab.A) (_ : FakeEllipticCurve.IsPullbackVia (RingHom.id _) ρ.Ab ρ'.Ab uA) (_ : uA ≫ ρ.gA = ρ'.gA)
            (i₁ : ℕ),
            ib ≫ ρ'.φ ≫ uA ≫ ρ.Ab.act ⟨(((r ^ i₁ : ℕ) : ℤ) : ℚ), hΛℤ _⟩ = ρ.φ ≫ ρ.Ab.act ⟨(((r ^ i₁ : ℕ) : ℤ) : ℚ), hΛℤ _⟩ →
              ib ≫ ρ'.φ ≫ uA = ρ.φ) := by
  classical
  refine ⟨cdeg (r := r) hΛℤ A₀, degφ (r := r) A₀, degφ' (r := r) A₀, one_lt_cdeg hΛℤ A₀, ?_, ?_⟩
  · intro T _ _ _ hTc h0 ψT u u' ρ ρ' hd i hi hI ib hib hibf uA huA huAg i₁ j₁ hrel

    have sq := huA.1
    have huAiso : IsIso uA := by
      have : IsIso (Spec.map (CommRingCat.ofHom (RingHom.id (T ⧸ Ideal.span {algebraMap 𝒪 T π})))) := by
        rw [CommRingCat.ofHom_id, Spec.map_id]; infer_instance
      exact W7Aux.isIso_of_isPullback_of_isIso _ _ _ _ sq
    by_cases hne' : Nonempty ↥ρ'.Ab.A
    · obtain ⟨y'⟩ := hne'
      have hne : Nonempty ↥ρ.Ab.A := ⟨uA.base y'⟩

      let w : ↥ρ.Eb.A := (ρ.Eb.L.one (𝟙 _)).1.base (ρ.Ab.f.base (uA.base y'))
      let w' : ↥ρ'.Eb.A := (ρ'.Eb.L.one (𝟙 _)).1.base (ρ'.Ab.f.base y')
      have eφ : degφ (r := r) A₀ T ψT u.1 ρ = ρ.φ.finrank (uA.base y') := by
        unfold degφ; rw [dif_pos hne]; exact finrank_φ_eq hΛℤ A₀ T hTc h0 ψT u.1 ρ _ _
      have eφ2 : degφ (r := r) A₀ T ψT u'.1 ρ' = ρ'.φ.finrank y' := by
        unfold degφ; rw [dif_pos ⟨y'⟩]; exact finrank_φ_eq hΛℤ A₀ T hTc h0 ψT u'.1 ρ' _ _
      have eφ' : degφ' (r := r) A₀ T ψT u.1 ρ = ρ.φ'.finrank w := by
        unfold degφ'; rw [dif_pos ⟨w⟩]; exact finrank_φ'_eq hΛℤ A₀ T hTc h0 ψT u.1 ρ _ _
      have eφ'2 : degφ' (r := r) A₀ T ψT u'.1 ρ' = ρ'.φ'.finrank w' := by
        unfold degφ'; rw [dif_pos ⟨w'⟩]; exact finrank_φ'_eq hΛℤ A₀ T hTc h0 ψT u'.1 ρ' _ _
      have ec : cdeg (r := r) hΛℤ A₀ = (ρ.Ab.act ⟨(((r ^ 1 : ℕ) : ℤ) : ℚ), hΛℤ _⟩).finrank (uA.base y') :=
        (finrank_act_Ab_eq_cdeg hΛℤ hOnr_max A₀ T ψT u.1 ρ (uA.base y')).symm
      refine ⟨?_, ?_⟩
      · rw [eφ, eφ2, ec]
        exact CerednikDrinfeld.QM.FakeEllipticCurve.Rigidification.finrank_mul_finrank_act_pow_eq_of_corr 𝒪 π Onr Λ hΛℤ A₀
          T ψT u.1 u'.1 ρ ρ' i hi ib hib hibf uA huA huAg i₁ j₁ hrel y'
      · rw [eφ', eφ'2, ec]
        exact DEG2.finrank_φ'_mul_pow_eq_of_corr hΛℤ A₀ T ψT u.1 u'.1 ρ ρ' hd i hi ib hib hibf uA
          huA huAg i₁ j₁ hrel y'
    · have hne : ¬ Nonempty ↥ρ.Ab.A := fun ⟨y⟩ => hne' ⟨(inv uA).base y⟩
      have hneE : ¬ Nonempty ↥ρ.Eb.A := fun ⟨w⟩ => hne ⟨ρ.φ.base w⟩
      have hneE' : ¬ Nonempty ↥ρ'.Eb.A := fun ⟨w⟩ => hne' ⟨ρ'.φ.base w⟩
      simp only [degφ, degφ', dif_neg hne, dif_neg hne', dif_neg hneE, dif_neg hneE', zero_mul, and_self]
  · intro T _ _ _ hTc h0 ψT u u' ρ ρ' i hi hI ib hib hibf uA huA huAg i₁ hrel
    exact comp_eq_of_comp_act_pow_eq hΛℤ A₀ T ψT u.1 u'.1 ρ ρ' i hi ⟨hI.1, hI.2.1, hI.2.2.1⟩ ib hib hibf uA huA huAg i₁ hrel

end DEG
p2m_reactivate "P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_exists_opens_ratioWindow_degree_laws_of_rigidifiedToG_of_bdd.Ws16WC.Clopen P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_exists_opens_ratioWindow_degree_laws_of_rigidifiedToG_of_bdd.Ws16WC.DEGb.DegreeMaps P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_exists_opens_ratioWindow_degree_laws_of_rigidifiedToG_of_bdd.Ws16WC.DEGb P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_exists_opens_ratioWindow_degree_laws_of_rigidifiedToG_of_bdd.Ws16WC"

set_option autoImplicit false

open scoped TensorProduct Quaternion NumberField
p2m_open "CategoryTheory AlgebraicGeometry QuaternionAlgebra CerednikDrinfeld P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_exists_opens_ratioWindow_degree_laws_of_rigidifiedToG_of_bdd.CerednikDrinfeld CerednikDrinfeld.QM P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_exists_opens_ratioWindow_degree_laws_of_rigidifiedToG_of_bdd.CerednikDrinfeld.QM NeronModelInfra~schemeHomOverComp_coe GoodReductionJacobian"

namespace Ws2DegC

variable {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} {N : ℕ}

theorem isIsogenyPair_symm {S : Type} [CommRing S] {d : ℕ} {E E' : FakeEllipticCurve Λ N S}
    {φ : E.A ⟶ E'.A} {ψ : E'.A ⟶ E.A} (h : FakeEllipticCurve.IsIsogenyPair d E E' φ ψ) :
    FakeEllipticCurve.IsIsogenyPair d E' E ψ φ := by
  obtain ⟨hφ, hψ, h1, h2, h3, h4, h5⟩ := h
  exact ⟨hψ, hφ, h2, h1, h4, h3, fun hd => ⟨(h5 hd).2, (h5 hd).1⟩⟩

theorem finrank_eq_finrank_of_preconnectedSpace {S : Type} [CommRing S]
    (hconn : PreconnectedSpace ↥(Spec (CommRingCat.of S)))
    (E' A : FakeEllipticCurve Λ N S) (φ : E'.A ⟶ A.A) (hφ : φ ≫ A.f = E'.f)
    [IsFinite φ] [Flat φ] [LocallyOfFinitePresentation φ] (y y' : ↥A.A) :
    φ.finrank y = φ.finrank y' := by
  obtain ⟨h1, h2⟩ := CerednikDrinfeld.QM.FakeEllipticCurve.isLocallyConstant_finrank_one S E' A φ hφ
  rw [h1 y, h1 y']
  haveI := hconn
  exact h2.apply_eq_of_preconnectedSpace _ _

theorem finrank_pos_of_surjective {X Y : Scheme.{0}} (φ : X ⟶ Y) [IsFinite φ] [Flat φ] [Surjective φ] (y : ↥Y) :
    0 < φ.finrank y := by
  have h := (AlgebraicGeometry.Scheme.Hom.one_le_finrank_iff_surjective φ).mpr inferInstance y
  simp only [Pi.one_apply] at h
  omega

theorem intCast_mul_mem (m : ℤ) (x : ↥Λ) : ((m : ℚ) : ℍ[ℚ, a, b]) * (x : ℍ[ℚ, a, b]) ∈ Λ := by
  rw [QuaternionAlgebra.coe_mul_eq_smul, Int.cast_smul_eq_zsmul]; exact Λ.smul_mem m x.2

theorem mul_intCast_mem (m : ℤ) (x : ↥Λ) : (x : ℍ[ℚ, a, b]) * ((m : ℚ) : ℍ[ℚ, a, b]) ∈ Λ := by
  rw [← QuaternionAlgebra.coe_commutes]; exact intCast_mul_mem m x

variable (hΛℤ : ∀ m : ℤ, ((m : ℚ) : ℍ[ℚ, a, b]) ∈ Λ)
include hΛℤ

theorem act_comm_act_natCast {S : Type} [CommRing S] (F : FakeEllipticCurve Λ N S) (m : ℕ) (x : ↥Λ) :
    F.act x ≫ F.act ⟨(((m : ℕ) : ℤ) : ℚ), hΛℤ _⟩ = F.act ⟨(((m : ℕ) : ℤ) : ℚ), hΛℤ _⟩ ≫ F.act x := by
  have h2 := F.act_mul ⟨(((m : ℕ) : ℤ) : ℚ), hΛℤ _⟩ x (intCast_mul_mem (m : ℤ) x)
  have h1 := F.act_mul x ⟨(((m : ℕ) : ℤ) : ℚ), hΛℤ _⟩ (mul_intCast_mem (m : ℤ) x)
  have he : (⟨(((⟨(((m : ℕ) : ℤ) : ℚ), hΛℤ _⟩ : ↥Λ)) : ℍ[ℚ, a, b]) * (x : ℍ[ℚ, a, b]), intCast_mul_mem (m : ℤ) x⟩ : ↥Λ) =
      ⟨(x : ℍ[ℚ, a, b]) * ((⟨(((m : ℕ) : ℤ) : ℚ), hΛℤ _⟩ : ↥Λ) : ℍ[ℚ, a, b]), mul_intCast_mem (m : ℤ) x⟩ :=
    Subtype.ext (QuaternionAlgebra.coe_commutes _ _)
  rw [← h2, he, h1]

theorem isIsogenyPair_act_natCast_id {S : Type} [CommRing S] (F : FakeEllipticCurve Λ N S) (m : ℕ) :
    FakeEllipticCurve.IsIsogenyPair m F F (F.act ⟨(((m : ℕ) : ℤ) : ℚ), hΛℤ _⟩) (𝟙 F.A) := by
  refine ⟨F.act_over _, Category.id_comp _, fun t P Q => F.act_hom _ t P Q, fun t P Q => ?_,
    fun x => act_comm_act_natCast hΛℤ F m x, fun x => by simp, fun hd => ?_⟩
  · apply Subtype.ext; simp [mapPt]
  · have he : (⟨(((m : ℕ) : ℤ) : ℚ), hΛℤ _⟩ : ↥Λ) = ⟨(((m : ℕ)) : ℚ), hd⟩ := Subtype.ext (by norm_cast)
    rw [Category.comp_id, Category.id_comp, he]; exact ⟨rfl, rfl⟩

theorem isFinite_flat_act {S : Type} [CommRing S] (F : FakeEllipticCurve Λ N S) (r : ℕ) [Fact r.Prime] :
    IsFinite (F.act ⟨(((r : ℕ) : ℤ) : ℚ), hΛℤ _⟩) ∧ Flat (F.act ⟨(((r : ℕ) : ℤ) : ℚ), hΛℤ _⟩) ∧
      LocallyOfFinitePresentation (F.act ⟨(((r : ℕ) : ℤ) : ℚ), hΛℤ _⟩) ∧ Surjective (F.act ⟨(((r : ℕ) : ℤ) : ℚ), hΛℤ _⟩) := by
  have h : FakeEllipticCurve.IsIsogenyPair (r ^ 1) F F (F.act ⟨(((r : ℕ) : ℤ) : ℚ), hΛℤ _⟩) (𝟙 F.A) := by
    simpa only [pow_one] using isIsogenyPair_act_natCast_id hΛℤ F r
  exact CerednikDrinfeld.QM.FakeEllipticCurve.isFinite_flat_surjective_of_isIsogenyPair hΛℤ r 1 S F F _ _ h

theorem act_pow_succ {S : Type} [CommRing S] (F : FakeEllipticCurve Λ N S) (r k : ℕ) :
    F.act ⟨(((r ^ (k + 1) : ℕ) : ℤ) : ℚ), hΛℤ _⟩ =
      F.act ⟨(((r : ℕ) : ℤ) : ℚ), hΛℤ _⟩ ≫ F.act ⟨(((r ^ k : ℕ) : ℤ) : ℚ), hΛℤ _⟩ := by
  have hmem : (((((r ^ k : ℕ) : ℤ) : ℚ) : ℍ[ℚ, a, b]) * ((((r : ℕ) : ℤ) : ℚ) : ℍ[ℚ, a, b])) ∈ Λ := by
    have := hΛℤ ((r ^ (k + 1) : ℕ) : ℤ)
    rw [pow_succ] at this
    convert this using 1
    push_cast
    rfl
  have hmul := F.act_mul ⟨(((r ^ k : ℕ) : ℤ) : ℚ), hΛℤ _⟩ ⟨(((r : ℕ) : ℤ) : ℚ), hΛℤ _⟩ hmem
  rw [← hmul]
  congr 1
  apply Subtype.ext
  simp only [pow_succ]
  push_cast
  rfl

theorem act_pow_zero {S : Type} [CommRing S] (F : FakeEllipticCurve Λ N S) (r : ℕ) :
    F.act ⟨(((r ^ 0 : ℕ) : ℤ) : ℚ), hΛℤ _⟩ = 𝟙 F.A := by
  have h1 : (1 : ℍ[ℚ, a, b]) ∈ Λ := by simpa using hΛℤ 1
  rw [← F.act_one h1]
  congr 1

theorem isFinite_flat_finrank_act_pow {S : Type} [CommRing S] (F : FakeEllipticCurve Λ N S) (r c : ℕ)
    [IsFinite (F.act ⟨(((r : ℕ) : ℤ) : ℚ), hΛℤ _⟩)] [Flat (F.act ⟨(((r : ℕ) : ℤ) : ℚ), hΛℤ _⟩)]
    (hc : ∀ y : ↥F.A, (F.act ⟨(((r : ℕ) : ℤ) : ℚ), hΛℤ _⟩).finrank y = c) (k : ℕ) :
    IsFinite (F.act ⟨(((r ^ k : ℕ) : ℤ) : ℚ), hΛℤ _⟩) ∧ Flat (F.act ⟨(((r ^ k : ℕ) : ℤ) : ℚ), hΛℤ _⟩) ∧
      ∀ y : ↥F.A, (F.act ⟨(((r ^ k : ℕ) : ℤ) : ℚ), hΛℤ _⟩).finrank y = c ^ k := by
  induction k with
  | zero =>
    rw [act_pow_zero hΛℤ F r]
    exact ⟨inferInstance, inferInstance, fun y => by simp [Scheme.Hom.finrank_eq_one_of_isIso]⟩
  | succ k ih =>
    obtain ⟨hfin, hfl, hk⟩ := ih
    rw [act_pow_succ hΛℤ F r k]
    refine ⟨inferInstance, inferInstance, fun y => ?_⟩
    rw [AlgebraicGeometry.Scheme.Hom.finrank_comp_of_finrank_eq_const _ _ c hc, hk, pow_succ, mul_comm]

variable {r : ℕ} {𝒪 : Type} [CommRing 𝒪] {π : 𝒪} {Onr : Type} [CommRing Onr] [Algebra 𝒪 Onr]
  {A₀ : FakeEllipticCurve Λ N (Onr ⧸ Ideal.span {algebraMap 𝒪 Onr π})}
  {B : Type} [CommRing B] [Algebra 𝒪 B] {ψ : Onr →ₐ[𝒪] B} {E : FakeEllipticCurve Λ N B}

theorem rig_insts [Fact r.Prime] (ρ : FakeEllipticCurve.Rigidification r π A₀ ψ E) :
    (IsFinite ρ.φ ∧ Flat ρ.φ ∧ LocallyOfFinitePresentation ρ.φ ∧ Surjective ρ.φ) ∧
      (IsFinite ρ.φ' ∧ Flat ρ.φ' ∧ LocallyOfFinitePresentation ρ.φ' ∧ Surjective ρ.φ') :=
  ⟨CerednikDrinfeld.QM.FakeEllipticCurve.isFinite_flat_surjective_of_isIsogenyPair hΛℤ r ρ.d _ ρ.Eb ρ.Ab ρ.φ ρ.φ'
      ρ.isIsogenyPair,
    CerednikDrinfeld.QM.FakeEllipticCurve.isFinite_flat_surjective_of_isIsogenyPair hΛℤ r ρ.d _ ρ.Ab ρ.Eb ρ.φ' ρ.φ
      (isIsogenyPair_symm ρ.isIsogenyPair)⟩

theorem rig_φ'_comp_φ (ρ : FakeEllipticCurve.Rigidification r π A₀ ψ E) :
    ρ.φ' ≫ ρ.φ = ρ.Ab.act ⟨(((r ^ ρ.d : ℕ) : ℤ) : ℚ), hΛℤ _⟩ := by
  obtain ⟨-, -, -, -, -, -, h5⟩ := ρ.isIsogenyPair
  have hmem : (((r ^ ρ.d : ℕ) : ℚ) : ℍ[ℚ, a, b]) ∈ Λ := by exact_mod_cast hΛℤ (r ^ ρ.d : ℕ)
  have he : (⟨(((r ^ ρ.d : ℕ)) : ℚ), hmem⟩ : ↥Λ) = ⟨(((r ^ ρ.d : ℕ) : ℤ) : ℚ), hΛℤ _⟩ := Subtype.ext (by norm_cast)
  rw [← he]; exact (h5 hmem).2

theorem rig_φ_comp_φ' (ρ : FakeEllipticCurve.Rigidification r π A₀ ψ E) :
    ρ.φ ≫ ρ.φ' = ρ.Eb.act ⟨(((r ^ ρ.d : ℕ) : ℤ) : ℚ), hΛℤ _⟩ := by
  obtain ⟨-, -, -, -, -, -, h5⟩ := ρ.isIsogenyPair
  have hmem : (((r ^ ρ.d : ℕ) : ℚ) : ℍ[ℚ, a, b]) ∈ Λ := by exact_mod_cast hΛℤ (r ^ ρ.d : ℕ)
  have he : (⟨(((r ^ ρ.d : ℕ)) : ℚ), hmem⟩ : ↥Λ) = ⟨(((r ^ ρ.d : ℕ) : ℤ) : ℚ), hΛℤ _⟩ := Subtype.ext (by norm_cast)
  rw [← he]; exact (h5 hmem).1

theorem degc_pos [Fact r.Prime] (ρ : FakeEllipticCurve.Rigidification r π A₀ ψ E) (y : ↥ρ.Ab.A) (z : ↥ρ.Eb.A) :
    0 < ρ.φ.finrank y ∧ 0 < ρ.φ'.finrank z := by
  obtain ⟨⟨_, _, _, _⟩, ⟨_, _, _, _⟩⟩ := rig_insts hΛℤ ρ
  exact ⟨finrank_pos_of_surjective ρ.φ y, finrank_pos_of_surjective ρ.φ' z⟩

theorem degc_prod_of_const [Fact r.Prime] (ρ : FakeEllipticCurve.Rigidification r π A₀ ψ E) (c m m' : ℕ)
    (hc : ∀ y : ↥ρ.Ab.A, (ρ.Ab.act ⟨(((r : ℕ) : ℤ) : ℚ), hΛℤ _⟩).finrank y = c)
    (hm : ∀ y : ↥ρ.Ab.A, ρ.φ.finrank y = m) (hm' : ∀ z : ↥ρ.Eb.A, ρ.φ'.finrank z = m')
    (y : ↥ρ.Ab.A) : m * m' = c ^ ρ.d := by
  obtain ⟨⟨_, _, _, _⟩, ⟨_, _, _, _⟩⟩ := rig_insts hΛℤ ρ
  obtain ⟨_, _, _, _⟩ := isFinite_flat_act hΛℤ ρ.Ab r
  have key := AlgebraicGeometry.Scheme.Hom.finrank_comp_of_finrank_eq_const ρ.φ' ρ.φ m' hm' y
  rw [rig_φ'_comp_φ hΛℤ ρ, (isFinite_flat_finrank_act_pow hΛℤ ρ.Ab r c hc ρ.d).2.2 y, hm y] at key
  rw [key, mul_comm]

theorem degc_finrank_φ_comp_act_pow [Fact r.Prime] (ρ : FakeEllipticCurve.Rigidification r π A₀ ψ E) (i c m : ℕ)
    (hc : ∀ y : ↥ρ.Ab.A, (ρ.Ab.act ⟨(((r : ℕ) : ℤ) : ℚ), hΛℤ _⟩).finrank y = c)
    (hm : ∀ y : ↥ρ.Ab.A, ρ.φ.finrank y = m) (y : ↥ρ.Ab.A) :
    (ρ.φ ≫ ρ.Ab.act ⟨(((r ^ i : ℕ) : ℤ) : ℚ), hΛℤ _⟩).finrank y = c ^ i * m := by
  obtain ⟨⟨_, _, _, _⟩, -⟩ := rig_insts hΛℤ ρ
  obtain ⟨_, _, _, _⟩ := isFinite_flat_act hΛℤ ρ.Ab r
  obtain ⟨_, _, hi⟩ := isFinite_flat_finrank_act_pow hΛℤ ρ.Ab r c hc i
  rw [AlgebraicGeometry.Scheme.Hom.finrank_comp_of_finrank_eq_const ρ.φ (ρ.Ab.act ⟨(((r ^ i : ℕ) : ℤ) : ℚ), hΛℤ _⟩) m hm y,
    hi y, mul_comm]

theorem degc_finrank_act_pow_comp_φ' [Fact r.Prime] (ρ : FakeEllipticCurve.Rigidification r π A₀ ψ E) (i c : ℕ)
    (hc : ∀ y : ↥ρ.Ab.A, (ρ.Ab.act ⟨(((r : ℕ) : ℤ) : ℚ), hΛℤ _⟩).finrank y = c) (z : ↥ρ.Eb.A) :
    (ρ.Ab.act ⟨(((r ^ i : ℕ) : ℤ) : ℚ), hΛℤ _⟩ ≫ ρ.φ').finrank z = c ^ i * ρ.φ'.finrank z := by
  obtain ⟨-, ⟨_, _, _, _⟩⟩ := rig_insts hΛℤ ρ
  obtain ⟨_, _, _, _⟩ := isFinite_flat_act hΛℤ ρ.Ab r
  obtain ⟨_, _, hi⟩ := isFinite_flat_finrank_act_pow hΛℤ ρ.Ab r c hc i
  exact AlgebraicGeometry.Scheme.Hom.finrank_comp_of_finrank_eq_const _ ρ.φ' (c ^ i) hi z

theorem degc_prod [Fact r.Prime]
    (hconn : PreconnectedSpace ↥(Spec (CommRingCat.of (B ⧸ Ideal.span {algebraMap 𝒪 B π}))))
    (ρ : FakeEllipticCurve.Rigidification r π A₀ ψ E) (c : ℕ)
    (hc : ∀ y : ↥ρ.Ab.A, (ρ.Ab.act ⟨(((r : ℕ) : ℤ) : ℚ), hΛℤ _⟩).finrank y = c)
    (y : ↥ρ.Ab.A) (z : ↥ρ.Eb.A) :
    ρ.φ.finrank y * ρ.φ'.finrank z = c ^ ρ.d := by
  obtain ⟨⟨_, _, _, _⟩, ⟨_, _, _, _⟩⟩ := rig_insts hΛℤ ρ
  obtain ⟨-, hψ, -⟩ := ρ.isIsogenyPair
  exact degc_prod_of_const hΛℤ ρ c _ _ hc
    (fun y' => finrank_eq_finrank_of_preconnectedSpace hconn ρ.Eb ρ.Ab ρ.φ ρ.φ_over y' y)
    (fun z' => finrank_eq_finrank_of_preconnectedSpace hconn ρ.Ab ρ.Eb ρ.φ' hψ z' z) y

theorem degc_pad [Fact r.Prime]
    (hconn : PreconnectedSpace ↥(Spec (CommRingCat.of (B ⧸ Ideal.span {algebraMap 𝒪 B π}))))
    (ρ : FakeEllipticCurve.Rigidification r π A₀ ψ E) (i c : ℕ)
    (hc : ∀ y : ↥ρ.Ab.A, (ρ.Ab.act ⟨(((r : ℕ) : ℤ) : ℚ), hΛℤ _⟩).finrank y = c)
    (y : ↥ρ.Ab.A) (z : ↥ρ.Eb.A) :
    (ρ.φ ≫ ρ.Ab.act ⟨(((r ^ i : ℕ) : ℤ) : ℚ), hΛℤ _⟩).finrank y = c ^ i * ρ.φ.finrank y ∧
      (ρ.Ab.act ⟨(((r ^ i : ℕ) : ℤ) : ℚ), hΛℤ _⟩ ≫ ρ.φ').finrank z = c ^ i * ρ.φ'.finrank z := by
  obtain ⟨⟨_, _, _, _⟩, -⟩ := rig_insts hΛℤ ρ
  exact ⟨degc_finrank_φ_comp_act_pow hΛℤ ρ i c _ hc
      (fun y' => finrank_eq_finrank_of_preconnectedSpace hconn ρ.Eb ρ.Ab ρ.φ ρ.φ_over y' y) y,
    degc_finrank_act_pow_comp_φ' hΛℤ ρ i c hc z⟩

theorem degc_pad' [Fact r.Prime]
    (hconn : PreconnectedSpace ↥(Spec (CommRingCat.of (B ⧸ Ideal.span {algebraMap 𝒪 B π}))))
    (ρ : FakeEllipticCurve.Rigidification r π A₀ ψ E) (i c : ℕ)
    (hc : ∀ y : ↥ρ.Ab.A, (ρ.Ab.act ⟨(((r : ℕ) : ℤ) : ℚ), hΛℤ _⟩).finrank y = c)
    (y y' : ↥ρ.Ab.A) (z z' : ↥ρ.Eb.A) :
    (ρ.φ ≫ ρ.Ab.act ⟨(((r ^ i : ℕ) : ℤ) : ℚ), hΛℤ _⟩).finrank y = c ^ i * ρ.φ.finrank y' ∧
      (ρ.Ab.act ⟨(((r ^ i : ℕ) : ℤ) : ℚ), hΛℤ _⟩ ≫ ρ.φ').finrank z = c ^ i * ρ.φ'.finrank z' := by
  obtain ⟨⟨_, _, _, _⟩, ⟨_, _, _, _⟩⟩ := rig_insts hΛℤ ρ
  obtain ⟨-, hψ, -⟩ := ρ.isIsogenyPair
  refine ⟨degc_finrank_φ_comp_act_pow hΛℤ ρ i c _ hc
      (fun y'' => finrank_eq_finrank_of_preconnectedSpace hconn ρ.Eb ρ.Ab ρ.φ ρ.φ_over y'' y') y, ?_⟩
  rw [degc_finrank_act_pow_comp_φ' hΛℤ ρ i c hc z,
    finrank_eq_finrank_of_preconnectedSpace hconn ρ.Ab ρ.Eb ρ.φ' hψ z z']

omit hΛℤ in

private theorem _root_.Ws2DegC.preconnectedSpace_primeSpectrum_of_isIdempotentElem {R : Type} [CommRing R]
    (h : ∀ e : R, IsIdempotentElem e → e = 0 ∨ e = 1) : PreconnectedSpace (PrimeSpectrum R) := by
  rw [preconnectedSpace_iff_clopen]
  intro s hs
  obtain ⟨e, he, rfl⟩ := PrimeSpectrum.isClopen_iff.mp hs
  rcases h e he with rfl | rfl
  · left; simp [PrimeSpectrum.basicOpen_zero]
  · right; simp [PrimeSpectrum.basicOpen_one]

p2m_export "Ws2DegC" "preconnectedSpace_primeSpectrum_of_isIdempotentElem"
omit hΛℤ in

theorem isIdempotentElem_quotient_of_eq_bot {R : Type} [CommRing R] (I : Ideal R) (hI : I = ⊥)
    (h : ∀ e : R, IsIdempotentElem e → e = 0 ∨ e = 1) :
    ∀ e : R ⧸ I, IsIdempotentElem e → e = 0 ∨ e = 1 := by
  subst hI
  intro e he
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective e
  have hx : IsIdempotentElem x := by
    have h2 : (Ideal.Quotient.mk ⊥ (x * x) : R ⧸ (⊥ : Ideal R)) = Ideal.Quotient.mk ⊥ x := by
      rw [map_mul]; exact he.eq
    rw [Ideal.Quotient.eq, Ideal.mem_bot, sub_eq_zero] at h2
    exact h2
  rcases h x hx with rfl | rfl
  · left; simp
  · right; simp

omit hΛℤ in
theorem span_algebraMap_eq_bot (hπ : algebraMap 𝒪 B π = 0) : Ideal.span {algebraMap 𝒪 B π} = (⊥ : Ideal B) := by
  rw [hπ, Ideal.span_singleton_eq_bot]

omit hΛℤ in

theorem preconnectedSpace_spec_quot (hidem : ∀ e : B, IsIdempotentElem e → e = 0 ∨ e = 1) (hπ : algebraMap 𝒪 B π = 0) :
    PreconnectedSpace ↥(Spec (CommRingCat.of (B ⧸ Ideal.span {algebraMap 𝒪 B π}))) :=
  preconnectedSpace_primeSpectrum_of_isIdempotentElem
    (isIdempotentElem_quotient_of_eq_bot _ (span_algebraMap_eq_bot hπ) hidem)

omit hΛℤ in
theorem nontrivial_quot [Nontrivial B] (hπ : algebraMap 𝒪 B π = 0) : Nontrivial (B ⧸ Ideal.span {algebraMap 𝒪 B π}) :=
  Ideal.Quotient.nontrivial_iff.mpr (by rw [span_algebraMap_eq_bot hπ]; exact bot_ne_top)

omit hΛℤ in

noncomputable def basePt [Nontrivial B] (hπ : algebraMap 𝒪 B π = 0) :
    ↥(Spec (CommRingCat.of (B ⧸ Ideal.span {algebraMap 𝒪 B π}))) :=
  (PrimeSpectrum.nonempty_iff_nontrivial.mpr (nontrivial_quot hπ)).some

omit hΛℤ in

noncomputable def degAt (s : ↥(Spec (CommRingCat.of (B ⧸ Ideal.span {algebraMap 𝒪 B π}))))
    {E' A : FakeEllipticCurve Λ N (B ⧸ Ideal.span {algebraMap 𝒪 B π})} (φ : E'.A ⟶ A.A) : ℕ :=
  φ.finrank ((A.L.one (𝟙 (Spec (CommRingCat.of (B ⧸ Ideal.span {algebraMap 𝒪 B π}))))).1.base s)

theorem degc_face [Fact r.Prime]
    (hidem : ∀ e : B, IsIdempotentElem e → e = 0 ∨ e = 1) (hπ : algebraMap 𝒪 B π = 0)
    (s : ↥(Spec (CommRingCat.of (B ⧸ Ideal.span {algebraMap 𝒪 B π})))) (c : ℕ)
    (hc : ∀ {E : FakeEllipticCurve Λ N B} (ρ : FakeEllipticCurve.Rigidification r π A₀ ψ E) (y : ↥ρ.Ab.A),
      (ρ.Ab.act ⟨(((r : ℕ) : ℤ) : ℚ), hΛℤ _⟩).finrank y = c) :
    (∀ {E : FakeEllipticCurve Λ N B} (ρ : FakeEllipticCurve.Rigidification r π A₀ ψ E),
        0 < degAt s ρ.φ ∧ 0 < degAt s ρ.φ') ∧
    (∀ {E : FakeEllipticCurve Λ N B} (ρ : FakeEllipticCurve.Rigidification r π A₀ ψ E),
        degAt s ρ.φ * degAt s ρ.φ' = c ^ ρ.d) ∧
    (∀ {E : FakeEllipticCurve Λ N B} (ρ : FakeEllipticCurve.Rigidification r π A₀ ψ E) (i : ℕ),
        degAt s (ρ.φ ≫ ρ.Ab.act ⟨(((r ^ i : ℕ) : ℤ) : ℚ), hΛℤ _⟩) = c ^ i * degAt s ρ.φ ∧
        degAt s (ρ.Ab.act ⟨(((r ^ i : ℕ) : ℤ) : ℚ), hΛℤ _⟩ ≫ ρ.φ') = c ^ i * degAt s ρ.φ') :=
  ⟨fun ρ => degc_pos hΛℤ ρ _ _,
   fun ρ => degc_prod hΛℤ (preconnectedSpace_spec_quot hidem hπ) ρ c (hc ρ) _ _,
   fun ρ i => degc_pad hΛℤ (preconnectedSpace_spec_quot hidem hπ) ρ i c (hc ρ) _ _⟩

theorem degc_face' [Fact r.Prime] [Nontrivial B]
    (hidem : ∀ e : B, IsIdempotentElem e → e = 0 ∨ e = 1) (hπ : algebraMap 𝒪 B π = 0) (c : ℕ)
    (hc : ∀ {E : FakeEllipticCurve Λ N B} (ρ : FakeEllipticCurve.Rigidification r π A₀ ψ E) (y : ↥ρ.Ab.A),
      (ρ.Ab.act ⟨(((r : ℕ) : ℤ) : ℚ), hΛℤ _⟩).finrank y = c) :
    (∀ {E : FakeEllipticCurve Λ N B} (ρ : FakeEllipticCurve.Rigidification r π A₀ ψ E),
        0 < degAt (basePt hπ) ρ.φ ∧ 0 < degAt (basePt hπ) ρ.φ') ∧
    (∀ {E : FakeEllipticCurve Λ N B} (ρ : FakeEllipticCurve.Rigidification r π A₀ ψ E),
        degAt (basePt hπ) ρ.φ * degAt (basePt hπ) ρ.φ' = c ^ ρ.d) ∧
    (∀ {E : FakeEllipticCurve Λ N B} (ρ : FakeEllipticCurve.Rigidification r π A₀ ψ E) (i : ℕ),
        degAt (basePt hπ) (ρ.φ ≫ ρ.Ab.act ⟨(((r ^ i : ℕ) : ℤ) : ℚ), hΛℤ _⟩) = c ^ i * degAt (basePt hπ) ρ.φ ∧
        degAt (basePt hπ) (ρ.Ab.act ⟨(((r ^ i : ℕ) : ℤ) : ℚ), hΛℤ _⟩ ≫ ρ.φ') = c ^ i * degAt (basePt hπ) ρ.φ') :=
  degc_face hΛℤ hidem hπ (basePt hπ) c hc

end Ws2DegC
p2m_reactivate "P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_exists_opens_ratioWindow_degree_laws_of_rigidifiedToG_of_bdd.Ws16WC.Clopen P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_exists_opens_ratioWindow_degree_laws_of_rigidifiedToG_of_bdd.Ws16WC.DEGb.DegreeMaps P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_exists_opens_ratioWindow_degree_laws_of_rigidifiedToG_of_bdd.Ws16WC.DEGb P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_exists_opens_ratioWindow_degree_laws_of_rigidifiedToG_of_bdd.Ws16WC"

noncomputable section

namespace ChartDict3

section DegA
variable {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} {N n r : ℕ}
  {𝒪 : Type} [CommRing 𝒪] (π : 𝒪) {Onr : Type} [CommRing Onr] [Algebra 𝒪 Onr]
  (A₀ : FakeEllipticCurve Λ N (Onr ⧸ Ideal.span {algebraMap 𝒪 Onr π}))
  {C : Type} [CommRing C] [Algebra 𝒪 C] (χC : Onr →ₐ[𝒪] C)
  {M : Scheme.{0}} (fM : M ⟶ Spec (CommRingCat.of 𝒪))
  (Xs : ℕ → Scheme.{0}) (ξ : ∀ d, Xs d ⟶ Limits.pullback fM (Spec.map (CommRingCat.ofHom (algebraMap 𝒪 C))))
  (ptX : ∀ (d : ℕ) (T : Type) [CommRing T] [Algebra C T] [Algebra 𝒪 T] [IsScalarTower 𝒪 C T]
            (ψT : Onr →ₐ[𝒪] T) (_ : ψT = (IsScalarTower.toAlgHom 𝒪 C T).comp χC)
            (u : FakeEllipticCurve.WithFullLevel Λ N n T) (ρ : FakeEllipticCurve.Rigidification r π A₀ ψT u.1),
            ρ.d = d → algebraMap C T (algebraMap 𝒪 C π) = 0 →
              SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap C T))) (ξ d ≫ Limits.pullback.snd fM (Spec.map (CommRingCat.ofHom (algebraMap 𝒪 C)))))

abbrev strMap (d : ℕ) : Xs d ⟶ Spec (CommRingCat.of C) :=
  ξ d ≫ Limits.pullback.snd fM (Spec.map (CommRingCat.ofHom (algebraMap 𝒪 C)))

def rdeg {T : Type} [CommRing T] [Algebra 𝒪 T] {ψT : Onr →ₐ[𝒪] T} {E : FakeEllipticCurve Λ N T}
    (ρ : FakeEllipticCurve.Rigidification r π A₀ ψT E) (q : ↥(Spec (CommRingCat.of (T ⧸ Ideal.span {algebraMap 𝒪 T π})))) : ℕ :=
  ρ.φ.finrank ((ρ.Ab.L.one (𝟙 (Spec (CommRingCat.of (T ⧸ Ideal.span {algebraMap 𝒪 T π}))))).1.base q)

def rdeg' {T : Type} [CommRing T] [Algebra 𝒪 T] {ψT : Onr →ₐ[𝒪] T} {E : FakeEllipticCurve Λ N T}
    (ρ : FakeEllipticCurve.Rigidification r π A₀ ψT E) (q : ↥(Spec (CommRingCat.of (T ⧸ Ideal.span {algebraMap 𝒪 T π})))) : ℕ :=
  ρ.φ'.finrank ((ρ.Eb.L.one (𝟙 (Spec (CommRingCat.of (T ⧸ Ideal.span {algebraMap 𝒪 T π}))))).1.base q)

def DegAt (val : ∀ {T : Type} [CommRing T] [Algebra 𝒪 T] {ψT : Onr →ₐ[𝒪] T} {E : FakeEllipticCurve Λ N T},
      FakeEllipticCurve.Rigidification r π A₀ ψT E → ↥(Spec (CommRingCat.of (T ⧸ Ideal.span {algebraMap 𝒪 T π}))) → ℕ)
    (d : ℕ) (x : ↥(Xs d)) (m : ℕ) : Prop :=
  ∃ (T : Type) (_ : CommRing T) (_ : Algebra C T) (_ : Algebra 𝒪 T) (_ : IsScalarTower 𝒪 C T)
    (u : FakeEllipticCurve.WithFullLevel Λ N n T)
    (ρ : FakeEllipticCurve.Rigidification r π A₀ ((IsScalarTower.toAlgHom 𝒪 C T).comp χC) u.1)
    (hd : ρ.d = d) (h0 : algebraMap C T (algebraMap 𝒪 C π) = 0)
    (q : ↥(Spec (CommRingCat.of (T ⧸ Ideal.span {algebraMap 𝒪 T π})))),
    (ptX d T ((IsScalarTower.toAlgHom 𝒪 C T).comp χC) rfl u ρ hd h0).1.base
        ((Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (Ideal.span {algebraMap 𝒪 T π})))).base q) = x ∧
      m = val ρ q

open Classical in

def degF (val : ∀ {T : Type} [CommRing T] [Algebra 𝒪 T] {ψT : Onr →ₐ[𝒪] T} {E : FakeEllipticCurve Λ N T},
      FakeEllipticCurve.Rigidification r π A₀ ψT E → ↥(Spec (CommRingCat.of (T ⧸ Ideal.span {algebraMap 𝒪 T π}))) → ℕ) (d : ℕ) (x : ↥(Xs d)) : ℕ :=
  if h : ∃ m, DegAt π A₀ χC fM Xs ξ ptX val d x m then h.choose else 0

theorem degF_eq_of_degAt (val : ∀ {T : Type} [CommRing T] [Algebra 𝒪 T] {ψT : Onr →ₐ[𝒪] T} {E : FakeEllipticCurve Λ N T},
      FakeEllipticCurve.Rigidification r π A₀ ψT E → ↥(Spec (CommRingCat.of (T ⧸ Ideal.span {algebraMap 𝒪 T π}))) → ℕ)
    (huniq : ∀ (d : ℕ) (x : ↥(Xs d)) (m m' : ℕ), DegAt π A₀ χC fM Xs ξ ptX val d x m → DegAt π A₀ χC fM Xs ξ ptX val d x m' → m = m')
    (d : ℕ) (x : ↥(Xs d)) (m : ℕ) (h : DegAt π A₀ χC fM Xs ξ ptX val d x m) : degF π A₀ χC fM Xs ξ ptX val d x = m := by
  classical
  have hex : ∃ m, DegAt π A₀ χC fM Xs ξ ptX val d x m := ⟨m, h⟩
  rw [degF, dif_pos hex]
  exact huniq d x _ _ hex.choose_spec h

theorem degF_ptX_apply (val : ∀ {T : Type} [CommRing T] [Algebra 𝒪 T] {ψT : Onr →ₐ[𝒪] T} {E : FakeEllipticCurve Λ N T},
      FakeEllipticCurve.Rigidification r π A₀ ψT E → ↥(Spec (CommRingCat.of (T ⧸ Ideal.span {algebraMap 𝒪 T π}))) → ℕ)
    (huniq : ∀ (d : ℕ) (x : ↥(Xs d)) (m m' : ℕ), DegAt π A₀ χC fM Xs ξ ptX val d x m → DegAt π A₀ χC fM Xs ξ ptX val d x m' → m = m')
    (d : ℕ) (T : Type) [CommRing T] [Algebra C T] [Algebra 𝒪 T] [IsScalarTower 𝒪 C T]
    (u : FakeEllipticCurve.WithFullLevel Λ N n T)
    (ρ : FakeEllipticCurve.Rigidification r π A₀ ((IsScalarTower.toAlgHom 𝒪 C T).comp χC) u.1)
    (hd : ρ.d = d) (h0 : algebraMap C T (algebraMap 𝒪 C π) = 0)
    (q : ↥(Spec (CommRingCat.of (T ⧸ Ideal.span {algebraMap 𝒪 T π})))) :
    degF π A₀ χC fM Xs ξ ptX val d
      ((ptX d T ((IsScalarTower.toAlgHom 𝒪 C T).comp χC) rfl u ρ hd h0).1.base
        ((Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (Ideal.span {algebraMap 𝒪 T π})))).base q)) = val ρ q :=
  degF_eq_of_degAt π A₀ χC fM Xs ξ ptX val huniq d _ _ ⟨T, _, _, _, _, u, ρ, hd, h0, q, rfl, rfl⟩

theorem degAt_exists (val : ∀ {T : Type} [CommRing T] [Algebra 𝒪 T] {ψT : Onr →ₐ[𝒪] T} {E : FakeEllipticCurve Λ N T},
      FakeEllipticCurve.Rigidification r π A₀ ψT E → ↥(Spec (CommRingCat.of (T ⧸ Ideal.span {algebraMap 𝒪 T π}))) → ℕ)
    (hs0 : ∀ (d : ℕ) (T : Type) [CommRing T] [Algebra C T]
            (x : SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap C T))) (ξ d ≫ Limits.pullback.snd fM (Spec.map (CommRingCat.ofHom (algebraMap 𝒪 C))))),
            algebraMap C T (algebraMap 𝒪 C π) = 0)
    (hx3 : ∀ (d : ℕ) (T : Type) [CommRing T] [Algebra C T] [Algebra 𝒪 T] [IsScalarTower 𝒪 C T]
              (ψT : Onr →ₐ[𝒪] T) (hψT : ψT = (IsScalarTower.toAlgHom 𝒪 C T).comp χC)
              (h0 : algebraMap C T (algebraMap 𝒪 C π) = 0) (x : SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap C T))) (ξ d ≫ Limits.pullback.snd fM (Spec.map (CommRingCat.ofHom (algebraMap 𝒪 C))))),
              ∃ (u : FakeEllipticCurve.WithFullLevel Λ N n T) (ρ : FakeEllipticCurve.Rigidification r π A₀ ψT u.1) (hd : ρ.d = d),
                ptX d T ψT hψT u ρ hd h0 = x)
    (d : ℕ) (x : ↥(Xs d)) : ∃ m, DegAt π A₀ χC fM Xs ξ ptX val d x m := by
  classical
  let K : Type := ↥((Xs d).residueField x)
  let t : Spec (CommRingCat.of K) ⟶ Xs d := (Xs d).fromSpecResidueField x
  let φ : CommRingCat.of C ⟶ CommRingCat.of K := Spec.preimage (t ≫ strMap fM Xs ξ d)
  letI iC : Algebra C K := φ.hom.toAlgebra
  letI i𝒪 : Algebra 𝒪 K := (φ.hom.comp (algebraMap 𝒪 C)).toAlgebra
  haveI : IsScalarTower 𝒪 C K := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  have hmap : Spec.map (CommRingCat.ofHom (algebraMap C K)) = t ≫ strMap fM Xs ξ d := by
    show Spec.map (CommRingCat.ofHom φ.hom) = _
    rw [CommRingCat.ofHom_hom, Spec.map_preimage]
  let xK : SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap C K))) (strMap fM Xs ξ d) := ⟨t, hmap.symm⟩
  have h0 : algebraMap C K (algebraMap 𝒪 C π) = 0 := hs0 d K xK
  obtain ⟨u, ρ, hd, hx⟩ := hx3 d K ((IsScalarTower.toAlgHom 𝒪 C K).comp χC) rfl h0 xK
  have hπK : algebraMap 𝒪 K π = 0 := h0
  haveI : Nontrivial (K ⧸ Ideal.span {algebraMap 𝒪 K π}) :=
    Ideal.Quotient.nontrivial_iff.mpr (by rw [Ne, hπK, Ideal.span_singleton_eq_top]; exact not_isUnit_zero)
  obtain ⟨q⟩ : Nonempty ↥(Spec (CommRingCat.of (K ⧸ Ideal.span {algebraMap 𝒪 K π}))) := inferInstance
  refine ⟨val ρ q, K, inferInstance, iC, i𝒪, inferInstance, u, ρ, hd, h0, q, ?_, rfl⟩
  rw [hx]
  show t.base _ = x
  exact Scheme.fromSpecResidueField_apply x _

theorem isIso_specMap_quotientMk {T : Type} [CommRing T] [Algebra 𝒪 T] (hπ : algebraMap 𝒪 T π = 0) :
    IsIso (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (Ideal.span {algebraMap 𝒪 T π})))) := by
  have hbot : (⊥ : Ideal T) = Ideal.span {algebraMap 𝒪 T π} := by
    rw [hπ, Ideal.span_singleton_eq_bot.mpr rfl]
  let e : T ≃+* (T ⧸ Ideal.span {algebraMap 𝒪 T π}) := (RingEquiv.quotientBot T).symm.trans (Ideal.quotEquivOfEq hbot)
  have he : (e : T →+* (T ⧸ Ideal.span {algebraMap 𝒪 T π})) = Ideal.Quotient.mk (Ideal.span {algebraMap 𝒪 T π}) := by
    ext x
    show Ideal.quotEquivOfEq hbot ((RingEquiv.quotientBot T).symm x) = _
    have hs : (RingEquiv.quotientBot T).symm x = Ideal.Quotient.mk ⊥ x := by
      rw [RingEquiv.symm_apply_eq]; exact (RingEquiv.quotientBot_mk x).symm
    rw [hs, Ideal.quotEquivOfEq_mk]
  have : CommRingCat.ofHom (Ideal.Quotient.mk (Ideal.span {algebraMap 𝒪 T π})) = e.toCommRingCatIso.hom := by
    rw [← he]; rfl
  rw [this]
  infer_instance

theorem isLocallyConstant_degF (val : ∀ {T : Type} [CommRing T] [Algebra 𝒪 T] {ψT : Onr →ₐ[𝒪] T} {E : FakeEllipticCurve Λ N T},
      FakeEllipticCurve.Rigidification r π A₀ ψT E → ↥(Spec (CommRingCat.of (T ⧸ Ideal.span {algebraMap 𝒪 T π}))) → ℕ)
    (huniq : ∀ (d : ℕ) (x : ↥(Xs d)) (m m' : ℕ), DegAt π A₀ χC fM Xs ξ ptX val d x m → DegAt π A₀ χC fM Xs ξ ptX val d x m' → m = m')
    (hs0 : ∀ (d : ℕ) (T : Type) [CommRing T] [Algebra C T]
            (x : SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap C T))) (ξ d ≫ Limits.pullback.snd fM (Spec.map (CommRingCat.ofHom (algebraMap 𝒪 C))))),
            algebraMap C T (algebraMap 𝒪 C π) = 0)
    (hx3 : ∀ (d : ℕ) (T : Type) [CommRing T] [Algebra C T] [Algebra 𝒪 T] [IsScalarTower 𝒪 C T]
              (ψT : Onr →ₐ[𝒪] T) (hψT : ψT = (IsScalarTower.toAlgHom 𝒪 C T).comp χC)
              (h0 : algebraMap C T (algebraMap 𝒪 C π) = 0) (x : SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap C T))) (ξ d ≫ Limits.pullback.snd fM (Spec.map (CommRingCat.ofHom (algebraMap 𝒪 C))))),
              ∃ (u : FakeEllipticCurve.WithFullLevel Λ N n T) (ρ : FakeEllipticCurve.Rigidification r π A₀ ψT u.1) (hd : ρ.d = d),
                ptX d T ψT hψT u ρ hd h0 = x)
    (hval : ∀ (T : Type) [CommRing T] [Algebra 𝒪 T] (ψT : Onr →ₐ[𝒪] T) (E : FakeEllipticCurve Λ N T)
      (ρ : FakeEllipticCurve.Rigidification r π A₀ ψT E), IsLocallyConstant (val ρ))
    (d : ℕ) : IsLocallyConstant (degF π A₀ χC fM Xs ξ ptX val d) := by
  classical
  rw [IsLocallyConstant.iff_exists_open]
  intro x

  obtain ⟨R, t, ht, y₀, hy₀⟩ := (Xs d).exists_Spec_apply_eq x
  let T : Type := ↥R
  let φ : CommRingCat.of C ⟶ CommRingCat.of T := Spec.preimage (t ≫ strMap fM Xs ξ d)
  letI iC : Algebra C T := φ.hom.toAlgebra
  letI i𝒪 : Algebra 𝒪 T := (φ.hom.comp (algebraMap 𝒪 C)).toAlgebra
  haveI : IsScalarTower 𝒪 C T := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  have hmap : Spec.map (CommRingCat.ofHom (algebraMap C T)) = t ≫ strMap fM Xs ξ d := by
    show Spec.map (CommRingCat.ofHom φ.hom) = _
    rw [CommRingCat.ofHom_hom, Spec.map_preimage]
  let xT : SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap C T))) (strMap fM Xs ξ d) := ⟨t, hmap.symm⟩
  have h0 : algebraMap C T (algebraMap 𝒪 C π) = 0 := hs0 d T xT
  obtain ⟨u, ρ, hd, hx⟩ := hx3 d T ((IsScalarTower.toAlgHom 𝒪 C T).comp χC) rfl h0 xT
  have hpt : (ptX d T ((IsScalarTower.toAlgHom 𝒪 C T).comp χC) rfl u ρ hd h0).1 = t := by rw [hx]

  have hπT : algebraMap 𝒪 T π = 0 := h0
  haveI hiso := isIso_specMap_quotientMk π hπT
  let mkS := Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (Ideal.span {algebraMap 𝒪 T π})))
  let h : ↥(Spec (CommRingCat.of (T ⧸ Ideal.span {algebraMap 𝒪 T π}))) ≃ₜ ↥(Spec (CommRingCat.of T)) := mkS.homeomorph
  have hread : ∀ q, degF π A₀ χC fM Xs ξ ptX val d (t.base (h q)) = val ρ q := by
    intro q
    rw [← hpt]
    exact degF_ptX_apply π A₀ χC fM Xs ξ ptX val huniq d T u ρ hd h0 q

  have hlc := (hval T ((IsScalarTower.toAlgHom 𝒪 C T).comp χC) u.1 ρ)
  rw [IsLocallyConstant.iff_exists_open] at hlc
  obtain ⟨V, hVo, hyV, hV⟩ := hlc (h.symm y₀)
  refine ⟨t.base '' (h '' V), ?_, ?_, ?_⟩
  · exact ht.base_open.isOpenMap _ (h.isOpenMap _ hVo)
  · exact ⟨h (h.symm y₀), ⟨_, hyV, rfl⟩, by rw [h.apply_symm_apply, hy₀]⟩
  · rintro x' ⟨_, ⟨q, hq, rfl⟩, rfl⟩
    rw [hread q, ← hy₀, ← h.apply_symm_apply y₀, hread (h.symm y₀)]
    exact hV q hq

def U1Statement (val : ∀ {T : Type} [CommRing T] [Algebra 𝒪 T] {ψT : Onr →ₐ[𝒪] T} {E : FakeEllipticCurve Λ N T},
      FakeEllipticCurve.Rigidification r π A₀ ψT E → ↥(Spec (CommRingCat.of (T ⧸ Ideal.span {algebraMap 𝒪 T π}))) → ℕ) : Prop :=
  ∀ (d : ℕ) (x : ↥(Xs d)) (m m' : ℕ),
    DegAt π A₀ χC fM Xs ξ ptX val d x m → DegAt π A₀ χC fM Xs ξ ptX val d x m' → m = m'

end DegA
p2m_reactivate "P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_exists_opens_ratioWindow_degree_laws_of_rigidifiedToG_of_bdd.Ws16WC.Clopen P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_exists_opens_ratioWindow_degree_laws_of_rigidifiedToG_of_bdd.Ws16WC.DEGb.DegreeMaps P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_exists_opens_ratioWindow_degree_laws_of_rigidifiedToG_of_bdd.Ws16WC.DEGb P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_exists_opens_ratioWindow_degree_laws_of_rigidifiedToG_of_bdd.Ws16WC"
end ChartDict3
p2m_reactivate "P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_exists_opens_ratioWindow_degree_laws_of_rigidifiedToG_of_bdd.Ws16WC.Clopen P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_exists_opens_ratioWindow_degree_laws_of_rigidifiedToG_of_bdd.Ws16WC.DEGb.DegreeMaps P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_exists_opens_ratioWindow_degree_laws_of_rigidifiedToG_of_bdd.Ws16WC.DEGb P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_exists_opens_ratioWindow_degree_laws_of_rigidifiedToG_of_bdd.Ws16WC"

namespace ChartDict3

theorem exists_pullback_presentation
    {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} {N n r : ℕ}
    {𝒪 : Type} [CommRing 𝒪] (π : 𝒪) {Onr : Type} [CommRing Onr] [Algebra 𝒪 Onr]
    (A₀ : FakeEllipticCurve Λ N (Onr ⧸ Ideal.span {algebraMap 𝒪 Onr π}))
    {C : Type} [CommRing C] [Algebra 𝒪 C]
    {T T' : Type} [CommRing T] [Algebra C T] [Algebra 𝒪 T] [IsScalarTower 𝒪 C T]
    [CommRing T'] [Algebra C T'] [Algebra 𝒪 T'] [IsScalarTower 𝒪 C T'] (φ : T →ₐ[C] T')
    (ψT : Onr →ₐ[𝒪] T) (u : FakeEllipticCurve.WithFullLevel Λ N n T)
    (ρ : FakeEllipticCurve.Rigidification r π A₀ ψT u.1) :
    ∃ (u' : FakeEllipticCurve.WithFullLevel Λ N n T') (g : u'.1.A ⟶ u.1.A)
      (hg : FakeEllipticCurve.IsPullbackVia (φ : T →+* T') u.1 u'.1 g)
      (ρ' : FakeEllipticCurve.Rigidification r π A₀ ((φ.restrictScalars 𝒪).comp ψT) u'.1),
      (u'.2.P).1 ≫ g = Spec.map (CommRingCat.ofHom (φ : T →+* T')) ≫ (u.2.P).1 ∧
      FakeEllipticCurve.Rigidification.IsPullbackVia (φ.restrictScalars 𝒪) g hg ρ ρ' ∧ ρ'.d = ρ.d := by
  obtain ⟨E', g, hg0, h1, h2, h3, h4⟩ := FakeEllipticCurve.exists_isPullback_levelIff (φ : T →+* T') u.1
  have hg : FakeEllipticCurve.IsPullbackVia (φ : T →+* T') u.1 E' g := ⟨hg0, h1, h2, fun t' P => h3 t' P⟩
  obtain ⟨P', hP'⟩ := FakeEllipticCurve.FullLevel.exists_comp_eq_specMap_comp_of_isPullbackVia n (φ : T →+* T') u.1 E' g hg u.2
  obtain ⟨ρ', hρ'⟩ := FakeEllipticCurve.Rigidification.exists_isPullbackVia_of_isPullbackVia 𝒪 π Onr Λ A₀ T T' (φ.restrictScalars 𝒪) ψT u.1 E' g hg ρ
  have hd : ρ'.d = ρ.d := by
    obtain ⟨_, _, _, _, _, _, hd, _⟩ := hρ'
    exact hd
  exact ⟨⟨E', P'⟩, g, hg, ρ', hP', hρ', hd⟩

end ChartDict3
p2m_reactivate "P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_exists_opens_ratioWindow_degree_laws_of_rigidifiedToG_of_bdd.Ws16WC.Clopen P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_exists_opens_ratioWindow_degree_laws_of_rigidifiedToG_of_bdd.Ws16WC.DEGb.DegreeMaps P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_exists_opens_ratioWindow_degree_laws_of_rigidifiedToG_of_bdd.Ws16WC.DEGb P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_exists_opens_ratioWindow_degree_laws_of_rigidifiedToG_of_bdd.Ws16WC"

set_option autoImplicit false

open scoped TensorProduct Quaternion NumberField
p2m_open "CategoryTheory AlgebraicGeometry QuaternionAlgebra IsDedekindDomain CerednikDrinfeld P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_exists_opens_ratioWindow_degree_laws_of_rigidifiedToG_of_bdd.CerednikDrinfeld CerednikDrinfeld.QM P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_exists_opens_ratioWindow_degree_laws_of_rigidifiedToG_of_bdd.CerednikDrinfeld.QM CerednikDrinfeld.FormalOmega CerednikDrinfeld.SpecialFormal NeronModelInfra~schemeHomOverComp_coe GoodReductionJacobian"

open LT.LatticeTree (FullLattice)

noncomputable section

namespace ChartDict3

section castlemmas
variable {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} {N r : ℕ}
  {𝒪 : Type} [CommRing 𝒪] {π : 𝒪} {Onr : Type} [CommRing Onr] [Algebra 𝒪 Onr]
  {A₀ : FakeEllipticCurve Λ N (Onr ⧸ Ideal.span {algebraMap 𝒪 Onr π})}

def Rigidification.castLeg {T : Type} [CommRing T] [Algebra 𝒪 T] {ψ₁ ψ₂ : Onr →ₐ[𝒪] T} (e : ψ₁ = ψ₂)
    {E : FakeEllipticCurve Λ N T} (ρ : FakeEllipticCurve.Rigidification r π A₀ ψ₁ E) :
    FakeEllipticCurve.Rigidification r π A₀ ψ₂ E := e ▸ ρ

theorem Rigidification.castLeg_d {T : Type} [CommRing T] [Algebra 𝒪 T] {ψ₁ ψ₂ : Onr →ₐ[𝒪] T} (e : ψ₁ = ψ₂)
    {E : FakeEllipticCurve Λ N T} (ρ : FakeEllipticCurve.Rigidification r π A₀ ψ₁ E) :
    (Rigidification.castLeg e ρ).d = ρ.d := by subst e; rfl

theorem val_castLeg
    (val : ∀ {T : Type} [CommRing T] [Algebra 𝒪 T] {ψT : Onr →ₐ[𝒪] T} {E : FakeEllipticCurve Λ N T},
      FakeEllipticCurve.Rigidification r π A₀ ψT E → ↥(Spec (CommRingCat.of (T ⧸ Ideal.span {algebraMap 𝒪 T π}))) → ℕ)
    {T : Type} [CommRing T] [Algebra 𝒪 T] {ψ₁ ψ₂ : Onr →ₐ[𝒪] T} (e : ψ₁ = ψ₂)
    {E : FakeEllipticCurve Λ N T} (ρ : FakeEllipticCurve.Rigidification r π A₀ ψ₁ E)
    (q : ↥(Spec (CommRingCat.of (T ⧸ Ideal.span {algebraMap 𝒪 T π})))) :
    val (Rigidification.castLeg e ρ) q = val ρ q := by subst e; rfl

end castlemmas
p2m_reactivate "P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_exists_opens_ratioWindow_degree_laws_of_rigidifiedToG_of_bdd.Ws16WC.Clopen P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_exists_opens_ratioWindow_degree_laws_of_rigidifiedToG_of_bdd.Ws16WC.DEGb.DegreeMaps P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_exists_opens_ratioWindow_degree_laws_of_rigidifiedToG_of_bdd.Ws16WC.DEGb P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_exists_opens_ratioWindow_degree_laws_of_rigidifiedToG_of_bdd.Ws16WC"

section pointlemmas

theorem primeSpectrum_subsingleton_of_field {K : Type} [CommRing K] (hK : ∀ I : Ideal K, I.IsPrime → I = ⊥) (z : K) :
    Subsingleton ↥(Spec (CommRingCat.of (K ⧸ Ideal.span {z}))) := by
  constructor
  intro p p'
  have key : ∀ p : ↥(Spec (CommRingCat.of (K ⧸ Ideal.span {z}))), p.asIdeal = ⊥ := by
    intro p
    have h1 : (p.asIdeal.comap (Ideal.Quotient.mk (Ideal.span {z}))) = ⊥ := hK _ (Ideal.comap_isPrime _ _)
    have h2 := Ideal.map_comap_of_surjective (Ideal.Quotient.mk (Ideal.span {z})) Ideal.Quotient.mk_surjective p.asIdeal
    rw [h1, Ideal.map_bot] at h2
    exact h2.symm
  exact PrimeSpectrum.ext ((key p).trans (key p').symm)

theorem specMap_algebraMap_residueField_base {R : Type} [CommRing R] (q : ↥(Spec (CommRingCat.of R)))
    (p : ↥(Spec (CommRingCat.of q.asIdeal.ResidueField))) :
    (Spec.map (CommRingCat.ofHom (algebraMap R q.asIdeal.ResidueField))).base p = q := by
  apply PrimeSpectrum.ext
  show Ideal.comap (algebraMap R q.asIdeal.ResidueField) p.asIdeal = q.asIdeal
  rw [Ideal.eq_bot_of_prime p.asIdeal, ← RingHom.ker_eq_comap_bot, Ideal.ker_algebraMap_residueField]

end pointlemmas
p2m_reactivate "P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_exists_opens_ratioWindow_degree_laws_of_rigidifiedToG_of_bdd.Ws16WC.Clopen P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_exists_opens_ratioWindow_degree_laws_of_rigidifiedToG_of_bdd.Ws16WC.DEGb.DegreeMaps P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_exists_opens_ratioWindow_degree_laws_of_rigidifiedToG_of_bdd.Ws16WC.DEGb P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_exists_opens_ratioWindow_degree_laws_of_rigidifiedToG_of_bdd.Ws16WC"

section DegA
variable {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} {N n r : ℕ}
  {𝒪 : Type} [CommRing 𝒪] (π : 𝒪) {Onr : Type} [CommRing Onr] [Algebra 𝒪 Onr]
  (A₀ : FakeEllipticCurve Λ N (Onr ⧸ Ideal.span {algebraMap 𝒪 Onr π}))
  {C : Type} [CommRing C] [Algebra 𝒪 C] (χC : Onr →ₐ[𝒪] C)
  {M : Scheme.{0}} (fM : M ⟶ Spec (CommRingCat.of 𝒪))
  (Xs : ℕ → Scheme.{0}) (ξ : ∀ d, Xs d ⟶ Limits.pullback fM (Spec.map (CommRingCat.ofHom (algebraMap 𝒪 C))))
  (ptX : ∀ (d : ℕ) (T : Type) [CommRing T] [Algebra C T] [Algebra 𝒪 T] [IsScalarTower 𝒪 C T]
            (ψT : Onr →ₐ[𝒪] T) (_ : ψT = (IsScalarTower.toAlgHom 𝒪 C T).comp χC)
            (u : FakeEllipticCurve.WithFullLevel Λ N n T) (ρ : FakeEllipticCurve.Rigidification r π A₀ ψT u.1),
            ρ.d = d → algebraMap C T (algebraMap 𝒪 C π) = 0 →
              SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap C T))) (ξ d ≫ Limits.pullback.snd fM (Spec.map (CommRingCat.ofHom (algebraMap 𝒪 C)))))

theorem ptX_castLeg (d : ℕ) (T : Type) [CommRing T] [Algebra C T] [Algebra 𝒪 T] [IsScalarTower 𝒪 C T]
    {ψ₁ ψ₂ : Onr →ₐ[𝒪] T} (e : ψ₁ = ψ₂) (h₁ : ψ₁ = (IsScalarTower.toAlgHom 𝒪 C T).comp χC) (h₂ : ψ₂ = (IsScalarTower.toAlgHom 𝒪 C T).comp χC)
    (u : FakeEllipticCurve.WithFullLevel Λ N n T) (ρ : FakeEllipticCurve.Rigidification r π A₀ ψ₁ u.1)
    (hd₁ : ρ.d = d) (hd₂ : (Rigidification.castLeg e ρ).d = d) (h0 : algebraMap C T (algebraMap 𝒪 C π) = 0) :
    ptX d T ψ₂ h₂ u (Rigidification.castLeg e ρ) hd₂ h0 = ptX d T ψ₁ h₁ u ρ hd₁ h0 := by
  subst e; rfl

theorem val_eq_val_ref (val : ∀ {T : Type} [CommRing T] [Algebra 𝒪 T] {ψT : Onr →ₐ[𝒪] T} {E : FakeEllipticCurve Λ N T},
      FakeEllipticCurve.Rigidification r π A₀ ψT E → ↥(Spec (CommRingCat.of (T ⧸ Ideal.span {algebraMap 𝒪 T π}))) → ℕ)
    (hx2 : ∀ (d : ℕ) (T T' : Type) [CommRing T] [Algebra C T] [Algebra 𝒪 T] [IsScalarTower 𝒪 C T]
              [CommRing T'] [Algebra C T'] [Algebra 𝒪 T'] [IsScalarTower 𝒪 C T'] (φ : T →ₐ[C] T')
              (ψT : Onr →ₐ[𝒪] T) (hψT : ψT = (IsScalarTower.toAlgHom 𝒪 C T).comp χC)
              (hψT' : (φ.restrictScalars 𝒪).comp ψT = (IsScalarTower.toAlgHom 𝒪 C T').comp χC)
              (u : FakeEllipticCurve.WithFullLevel Λ N n T) (u' : FakeEllipticCurve.WithFullLevel Λ N n T')
              (ρ : FakeEllipticCurve.Rigidification r π A₀ ψT u.1)
              (ρ' : FakeEllipticCurve.Rigidification r π A₀ ((φ.restrictScalars 𝒪).comp ψT) u'.1)
              (g : u'.1.A ⟶ u.1.A) (hg : FakeEllipticCurve.IsPullbackVia (φ : T →+* T') u.1 u'.1 g)
              (hd : ρ.d = d) (hd' : ρ'.d = d) (h0 : algebraMap C T (algebraMap 𝒪 C π) = 0) (h0' : algebraMap C T' (algebraMap 𝒪 C π) = 0),
              (u'.2.P).1 ≫ g = Spec.map (CommRingCat.ofHom (φ : T →+* T')) ≫ (u.2.P).1 →
              FakeEllipticCurve.Rigidification.IsPullbackVia (φ.restrictScalars 𝒪) g hg ρ ρ' →
                (ptX d T' ((φ.restrictScalars 𝒪).comp ψT) hψT' u' ρ' hd' h0').1 =
                  Spec.map (CommRingCat.ofHom (φ : T →+* T')) ≫ (ptX d T ψT hψT u ρ hd h0).1)
    (hx4 : ∀ (d : ℕ) (T : Type) [CommRing T] [Algebra C T] [Algebra 𝒪 T] [IsScalarTower 𝒪 C T]
              (ψT : Onr →ₐ[𝒪] T) (hψT : ψT = (IsScalarTower.toAlgHom 𝒪 C T).comp χC)
              (h0 : algebraMap C T (algebraMap 𝒪 C π) = 0)
              (u u' : FakeEllipticCurve.WithFullLevel Λ N n T)
              (ρ : FakeEllipticCurve.Rigidification r π A₀ ψT u.1) (ρ' : FakeEllipticCurve.Rigidification r π A₀ ψT u'.1)
              (hd : ρ.d = d) (hd' : ρ'.d = d),
              (ptX d T ψT hψT u ρ hd h0 = ptX d T ψT hψT u' ρ' hd' h0 ↔
                ∃ (i : u.1.A ≅ u'.1.A) (hi : i.hom ≫ u'.1.f = u.1.f), FakeEllipticCurve.WithFullLevel.IsoVia u u' i hi ∧
                  ∃ (ib : ρ.Eb.A ⟶ ρ'.Eb.A) (_ : ib ≫ ρ'.gb = ρ.gb ≫ i.hom) (_ : ib ≫ ρ'.Eb.f = ρ.Eb.f)
                    (uA : ρ'.Ab.A ⟶ ρ.Ab.A) (_ : FakeEllipticCurve.IsPullbackVia (RingHom.id _) ρ.Ab ρ'.Ab uA) (_ : uA ≫ ρ.gA = ρ'.gA),
                    ib ≫ ρ'.φ ≫ uA = ρ.φ))
    (hα : ∀ {T T' : Type} [CommRing T] [Algebra 𝒪 T] [CommRing T'] [Algebra 𝒪 T'] (f : T →ₐ[𝒪] T')
      {ψT : Onr →ₐ[𝒪] T} {E : FakeEllipticCurve Λ N T} {E' : FakeEllipticCurve Λ N T'} (g : E'.A ⟶ E.A)
      (hg : FakeEllipticCurve.IsPullbackVia (f : T →+* T') E E' g)
      (ρ : FakeEllipticCurve.Rigidification r π A₀ ψT E) (ρ' : FakeEllipticCurve.Rigidification r π A₀ (f.comp ψT) E'),
      FakeEllipticCurve.Rigidification.IsPullbackVia f g hg ρ ρ' →
      ∀ (hle : Ideal.span {algebraMap 𝒪 T π} ≤ (Ideal.span {algebraMap 𝒪 T' π}).comap (f : T →+* T'))
        (q' : ↥(Spec (CommRingCat.of (T' ⧸ Ideal.span {algebraMap 𝒪 T' π})))),
        val ρ' q' = val ρ ((Spec.map (CommRingCat.ofHom (Ideal.quotientMap (Ideal.span {algebraMap 𝒪 T' π}) (f : T →+* T') hle))).base q'))
    (hβ : ∀ {T : Type} [CommRing T] [Algebra 𝒪 T] {ψT : Onr →ₐ[𝒪] T}
      (u u' : FakeEllipticCurve.WithFullLevel Λ N n T)
      (ρ : FakeEllipticCurve.Rigidification r π A₀ ψT u.1) (ρ' : FakeEllipticCurve.Rigidification r π A₀ ψT u'.1)
      (i : u.1.A ≅ u'.1.A) (hi : i.hom ≫ u'.1.f = u.1.f), FakeEllipticCurve.WithFullLevel.IsoVia u u' i hi →
      ∀ (ib : ρ.Eb.A ⟶ ρ'.Eb.A) (_ : ib ≫ ρ'.gb = ρ.gb ≫ i.hom) (_ : ib ≫ ρ'.Eb.f = ρ.Eb.f)
        (uA : ρ'.Ab.A ⟶ ρ.Ab.A) (_ : FakeEllipticCurve.IsPullbackVia (RingHom.id _) ρ.Ab ρ'.Ab uA) (_ : uA ≫ ρ.gA = ρ'.gA),
        ib ≫ ρ'.φ ≫ uA = ρ.φ →
        ∀ q : ↥(Spec (CommRingCat.of (T ⧸ Ideal.span {algebraMap 𝒪 T π}))), val ρ q = val ρ' q)
    (d : ℕ) (x : ↥(Xs d))
    (K₀ : Type) [CommRing K₀] [Algebra C K₀] [Algebra 𝒪 K₀] [IsScalarTower 𝒪 C K₀]
    (hK₀ : ∀ I : Ideal K₀, I.IsPrime → I = ⊥)
    (t : Spec (CommRingCat.of K₀) ⟶ Xs d)
    (hK : Spec.map (CommRingCat.ofHom (algebraMap C K₀)) = t ≫ strMap fM Xs ξ d)
    (hfac : ∀ (K : Type) [Field K] (f : Spec (CommRingCat.of K) ⟶ Xs d), f.base (IsLocalRing.closedPoint K) = x →
      ∃ e : CommRingCat.of K₀ ⟶ CommRingCat.of K, Spec.map e ≫ t = f)
    (u₀ : FakeEllipticCurve.WithFullLevel Λ N n K₀)
    (ρ₀ : FakeEllipticCurve.Rigidification r π A₀ ((IsScalarTower.toAlgHom 𝒪 C K₀).comp χC) u₀.1)
    (hd₀ : ρ₀.d = d) (h0₀ : algebraMap C K₀ (algebraMap 𝒪 C π) = 0)
    (hpt₀ : (ptX d K₀ _ rfl u₀ ρ₀ hd₀ h0₀).1 = t)
    (q₀ : ↥(Spec (CommRingCat.of (K₀ ⧸ Ideal.span {algebraMap 𝒪 K₀ π}))))
    (T : Type) [CommRing T] [Algebra C T] [Algebra 𝒪 T] [IsScalarTower 𝒪 C T]
    (u : FakeEllipticCurve.WithFullLevel Λ N n T)
    (ρ : FakeEllipticCurve.Rigidification r π A₀ ((IsScalarTower.toAlgHom 𝒪 C T).comp χC) u.1)
    (hd : ρ.d = d) (h0 : algebraMap C T (algebraMap 𝒪 C π) = 0)
    (q : ↥(Spec (CommRingCat.of (T ⧸ Ideal.span {algebraMap 𝒪 T π}))))
    (hx : (ptX d T ((IsScalarTower.toAlgHom 𝒪 C T).comp χC) rfl u ρ hd h0).1.base
        ((Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (Ideal.span {algebraMap 𝒪 T π})))).base q) = x) :
    val ρ q = val ρ₀ q₀ := by
  classical

  let K : Type := q.asIdeal.ResidueField
  letI iTK : Algebra T K := ((algebraMap (T ⧸ Ideal.span {algebraMap 𝒪 T π}) K).comp (Ideal.Quotient.mk _)).toAlgebra
  letI iCK : Algebra C K := ((algebraMap T K).comp (algebraMap C T)).toAlgebra
  letI i𝒪K : Algebra 𝒪 K := ((algebraMap T K).comp (algebraMap 𝒪 T)).toAlgebra
  haveI : IsScalarTower C T K := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  haveI : IsScalarTower 𝒪 T K := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  haveI : IsScalarTower 𝒪 C K := IsScalarTower.of_algebraMap_eq (fun z =>
    congrArg (algebraMap T K) (IsScalarTower.algebraMap_apply 𝒪 C T z))
  let φq : T →ₐ[C] K := IsScalarTower.toAlgHom C T K
  have hφq : (φq : T →+* K) = (algebraMap (T ⧸ Ideal.span {algebraMap 𝒪 T π}) K).comp (Ideal.Quotient.mk _) := rfl
  have h0K : algebraMap C K (algebraMap 𝒪 C π) = 0 := by
    show algebraMap T K (algebraMap C T (algebraMap 𝒪 C π)) = 0
    rw [h0, map_zero]
  have hψK : (φq.restrictScalars 𝒪).comp ((IsScalarTower.toAlgHom 𝒪 C T).comp χC) =
      (IsScalarTower.toAlgHom 𝒪 C K).comp χC := by
    ext z
    show φq (algebraMap C T (χC z)) = algebraMap C K (χC z)
    exact φq.commutes _

  obtain ⟨u₁, g₁, hg₁, ρ₁, hP₁, hρ₁, hd₁⟩ :=
    exists_pullback_presentation π A₀ φq ((IsScalarTower.toAlgHom 𝒪 C T).comp χC) u ρ
  have hd₁' : ρ₁.d = d := hd₁.trans hd
  have hpt₁ := hx2 d T K φq _ rfl hψK u u₁ ρ ρ₁ g₁ hg₁ hd hd₁' h0 h0K hP₁ hρ₁

  let f : Spec (CommRingCat.of K) ⟶ Xs d :=
    Spec.map (CommRingCat.ofHom (φq : T →+* K)) ≫ (ptX d T ((IsScalarTower.toAlgHom 𝒪 C T).comp χC) rfl u ρ hd h0).1
  have hSpecφ : Spec.map (CommRingCat.ofHom (φq : T →+* K)) =
      Spec.map (CommRingCat.ofHom (algebraMap (T ⧸ Ideal.span {algebraMap 𝒪 T π}) K)) ≫
        Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (Ideal.span {algebraMap 𝒪 T π}))) := by
    rw [hφq, CommRingCat.ofHom_comp, Spec.map_comp]
  have hfx : f.base (IsLocalRing.closedPoint K) = x := by
    rw [← hx]
    show (Spec.map (CommRingCat.ofHom (φq : T →+* K)) ≫ (ptX d T _ rfl u ρ hd h0).1).base _ = _
    rw [hSpecφ]
    show (ptX d T _ rfl u ρ hd h0).1.base ((Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk _))).base
      ((Spec.map (CommRingCat.ofHom (algebraMap (T ⧸ Ideal.span {algebraMap 𝒪 T π}) K))).base (IsLocalRing.closedPoint K))) = _
    rw [specMap_algebraMap_residueField_base]
  obtain ⟨e, he⟩ := hfac K f hfx

  have hstr : (ptX d T ((IsScalarTower.toAlgHom 𝒪 C T).comp χC) rfl u ρ hd h0).1 ≫ strMap fM Xs ξ d =
      Spec.map (CommRingCat.ofHom (algebraMap C T)) := (ptX d T _ rfl u ρ hd h0).2
  have heC : e.hom.comp (algebraMap C K₀) = algebraMap C K := by
    have h1 : Spec.map (CommRingCat.ofHom (e.hom.comp (algebraMap C K₀))) = Spec.map (CommRingCat.ofHom (algebraMap C K)) := by
      rw [CommRingCat.ofHom_comp, Spec.map_comp, CommRingCat.ofHom_hom, hK, ← Category.assoc, he]
      show (Spec.map (CommRingCat.ofHom (φq : T →+* K)) ≫ (ptX d T _ rfl u ρ hd h0).1) ≫ strMap fM Xs ξ d = _
      rw [Category.assoc, hstr, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
      rfl
    exact congrArg CommRingCat.Hom.hom (Spec.map_inj.mp h1)
  let eC : K₀ →ₐ[C] K :=
    { toRingHom := e.hom, commutes' := fun c => by
        show e.hom (algebraMap C K₀ c) = algebraMap C K c
        rw [← heC]; rfl }
  have heC' : CommRingCat.ofHom (eC : K₀ →+* K) = e := rfl
  have hψ₂ : (eC.restrictScalars 𝒪).comp ((IsScalarTower.toAlgHom 𝒪 C K₀).comp χC) =
      (IsScalarTower.toAlgHom 𝒪 C K).comp χC := by
    ext z
    show eC (algebraMap C K₀ (χC z)) = algebraMap C K (χC z)
    exact eC.commutes _

  obtain ⟨u₂, g₂, hg₂, ρ₂, hP₂, hρ₂, hd₂⟩ :=
    exists_pullback_presentation π A₀ eC ((IsScalarTower.toAlgHom 𝒪 C K₀).comp χC) u₀ ρ₀
  have hd₂' : ρ₂.d = d := hd₂.trans hd₀
  have hpt₂ := hx2 d K₀ K eC _ rfl hψ₂ u₀ u₂ ρ₀ ρ₂ g₂ hg₂ hd₀ hd₂' h0₀ h0K hP₂ hρ₂
  have hpt₂' : (ptX d K _ hψ₂ u₂ ρ₂ hd₂' h0K).1 = f := by rw [hpt₂, hpt₀, heC']; exact he
  have hpt₁' : (ptX d K _ hψK u₁ ρ₁ hd₁' h0K).1 = f := hpt₁

  have hd₁c : (Rigidification.castLeg hψK ρ₁).d = d := by rw [Rigidification.castLeg_d]; exact hd₁'
  have hd₂c : (Rigidification.castLeg hψ₂ ρ₂).d = d := by rw [Rigidification.castLeg_d]; exact hd₂'
  have heq : ptX d K ((IsScalarTower.toAlgHom 𝒪 C K).comp χC) rfl u₁ (Rigidification.castLeg hψK ρ₁) hd₁c h0K =
      ptX d K ((IsScalarTower.toAlgHom 𝒪 C K).comp χC) rfl u₂ (Rigidification.castLeg hψ₂ ρ₂) hd₂c h0K := by
    apply Subtype.ext
    rw [ptX_castLeg π A₀ χC fM Xs ξ ptX d K hψK hψK rfl u₁ ρ₁ hd₁' hd₁c h0K,
      ptX_castLeg π A₀ χC fM Xs ξ ptX d K hψ₂ hψ₂ rfl u₂ ρ₂ hd₂' hd₂c h0K, hpt₁', hpt₂']
  obtain ⟨i, hi, hI, ib, hib, hibf, uA, huA, huAg, hcorr⟩ :=
    (hx4 d K _ rfl h0K u₁ u₂ _ _ hd₁c hd₂c).mp heq
  obtain ⟨qK⟩ : Nonempty ↥(Spec (CommRingCat.of (K ⧸ Ideal.span {algebraMap 𝒪 K π}))) := by
    have hπK : algebraMap 𝒪 K π = 0 := by rw [IsScalarTower.algebraMap_apply 𝒪 C K]; exact h0K
    haveI : Nontrivial (K ⧸ Ideal.span {algebraMap 𝒪 K π}) :=
      Ideal.Quotient.nontrivial_iff.mpr (by rw [Ne, hπK, Ideal.span_singleton_eq_top]; exact not_isUnit_zero)
    infer_instance
  have h12 : val ρ₁ qK = val ρ₂ qK := by
    have := hβ u₁ u₂ _ _ i hi hI ib hib hibf uA huA huAg hcorr qK
    rwa [val_castLeg val, val_castLeg val] at this

  have hle₁ : Ideal.span {algebraMap 𝒪 T π} ≤ (Ideal.span {algebraMap 𝒪 K π}).comap ((φq.restrictScalars 𝒪 : T →ₐ[𝒪] K) : T →+* K) := by
    rw [Ideal.span_le, Set.singleton_subset_iff]
    show (φq.restrictScalars 𝒪) (algebraMap 𝒪 T π) ∈ Ideal.span {algebraMap 𝒪 K π}
    rw [AlgHom.commutes]; exact Ideal.subset_span rfl
  have hle₂ : Ideal.span {algebraMap 𝒪 K₀ π} ≤ (Ideal.span {algebraMap 𝒪 K π}).comap ((eC.restrictScalars 𝒪 : K₀ →ₐ[𝒪] K) : K₀ →+* K) := by
    rw [Ideal.span_le, Set.singleton_subset_iff]
    show (eC.restrictScalars 𝒪) (algebraMap 𝒪 K₀ π) ∈ Ideal.span {algebraMap 𝒪 K π}
    rw [AlgHom.commutes]; exact Ideal.subset_span rfl
  have hα₁ := hα (φq.restrictScalars 𝒪) g₁ hg₁ ρ ρ₁ hρ₁ hle₁ qK
  have hα₂ := hα (eC.restrictScalars 𝒪) g₂ hg₂ ρ₀ ρ₂ hρ₂ hle₂ qK

  have hq₁ : (Spec.map (CommRingCat.ofHom (Ideal.quotientMap (Ideal.span {algebraMap 𝒪 K π})
      ((φq.restrictScalars 𝒪 : T →ₐ[𝒪] K) : T →+* K) hle₁))).base qK = q := by
    apply PrimeSpectrum.ext
    apply Ideal.comap_injective_of_surjective (Ideal.Quotient.mk (Ideal.span {algebraMap 𝒪 T π})) Ideal.Quotient.mk_surjective
    show Ideal.comap (Ideal.Quotient.mk _) (Ideal.comap (Ideal.quotientMap _ _ hle₁) qK.asIdeal) = Ideal.comap (Ideal.Quotient.mk _) q.asIdeal
    haveI : (Ideal.comap (Ideal.Quotient.mk (Ideal.span {algebraMap 𝒪 K π})) qK.asIdeal).IsPrime := Ideal.comap_isPrime _ _
    rw [Ideal.comap_comap, Ideal.quotientMap_comp_mk, ← Ideal.comap_comap, Ideal.eq_bot_of_prime (Ideal.comap (Ideal.Quotient.mk (Ideal.span {algebraMap 𝒪 K π})) qK.asIdeal),
      ← RingHom.ker_eq_comap_bot]
    show RingHom.ker ((algebraMap (T ⧸ Ideal.span {algebraMap 𝒪 T π}) K).comp (Ideal.Quotient.mk _)) = _
    rw [← RingHom.comap_ker, Ideal.ker_algebraMap_residueField]

  have hq₂ : (Spec.map (CommRingCat.ofHom (Ideal.quotientMap (Ideal.span {algebraMap 𝒪 K π})
      ((eC.restrictScalars 𝒪 : K₀ →ₐ[𝒪] K) : K₀ →+* K) hle₂))).base qK = q₀ := by
    haveI := primeSpectrum_subsingleton_of_field hK₀ (algebraMap 𝒪 K₀ π)
    exact Subsingleton.elim _ _
  calc val ρ q = val ρ₁ qK := by rw [hα₁, hq₁]
    _ = val ρ₂ qK := h12
    _ = val ρ₀ q₀ := by rw [hα₂, hq₂]

theorem exists_specMap_comp_fromSpecResidueField_eq {X : Scheme.{0}} (x : ↥X) (K : Type) [Field K]
    (f : Spec (CommRingCat.of K) ⟶ X) (h : f.base (IsLocalRing.closedPoint K) = x) :
    ∃ e : X.residueField x ⟶ CommRingCat.of K, Spec.map e ≫ X.fromSpecResidueField x = f := by
  subst h
  exact ⟨((Scheme.SpecToEquivOfField K X) f).2, (Scheme.SpecToEquivOfField K X).symm_apply_apply f⟩

theorem degAt_unique (val : ∀ {T : Type} [CommRing T] [Algebra 𝒪 T] {ψT : Onr →ₐ[𝒪] T} {E : FakeEllipticCurve Λ N T},
      FakeEllipticCurve.Rigidification r π A₀ ψT E → ↥(Spec (CommRingCat.of (T ⧸ Ideal.span {algebraMap 𝒪 T π}))) → ℕ)
    (hs0 : ∀ (d : ℕ) (T : Type) [CommRing T] [Algebra C T]
            (x : SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap C T))) (ξ d ≫ Limits.pullback.snd fM (Spec.map (CommRingCat.ofHom (algebraMap 𝒪 C))))),
            algebraMap C T (algebraMap 𝒪 C π) = 0)
    (hx2 : ∀ (d : ℕ) (T T' : Type) [CommRing T] [Algebra C T] [Algebra 𝒪 T] [IsScalarTower 𝒪 C T]
              [CommRing T'] [Algebra C T'] [Algebra 𝒪 T'] [IsScalarTower 𝒪 C T'] (φ : T →ₐ[C] T')
              (ψT : Onr →ₐ[𝒪] T) (hψT : ψT = (IsScalarTower.toAlgHom 𝒪 C T).comp χC)
              (hψT' : (φ.restrictScalars 𝒪).comp ψT = (IsScalarTower.toAlgHom 𝒪 C T').comp χC)
              (u : FakeEllipticCurve.WithFullLevel Λ N n T) (u' : FakeEllipticCurve.WithFullLevel Λ N n T')
              (ρ : FakeEllipticCurve.Rigidification r π A₀ ψT u.1)
              (ρ' : FakeEllipticCurve.Rigidification r π A₀ ((φ.restrictScalars 𝒪).comp ψT) u'.1)
              (g : u'.1.A ⟶ u.1.A) (hg : FakeEllipticCurve.IsPullbackVia (φ : T →+* T') u.1 u'.1 g)
              (hd : ρ.d = d) (hd' : ρ'.d = d) (h0 : algebraMap C T (algebraMap 𝒪 C π) = 0) (h0' : algebraMap C T' (algebraMap 𝒪 C π) = 0),
              (u'.2.P).1 ≫ g = Spec.map (CommRingCat.ofHom (φ : T →+* T')) ≫ (u.2.P).1 →
              FakeEllipticCurve.Rigidification.IsPullbackVia (φ.restrictScalars 𝒪) g hg ρ ρ' →
                (ptX d T' ((φ.restrictScalars 𝒪).comp ψT) hψT' u' ρ' hd' h0').1 =
                  Spec.map (CommRingCat.ofHom (φ : T →+* T')) ≫ (ptX d T ψT hψT u ρ hd h0).1)
    (hx3 : ∀ (d : ℕ) (T : Type) [CommRing T] [Algebra C T] [Algebra 𝒪 T] [IsScalarTower 𝒪 C T]
              (ψT : Onr →ₐ[𝒪] T) (hψT : ψT = (IsScalarTower.toAlgHom 𝒪 C T).comp χC)
              (h0 : algebraMap C T (algebraMap 𝒪 C π) = 0) (x : SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap C T))) (ξ d ≫ Limits.pullback.snd fM (Spec.map (CommRingCat.ofHom (algebraMap 𝒪 C))))),
              ∃ (u : FakeEllipticCurve.WithFullLevel Λ N n T) (ρ : FakeEllipticCurve.Rigidification r π A₀ ψT u.1) (hd : ρ.d = d),
                ptX d T ψT hψT u ρ hd h0 = x)
    (hx4 : ∀ (d : ℕ) (T : Type) [CommRing T] [Algebra C T] [Algebra 𝒪 T] [IsScalarTower 𝒪 C T]
              (ψT : Onr →ₐ[𝒪] T) (hψT : ψT = (IsScalarTower.toAlgHom 𝒪 C T).comp χC)
              (h0 : algebraMap C T (algebraMap 𝒪 C π) = 0)
              (u u' : FakeEllipticCurve.WithFullLevel Λ N n T)
              (ρ : FakeEllipticCurve.Rigidification r π A₀ ψT u.1) (ρ' : FakeEllipticCurve.Rigidification r π A₀ ψT u'.1)
              (hd : ρ.d = d) (hd' : ρ'.d = d),
              (ptX d T ψT hψT u ρ hd h0 = ptX d T ψT hψT u' ρ' hd' h0 ↔
                ∃ (i : u.1.A ≅ u'.1.A) (hi : i.hom ≫ u'.1.f = u.1.f), FakeEllipticCurve.WithFullLevel.IsoVia u u' i hi ∧
                  ∃ (ib : ρ.Eb.A ⟶ ρ'.Eb.A) (_ : ib ≫ ρ'.gb = ρ.gb ≫ i.hom) (_ : ib ≫ ρ'.Eb.f = ρ.Eb.f)
                    (uA : ρ'.Ab.A ⟶ ρ.Ab.A) (_ : FakeEllipticCurve.IsPullbackVia (RingHom.id _) ρ.Ab ρ'.Ab uA) (_ : uA ≫ ρ.gA = ρ'.gA),
                    ib ≫ ρ'.φ ≫ uA = ρ.φ))
    (hα : ∀ {T T' : Type} [CommRing T] [Algebra 𝒪 T] [CommRing T'] [Algebra 𝒪 T'] (f : T →ₐ[𝒪] T')
      {ψT : Onr →ₐ[𝒪] T} {E : FakeEllipticCurve Λ N T} {E' : FakeEllipticCurve Λ N T'} (g : E'.A ⟶ E.A)
      (hg : FakeEllipticCurve.IsPullbackVia (f : T →+* T') E E' g)
      (ρ : FakeEllipticCurve.Rigidification r π A₀ ψT E) (ρ' : FakeEllipticCurve.Rigidification r π A₀ (f.comp ψT) E'),
      FakeEllipticCurve.Rigidification.IsPullbackVia f g hg ρ ρ' →
      ∀ (hle : Ideal.span {algebraMap 𝒪 T π} ≤ (Ideal.span {algebraMap 𝒪 T' π}).comap (f : T →+* T'))
        (q' : ↥(Spec (CommRingCat.of (T' ⧸ Ideal.span {algebraMap 𝒪 T' π})))),
        val ρ' q' = val ρ ((Spec.map (CommRingCat.ofHom (Ideal.quotientMap (Ideal.span {algebraMap 𝒪 T' π}) (f : T →+* T') hle))).base q'))
    (hβ : ∀ {T : Type} [CommRing T] [Algebra 𝒪 T] {ψT : Onr →ₐ[𝒪] T}
      (u u' : FakeEllipticCurve.WithFullLevel Λ N n T)
      (ρ : FakeEllipticCurve.Rigidification r π A₀ ψT u.1) (ρ' : FakeEllipticCurve.Rigidification r π A₀ ψT u'.1)
      (i : u.1.A ≅ u'.1.A) (hi : i.hom ≫ u'.1.f = u.1.f), FakeEllipticCurve.WithFullLevel.IsoVia u u' i hi →
      ∀ (ib : ρ.Eb.A ⟶ ρ'.Eb.A) (_ : ib ≫ ρ'.gb = ρ.gb ≫ i.hom) (_ : ib ≫ ρ'.Eb.f = ρ.Eb.f)
        (uA : ρ'.Ab.A ⟶ ρ.Ab.A) (_ : FakeEllipticCurve.IsPullbackVia (RingHom.id _) ρ.Ab ρ'.Ab uA) (_ : uA ≫ ρ.gA = ρ'.gA),
        ib ≫ ρ'.φ ≫ uA = ρ.φ →
        ∀ q : ↥(Spec (CommRingCat.of (T ⧸ Ideal.span {algebraMap 𝒪 T π}))), val ρ q = val ρ' q)
    (d : ℕ) (x : ↥(Xs d)) (m m' : ℕ)
    (hm : DegAt π A₀ χC fM Xs ξ ptX val d x m) (hm' : DegAt π A₀ χC fM Xs ξ ptX val d x m') : m = m' := by
  classical

  let K₀ : Type := ↥((Xs d).residueField x)
  let t : Spec (CommRingCat.of K₀) ⟶ Xs d := (Xs d).fromSpecResidueField x
  let φ : CommRingCat.of C ⟶ CommRingCat.of K₀ := Spec.preimage (t ≫ strMap fM Xs ξ d)
  letI iC : Algebra C K₀ := φ.hom.toAlgebra
  letI i𝒪 : Algebra 𝒪 K₀ := (φ.hom.comp (algebraMap 𝒪 C)).toAlgebra
  haveI : IsScalarTower 𝒪 C K₀ := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  have hmap : Spec.map (CommRingCat.ofHom (algebraMap C K₀)) = t ≫ strMap fM Xs ξ d := by
    show Spec.map (CommRingCat.ofHom φ.hom) = _
    rw [CommRingCat.ofHom_hom, Spec.map_preimage]
  let xK : SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap C K₀))) (strMap fM Xs ξ d) := ⟨t, hmap.symm⟩
  have h0 : algebraMap C K₀ (algebraMap 𝒪 C π) = 0 := hs0 d K₀ xK
  obtain ⟨u₀, ρ₀, hd₀, hx₀⟩ := hx3 d K₀ ((IsScalarTower.toAlgHom 𝒪 C K₀).comp χC) rfl h0 xK
  have hπK : algebraMap 𝒪 K₀ π = 0 := h0
  haveI : Nontrivial (K₀ ⧸ Ideal.span {algebraMap 𝒪 K₀ π}) :=
    Ideal.Quotient.nontrivial_iff.mpr (by rw [Ne, hπK, Ideal.span_singleton_eq_top]; exact not_isUnit_zero)
  obtain ⟨q₀⟩ : Nonempty ↥(Spec (CommRingCat.of (K₀ ⧸ Ideal.span {algebraMap 𝒪 K₀ π}))) := inferInstance
  have hK₀ : ∀ I : Ideal K₀, I.IsPrime → I = ⊥ := fun I hI => @Ideal.eq_bot_of_prime _ _ I hI
  have hfac : ∀ (K : Type) [Field K] (f : Spec (CommRingCat.of K) ⟶ Xs d), f.base (IsLocalRing.closedPoint K) = x →
      ∃ e : CommRingCat.of K₀ ⟶ CommRingCat.of K, Spec.map e ≫ t = f :=
    fun K _ f hf => exists_specMap_comp_fromSpecResidueField_eq x K f hf
  have hpt₀ : (ptX d K₀ _ rfl u₀ ρ₀ hd₀ h0).1 = t := congrArg Subtype.val hx₀

  obtain ⟨T, iT, iA, iO, iS, u, ρ, hd, h0T, q, hq, rfl⟩ := hm
  obtain ⟨T', iT', iA', iO', iS', u', ρ', hd', h0T', q', hq', rfl⟩ := hm'
  have e1 := @val_eq_val_ref _ _ _ _ _ _ _ _ π _ _ _ A₀ _ _ _ χC _ fM Xs ξ ptX val hx2 hx4 hα hβ d x K₀ _ _ _ _ hK₀ t hmap hfac
    u₀ ρ₀ hd₀ h0 hpt₀ q₀ T iT iA iO iS u ρ hd h0T q hq
  have e2 := @val_eq_val_ref _ _ _ _ _ _ _ _ π _ _ _ A₀ _ _ _ χC _ fM Xs ξ ptX val hx2 hx4 hα hβ d x K₀ _ _ _ _ hK₀ t hmap hfac
    u₀ ρ₀ hd₀ h0 hpt₀ q₀ T' iT' iA' iO' iS' u' ρ' hd' h0T' q' hq'
  first | exact e1.trans e2.symm | (beta_reduce; rw [e1, e2])

end DegA
p2m_reactivate "P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_exists_opens_ratioWindow_degree_laws_of_rigidifiedToG_of_bdd.Ws16WC.Clopen P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_exists_opens_ratioWindow_degree_laws_of_rigidifiedToG_of_bdd.Ws16WC.DEGb.DegreeMaps P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_exists_opens_ratioWindow_degree_laws_of_rigidifiedToG_of_bdd.Ws16WC.DEGb P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_exists_opens_ratioWindow_degree_laws_of_rigidifiedToG_of_bdd.Ws16WC"
end ChartDict3
p2m_reactivate "P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_exists_opens_ratioWindow_degree_laws_of_rigidifiedToG_of_bdd.Ws16WC.Clopen P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_exists_opens_ratioWindow_degree_laws_of_rigidifiedToG_of_bdd.Ws16WC.DEGb.DegreeMaps P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_exists_opens_ratioWindow_degree_laws_of_rigidifiedToG_of_bdd.Ws16WC.DEGb P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_exists_opens_ratioWindow_degree_laws_of_rigidifiedToG_of_bdd.Ws16WC"

namespace ChartDict3

theorem rdeg_pullback
    {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} {N r : ℕ} [Fact r.Prime]
    (hΛℤ : ∀ m : ℤ, ((m : ℚ) : ℍ[ℚ, a, b]) ∈ Λ)
    {𝒪 : Type} [CommRing 𝒪] (π : 𝒪) {Onr : Type} [CommRing Onr] [Algebra 𝒪 Onr]
    (A₀ : FakeEllipticCurve Λ N (Onr ⧸ Ideal.span {algebraMap 𝒪 Onr π}))
    {T T' : Type} [CommRing T] [Algebra 𝒪 T] [CommRing T'] [Algebra 𝒪 T'] (f : T →ₐ[𝒪] T')
    {ψT : Onr →ₐ[𝒪] T} {E : FakeEllipticCurve Λ N T} {E' : FakeEllipticCurve Λ N T'} (g : E'.A ⟶ E.A)
    (hg : FakeEllipticCurve.IsPullbackVia (f : T →+* T') E E' g)
    (ρ : FakeEllipticCurve.Rigidification r π A₀ ψT E) (ρ' : FakeEllipticCurve.Rigidification r π A₀ (f.comp ψT) E')
    (h : FakeEllipticCurve.Rigidification.IsPullbackVia f g hg ρ ρ')
    (hle : Ideal.span {algebraMap 𝒪 T π} ≤ (Ideal.span {algebraMap 𝒪 T' π}).comap (f : T →+* T'))
    (q' : ↥(Spec (CommRingCat.of (T' ⧸ Ideal.span {algebraMap 𝒪 T' π})))) :
    rdeg π A₀ ρ' q' = rdeg π A₀ ρ ((Spec.map (CommRingCat.ofHom (Ideal.quotientMap (Ideal.span {algebraMap 𝒪 T' π}) (f : T →+* T') hle))).base q') := by
  obtain ⟨ub, uA, hEb, hub, hAb, huA, hd, hcomm⟩ := h
  obtain ⟨h1, h2, -, -⟩ := FakeEllipticCurve.isFinite_flat_surjective_of_isIsogenyPair hΛℤ r ρ.d _ ρ.Eb ρ.Ab ρ.φ ρ.φ' ρ.isIsogenyPair
  exact DEG44.finrank_one_eq_of_isPullbackVia _ ρ.Eb ρ'.Eb ub hEb ρ.Ab ρ'.Ab uA hAb ρ.φ ρ.φ_over ρ'.φ ρ'.φ_over hcomm q'

theorem rdeg_eq_of_corr
    {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} {N n r : ℕ} [Fact r.Prime]
    (hΛℤ : ∀ m : ℤ, ((m : ℚ) : ℍ[ℚ, a, b]) ∈ Λ)
    {𝒪 : Type} [CommRing 𝒪] (π : 𝒪) {Onr : Type} [CommRing Onr] [Algebra 𝒪 Onr]
    (A₀ : FakeEllipticCurve Λ N (Onr ⧸ Ideal.span {algebraMap 𝒪 Onr π}))
    {T : Type} [CommRing T] [Algebra 𝒪 T] {ψT : Onr →ₐ[𝒪] T}
    (u u' : FakeEllipticCurve.WithFullLevel Λ N n T)
    (ρ : FakeEllipticCurve.Rigidification r π A₀ ψT u.1) (ρ' : FakeEllipticCurve.Rigidification r π A₀ ψT u'.1)
    (i : u.1.A ≅ u'.1.A) (hi : i.hom ≫ u'.1.f = u.1.f) (hI : FakeEllipticCurve.WithFullLevel.IsoVia u u' i hi)
    (ib : ρ.Eb.A ⟶ ρ'.Eb.A) (hib : ib ≫ ρ'.gb = ρ.gb ≫ i.hom) (hibf : ib ≫ ρ'.Eb.f = ρ.Eb.f)
    (uA : ρ'.Ab.A ⟶ ρ.Ab.A) (huA : FakeEllipticCurve.IsPullbackVia (RingHom.id _) ρ.Ab ρ'.Ab uA) (huAg : uA ≫ ρ.gA = ρ'.gA)
    (hrel : ib ≫ ρ'.φ ≫ uA = ρ.φ)
    (q : ↥(Spec (CommRingCat.of (T ⧸ Ideal.span {algebraMap 𝒪 T π})))) :
    rdeg π A₀ ρ q = rdeg π A₀ ρ' q := by
  have hrel0 : ib ≫ ρ'.φ ≫ uA ≫ ρ.Ab.act ⟨(((r ^ 0 : ℕ) : ℤ) : ℚ), hΛℤ _⟩ = ρ.φ ≫ ρ.Ab.act ⟨(((r ^ 0 : ℕ) : ℤ) : ℚ), hΛℤ _⟩ := by
    rw [← hrel]; simp only [Category.assoc]
  let y' : ↥ρ'.Ab.A := (ρ'.Ab.L.one (𝟙 (Spec (CommRingCat.of (T ⧸ Ideal.span {algebraMap 𝒪 T π}))))).1.base q
  have key := CerednikDrinfeld.QM.FakeEllipticCurve.Rigidification.finrank_mul_finrank_act_pow_eq_of_corr 𝒪 π Onr Λ hΛℤ A₀
    T ψT u.1 u'.1 ρ ρ' i hi ib hib hibf uA huA huAg 0 0 hrel0 y'
  simp only [pow_zero, mul_one] at key

  have hone := DEG44.one_comp_eq_specMap_comp_one (RingHom.id _) ρ.Ab ρ'.Ab uA huA
  have hy : uA.base y' = (ρ.Ab.L.one (𝟙 (Spec (CommRingCat.of (T ⧸ Ideal.span {algebraMap 𝒪 T π}))))).1.base q := by
    show ((ρ'.Ab.L.one (𝟙 _)).1 ≫ uA).base q = _
    rw [hone, CommRingCat.ofHom_id, Spec.map_id, Category.id_comp]
  unfold rdeg
  rw [← hy]
  exact key.symm

end ChartDict3
p2m_reactivate "P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_exists_opens_ratioWindow_degree_laws_of_rigidifiedToG_of_bdd.Ws16WC.Clopen P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_exists_opens_ratioWindow_degree_laws_of_rigidifiedToG_of_bdd.Ws16WC.DEGb.DegreeMaps P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_exists_opens_ratioWindow_degree_laws_of_rigidifiedToG_of_bdd.Ws16WC.DEGb P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_exists_opens_ratioWindow_degree_laws_of_rigidifiedToG_of_bdd.Ws16WC"

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

    (μΛ : ↥Λ) (hμΛ : (μΛ : ℍ[ℚ, a, b]) * (μΛ : ℍ[ℚ, a, b]) = -(((r * rbar : ℕ) : ℚ) • (1 : ℍ[ℚ, a, b])))
    (starΛ : ↥Λ → ↥Λ) (hstarΛ : ∀ x : ↥Λ, (μΛ : ℍ[ℚ, a, b]) * (starΛ x : ℍ[ℚ, a, b]) = Star.star (x : ℍ[ℚ, a, b]) * μΛ)
    (h2 : IsUnit ((2 : ℕ) : 𝒪))
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

      (hbdd : ∀ (M' M : FullLattice 𝒪 K₀), M'.1 ≤ M.1 → (∀ v ∈ M.1, algebraMap 𝒪 K₀ π • v ∈ M'.1) →
        ∃ Nγ : ℕ, ∀ (B : Type) [CommRing B] [IsNoetherianRing B] [IsLocalRing B] [IsArtinianRing B]
          [IsAlgClosed (IsLocalRing.ResidueField B)] [Algebra 𝒪 B]
          (hB : IsNilpotent (algebraMap 𝒪 B π)) (y : (ModuliPackage.G 𝒪 MD).obj B),
          DeligneDatum.InEdgeChart π (eD B hB y).2 M' M →
            ∃ t : Rigidified r Φ B, t.IsAdmissible ι (y.ψ : Onr →+* B) ∧ η B (y.ψ : Onr →+* B) y.nilp t = y.pt ∧ t.n ≤ Nγ)

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

    (C : Type) [CommRing C] [IsNoetherianRing C] [Algebra 𝒪 C] (hCπ : IsNilpotent (algebraMap 𝒪 C π)) (χC : Onr →ₐ[𝒪] C)
    (PR : CerednikDrinfeld.FormalOmega.AlgFunctor C)
    (ptR : ∀ (S : Type) [CommRing S] [Algebra C S] [Algebra 𝒪 S] [IsScalarTower 𝒪 C S]
        (ψS : Onr →ₐ[𝒪] S) (_ : ψS = (IsScalarTower.toAlgHom 𝒪 C S).comp χC)
        (u : FakeEllipticCurve.WithFullLevel Λ N n S), FakeEllipticCurve.Rigidification r π A₀ ψS u.1 →
          PR.obj S)

    (hR2 : (∀ (S S' : Type) [CommRing S] [Algebra C S] [Algebra 𝒪 S] [IsScalarTower 𝒪 C S]
          [CommRing S'] [Algebra C S'] [Algebra 𝒪 S'] [IsScalarTower 𝒪 C S'] (φ : S →ₐ[C] S')
          (ψS : Onr →ₐ[𝒪] S) (hψS : ψS = (IsScalarTower.toAlgHom 𝒪 C S).comp χC)
          (hψS' : (φ.restrictScalars 𝒪).comp ψS = (IsScalarTower.toAlgHom 𝒪 C S').comp χC)
          (u : FakeEllipticCurve.WithFullLevel Λ N n S) (u' : FakeEllipticCurve.WithFullLevel Λ N n S')
          (ρ : FakeEllipticCurve.Rigidification r π A₀ ψS u.1)
          (ρ' : FakeEllipticCurve.Rigidification r π A₀ ((φ.restrictScalars 𝒪).comp ψS) u'.1)
          (g : u'.1.A ⟶ u.1.A) (hg : FakeEllipticCurve.IsPullbackVia (φ : S →+* S') u.1 u'.1 g),
          (u'.2.P).1 ≫ g = Spec.map (CommRingCat.ofHom (φ : S →+* S')) ≫ (u.2.P).1 →
          FakeEllipticCurve.Rigidification.IsPullbackVia (φ.restrictScalars 𝒪) g hg ρ ρ' →
            PR.map φ (ptR S ψS hψS u ρ) = ptR S' ((φ.restrictScalars 𝒪).comp ψS) hψS' u' ρ'))

    (hR3s : (∀ (S : Type) [CommRing S] [Algebra C S] [Algebra 𝒪 S] [IsScalarTower 𝒪 C S]
          (ψS : Onr →ₐ[𝒪] S) (hψS : ψS = (IsScalarTower.toAlgHom 𝒪 C S).comp χC)
          (z : PR.obj S),
          ∃ (u : FakeEllipticCurve.WithFullLevel Λ N n S) (ρ : FakeEllipticCurve.Rigidification r π A₀ ψS u.1), ptR S ψS hψS u ρ = z))
    (hR3i : (∀ (S : Type) [CommRing S] [Algebra C S] [Algebra 𝒪 S] [IsScalarTower 𝒪 C S]
          (ψS : Onr →ₐ[𝒪] S) (hψS : ψS = (IsScalarTower.toAlgHom 𝒪 C S).comp χC)
          (hSc : ∀ e : S, IsIdempotentElem e → e = 0 ∨ e = 1)
          (u u' : FakeEllipticCurve.WithFullLevel Λ N n S)
          (ρ : FakeEllipticCurve.Rigidification r π A₀ ψS u.1) (ρ' : FakeEllipticCurve.Rigidification r π A₀ ψS u'.1),
          ptR S ψS hψS u ρ = ptR S ψS hψS u' ρ' →
            ∃ (i : u.1.A ≅ u'.1.A) (hi : i.hom ≫ u'.1.f = u.1.f), FakeEllipticCurve.WithFullLevel.IsoVia u u' i hi ∧
              ∃ (ib : ρ.Eb.A ⟶ ρ'.Eb.A) (_ : ib ≫ ρ'.gb = ρ.gb ≫ i.hom) (_ : ib ≫ ρ'.Eb.f = ρ.Eb.f)
              (uA : ρ'.Ab.A ⟶ ρ.Ab.A) (_ : FakeEllipticCurve.IsPullbackVia (RingHom.id _) ρ.Ab ρ'.Ab uA) (_ : uA ≫ ρ.gA = ρ'.gA)
              (i₁ j₁ : ℕ),
              ib ≫ ρ'.φ ≫ uA ≫ ρ.Ab.act ⟨(((r ^ i₁ : ℕ) : ℤ) : ℚ), hΛℤ _⟩ = ρ.φ ≫ ρ.Ab.act ⟨(((r ^ j₁ : ℕ) : ℤ) : ℚ), hΛℤ _⟩))

    (hR1 : (∀ (S : Type) [CommRing S] [Algebra C S] [Algebra 𝒪 S] [IsScalarTower 𝒪 C S]
          (ψS : Onr →ₐ[𝒪] S) (hψS : ψS = (IsScalarTower.toAlgHom 𝒪 C S).comp χC)
          (u u' : FakeEllipticCurve.WithFullLevel Λ N n S)
          (ρ : FakeEllipticCurve.Rigidification r π A₀ ψS u.1) (ρ' : FakeEllipticCurve.Rigidification r π A₀ ψS u'.1)
          (i : u.1.A ≅ u'.1.A) (hi : i.hom ≫ u'.1.f = u.1.f),
          FakeEllipticCurve.WithFullLevel.IsoVia u u' i hi →
          (∃ (ib : ρ.Eb.A ⟶ ρ'.Eb.A) (_ : ib ≫ ρ'.gb = ρ.gb ≫ i.hom) (_ : ib ≫ ρ'.Eb.f = ρ.Eb.f)
              (uA : ρ'.Ab.A ⟶ ρ.Ab.A) (_ : FakeEllipticCurve.IsPullbackVia (RingHom.id _) ρ.Ab ρ'.Ab uA) (_ : uA ≫ ρ.gA = ρ'.gA)
              (i₁ j₁ : ℕ),
              ib ≫ ρ'.φ ≫ uA ≫ ρ.Ab.act ⟨(((r ^ i₁ : ℕ) : ℤ) : ℚ), hΛℤ _⟩ = ρ.φ ≫ ρ.Ab.act ⟨(((r ^ j₁ : ℕ) : ℤ) : ℚ), hΛℤ _⟩) →
            ptR S ψS hψS u ρ = ptR S ψS hψS u' ρ'))

    (θ : (∀ (S : Type) [CommRing S] [Algebra C S] [IsNoetherianRing S] [Algebra 𝒪 S] [IsScalarTower 𝒪 C S],
        PR.obj S → (Omega K₀ π).obj S))
    (hθnat : (∀ (S S' : Type) [CommRing S] [Algebra C S] [IsNoetherianRing S] [Algebra 𝒪 S] [IsScalarTower 𝒪 C S]
          [CommRing S'] [Algebra C S'] [IsNoetherianRing S'] [Algebra 𝒪 S'] [IsScalarTower 𝒪 C S']
          (g : S →ₐ[C] S') (x : PR.obj S),
          θ S' (PR.map g x) = (Omega K₀ π).map (g.restrictScalars 𝒪) (θ S x)))
    (hθ : (∀ (S : Type) [CommRing S] [Algebra C S] [IsNoetherianRing S] [Algebra 𝒪 S] [IsScalarTower 𝒪 C S]
          (hS : IsNilpotent (algebraMap 𝒪 S π))
          (ψS : Onr →ₐ[𝒪] S) (hψS : ψS = (IsScalarTower.toAlgHom 𝒪 C S).comp χC)
          (u : FakeEllipticCurve.WithFullLevel Λ N n S) (ρ : FakeEllipticCurve.Rigidification r π A₀ ψS u.1),
          θ S (ptR S ψS hψS u ρ) = DeligneDatum.pullback π S (g₀⁻¹)⁻¹ (eD S hS (Ξ S ψS hS ⟨u.1, ρ⟩)).2))

    (toM : ∀ (S : Type) [CommRing S] [Algebra C S],
        PR.obj S → SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap C S))) (Limits.pullback.snd fM (Spec.map (CommRingCat.ofHom (algebraMap 𝒪 C)))))

(hR0 : ∀ (S S' : Type) [CommRing S] [Algebra C S] [CommRing S'] [Algebra C S'] (φ : S →ₐ[C] S') (x : PR.obj S),
        (toM S' (PR.map φ x)).1 = Spec.map (CommRingCat.ofHom (φ : S →+* S')) ≫ (toM S x).1)

(hR4 : ∀ (S : Type) [CommRing S] [Algebra C S] [Algebra 𝒪 S] [IsScalarTower 𝒪 C S]
        (ψS : Onr →ₐ[𝒪] S) (hψS : ψS = (IsScalarTower.toAlgHom 𝒪 C S).comp χC)
        (u : FakeEllipticCurve.WithFullLevel Λ N n S) (ρ : FakeEllipticCurve.Rigidification r π A₀ ψS u.1),
        (toM S (ptR S ψS hψS u ρ)).1 ≫ Limits.pullback.fst fM (Spec.map (CommRingCat.ofHom (algebraMap 𝒪 C))) =
          (ptF S (Spec.map (CommRingCat.ofHom (algebraMap 𝒪 S))) u).1)

(hsh : ∀ (A : Type) [CommRing A] [Algebra C A] (n : ℕ) (f : Fin n → A),
      Ideal.span (Set.range f) = ⊤ →
      ∀ (B : Fin n → Type) [∀ i, CommRing (B i)] [∀ i, Algebra A (B i)] [∀ i, Algebra C (B i)]
        [∀ i, IsScalarTower C A (B i)] [∀ i, IsLocalization.Away (f i) (B i)] (s : ∀ i, PR.obj (B i)),
      (∀ (i j : Fin n) (D : Type) [CommRing D] [Algebra A D] [Algebra C D] [IsScalarTower C A D]
          [IsLocalization.Away (f i * f j) D] (ρ₁ : B i →ₐ[A] D) (ρ₂ : B j →ₐ[A] D),
          PR.map (ρ₁.restrictScalars C) (s i) = PR.map (ρ₂.restrictScalars C) (s j)) →
      ∃! s₀ : PR.obj A, ∀ i, PR.map (IsScalarTower.toAlgHom C A (B i)) s₀ = s i)

(het' : ∀ (S S₀ : Type) [CommRing S] [IsNoetherianRing S] [Algebra C S] [CommRing S₀] [Algebra C S₀] (p : S →ₐ[C] S₀),
        Function.Surjective p → RingHom.ker (p : S →+* S₀) ^ 2 = ⊥ →
        ∀ (x₀ : PR.obj S₀) (t : SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap C S))) (Limits.pullback.snd fM (Spec.map (CommRingCat.ofHom (algebraMap 𝒪 C))))),
        Spec.map (CommRingCat.ofHom (p : S →+* S₀)) ≫ t.1 = (toM S₀ x₀).1 →
        ∃! x : PR.obj S, PR.map p x = x₀ ∧ toM S x = t)

(hred : ∀ (T : Type) [CommRing T] [IsNoetherianRing T] [Algebra C T]
        (xb : PR.obj (T ⧸ Ideal.span {algebraMap C T (algebraMap 𝒪 C π)}))
        (t : SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap C T))) (Limits.pullback.snd fM (Spec.map (CommRingCat.ofHom (algebraMap 𝒪 C))))),
        Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (Ideal.span {algebraMap C T (algebraMap 𝒪 C π)}))) ≫ t.1 =
          (toM _ xb).1 →
        ∃! x : PR.obj T,
          PR.map (Ideal.Quotient.mkₐ C (Ideal.span {algebraMap C T (algebraMap 𝒪 C π)})) x = xb ∧ toM T x = t)
    (Xs : ℕ → Scheme.{0}) (ξ : ∀ d, Xs d ⟶ Limits.pullback fM (Spec.map (CommRingCat.ofHom (algebraMap 𝒪 C))))
    (hξ : ∀ d, LocallyOfFinitePresentation (ξ d)) (hunrξ : ∀ d, FormallyUnramified (ξ d))
    (pts : ∀ (d : ℕ) (T : Type) [CommRing T] [Algebra C T],
          SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap C T))) (ξ d ≫ Limits.pullback.snd fM (Spec.map (CommRingCat.ofHom (algebraMap 𝒪 C)))) → PR.obj T)
    (ptX : ∀ (d : ℕ) (T : Type) [CommRing T] [Algebra C T] [Algebra 𝒪 T] [IsScalarTower 𝒪 C T]
            (ψT : Onr →ₐ[𝒪] T) (_ : ψT = (IsScalarTower.toAlgHom 𝒪 C T).comp χC)
            (u : FakeEllipticCurve.WithFullLevel Λ N n T) (ρ : FakeEllipticCurve.Rigidification r π A₀ ψT u.1),
            ρ.d = d → algebraMap C T (algebraMap 𝒪 C π) = 0 → SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap C T))) (ξ d ≫ Limits.pullback.snd fM (Spec.map (CommRingCat.ofHom (algebraMap 𝒪 C)))))

(hs0 : ∀ (d : ℕ) (T : Type) [CommRing T] [Algebra C T]
            (x : SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap C T))) (ξ d ≫ Limits.pullback.snd fM (Spec.map (CommRingCat.ofHom (algebraMap 𝒪 C))))),
            algebraMap C T (algebraMap 𝒪 C π) = 0)

(hs1 : ∀ (d : ℕ) (T : Type) [CommRing T] [Algebra C T]
            (x : SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap C T))) (ξ d ≫ Limits.pullback.snd fM (Spec.map (CommRingCat.ofHom (algebraMap 𝒪 C))))),
            (toM T (pts d T x)).1 = x.1 ≫ ξ d)

(hs2 : ∀ (d : ℕ) (T T' : Type) [CommRing T] [Algebra C T] [CommRing T'] [Algebra C T'] (φ : T →ₐ[C] T')
            (x : SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap C T))) (ξ d ≫ Limits.pullback.snd fM (Spec.map (CommRingCat.ofHom (algebraMap 𝒪 C)))))
            (x' : SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap C T'))) (ξ d ≫ Limits.pullback.snd fM (Spec.map (CommRingCat.ofHom (algebraMap 𝒪 C))))),
            x'.1 = Spec.map (CommRingCat.ofHom (φ : T →+* T')) ≫ x.1 → pts d T' x' = PR.map φ (pts d T x))

(hx1 : ∀ (d : ℕ) (T : Type) [CommRing T] [Algebra C T] [Algebra 𝒪 T] [IsScalarTower 𝒪 C T]
              (ψT : Onr →ₐ[𝒪] T) (hψT : ψT = (IsScalarTower.toAlgHom 𝒪 C T).comp χC)
              (u : FakeEllipticCurve.WithFullLevel Λ N n T) (ρ : FakeEllipticCurve.Rigidification r π A₀ ψT u.1)
              (hd : ρ.d = d) (h0 : algebraMap C T (algebraMap 𝒪 C π) = 0),
              pts d T (ptX d T ψT hψT u ρ hd h0) = ptR T ψT hψT u ρ)

(hx2 : ∀ (d : ℕ) (T T' : Type) [CommRing T] [Algebra C T] [Algebra 𝒪 T] [IsScalarTower 𝒪 C T]
              [CommRing T'] [Algebra C T'] [Algebra 𝒪 T'] [IsScalarTower 𝒪 C T'] (φ : T →ₐ[C] T')
              (ψT : Onr →ₐ[𝒪] T) (hψT : ψT = (IsScalarTower.toAlgHom 𝒪 C T).comp χC)
              (hψT' : (φ.restrictScalars 𝒪).comp ψT = (IsScalarTower.toAlgHom 𝒪 C T').comp χC)
              (u : FakeEllipticCurve.WithFullLevel Λ N n T) (u' : FakeEllipticCurve.WithFullLevel Λ N n T')
              (ρ : FakeEllipticCurve.Rigidification r π A₀ ψT u.1)
              (ρ' : FakeEllipticCurve.Rigidification r π A₀ ((φ.restrictScalars 𝒪).comp ψT) u'.1)
              (g : u'.1.A ⟶ u.1.A) (hg : FakeEllipticCurve.IsPullbackVia (φ : T →+* T') u.1 u'.1 g)
              (hd : ρ.d = d) (hd' : ρ'.d = d) (h0 : algebraMap C T (algebraMap 𝒪 C π) = 0) (h0' : algebraMap C T' (algebraMap 𝒪 C π) = 0),
              (u'.2.P).1 ≫ g = Spec.map (CommRingCat.ofHom (φ : T →+* T')) ≫ (u.2.P).1 →
              FakeEllipticCurve.Rigidification.IsPullbackVia (φ.restrictScalars 𝒪) g hg ρ ρ' →
                (ptX d T' ((φ.restrictScalars 𝒪).comp ψT) hψT' u' ρ' hd' h0').1 =
                  Spec.map (CommRingCat.ofHom (φ : T →+* T')) ≫ (ptX d T ψT hψT u ρ hd h0).1)

(hx3 : ∀ (d : ℕ) (T : Type) [CommRing T] [Algebra C T] [Algebra 𝒪 T] [IsScalarTower 𝒪 C T]
              (ψT : Onr →ₐ[𝒪] T) (hψT : ψT = (IsScalarTower.toAlgHom 𝒪 C T).comp χC)
              (h0 : algebraMap C T (algebraMap 𝒪 C π) = 0) (x : SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap C T))) (ξ d ≫ Limits.pullback.snd fM (Spec.map (CommRingCat.ofHom (algebraMap 𝒪 C))))),
              ∃ (u : FakeEllipticCurve.WithFullLevel Λ N n T) (ρ : FakeEllipticCurve.Rigidification r π A₀ ψT u.1) (hd : ρ.d = d),
                ptX d T ψT hψT u ρ hd h0 = x)

(hx4 : ∀ (d : ℕ) (T : Type) [CommRing T] [Algebra C T] [Algebra 𝒪 T] [IsScalarTower 𝒪 C T]
              (ψT : Onr →ₐ[𝒪] T) (hψT : ψT = (IsScalarTower.toAlgHom 𝒪 C T).comp χC)
              (h0 : algebraMap C T (algebraMap 𝒪 C π) = 0)
              (u u' : FakeEllipticCurve.WithFullLevel Λ N n T)
              (ρ : FakeEllipticCurve.Rigidification r π A₀ ψT u.1) (ρ' : FakeEllipticCurve.Rigidification r π A₀ ψT u'.1)
              (hd : ρ.d = d) (hd' : ρ'.d = d),
              (ptX d T ψT hψT u ρ hd h0 = ptX d T ψT hψT u' ρ' hd' h0 ↔
                ∃ (i : u.1.A ≅ u'.1.A) (hi : i.hom ≫ u'.1.f = u.1.f), FakeEllipticCurve.WithFullLevel.IsoVia u u' i hi ∧
                  ∃ (ib : ρ.Eb.A ⟶ ρ'.Eb.A) (_ : ib ≫ ρ'.gb = ρ.gb ≫ i.hom) (_ : ib ≫ ρ'.Eb.f = ρ.Eb.f)
                    (uA : ρ'.Ab.A ⟶ ρ.Ab.A) (_ : FakeEllipticCurve.IsPullbackVia (RingHom.id _) ρ.Ab ρ'.Ab uA) (_ : uA ≫ ρ.gA = ρ'.gA),
                    ib ≫ ρ'.φ ≫ uA = ρ.φ))

(hs4 : ∀ (d : ℕ) (T : Type) [CommRing T] [Algebra C T] [Algebra 𝒪 T] [IsScalarTower 𝒪 C T]
            (ψT : Onr →ₐ[𝒪] T) (hψT : ψT = (IsScalarTower.toAlgHom 𝒪 C T).comp χC)
            (u : FakeEllipticCurve.WithFullLevel Λ N n T) (ρ : FakeEllipticCurve.Rigidification r π A₀ ψT u.1),
            algebraMap C T (algebraMap 𝒪 C π) = 0 →
            ((∃ x, pts d T x = ptR T ψT hψT u ρ) ↔
              ∃ (ρ' : FakeEllipticCurve.Rigidification r π A₀ ψT u.1), ρ'.d = d ∧ ptR T ψT hψT u ρ' = ptR T ψT hψT u ρ))

    (gπ : Matrix.GeneralLinearGroup (Fin 2) K₀) (hgπ : (gπ : Matrix (Fin 2) (Fin 2) K₀) = Matrix.diagonal ![algebraMap 𝒪 K₀ π, 1])
    (D : ℕ) :
    ∃ (B : (Xs D).Opens) (c : ℕ) (_ : 2 ≤ c),
      ∀ (T : Type) [CommRing T] [Algebra C T] [IsNoetherianRing T] [Algebra 𝒪 T] [IsScalarTower 𝒪 C T] [Nontrivial T]
        (_ : ∀ e : T, IsIdempotentElem e → e = 0 ∨ e = 1) (h0 : algebraMap C T (algebraMap 𝒪 C π) = 0),
        ∃ (degφ : ∀ {E A : FakeEllipticCurve Λ N (T ⧸ Ideal.span {algebraMap 𝒪 T π})}, (E.A ⟶ A.A) → ℕ),

          (∀ {E : FakeEllipticCurve Λ N T} (ρ : FakeEllipticCurve.Rigidification r π A₀ ((IsScalarTower.toAlgHom 𝒪 C T).comp χC) E),
              0 < degφ ρ.φ ∧ 0 < degφ ρ.φ') ∧

          (∀ {E : FakeEllipticCurve Λ N T} (ρ : FakeEllipticCurve.Rigidification r π A₀ ((IsScalarTower.toAlgHom 𝒪 C T).comp χC) E),
              degφ ρ.φ * degφ ρ.φ' = c ^ ρ.d) ∧

          (∀ {E : FakeEllipticCurve Λ N T} (ρ : FakeEllipticCurve.Rigidification r π A₀ ((IsScalarTower.toAlgHom 𝒪 C T).comp χC) E) (i : ℕ),
              degφ (ρ.φ ≫ ρ.Ab.act ⟨(((r ^ i : ℕ) : ℤ) : ℚ), hΛℤ _⟩) = c ^ i * degφ ρ.φ ∧
              degφ (ρ.Ab.act ⟨(((r ^ i : ℕ) : ℤ) : ℚ), hΛℤ _⟩ ≫ ρ.φ') = c ^ i * degφ ρ.φ') ∧

          (∀ (u u' : FakeEllipticCurve.WithFullLevel Λ N n T)
            (ρ : FakeEllipticCurve.Rigidification r π A₀ ((IsScalarTower.toAlgHom 𝒪 C T).comp χC) u.1)
            (ρ' : FakeEllipticCurve.Rigidification r π A₀ ((IsScalarTower.toAlgHom 𝒪 C T).comp χC) u'.1)
            (i : u.1.A ≅ u'.1.A) (hi : i.hom ≫ u'.1.f = u.1.f) (hI : FakeEllipticCurve.WithFullLevel.IsoVia u u' i hi)
            (ib : ρ.Eb.A ⟶ ρ'.Eb.A) (_ : ib ≫ ρ'.gb = ρ.gb ≫ i.hom) (_ : ib ≫ ρ'.Eb.f = ρ.Eb.f)
            (uA : ρ'.Ab.A ⟶ ρ.Ab.A) (_ : FakeEllipticCurve.IsPullbackVia (RingHom.id _) ρ.Ab ρ'.Ab uA) (_ : uA ≫ ρ.gA = ρ'.gA)
            (i₁ j₁ : ℕ),
            ib ≫ ρ'.φ ≫ uA ≫ ρ.Ab.act ⟨(((r ^ i₁ : ℕ) : ℤ) : ℚ), hΛℤ _⟩ = ρ.φ ≫ ρ.Ab.act ⟨(((r ^ j₁ : ℕ) : ℤ) : ℚ), hΛℤ _⟩ →
              degφ ρ'.φ * c ^ i₁ = degφ ρ.φ * c ^ j₁) ∧

          (∀ (u u' : FakeEllipticCurve.WithFullLevel Λ N n T)
            (ρ : FakeEllipticCurve.Rigidification r π A₀ ((IsScalarTower.toAlgHom 𝒪 C T).comp χC) u.1)
            (ρ' : FakeEllipticCurve.Rigidification r π A₀ ((IsScalarTower.toAlgHom 𝒪 C T).comp χC) u'.1)
            (i : u.1.A ≅ u'.1.A) (hi : i.hom ≫ u'.1.f = u.1.f) (hI : FakeEllipticCurve.WithFullLevel.IsoVia u u' i hi)
            (ib : ρ.Eb.A ⟶ ρ'.Eb.A) (_ : ib ≫ ρ'.gb = ρ.gb ≫ i.hom) (_ : ib ≫ ρ'.Eb.f = ρ.Eb.f)
            (uA : ρ'.Ab.A ⟶ ρ.Ab.A) (_ : FakeEllipticCurve.IsPullbackVia (RingHom.id _) ρ.Ab ρ'.Ab uA) (_ : uA ≫ ρ.gA = ρ'.gA)
            (i₁ : ℕ),
            ib ≫ ρ'.φ ≫ uA ≫ ρ.Ab.act ⟨(((r ^ i₁ : ℕ) : ℤ) : ℚ), hΛℤ _⟩ = ρ.φ ≫ ρ.Ab.act ⟨(((r ^ i₁ : ℕ) : ℤ) : ℚ), hΛℤ _⟩ →
              ib ≫ ρ'.φ ≫ uA = ρ.φ) ∧

          (∀ (u : FakeEllipticCurve.WithFullLevel Λ N n T)
            (ρ : FakeEllipticCurve.Rigidification r π A₀ ((IsScalarTower.toAlgHom 𝒪 C T).comp χC) u.1) (hd : ρ.d = D),
            (∀ p : ↥(Spec (CommRingCat.of T)), (ptX D T ((IsScalarTower.toAlgHom 𝒪 C T).comp χC) rfl u ρ hd h0).1 p ∈ B) ↔
              (degφ ρ.φ ≤ degφ ρ.φ' ∧ degφ ρ.φ' < c ^ 2 * degφ ρ.φ)) := by
  classical

  have hc2 : 2 ≤ DEG.cdeg (r := r) hΛℤ A₀ := DEG.one_lt_cdeg hΛℤ A₀

  have huniq : ChartDict3.U1Statement π A₀ χC fM Xs ξ ptX (ChartDict3.rdeg π A₀) := by
    intro d x m m' hm hm'
    refine ChartDict3.degAt_unique π A₀ χC fM Xs ξ ptX (ChartDict3.rdeg π A₀) hs0 hx2 hx3 hx4 ?_ ?_ d x m m' hm hm'
    · intro T T' _ _ _ _ f ψT E E' g hg ρ ρ' h hle q'
      exact ChartDict3.rdeg_pullback hΛℤ π A₀ f g hg ρ ρ' h hle q'
    · intro T _ _ ψT u u' ρ ρ' i hi hI ib hib hibf uA huA huAg hrel q
      exact ChartDict3.rdeg_eq_of_corr hΛℤ π A₀ u u' ρ ρ' i hi hI ib hib hibf uA huA huAg hrel q

  have hval : ∀ (T : Type) [CommRing T] [Algebra 𝒪 T] (ψT : Onr →ₐ[𝒪] T) (E : FakeEllipticCurve Λ N T)
      (ρ : FakeEllipticCurve.Rigidification r π A₀ ψT E), IsLocallyConstant (ChartDict3.rdeg π A₀ ρ) := by
    intro T _ _ ψT E ρ
    exact Ws16WC.FEC.isLocallyConstant_degOnBase' _ ρ.Eb ρ.Ab ρ.φ
      (FakeEllipticCurve.isFinite_flat_surjective_of_isIsogenyPair hΛℤ r ρ.d _ ρ.Eb ρ.Ab ρ.φ ρ.φ' ρ.isIsogenyPair)

  let δ : Ws16WC.DEGb.DegreeMaps (Xs D) :=
    { f := ChartDict3.degF π A₀ χC fM Xs ξ ptX (ChartDict3.rdeg π A₀) D
      g := fun x => DEG.cdeg (r := r) hΛℤ A₀ ^ D / ChartDict3.degF π A₀ χC fM Xs ξ ptX (ChartDict3.rdeg π A₀) D x
      c := fun _ => DEG.cdeg (r := r) hΛℤ A₀
      hf := ChartDict3.isLocallyConstant_degF π A₀ χC fM Xs ξ ptX _ huniq hs0 hx3 hval D
      hg := (ChartDict3.isLocallyConstant_degF π A₀ χC fM Xs ξ ptX _ huniq hs0 hx3 hval D).comp
        (fun m => DEG.cdeg (r := r) hΛℤ A₀ ^ D / m)
      hc := IsLocallyConstant.const _ }
  refine ⟨Ws16WC.DEGb.B δ, DEG.cdeg (r := r) hΛℤ A₀, hc2, ?_⟩
  intro T _ _ _ _ _ _ hTc h0
  have hπT : algebraMap 𝒪 T π = 0 := by rw [IsScalarTower.algebraMap_apply 𝒪 C T]; exact h0
  haveI hpre : PreconnectedSpace ↥(Spec (CommRingCat.of (T ⧸ Ideal.span {algebraMap 𝒪 T π}))) :=
    Ws2DegC.preconnectedSpace_spec_quot hTc hπT
  let q₀ : ↥(Spec (CommRingCat.of (T ⧸ Ideal.span {algebraMap 𝒪 T π}))) := Ws2DegC.basePt hπT

  have hcr : ∀ {E : FakeEllipticCurve Λ N T} (ρ : FakeEllipticCurve.Rigidification r π A₀ ((IsScalarTower.toAlgHom 𝒪 C T).comp χC) E) (y : ↥ρ.Ab.A),
      (ρ.Ab.act ⟨(((r : ℕ) : ℤ) : ℚ), hΛℤ _⟩).finrank y = DEG.cdeg (r := r) hΛℤ A₀ := by
    intro E ρ y
    have h1 := DEG.finrank_act_Ab_eq_cdeg hΛℤ hOnr_max A₀ T ((IsScalarTower.toAlgHom 𝒪 C T).comp χC) E ρ y
    have he : (⟨(((r ^ 1 : ℕ) : ℤ) : ℚ), hΛℤ _⟩ : ↥Λ) = ⟨(((r : ℕ) : ℤ) : ℚ), hΛℤ _⟩ := Subtype.ext (by simp)
    rw [he] at h1; exact h1
  obtain ⟨hpos, hprod, hpad⟩ := Ws2DegC.degc_face hΛℤ hTc hπT q₀ (DEG.cdeg (r := r) hΛℤ A₀) (fun ρ y => hcr ρ y)
  refine ⟨fun {E A} f => Ws2DegC.degAt q₀ f, hpos, hprod, hpad, ?_, ?_, ?_⟩
  ·
    intro u u' ρ ρ' i hi hI ib hib hibf uA huA huAg i₁ j₁ hrel
    let y' : ↥ρ'.Ab.A := (ρ'.Ab.L.one (𝟙 (Spec (CommRingCat.of (T ⧸ Ideal.span {algebraMap 𝒪 T π}))))).1.base q₀
    have key := CerednikDrinfeld.QM.FakeEllipticCurve.Rigidification.finrank_mul_finrank_act_pow_eq_of_corr 𝒪 π Onr Λ hΛℤ A₀
      T ((IsScalarTower.toAlgHom 𝒪 C T).comp χC) u.1 u'.1 ρ ρ' i hi ib hib hibf uA huA huAg i₁ j₁ hrel y'
    have he : (⟨(((r ^ 1 : ℕ) : ℤ) : ℚ), hΛℤ _⟩ : ↥Λ) = ⟨(((r : ℕ) : ℤ) : ℚ), hΛℤ _⟩ := Subtype.ext (by simp)
    rw [he, hcr ρ (uA.base y'), DEG.finrank_φ_eq hΛℤ A₀ T hTc hπT ((IsScalarTower.toAlgHom 𝒪 C T).comp χC) u.1 ρ (uA.base y')
      ((ρ.Ab.L.one (𝟙 (Spec (CommRingCat.of (T ⧸ Ideal.span {algebraMap 𝒪 T π}))))).1.base q₀)] at key
    exact key
  ·
    intro u u' ρ ρ' i hi hI ib hib hibf uA huA huAg i₁ hrel
    exact DEG.comp_eq_of_comp_act_pow_eq hΛℤ A₀ T ((IsScalarTower.toAlgHom 𝒪 C T).comp χC) u.1 u'.1 ρ ρ' i hi ⟨hI.1, hI.2.1, hI.2.2.1⟩ ib hib hibf uA huA huAg i₁ hrel
  ·
    intro u ρ hd
    haveI hiso := ChartDict3.isIso_specMap_quotientMk π hπT
    let h := (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (Ideal.span {algebraMap 𝒪 T π})))).homeomorph
    let xT := (ptX D T ((IsScalarTower.toAlgHom 𝒪 C T).comp χC) rfl u ρ hd h0).1
    have hfT : ∀ p, δ.f (xT.base p) = Ws2DegC.degAt q₀ ρ.φ := by
      intro p
      obtain ⟨q, rfl⟩ : ∃ q, h q = p := ⟨h.symm p, h.apply_symm_apply p⟩
      exact (ChartDict3.degF_ptX_apply π A₀ χC fM Xs ξ ptX (ChartDict3.rdeg π A₀) huniq D T u ρ hd h0 q).trans
        ((hval T ((IsScalarTower.toAlgHom 𝒪 C T).comp χC) u.1 ρ).apply_eq_of_preconnectedSpace q q₀)
    have hgT : ∀ p, δ.g (xT.base p) = Ws2DegC.degAt q₀ ρ.φ' := by
      intro p
      show DEG.cdeg (r := r) hΛℤ A₀ ^ D / δ.f (xT.base p) = _
      rw [hfT p]
      have hp := hprod ρ
      rw [hd] at hp
      exact Nat.div_eq_of_eq_mul_left (hpos ρ).1 (by rw [← hp, mul_comm])
    have hcT : ∀ p, δ.c (xT.base p) = DEG.cdeg (r := r) hΛℤ A₀ := fun _ => rfl
    exact Ws16WC.DEGb.forall_mem_B_iff_inWindow_const δ xT _ _ _ hfT hgT hcT

end
end
end S_CerednikDrinfeld_QM_FakeEllipticCurve_exists_opens_ratioWindow_degree_laws_of_rigidifiedToG_of_bdd
end P2MW
export P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_exists_opens_ratioWindow_degree_laws_of_rigidifiedToG_of_bdd (solution)
