-- Prove2me | solution 1 for CerednikDrinfeld.QM.FakeEllipticCurve.exists_isoVia_corr_inducing_of_formalIso_of_isRigTransport_of_isAlgClosed
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.141142+00:00
-- url     : https://prove2.me/submissions/48d6c957-58d0-5d7e-8be2-92625e1b2856

import Definitions.Def_CerednikDrinfeld_QMRigidification
import Definitions.Def_CerednikDrinfeld_SpecialFormalFunctorG
import Definitions.Def_CerednikDrinfeld_CosetGraphAtPrime

import Definitions.Def_CerednikDrinfeld_QMFormalModuleOf
import Definitions.Def_CerednikDrinfeld_QMIsogeny
import Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_Rigidification_exists_represents_comp_act_pow_eq_of_isRigTransport_of_act_comp_hom_comp_eq
import Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_exists_iso_comp_eq_of_formalIso_comp_germ_eq_of_isIsogenyPair_of_hasHeight_four_of_isAlgClosed_of_constantCoeff_eq_zero
import Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_exists_isPullbackVia_id_comp_eq_of_isPullbackVia_of_isPullbackVia_of_isUnit
import Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_IsPullbackVia_exists_isFormalModuleVia_map_and_comp_eq
import Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_Rigidification_exists_germs_represents_comp_eq_of_represents_of_act_pow_comp_eq_of_constantCoeff_eq_zero
import Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_Rigidification_exists_isoVia_corr_inducing_of_iso_reduction_of_act_pow_comp_eq_of_isAlgClosed
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_exists_isoVia_corr_inducing_of_formalIso_of_isRigTransport_of_isAlgClosed
p2m_attr_erase "instance" "MvFormalGroup.Points.instNeg MvFormalGroup.Points.instZero MvFormalGroup.Points.instAdd MvFormalGroup.Points.instAddCommGroup MvFormalGroup.Points.instAddGroup instTopologicallyFGOfFiniteType GoodReductionJacobian.RelativeGroupLaw.isIso_endKerStr_schemeHomOverId AlgebraicGeometry.Scheme.PresheafOfModules.symmetricCategory SheafOfModules.instFaithfulRingSheafPModToPMod SheafOfModules.symmetricCategory AlgebraicGeometry.Scheme.PresheafOfModules.monoidalCategory AlgebraicGeometry.Scheme.PresheafOfModules.monoidalClosed SheafOfModules.instFullRingSheafPModToPMod SheafOfModules.monoidalCategory AlgebraicGeometry.Scheme.Modules.symmetricCategory SheafOfModules.monoidalClosed SheafOfModules.instIsLocalizationPModRingSheafSheafifyFunctorPresheafW SheafOfModules.sheafifyFunctor_monoidal AlgebraicGeometry.Scheme.Modules.monoidalClosed AlgebraicGeometry.instMonoidalPresheafOfModulesModulesSheafify AlgebraicGeometry.Scheme.Modules.monoidalCategory PresheafOfModules.instMonoidalClosed PresheafOfModules.InternalHom.instModuleCarrierObjOppositeCommRingCatSubtypePiFamilyMemAddSubgroupNaturalFamilies PresheafOfModules.InternalHom.instModuleCarrierObjOppositeRingCatCompCommRingCatForget₂RingHomCarrierCarrierAbPresheaf PresheafOfModules.InternalHom.instSMulCarrierObjOppositeCommRingCatSubtypePiFamilyMemAddSubgroupNaturalFamilies AlgebraicGeometry.Scheme.Hom.opensMapFinal AlgebraicGeometry.RelPicard.RigidifiedLineBundle.setoid AlgebraicGeometry.RelPicard.RigidifiedLineBundle.instInhabited AlgebraicGeometry.OModulePresheaf.isScalarTower AlgebraicGeometry.Scheme.OrderedAffineCover.instLinearOrder AlgebraicGeometry.OModulePresheaf.module AlgebraicGeometry.Scheme.OrderedAffineCover.instFintype AlgebraicGeometry.Scheme.OrderedAffineCover.instFintypeIdx AlgebraicGeometry.OModulePresheaf.addCommGroup AlgebraicGeometry.Scheme.OrderedAffineCover.instDecidableEqIdx AlgebraicGeometry.OModulePresheaf.moduleSections TwoChartCech.Sections.M0_moduleA TwoChartCech.Sections.M1_module TwoChartCech.Cover.A01_algebra TwoChartCech.Cover.A0_algebra"
p2m_attr_erase "instance" "TwoChartCech.Cover.A1_commRing TwoChartCech.Cover.A1_algebra TwoChartCech.Sections.M01_module TwoChartCech.Sections.M0_addCommGroup TwoChartCech.Sections.M0_tower TwoChartCech.Sections.M01_addCommGroup TwoChartCech.Cover.A0_commRing TwoChartCech.Sections.M1_tower TwoChartCech.Sections.M01_moduleA TwoChartCech.Sections.M0_module TwoChartCech.Sections.M1_moduleA TwoChartCech.Sections.M1_addCommGroup TwoChartCech.Cover.A01_commRing TwoChartCech.Sections.M01_tower CoherentBaseChange.TwoTermComplex.C0_module CoherentBaseChange.TwoTermComplex.C0_addCommGroup CoherentBaseChange.TwoTermComplex.C1_module CoherentBaseChange.TwoTermComplex.C1_addCommGroup CoherentBaseChange.TwoTermComplex.C0_free CoherentBaseChange.TwoTermComplex.C1_finite CoherentBaseChange.TwoTermComplex.C0_finite CoherentBaseChange.TwoTermComplex.C1_free AlgebraicGeometry.OModulePresheaf.instSubsingletonObjZero AlgebraicGeometry.Scheme.Modules.preservesBinaryProducts_opensMap AlgebraicGeometry.Scheme.Modules.pullback_monoidal AlgebraicGeometry.Scheme.Modules.sheafify_isLocalization' AlgebraicGeometry.Scheme.Modules.preservesTerminal_opensMap AlgebraicGeometry.Scheme.Modules.pullback₀_monoidal AlgebraicGeometry.Scheme.Modules.preservesFiniteProducts_opensMap AlgebraicGeometry.Scheme.Modules.instLiftingPresheafOfModulesSheafifyPresheafWOpensCarrierCarrierCommRingCatGrothendieckTopologyObjFunctorOppositeIsSheafSheafCompPullback₀Pullback PresheafOfModules.PullbackMonoidal.pullback_monoidal PresheafOfModules.PullbackMonoidal.isIso_δ PresheafOfModules.pushforward_laxMonoidal PresheafOfModules.PullbackMonoidal.isIso_η PresheafOfModules.free_monoidal PresheafOfModules.restrictScalars_laxMonoidal PresheafOfModules.PullbackMonoidal.isIso_δ_gS PresheafOfModules.pullback_oplaxMonoidal PresheafOfModules.PullbackMonoidal.instPreservesColimitsOfSizeCompOppositeCommRingCatRingCatForget₂RingHomCarrierCarrierPb PresheafOfModules.pullback_monoidal'"
p2m_attr_erase "instance" "AlgebraicGeometry.SmoothOfRelativeDimension.fiberToSpecResidueField AlgebraicGeometry.SmoothOfRelativeDimension.pullback_snd AlgebraicGeometry.SmoothOfRelativeDimension.pullback_fst AlgebraicGeometry.SmoothOfRelativeDimension.smooth_one AlgebraicGeometry.SmoothProperCurve.isIntegral_pullback_Spec_field AlgebraicGeometry.IsProper.fiberToSpecResidueField AlgebraicCurve.CurveModel.isProper AlgebraicCurve.CurveModel.isIntegral AlgebraicCurve.CurveModel.smooth AlgebraicGeometry.Scheme.LocalRepresentabilityULift.instIsLocallyInjectiveFunUliftYonedaGluedToSheaf AlgebraicGeometry.Scheme.LocalRepresentabilityULift.instIsLocallySurjectiveFunUliftYonedaGluedToSheafOfIsLocallySurjectiveZariskiTopologyDescFunctorOppositeType AlgebraicGeometry.Scheme.LocalRepresentabilityULift.instIsOpenImmersionToGlued AlgebraicGeometry.Scheme.LocalRepresentabilityULift.instIsIsoSheafZariskiTopologyTypeUliftYonedaGluedToSheaf AlgebraicGeometry.RelPicard.instIsOpenImmersionToGlued AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.instFundamentalIdentityOfSumRamificationInertia AlgebraicCurve.Place.instIsScalarTowerResidueFieldRestrictPushforward AlgebraicCurve.Place.instAlgebraResidueFieldRestrictPushforward AlgebraicCurve.Place.instIsLocalHomRestrictInclusion AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions PresheafOfModules.ExteriorPower.instModulePresheafAb AlgebraicGeometry.RelEffCartierDiv.subsingleton_of_degree_zero AlgebraicGeometry.RelEffCartierDiv.isIso_subschemeIota_snd_of_degree_one AlgebraicGeometry.isIso_ker_graphOver_subschemeIota_snd AlgebraicGeometry.isClosedImmersion_graphOver AlgebraicGeometry.FGSubalgebra.instIsDirectedLe AlgebraicGeometry.FGSubalgebra.instQuasiSeparatedSpaceCarrierCarrierCommRingCatObjOppositeSchemeSpecDiagram AlgebraicGeometry.FGSubalgebra.instIsCofilteredOpposite AlgebraicGeometry.FGSubalgebra.instIsAffineObjOppositeSchemeSpecDiagram AlgebraicGeometry.FGSubalgebra.instNonempty AlgebraicGeometry.FGSubalgebra.instNonemptySubtypeLeSubalgebraValFG AlgebraicGeometry.FGSubalgebra.instCompactSpaceCarrierCarrierCommRingCatObjOppositeSchemeSpecDiagram AlgebraicGeometry.FGSubalgebra.instIsDirectedSubtypeLeSubalgebraValFG AlgebraicGeometry.FGSubalgebra.instIsAffineHomMapOppositeSchemeSpecDiagram"
p2m_attr_erase "instance" "AlgebraicGeometry.FGSubalgebra.instIsFiltered AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instNeg AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instSMulInt AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instAddCommGroup AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instAdd AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instSub AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instModuleCarrierObjOppositeOpensCarrierCarrierCommRingCatPresheafOpOpensTop AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instSMulCarrierObjOppositeOpensCarrierCarrierCommRingCatPresheafOpOpensTop AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instSMulNat AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instZero AlgebraicCurve.instHasLocalResidue_of_hasCanonicalLocalResidueK AlgebraicCurve.instHasCanonicalLocalResidueK_of_hasCanonicalLocalResidueKStar AlgebraicCurve.Place.kw_ffgc_finiteDimensional_adicCompletion instAlgebraSubtypeMemValuationSubring_definitions AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersIntegersCompletion ModularCurve.KwF4gRRTate.instAlgebraKAdicCompletionIntegers AlgebraicCurve.Place.kw_ffgc_continuousSMul_adicCompletionComap AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersCompletionCompletion IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions AlgebraicCurve.instHasCanonicalLocalResidueK AlgebraicCurve.Place.instAlgebra_restrictResidueField AlgebraicCurve.Place.instIsScalarTower_restrictResidueField AlgebraicCurve.instHasLocalResidue AlgebraicCurve.HasSeparableResidue.of_perfectField_of_isCurveOver AlgebraicCurve.HasSeparableResidue.of_perfectField AlgebraicCurve.Place.instIsLocalHom_restrictSubringHom AlgebraicCurve.instHasCanonicalLocalResidueKStar ModularCurve.KwNo6Pin.isLocalRing_completion SheafOfModules.isIso_ihomModelToIhom AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instDecidableEqIdx AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instFintype AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instLinearOrder AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instFintypeIdx AlgebraicGeometry.OModulePresheaf.Leray.relAltC_scalarTower AlgebraicGeometry.OModulePresheaf.Leray.ker_relAltd_modΓ"
p2m_attr_erase "instance" "AlgebraicGeometry.OModulePresheaf.Leray.relAltC_modΓ AlgebraicGeometry.OModulePresheaf.Leray.biC_abGrp AlgebraicGeometry.OModulePresheaf.Leray.relAltH_modΓ AlgebraicGeometry.OModulePresheaf.Leray.ker_relAltd_smul AlgebraicGeometry.OModulePresheaf.Leray.relAltH_scalarTower AlgebraicGeometry.OModulePresheaf.Leray.relAltH_smul AlgebraicGeometry.OModulePresheaf.Leray.biC_module DoubleComplex.instModuleE₂I DoubleComplex.Bounded.modR DoubleComplex.instModuleE₂II DoubleComplex.instAddCommGroupE₂II DoubleComplex.Bounded.abGrp DoubleComplex.instAddCommGroupE₂I AlgebraicGeometry.ChowDatum.hι_closed AlgebraicGeometry.ChowDatumProj.hιN_closed AlgebraicGeometry.ChowDatumProj.hp_proper AlgebraicGeometry.ChowDatum.hp_isoU AlgebraicGeometry.ChowDatum.hp_proper AlgebraicGeometry.ProjSpace.algebraAway AlgebraicGeometry.ProjSpace.instIsProperProdOverπ AlgebraicGeometry.ChowDatumProj.hp_isoU AlgebraicGeometry.ProjSpace.isProper_π AlgebraicGeometry.ProjSpace.finiteType_mvPolynomial ProjSpaceCech.GradedModule.H.module ProjSpaceCech.GradedModule.H.addCommGroup ProjSpaceCech.GradedModule.sec.instAdd ProjSpaceCech.GradedModule.sec.instNeg ProjSpaceCech.GradedModule.acg ProjSpaceCech.GradedModule.Frac.setoid ProjSpaceCech.GradedModule.modR ProjSpaceCech.GradedModule.sec.instModule ProjSpaceCech.GradedModule.sec.instAddCommGroup ProjSpaceCech.GradedModule.sec.instZero ProjSpaceCech.GradedModule.Presentation.fJ ProjSpaceCech.GradedModule.sec.instSMul ProjSpaceCech.Twist.H.module ProjSpaceCech.Idx.instFintype ProjSpaceCech.Twist.H.addCommGroup ProjSpaceCech.Idx.instDecidableEq ProjSpaceCech.Twist.Mon.instDecidableEq"
p2m_attr_erase "instance" "ProjSpaceCech.Twist.cochain.instAddCommGroup ProjSpaceCech.Twist.cochain.instModule AlgebraicGeometry.FGSubalgebra.tensorStage_directedSystem AlgebraicGeometry.RelEffCartierDiv.isClosedImmersion_subschemeι_resProdMap AlgebraicGeometry.RelEffCartierDiv.isOpenImmersion_resProdMap AlgebraicCurve.CurveModel.locallyOfFiniteType_gluedToBase AlgebraicCurve.CurveModel.isFractionRing_overlap AlgebraicCurve.CurveModel.isLocallyNoetherian_glued AlgebraicCurve.CurveModel.jacobsonSpace_glued AlgebraicCurve.CurveModel.isOpenImmersion_ι₀ AlgebraicCurve.CurveModel.isIntegral_glued AlgebraicCurve.CurveModel.quasiSeparated_gluedToBase AlgebraicCurve.CurveModel.compactSpace_glued AlgebraicCurve.CurveModel.isIntegral_adjoin_chartRing AlgebraicCurve.CurveModel.isFractionRing_overlap_functionField AlgebraicCurve.CurveModel.isProper_gluedToBase AlgebraicCurve.CurveModel.isOpenImmersion_ιU AlgebraicCurve.CurveModel.isOpenImmersion_f₀ AlgebraicCurve.CurveModel.isOpenImmersion_fInf AlgebraicCurve.CurveModel.isOpenImmersion_ιInf AlgebraicCurve.CurveModel.algebra_overlap_functionField AlgebraicCurve.CurveModel.quasiCompact_gluedToBase AlgebraicCurve.CurveModel.algebraAdjoin AlgebraicCurve.CurveModel.isDedekindDomain_chartRing AlgebraicCurve.CurveModel.isIntegralClosure AlgebraicCurve.CurveModel.finite_chartRing AlgebraicCurve.CurveModel.centre_isPrime AlgebraicCurve.CurveModel.isFractionRing_chartRing AlgebraicCurve.CurveModel.finiteType_chartRing AlgebraicCurve.CurveModel.isNoetherianRing_chartRing AlgebraicCurve.CurveModel.isScalarTower_base_adjoin AlgebraicCurve.CurveModel.isScalarTower_adjoin AlgebraicCurve.CurveModel.chartRing_finitePresentation AlgebraicGeometry.ProjSpace.twistObj.addCommGroup AlgebraicGeometry.ProjSpace.twistFam.module AlgebraicGeometry.ProjSpace.twistObj.module AlgebraicGeometry.ProjSpace.twistObj.moduleSections AlgebraicGeometry.ProjSpace.twistFam.addCommGroup kmfloorsGlue_int_three_isPrime kmfloorsGlue_int_bot_isPrime"
p2m_attr_erase "simp" "MvFormalGroup.Points.mk.injEq MvFormalGroup.Points.mk.sizeOf_spec GoodReductionJacobian.RelativeGroupLaw.nsmul_zero GoodReductionJacobian.RelativeGroupLaw.mem_torsionSubset GoodReductionJacobian.RelativeGroupLaw.nsmul_succ GoodReductionJacobian.RelativeGroupLaw.baseChangePointToBase_ofBase GoodReductionJacobian.RelativeGroupLaw.baseChangePointToBase_coe GoodReductionJacobian.RelativeGroupLaw.baseChangePointOfBase_coe GoodReductionJacobian.RelativeGroupLaw.baseChange_inv GoodReductionJacobian.RelativeGroupLaw.baseChangePointOfBase_toBase GoodReductionJacobian.RelativeGroupLaw.baseChange_mul GoodReductionJacobian.RelativeGroupLaw.baseChange_one NeronModelInfra.NeronModelPropertyBundle.endExtensionEquiv_symm_restrict NeronModelInfra.schemeHomOverComp_id_left NeronModelInfra.schemeHomOverComp_id_right NeronModelInfra.schemeHomOverId_coe NeronModelInfra.NeronModelPropertyBundle.endExtensionEquiv_apply NeronModelInfra.NeronModelPropertyBundle.restrict_endExtensionEquiv_symm NeronModelInfra.schemeHomOverComp_coe NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_fst NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_snd NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_fst NeronSpecialFibreInfra.neronEndRestrictEquiv_apply NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_fst_assoc NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_snd NeronSpecialFibreInfra.neronEndExtension_genericFibreRestrict NeronSpecialFibreInfra.specClosedFibreInclusion_eq NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_fst_assoc NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_snd_assoc NeronSpecialFibreInfra.genericFibreRestrict_neronEndExtension NeronSpecialFibreInfra.homOverId_coe NeronSpecialFibreInfra.homOverComp_coe NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_snd_assoc GoodReductionJacobian.RelativeGroupLaw.fibre_inv GoodReductionJacobian.RelativeGroupLaw.fibrePointToBase_coe GoodReductionJacobian.RelativeGroupLaw.fibrePointOfBase_toBase GoodReductionJacobian.RelativeGroupLaw.fibre_mul GoodReductionJacobian.RelativeGroupLaw.fibrePointToBase_ofBase GoodReductionJacobian.RelativeGroupLaw.fibre_one GoodReductionJacobian.RelativeGroupLaw.fibrePointOfBase_coe"
p2m_attr_erase "simp" "AlgebraicGeometry.schemeFibreEndo_snd AlgebraicGeometry.schemeFibreEndo_fst RegularLocalRingQuotientAscent.dualNumberFst_apply AlgebraicGeometry.Scheme.relFrobenius_snd AlgebraicGeometry.Scheme.frobenius_preimage AlgebraicGeometry.Scheme.relFrobenius_fst AlgebraicGeometry.Scheme.relFrobenius_snd_assoc AlgebraicGeometry.Scheme.relFrobenius_fst_assoc AlgebraicGeometry.powCharRingHom_apply AlgebraicGeometry.Scheme.frobenius_base NeronModelInfra.schemeHomOverNpow_succ NeronModelInfra.schemeHomOverNpow_zero GoodReductionJacobian.relativeGroupLawOfGrpObj_inv GoodReductionJacobian.relativeGroupLawOfGrpObj_mul GoodReductionJacobian.overHomEquivSchemeHomOver_apply_coe GoodReductionJacobian.relativeGroupLawOfGrpObj_one GoodReductionJacobian.overHomEquivSchemeHomOver_symm_apply_left SheafOfModules.tensorUnit_eq AlgebraicGeometry.Scheme.Modules.tensorUnit_eq PresheafOfModules.InternalHom.presheaf_map_apply PresheafOfModules.InternalHom.curryFamily_app PresheafOfModules.InternalHom.add_app PresheafOfModules.InternalHom.smul_app PresheafOfModules.InternalHom.zero_app PresheafOfModules.ihomObj_map_val PresheafOfModules.ihomFunctor_map PresheafOfModules.InternalHom.restrict_app PresheafOfModules.InternalHom.postcomp_app PresheafOfModules.InternalHom.neg_app PresheafOfModules.curry'_app_val PresheafOfModules.InternalHom.presheaf_obj PresheafOfModules.ihomFunctor_obj PresheafOfModules.ihomObj_obj PresheafOfModules.InternalHom.sub_app PresheafOfModules.ihomMap_app_val AlgebraicGeometry.Scheme.Modules.tensorPow_zero AlgebraicGeometry.Scheme.Modules.tensorPow_succ AlgebraicGeometry.RelPicard.RigidifiedLineBundle.mk.sizeOf_spec AlgebraicGeometry.RelPicard.RigidifiedLineBundle.mk.injEq AlgebraicGeometry.Scheme.OrderedAffineCover.mk.injEq"
p2m_attr_erase "simp" "AlgebraicGeometry.OModulePresheaf.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCover.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.mk.injEq AlgebraicGeometry.Scheme.TwoAffineOpenCover.mk.injEq AlgebraicGeometry.Scheme.TwoAffineOpenCover.mk.sizeOf_spec AlgebraicGeometry.Scheme.TwoAffineOpenCover.pullback_U1 AlgebraicGeometry.Scheme.TwoAffineOpenCover.pullback_U0 TwoChartCech.Sections.mk.injEq TwoChartCech.Cover.mk.injEq TwoChartCech.GrothendieckComplex.mk.injEq TwoChartCech.Sections.mk.sizeOf_spec TwoChartCech.Cover.mk.sizeOf_spec TwoChartCech.Cover.lineBundle_r0_apply TwoChartCech.GrothendieckComplex.mk.sizeOf_spec TwoChartCech.Cover.lineBundle_r1_apply CoherentBaseChange.TwoTermComplex.mk.sizeOf_spec CoherentBaseChange.TwoTermComplex.mk.injEq AlgebraicGeometry.OModulePresheaf.prod_obj AlgebraicGeometry.OModulePresheaf.restrOpen_obj AlgebraicGeometry.OModulePresheaf.DevissageStep.mk.injEq AlgebraicGeometry.OModulePresheaf.pushforward_obj AlgebraicGeometry.OModulePresheaf.im_obj AlgebraicGeometry.OModulePresheaf.pow_obj AlgebraicGeometry.OModulePresheaf.fstHom_app AlgebraicGeometry.OModulePresheaf.ker_obj AlgebraicGeometry.OModulePresheaf.coker_obj AlgebraicGeometry.OModulePresheaf.DevissageStep.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCover.preimage_U AlgebraicGeometry.OModulePresheaf.sndHom_app AlgebraicGeometry.OModulePresheaf.Hom.mk.injEq AlgebraicGeometry.OModulePresheaf.Hom.id_app AlgebraicGeometry.OModulePresheaf.AffHom.appSections_apply AlgebraicGeometry.OModulePresheaf.AffHom.comp_app AlgebraicGeometry.OModulePresheaf.AffSES.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.AffHom.kerMap_coe AlgebraicGeometry.OModulePresheaf.AffHom.id_app AlgebraicGeometry.OModulePresheaf.Hom.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.Hom.toAffHom_app AlgebraicGeometry.OModulePresheaf.SES.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.AffHom.mk.sizeOf_spec"
p2m_attr_erase "simp" "AlgebraicGeometry.OModulePresheaf.Hom.comp_app AlgebraicGeometry.OModulePresheaf.SES.mk.injEq AlgebraicGeometry.OModulePresheaf.AffHom.mk.injEq AlgebraicGeometry.OModulePresheaf.Hom.appSections_apply AlgebraicGeometry.OModulePresheaf.AffSES.mk.injEq PresheafOfModules.freeεIso_hom_app PresheafOfModules.freeμIso_hom_app AlgebraicGeometry.RelPicard.RepresentsRelSubPic.mk.injEq AlgebraicGeometry.RelPicard.SubPicCondition.mk.injEq AlgebraicGeometry.RelPicard.SubPicCondition.mk.sizeOf_spec AlgebraicGeometry.RelPicard.RepresentsRelSubPic.mk.sizeOf_spec AlgebraicGeometry.SmoothProperCurve.sectionBaseChange_coe_snd AlgebraicGeometry.SmoothProperCurve.sectionBaseChange_coe_fst AlgebraicCurve.CurveModel.mk.injEq AlgebraicCurve.CurveModel.mk.sizeOf_spec AlgebraicCurve.mulAdele_apply AlgebraicCurve.residuePairing_apply_coe AlgebraicCurve.mem_adeleBdd AlgebraicCurve.weilSmul_one AlgebraicCurve.diagonalHom_apply AlgebraicCurve.weilSmul_apply AlgebraicCurve.adeleSpaceMul_coe AlgebraicCurve.mulAdele_one AlgebraicGeometry.SmoothProperCurve.FiniteMapData.twoAffineOpenCover_U1 AlgebraicGeometry.SmoothProperCurve.FiniteMapData.mk.injEq AlgebraicGeometry.SmoothProperCurve.FiniteMapData.mk.sizeOf_spec AlgebraicGeometry.SmoothProperCurve.FiniteMapData.twoAffineOpenCover_U0 AlgebraicGeometry.RelPicard.SubPicCondition.onClasses_mk AlgebraicGeometry.RelPicard.relSubPicPresheaf_map_coe CategoryTheory.Functor.OverTotal.ofFibre_fst CategoryTheory.Functor.overTotal_map_fst AlgebraicGeometry.Scheme.LocalRepresentabilityULift.glueData_J AlgebraicGeometry.Scheme.LocalRepresentabilityULift.uliftYoneda_toGlued_uliftYonedaGluedToSheaf AlgebraicGeometry.Scheme.LocalRepresentabilityULift.glueData_t' AlgebraicGeometry.Scheme.LocalRepresentabilityULift.uliftYoneda_toGlued_uliftYonedaGluedToSheaf_assoc AlgebraicGeometry.Scheme.LocalRepresentabilityULift.uliftYonedaGluedToSheaf_app_toGlued AlgebraicGeometry.Scheme.LocalRepresentabilityULift.glueData_openCover_map AlgebraicGeometry.Scheme.LocalRepresentabilityULift.uliftYonedaGluedToSheaf_app_comp AlgebraicGeometry.Scheme.LocalRepresentabilityULift.glueData_V AlgebraicGeometry.Scheme.LocalRepresentabilityULift.glueData_t"
p2m_attr_erase "simp" "AlgebraicGeometry.Scheme.LocalRepresentabilityULift.glueData_U AlgebraicGeometry.Scheme.LocalRepresentabilityULift.glueData_f AlgebraicGeometry.RelPicard.designationOfRepresentableBy_P AlgebraicGeometry.RelPicard.designationOfRepresentableBy_toBase AlgebraicGeometry.RelPicard.rigSection_snd AlgebraicGeometry.RelPicard.RigidifiedLineBundle.ofInvertible_L AlgebraicGeometry.RelPicard.rigSection_snd_assoc AlgebraicGeometry.RelPicard.SubPicGroupCondition.mk.injEq AlgebraicGeometry.RelPicard.SubPicGroupCondition.mk.sizeOf_spec AlgebraicCurve.coe_cechH0Equiv_apply AlgebraicCurve.cechH1ToH1_mk AlgebraicCurve.lSpaceOn_univ AlgebraicCurve.lSpaceOn_empty AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.Divisor.mapRestrict_single AlgebraicCurve.Divisor.pushforward_single AlgebraicCurve.Place.coe_restrictInclusion AlgebraicCurve.Place.mem_fiber AlgebraicCurve.Place.restrict_toValuationSubring AlgebraicCurve.Divisor.degree_pushforward AlgebraicCurve.Place.restrictResidueMap_residue AlgebraicCurve.Pic0.coe_pushforwardDegZeroHom AlgebraicCurve.Pic0.coe_pullbackDegZeroHom AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk"
p2m_attr_erase "simp" "ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Divisor.degree_pushforwardAlong AlgebraicCurve.Pic0.coe_degZeroCorrespondence AlgebraicCurve.Place.mem_fiberAlong AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.jqNModC_one ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one AlgebraicCurve.Place.differentialCoeff_zero AlgebraicCurve.Place.differentialCoeff_dCoord AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.injEq AlgebraicCurve.TranscendenceTower.mk.injEq AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec AlgebraicCurve.PoleDivisorPackage.mk.injEq AlgebraicGeometry.RelPicard.thetaBundle_def AlgebraicGeometry.RelPicard.picardBundle_def AlgebraicGeometry.RelEffCartierDiv.toRelEffDivisor_ofRelEffDivisor AlgebraicGeometry.RelEffCartierDiv.toRelEffDivisor_I"
p2m_attr_erase "simp" "AlgebraicGeometry.mapOnProdOver_fst_assoc AlgebraicGeometry.RelEffCartierDiv.mk.sizeOf_spec AlgebraicGeometry.RelEffCartierDiv.mk.injEq AlgebraicGeometry.mapOnProdOver_snd AlgebraicGeometry.mapOnProdOver_fst AlgebraicGeometry.mapOnProdOver_snd_assoc AlgebraicGeometry.mapOnProdOver_id AlgebraicCurve.RelEffDivisor.mk.sizeOf_spec AlgebraicCurve.mapOnProd_fst AlgebraicCurve.mapOnProd_fst_assoc AlgebraicCurve.mapOnProd_snd AlgebraicCurve.UnivDivisorPack.mk.injEq AlgebraicCurve.RelEffDivisor.mk.injEq AlgebraicCurve.UnivDivisorPack.mk.sizeOf_spec AlgebraicCurve.mapOnProd_snd_assoc AlgebraicGeometry.Scheme.Modules.exteriorPower_obj PresheafOfModules.exteriorPower_map_ιMulti PresheafOfModules.ExteriorPower.appₗ_apply AlgebraicGeometry.prodKerGraph_one AlgebraicGeometry.fibrePowOver.proj_comp AlgebraicGeometry.prodKerGraph_zero AlgebraicGeometry.RelEffCartierDiv.empty_I AlgebraicGeometry.fibrePowOver.proj_comp_assoc AlgebraicGeometry.graphOver_fst_assoc AlgebraicGeometry.RelEffCartierDiv.toPoint_comp AlgebraicGeometry.RelEffCartierDiv.toPoint_comp_assoc AlgebraicGeometry.graphOver_fst AlgebraicGeometry.RelEffCartierDiv.ofPoint_I AlgebraicGeometry.graphOver_snd AlgebraicGeometry.graphOver_snd_assoc AlgebraicCurve.SymmetricPowerPackage.mk.sizeOf_spec AlgebraicCurve.SymmetricPowerPackage.mk.injEq AlgebraicGeometry.FGSubalgebra.cocone_ι_app_apply AlgebraicGeometry.RelPicard.fst_toProdSpec AlgebraicGeometry.RelPicard.toProdSpec_fst_assoc AlgebraicGeometry.RelPicard.pointsSubBasepointModule_cons AlgebraicGeometry.RelPicard.pointsSubBasepointModule_nil AlgebraicGeometry.RelPicard.fst_toProdSpec_assoc AlgebraicGeometry.RelPicard.toProdSpec_fst AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.sub_app"
p2m_attr_erase "simp" "AlgebraicGeometry.Scheme.IdealSheafData.sres_sresTop AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.add_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.mk.sizeOf_spec AlgebraicGeometry.Scheme.IdealSheafData.coe_resLE AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.smul_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.coe_ofLE_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.ideal_range AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.zero_app AlgebraicGeometry.Scheme.IdealSheafData.sres_sres AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.comp_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.neg_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.id_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.coe_mulRight_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.nsmul_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.mk.injEq AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.zsmul_app AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.sizeOf_spec AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.injEq AlgebraicCurve.adeleSingle_coe AlgebraicCurve.kaehlerResidueTermKFam_apply AlgebraicCurve.Place.LocalResidueData.mk.injEq AlgebraicCurve.Place.LocalResidueData.mk.sizeOf_spec AlgebraicCurve.Place.kw_ffgc_adicCompletionComapIntegers_coe AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.sizeOf_spec AlgebraicCurve.Place.mem_simplePoleSubmodule AlgebraicCurve.Place.coe_uniformizerSubring ModularCurve.Lg37.Lg37CompletionSection.mk.injEq AlgebraicCurve.Place.CoefficientFieldSection.mk.injEq AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.injEq ModularCurve.Lg37.Lg37CompletionSection.mk.sizeOf_spec AlgebraicCurve.Place.CoefficientFieldSection.mk.sizeOf_spec AlgebraicCurve.Place.poleSubmodule_one AlgebraicCurve.Place.mem_poleSubmodule AlgebraicGeometry.Scheme.Modules.toUnitSection_ofUnitSection AlgebraicGeometry.Scheme.Modules.pullbackSection_def AlgebraicGeometry.Scheme.Modules.ofUnitSection_toUnitSection PresheafOfModules.InternalHom.IsSheafAux.appAt_toPresheafHom SheafOfModules.ihomSectionsEquivFamily_unit AlgebraicGeometry.Scheme.Modules.restrictHomEquivFamily_apply SheafOfModules.ihomEval_unit_app"
p2m_attr_erase "simp" "AlgebraicGeometry.Scheme.Modules.ihomEval_zero_right AlgebraicGeometry.Scheme.Modules.ihomEval_zero_left AlgebraicGeometry.Scheme.Modules.homOfFamily_app_apply SheafOfModules.unit_ihomSectionsEquivFamily AlgebraicGeometry.Scheme.Modules.familyOfHom_app AlgebraicGeometry.Scheme.Modules.restrictUnitIso_hom_app_apply AlgebraicGeometry.Scheme.Modules.restrictUnitIso_inv_app_apply AlgebraicGeometry.Scheme.Modules.restrictHomOfFamily_app_apply AlgebraicGeometry.Scheme.Modules.restrictHomEquivFamily_symm_apply AlgebraicGeometry.Scheme.Modules.tensorSections_zero_right AlgebraicGeometry.Scheme.Modules.map_unitSection AlgebraicGeometry.Scheme.Modules.tensorSectionsBilin_apply AlgebraicGeometry.Scheme.Modules.tensorPowSection_zero AlgebraicGeometry.Scheme.Modules.tensorSections_zero_left AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_neg AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_zero AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_sub AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_add AlgebraicGeometry.Scheme.OrderedAffineCover.toCoverOf_U AlgebraicGeometry.Scheme.OrderedAffineCoverOf.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCoverOf.mk.injEq AlgebraicGeometry.Scheme.OrderedAffineCover.restrict_U AlgebraicGeometry.OModulePresheaf.Leray.restrictToPreimage_U DoubleComplex.Bounded.mk.injEq DoubleComplex.Bounded.mk.sizeOf_spec DoubleComplex.Convergence.mk.injEq DoubleComplex.Convergence.mk.sizeOf_spec DoubleComplex.SubQuot.mk.sizeOf_spec DoubleComplex.SubQuot.mk.injEq AlgebraicGeometry.ChowDatumProj.mk.sizeOf_spec AlgebraicGeometry.ChowDatum.mk.sizeOf_spec AlgebraicGeometry.ChowDatumProj.mk.injEq AlgebraicGeometry.ChowDatum.mk.injEq ProjSpaceCech.GradedModule.mk.injEq ProjSpaceCech.GradedModule.mk.sizeOf_spec ProjSpaceCech.GradedModule.Frac.mk.sizeOf_spec ProjSpaceCech.GradedModule.Presentation.mk.injEq ProjSpaceCech.GradedModule.Frac.mk.injEq ProjSpaceCech.GradedModule.Presentation.mk.sizeOf_spec ProjSpaceCech.GradedModule.Hom.shift_toLinearMap"
p2m_attr_erase "simp" "ProjSpaceCech.GradedModule.Hom.mk.sizeOf_spec ProjSpaceCech.GradedModule.Hom.mk.injEq TwoChartCech.Mumford.dK_apply TwoChartCech.Mumford.ι0_apply TwoChartCech.Mumford.ι1_apply TwoChartCech.KerCoprod.dK_apply TwoChartCech.KerCoprod.ι1_apply TwoChartCech.KerCoprod.ι0_apply AlgebraicGeometry.tilde.functorCompPullbackSpecIso_app AlgebraicGeometry.RelPicard.algEquivZeroGroupCut_toSubPicCondition AlgebraicGeometry.RelPicard.LFP.stageHom_val AlgebraicGeometry.RelPicard.BaseChange.relSubPicPresheafRestrictIso_hom_app_coe AlgebraicGeometry.RelPicard.BaseChange.relSubPicPresheafRestrictIso_inv_app_coe AlgebraicGeometry.RelPicard.BaseChange.restrict_P AlgebraicGeometry.RelEffCartierDiv.IsUniversal.lift_comp AlgebraicGeometry.RelEffCartierDiv.functor_map_fst AlgebraicGeometry.RelEffCartierDiv.IsUniversal.homEquiv_apply AlgebraicGeometry.RelEffCartierDiv.IsUniversal.lift_pullbackAlong AlgebraicGeometry.RelEffCartierDiv.IsUniversal.homEquiv_symm_apply AlgebraicGeometry.RelEffCartierDiv.IsUniversal.lift_comp_assoc AlgebraicGeometry.RelEffCartierDiv.supportedIn_top AlgebraicGeometry.RelEffCartierDiv.mem_supportedIn_iff AlgebraicGeometry.RelEffCartierDiv.supportedIn_top_eq AlgebraicGeometry.RelEffCartierDiv.restrictAlong_extendAlong AlgebraicGeometry.RelEffCartierDiv.extendAlong_I AlgebraicGeometry.RelEffCartierDiv.resProdMap_snd AlgebraicGeometry.RelEffCartierDiv.restrictAlong_I AlgebraicGeometry.RelEffCartierDiv.extendAlong_restrictAlong AlgebraicGeometry.RelEffCartierDiv.resProdMap_fst_assoc AlgebraicGeometry.RelEffCartierDiv.resProdMap_snd_assoc AlgebraicGeometry.RelEffCartierDiv.resProdMap_fst CoherentBaseChange.FibreH0Family.mk.sizeOf_spec CoherentBaseChange.FibreH0Family.mk.injEq AlgebraicGeometry.Scheme.Modules.ProjPresentation.mk.injEq AlgebraicGeometry.Scheme.Modules.ProjPresentation.mk.sizeOf_spec AlgebraicCurve.CurveModel.coe_gInf AlgebraicCurve.CurveModel.coe_tInvChart AlgebraicCurve.CurveModel.ιInf_gluedToBase_assoc AlgebraicCurve.CurveModel.ιInf_gluedToBase AlgebraicCurve.CurveModel.primeOfι₀_asIdeal"
p2m_attr_erase "simp" "AlgebraicCurve.CurveModel.coe_tChart AlgebraicCurve.CurveModel.ι₀_gluedToBase_assoc AlgebraicCurve.CurveModel.primeOfιInf_asIdeal AlgebraicCurve.CurveModel.ι₀_gluedToBase AlgebraicCurve.CurveModel.coe_tma AlgebraicCurve.CurveModel.coe_primeEquivChartPlaces AlgebraicGeometry.ProjSpace.twistObj.mk.injEq AlgebraicGeometry.ProjSpace.twistObj.zero_val AlgebraicGeometry.ProjSpace.twistObj.add_val AlgebraicGeometry.ProjSpace.twist_res_val AlgebraicGeometry.ProjSpace.twist_smul_val AlgebraicGeometry.ProjSpace.twistGradeToObj_val AlgebraicGeometry.ProjSpace.twistObj.smul_val AlgebraicGeometry.ProjSpace.twistGradeEquiv_apply_val AlgebraicGeometry.ProjSpace.twistObj.mk.sizeOf_spec"

set_option autoImplicit false

open scoped TensorProduct Quaternion NumberField
open CategoryTheory AlgebraicGeometry QuaternionAlgebra IsDedekindDomain CerednikDrinfeld CerednikDrinfeld.QM CerednikDrinfeld.FormalOmega CerednikDrinfeld.SpecialFormal NeronModelInfra GoodReductionJacobian

namespace FIRAsm

open CerednikDrinfeld.SpecialFormal

theorem isIso_map {p : ℕ} [Fact p.Prime] {R S : Type} [CommRing R] [CommRing S] (f : R →+* S) {X Y : FormalODModule p R}
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

section Pts
variable {R : Type} [CommRing R] {A : Scheme.{0}} {f : A ⟶ Spec (CommRingCat.of R)}

theorem mul_val_congr (L : RelativeGroupLaw R f) {T : Scheme.{0}} {t₁ t₂ : T ⟶ Spec (CommRingCat.of R)}
    (e : t₁ = t₂) (x₁ y₁ : SchemeHomOver t₁ f) (x₂ y₂ : SchemeHomOver t₂ f) (hx : x₁.1 = x₂.1) (hy : y₁.1 = y₂.1) :
    (L.mul t₁ x₁ y₁).1 = (L.mul t₂ x₂ y₂).1 := by
  subst e
  have h1 : x₁ = x₂ := Subtype.ext hx
  have h2 : y₁ = y₂ := Subtype.ext hy
  subst h1 h2
  rfl

theorem mapPt_hom_comp {A' A'' : Scheme.{0}} {f' : A' ⟶ Spec (CommRingCat.of R)} {f'' : A'' ⟶ Spec (CommRingCat.of R)}
    (L : RelativeGroupLaw R f) (L' : RelativeGroupLaw R f') (L'' : RelativeGroupLaw R f'')
    (φ : A ⟶ A') (hφ : φ ≫ f' = f) (ψ : A' ⟶ A'') (hψ : ψ ≫ f'' = f')
    (hφm : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of R)) (P Q : SchemeHomOver t f),
      mapPt φ hφ (L.mul t P Q) = L'.mul t (mapPt φ hφ P) (mapPt φ hφ Q))
    (hψm : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of R)) (P Q : SchemeHomOver t f'),
      mapPt ψ hψ (L'.mul t P Q) = L''.mul t (mapPt ψ hψ P) (mapPt ψ hψ Q))
    (hφψ : (φ ≫ ψ) ≫ f'' = f) :
    ∀ ⦃T : Scheme.{0}⦄ (t : T ⟶ Spec (CommRingCat.of R)) (P Q : SchemeHomOver t f),
      mapPt (φ ≫ ψ) hφψ (L.mul t P Q) = L''.mul t (mapPt (φ ≫ ψ) hφψ P) (mapPt (φ ≫ ψ) hφψ Q) := by
  intro T t P Q
  have e : ∀ (X : SchemeHomOver t f), mapPt (φ ≫ ψ) hφψ X = mapPt ψ hψ (mapPt φ hφ X) :=
    fun X => Subtype.ext (by simp only [mapPt_coe, Category.assoc])
  rw [e, e, e, hφm, hψm]

end Pts

section FEC
variable {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} {N : ℕ} {S : Type} [CommRing S]

theorem mul_of_isPullbackVia_id (E₁ E₂ : FakeEllipticCurve Λ N S) (h : E₂.A ⟶ E₁.A) (hh : h ≫ E₁.f = E₂.f)
    (hv : FakeEllipticCurve.IsPullbackVia (RingHom.id S) E₁ E₂ h) :
    ∀ ⦃T : Scheme.{0}⦄ (t : T ⟶ Spec (CommRingCat.of S)) (P Q : SchemeHomOver t E₂.f),
      mapPt h hh (E₂.L.mul t P Q) = E₁.L.mul t (mapPt h hh P) (mapPt h hh Q) := by
  intro T t P Q
  obtain ⟨hsq, hmul, -, -⟩ := hv
  apply Subtype.ext
  rw [mapPt_coe, hmul t P Q]
  have e : t ≫ Spec.map (CommRingCat.ofHom (RingHom.id S)) = t := by
    rw [CommRingCat.ofHom_id]
    erw [Spec.map_id]
    exact Category.comp_id t
  exact mul_val_congr E₁.L e _ _ _ _ rfl rfl

variable (E : FakeEllipticCurve Λ N S) (hΛℤ : ∀ m : ℤ, ((m : ℚ) : ℍ[ℚ, a, b]) ∈ Λ)

theorem act_rpow_comp (r i j : ℕ) :
    E.act ⟨(((r ^ i : ℕ) : ℤ) : ℚ), hΛℤ _⟩ ≫ E.act ⟨(((r ^ j : ℕ) : ℤ) : ℚ), hΛℤ _⟩ =
      E.act ⟨(((r ^ (i + j) : ℕ) : ℤ) : ℚ), hΛℤ _⟩ := by
  have hmem : ((((r ^ j : ℕ) : ℤ) : ℚ) : ℍ[ℚ, a, b]) * ((((r ^ i : ℕ) : ℤ) : ℚ) : ℍ[ℚ, a, b]) ∈ Λ := by
    rw [← QuaternionAlgebra.coe_mul]; exact_mod_cast hΛℤ ((r ^ j : ℕ) * (r ^ i : ℕ) : ℤ)
  rw [← E.act_mul ⟨_, hΛℤ _⟩ ⟨_, hΛℤ _⟩ hmem]
  congr 1
  apply Subtype.ext
  push_cast
  rw [← pow_add, Nat.add_comm]

theorem act_comm_coe (hO : IsOrder Λ) (q : ℚ) (hq : ((q : ℚ) : ℍ[ℚ, a, b]) ∈ Λ) (y : ↥Λ) :
    E.act y ≫ E.act ⟨(q : ℍ[ℚ, a, b]), hq⟩ = E.act ⟨(q : ℍ[ℚ, a, b]), hq⟩ ≫ E.act y := by
  rw [← E.act_mul ⟨(q : ℍ[ℚ, a, b]), hq⟩ y (hO.mul_mem hq y.2), ← E.act_mul y ⟨(q : ℍ[ℚ, a, b]), hq⟩ (hO.mul_mem y.2 hq)]
  congr 1
  apply Subtype.ext
  show (q : ℍ[ℚ, a, b]) * (y : ℍ[ℚ, a, b]) = (y : ℍ[ℚ, a, b]) * (q : ℍ[ℚ, a, b])
  rw [QuaternionAlgebra.coe_mul_eq_smul, QuaternionAlgebra.mul_coe_eq_smul]

theorem act_natpow_eq (r n : ℕ) (hd : (((r ^ n : ℕ) : ℚ) : ℍ[ℚ, a, b]) ∈ Λ) :
    E.act ⟨(((r ^ n : ℕ) : ℚ) : ℍ[ℚ, a, b]), hd⟩ = E.act ⟨(((r ^ n : ℕ) : ℤ) : ℚ), hΛℤ _⟩ := by
  congr 1
  all_goals (apply Subtype.ext; norm_cast)

end FEC

section CC
open MvPowerSeries

theorem constantCoeff_subst_of_constantCoeff_zero {S : Type} [CommRing S] (a : Fin 2 → MvPowerSeries (Fin 2) S)
    (ha0 : ∀ i, constantCoeff (a i) = 0) (f : MvPowerSeries (Fin 2) S) :
    constantCoeff (subst a f) = constantCoeff f := by
  have ha : HasSubst a := hasSubst_of_constantCoeff_zero ha0
  rw [constantCoeff_subst ha]
  rw [finsum_eq_single _ (0 : Fin 2 →₀ ℕ)]
  · simp
  · intro d hd
    obtain ⟨s, hs⟩ : ∃ s, d s ≠ 0 := by
      by_contra h; push Not at h; exact hd (Finsupp.ext fun s => by simpa using h s)
    rw [Finsupp.prod, map_prod]
    rw [Finset.prod_eq_zero (Finsupp.mem_support_iff.2 hs) (by rw [map_pow, ha0, zero_pow hs]), smul_zero]

theorem constantCoeff_comp {S : Type} [CommRing S] (ψ φ : CerednikDrinfeld.SpecialFormal.Series S)
    (hφ : ∀ i, constantCoeff (φ i) = 0) (i : Fin 2) :
    constantCoeff ((ψ.comp φ) i) = constantCoeff (ψ i) :=
  constantCoeff_subst_of_constantCoeff_zero φ hφ (ψ i)

theorem constantCoeff_frobSeries {p : ℕ} [Fact p.Prime] (S : Type) [CommRing S] (j : ℕ) (i : Fin 2) :
    constantCoeff (CerednikDrinfeld.SpecialFormal.Rigidified.frobSeries (p := p) S j i) = 0 := by
  show constantCoeff ((X i : MvPowerSeries (Fin 2) S) ^ (p ^ j)) = 0
  rw [map_pow, constantCoeff_X, zero_pow (pow_ne_zero _ (Fact.out : p.Prime).ne_zero)]

theorem constantCoeff_map_zero {S S' : Type} [CommRing S] [CommRing S'] (g : S →+* S')
    (φ : CerednikDrinfeld.SpecialFormal.Series S) (hφ : ∀ i, constantCoeff (φ i) = 0) (i : Fin 2) :
    constantCoeff ((φ.map g) i) = 0 := by
  show constantCoeff (MvPowerSeries.map g (φ i)) = 0
  rw [constantCoeff_map, hφ i, map_zero]

end CC

end FIRAsm

open FIRAsm in
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
    (E₀ : Subring.centralizer (Set.range Φ.actEnd ∪ {Φ.varpiEnd}) →+* Matrix (Fin 2) (Fin 2) K₀)
    (hE₀ : Function.Injective E₀ ∧
      ∃ m : ℕ,
        (∀ A : Matrix (Fin 2) (Fin 2) 𝒪, ∃ e, E₀ e = (r : K₀) ^ m • A.map (algebraMap 𝒪 K₀)) ∧
        (∀ e, ∃ A : Matrix (Fin 2) (Fin 2) 𝒪, (r : K₀) ^ m • E₀ e = A.map (algebraMap 𝒪 K₀)))

    (κ : (Onr ⧸ Ideal.span {algebraMap 𝒪 Onr π}) →+* (Onr ⧸ pIdeal r Onr))
    (hκ : κ.comp (Ideal.Quotient.mk (Ideal.span {algebraMap 𝒪 Onr π})) = Ideal.Quotient.mk (pIdeal r Onr))
    (n₀ : ℕ) (β₀ : Series (Onr ⧸ pIdeal r Onr)) (hβ₀ : FormalODModule.IsIsogenyOfHeight Φ (X₀.map κ) β₀ (4 * n₀))

    (k : Type) [Field k] [IsAlgClosed k] [Algebra 𝒪 k] (hk : IsNilpotent (algebraMap 𝒪 k π)) (hkr : IsNilpotent ((r : ℕ) : k))
    (ψ : Onr →ₐ[𝒪] k)
    (x x' : FakeEllipticCurve.RigidifiedCurve r π A₀ k ψ)
    (X X' : FormalODModule r k)
    (θ : RelativeGroupLaw.FormalCoordinates x.1.f 2) (θ' : RelativeGroupLaw.FormalCoordinates x'.1.f 2)
    (hX : x.1.IsFormalModuleVia coord X θ) (hX' : x'.1.IsFormalModuleVia coord X' θ')

    (j : ℕ) (t t' : Rigidified r Φ k) (htX : t.X = X) (ht'X : t'.X = X')
    (ht : FakeEllipticCurve.Rigidification.IsRigTransport θ₀ κ β₀ x.2 θ j t)
    (ht' : FakeEllipticCurve.Rigidification.IsRigTransport θ₀ κ β₀ x'.2 θ' j t')
    (hta : t.IsAdmissible ι ((frobTwist Onr Fr (-(j : ℤ)) ψ : Onr →ₐ[𝒪] k) : Onr →+* k))
    (ht'a : t'.IsAdmissible ι ((frobTwist Onr Fr (-(j : ℤ)) ψ : Onr →ₐ[𝒪] k) : Onr →+* k))

    (T₀ : FormalODModule.Hom X X') (hT₀ : T₀.IsIso) (m : ℕ)
    (hTρ : (t'.Xbar.act ((r : Zp2 r) ^ (m + t'.n))).comp
        ((T₀.toSeries.map (Ideal.Quotient.mk (pIdeal r k))).comp t.ρ) =
      (t'.Xbar.act ((r : Zp2 r) ^ (m + t.n))).comp t'.ρ) :
    ∃ (i : x.1.A ≅ x'.1.A) (hi : i.hom ≫ x'.1.f = x.1.f), FakeEllipticCurve.IsoVia x.1 x'.1 i hi ∧

      (∀ (B'' : Type) [CommRing B''] [Algebra k B''] (J : Ideal B'') (n : ℕ), J ^ (n + 1) = ⊥ →
          ∀ s : Fin 2 → B'', (∀ l, s l ∈ J) →
            (θ B'' s).1 ≫ i.hom = (θ' B'' (fun l => MvFormalGroup.nilEval n (T₀.toSeries l) s)).1) ∧

      ∃ (ib : x.2.Eb.A ⟶ x'.2.Eb.A) (_ : ib ≫ x'.2.gb = x.2.gb ≫ i.hom) (_ : ib ≫ x'.2.Eb.f = x.2.Eb.f)
        (uA : x'.2.Ab.A ⟶ x.2.Ab.A) (_ : FakeEllipticCurve.IsPullbackVia (RingHom.id _) x.2.Ab x'.2.Ab uA) (_ : uA ≫ x.2.gA = x'.2.gA)
        (i₁ j₁ : ℕ),
        ib ≫ x'.2.φ ≫ uA ≫ x.2.Ab.act ⟨(((r ^ i₁ : ℕ) : ℤ) : ℚ), hΛℤ _⟩ = x.2.φ ≫ x.2.Ab.act ⟨(((r ^ j₁ : ℕ) : ℤ) : ℚ), hΛℤ _⟩ := by
  classical

  have hπ0 : algebraMap 𝒪 k π = 0 := hk.eq_zero
  have hI : Ideal.span {algebraMap 𝒪 k π} = (⊥ : Ideal k) := by rw [hπ0, Ideal.span_singleton_eq_bot]
  haveI hImax : (Ideal.span {algebraMap 𝒪 k π}).IsMaximal := by rw [hI]; exact Ideal.bot_isMaximal
  letI instField : Field (k ⧸ Ideal.span {algebraMap 𝒪 k π}) := Ideal.Quotient.field _
  have hbij : Function.Bijective (Ideal.Quotient.mk (Ideal.span {algebraMap 𝒪 k π})) :=
    ⟨(Ideal.Quotient.mk (Ideal.span {algebraMap 𝒪 k π})).injective, Ideal.Quotient.mk_surjective⟩
  haveI : IsAlgClosed (k ⧸ Ideal.span {algebraMap 𝒪 k π}) :=
    IsAlgClosed.of_ringEquiv k _ (RingEquiv.ofBijective _ hbij)
  have hkr₁ : IsNilpotent ((r : ℕ) : k ⧸ Ideal.span {algebraMap 𝒪 k π}) := by
    have := hkr.map (Ideal.Quotient.mk (Ideal.span {algebraMap 𝒪 k π})); simpa using this
  have hN₁ : IsUnit ((N : ℕ) : k ⧸ Ideal.span {algebraMap 𝒪 k π}) := by
    have hr0 : (r : k) = 0 := hkr.eq_zero
    haveI : CharP k r := (CharP.charP_iff_prime_eq_zero Fact.out).mpr hr0
    have hNk : (N : k) ≠ 0 := fun h => hrN ((CharP.cast_eq_zero_iff k r N).mp h)
    rw [isUnit_iff_ne_zero]
    intro h
    apply hNk
    apply hbij.1
    rw [map_natCast, h, map_zero]
  have hΛ1 : (1 : ℍ[ℚ, a, b]) ∈ Λ := by simpa using hΛℤ 1

  obtain ⟨uA, huAg, huAf, huA⟩ :=
    CerednikDrinfeld.QM.FakeEllipticCurve.exists_isPullbackVia_id_comp_eq_of_isPullbackVia_of_isPullbackVia_of_isUnit
      (FakeEllipticCurve.Rigidification.residueLeg π ψ) hN₁ A₀ x.2.Ab x.2.gA x.2.isPullback_Ab x'.2.Ab x'.2.gA x'.2.isPullback_Ab
  obtain ⟨v, hvg, hvf, hv⟩ :=
    CerednikDrinfeld.QM.FakeEllipticCurve.exists_isPullbackVia_id_comp_eq_of_isPullbackVia_of_isPullbackVia_of_isUnit
      (FakeEllipticCurve.Rigidification.residueLeg π ψ) hN₁ A₀ x'.2.Ab x'.2.gA x'.2.isPullback_Ab x.2.Ab x.2.gA x.2.isPullback_Ab
  have huv : uA ≫ v = 𝟙 _ := by
    apply x'.2.isPullback_Ab.1.hom_ext
    · rw [Category.assoc, hvg, huAg, Category.id_comp]
    · rw [Category.assoc, hvf, huAf, Category.id_comp]
  have hvu : v ≫ uA = 𝟙 _ := by
    apply x.2.isPullback_Ab.1.hom_ext
    · rw [Category.assoc, huAg, hvg, Category.id_comp]
    · rw [Category.assoc, huAf, hvf, Category.id_comp]

  letI instOk : Algebra (Onr ⧸ Ideal.span {algebraMap 𝒪 Onr π}) (k ⧸ Ideal.span {algebraMap 𝒪 k π}) :=
    (FakeEllipticCurve.Rigidification.residueLeg π ψ).toAlgebra
  obtain ⟨θA, hθA, hθAg⟩ :=
    CerednikDrinfeld.QM.FakeEllipticCurve.IsPullbackVia.exists_isFormalModuleVia_map_and_comp_eq coord
      (Onr ⧸ Ideal.span {algebraMap 𝒪 Onr π}) (k ⧸ Ideal.span {algebraMap 𝒪 k π}) A₀ x.2.Ab x.2.gA x.2.isPullback_Ab X₀ θ₀ hA₀
  obtain ⟨θE, hθE, hθEg⟩ :=
    CerednikDrinfeld.QM.FakeEllipticCurve.IsPullbackVia.exists_isFormalModuleVia_map_and_comp_eq coord
      k (k ⧸ Ideal.span {algebraMap 𝒪 k π}) x.1 x.2.Eb x.2.gb x.2.isPullback_Eb X θ hX
  obtain ⟨θE', hθE', hθEg'⟩ :=
    CerednikDrinfeld.QM.FakeEllipticCurve.IsPullbackVia.exists_isFormalModuleVia_map_and_comp_eq coord
      k (k ⧸ Ideal.span {algebraMap 𝒪 k π}) x'.1 x'.2.Eb x'.2.gb x'.2.isPullback_Eb X' θ' hX'

  obtain ⟨κB, σ, σ', Nc, hκB1, hκB2, hσ, hσ', hρt, hρt', heq⟩ :=
    CerednikDrinfeld.QM.FakeEllipticCurve.Rigidification.exists_represents_comp_act_pow_eq_of_isRigTransport_of_act_comp_hom_comp_eq
      hrr hrN 𝒪 hdvr π hπ hcomplete hres hunr K₀ Onr Fr hOnr_complete hOnr_max hOnr_alg hOnr_closed hFr hB Λ hΛ hΛℤ coord hcoord
      A₀ X₀ hX₀ θ₀ hA₀ ι Φ hΦ hΦ4 E₀ hE₀ κ hκ n₀ β₀ hβ₀ k ψ x x' X X' θ θ' j t t'
      hta.constantCoeff_ρ ht'a.constantCoeff_ρ ht ht' T₀ m hTρ

  haveI : Nontrivial (k ⧸ pIdeal r k) := by
    have hne : pIdeal r k ≠ ⊤ := by
      intro htop
      rw [Ideal.span_singleton_eq_top, hkr.eq_zero] at htop
      exact not_isUnit_zero htop
    exact ⟨⟨0, 1, fun h01 => hne (Ideal.Quotient.zero_eq_one_iff.mp h01)⟩⟩
  have hκinj : Function.Injective κB := κB.injective
  have cβF : ∀ i, MvPowerSeries.constantCoeff (((β₀.map (residueMap (p := r) (ψ : Onr →+* k))).comp
      (Rigidified.frobSeries (p := r) (k ⧸ pIdeal r k) j)) i) = 0 :=
    fun i => by
      rw [constantCoeff_comp _ _ (constantCoeff_frobSeries _ j)]
      exact constantCoeff_map_zero _ β₀ hβ₀.1.constantCoeff i
  have hσ0 : ∀ i, MvPowerSeries.constantCoeff (σ i) = 0 := by
    intro i
    have h := hta.constantCoeff_ρ i
    rw [hρt, constantCoeff_comp _ _ cβF] at h
    apply hκinj
    rw [map_zero]
    simpa [CerednikDrinfeld.SpecialFormal.Series.map, MvPowerSeries.constantCoeff_map] using h
  have hσ'0 : ∀ i, MvPowerSeries.constantCoeff (σ' i) = 0 := by
    intro i
    have h := ht'a.constantCoeff_ρ i
    rw [hρt', constantCoeff_comp _ _ cβF] at h
    apply hκinj
    rw [map_zero]
    simpa [CerednikDrinfeld.SpecialFormal.Series.map, MvPowerSeries.constantCoeff_map] using h

  subst htX ht'X
  obtain ⟨σ₁, σ₁', hσ₁0, hσ₁'0, hσ₁, hσ₁', hTσ⟩ :=
    CerednikDrinfeld.QM.FakeEllipticCurve.Rigidification.exists_germs_represents_comp_eq_of_represents_of_act_pow_comp_eq_of_constantCoeff_eq_zero
      hrN 𝒪 π Onr Λ hΛ hΛℤ coord hcoord A₀ k hk hkr ψ x x' t.X t'.X θ θ' T₀ X₀ θ₀ hA₀ θA hθA
      (fun B'' _ _ _ h s hs => by
        haveI : IsScalarTower (Onr ⧸ Ideal.span {algebraMap 𝒪 Onr π}) (k ⧸ Ideal.span {algebraMap 𝒪 k π}) B'' :=
          IsScalarTower.of_algebraMap_eq (fun y => by rw [h]; rfl)
        exact hθAg B'' s hs) θE θE' hθE hθE' (fun B'' _ _ _ _ s hs => hθEg B'' s hs)
      (fun B'' _ _ _ _ s hs => hθEg' B'' s hs) v hv hvg κ κB hκB1 hκB2 σ σ' hσ0 hσ'0 hσ hσ' Nc (m + t'.n) (m + t.n) heq

  have hXA4 : (X₀.map (FakeEllipticCurve.Rigidification.residueLeg π ψ)).HasHeight 4 := by
    obtain ⟨-, -, hrk⟩ := hX₀
    have key : ∀ (κ' : Type) [Field κ'] (g : (k ⧸ Ideal.span {algebraMap 𝒪 k π}) →+* κ'),
        Module.finrank κ' (FormalODModule.KerAlgebra
          ((((X₀.map (FakeEllipticCurve.Rigidification.residueLeg π ψ)).act ((r : ℕ) : Zp2 r))).map g)) = r ^ 4 := by
      intro κ' _ g
      rw [FormalODModule.map_act, Series.map_map]
      exact hrk κ' (g.comp (FakeEllipticCurve.Rigidification.residueLeg π ψ))
    refine ⟨?_, Module.Projective.of_free, key⟩
    have h1 := key (k ⧸ Ideal.span {algebraMap 𝒪 k π}) (RingHom.id _)
    rw [Series.map_ringHom_id] at h1
    exact Module.finite_of_finrank_pos (by rw [h1]; exact pow_pos (Fact.out : r.Prime).pos 4)
  have hO : IsOrder Λ := hΛ.isOrder
  obtain ⟨hφ₁, hφ₁', mulφ₁, mulφ₁', actφ₁, actφ₁', compφ₁⟩ := x.2.isIsogenyPair
  obtain ⟨hφ₂, hφ₂', mulφ₂, mulφ₂', actφ₂, actφ₂', compφ₂⟩ := x'.2.isIsogenyPair
  have hrd₁ : (((r ^ x.2.d : ℕ) : ℚ) : ℍ[ℚ, a, b]) ∈ Λ := by exact_mod_cast hΛℤ ((r ^ x.2.d : ℕ) : ℤ)
  have hrd₂ : (((r ^ x'.2.d : ℕ) : ℚ) : ℍ[ℚ, a, b]) ∈ Λ := by exact_mod_cast hΛℤ ((r ^ x'.2.d : ℕ) : ℤ)
  have hφφ'₁ : x.2.φ ≫ x.2.φ' = x.2.Eb.act ⟨(((r ^ x.2.d : ℕ) : ℤ) : ℚ), hΛℤ _⟩ := by rw [(compφ₁ hrd₁).1, act_natpow_eq _ hΛℤ]
  have hφ'φ₁ : x.2.φ' ≫ x.2.φ = x.2.Ab.act ⟨(((r ^ x.2.d : ℕ) : ℤ) : ℚ), hΛℤ _⟩ := by rw [(compφ₁ hrd₁).2, act_natpow_eq _ hΛℤ]
  have hφφ'₂ : x'.2.φ ≫ x'.2.φ' = x'.2.Eb.act ⟨(((r ^ x'.2.d : ℕ) : ℤ) : ℚ), hΛℤ _⟩ := by rw [(compφ₂ hrd₂).1, act_natpow_eq _ hΛℤ]
  have hφ'φ₂ : x'.2.φ' ≫ x'.2.φ = x'.2.Ab.act ⟨(((r ^ x'.2.d : ℕ) : ℤ) : ℚ), hΛℤ _⟩ := by rw [(compφ₂ hrd₂).2, act_natpow_eq _ hΛℤ]

  have mulu := mul_of_isPullbackVia_id _ _ uA huAf huA
  have mulv := mul_of_isPullbackVia_id _ _ v hvf hv
  have actu : ∀ y : ↥Λ, x'.2.Ab.act y ≫ uA = uA ≫ x.2.Ab.act y := huA.2.2.1
  have actv : ∀ y : ↥Λ, x.2.Ab.act y ≫ v = v ≫ x'.2.Ab.act y := hv.2.2.1

  have hα : FakeEllipticCurve.IsIsogenyPair (r ^ (Nc + x.2.d + (m + t'.n))) x.2.Ab x.2.Eb
      (x.2.Ab.act ⟨(((r ^ Nc : ℕ) : ℤ) : ℚ), hΛℤ _⟩ ≫ x.2.φ' ≫ x.2.Eb.act ⟨(((r ^ (m + t'.n) : ℕ) : ℤ) : ℚ), hΛℤ _⟩) x.2.φ := by
    have h23 : (x.2.φ' ≫ x.2.Eb.act ⟨(((r ^ (m + t'.n) : ℕ) : ℤ) : ℚ), hΛℤ _⟩) ≫ x.2.Eb.f = x.2.Ab.f := by
      simp only [Category.assoc, x.2.Eb.act_over, hφ₁']
    have hover : (x.2.Ab.act ⟨(((r ^ Nc : ℕ) : ℤ) : ℚ), hΛℤ _⟩ ≫ x.2.φ' ≫ x.2.Eb.act ⟨(((r ^ (m + t'.n) : ℕ) : ℤ) : ℚ), hΛℤ _⟩) ≫ x.2.Eb.f = x.2.Ab.f := by
      simp only [Category.assoc, x.2.Eb.act_over, hφ₁', x.2.Ab.act_over]
    have m23 := mapPt_hom_comp x.2.Ab.L x.2.Eb.L x.2.Eb.L x.2.φ' hφ₁' _ (x.2.Eb.act_over _) mulφ₁'
      (fun t P Q => x.2.Eb.act_hom _ t P Q) h23
    have m123 := mapPt_hom_comp x.2.Ab.L x.2.Ab.L x.2.Eb.L _ (x.2.Ab.act_over _) _ h23
      (fun t P Q => x.2.Ab.act_hom _ t P Q) (fun t P Q => m23 t P Q) hover
    refine ⟨hover, hφ₁, fun t P Q => m123 t P Q, mulφ₁, ?_, actφ₁, ?_⟩
    · intro y
      simp only [Category.assoc]
      rw [reassoc_of% (act_comm_coe x.2.Ab hO _ _ y), reassoc_of% (actφ₁' y), act_comm_coe x.2.Eb hO _ _ y]
    · intro hd
      rw [act_natpow_eq _ hΛℤ, act_natpow_eq _ hΛℤ, Nat.add_assoc]
      constructor
      · simp only [Category.assoc]
        rw [actφ₁, reassoc_of% hφ'φ₁, act_rpow_comp, act_rpow_comp]
      · rw [reassoc_of% (actφ₁ _).symm, reassoc_of% hφφ'₁, act_rpow_comp, act_rpow_comp]

  have hα' : FakeEllipticCurve.IsIsogenyPair (r ^ (Nc + x'.2.d + (m + t.n))) x.2.Ab x'.2.Eb
      (x.2.Ab.act ⟨(((r ^ Nc : ℕ) : ℤ) : ℚ), hΛℤ _⟩ ≫ v ≫ x'.2.φ' ≫ x'.2.Eb.act ⟨(((r ^ (m + t.n) : ℕ) : ℤ) : ℚ), hΛℤ _⟩) (x'.2.φ ≫ uA) := by
    have h34 : (x'.2.φ' ≫ x'.2.Eb.act ⟨(((r ^ (m + t.n) : ℕ) : ℤ) : ℚ), hΛℤ _⟩) ≫ x'.2.Eb.f = x'.2.Ab.f := by
      simp only [Category.assoc, x'.2.Eb.act_over, hφ₂']
    have h234 : (v ≫ x'.2.φ' ≫ x'.2.Eb.act ⟨(((r ^ (m + t.n) : ℕ) : ℤ) : ℚ), hΛℤ _⟩) ≫ x'.2.Eb.f = x.2.Ab.f := by
      simp only [Category.assoc, x'.2.Eb.act_over, hφ₂', hvf]
    have hover : (x.2.Ab.act ⟨(((r ^ Nc : ℕ) : ℤ) : ℚ), hΛℤ _⟩ ≫ v ≫ x'.2.φ' ≫ x'.2.Eb.act ⟨(((r ^ (m + t.n) : ℕ) : ℤ) : ℚ), hΛℤ _⟩) ≫ x'.2.Eb.f = x.2.Ab.f := by
      simp only [Category.assoc, x'.2.Eb.act_over, hφ₂', hvf, x.2.Ab.act_over]
    have hover' : (x'.2.φ ≫ uA) ≫ x.2.Ab.f = x'.2.Eb.f := by simp only [Category.assoc, huAf, hφ₂]
    have m34 := mapPt_hom_comp x'.2.Ab.L x'.2.Eb.L x'.2.Eb.L x'.2.φ' hφ₂' _ (x'.2.Eb.act_over _) mulφ₂'
      (fun t P Q => x'.2.Eb.act_hom _ t P Q) h34
    have m234 := mapPt_hom_comp x.2.Ab.L x'.2.Ab.L x'.2.Eb.L v hvf _ h34 (fun t P Q => mulv t P Q) (fun t P Q => m34 t P Q) h234
    have m1234 := mapPt_hom_comp x.2.Ab.L x.2.Ab.L x'.2.Eb.L _ (x.2.Ab.act_over _) _ h234
      (fun t P Q => x.2.Ab.act_hom _ t P Q) (fun t P Q => m234 t P Q) hover
    have m56 := mapPt_hom_comp x'.2.Eb.L x'.2.Ab.L x.2.Ab.L x'.2.φ hφ₂ uA huAf mulφ₂ (fun t P Q => mulu t P Q) hover'
    refine ⟨hover, hover', fun t P Q => m1234 t P Q, fun t P Q => m56 t P Q, ?_, ?_, ?_⟩
    · intro y
      simp only [Category.assoc]
      rw [reassoc_of% (act_comm_coe x.2.Ab hO _ _ y), reassoc_of% (actv y), reassoc_of% (actφ₂' y),
        act_comm_coe x'.2.Eb hO _ _ y]
    · intro y
      simp only [Category.assoc]
      rw [reassoc_of% (actφ₂ y), actu y]
    · intro hd
      rw [act_natpow_eq _ hΛℤ, act_natpow_eq _ hΛℤ, Nat.add_assoc]
      constructor
      · simp only [Category.assoc]
        rw [reassoc_of% (actφ₂ _), reassoc_of% hφ'φ₂, reassoc_of% (act_rpow_comp x'.2.Ab hΛℤ r _ _),
          ← reassoc_of% (actv _), hvu, Category.comp_id, act_rpow_comp]
      · simp only [Category.assoc]
        rw [← reassoc_of% (actu _), reassoc_of% huv, reassoc_of% (actφ₂ _).symm,
          reassoc_of% hφφ'₂, act_rpow_comp, act_rpow_comp]
  obtain ⟨e, he, hαe, hemul, heact, heT⟩ :=
    CerednikDrinfeld.QM.FakeEllipticCurve.exists_iso_comp_eq_of_formalIso_comp_germ_eq_of_isIsogenyPair_of_hasHeight_four_of_isAlgClosed_of_constantCoeff_eq_zero
      hΛ1 hΛℤ coord hcoord (k ⧸ Ideal.span {algebraMap 𝒪 k π}) hkr₁
      x.2.Ab (X₀.map (FakeEllipticCurve.Rigidification.residueLeg π ψ)) θA hθA hXA4
      x.2.Eb x'.2.Eb (t.X.map (algebraMap k _)) (t'.X.map (algebraMap k _)) θE θE' hθE hθE'
      _ _ _ _ hα _ _ hα' σ₁ σ₁' hσ₁0 hσ₁'0 hσ₁ hσ₁'
      (T₀.map (algebraMap k _)) (isIso_map _ T₀ hT₀) hTσ

  exact CerednikDrinfeld.QM.FakeEllipticCurve.Rigidification.exists_isoVia_corr_inducing_of_iso_reduction_of_act_pow_comp_eq_of_isAlgClosed
    hrN 𝒪 π Onr Λ hΛ hΛℤ coord hcoord A₀ k hk hkr ψ x x' t.X t'.X θ θ' hX hX' T₀ θE θE' hθE hθE'
    (fun B'' _ _ _ _ s hs => hθEg B'' s hs) (fun B'' _ _ _ _ s hs => hθEg' B'' s hs)
    uA huA huAg v hv hvg huv hvu Nc (m + t'.n) (m + t.n) e he hαe hemul heact heT

end S_CerednikDrinfeld_QM_FakeEllipticCurve_exists_isoVia_corr_inducing_of_formalIso_of_isRigTransport_of_isAlgClosed
end P2MW
export P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_exists_isoVia_corr_inducing_of_formalIso_of_isRigTransport_of_isAlgClosed (solution)
