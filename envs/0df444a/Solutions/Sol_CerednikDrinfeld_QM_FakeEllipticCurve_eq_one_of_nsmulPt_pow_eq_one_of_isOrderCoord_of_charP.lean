-- Prove2me | solution 1 for CerednikDrinfeld.QM.FakeEllipticCurve.eq_one_of_nsmulPt_pow_eq_one_of_isOrderCoord_of_charP
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.837917+00:00
-- url     : https://prove2.me/submissions/0ac3c787-caf2-52b6-940b-fbf7785d24ab

import Mathlib
import Definitions.Def_CerednikDrinfeld_QMFormalModuleOf
import Theorems.Thm_CerednikDrinfeld_QM_IsOrderCoord_exists_eq_pow_smul_and_exists_nsmul_mem_and_exists_coprime
import Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_finite_and_natCard_torsionPoints_le_sq_of_charP_of_not_dvd
import Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_isFinite_and_flat_schemeNsmul
import Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_surjective_and_endDegree_eq_finrank_of_isFinite_of_flat
import Theorems.Thm_AlgebraicGeometry_exists_comp_eq_of_surjective_of_locallyOfFiniteType_of_isAlgClosed
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_eq_one_of_nsmulPt_pow_eq_one_of_isOrderCoord_of_charP
p2m_attr_erase "instance" "instTopologicallyFGOfFiniteType AlgebraicGeometry.Scheme.PresheafOfModules.symmetricCategory SheafOfModules.instFaithfulRingSheafPModToPMod SheafOfModules.symmetricCategory AlgebraicGeometry.Scheme.PresheafOfModules.monoidalCategory AlgebraicGeometry.Scheme.PresheafOfModules.monoidalClosed SheafOfModules.instFullRingSheafPModToPMod SheafOfModules.monoidalCategory AlgebraicGeometry.Scheme.Modules.symmetricCategory SheafOfModules.monoidalClosed SheafOfModules.instIsLocalizationPModRingSheafSheafifyFunctorPresheafW SheafOfModules.sheafifyFunctor_monoidal AlgebraicGeometry.Scheme.Modules.monoidalClosed AlgebraicGeometry.instMonoidalPresheafOfModulesModulesSheafify AlgebraicGeometry.Scheme.Modules.monoidalCategory PresheafOfModules.instMonoidalClosed PresheafOfModules.InternalHom.instModuleCarrierObjOppositeCommRingCatSubtypePiFamilyMemAddSubgroupNaturalFamilies PresheafOfModules.InternalHom.instModuleCarrierObjOppositeRingCatCompCommRingCatForget₂RingHomCarrierCarrierAbPresheaf PresheafOfModules.InternalHom.instSMulCarrierObjOppositeCommRingCatSubtypePiFamilyMemAddSubgroupNaturalFamilies AlgebraicGeometry.Scheme.Hom.opensMapFinal AlgebraicGeometry.RelPicard.RigidifiedLineBundle.setoid AlgebraicGeometry.RelPicard.RigidifiedLineBundle.instInhabited AlgebraicGeometry.OModulePresheaf.isScalarTower AlgebraicGeometry.Scheme.OrderedAffineCover.instLinearOrder AlgebraicGeometry.OModulePresheaf.module AlgebraicGeometry.Scheme.OrderedAffineCover.instFintype AlgebraicGeometry.Scheme.OrderedAffineCover.instFintypeIdx AlgebraicGeometry.OModulePresheaf.addCommGroup AlgebraicGeometry.Scheme.OrderedAffineCover.instDecidableEqIdx AlgebraicGeometry.OModulePresheaf.moduleSections TwoChartCech.Sections.M0_moduleA TwoChartCech.Sections.M1_module TwoChartCech.Cover.A01_algebra TwoChartCech.Cover.A0_algebra TwoChartCech.Cover.A1_commRing TwoChartCech.Cover.A1_algebra TwoChartCech.Sections.M01_module TwoChartCech.Sections.M0_addCommGroup TwoChartCech.Sections.M0_tower TwoChartCech.Sections.M01_addCommGroup"
p2m_attr_erase "instance" "TwoChartCech.Cover.A0_commRing TwoChartCech.Sections.M1_tower TwoChartCech.Sections.M01_moduleA TwoChartCech.Sections.M0_module TwoChartCech.Sections.M1_moduleA TwoChartCech.Sections.M1_addCommGroup TwoChartCech.Cover.A01_commRing TwoChartCech.Sections.M01_tower CoherentBaseChange.TwoTermComplex.C0_module CoherentBaseChange.TwoTermComplex.C0_addCommGroup CoherentBaseChange.TwoTermComplex.C1_module CoherentBaseChange.TwoTermComplex.C1_addCommGroup CoherentBaseChange.TwoTermComplex.C0_free CoherentBaseChange.TwoTermComplex.C1_finite CoherentBaseChange.TwoTermComplex.C0_finite CoherentBaseChange.TwoTermComplex.C1_free AlgebraicGeometry.OModulePresheaf.instSubsingletonObjZero AlgebraicGeometry.Scheme.Modules.preservesBinaryProducts_opensMap AlgebraicGeometry.Scheme.Modules.pullback_monoidal AlgebraicGeometry.Scheme.Modules.sheafify_isLocalization' AlgebraicGeometry.Scheme.Modules.preservesTerminal_opensMap AlgebraicGeometry.Scheme.Modules.pullback₀_monoidal AlgebraicGeometry.Scheme.Modules.preservesFiniteProducts_opensMap AlgebraicGeometry.Scheme.Modules.instLiftingPresheafOfModulesSheafifyPresheafWOpensCarrierCarrierCommRingCatGrothendieckTopologyObjFunctorOppositeIsSheafSheafCompPullback₀Pullback PresheafOfModules.PullbackMonoidal.pullback_monoidal PresheafOfModules.PullbackMonoidal.isIso_δ PresheafOfModules.pushforward_laxMonoidal PresheafOfModules.PullbackMonoidal.isIso_η PresheafOfModules.free_monoidal PresheafOfModules.restrictScalars_laxMonoidal PresheafOfModules.PullbackMonoidal.isIso_δ_gS PresheafOfModules.pullback_oplaxMonoidal PresheafOfModules.PullbackMonoidal.instPreservesColimitsOfSizeCompOppositeCommRingCatRingCatForget₂RingHomCarrierCarrierPb PresheafOfModules.pullback_monoidal' AlgebraicGeometry.SmoothOfRelativeDimension.fiberToSpecResidueField AlgebraicGeometry.SmoothOfRelativeDimension.pullback_snd AlgebraicGeometry.SmoothOfRelativeDimension.pullback_fst AlgebraicGeometry.SmoothOfRelativeDimension.smooth_one AlgebraicGeometry.SmoothProperCurve.isIntegral_pullback_Spec_field AlgebraicGeometry.IsProper.fiberToSpecResidueField"
p2m_attr_erase "instance" "AlgebraicCurve.CurveModel.isProper AlgebraicCurve.CurveModel.isIntegral AlgebraicCurve.CurveModel.smooth AlgebraicGeometry.Scheme.LocalRepresentabilityULift.instIsLocallyInjectiveFunUliftYonedaGluedToSheaf AlgebraicGeometry.Scheme.LocalRepresentabilityULift.instIsLocallySurjectiveFunUliftYonedaGluedToSheafOfIsLocallySurjectiveZariskiTopologyDescFunctorOppositeType AlgebraicGeometry.Scheme.LocalRepresentabilityULift.instIsOpenImmersionToGlued AlgebraicGeometry.Scheme.LocalRepresentabilityULift.instIsIsoSheafZariskiTopologyTypeUliftYonedaGluedToSheaf AlgebraicGeometry.RelPicard.instIsOpenImmersionToGlued AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.instFundamentalIdentityOfSumRamificationInertia AlgebraicCurve.Place.instIsScalarTowerResidueFieldRestrictPushforward AlgebraicCurve.Place.instAlgebraResidueFieldRestrictPushforward AlgebraicCurve.Place.instIsLocalHomRestrictInclusion AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions PresheafOfModules.ExteriorPower.instModulePresheafAb AlgebraicGeometry.RelEffCartierDiv.subsingleton_of_degree_zero AlgebraicGeometry.RelEffCartierDiv.isIso_subschemeIota_snd_of_degree_one AlgebraicGeometry.isIso_ker_graphOver_subschemeIota_snd AlgebraicGeometry.isClosedImmersion_graphOver AlgebraicGeometry.FGSubalgebra.instIsDirectedLe AlgebraicGeometry.FGSubalgebra.instQuasiSeparatedSpaceCarrierCarrierCommRingCatObjOppositeSchemeSpecDiagram AlgebraicGeometry.FGSubalgebra.instIsCofilteredOpposite AlgebraicGeometry.FGSubalgebra.instIsAffineObjOppositeSchemeSpecDiagram AlgebraicGeometry.FGSubalgebra.instNonempty AlgebraicGeometry.FGSubalgebra.instNonemptySubtypeLeSubalgebraValFG AlgebraicGeometry.FGSubalgebra.instCompactSpaceCarrierCarrierCommRingCatObjOppositeSchemeSpecDiagram AlgebraicGeometry.FGSubalgebra.instIsDirectedSubtypeLeSubalgebraValFG AlgebraicGeometry.FGSubalgebra.instIsAffineHomMapOppositeSchemeSpecDiagram AlgebraicGeometry.FGSubalgebra.instIsFiltered AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instNeg AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instSMulInt AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instAddCommGroup AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instAdd AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instSub"
p2m_attr_erase "instance" "AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instModuleCarrierObjOppositeOpensCarrierCarrierCommRingCatPresheafOpOpensTop AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instSMulCarrierObjOppositeOpensCarrierCarrierCommRingCatPresheafOpOpensTop AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instSMulNat AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instZero AlgebraicCurve.instHasLocalResidue_of_hasCanonicalLocalResidueK AlgebraicCurve.instHasCanonicalLocalResidueK_of_hasCanonicalLocalResidueKStar AlgebraicCurve.Place.kw_ffgc_finiteDimensional_adicCompletion instAlgebraSubtypeMemValuationSubring_definitions AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersIntegersCompletion ModularCurve.KwF4gRRTate.instAlgebraKAdicCompletionIntegers AlgebraicCurve.Place.kw_ffgc_continuousSMul_adicCompletionComap AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersCompletionCompletion IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions AlgebraicCurve.instHasCanonicalLocalResidueK AlgebraicCurve.Place.instAlgebra_restrictResidueField AlgebraicCurve.Place.instIsScalarTower_restrictResidueField AlgebraicCurve.instHasLocalResidue AlgebraicCurve.HasSeparableResidue.of_perfectField_of_isCurveOver AlgebraicCurve.HasSeparableResidue.of_perfectField AlgebraicCurve.Place.instIsLocalHom_restrictSubringHom AlgebraicCurve.instHasCanonicalLocalResidueKStar ModularCurve.KwNo6Pin.isLocalRing_completion SheafOfModules.isIso_ihomModelToIhom AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instDecidableEqIdx AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instFintype AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instLinearOrder AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instFintypeIdx AlgebraicGeometry.OModulePresheaf.Leray.relAltC_scalarTower AlgebraicGeometry.OModulePresheaf.Leray.ker_relAltd_modΓ AlgebraicGeometry.OModulePresheaf.Leray.relAltC_modΓ AlgebraicGeometry.OModulePresheaf.Leray.biC_abGrp AlgebraicGeometry.OModulePresheaf.Leray.relAltH_modΓ AlgebraicGeometry.OModulePresheaf.Leray.ker_relAltd_smul AlgebraicGeometry.OModulePresheaf.Leray.relAltH_scalarTower AlgebraicGeometry.OModulePresheaf.Leray.relAltH_smul"
p2m_attr_erase "instance" "AlgebraicGeometry.OModulePresheaf.Leray.biC_module DoubleComplex.instModuleE₂I DoubleComplex.Bounded.modR DoubleComplex.instModuleE₂II DoubleComplex.instAddCommGroupE₂II DoubleComplex.Bounded.abGrp DoubleComplex.instAddCommGroupE₂I AlgebraicGeometry.ChowDatum.hι_closed AlgebraicGeometry.ChowDatumProj.hιN_closed AlgebraicGeometry.ChowDatumProj.hp_proper AlgebraicGeometry.ChowDatum.hp_isoU AlgebraicGeometry.ChowDatum.hp_proper AlgebraicGeometry.ProjSpace.algebraAway AlgebraicGeometry.ProjSpace.instIsProperProdOverπ AlgebraicGeometry.ChowDatumProj.hp_isoU AlgebraicGeometry.ProjSpace.isProper_π AlgebraicGeometry.ProjSpace.finiteType_mvPolynomial ProjSpaceCech.GradedModule.H.module ProjSpaceCech.GradedModule.H.addCommGroup ProjSpaceCech.GradedModule.sec.instAdd ProjSpaceCech.GradedModule.sec.instNeg ProjSpaceCech.GradedModule.acg ProjSpaceCech.GradedModule.Frac.setoid ProjSpaceCech.GradedModule.modR ProjSpaceCech.GradedModule.sec.instModule ProjSpaceCech.GradedModule.sec.instAddCommGroup ProjSpaceCech.GradedModule.sec.instZero ProjSpaceCech.GradedModule.Presentation.fJ ProjSpaceCech.GradedModule.sec.instSMul ProjSpaceCech.Twist.H.module ProjSpaceCech.Idx.instFintype ProjSpaceCech.Twist.H.addCommGroup ProjSpaceCech.Idx.instDecidableEq ProjSpaceCech.Twist.Mon.instDecidableEq ProjSpaceCech.Twist.cochain.instAddCommGroup ProjSpaceCech.Twist.cochain.instModule AlgebraicGeometry.FGSubalgebra.tensorStage_directedSystem AlgebraicGeometry.RelEffCartierDiv.isClosedImmersion_subschemeι_resProdMap AlgebraicGeometry.RelEffCartierDiv.isOpenImmersion_resProdMap AlgebraicCurve.CurveModel.locallyOfFiniteType_gluedToBase"
p2m_attr_erase "instance" "AlgebraicCurve.CurveModel.isFractionRing_overlap AlgebraicCurve.CurveModel.isLocallyNoetherian_glued AlgebraicCurve.CurveModel.jacobsonSpace_glued AlgebraicCurve.CurveModel.isOpenImmersion_ι₀ AlgebraicCurve.CurveModel.isIntegral_glued AlgebraicCurve.CurveModel.quasiSeparated_gluedToBase AlgebraicCurve.CurveModel.compactSpace_glued AlgebraicCurve.CurveModel.isIntegral_adjoin_chartRing AlgebraicCurve.CurveModel.isFractionRing_overlap_functionField AlgebraicCurve.CurveModel.isProper_gluedToBase AlgebraicCurve.CurveModel.isOpenImmersion_ιU AlgebraicCurve.CurveModel.isOpenImmersion_f₀ AlgebraicCurve.CurveModel.isOpenImmersion_fInf AlgebraicCurve.CurveModel.isOpenImmersion_ιInf AlgebraicCurve.CurveModel.algebra_overlap_functionField AlgebraicCurve.CurveModel.quasiCompact_gluedToBase AlgebraicCurve.CurveModel.algebraAdjoin AlgebraicCurve.CurveModel.isDedekindDomain_chartRing AlgebraicCurve.CurveModel.isIntegralClosure AlgebraicCurve.CurveModel.finite_chartRing AlgebraicCurve.CurveModel.centre_isPrime AlgebraicCurve.CurveModel.isFractionRing_chartRing AlgebraicCurve.CurveModel.finiteType_chartRing AlgebraicCurve.CurveModel.isNoetherianRing_chartRing AlgebraicCurve.CurveModel.isScalarTower_base_adjoin AlgebraicCurve.CurveModel.isScalarTower_adjoin AlgebraicCurve.CurveModel.chartRing_finitePresentation AlgebraicGeometry.ProjSpace.twistObj.addCommGroup AlgebraicGeometry.ProjSpace.twistFam.module AlgebraicGeometry.ProjSpace.twistObj.module AlgebraicGeometry.ProjSpace.twistObj.moduleSections AlgebraicGeometry.ProjSpace.twistFam.addCommGroup kmfloorsGlue_int_three_isPrime kmfloorsGlue_int_bot_isPrime"
p2m_attr_erase "simp" "CerednikDrinfeld.QM.FakeEllipticCurve.ExtraLevel.mk.injEq CerednikDrinfeld.QM.FakeEllipticCurve.ExtraLevel.mk.sizeOf_spec AlgebraicGeometry.Scheme.relFrobenius_snd AlgebraicGeometry.Scheme.frobenius_preimage AlgebraicGeometry.Scheme.relFrobenius_fst AlgebraicGeometry.Scheme.relFrobenius_snd_assoc AlgebraicGeometry.Scheme.relFrobenius_fst_assoc AlgebraicGeometry.powCharRingHom_apply AlgebraicGeometry.Scheme.frobenius_base GoodReductionJacobian.RelativeGroupLaw.baseChangePointToBase_ofBase GoodReductionJacobian.RelativeGroupLaw.baseChangePointToBase_coe GoodReductionJacobian.RelativeGroupLaw.baseChangePointOfBase_coe GoodReductionJacobian.RelativeGroupLaw.baseChange_inv GoodReductionJacobian.RelativeGroupLaw.baseChangePointOfBase_toBase GoodReductionJacobian.RelativeGroupLaw.baseChange_mul GoodReductionJacobian.RelativeGroupLaw.baseChange_one NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_fst NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_snd NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_fst NeronSpecialFibreInfra.neronEndRestrictEquiv_apply NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_fst_assoc NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_snd NeronSpecialFibreInfra.neronEndExtension_genericFibreRestrict NeronSpecialFibreInfra.specClosedFibreInclusion_eq NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_fst_assoc NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_snd_assoc NeronSpecialFibreInfra.genericFibreRestrict_neronEndExtension NeronSpecialFibreInfra.homOverId_coe NeronSpecialFibreInfra.homOverComp_coe NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_snd_assoc GoodReductionJacobian.RelativeGroupLaw.fibre_inv GoodReductionJacobian.RelativeGroupLaw.fibrePointToBase_coe GoodReductionJacobian.RelativeGroupLaw.fibrePointOfBase_toBase GoodReductionJacobian.RelativeGroupLaw.fibre_mul GoodReductionJacobian.RelativeGroupLaw.fibrePointToBase_ofBase GoodReductionJacobian.RelativeGroupLaw.fibre_one GoodReductionJacobian.RelativeGroupLaw.fibrePointOfBase_coe AlgebraicGeometry.schemeFibreEndo_snd AlgebraicGeometry.schemeFibreEndo_fst RegularLocalRingQuotientAscent.dualNumberFst_apply"
p2m_attr_erase "simp" "GoodReductionJacobian.relativeGroupLawOfGrpObj_inv GoodReductionJacobian.relativeGroupLawOfGrpObj_mul GoodReductionJacobian.overHomEquivSchemeHomOver_apply_coe GoodReductionJacobian.relativeGroupLawOfGrpObj_one GoodReductionJacobian.overHomEquivSchemeHomOver_symm_apply_left SheafOfModules.tensorUnit_eq AlgebraicGeometry.Scheme.Modules.tensorUnit_eq PresheafOfModules.InternalHom.presheaf_map_apply PresheafOfModules.InternalHom.curryFamily_app PresheafOfModules.InternalHom.add_app PresheafOfModules.InternalHom.smul_app PresheafOfModules.InternalHom.zero_app PresheafOfModules.ihomObj_map_val PresheafOfModules.ihomFunctor_map PresheafOfModules.InternalHom.restrict_app PresheafOfModules.InternalHom.postcomp_app PresheafOfModules.InternalHom.neg_app PresheafOfModules.curry'_app_val PresheafOfModules.InternalHom.presheaf_obj PresheafOfModules.ihomFunctor_obj PresheafOfModules.ihomObj_obj PresheafOfModules.InternalHom.sub_app PresheafOfModules.ihomMap_app_val AlgebraicGeometry.Scheme.Modules.tensorPow_zero AlgebraicGeometry.Scheme.Modules.tensorPow_succ AlgebraicGeometry.RelPicard.RigidifiedLineBundle.mk.sizeOf_spec AlgebraicGeometry.RelPicard.RigidifiedLineBundle.mk.injEq AlgebraicGeometry.Scheme.OrderedAffineCover.mk.injEq AlgebraicGeometry.OModulePresheaf.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCover.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.mk.injEq AlgebraicGeometry.Scheme.TwoAffineOpenCover.mk.injEq AlgebraicGeometry.Scheme.TwoAffineOpenCover.mk.sizeOf_spec AlgebraicGeometry.Scheme.TwoAffineOpenCover.pullback_U1 AlgebraicGeometry.Scheme.TwoAffineOpenCover.pullback_U0 TwoChartCech.Sections.mk.injEq TwoChartCech.Cover.mk.injEq TwoChartCech.GrothendieckComplex.mk.injEq TwoChartCech.Sections.mk.sizeOf_spec TwoChartCech.Cover.mk.sizeOf_spec"
p2m_attr_erase "simp" "TwoChartCech.Cover.lineBundle_r0_apply TwoChartCech.GrothendieckComplex.mk.sizeOf_spec TwoChartCech.Cover.lineBundle_r1_apply CoherentBaseChange.TwoTermComplex.mk.sizeOf_spec CoherentBaseChange.TwoTermComplex.mk.injEq AlgebraicGeometry.OModulePresheaf.prod_obj AlgebraicGeometry.OModulePresheaf.restrOpen_obj AlgebraicGeometry.OModulePresheaf.DevissageStep.mk.injEq AlgebraicGeometry.OModulePresheaf.pushforward_obj AlgebraicGeometry.OModulePresheaf.im_obj AlgebraicGeometry.OModulePresheaf.pow_obj AlgebraicGeometry.OModulePresheaf.fstHom_app AlgebraicGeometry.OModulePresheaf.ker_obj AlgebraicGeometry.OModulePresheaf.coker_obj AlgebraicGeometry.OModulePresheaf.DevissageStep.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCover.preimage_U AlgebraicGeometry.OModulePresheaf.sndHom_app AlgebraicGeometry.OModulePresheaf.Hom.mk.injEq AlgebraicGeometry.OModulePresheaf.Hom.id_app AlgebraicGeometry.OModulePresheaf.AffHom.appSections_apply AlgebraicGeometry.OModulePresheaf.AffHom.comp_app AlgebraicGeometry.OModulePresheaf.AffSES.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.AffHom.kerMap_coe AlgebraicGeometry.OModulePresheaf.AffHom.id_app AlgebraicGeometry.OModulePresheaf.Hom.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.Hom.toAffHom_app AlgebraicGeometry.OModulePresheaf.SES.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.AffHom.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.Hom.comp_app AlgebraicGeometry.OModulePresheaf.SES.mk.injEq AlgebraicGeometry.OModulePresheaf.AffHom.mk.injEq AlgebraicGeometry.OModulePresheaf.Hom.appSections_apply AlgebraicGeometry.OModulePresheaf.AffSES.mk.injEq PresheafOfModules.freeεIso_hom_app PresheafOfModules.freeμIso_hom_app AlgebraicGeometry.RelPicard.RepresentsRelSubPic.mk.injEq AlgebraicGeometry.RelPicard.SubPicCondition.mk.injEq AlgebraicGeometry.RelPicard.SubPicCondition.mk.sizeOf_spec AlgebraicGeometry.RelPicard.RepresentsRelSubPic.mk.sizeOf_spec AlgebraicGeometry.SmoothProperCurve.sectionBaseChange_coe_snd"
p2m_attr_erase "simp" "AlgebraicGeometry.SmoothProperCurve.sectionBaseChange_coe_fst AlgebraicCurve.CurveModel.mk.injEq AlgebraicCurve.CurveModel.mk.sizeOf_spec AlgebraicCurve.mulAdele_apply AlgebraicCurve.residuePairing_apply_coe AlgebraicCurve.mem_adeleBdd AlgebraicCurve.weilSmul_one AlgebraicCurve.diagonalHom_apply AlgebraicCurve.weilSmul_apply AlgebraicCurve.adeleSpaceMul_coe AlgebraicCurve.mulAdele_one AlgebraicGeometry.SmoothProperCurve.FiniteMapData.twoAffineOpenCover_U1 AlgebraicGeometry.SmoothProperCurve.FiniteMapData.mk.injEq AlgebraicGeometry.SmoothProperCurve.FiniteMapData.mk.sizeOf_spec AlgebraicGeometry.SmoothProperCurve.FiniteMapData.twoAffineOpenCover_U0 AlgebraicGeometry.RelPicard.SubPicCondition.onClasses_mk AlgebraicGeometry.RelPicard.relSubPicPresheaf_map_coe CategoryTheory.Functor.OverTotal.ofFibre_fst CategoryTheory.Functor.overTotal_map_fst AlgebraicGeometry.Scheme.LocalRepresentabilityULift.glueData_J AlgebraicGeometry.Scheme.LocalRepresentabilityULift.uliftYoneda_toGlued_uliftYonedaGluedToSheaf AlgebraicGeometry.Scheme.LocalRepresentabilityULift.glueData_t' AlgebraicGeometry.Scheme.LocalRepresentabilityULift.uliftYoneda_toGlued_uliftYonedaGluedToSheaf_assoc AlgebraicGeometry.Scheme.LocalRepresentabilityULift.uliftYonedaGluedToSheaf_app_toGlued AlgebraicGeometry.Scheme.LocalRepresentabilityULift.glueData_openCover_map AlgebraicGeometry.Scheme.LocalRepresentabilityULift.uliftYonedaGluedToSheaf_app_comp AlgebraicGeometry.Scheme.LocalRepresentabilityULift.glueData_V AlgebraicGeometry.Scheme.LocalRepresentabilityULift.glueData_t AlgebraicGeometry.Scheme.LocalRepresentabilityULift.glueData_U AlgebraicGeometry.Scheme.LocalRepresentabilityULift.glueData_f AlgebraicGeometry.RelPicard.designationOfRepresentableBy_P AlgebraicGeometry.RelPicard.designationOfRepresentableBy_toBase AlgebraicGeometry.RelPicard.rigSection_snd AlgebraicGeometry.RelPicard.RigidifiedLineBundle.ofInvertible_L AlgebraicGeometry.RelPicard.rigSection_snd_assoc AlgebraicGeometry.RelPicard.SubPicGroupCondition.mk.injEq AlgebraicGeometry.RelPicard.SubPicGroupCondition.mk.sizeOf_spec AlgebraicCurve.coe_cechH0Equiv_apply AlgebraicCurve.cechH1ToH1_mk AlgebraicCurve.lSpaceOn_univ"
p2m_attr_erase "simp" "AlgebraicCurve.lSpaceOn_empty AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.Divisor.mapRestrict_single AlgebraicCurve.Divisor.pushforward_single AlgebraicCurve.Place.coe_restrictInclusion AlgebraicCurve.Place.mem_fiber AlgebraicCurve.Place.restrict_toValuationSubring AlgebraicCurve.Divisor.degree_pushforward AlgebraicCurve.Place.restrictResidueMap_residue AlgebraicCurve.Pic0.coe_pushforwardDegZeroHom AlgebraicCurve.Pic0.coe_pullbackDegZeroHom AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Divisor.degree_pushforwardAlong AlgebraicCurve.Pic0.coe_degZeroCorrespondence AlgebraicCurve.Place.mem_fiberAlong AlgebraicCurve.coe_frobeniusPushforwardDegZero"
p2m_attr_erase "simp" "AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.jqNModC_one ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one AlgebraicCurve.Place.differentialCoeff_zero AlgebraicCurve.Place.differentialCoeff_dCoord AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.injEq AlgebraicCurve.TranscendenceTower.mk.injEq AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec AlgebraicCurve.PoleDivisorPackage.mk.injEq AlgebraicGeometry.RelPicard.thetaBundle_def AlgebraicGeometry.RelPicard.picardBundle_def AlgebraicGeometry.RelEffCartierDiv.toRelEffDivisor_ofRelEffDivisor AlgebraicGeometry.RelEffCartierDiv.toRelEffDivisor_I AlgebraicGeometry.mapOnProdOver_fst_assoc AlgebraicGeometry.RelEffCartierDiv.mk.sizeOf_spec AlgebraicGeometry.RelEffCartierDiv.mk.injEq AlgebraicGeometry.mapOnProdOver_snd AlgebraicGeometry.mapOnProdOver_fst AlgebraicGeometry.mapOnProdOver_snd_assoc AlgebraicGeometry.mapOnProdOver_id AlgebraicCurve.RelEffDivisor.mk.sizeOf_spec AlgebraicCurve.mapOnProd_fst AlgebraicCurve.mapOnProd_fst_assoc AlgebraicCurve.mapOnProd_snd AlgebraicCurve.UnivDivisorPack.mk.injEq"
p2m_attr_erase "simp" "AlgebraicCurve.RelEffDivisor.mk.injEq AlgebraicCurve.UnivDivisorPack.mk.sizeOf_spec AlgebraicCurve.mapOnProd_snd_assoc AlgebraicGeometry.Scheme.Modules.exteriorPower_obj PresheafOfModules.exteriorPower_map_ιMulti PresheafOfModules.ExteriorPower.appₗ_apply AlgebraicGeometry.prodKerGraph_one AlgebraicGeometry.fibrePowOver.proj_comp AlgebraicGeometry.prodKerGraph_zero AlgebraicGeometry.RelEffCartierDiv.empty_I AlgebraicGeometry.fibrePowOver.proj_comp_assoc AlgebraicGeometry.graphOver_fst_assoc AlgebraicGeometry.RelEffCartierDiv.toPoint_comp AlgebraicGeometry.RelEffCartierDiv.toPoint_comp_assoc AlgebraicGeometry.graphOver_fst AlgebraicGeometry.RelEffCartierDiv.ofPoint_I AlgebraicGeometry.graphOver_snd AlgebraicGeometry.graphOver_snd_assoc AlgebraicCurve.SymmetricPowerPackage.mk.sizeOf_spec AlgebraicCurve.SymmetricPowerPackage.mk.injEq AlgebraicGeometry.FGSubalgebra.cocone_ι_app_apply AlgebraicGeometry.RelPicard.fst_toProdSpec AlgebraicGeometry.RelPicard.toProdSpec_fst_assoc AlgebraicGeometry.RelPicard.pointsSubBasepointModule_cons AlgebraicGeometry.RelPicard.pointsSubBasepointModule_nil AlgebraicGeometry.RelPicard.fst_toProdSpec_assoc AlgebraicGeometry.RelPicard.toProdSpec_fst AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.sub_app AlgebraicGeometry.Scheme.IdealSheafData.sres_sresTop AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.add_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.mk.sizeOf_spec AlgebraicGeometry.Scheme.IdealSheafData.coe_resLE AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.smul_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.coe_ofLE_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.ideal_range AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.zero_app AlgebraicGeometry.Scheme.IdealSheafData.sres_sres AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.comp_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.neg_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.id_app"
p2m_attr_erase "simp" "AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.coe_mulRight_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.nsmul_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.mk.injEq AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.zsmul_app AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.sizeOf_spec AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.injEq AlgebraicCurve.adeleSingle_coe AlgebraicCurve.kaehlerResidueTermKFam_apply AlgebraicCurve.Place.LocalResidueData.mk.injEq AlgebraicCurve.Place.LocalResidueData.mk.sizeOf_spec AlgebraicCurve.Place.kw_ffgc_adicCompletionComapIntegers_coe AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.sizeOf_spec AlgebraicCurve.Place.mem_simplePoleSubmodule AlgebraicCurve.Place.coe_uniformizerSubring ModularCurve.Lg37.Lg37CompletionSection.mk.injEq AlgebraicCurve.Place.CoefficientFieldSection.mk.injEq AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.injEq ModularCurve.Lg37.Lg37CompletionSection.mk.sizeOf_spec AlgebraicCurve.Place.CoefficientFieldSection.mk.sizeOf_spec AlgebraicCurve.Place.poleSubmodule_one AlgebraicCurve.Place.mem_poleSubmodule AlgebraicGeometry.Scheme.Modules.toUnitSection_ofUnitSection AlgebraicGeometry.Scheme.Modules.pullbackSection_def AlgebraicGeometry.Scheme.Modules.ofUnitSection_toUnitSection PresheafOfModules.InternalHom.IsSheafAux.appAt_toPresheafHom SheafOfModules.ihomSectionsEquivFamily_unit AlgebraicGeometry.Scheme.Modules.restrictHomEquivFamily_apply SheafOfModules.ihomEval_unit_app AlgebraicGeometry.Scheme.Modules.ihomEval_zero_right AlgebraicGeometry.Scheme.Modules.ihomEval_zero_left AlgebraicGeometry.Scheme.Modules.homOfFamily_app_apply SheafOfModules.unit_ihomSectionsEquivFamily AlgebraicGeometry.Scheme.Modules.familyOfHom_app AlgebraicGeometry.Scheme.Modules.restrictUnitIso_hom_app_apply AlgebraicGeometry.Scheme.Modules.restrictUnitIso_inv_app_apply AlgebraicGeometry.Scheme.Modules.restrictHomOfFamily_app_apply AlgebraicGeometry.Scheme.Modules.restrictHomEquivFamily_symm_apply AlgebraicGeometry.Scheme.Modules.tensorSections_zero_right AlgebraicGeometry.Scheme.Modules.map_unitSection AlgebraicGeometry.Scheme.Modules.tensorSectionsBilin_apply"
p2m_attr_erase "simp" "AlgebraicGeometry.Scheme.Modules.tensorPowSection_zero AlgebraicGeometry.Scheme.Modules.tensorSections_zero_left AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_neg AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_zero AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_sub AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_add AlgebraicGeometry.Scheme.OrderedAffineCover.toCoverOf_U AlgebraicGeometry.Scheme.OrderedAffineCoverOf.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCoverOf.mk.injEq AlgebraicGeometry.Scheme.OrderedAffineCover.restrict_U AlgebraicGeometry.OModulePresheaf.Leray.restrictToPreimage_U DoubleComplex.Bounded.mk.injEq DoubleComplex.Bounded.mk.sizeOf_spec DoubleComplex.Convergence.mk.injEq DoubleComplex.Convergence.mk.sizeOf_spec DoubleComplex.SubQuot.mk.sizeOf_spec DoubleComplex.SubQuot.mk.injEq AlgebraicGeometry.ChowDatumProj.mk.sizeOf_spec AlgebraicGeometry.ChowDatum.mk.sizeOf_spec AlgebraicGeometry.ChowDatumProj.mk.injEq AlgebraicGeometry.ChowDatum.mk.injEq ProjSpaceCech.GradedModule.mk.injEq ProjSpaceCech.GradedModule.mk.sizeOf_spec ProjSpaceCech.GradedModule.Frac.mk.sizeOf_spec ProjSpaceCech.GradedModule.Presentation.mk.injEq ProjSpaceCech.GradedModule.Frac.mk.injEq ProjSpaceCech.GradedModule.Presentation.mk.sizeOf_spec ProjSpaceCech.GradedModule.Hom.shift_toLinearMap ProjSpaceCech.GradedModule.Hom.mk.sizeOf_spec ProjSpaceCech.GradedModule.Hom.mk.injEq TwoChartCech.Mumford.dK_apply TwoChartCech.Mumford.ι0_apply TwoChartCech.Mumford.ι1_apply TwoChartCech.KerCoprod.dK_apply TwoChartCech.KerCoprod.ι1_apply TwoChartCech.KerCoprod.ι0_apply AlgebraicGeometry.tilde.functorCompPullbackSpecIso_app AlgebraicGeometry.RelPicard.algEquivZeroGroupCut_toSubPicCondition AlgebraicGeometry.RelPicard.LFP.stageHom_val AlgebraicGeometry.RelPicard.BaseChange.relSubPicPresheafRestrictIso_hom_app_coe"
p2m_attr_erase "simp" "AlgebraicGeometry.RelPicard.BaseChange.relSubPicPresheafRestrictIso_inv_app_coe AlgebraicGeometry.RelPicard.BaseChange.restrict_P AlgebraicGeometry.RelEffCartierDiv.IsUniversal.lift_comp AlgebraicGeometry.RelEffCartierDiv.functor_map_fst AlgebraicGeometry.RelEffCartierDiv.IsUniversal.homEquiv_apply AlgebraicGeometry.RelEffCartierDiv.IsUniversal.lift_pullbackAlong AlgebraicGeometry.RelEffCartierDiv.IsUniversal.homEquiv_symm_apply AlgebraicGeometry.RelEffCartierDiv.IsUniversal.lift_comp_assoc AlgebraicGeometry.RelEffCartierDiv.supportedIn_top AlgebraicGeometry.RelEffCartierDiv.mem_supportedIn_iff AlgebraicGeometry.RelEffCartierDiv.supportedIn_top_eq AlgebraicGeometry.RelEffCartierDiv.restrictAlong_extendAlong AlgebraicGeometry.RelEffCartierDiv.extendAlong_I AlgebraicGeometry.RelEffCartierDiv.resProdMap_snd AlgebraicGeometry.RelEffCartierDiv.restrictAlong_I AlgebraicGeometry.RelEffCartierDiv.extendAlong_restrictAlong AlgebraicGeometry.RelEffCartierDiv.resProdMap_fst_assoc AlgebraicGeometry.RelEffCartierDiv.resProdMap_snd_assoc AlgebraicGeometry.RelEffCartierDiv.resProdMap_fst CoherentBaseChange.FibreH0Family.mk.sizeOf_spec CoherentBaseChange.FibreH0Family.mk.injEq AlgebraicGeometry.Scheme.Modules.ProjPresentation.mk.injEq AlgebraicGeometry.Scheme.Modules.ProjPresentation.mk.sizeOf_spec AlgebraicCurve.CurveModel.coe_gInf AlgebraicCurve.CurveModel.coe_tInvChart AlgebraicCurve.CurveModel.ιInf_gluedToBase_assoc AlgebraicCurve.CurveModel.ιInf_gluedToBase AlgebraicCurve.CurveModel.primeOfι₀_asIdeal AlgebraicCurve.CurveModel.coe_tChart AlgebraicCurve.CurveModel.ι₀_gluedToBase_assoc AlgebraicCurve.CurveModel.primeOfιInf_asIdeal AlgebraicCurve.CurveModel.ι₀_gluedToBase AlgebraicCurve.CurveModel.coe_tma AlgebraicCurve.CurveModel.coe_primeEquivChartPlaces AlgebraicGeometry.ProjSpace.twistObj.mk.injEq AlgebraicGeometry.ProjSpace.twistObj.zero_val AlgebraicGeometry.ProjSpace.twistObj.add_val AlgebraicGeometry.ProjSpace.twist_res_val AlgebraicGeometry.ProjSpace.twist_smul_val AlgebraicGeometry.ProjSpace.twistGradeToObj_val"
p2m_attr_erase "simp" "AlgebraicGeometry.ProjSpace.twistObj.smul_val AlgebraicGeometry.ProjSpace.twistGradeEquiv_apply_val AlgebraicGeometry.ProjSpace.twistObj.mk.sizeOf_spec"

set_option autoImplicit false

open CerednikDrinfeld CerednikDrinfeld.QM
open scoped Quaternion

namespace R4X5Heart

variable {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} {q : ℕ} [Fact q.Prime]

noncomputable abbrev qPow (q : ℕ) [Fact q.Prime] (k : ℕ) : Ideal (Zp2 q) := Ideal.span {((q : ℕ) : Zp2 q) ^ k}

theorem natCast_pow_mem_qPow (k : ℕ) : ((q : ℕ) : Zp2 q) ^ k ∈ qPow q k := Ideal.subset_span rfl

theorem qPow_mono {k l : ℕ} (h : k ≤ l) : qPow q l ≤ qPow q k := by
  refine Ideal.span_singleton_le_span_singleton.mpr ?_
  exact pow_dvd_pow _ h

theorem frobenius_mem_qPow {k : ℕ} {x : Zp2 q} (hx : x ∈ qPow q k) : WittVector.frobenius x ∈ qPow q k := by
  rcases Ideal.mem_span_singleton'.mp hx with ⟨c, rfl⟩
  rw [map_mul, map_pow, map_natCast]
  exact Ideal.mem_span_singleton'.mpr ⟨_, rfl⟩

theorem natCast_mul_mem_qPow_succ {k : ℕ} {x : Zp2 q} (hx : x ∈ qPow q k) :
    ((q : ℕ) : Zp2 q) * x ∈ qPow q (k + 1) := by
  rcases Ideal.mem_span_singleton'.mp hx with ⟨c, rfl⟩
  refine Ideal.mem_span_singleton'.mpr ⟨c, ?_⟩
  ring

private noncomputable def _root_.R4X5Heart.tmul (v w : Zp2 q × Zp2 q) : Zp2 q × Zp2 q :=
  (v.1 * w.1 + ((q : ℕ) : Zp2 q) * (v.2 * WittVector.frobenius w.2), v.1 * w.2 + v.2 * WittVector.frobenius w.1)

p2m_export "R4X5Heart" "tmul"

def Cong (k : ℕ) (v w : Zp2 q × Zp2 q) : Prop := v.1 - w.1 ∈ qPow q k ∧ v.2 - w.2 ∈ qPow q k

theorem Cong.refl (k : ℕ) (v : Zp2 q × Zp2 q) : Cong k v v := ⟨by simp, by simp⟩

theorem Cong.symm {k : ℕ} {v w : Zp2 q × Zp2 q} (h : Cong k v w) : Cong k w v :=
  ⟨by rw [← neg_sub]; exact (qPow q k).neg_mem h.1, by rw [← neg_sub]; exact (qPow q k).neg_mem h.2⟩

theorem Cong.trans {k : ℕ} {u v w : Zp2 q × Zp2 q} (h : Cong k u v) (h' : Cong k v w) : Cong k u w :=
  ⟨by have := Ideal.add_mem _ h.1 h'.1; rwa [sub_add_sub_cancel] at this,
   by have := Ideal.add_mem _ h.2 h'.2; rwa [sub_add_sub_cancel] at this⟩

theorem Cong.add {k : ℕ} {v v' w w' : Zp2 q × Zp2 q} (h : Cong k v v') (h' : Cong k w w') :
    Cong k (v + w) (v' + w') :=
  ⟨by have := Ideal.add_mem _ h.1 h'.1; rwa [Prod.fst_add, Prod.fst_add, add_sub_add_comm],
   by have := Ideal.add_mem _ h.2 h'.2; rwa [Prod.snd_add, Prod.snd_add, add_sub_add_comm]⟩

theorem Cong.sub {k : ℕ} {v v' w w' : Zp2 q × Zp2 q} (h : Cong k v v') (h' : Cong k w w') :
    Cong k (v - w) (v' - w') :=
  ⟨by have := Ideal.sub_mem _ h.1 h'.1; rwa [Prod.fst_sub, Prod.fst_sub, sub_sub_sub_comm],
   by have := Ideal.sub_mem _ h.2 h'.2; rwa [Prod.snd_sub, Prod.snd_sub, sub_sub_sub_comm]⟩

theorem Cong.nsmul {k : ℕ} (n : ℕ) {v w : Zp2 q × Zp2 q} (h : Cong k v w) : Cong k (n • v) (n • w) := by
  refine ⟨?_, ?_⟩
  · rw [Prod.smul_fst, Prod.smul_fst, ← nsmul_sub, nsmul_eq_mul]
    exact Ideal.mul_mem_left _ _ h.1
  · rw [Prod.smul_snd, Prod.smul_snd, ← nsmul_sub, nsmul_eq_mul]
    exact Ideal.mul_mem_left _ _ h.2

theorem Cong.of_le {k l : ℕ} (hkl : k ≤ l) {v w : Zp2 q × Zp2 q} (h : Cong l v w) : Cong k v w :=
  ⟨qPow_mono hkl h.1, qPow_mono hkl h.2⟩

theorem Cong.tmul {k : ℕ} {v v' w w' : Zp2 q × Zp2 q} (h : Cong k v v') (h' : Cong k w w') :
    Cong k (tmul v w) (tmul v' w') := by
  obtain ⟨h1, h2⟩ := h
  obtain ⟨h1', h2'⟩ := h'
  have hf2 := frobenius_mem_qPow h2'
  have hf1 := frobenius_mem_qPow h1'
  rw [map_sub] at hf2 hf1
  refine ⟨?_, ?_⟩
  · show (v.1 * w.1 + (q : Zp2 q) * (v.2 * WittVector.frobenius w.2)) -
        (v'.1 * w'.1 + (q : Zp2 q) * (v'.2 * WittVector.frobenius w'.2)) ∈ qPow q k
    have e : (v.1 * w.1 + (q : Zp2 q) * (v.2 * WittVector.frobenius w.2)) -
        (v'.1 * w'.1 + (q : Zp2 q) * (v'.2 * WittVector.frobenius w'.2)) =
        (v.1 - v'.1) * w.1 + v'.1 * (w.1 - w'.1) +
          (q : Zp2 q) * ((v.2 - v'.2) * WittVector.frobenius w.2 +
            v'.2 * (WittVector.frobenius w.2 - WittVector.frobenius w'.2)) := by ring
    rw [e]
    refine Ideal.add_mem _ (Ideal.add_mem _ (Ideal.mul_mem_right _ _ h1) (Ideal.mul_mem_left _ _ h1'))
      (Ideal.mul_mem_left _ _ (Ideal.add_mem _ (Ideal.mul_mem_right _ _ h2) (Ideal.mul_mem_left _ _ hf2)))
  · show (v.1 * w.2 + v.2 * WittVector.frobenius w.1) - (v'.1 * w'.2 + v'.2 * WittVector.frobenius w'.1) ∈ qPow q k
    have e : (v.1 * w.2 + v.2 * WittVector.frobenius w.1) - (v'.1 * w'.2 + v'.2 * WittVector.frobenius w'.1) =
        (v.1 - v'.1) * w.2 + v'.1 * (w.2 - w'.2) +
          ((v.2 - v'.2) * WittVector.frobenius w.1 + v'.2 * (WittVector.frobenius w.1 - WittVector.frobenius w'.1)) := by
      ring
    rw [e]
    exact Ideal.add_mem _ (Ideal.add_mem _ (Ideal.mul_mem_right _ _ h1) (Ideal.mul_mem_left _ _ h2'))
      (Ideal.add_mem _ (Ideal.mul_mem_right _ _ h2) (Ideal.mul_mem_left _ _ hf1))

structure LatAct (Λ : Submodule ℤ ℍ[ℚ, a, b]) (G : Type*) [AddCommGroup G] where

  ρ : ↥Λ → G →+ G

  map_add : ∀ m m' : ↥Λ, ρ (m + m') = ρ m + ρ m'

  map_mul : ∀ (m m' : ↥Λ) (h : (m : ℍ[ℚ, a, b]) * (m' : ℍ[ℚ, a, b]) ∈ Λ),
    ρ ⟨(m : ℍ[ℚ, a, b]) * (m' : ℍ[ℚ, a, b]), h⟩ = (ρ m).comp (ρ m')

namespace LatAct

variable {G : Type*} [AddCommGroup G] (A : LatAct Λ G)

theorem map_zero : A.ρ 0 = 0 := by
  have h := A.map_add 0 0
  rw [add_zero] at h
  exact left_eq_add.mp h

theorem map_nsmul (n : ℕ) (m : ↥Λ) : A.ρ (n • m) = n • A.ρ m := by
  induction n with
  | zero => rw [zero_smul, zero_smul, A.map_zero]
  | succ n ih => rw [succ_nsmul, A.map_add, ih, succ_nsmul]

theorem map_sub (m m' : ↥Λ) : A.ρ (m - m') = A.ρ m - A.ρ m' := by
  have h := A.map_add (m - m') m'
  rw [sub_add_cancel] at h
  rw [h, add_sub_cancel_right]

end LatAct

section Torsion

variable {G : Type*} [AddCommGroup G]

theorem nsmul_eq_zero_of_dvd {x : G} {n m : ℕ} (h : n ∣ m) (hx : n • x = 0) : m • x = 0 := by
  rcases h with ⟨c, rfl⟩
  rw [mul_comm, mul_nsmul', hx, nsmul_zero]

omit [Fact q.Prime] in

theorem eq_zero_of_coprime_nsmul {k n : ℕ} (hn : n.Coprime q) {x : G} (hx : q ^ k • x = 0) (h : n • x = 0) :
    x = 0 := by
  have hc : IsCoprime (n : ℤ) ((q : ℤ) ^ k) := by
    rw [Int.isCoprime_iff_gcd_eq_one, ← Int.natCast_pow, Int.gcd_natCast_natCast]
    exact (Nat.Coprime.pow_right k hn)
  obtain ⟨u, v, huv⟩ := hc
  have hxz : ((q : ℤ) ^ k) • x = 0 := by rw [← Int.natCast_pow, natCast_zsmul, hx]
  have hnz : (n : ℤ) • x = 0 := by rw [natCast_zsmul, h]
  calc x = ((u * n + v * (q : ℤ) ^ k) : ℤ) • x := by rw [huv, one_zsmul]
    _ = 0 := by rw [add_zsmul, mul_zsmul, mul_zsmul, hxz, hnz, zsmul_zero, zsmul_zero, add_zero]

omit [Fact q.Prime] in
theorem eq_of_coprime_nsmul {k n : ℕ} (hn : n.Coprime q) {x y : G} (hx : q ^ k • x = 0) (hy : q ^ k • y = 0)
    (h : n • x = n • y) : x = y := by
  have : n • (x - y) = 0 := by rw [nsmul_sub, h, sub_self]
  have h' := eq_zero_of_coprime_nsmul (q := q) (k := k) hn (x := x - y)
    (by rw [nsmul_sub, hx, hy, sub_self]) this
  exact sub_eq_zero.mp h'

end Torsion

section Heart

variable {G : Type*} [AddCommGroup G]

theorem apply_eq_zero_of_cong_zero (A : LatAct Λ G) (coord : ↥Λ → Zp2 q × Zp2 q)
    (hsat : ∀ (K : ℕ) (m : ↥Λ), (coord m).1 ∈ Ideal.span {((q : ℕ) : Zp2 q) ^ K} →
        (coord m).2 ∈ Ideal.span {((q : ℕ) : Zp2 q) ^ K} → ∃ m' : ↥Λ, m = (q ^ K : ℕ) • m')
    {k : ℕ} {m : ↥Λ} (hm : Cong k (coord m) 0) {x : G} (hx : q ^ k • x = 0) : A.ρ m x = 0 := by
  obtain ⟨h1, h2⟩ := hm
  rw [Prod.fst_zero, sub_zero] at h1
  rw [Prod.snd_zero, sub_zero] at h2
  obtain ⟨m', rfl⟩ := hsat k m h1 h2
  rw [A.map_nsmul, AddMonoidHom.nsmul_apply, ← map_nsmul, hx, map_zero]

theorem apply_eq_of_cong (A : LatAct Λ G) (coord : ↥Λ → Zp2 q × Zp2 q) (hadd : ∀ m m' : ↥Λ, coord (m + m') = coord m + coord m')
    (hsat : ∀ (K : ℕ) (m : ↥Λ), (coord m).1 ∈ Ideal.span {((q : ℕ) : Zp2 q) ^ K} →
        (coord m).2 ∈ Ideal.span {((q : ℕ) : Zp2 q) ^ K} → ∃ m' : ↥Λ, m = (q ^ K : ℕ) • m')
    {k : ℕ} {m m' : ↥Λ} (hm : Cong k (coord m) (coord m')) {x : G} (hx : q ^ k • x = 0) : A.ρ m x = A.ρ m' x := by
  have hsub : coord (m - m') = coord m - coord m' := by
    have h := hadd (m - m') m'
    rw [sub_add_cancel] at h
    rw [h, add_sub_cancel_right]
  have hc : Cong k (coord (m - m')) 0 := by
    rw [hsub]; simpa using hm.sub (Cong.refl k (coord m'))
  have h := apply_eq_zero_of_cong_zero A coord hsat hc hx
  rwa [A.map_sub, AddMonoidHom.sub_apply, sub_eq_zero] at h

omit [Fact q.Prime] in
theorem tmul_nsmul_left [Fact q.Prime] (n : ℕ) (v w : Zp2 q × Zp2 q) : tmul (n • v) w = n • tmul v w := by
  obtain ⟨v1, v2⟩ := v
  obtain ⟨w1, w2⟩ := w
  simp only [tmul, Prod.smul_mk, nsmul_eq_mul, Prod.mk.injEq]
  constructor <;> ring

theorem qPow_one_eq : qPow q 1 = Ideal.span {((q : ℕ) : Zp2 q)} := by
  show Ideal.span {((q : ℕ) : Zp2 q) ^ 1} = _
  rw [pow_one]

theorem qPow_one_isMaximal : (qPow q 1).IsMaximal := by
  rw [qPow_one_eq]
  refine Ideal.Quotient.maximal_of_isField _ ?_
  exact MulEquiv.isField (Field.toIsField (GaloisField q 2))
    (WittVector.quotientPEquiv (p := q) (k := GaloisField q 2)).toMulEquiv

theorem natCard_quotient_qPow_one : Nat.card (Zp2 q ⧸ qPow q 1) = q ^ 2 := by
  rw [qPow_one_eq]
  rw [Nat.card_congr (WittVector.quotientPEquiv (p := q) (k := GaloisField q 2)).toEquiv]
  exact GaloisField.card q 2 (by norm_num)

theorem exists_natCard_eq_pow_of_forall_smul_eq_zero (V : Type*) [AddCommGroup V] [Module (Zp2 q) V]
    [Finite V] (hV : ∀ v : V, ((q : ℕ) : Zp2 q) • v = 0) :
    ∃ a : ℕ, Nat.card V = (q ^ 2) ^ a := by
  have hT : Module.IsTorsionBy (Zp2 q) V (((q : ℕ) : Zp2 q) ^ 1) := fun v => by
    show ((q : ℕ) : Zp2 q) ^ 1 • v = 0
    rw [pow_one]; exact hV v
  letI : Module (Zp2 q ⧸ qPow q 1) V := hT.module
  haveI : (qPow q 1).IsMaximal := qPow_one_isMaximal
  letI : Field (Zp2 q ⧸ qPow q 1) := Ideal.Quotient.field (qPow q 1)
  haveI : Module.Finite (Zp2 q ⧸ qPow q 1) V := Module.Finite.of_finite
  refine ⟨Module.finrank (Zp2 q ⧸ qPow q 1) V, ?_⟩
  rw [Module.natCard_eq_pow_finrank (K := Zp2 q ⧸ qPow q 1) (V := V), natCard_quotient_qPow_one]

variable (A : LatAct Λ G) (coord : ↥Λ → Zp2 q × Zp2 q)

theorem coord_nsmul (hcoord : IsOrderCoord Λ q coord) (n : ℕ) (m : ↥Λ) : coord (n • m) = n • coord m := by
  induction n with
  | zero =>
      have h := hcoord.map_add 0 0
      rw [add_zero] at h
      rw [zero_smul, zero_smul]
      exact left_eq_add.mp h
  | succ n ih => rw [succ_nsmul, hcoord.map_add, ih, succ_nsmul]

theorem exists_prod (hcoord : IsOrderCoord Λ q coord) (m m' : ↥Λ) :
    ∃ n : ℕ, n.Coprime q ∧ ∃ P : ↥Λ, coord P = n • tmul (coord m) (coord m') ∧
      ∀ x : G, A.ρ P x = n • A.ρ m (A.ρ m' x) := by
  obtain ⟨-, -, hprod, -⟩ :=
    CerednikDrinfeld.QM.IsOrderCoord.exists_eq_pow_smul_and_exists_nsmul_mem_and_exists_coprime coord hcoord
  obtain ⟨n, hn, hmem⟩ := hprod m m'
  have hcoe : ((n • m : ↥Λ) : ℍ[ℚ, a, b]) = (n : ℚ) • (m : ℍ[ℚ, a, b]) := by
    rw [AddSubmonoidClass.coe_nsmul, Nat.cast_smul_eq_nsmul]
  have hmem' : ((n • m : ↥Λ) : ℍ[ℚ, a, b]) * (m' : ℍ[ℚ, a, b]) ∈ Λ := by
    rw [hcoe, smul_mul_assoc]; exact hmem
  refine ⟨n, hn, ⟨_, hmem'⟩, ?_, fun x => ?_⟩
  · rw [hcoord.map_mul (n • m) m' hmem', coord_nsmul coord hcoord, ← tmul_nsmul_left]
    rfl
  · rw [A.map_mul (n • m) m' hmem', A.map_nsmul]
    rfl

variable {A coord}

theorem heart (A : LatAct Λ G) (coord : ↥Λ → Zp2 q × Zp2 q) (hcoord : IsOrderCoord Λ q coord)
    (hscal : ∃ n₀ : ℕ, n₀.Coprime q ∧ ∃ u : ↥Λ, coord u = (((n₀ : ℕ) : Zp2 q), 0) ∧ ∀ x : G, A.ρ u x = n₀ • x)
    (hdiv : ∀ x : G, ∃ y : G, q • y = x)
    (hfin : Set.Finite {x : G | q • x = 0}) (hcard : Nat.card {x : G // q • x = 0} ≤ q ^ 2) :
    ∀ x : G, q • x = 0 → x = 0 := by
  classical
  obtain ⟨hsat, -, -, -⟩ :=
    CerednikDrinfeld.QM.IsOrderCoord.exists_eq_pow_smul_and_exists_nsmul_mem_and_exists_coprime coord hcoord
  obtain ⟨n₀, hn₀, u, hu, hux⟩ := hscal
  have hq : (q : ℕ) ≠ 0 := (Fact.out : q.Prime).ne_zero

  have tors1 : ∀ {x : G}, q • x = 0 → q ^ 1 • x = 0 := fun h => by rwa [pow_one]
  have tors2 : ∀ {x : G}, q • x = 0 → q ^ 2 • x = 0 := fun h => by
    rw [pow_succ, pow_one, mul_nsmul', h, nsmul_zero]
  have torsmap : ∀ (φ : G →+ G) {n : ℕ} {x : G}, n • x = 0 → n • φ x = 0 := fun φ n x h => by
    rw [← map_nsmul, h, map_zero]

  have hcong : ∀ {k : ℕ} {m m' : ↥Λ}, Cong k (coord m) (coord m') → ∀ {x : G}, q ^ k • x = 0 →
      A.ρ m x = A.ρ m' x := fun hm x hx => apply_eq_of_cong A coord hcoord.map_add hsat hm hx
  have hcong0 : ∀ {k : ℕ} {m : ↥Λ}, Cong k (coord m) 0 → ∀ {x : G}, q ^ k • x = 0 → A.ρ m x = 0 :=
    fun hm x hx => apply_eq_zero_of_cong_zero A coord hsat hm hx
  have hfrob1 : WittVector.frobenius (1 : Zp2 q) = 1 := map_one _
  have hfrob0 : WittVector.frobenius (0 : Zp2 q) = 0 := map_zero _

  obtain ⟨π, hπ1, hπ2⟩ := hcoord.dense 2 0 1
  have hπ : Cong 2 (coord π) (0, 1) := ⟨hπ1, hπ2⟩
  set ϖ : G →+ G := A.ρ π with hϖdef
  have hϖϖ : ∀ y : G, q ^ 2 • y = 0 → ϖ (ϖ y) = q • y := by
    intro y hy
    obtain ⟨n₁, hn₁, P, hPc, hPρ⟩ := exists_prod A coord hcoord π π

    have h1 : Cong 2 (tmul (coord π) (coord π)) (tmul ((0 : Zp2 q), (1 : Zp2 q)) (0, 1)) := hπ.tmul hπ
    have h2 : tmul ((0 : Zp2 q), (1 : Zp2 q)) (0, 1) = (((q : ℕ) : Zp2 q), 0) := by
      simp only [tmul, hfrob1, hfrob0]; ext <;> simp
    rw [h2] at h1
    have h3 : Cong 2 (coord (n₀ • P)) (coord ((q * n₁) • u)) := by
      rw [coord_nsmul coord hcoord, coord_nsmul coord hcoord, hPc, hu]
      have h4 : (q * n₁) • ((((n₀ : ℕ) : Zp2 q), (0 : Zp2 q)) : Zp2 q × Zp2 q) =
          n₀ • n₁ • ((((q : ℕ) : Zp2 q)), (0 : Zp2 q)) := by
        ext <;> simp [nsmul_eq_mul]; ring_nf
      rw [h4]
      exact (h1.nsmul n₁).nsmul n₀
    have h5 := hcong h3 hy
    rw [A.map_nsmul, A.map_nsmul, AddMonoidHom.nsmul_apply, AddMonoidHom.nsmul_apply, hPρ, hux] at h5
    simp only [smul_smul] at h5

    have h6 : (n₀ * n₁) • ϖ (ϖ y) = (n₀ * n₁) • (q • y) := by
      rw [hϖdef, h5, smul_smul]; congr 1; ring
    refine eq_of_coprime_nsmul (q := q) (k := 2) (Nat.Coprime.mul_left hn₀ hn₁) ?_ ?_ h6
    · exact torsmap _ (torsmap _ hy)
    · rw [← mul_nsmul', mul_comm, mul_nsmul', hy, nsmul_zero]

  let mα : Zp2 q → ↥Λ := fun α => Classical.choose (hcoord.dense 1 α 0)
  have hmα : ∀ α, Cong 1 (coord (mα α)) (α, 0) := fun α => Classical.choose_spec (hcoord.dense 1 α 0)
  set s : Zp2 q → G →+ G := fun α => A.ρ (mα α) with hsdef
  have hs_add : ∀ (α β : Zp2 q) {x : G}, q • x = 0 → s (α + β) x = s α x + s β x := by
    intro α β x hx
    have h : Cong 1 (coord (mα (α + β))) (coord (mα α + mα β)) := by
      rw [hcoord.map_add]
      refine (hmα (α + β)).trans ?_
      have := (hmα α).add (hmα β)
      simp only [Prod.mk_add_mk, add_zero] at this
      exact this.symm
    have := hcong h (tors1 hx)
    rw [A.map_add, AddMonoidHom.add_apply] at this
    exact this
  have hs_q : ∀ (α : Zp2 q), α ∈ qPow q 1 → ∀ {x : G}, q • x = 0 → s α x = 0 := by
    intro α hα x hx
    refine hcong0 ((hmα α).trans ⟨by simpa using hα, by simp⟩) (tors1 hx)
  have hs_one : ∀ {x : G}, q • x = 0 → s 1 x = x := by
    intro x hx
    have h : Cong 1 (coord (n₀ • mα 1)) (coord u) := by
      rw [coord_nsmul coord hcoord, hu]
      have e : n₀ • ((1 : Zp2 q), (0 : Zp2 q)) = (((n₀ : ℕ) : Zp2 q), 0) := Prod.ext (by simp) (by simp)
      rw [← e]
      exact (hmα 1).nsmul n₀
    have h' := hcong h (tors1 hx)
    rw [A.map_nsmul, AddMonoidHom.nsmul_apply, hux] at h'
    exact eq_of_coprime_nsmul (q := q) (k := 1) hn₀ (torsmap _ (tors1 hx)) (tors1 hx) h'
  have hs_mul : ∀ (α β : Zp2 q) {x : G}, q • x = 0 → s (α * β) x = s α (s β x) := by
    intro α β x hx
    obtain ⟨n, hn, P, hPc, hPρ⟩ := exists_prod A coord hcoord (mα α) (mα β)
    have h1 : Cong 1 (coord P) (coord (n • mα (α * β))) := by
      rw [hPc, coord_nsmul coord hcoord]
      refine (((hmα α).tmul (hmα β)).trans ?_).nsmul n |>.trans ((hmα (α * β)).nsmul n).symm
      simp only [tmul, hfrob0, mul_zero, zero_mul, add_zero]
      exact Cong.refl 1 _
    have h2 := hcong h1 (tors1 hx)
    rw [hPρ, A.map_nsmul, AddMonoidHom.nsmul_apply] at h2
    exact (eq_of_coprime_nsmul (q := q) (k := 1) hn (torsmap _ (tors1 hx))
      (torsmap _ (torsmap _ (tors1 hx))) h2.symm)
  have hs_frob : ∀ (α : Zp2 q) {x : G}, q • x = 0 → ϖ (s α x) = s (WittVector.frobenius α) (ϖ x) := by
    intro α x hx
    obtain ⟨n, hn, P, hPc, hPρ⟩ := exists_prod A coord hcoord π (mα α)
    obtain ⟨n', hn', P', hP'c, hP'ρ⟩ := exists_prod A coord hcoord (mα (WittVector.frobenius α)) π
    have e1 : Cong 1 (coord P) (n • ((0 : Zp2 q), WittVector.frobenius α)) := by
      rw [hPc]
      refine (((hπ.of_le (by norm_num)).tmul (hmα α)).trans ?_).nsmul n
      simp only [tmul, hfrob0, mul_zero, zero_mul, add_zero, zero_add, one_mul]
      exact Cong.refl 1 _
    have e2 : Cong 1 (coord P') (n' • ((0 : Zp2 q), WittVector.frobenius α)) := by
      rw [hP'c]
      refine (((hmα _).tmul (hπ.of_le (by norm_num))).trans ?_).nsmul n'
      simp only [tmul, hfrob0, hfrob1, mul_zero, add_zero, mul_one]
      exact Cong.refl 1 _
    have e3 : Cong 1 (coord (n' • P)) (coord (n • P')) := by
      rw [coord_nsmul coord hcoord, coord_nsmul coord hcoord]
      refine (e1.nsmul n').trans ?_
      rw [smul_smul, mul_comm n' n, ← smul_smul]
      exact (e2.nsmul n).symm
    have e4 := hcong e3 (tors1 hx)
    rw [A.map_nsmul, A.map_nsmul, AddMonoidHom.nsmul_apply, AddMonoidHom.nsmul_apply, hPρ, hP'ρ,
      ← mul_nsmul', ← mul_nsmul', mul_comm n n'] at e4
    exact eq_of_coprime_nsmul (q := q) (k := 1) (Nat.Coprime.mul_left hn' hn) (torsmap _ (torsmap _ (tors1 hx)))
      (torsmap _ (torsmap _ (tors1 hx))) e4

  let T : AddSubgroup G :=
    { carrier := {x | q • x = 0}
      add_mem' := fun {x y} hx hy => by
        simp only [Set.mem_setOf_eq] at hx hy ⊢
        rw [nsmul_add, hx, hy, add_zero]
      zero_mem' := by simp
      neg_mem' := fun {x} hx => by
        simp only [Set.mem_setOf_eq] at hx ⊢
        rw [smul_neg, hx, neg_zero] }
  have hmemT : ∀ x : G, x ∈ T ↔ q • x = 0 := fun x => Iff.rfl
  let K : AddSubgroup G :=
    { carrier := {x | q • x = 0 ∧ ϖ x = 0}
      add_mem' := fun {x y} hx hy => by
        simp only [Set.mem_setOf_eq] at hx hy ⊢
        rw [nsmul_add, hx.1, hy.1, add_zero, map_add, hx.2, hy.2, add_zero]
        exact ⟨rfl, rfl⟩
      zero_mem' := by simp
      neg_mem' := fun {x} hx => by
        simp only [Set.mem_setOf_eq] at hx ⊢
        rw [smul_neg, hx.1, neg_zero, map_neg, hx.2, neg_zero]
        exact ⟨rfl, rfl⟩ }
  have hmemK : ∀ x : G, x ∈ K ↔ q • x = 0 ∧ ϖ x = 0 := fun x => Iff.rfl
  haveI hTfin : Finite T := hfin.to_subtype
  have hKT : K ≤ T := fun x hx => hx.1
  haveI : Finite K := Finite.of_injective (AddSubgroup.inclusion hKT) (AddSubgroup.inclusion_injective hKT)

  have hsK : ∀ (α : Zp2 q) (x : K), s α (x : G) ∈ K := fun α x => by
    refine ⟨torsmap _ x.2.1, ?_⟩
    rw [hs_frob α x.2.1, x.2.2, map_zero]
  letI : SMul (Zp2 q) K := ⟨fun α x => ⟨s α x, hsK α x⟩⟩
  have hsmul : ∀ (α : Zp2 q) (x : K), ((α • x : K) : G) = s α x := fun _ _ => rfl
  letI : Module (Zp2 q) K :=
    { one_smul := fun x => Subtype.ext (by rw [hsmul]; exact hs_one x.2.1)
      mul_smul := fun α β x => Subtype.ext (by rw [hsmul, hsmul, hsmul]; exact hs_mul α β x.2.1)
      smul_zero := fun α => Subtype.ext (by rw [hsmul]; exact map_zero _)
      smul_add := fun α x y => Subtype.ext (by
        rw [hsmul, AddSubgroup.coe_add, AddSubgroup.coe_add, map_add, hsmul, hsmul])
      add_smul := fun α β x => Subtype.ext (by
        rw [hsmul, AddSubgroup.coe_add, hsmul, hsmul]; exact hs_add α β x.2.1)
      zero_smul := fun x => Subtype.ext (by
        rw [hsmul, AddSubgroup.coe_zero]
        exact hs_q 0 (Ideal.zero_mem _) x.2.1) }
  obtain ⟨t, ht⟩ := exists_natCard_eq_pow_of_forall_smul_eq_zero (q := q) K fun x =>
    Subtype.ext (by rw [hsmul, AddSubgroup.coe_zero]; exact hs_q _ (by simpa using natCast_pow_mem_qPow (q := q) 1) x.2.1)

  let ψ : T →+ K :=
    { toFun := fun x => ⟨ϖ x, torsmap _ x.2, by rw [hϖϖ _ (tors2 x.2)]; exact x.2⟩
      map_zero' := Subtype.ext (by simp)
      map_add' := fun x y => Subtype.ext (by simp) }
  have hψ : Function.Surjective ψ := by
    rintro ⟨z, hz1, hz2⟩
    obtain ⟨y, rfl⟩ := hdiv z
    have hy2 : q ^ 2 • y = 0 := by rw [pow_succ, pow_one, mul_comm, mul_nsmul', hz1]
    refine ⟨⟨ϖ y, ?_⟩, Subtype.ext ?_⟩
    · show q • ϖ y = 0
      rw [← map_nsmul, hz2]
    · show ϖ (ϖ y) = q • y
      exact hϖϖ y hy2
  have hker : Nat.card ψ.ker = Nat.card K := by
    refine Nat.card_congr
      { toFun := fun m => ⟨(m.1 : G), m.1.2, congrArg Subtype.val (AddMonoidHom.mem_ker.mp m.2)⟩
        invFun := fun k => ⟨⟨(k : G), hKT k.2⟩, AddMonoidHom.mem_ker.mpr (Subtype.ext k.2.2)⟩
        left_inv := fun m => rfl
        right_inv := fun k => rfl }
  have hTcard : Nat.card T = (q ^ 4) ^ t := by
    rw [AddSubgroup.card_eq_card_quotient_mul_card_addSubgroup ψ.ker,
      Nat.card_congr (QuotientAddGroup.quotientKerEquivOfSurjective ψ hψ).toEquiv, hker, ht, ← mul_pow]
    ring

  have hTcard' : Nat.card T ≤ q ^ 2 := by
    have : Nat.card {x : G // q • x = 0} = Nat.card T := Nat.card_congr (Equiv.refl _)
    rw [← this]; exact hcard
  have ht0 : t = 0 := by
    by_contra htne
    have hq1 : 1 < q := (Fact.out : q.Prime).one_lt
    have h1 : q ^ 4 ≤ (q ^ 4) ^ t := Nat.le_self_pow htne _
    have h2 : q ^ 2 < q ^ 4 := Nat.pow_lt_pow_right hq1 (by norm_num)
    have := hTcard ▸ hTcard'
    omega
  rw [ht0, pow_zero] at hTcard

  intro x hx
  haveI : Subsingleton T := (Nat.card_eq_one_iff_unique.mp hTcard).1
  have h := Subsingleton.elim (⟨x, hx⟩ : T) ⟨0, T.zero_mem⟩
  exact congrArg Subtype.val h

end Heart

end R4X5Heart

namespace R4X5Heart

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian CerednikDrinfeld CerednikDrinfeld.QM

open scoped Quaternion

section Geom

universe u

variable {R : Type u} [CommRing R] {A : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of R)}

theorem nsmulPt_eq_nsmul (L : RelativeGroupLaw R f) {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (n : ℕ)
    (P : SchemeHomOver t f) : nsmulPt L t n P = L.nsmul t n P := by
  induction n with
  | zero => rfl
  | succ n ih => rw [RelativeGroupLaw.nsmul_succ, ← ih]; rfl

theorem pow_eq_nsmulPt (L : RelativeGroupLaw R f) {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (n : ℕ)
    (P : SchemeHomOver t f) :
    (letI := L.pointGroup t; P ^ n) = nsmulPt L t n P := by
  letI := L.pointGroup t
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [pow_succ, ih]
      rfl

theorem nsmul_val (L : RelativeGroupLaw R f) {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (n : ℕ)
    (Q : SchemeHomOver t f) : (L.nsmul t n Q).1 = Q.1 ≫ L.schemeNsmul n := by
  have h := L.nsmul_natural f t Q.1 Q.2 n RelativeGroupLaw.idPoint
  have hQ : schemeHomOverComp Q.1 Q.2 (RelativeGroupLaw.idPoint (f := f)) = Q :=
    Subtype.ext (Category.comp_id _)
  rw [hQ] at h
  rw [← h]
  rfl

end Geom

section GeomField

variable {k : Type} [Field k] {A : Scheme.{0}} {f : A ⟶ Spec (CommRingCat.of k)}

theorem connectedSpace_of_bundle (hA : AbelianSchemePropertyBundle k f) : ConnectedSpace A := by
  have h := hA.connectedFibres (IsLocalRing.closedPoint k)
  refine connectedSpace_iff_univ.mpr ?_
  convert h using 1
  exact (Set.eq_univ_of_forall fun x => Subsingleton.elim _ _).symm

theorem exists_nsmul_eq [IsAlgClosed k] (L : RelativeGroupLaw k f) (hA : AbelianSchemePropertyBundle k f)
    (hcomm : L.IsCommutative) (n : ℕ) (hn : 0 < n)
    (P : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) f) :
    ∃ Q : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) f, L.nsmul (𝟙 _) n Q = P := by
  obtain ⟨hfin, hflat⟩ :=
    GoodReductionJacobian.RelativeGroupLaw.isFinite_and_flat_schemeNsmul L hA (fun t x y => hcomm t x y) n hn
  haveI := hA.smooth
  haveI : LocallyOfFiniteType f := inferInstance
  haveI : ConnectedSpace A := connectedSpace_of_bundle hA
  haveI : IsFinite (⟨L.schemeNsmul n, L.schemeNsmul_over n⟩ : SchemeHomOver f f).1 := hfin
  haveI : Flat (⟨L.schemeNsmul n, L.schemeNsmul_over n⟩ : SchemeHomOver f f).1 := hflat
  have hsurj := (GoodReductionJacobian.RelativeGroupLaw.surjective_and_endDegree_eq_finrank_of_isFinite_of_flat k f L
    ⟨L.schemeNsmul n, L.schemeNsmul_over n⟩).1
  haveI : Surjective (L.schemeNsmul n) := ⟨hsurj⟩
  haveI : IsFinite (L.schemeNsmul n) := hfin
  haveI : LocallyOfFiniteType (L.schemeNsmul n) := inferInstance
  obtain ⟨Q₀, hQ₀⟩ :=
    AlgebraicGeometry.exists_comp_eq_of_surjective_of_locallyOfFiniteType_of_isAlgClosed (L.schemeNsmul n) P.1
  refine ⟨⟨Q₀, ?_⟩, Subtype.ext ?_⟩
  · rw [← L.schemeNsmul_over n, ← Category.assoc, hQ₀]; exact P.2
  · rw [nsmul_val, hQ₀]

end GeomField

end R4X5Heart

namespace R4X5HeartL

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian CerednikDrinfeld CerednikDrinfeld.QM

open scoped Quaternion

universe u

variable {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} {N : ℕ} {S : Type u} [CommRing S]

theorem eq_one_of_factorsThrough_one {A : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of S)} (L : RelativeGroupLaw S f)
    {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of S)) (P : SchemeHomOver t f)
    (h : FactorsThrough (L.one (𝟙 (Spec (CommRingCat.of S)))).1 P) : P = L.one t := by
  obtain ⟨P₀, hP₀⟩ := h
  have ht : P₀ = t := by
    have h2 := congrArg (· ≫ f) hP₀
    simp only [Category.assoc, (L.one (𝟙 _)).2, Category.comp_id] at h2
    rw [h2, P.2]
  subst ht
  have h1 := L.one_natural (𝟙 (Spec (CommRingCat.of S))) P₀ P₀ (Category.comp_id _)
  apply Subtype.ext
  rw [← hP₀, ← h1]
  rfl

theorem factorsThrough_one_iff {A : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of S)} (L : RelativeGroupLaw S f)
    {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of S)) (P : SchemeHomOver t f) :
    FactorsThrough (L.one (𝟙 (Spec (CommRingCat.of S)))).1 P ↔ P = L.one t := by
  refine ⟨eq_one_of_factorsThrough_one L t P, fun h => ⟨t, ?_⟩⟩
  subst h
  have h1 := L.one_natural (𝟙 (Spec (CommRingCat.of S))) t t (Category.comp_id _)
  rw [← h1]
  rfl

noncomputable def toLevelOne (E : FakeEllipticCurve Λ N S) : FakeEllipticCurve Λ 1 S where
  A := E.A
  f := E.f
  L := E.L
  comm := E.comm
  bundle := E.bundle
  dim_fibre := E.dim_fibre
  act := E.act
  act_over := E.act_over
  act_hom := E.act_hom
  act_one := E.act_one
  act_mul := E.act_mul
  act_add := E.act_add
  act_trace := E.act_trace
  C := Spec (CommRingCat.of S)
  lev := (E.L.one (𝟙 (Spec (CommRingCat.of S)))).1
  lev_closed := by
    haveI := E.bundle.proper
    haveI : IsClosedImmersion ((E.L.one (𝟙 (Spec (CommRingCat.of S)))).1 ≫ E.f) := by
      rw [(E.L.one (𝟙 _)).2]; infer_instance
    exact IsClosedImmersion.of_comp _ E.f
  lev_sub := fun {T} t P Q hP hQ => by
    rw [factorsThrough_one_iff] at hP hQ ⊢
    rw [factorsThrough_one_iff]
    subst hP; subst hQ
    exact ⟨E.L.one_mul t _, by
      letI := E.L.pointGroup t
      exact inv_one⟩
  lev_one := fun {T} t => (factorsThrough_one_iff E.L t _).mpr rfl
  lev_torsion := fun {T} t P hP => by
    rw [factorsThrough_one_iff] at hP
    subst hP
    show E.L.mul t (E.L.one t) (E.L.one t) = E.L.one t
    exact E.L.one_mul t _
  lev_stable := fun x {T} t P hP => by
    rw [factorsThrough_one_iff] at hP ⊢
    subst hP
    letI := E.L.pointGroup t
    have h : pushPt (E.act x) (E.act_over x) (E.L.one t) * pushPt (E.act x) (E.act_over x) (E.L.one t) =
        pushPt (E.act x) (E.act_over x) (E.L.one t) := by
      show E.L.mul t _ _ = _
      rw [← E.act_hom x t, E.L.one_mul]
    exact mul_eq_right.mp h
  lev_finite := by rw [(E.L.one (𝟙 _)).2]; infer_instance
  lev_flat := by rw [(E.L.one (𝟙 _)).2]; infer_instance
  lev_finitePresentation := by rw [(E.L.one (𝟙 _)).2]; infer_instance
  lev_rank := fun s => by
    rw [(E.L.one (𝟙 _)).2, one_pow]
    exact congrFun (Scheme.Hom.finrank_eq_one_of_isIso (𝟙 (Spec (CommRingCat.of S)))) s
  lev_fibre := fun k _ _ sk _ => by
    haveI : Unique (ZMod 1) := inferInstanceAs (Unique (Fin 1))
    haveI : Unique (ZMod 1 × ZMod 1) := { default := (default, default), uniq := fun x => Prod.ext (Subsingleton.elim _ _) (Subsingleton.elim _ _) }
    haveI : Unique {P : SchemeHomOver (geomPoint k sk) E.f //
        FactorsThrough (E.L.one (𝟙 (Spec (CommRingCat.of S)))).1 P} :=
      { default := ⟨E.L.one _, (factorsThrough_one_iff E.L _ _).mpr rfl⟩
        uniq := fun P => Subtype.ext ((factorsThrough_one_iff E.L _ _).mp P.2) }
    refine ⟨Equiv.ofUnique _ _, fun x y => ?_⟩
    have hx : ((Equiv.ofUnique (ZMod 1 × ZMod 1) _ (x + y) : {P : SchemeHomOver (geomPoint k sk) E.f //
        FactorsThrough (E.L.one (𝟙 (Spec (CommRingCat.of S)))).1 P}) : SchemeHomOver (geomPoint k sk) E.f) =
        E.L.one _ := (factorsThrough_one_iff E.L _ _).mp (Subtype.property _)
    have h1 : ∀ z, ((Equiv.ofUnique (ZMod 1 × ZMod 1) _ z : {P : SchemeHomOver (geomPoint k sk) E.f //
        FactorsThrough (E.L.one (𝟙 (Spec (CommRingCat.of S)))).1 P}) : SchemeHomOver (geomPoint k sk) E.f) =
        E.L.one _ := fun z => (factorsThrough_one_iff E.L _ _).mp (Subtype.property _)
    rw [h1, h1, h1, E.L.one_mul]

@[scoped simp] theorem toLevelOne_A (E : FakeEllipticCurve Λ N S) : (toLevelOne E).A = E.A := rfl
@[scoped simp] theorem toLevelOne_f (E : FakeEllipticCurve Λ N S) : (toLevelOne E).f = E.f := rfl
@[scoped simp] theorem toLevelOne_L (E : FakeEllipticCurve Λ N S) : (toLevelOne E).L = E.L := rfl

theorem finite_and_natCard_torsionPoints_le_sq (k : Type u) [Field k] [IsAlgClosed k] (q : ℕ) [Fact q.Prime]
    [CharP k q] (E : FakeEllipticCurve Λ N k) :
    Finite {P : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) E.f //
        nsmulPt E.L (𝟙 (Spec (CommRingCat.of k))) q P = E.L.one (𝟙 (Spec (CommRingCat.of k)))} ∧
      Nat.card {P : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) E.f //
        nsmulPt E.L (𝟙 (Spec (CommRingCat.of k))) q P = E.L.one (𝟙 (Spec (CommRingCat.of k)))} ≤ q ^ 2 :=
  CerednikDrinfeld.QM.FakeEllipticCurve.finite_and_natCard_torsionPoints_le_sq_of_charP_of_not_dvd k q
    (Nat.Prime.not_dvd_one (Fact.out)) (toLevelOne E)

end R4X5HeartL
p2m_reactivate "P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_eq_one_of_nsmulPt_pow_eq_one_of_isOrderCoord_of_charP.R4X5HeartL"

namespace R4X5Heart

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian CerednikDrinfeld CerednikDrinfeld.QM

open scoped Quaternion

section Core

variable {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} {N : ℕ} {q : ℕ} [Fact q.Prime]

theorem eq_one_of_nsmulPt_eq_one (coord : ↥Λ → Zp2 q × Zp2 q) (hcoord : IsOrderCoord Λ q coord)
    (h1 : (1 : ℍ[ℚ, a, b]) ∈ Λ)
    (k : Type) [Field k] [IsAlgClosed k] [CharP k q] (E : FakeEllipticCurve Λ N k)
    (P : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) E.f)
    (hP : nsmulPt E.L (𝟙 (Spec (CommRingCat.of k))) q P = E.L.one (𝟙 (Spec (CommRingCat.of k)))) :
    P = E.L.one (𝟙 (Spec (CommRingCat.of k))) := by
  classical

  let t₀ := 𝟙 (Spec (CommRingCat.of k))
  letI grp : Group (SchemeHomOver t₀ E.f) := E.L.pointGroup t₀
  letI cgrp : CommGroup (SchemeHomOver t₀ E.f) := { grp with mul_comm := fun x y => E.comm t₀ x y }
  let G := Additive (SchemeHomOver t₀ E.f)
  have hmulG : ∀ x y : SchemeHomOver t₀ E.f, x * y = E.L.mul t₀ x y := fun _ _ => rfl
  have honeG : (1 : SchemeHomOver t₀ E.f) = E.L.one t₀ := rfl
  have hpow : ∀ (n : ℕ) (x : SchemeHomOver t₀ E.f), x ^ n = nsmulPt E.L t₀ n x := fun n x =>
    pow_eq_nsmulPt E.L t₀ n x

  let ρ₀ : ↥Λ → SchemeHomOver t₀ E.f →* SchemeHomOver t₀ E.f := fun m =>
    MonoidHom.mk' (fun P => pushPt (E.act m) (E.act_over m) P) (fun P Q => E.act_hom m t₀ P Q)
  have hρ₀ : ∀ (m : ↥Λ) (x : SchemeHomOver t₀ E.f), ρ₀ m x = pushPt (E.act m) (E.act_over m) x := fun _ _ => rfl
  let Aact : LatAct Λ G :=
    { ρ := fun m => MonoidHom.toAdditive (ρ₀ m)
      map_add := fun m m' => by
        refine AddMonoidHom.ext fun x => ?_
        show Additive.ofMul (ρ₀ (m + m') (Additive.toMul x)) =
          Additive.ofMul (ρ₀ m (Additive.toMul x)) + Additive.ofMul (ρ₀ m' (Additive.toMul x))
        rw [← ofMul_mul, hρ₀, hρ₀, hρ₀, hmulG]
        exact congrArg Additive.ofMul (E.act_add m m' t₀ (Additive.toMul x))
      map_mul := fun m m' h => by
        refine AddMonoidHom.ext fun x => ?_
        show Additive.ofMul (ρ₀ ⟨(m : ℍ[ℚ, a, b]) * m', h⟩ (Additive.toMul x)) =
          Additive.ofMul (ρ₀ m (ρ₀ m' (Additive.toMul x)))
        rw [hρ₀, hρ₀, hρ₀]
        refine congrArg Additive.ofMul (Subtype.ext ?_)
        show (Additive.toMul x).1 ≫ E.act ⟨(m : ℍ[ℚ, a, b]) * m', h⟩ =
          ((Additive.toMul x).1 ≫ E.act m') ≫ E.act m
        rw [E.act_mul m m' h, Category.assoc] }
  have hAρ : ∀ (m : ↥Λ) (x : G), Aact.ρ m x = Additive.ofMul (pushPt (E.act m) (E.act_over m) (Additive.toMul x)) :=
    fun _ _ => rfl

  have hscal : ∃ n₀ : ℕ, n₀.Coprime q ∧ ∃ u : ↥Λ, coord u = (((n₀ : ℕ) : Zp2 q), 0) ∧ ∀ x : G, Aact.ρ u x = n₀ • x := by
    obtain ⟨-, -, -, n₀, hn₀, hmem, hc⟩ :=
      CerednikDrinfeld.QM.IsOrderCoord.exists_eq_pow_smul_and_exists_nsmul_mem_and_exists_coprime coord hcoord
    refine ⟨n₀, hn₀, _, hc, fun x => ?_⟩
    have hu : (⟨((n₀ : ℚ) : ℍ[ℚ, a, b]), hmem⟩ : ↥Λ) = n₀ • ⟨1, h1⟩ := by
      apply Subtype.ext
      show ((n₀ : ℚ) : ℍ[ℚ, a, b]) = ((n₀ • (⟨1, h1⟩ : ↥Λ) : ↥Λ) : ℍ[ℚ, a, b])
      rw [AddSubmonoidClass.coe_nsmul]
      show ((n₀ : ℚ) : ℍ[ℚ, a, b]) = n₀ • (1 : ℍ[ℚ, a, b])
      rw [nsmul_eq_mul, mul_one]
      norm_cast
    rw [hu, Aact.map_nsmul, AddMonoidHom.nsmul_apply]
    congr 1
    rw [hAρ]
    conv_rhs => rw [← ofMul_toMul x]
    refine congrArg Additive.ofMul (Subtype.ext ?_)
    show (Additive.toMul x).1 ≫ E.act ⟨1, h1⟩ = (Additive.toMul x).1
    rw [E.act_one h1, Category.comp_id]

  have hq0 : 0 < q := (Fact.out : q.Prime).pos
  have hdiv : ∀ x : G, ∃ y : G, q • y = x := by
    intro x
    obtain ⟨Q, hQ⟩ := exists_nsmul_eq E.L E.bundle E.comm q hq0 (Additive.toMul x)
    refine ⟨Additive.ofMul Q, ?_⟩
    rw [← ofMul_pow, hpow, nsmulPt_eq_nsmul, hQ, ofMul_toMul]

  obtain ⟨hfinP, hcardP⟩ := R4X5HeartL.finite_and_natCard_torsionPoints_le_sq k q E
  let e : {P : SchemeHomOver t₀ E.f // nsmulPt E.L t₀ q P = E.L.one t₀} ≃ {x : G // q • x = 0} :=
    { toFun := fun P => ⟨Additive.ofMul P.1, by
        rw [← ofMul_pow, hpow, P.2, ← honeG, ofMul_one]⟩
      invFun := fun x => ⟨Additive.toMul x.1, by
        have hx := x.2
        apply Additive.ofMul.injective
        rw [← hpow, ofMul_pow, ofMul_toMul, ← honeG, ofMul_one]
        exact hx⟩
      left_inv := fun P => Subtype.ext rfl
      right_inv := fun x => Subtype.ext rfl }
  haveI : Finite {P : SchemeHomOver t₀ E.f // nsmulPt E.L t₀ q P = E.L.one t₀} := hfinP
  have hfin : Set.Finite {x : G | q • x = 0} := (Finite.of_equiv _ e).of_injective _ (fun _ _ h => h) |> fun h =>
    Set.finite_coe_iff.mp h
  have hcard : Nat.card {x : G // q • x = 0} ≤ q ^ 2 := by
    rw [← Nat.card_congr e]; exact hcardP

  have hmain := heart Aact coord hcoord hscal hdiv hfin hcard (Additive.ofMul P) (by
    rw [← ofMul_pow, hpow, hP, ← honeG, ofMul_one])
  exact Additive.ofMul.injective (hmain.trans ofMul_one.symm)

theorem eq_one_of_nsmulPt_pow_eq_one (coord : ↥Λ → Zp2 q × Zp2 q) (hcoord : IsOrderCoord Λ q coord)
    (h1 : (1 : ℍ[ℚ, a, b]) ∈ Λ)
    (k : Type) [Field k] [IsAlgClosed k] [CharP k q] (E : FakeEllipticCurve Λ N k) (m : ℕ)
    (P : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) E.f)
    (hP : nsmulPt E.L (𝟙 (Spec (CommRingCat.of k))) (q ^ m) P = E.L.one (𝟙 (Spec (CommRingCat.of k)))) :
    P = E.L.one (𝟙 (Spec (CommRingCat.of k))) := by
  let t₀ := 𝟙 (Spec (CommRingCat.of k))
  letI grp : Group (SchemeHomOver t₀ E.f) := E.L.pointGroup t₀
  have hpow : ∀ (n : ℕ) (x : SchemeHomOver t₀ E.f), x ^ n = nsmulPt E.L t₀ n x := fun n x =>
    pow_eq_nsmulPt E.L t₀ n x
  have honeG : (1 : SchemeHomOver t₀ E.f) = E.L.one t₀ := rfl
  induction m generalizing P with
  | zero =>
      rw [pow_zero, ← hpow, pow_one] at hP
      exact hP
  | succ m ih =>
      apply ih
      apply eq_one_of_nsmulPt_eq_one coord hcoord h1 k E
      rw [← hpow, ← hpow, ← pow_mul, ← pow_succ, hpow]
      exact hP

end Core
p2m_reactivate "P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_eq_one_of_nsmulPt_pow_eq_one_of_isOrderCoord_of_charP.R4X5HeartL"

end R4X5Heart
p2m_reactivate "P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_eq_one_of_nsmulPt_pow_eq_one_of_isOrderCoord_of_charP.R4X5HeartL"

open CategoryTheory AlgebraicGeometry NeronModelInfra GoodReductionJacobian CerednikDrinfeld CerednikDrinfeld.QM
open scoped Quaternion

theorem solution
    {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} {N : ℕ} {q : ℕ} [Fact q.Prime]
    (coord : ↥Λ → Zp2 q × Zp2 q) (hcoord : IsOrderCoord Λ q coord) (h1 : (1 : ℍ[ℚ, a, b]) ∈ Λ)
    (k : Type) [Field k] [IsAlgClosed k] [CharP k q]
    (E : FakeEllipticCurve Λ N k) (m : ℕ)
    (P : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) E.f)
    (hP : nsmulPt E.L (𝟙 (Spec (CommRingCat.of k))) (q ^ m) P = E.L.one (𝟙 (Spec (CommRingCat.of k)))) :
    P = E.L.one (𝟙 (Spec (CommRingCat.of k))) :=
  R4X5Heart.eq_one_of_nsmulPt_pow_eq_one coord hcoord h1 k E m P hP

end S_CerednikDrinfeld_QM_FakeEllipticCurve_eq_one_of_nsmulPt_pow_eq_one_of_isOrderCoord_of_charP
end P2MW
export P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_eq_one_of_nsmulPt_pow_eq_one_of_isOrderCoord_of_charP (solution)
