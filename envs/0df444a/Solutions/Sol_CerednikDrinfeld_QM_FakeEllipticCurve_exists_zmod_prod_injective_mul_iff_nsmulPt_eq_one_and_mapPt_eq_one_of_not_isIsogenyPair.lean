-- Prove2me | solution 1 for CerednikDrinfeld.QM.FakeEllipticCurve.exists_zmod_prod_injective_mul_iff_nsmulPt_eq_one_and_mapPt_eq_one_of_not_isIsogenyPair
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.141142+00:00
-- url     : https://prove2.me/submissions/2afb2649-d878-54dd-820e-a7a9f4a9d51f

import Mathlib
import Definitions.Def_CerednikDrinfeld_QMRigidification
import Definitions.Def_CerednikDrinfeld_QMIsogeny
import Definitions.Def_CerednikDrinfeld_ShimuraCurve
import Definitions.Def_QuaternionAlgebra_EichlerOrder
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawKernel
import Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_exists_eq_act_comp_of_forall_nsmulPt_eq_one_imp_mapPt_eq_one
import Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_epi_act_of_ne_zero
import Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_forall_mapPt_eq_one_of_forall_rationalPoint
import Theorems.Thm_QuaternionAlgebra_IsMaximalOrder_exists_chain_subgroup_relIndex_eq_sq
import Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_finite_and_natCard_torsion_eq_pow_four_of_isUnit
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_exists_zmod_prod_injective_mul_iff_nsmulPt_eq_one_and_mapPt_eq_one_of_not_isIsogenyPair
p2m_attr_erase "instance" "GoodReductionJacobian.RelativeGroupLaw.isIso_endKerStr_schemeHomOverId AlgebraicGeometry.Scheme.PresheafOfModules.symmetricCategory SheafOfModules.instFaithfulRingSheafPModToPMod SheafOfModules.symmetricCategory AlgebraicGeometry.Scheme.PresheafOfModules.monoidalCategory AlgebraicGeometry.Scheme.PresheafOfModules.monoidalClosed SheafOfModules.instFullRingSheafPModToPMod SheafOfModules.monoidalCategory AlgebraicGeometry.Scheme.Modules.symmetricCategory SheafOfModules.monoidalClosed SheafOfModules.instIsLocalizationPModRingSheafSheafifyFunctorPresheafW SheafOfModules.sheafifyFunctor_monoidal AlgebraicGeometry.Scheme.Modules.monoidalClosed AlgebraicGeometry.instMonoidalPresheafOfModulesModulesSheafify AlgebraicGeometry.Scheme.Modules.monoidalCategory PresheafOfModules.instMonoidalClosed PresheafOfModules.InternalHom.instModuleCarrierObjOppositeCommRingCatSubtypePiFamilyMemAddSubgroupNaturalFamilies PresheafOfModules.InternalHom.instModuleCarrierObjOppositeRingCatCompCommRingCatForget₂RingHomCarrierCarrierAbPresheaf PresheafOfModules.InternalHom.instSMulCarrierObjOppositeCommRingCatSubtypePiFamilyMemAddSubgroupNaturalFamilies AlgebraicGeometry.Scheme.Hom.opensMapFinal AlgebraicGeometry.RelPicard.RigidifiedLineBundle.setoid AlgebraicGeometry.RelPicard.RigidifiedLineBundle.instInhabited AlgebraicGeometry.OModulePresheaf.isScalarTower AlgebraicGeometry.Scheme.OrderedAffineCover.instLinearOrder AlgebraicGeometry.OModulePresheaf.module AlgebraicGeometry.Scheme.OrderedAffineCover.instFintype AlgebraicGeometry.Scheme.OrderedAffineCover.instFintypeIdx AlgebraicGeometry.OModulePresheaf.addCommGroup AlgebraicGeometry.Scheme.OrderedAffineCover.instDecidableEqIdx AlgebraicGeometry.OModulePresheaf.moduleSections TwoChartCech.Sections.M0_moduleA TwoChartCech.Sections.M1_module TwoChartCech.Cover.A01_algebra TwoChartCech.Cover.A0_algebra TwoChartCech.Cover.A1_commRing TwoChartCech.Cover.A1_algebra TwoChartCech.Sections.M01_module TwoChartCech.Sections.M0_addCommGroup TwoChartCech.Sections.M0_tower TwoChartCech.Sections.M01_addCommGroup"
p2m_attr_erase "instance" "TwoChartCech.Cover.A0_commRing TwoChartCech.Sections.M1_tower TwoChartCech.Sections.M01_moduleA TwoChartCech.Sections.M0_module TwoChartCech.Sections.M1_moduleA TwoChartCech.Sections.M1_addCommGroup TwoChartCech.Cover.A01_commRing TwoChartCech.Sections.M01_tower CoherentBaseChange.TwoTermComplex.C0_module CoherentBaseChange.TwoTermComplex.C0_addCommGroup CoherentBaseChange.TwoTermComplex.C1_module CoherentBaseChange.TwoTermComplex.C1_addCommGroup CoherentBaseChange.TwoTermComplex.C0_free CoherentBaseChange.TwoTermComplex.C1_finite CoherentBaseChange.TwoTermComplex.C0_finite CoherentBaseChange.TwoTermComplex.C1_free AlgebraicGeometry.OModulePresheaf.instSubsingletonObjZero AlgebraicGeometry.Scheme.Modules.preservesBinaryProducts_opensMap AlgebraicGeometry.Scheme.Modules.pullback_monoidal AlgebraicGeometry.Scheme.Modules.sheafify_isLocalization' AlgebraicGeometry.Scheme.Modules.preservesTerminal_opensMap AlgebraicGeometry.Scheme.Modules.pullback₀_monoidal AlgebraicGeometry.Scheme.Modules.preservesFiniteProducts_opensMap AlgebraicGeometry.Scheme.Modules.instLiftingPresheafOfModulesSheafifyPresheafWOpensCarrierCarrierCommRingCatGrothendieckTopologyObjFunctorOppositeIsSheafSheafCompPullback₀Pullback PresheafOfModules.PullbackMonoidal.pullback_monoidal PresheafOfModules.PullbackMonoidal.isIso_δ PresheafOfModules.pushforward_laxMonoidal PresheafOfModules.PullbackMonoidal.isIso_η PresheafOfModules.free_monoidal PresheafOfModules.restrictScalars_laxMonoidal PresheafOfModules.PullbackMonoidal.isIso_δ_gS PresheafOfModules.pullback_oplaxMonoidal PresheafOfModules.PullbackMonoidal.instPreservesColimitsOfSizeCompOppositeCommRingCatRingCatForget₂RingHomCarrierCarrierPb PresheafOfModules.pullback_monoidal' AlgebraicGeometry.SmoothOfRelativeDimension.fiberToSpecResidueField AlgebraicGeometry.SmoothOfRelativeDimension.pullback_snd AlgebraicGeometry.SmoothOfRelativeDimension.pullback_fst AlgebraicGeometry.SmoothOfRelativeDimension.smooth_one AlgebraicGeometry.SmoothProperCurve.isIntegral_pullback_Spec_field AlgebraicGeometry.IsProper.fiberToSpecResidueField"
p2m_attr_erase "instance" "AlgebraicCurve.CurveModel.isProper AlgebraicCurve.CurveModel.isIntegral AlgebraicCurve.CurveModel.smooth AlgebraicGeometry.Scheme.LocalRepresentabilityULift.instIsLocallyInjectiveFunUliftYonedaGluedToSheaf AlgebraicGeometry.Scheme.LocalRepresentabilityULift.instIsLocallySurjectiveFunUliftYonedaGluedToSheafOfIsLocallySurjectiveZariskiTopologyDescFunctorOppositeType AlgebraicGeometry.Scheme.LocalRepresentabilityULift.instIsOpenImmersionToGlued AlgebraicGeometry.Scheme.LocalRepresentabilityULift.instIsIsoSheafZariskiTopologyTypeUliftYonedaGluedToSheaf AlgebraicGeometry.RelPicard.instIsOpenImmersionToGlued AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.instFundamentalIdentityOfSumRamificationInertia AlgebraicCurve.Place.instIsScalarTowerResidueFieldRestrictPushforward AlgebraicCurve.Place.instAlgebraResidueFieldRestrictPushforward AlgebraicCurve.Place.instIsLocalHomRestrictInclusion AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions PresheafOfModules.ExteriorPower.instModulePresheafAb AlgebraicGeometry.RelEffCartierDiv.subsingleton_of_degree_zero AlgebraicGeometry.RelEffCartierDiv.isIso_subschemeIota_snd_of_degree_one AlgebraicGeometry.isIso_ker_graphOver_subschemeIota_snd AlgebraicGeometry.isClosedImmersion_graphOver AlgebraicGeometry.FGSubalgebra.instIsDirectedLe AlgebraicGeometry.FGSubalgebra.instQuasiSeparatedSpaceCarrierCarrierCommRingCatObjOppositeSchemeSpecDiagram AlgebraicGeometry.FGSubalgebra.instIsCofilteredOpposite AlgebraicGeometry.FGSubalgebra.instIsAffineObjOppositeSchemeSpecDiagram AlgebraicGeometry.FGSubalgebra.instNonempty AlgebraicGeometry.FGSubalgebra.instNonemptySubtypeLeSubalgebraValFG AlgebraicGeometry.FGSubalgebra.instCompactSpaceCarrierCarrierCommRingCatObjOppositeSchemeSpecDiagram AlgebraicGeometry.FGSubalgebra.instIsDirectedSubtypeLeSubalgebraValFG AlgebraicGeometry.FGSubalgebra.instIsAffineHomMapOppositeSchemeSpecDiagram AlgebraicGeometry.FGSubalgebra.instIsFiltered AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instNeg AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instSMulInt AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instAddCommGroup AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instAdd AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instSub"
p2m_attr_erase "instance" "AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instModuleCarrierObjOppositeOpensCarrierCarrierCommRingCatPresheafOpOpensTop AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instSMulCarrierObjOppositeOpensCarrierCarrierCommRingCatPresheafOpOpensTop AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instSMulNat AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instZero AlgebraicCurve.instHasLocalResidue_of_hasCanonicalLocalResidueK AlgebraicCurve.instHasCanonicalLocalResidueK_of_hasCanonicalLocalResidueKStar AlgebraicCurve.Place.kw_ffgc_finiteDimensional_adicCompletion instAlgebraSubtypeMemValuationSubring_definitions AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersIntegersCompletion ModularCurve.KwF4gRRTate.instAlgebraKAdicCompletionIntegers AlgebraicCurve.Place.kw_ffgc_continuousSMul_adicCompletionComap AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersCompletionCompletion IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions AlgebraicCurve.instHasCanonicalLocalResidueK AlgebraicCurve.Place.instAlgebra_restrictResidueField AlgebraicCurve.Place.instIsScalarTower_restrictResidueField AlgebraicCurve.instHasLocalResidue AlgebraicCurve.HasSeparableResidue.of_perfectField_of_isCurveOver AlgebraicCurve.HasSeparableResidue.of_perfectField AlgebraicCurve.Place.instIsLocalHom_restrictSubringHom AlgebraicCurve.instHasCanonicalLocalResidueKStar ModularCurve.KwNo6Pin.isLocalRing_completion SheafOfModules.isIso_ihomModelToIhom AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instDecidableEqIdx AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instFintype AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instLinearOrder AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instFintypeIdx AlgebraicGeometry.OModulePresheaf.Leray.relAltC_scalarTower AlgebraicGeometry.OModulePresheaf.Leray.ker_relAltd_modΓ AlgebraicGeometry.OModulePresheaf.Leray.relAltC_modΓ AlgebraicGeometry.OModulePresheaf.Leray.biC_abGrp AlgebraicGeometry.OModulePresheaf.Leray.relAltH_modΓ AlgebraicGeometry.OModulePresheaf.Leray.ker_relAltd_smul AlgebraicGeometry.OModulePresheaf.Leray.relAltH_scalarTower AlgebraicGeometry.OModulePresheaf.Leray.relAltH_smul"
p2m_attr_erase "instance" "AlgebraicGeometry.OModulePresheaf.Leray.biC_module DoubleComplex.instModuleE₂I DoubleComplex.Bounded.modR DoubleComplex.instModuleE₂II DoubleComplex.instAddCommGroupE₂II DoubleComplex.Bounded.abGrp DoubleComplex.instAddCommGroupE₂I AlgebraicGeometry.ChowDatum.hι_closed AlgebraicGeometry.ChowDatumProj.hιN_closed AlgebraicGeometry.ChowDatumProj.hp_proper AlgebraicGeometry.ChowDatum.hp_isoU AlgebraicGeometry.ChowDatum.hp_proper AlgebraicGeometry.ProjSpace.algebraAway AlgebraicGeometry.ProjSpace.instIsProperProdOverπ AlgebraicGeometry.ChowDatumProj.hp_isoU AlgebraicGeometry.ProjSpace.isProper_π AlgebraicGeometry.ProjSpace.finiteType_mvPolynomial ProjSpaceCech.GradedModule.H.module ProjSpaceCech.GradedModule.H.addCommGroup ProjSpaceCech.GradedModule.sec.instAdd ProjSpaceCech.GradedModule.sec.instNeg ProjSpaceCech.GradedModule.acg ProjSpaceCech.GradedModule.Frac.setoid ProjSpaceCech.GradedModule.modR ProjSpaceCech.GradedModule.sec.instModule ProjSpaceCech.GradedModule.sec.instAddCommGroup ProjSpaceCech.GradedModule.sec.instZero ProjSpaceCech.GradedModule.Presentation.fJ ProjSpaceCech.GradedModule.sec.instSMul ProjSpaceCech.Twist.H.module ProjSpaceCech.Idx.instFintype ProjSpaceCech.Twist.H.addCommGroup ProjSpaceCech.Idx.instDecidableEq ProjSpaceCech.Twist.Mon.instDecidableEq ProjSpaceCech.Twist.cochain.instAddCommGroup ProjSpaceCech.Twist.cochain.instModule AlgebraicGeometry.FGSubalgebra.tensorStage_directedSystem AlgebraicGeometry.RelEffCartierDiv.isClosedImmersion_subschemeι_resProdMap AlgebraicGeometry.RelEffCartierDiv.isOpenImmersion_resProdMap AlgebraicCurve.CurveModel.locallyOfFiniteType_gluedToBase"
p2m_attr_erase "instance" "AlgebraicCurve.CurveModel.isFractionRing_overlap AlgebraicCurve.CurveModel.isLocallyNoetherian_glued AlgebraicCurve.CurveModel.jacobsonSpace_glued AlgebraicCurve.CurveModel.isOpenImmersion_ι₀ AlgebraicCurve.CurveModel.isIntegral_glued AlgebraicCurve.CurveModel.quasiSeparated_gluedToBase AlgebraicCurve.CurveModel.compactSpace_glued AlgebraicCurve.CurveModel.isIntegral_adjoin_chartRing AlgebraicCurve.CurveModel.isFractionRing_overlap_functionField AlgebraicCurve.CurveModel.isProper_gluedToBase AlgebraicCurve.CurveModel.isOpenImmersion_ιU AlgebraicCurve.CurveModel.isOpenImmersion_f₀ AlgebraicCurve.CurveModel.isOpenImmersion_fInf AlgebraicCurve.CurveModel.isOpenImmersion_ιInf AlgebraicCurve.CurveModel.algebra_overlap_functionField AlgebraicCurve.CurveModel.quasiCompact_gluedToBase AlgebraicCurve.CurveModel.algebraAdjoin AlgebraicCurve.CurveModel.isDedekindDomain_chartRing AlgebraicCurve.CurveModel.isIntegralClosure AlgebraicCurve.CurveModel.finite_chartRing AlgebraicCurve.CurveModel.centre_isPrime AlgebraicCurve.CurveModel.isFractionRing_chartRing AlgebraicCurve.CurveModel.finiteType_chartRing AlgebraicCurve.CurveModel.isNoetherianRing_chartRing AlgebraicCurve.CurveModel.isScalarTower_base_adjoin AlgebraicCurve.CurveModel.isScalarTower_adjoin AlgebraicCurve.CurveModel.chartRing_finitePresentation instTopologicallyFGOfFiniteType AlgebraicGeometry.ProjSpace.twistObj.addCommGroup AlgebraicGeometry.ProjSpace.twistFam.module AlgebraicGeometry.ProjSpace.twistObj.module AlgebraicGeometry.ProjSpace.twistObj.moduleSections AlgebraicGeometry.ProjSpace.twistFam.addCommGroup kmfloorsGlue_int_three_isPrime kmfloorsGlue_int_bot_isPrime"
p2m_attr_erase "simp" "GoodReductionJacobian.RelativeGroupLaw.fibre_inv GoodReductionJacobian.RelativeGroupLaw.fibrePointToBase_coe GoodReductionJacobian.RelativeGroupLaw.fibrePointOfBase_toBase GoodReductionJacobian.RelativeGroupLaw.fibre_mul GoodReductionJacobian.RelativeGroupLaw.fibrePointToBase_ofBase GoodReductionJacobian.RelativeGroupLaw.fibre_one GoodReductionJacobian.RelativeGroupLaw.fibrePointOfBase_coe AlgebraicGeometry.schemeFibreEndo_snd AlgebraicGeometry.schemeFibreEndo_fst GoodReductionJacobian.RelativeGroupLaw.baseChangePointToBase_ofBase GoodReductionJacobian.RelativeGroupLaw.baseChangePointToBase_coe GoodReductionJacobian.RelativeGroupLaw.baseChangePointOfBase_coe GoodReductionJacobian.RelativeGroupLaw.baseChange_inv GoodReductionJacobian.RelativeGroupLaw.baseChangePointOfBase_toBase GoodReductionJacobian.RelativeGroupLaw.baseChange_mul GoodReductionJacobian.RelativeGroupLaw.baseChange_one NeronModelInfra.NeronModelPropertyBundle.endExtensionEquiv_symm_restrict NeronModelInfra.schemeHomOverComp_id_left NeronModelInfra.schemeHomOverComp_id_right NeronModelInfra.schemeHomOverId_coe NeronModelInfra.NeronModelPropertyBundle.endExtensionEquiv_apply NeronModelInfra.NeronModelPropertyBundle.restrict_endExtensionEquiv_symm NeronModelInfra.schemeHomOverComp_coe NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_fst NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_snd NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_fst NeronSpecialFibreInfra.neronEndRestrictEquiv_apply NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_fst_assoc NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_snd NeronSpecialFibreInfra.neronEndExtension_genericFibreRestrict NeronSpecialFibreInfra.specClosedFibreInclusion_eq NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_fst_assoc NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_snd_assoc NeronSpecialFibreInfra.genericFibreRestrict_neronEndExtension NeronSpecialFibreInfra.homOverId_coe NeronSpecialFibreInfra.homOverComp_coe NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_snd_assoc NeronModelInfra.schemeHomOverNpow_succ NeronModelInfra.schemeHomOverNpow_zero GoodReductionJacobian.relativeGroupLawOfGrpObj_inv"
p2m_attr_erase "simp" "GoodReductionJacobian.relativeGroupLawOfGrpObj_mul GoodReductionJacobian.overHomEquivSchemeHomOver_apply_coe GoodReductionJacobian.relativeGroupLawOfGrpObj_one GoodReductionJacobian.overHomEquivSchemeHomOver_symm_apply_left SheafOfModules.tensorUnit_eq AlgebraicGeometry.Scheme.Modules.tensorUnit_eq PresheafOfModules.InternalHom.presheaf_map_apply PresheafOfModules.InternalHom.curryFamily_app PresheafOfModules.InternalHom.add_app PresheafOfModules.InternalHom.smul_app PresheafOfModules.InternalHom.zero_app PresheafOfModules.ihomObj_map_val PresheafOfModules.ihomFunctor_map PresheafOfModules.InternalHom.restrict_app PresheafOfModules.InternalHom.postcomp_app PresheafOfModules.InternalHom.neg_app PresheafOfModules.curry'_app_val PresheafOfModules.InternalHom.presheaf_obj PresheafOfModules.ihomFunctor_obj PresheafOfModules.ihomObj_obj PresheafOfModules.InternalHom.sub_app PresheafOfModules.ihomMap_app_val AlgebraicGeometry.Scheme.Modules.tensorPow_zero AlgebraicGeometry.Scheme.Modules.tensorPow_succ AlgebraicGeometry.RelPicard.RigidifiedLineBundle.mk.sizeOf_spec AlgebraicGeometry.RelPicard.RigidifiedLineBundle.mk.injEq AlgebraicGeometry.Scheme.OrderedAffineCover.mk.injEq AlgebraicGeometry.OModulePresheaf.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCover.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.mk.injEq AlgebraicGeometry.Scheme.TwoAffineOpenCover.mk.injEq AlgebraicGeometry.Scheme.TwoAffineOpenCover.mk.sizeOf_spec AlgebraicGeometry.Scheme.TwoAffineOpenCover.pullback_U1 AlgebraicGeometry.Scheme.TwoAffineOpenCover.pullback_U0 TwoChartCech.Sections.mk.injEq TwoChartCech.Cover.mk.injEq TwoChartCech.GrothendieckComplex.mk.injEq TwoChartCech.Sections.mk.sizeOf_spec TwoChartCech.Cover.mk.sizeOf_spec TwoChartCech.Cover.lineBundle_r0_apply"
p2m_attr_erase "simp" "TwoChartCech.GrothendieckComplex.mk.sizeOf_spec TwoChartCech.Cover.lineBundle_r1_apply CoherentBaseChange.TwoTermComplex.mk.sizeOf_spec CoherentBaseChange.TwoTermComplex.mk.injEq AlgebraicGeometry.OModulePresheaf.prod_obj AlgebraicGeometry.OModulePresheaf.restrOpen_obj AlgebraicGeometry.OModulePresheaf.DevissageStep.mk.injEq AlgebraicGeometry.OModulePresheaf.pushforward_obj AlgebraicGeometry.OModulePresheaf.im_obj AlgebraicGeometry.OModulePresheaf.pow_obj AlgebraicGeometry.OModulePresheaf.fstHom_app AlgebraicGeometry.OModulePresheaf.ker_obj AlgebraicGeometry.OModulePresheaf.coker_obj AlgebraicGeometry.OModulePresheaf.DevissageStep.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCover.preimage_U AlgebraicGeometry.OModulePresheaf.sndHom_app AlgebraicGeometry.OModulePresheaf.Hom.mk.injEq AlgebraicGeometry.OModulePresheaf.Hom.id_app AlgebraicGeometry.OModulePresheaf.AffHom.appSections_apply AlgebraicGeometry.OModulePresheaf.AffHom.comp_app AlgebraicGeometry.OModulePresheaf.AffSES.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.AffHom.kerMap_coe AlgebraicGeometry.OModulePresheaf.AffHom.id_app AlgebraicGeometry.OModulePresheaf.Hom.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.Hom.toAffHom_app AlgebraicGeometry.OModulePresheaf.SES.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.AffHom.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.Hom.comp_app AlgebraicGeometry.OModulePresheaf.SES.mk.injEq AlgebraicGeometry.OModulePresheaf.AffHom.mk.injEq AlgebraicGeometry.OModulePresheaf.Hom.appSections_apply AlgebraicGeometry.OModulePresheaf.AffSES.mk.injEq PresheafOfModules.freeεIso_hom_app PresheafOfModules.freeμIso_hom_app AlgebraicGeometry.RelPicard.RepresentsRelSubPic.mk.injEq AlgebraicGeometry.RelPicard.SubPicCondition.mk.injEq AlgebraicGeometry.RelPicard.SubPicCondition.mk.sizeOf_spec AlgebraicGeometry.RelPicard.RepresentsRelSubPic.mk.sizeOf_spec AlgebraicGeometry.SmoothProperCurve.sectionBaseChange_coe_snd AlgebraicGeometry.SmoothProperCurve.sectionBaseChange_coe_fst"
p2m_attr_erase "simp" "AlgebraicCurve.CurveModel.mk.injEq AlgebraicCurve.CurveModel.mk.sizeOf_spec AlgebraicCurve.mulAdele_apply AlgebraicCurve.residuePairing_apply_coe AlgebraicCurve.mem_adeleBdd AlgebraicCurve.weilSmul_one AlgebraicCurve.diagonalHom_apply AlgebraicCurve.weilSmul_apply AlgebraicCurve.adeleSpaceMul_coe AlgebraicCurve.mulAdele_one AlgebraicGeometry.SmoothProperCurve.FiniteMapData.twoAffineOpenCover_U1 AlgebraicGeometry.SmoothProperCurve.FiniteMapData.mk.injEq AlgebraicGeometry.SmoothProperCurve.FiniteMapData.mk.sizeOf_spec AlgebraicGeometry.SmoothProperCurve.FiniteMapData.twoAffineOpenCover_U0 AlgebraicGeometry.RelPicard.SubPicCondition.onClasses_mk AlgebraicGeometry.RelPicard.relSubPicPresheaf_map_coe CategoryTheory.Functor.OverTotal.ofFibre_fst CategoryTheory.Functor.overTotal_map_fst AlgebraicGeometry.Scheme.LocalRepresentabilityULift.glueData_J AlgebraicGeometry.Scheme.LocalRepresentabilityULift.uliftYoneda_toGlued_uliftYonedaGluedToSheaf AlgebraicGeometry.Scheme.LocalRepresentabilityULift.glueData_t' AlgebraicGeometry.Scheme.LocalRepresentabilityULift.uliftYoneda_toGlued_uliftYonedaGluedToSheaf_assoc AlgebraicGeometry.Scheme.LocalRepresentabilityULift.uliftYonedaGluedToSheaf_app_toGlued AlgebraicGeometry.Scheme.LocalRepresentabilityULift.glueData_openCover_map AlgebraicGeometry.Scheme.LocalRepresentabilityULift.uliftYonedaGluedToSheaf_app_comp AlgebraicGeometry.Scheme.LocalRepresentabilityULift.glueData_V AlgebraicGeometry.Scheme.LocalRepresentabilityULift.glueData_t AlgebraicGeometry.Scheme.LocalRepresentabilityULift.glueData_U AlgebraicGeometry.Scheme.LocalRepresentabilityULift.glueData_f AlgebraicGeometry.RelPicard.designationOfRepresentableBy_P AlgebraicGeometry.RelPicard.designationOfRepresentableBy_toBase AlgebraicGeometry.RelPicard.rigSection_snd AlgebraicGeometry.RelPicard.RigidifiedLineBundle.ofInvertible_L AlgebraicGeometry.RelPicard.rigSection_snd_assoc AlgebraicGeometry.RelPicard.SubPicGroupCondition.mk.injEq AlgebraicGeometry.RelPicard.SubPicGroupCondition.mk.sizeOf_spec AlgebraicCurve.coe_cechH0Equiv_apply AlgebraicCurve.cechH1ToH1_mk AlgebraicCurve.lSpaceOn_univ AlgebraicCurve.lSpaceOn_empty"
p2m_attr_erase "simp" "AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.Divisor.mapRestrict_single AlgebraicCurve.Divisor.pushforward_single AlgebraicCurve.Place.coe_restrictInclusion AlgebraicCurve.Place.mem_fiber AlgebraicCurve.Place.restrict_toValuationSubring AlgebraicCurve.Divisor.degree_pushforward AlgebraicCurve.Place.restrictResidueMap_residue AlgebraicCurve.Pic0.coe_pushforwardDegZeroHom AlgebraicCurve.Pic0.coe_pullbackDegZeroHom AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Divisor.degree_pushforwardAlong AlgebraicCurve.Pic0.coe_degZeroCorrespondence AlgebraicCurve.Place.mem_fiberAlong AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero"
p2m_attr_erase "simp" "ModularCurve.jqNModC_one ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one AlgebraicCurve.Place.differentialCoeff_zero AlgebraicCurve.Place.differentialCoeff_dCoord AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.injEq AlgebraicCurve.TranscendenceTower.mk.injEq AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec AlgebraicCurve.PoleDivisorPackage.mk.injEq AlgebraicGeometry.RelPicard.thetaBundle_def AlgebraicGeometry.RelPicard.picardBundle_def AlgebraicGeometry.RelEffCartierDiv.toRelEffDivisor_ofRelEffDivisor AlgebraicGeometry.RelEffCartierDiv.toRelEffDivisor_I AlgebraicGeometry.mapOnProdOver_fst_assoc AlgebraicGeometry.RelEffCartierDiv.mk.sizeOf_spec AlgebraicGeometry.RelEffCartierDiv.mk.injEq AlgebraicGeometry.mapOnProdOver_snd AlgebraicGeometry.mapOnProdOver_fst AlgebraicGeometry.mapOnProdOver_snd_assoc AlgebraicGeometry.mapOnProdOver_id AlgebraicCurve.RelEffDivisor.mk.sizeOf_spec AlgebraicCurve.mapOnProd_fst AlgebraicCurve.mapOnProd_fst_assoc AlgebraicCurve.mapOnProd_snd AlgebraicCurve.UnivDivisorPack.mk.injEq AlgebraicCurve.RelEffDivisor.mk.injEq"
p2m_attr_erase "simp" "AlgebraicCurve.UnivDivisorPack.mk.sizeOf_spec AlgebraicCurve.mapOnProd_snd_assoc AlgebraicGeometry.Scheme.Modules.exteriorPower_obj PresheafOfModules.exteriorPower_map_ιMulti PresheafOfModules.ExteriorPower.appₗ_apply AlgebraicGeometry.prodKerGraph_one AlgebraicGeometry.fibrePowOver.proj_comp AlgebraicGeometry.prodKerGraph_zero AlgebraicGeometry.RelEffCartierDiv.empty_I AlgebraicGeometry.fibrePowOver.proj_comp_assoc AlgebraicGeometry.graphOver_fst_assoc AlgebraicGeometry.RelEffCartierDiv.toPoint_comp AlgebraicGeometry.RelEffCartierDiv.toPoint_comp_assoc AlgebraicGeometry.graphOver_fst AlgebraicGeometry.RelEffCartierDiv.ofPoint_I AlgebraicGeometry.graphOver_snd AlgebraicGeometry.graphOver_snd_assoc AlgebraicCurve.SymmetricPowerPackage.mk.sizeOf_spec AlgebraicCurve.SymmetricPowerPackage.mk.injEq AlgebraicGeometry.FGSubalgebra.cocone_ι_app_apply AlgebraicGeometry.RelPicard.fst_toProdSpec AlgebraicGeometry.RelPicard.toProdSpec_fst_assoc AlgebraicGeometry.RelPicard.pointsSubBasepointModule_cons AlgebraicGeometry.RelPicard.pointsSubBasepointModule_nil AlgebraicGeometry.RelPicard.fst_toProdSpec_assoc AlgebraicGeometry.RelPicard.toProdSpec_fst AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.sub_app AlgebraicGeometry.Scheme.IdealSheafData.sres_sresTop AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.add_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.mk.sizeOf_spec AlgebraicGeometry.Scheme.IdealSheafData.coe_resLE AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.smul_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.coe_ofLE_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.ideal_range AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.zero_app AlgebraicGeometry.Scheme.IdealSheafData.sres_sres AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.comp_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.neg_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.id_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.coe_mulRight_app"
p2m_attr_erase "simp" "AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.nsmul_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.mk.injEq AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.zsmul_app AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.sizeOf_spec AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.injEq AlgebraicCurve.adeleSingle_coe AlgebraicCurve.kaehlerResidueTermKFam_apply AlgebraicCurve.Place.LocalResidueData.mk.injEq AlgebraicCurve.Place.LocalResidueData.mk.sizeOf_spec AlgebraicCurve.Place.kw_ffgc_adicCompletionComapIntegers_coe AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.sizeOf_spec AlgebraicCurve.Place.mem_simplePoleSubmodule AlgebraicCurve.Place.coe_uniformizerSubring ModularCurve.Lg37.Lg37CompletionSection.mk.injEq AlgebraicCurve.Place.CoefficientFieldSection.mk.injEq AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.injEq ModularCurve.Lg37.Lg37CompletionSection.mk.sizeOf_spec AlgebraicCurve.Place.CoefficientFieldSection.mk.sizeOf_spec AlgebraicCurve.Place.poleSubmodule_one AlgebraicCurve.Place.mem_poleSubmodule AlgebraicGeometry.Scheme.Modules.toUnitSection_ofUnitSection AlgebraicGeometry.Scheme.Modules.pullbackSection_def AlgebraicGeometry.Scheme.Modules.ofUnitSection_toUnitSection PresheafOfModules.InternalHom.IsSheafAux.appAt_toPresheafHom SheafOfModules.ihomSectionsEquivFamily_unit AlgebraicGeometry.Scheme.Modules.restrictHomEquivFamily_apply SheafOfModules.ihomEval_unit_app AlgebraicGeometry.Scheme.Modules.ihomEval_zero_right AlgebraicGeometry.Scheme.Modules.ihomEval_zero_left AlgebraicGeometry.Scheme.Modules.homOfFamily_app_apply SheafOfModules.unit_ihomSectionsEquivFamily AlgebraicGeometry.Scheme.Modules.familyOfHom_app AlgebraicGeometry.Scheme.Modules.restrictUnitIso_hom_app_apply AlgebraicGeometry.Scheme.Modules.restrictUnitIso_inv_app_apply AlgebraicGeometry.Scheme.Modules.restrictHomOfFamily_app_apply AlgebraicGeometry.Scheme.Modules.restrictHomEquivFamily_symm_apply AlgebraicGeometry.Scheme.Modules.tensorSections_zero_right AlgebraicGeometry.Scheme.Modules.map_unitSection AlgebraicGeometry.Scheme.Modules.tensorSectionsBilin_apply AlgebraicGeometry.Scheme.Modules.tensorPowSection_zero"
p2m_attr_erase "simp" "AlgebraicGeometry.Scheme.Modules.tensorSections_zero_left AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_neg AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_zero AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_sub AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_add AlgebraicGeometry.Scheme.OrderedAffineCover.toCoverOf_U AlgebraicGeometry.Scheme.OrderedAffineCoverOf.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCoverOf.mk.injEq AlgebraicGeometry.Scheme.OrderedAffineCover.restrict_U AlgebraicGeometry.OModulePresheaf.Leray.restrictToPreimage_U DoubleComplex.Bounded.mk.injEq DoubleComplex.Bounded.mk.sizeOf_spec DoubleComplex.Convergence.mk.injEq DoubleComplex.Convergence.mk.sizeOf_spec DoubleComplex.SubQuot.mk.sizeOf_spec DoubleComplex.SubQuot.mk.injEq AlgebraicGeometry.ChowDatumProj.mk.sizeOf_spec AlgebraicGeometry.ChowDatum.mk.sizeOf_spec AlgebraicGeometry.ChowDatumProj.mk.injEq AlgebraicGeometry.ChowDatum.mk.injEq ProjSpaceCech.GradedModule.mk.injEq ProjSpaceCech.GradedModule.mk.sizeOf_spec ProjSpaceCech.GradedModule.Frac.mk.sizeOf_spec ProjSpaceCech.GradedModule.Presentation.mk.injEq ProjSpaceCech.GradedModule.Frac.mk.injEq ProjSpaceCech.GradedModule.Presentation.mk.sizeOf_spec ProjSpaceCech.GradedModule.Hom.shift_toLinearMap ProjSpaceCech.GradedModule.Hom.mk.sizeOf_spec ProjSpaceCech.GradedModule.Hom.mk.injEq TwoChartCech.Mumford.dK_apply TwoChartCech.Mumford.ι0_apply TwoChartCech.Mumford.ι1_apply TwoChartCech.KerCoprod.dK_apply TwoChartCech.KerCoprod.ι1_apply TwoChartCech.KerCoprod.ι0_apply AlgebraicGeometry.tilde.functorCompPullbackSpecIso_app AlgebraicGeometry.RelPicard.algEquivZeroGroupCut_toSubPicCondition AlgebraicGeometry.RelPicard.LFP.stageHom_val AlgebraicGeometry.RelPicard.BaseChange.relSubPicPresheafRestrictIso_hom_app_coe AlgebraicGeometry.RelPicard.BaseChange.relSubPicPresheafRestrictIso_inv_app_coe"
p2m_attr_erase "simp" "AlgebraicGeometry.RelPicard.BaseChange.restrict_P AlgebraicGeometry.RelEffCartierDiv.IsUniversal.lift_comp AlgebraicGeometry.RelEffCartierDiv.functor_map_fst AlgebraicGeometry.RelEffCartierDiv.IsUniversal.homEquiv_apply AlgebraicGeometry.RelEffCartierDiv.IsUniversal.lift_pullbackAlong AlgebraicGeometry.RelEffCartierDiv.IsUniversal.homEquiv_symm_apply AlgebraicGeometry.RelEffCartierDiv.IsUniversal.lift_comp_assoc AlgebraicGeometry.RelEffCartierDiv.supportedIn_top AlgebraicGeometry.RelEffCartierDiv.mem_supportedIn_iff AlgebraicGeometry.RelEffCartierDiv.supportedIn_top_eq AlgebraicGeometry.RelEffCartierDiv.restrictAlong_extendAlong AlgebraicGeometry.RelEffCartierDiv.extendAlong_I AlgebraicGeometry.RelEffCartierDiv.resProdMap_snd AlgebraicGeometry.RelEffCartierDiv.restrictAlong_I AlgebraicGeometry.RelEffCartierDiv.extendAlong_restrictAlong AlgebraicGeometry.RelEffCartierDiv.resProdMap_fst_assoc AlgebraicGeometry.RelEffCartierDiv.resProdMap_snd_assoc AlgebraicGeometry.RelEffCartierDiv.resProdMap_fst CoherentBaseChange.FibreH0Family.mk.sizeOf_spec CoherentBaseChange.FibreH0Family.mk.injEq AlgebraicGeometry.Scheme.Modules.ProjPresentation.mk.injEq AlgebraicGeometry.Scheme.Modules.ProjPresentation.mk.sizeOf_spec AlgebraicCurve.CurveModel.coe_gInf AlgebraicCurve.CurveModel.coe_tInvChart AlgebraicCurve.CurveModel.ιInf_gluedToBase_assoc AlgebraicCurve.CurveModel.ιInf_gluedToBase AlgebraicCurve.CurveModel.primeOfι₀_asIdeal AlgebraicCurve.CurveModel.coe_tChart AlgebraicCurve.CurveModel.ι₀_gluedToBase_assoc AlgebraicCurve.CurveModel.primeOfιInf_asIdeal AlgebraicCurve.CurveModel.ι₀_gluedToBase AlgebraicCurve.CurveModel.coe_tma AlgebraicCurve.CurveModel.coe_primeEquivChartPlaces RegularLocalRingQuotientAscent.dualNumberFst_apply AlgebraicGeometry.ProjSpace.twistObj.mk.injEq AlgebraicGeometry.ProjSpace.twistObj.zero_val AlgebraicGeometry.ProjSpace.twistObj.add_val AlgebraicGeometry.ProjSpace.twist_res_val AlgebraicGeometry.ProjSpace.twist_smul_val AlgebraicGeometry.ProjSpace.twistGradeToObj_val"
p2m_attr_erase "simp" "AlgebraicGeometry.ProjSpace.twistObj.smul_val AlgebraicGeometry.ProjSpace.twistGradeEquiv_apply_val AlgebraicGeometry.ProjSpace.twistObj.mk.sizeOf_spec QuaternionAlgebra.ClassSet.map_mk QuaternionAlgebra.baseChangeRight_tmul QuaternionAlgebra.mapOfAlgebraMapEq_apply QuaternionAlgebra.baseChange_tmul"

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian QuaternionAlgebra IsDedekindDomain CerednikDrinfeld CerednikDrinfeld.QM
open scoped Quaternion TensorProduct NumberField

namespace XLKC1

variable {k : Type} [Field k] {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} {N : ℕ} (E : FakeEllipticCurve Λ N k)

theorem nsmulPt_eq_nsmul {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of k)) (n : ℕ) (P : SchemeHomOver t E.f) :
    nsmulPt E.L t n P = E.L.nsmul t n P := by
  induction n with
  | zero => rfl
  | succ n ih => rw [RelativeGroupLaw.nsmul_succ, ← ih]; rfl

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
    pushPt (E.act ⟨((m : ℤ) : ℚ), hΛℤ m⟩) (E.act_over _) P = E.L.nsmul t m P := by
  induction m with
  | zero =>
    have e : (⟨(((0 : ℕ) : ℤ) : ℚ), hΛℤ 0⟩ : ↥Λ) = ⟨0, by simpa using hΛℤ 0⟩ := by apply Subtype.ext; simp
    rw [e, pushPt_act_zero, RelativeGroupLaw.nsmul_zero]
  | succ m ih =>
    have e : (⟨(((m + 1 : ℕ) : ℤ) : ℚ), hΛℤ (m + 1 : ℕ)⟩ : ↥Λ) =
        ⟨((m : ℤ) : ℚ), hΛℤ m⟩ + ⟨((1 : ℤ) : ℚ), hΛℤ 1⟩ := by
      apply Subtype.ext; push_cast; simp
    rw [e, E.act_add, ih, RelativeGroupLaw.nsmul_succ]
    congr 1
    have e1 : (⟨((1 : ℤ) : ℚ), hΛℤ 1⟩ : ↥Λ) = ⟨1, by simpa using hΛℤ 1⟩ := by apply Subtype.ext; simp
    rw [e1]
    apply Subtype.ext; rw [mapPt_coe, E.act_one]; exact Category.comp_id _

theorem pushPt_act_natCast' (hΛℤ : ∀ m : ℤ, ((m : ℚ) : ℍ[ℚ, a, b]) ∈ Λ) (m : ℕ)
    {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of k)) (P : SchemeHomOver t E.f) :
    mapPt (E.act ⟨((m : ℤ) : ℚ), hΛℤ m⟩) (E.act_over _) P = nsmulPt E.L t m P := by
  rw [nsmulPt_eq_nsmul]; exact pushPt_act_natCast E hΛℤ m t P

theorem mapPt_one {E' : FakeEllipticCurve Λ N k} (φ : E.A ⟶ E'.A) (hφ : φ ≫ E'.f = E.f)
    (hφ_hom : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of k)) (P Q : SchemeHomOver t E.f),
      mapPt φ hφ (E.L.mul t P Q) = E'.L.mul t (mapPt φ hφ P) (mapPt φ hφ Q))
    {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of k)) : mapPt φ hφ (E.L.one t) = E'.L.one t := by
  letI := E'.L.pointGroup t
  have h := hφ_hom t (E.L.one t) (E.L.one t)
  rw [E.L.one_mul] at h
  have h' : (mapPt φ hφ (E.L.one t) : SchemeHomOver t E'.f) = mapPt φ hφ (E.L.one t) * mapPt φ hφ (E.L.one t) := h
  exact mul_eq_left.mp h'.symm

theorem mapPt_nsmulPt {E' : FakeEllipticCurve Λ N k} (φ : E.A ⟶ E'.A) (hφ : φ ≫ E'.f = E.f)
    (hφ_hom : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of k)) (P Q : SchemeHomOver t E.f),
      mapPt φ hφ (E.L.mul t P Q) = E'.L.mul t (mapPt φ hφ P) (mapPt φ hφ Q))
    {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of k)) (n : ℕ) (P : SchemeHomOver t E.f) :
    mapPt φ hφ (nsmulPt E.L t n P) = nsmulPt E'.L t n (mapPt φ hφ P) := by
  induction n with
  | zero => exact mapPt_one E φ hφ hφ_hom t
  | succ n ih => simp only [nsmulPt]; rw [hφ_hom, ih]

theorem mapPt_comp {A₁ A₂ A₃ : Scheme.{0}} {f₁ : A₁ ⟶ Spec (CommRingCat.of k)} {f₂ : A₂ ⟶ Spec (CommRingCat.of k)}
    {f₃ : A₃ ⟶ Spec (CommRingCat.of k)} (φ : A₁ ⟶ A₂) (hφ : φ ≫ f₂ = f₁) (ψ : A₂ ⟶ A₃) (hψ : ψ ≫ f₃ = f₂)
    (h : (φ ≫ ψ) ≫ f₃ = f₁) {T : Scheme.{0}} {t : T ⟶ Spec (CommRingCat.of k)} (P : SchemeHomOver t f₁) :
    mapPt (φ ≫ ψ) h P = mapPt ψ hψ (mapPt φ hφ P) :=
  Subtype.ext (by simp only [mapPt_coe, Category.assoc])

abbrev Pt := SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) E.f

@[reducible] noncomputable def ptCommGroup : CommGroup (Pt E) :=
  { E.L.pointGroup (𝟙 (Spec (CommRingCat.of k))) with mul_comm := fun x y => E.comm _ x y }

attribute [local instance] ptCommGroup

theorem nsmulPt_eq_pow (n : ℕ) (P : Pt E) : nsmulPt E.L (𝟙 _) n P = P ^ n := by
  induction n with
  | zero => rw [pow_zero]; rfl
  | succ n ih => rw [pow_succ]; simp only [nsmulPt]; rw [ih]; rfl

noncomputable def ρ (x : ↥Λ) : Pt E →* Pt E where
  toFun P := pushPt (E.act x) (E.act_over x) P
  map_one' := mapPt_one E (E.act x) (E.act_over x) (E.act_hom x) _
  map_mul' P Q := E.act_hom x _ P Q

theorem ρ_apply (x : ↥Λ) (P : Pt E) : ρ E x P = pushPt (E.act x) (E.act_over x) P := rfl

theorem ρ_one (h1 : (1 : ℍ[ℚ, a, b]) ∈ Λ) : ρ E ⟨1, h1⟩ = MonoidHom.id (Pt E) := by
  ext P
  show (P.1 ≫ E.act ⟨1, h1⟩) = P.1
  rw [E.act_one]; exact Category.comp_id _

theorem ρ_mul (x y : ↥Λ) (h : (x : ℍ[ℚ, a, b]) * (y : ℍ[ℚ, a, b]) ∈ Λ) :
    ρ E ⟨(x : ℍ[ℚ, a, b]) * (y : ℍ[ℚ, a, b]), h⟩ = (ρ E x).comp (ρ E y) := by
  ext P
  show P.1 ≫ E.act ⟨(x : ℍ[ℚ, a, b]) * (y : ℍ[ℚ, a, b]), h⟩ = (P.1 ≫ E.act y) ≫ E.act x
  rw [E.act_mul x y h, Category.assoc]

theorem ρ_add (x y : ↥Λ) (P : Pt E) : ρ E (x + y) P = ρ E x P * ρ E y P := E.act_add x y _ P

end XLKC1

namespace XLKC1

variable {k : Type} [Field k] {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} {N : ℕ} (E : FakeEllipticCurve Λ N k)

attribute [local instance] ptCommGroup

theorem mapPt_id {T : Scheme.{0}} {t : T ⟶ Spec (CommRingCat.of k)} (P : SchemeHomOver t E.f) :
    mapPt (𝟙 E.A) (Category.id_comp E.f) P = P :=
  Subtype.ext (by rw [mapPt_coe]; exact Category.comp_id _)

theorem act_comm_natCast (hΛℤ : ∀ m : ℤ, ((m : ℚ) : ℍ[ℚ, a, b]) ∈ Λ) (hO : IsOrder Λ) (n : ℕ) (x : ↥Λ) :
    E.act x ≫ E.act ⟨((n : ℤ) : ℚ), hΛℤ n⟩ = E.act ⟨((n : ℤ) : ℚ), hΛℤ n⟩ ≫ E.act x := by
  have h1 : (((n : ℤ) : ℚ) : ℍ[ℚ, a, b]) * (x : ℍ[ℚ, a, b]) ∈ Λ := hO.mul_mem (hΛℤ n) x.2
  have h2 : (x : ℍ[ℚ, a, b]) * (((n : ℤ) : ℚ) : ℍ[ℚ, a, b]) ∈ Λ := hO.mul_mem x.2 (hΛℤ n)
  rw [← E.act_mul ⟨((n : ℤ) : ℚ), hΛℤ n⟩ x h1, ← E.act_mul x ⟨((n : ℤ) : ℚ), hΛℤ n⟩ h2]
  congr 1; apply Subtype.ext
  show (((n : ℤ) : ℚ) : ℍ[ℚ, a, b]) * (x : ℍ[ℚ, a, b]) = (x : ℍ[ℚ, a, b]) * (((n : ℤ) : ℚ) : ℍ[ℚ, a, b])
  exact QuaternionAlgebra.coe_commutes _ _

theorem exists_isIsogenyPair_of_forall_point [IsAlgClosed k]
    (hΛℤ : ∀ m : ℤ, ((m : ℚ) : ℍ[ℚ, a, b]) ∈ Λ) (hO : IsOrder Λ) (ℓ : ℕ) (hℓk : (ℓ : k) ≠ 0) (d : ℕ)
    (g g' : E.A ⟶ E.A) (hg : g ≫ E.f = E.f) (hg' : g' ≫ E.f = E.f)
    (hg_hom : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of k)) (P Q : SchemeHomOver t E.f),
      mapPt g hg (E.L.mul t P Q) = E.L.mul t (mapPt g hg P) (mapPt g hg Q))
    (hg'_hom : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of k)) (P Q : SchemeHomOver t E.f),
      mapPt g' hg' (E.L.mul t P Q) = E.L.mul t (mapPt g' hg' P) (mapPt g' hg' Q))
    (hg_lin : ∀ m : ↥Λ, E.act m ≫ g = g ≫ E.act m) (hg'_lin : ∀ m : ↥Λ, E.act m ≫ g' = g' ≫ E.act m)
    (hgg' : g ≫ g' = E.act ⟨(((d * ℓ : ℕ) : ℤ) : ℚ), hΛℤ _⟩) (hg'g : g' ≫ g = E.act ⟨(((d * ℓ : ℕ) : ℤ) : ℚ), hΛℤ _⟩)
    (hkill : ∀ P : Pt E, nsmulPt E.L (𝟙 _) ℓ P = E.L.one (𝟙 _) → mapPt g hg P = E.L.one (𝟙 _)) :
    ∃ ψ : E.A ⟶ E.A, FakeEllipticCurve.IsIsogenyPair d E E g' ψ := by

  have hkillT : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of k)) (P : SchemeHomOver t E.f),
      nsmulPt E.L t ℓ P = E.L.one t → mapPt g hg P = E.L.one t := by
    intro T t P hP
    exact CerednikDrinfeld.QM.FakeEllipticCurve.forall_mapPt_eq_one_of_forall_rationalPoint k E E E ℓ hℓk
      (E.act ⟨((ℓ : ℤ) : ℚ), hΛℤ ℓ⟩) (E.act_over _) (E.act_hom _)
      (fun x => act_comm_natCast E hΛℤ hO ℓ x)
      (𝟙 E.A) (Category.id_comp E.f)
      (fun t P => by rw [mapPt_id, pushPt_act_natCast' E hΛℤ ℓ t P])
      (fun t Q => by rw [mapPt_id, pushPt_act_natCast' E hΛℤ ℓ t Q])
      g hg
      (fun P hP => hkill P (by rw [← pushPt_act_natCast' E hΛℤ ℓ _ P]; exact hP))
      t P (by rw [pushPt_act_natCast' E hΛℤ ℓ t P]; exact hP)

  obtain ⟨ψ, hψ, hψ_hom, hψ_lin, hgψ⟩ :=
    CerednikDrinfeld.QM.FakeEllipticCurve.exists_eq_act_comp_of_forall_nsmulPt_eq_one_imp_mapPt_eq_one hΛℤ k E ℓ hℓk g hg
      hg_hom hg_lin hkillT

  have hℓ0 : (ℓ : ℤ) ≠ 0 := by exact_mod_cast (show ℓ ≠ 0 by rintro rfl; exact hℓk (by simp))
  haveI : Epi (E.act ⟨((ℓ : ℤ) : ℚ), hΛℤ ℓ⟩) :=
    CerednikDrinfeld.QM.FakeEllipticCurve.epi_act_of_ne_zero hΛℤ k E (ℓ : ℤ) hℓ0
  have hdℓmem : (((d : ℤ) : ℚ) : ℍ[ℚ, a, b]) * (((ℓ : ℤ) : ℚ) : ℍ[ℚ, a, b]) ∈ Λ := hO.mul_mem (hΛℤ d) (hΛℤ ℓ)
  have hsplit : E.act ⟨(((d * ℓ : ℕ) : ℤ) : ℚ), hΛℤ _⟩ = E.act ⟨((ℓ : ℤ) : ℚ), hΛℤ ℓ⟩ ≫ E.act ⟨((d : ℤ) : ℚ), hΛℤ d⟩ := by
    rw [← E.act_mul ⟨((d : ℤ) : ℚ), hΛℤ d⟩ ⟨((ℓ : ℤ) : ℚ), hΛℤ ℓ⟩ hdℓmem]
    congr 1; apply Subtype.ext; push_cast; rfl
  have h1 : g' ≫ ψ = E.act ⟨((d : ℤ) : ℚ), hΛℤ d⟩ := by
    rw [← cancel_epi (E.act ⟨((ℓ : ℤ) : ℚ), hΛℤ ℓ⟩), ← Category.assoc, hg'_lin, Category.assoc, ← hgψ, hg'g, hsplit]
  have h2 : ψ ≫ g' = E.act ⟨((d : ℤ) : ℚ), hΛℤ d⟩ := by
    rw [← cancel_epi (E.act ⟨((ℓ : ℤ) : ℚ), hΛℤ ℓ⟩), ← Category.assoc, ← hgψ, hgg', hsplit]
  refine ⟨ψ, hg', hψ, hg'_hom, hψ_hom, hg'_lin, hψ_lin, fun hd => ?_⟩
  have e : (⟨((d : ℚ) : ℍ[ℚ, a, b]), hd⟩ : ↥Λ) = ⟨((d : ℤ) : ℚ), hΛℤ d⟩ := by apply Subtype.ext; push_cast; rfl
  rw [e]; exact ⟨h1, h2⟩

end XLKC1

namespace XLKC1

variable {k : Type} [Field k] {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} {N : ℕ} (E : FakeEllipticCurve Λ N k)

attribute [local instance] ptCommGroup

noncomputable def endHom (φ : E.A ⟶ E.A) (hφ : φ ≫ E.f = E.f)
    (hφ_hom : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of k)) (P Q : SchemeHomOver t E.f),
      mapPt φ hφ (E.L.mul t P Q) = E.L.mul t (mapPt φ hφ P) (mapPt φ hφ Q)) : Pt E →* Pt E where
  toFun P := mapPt φ hφ P
  map_one' := mapPt_one E φ hφ hφ_hom _
  map_mul' P Q := hφ_hom _ P Q

theorem endHom_apply (φ : E.A ⟶ E.A) (hφ : φ ≫ E.f = E.f)
    (hφ_hom : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of k)) (P Q : SchemeHomOver t E.f),
      mapPt φ hφ (E.L.mul t P Q) = E.L.mul t (mapPt φ hφ P) (mapPt φ hφ Q)) (P : Pt E) :
    endHom E φ hφ hφ_hom P = mapPt φ hφ P := rfl

theorem linEquiv_of_natCard_eq_sq {ℓ : ℕ} [Fact ℓ.Prime] {V : Type} [AddCommGroup V] [Module (ZMod ℓ) V] [Finite V]
    (h : Nat.card V = ℓ ^ 2) : Nonempty (V ≃ₗ[ZMod ℓ] (ZMod ℓ × ZMod ℓ)) := by
  have hrank : Module.finrank (ZMod ℓ) V = 2 := by
    have h' := Module.natCard_eq_pow_finrank (K := ZMod ℓ) (V := V)
    rw [Nat.card_zmod, h] at h'
    exact (Nat.pow_right_injective (Fact.out : ℓ.Prime).two_le h').symm
  have hrank2 : Module.finrank (ZMod ℓ) (ZMod ℓ × ZMod ℓ) = 2 := by
    rw [Module.finrank_prod, Module.finrank_self]
  exact ⟨LinearEquiv.ofFinrankEq _ _ (hrank.trans hrank2.symm)⟩

end XLKC1

open XLKC1 in
theorem solution
    {r rbar N : ℕ} [Fact r.Prime] [Fact rbar.Prime] [NeZero N] (hrr : rbar ≠ r)
    {a b : ℚ} (hB : IsIndefiniteRamifiedExactlyAt a b r rbar)
    (Λ : Submodule ℤ ℍ[ℚ, a, b]) (hΛ : IsMaximalOrder Λ) (hΛℤ : ∀ m : ℤ, ((m : ℚ) : ℍ[ℚ, a, b]) ∈ Λ)
    (k₀ : Type) [Field k₀] [IsAlgClosed k₀] [CharP k₀ r] (A₀ : FakeEllipticCurve Λ N k₀)
    (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓr : ℓ ≠ r) (hℓrbar : ℓ ≠ rbar) (e : ℕ)
    (f f' : A₀.A ⟶ A₀.A) (hf : f ≫ A₀.f = A₀.f) (hf' : f' ≫ A₀.f = A₀.f)
    (hf_hom : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of k₀)) (P Q : SchemeHomOver t A₀.f),
      mapPt f hf (A₀.L.mul t P Q) = A₀.L.mul t (mapPt f hf P) (mapPt f hf Q))
    (hf'_hom : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of k₀)) (P Q : SchemeHomOver t A₀.f),
      mapPt f' hf' (A₀.L.mul t P Q) = A₀.L.mul t (mapPt f' hf' P) (mapPt f' hf' Q))
    (hf_lin : ∀ m : ↥Λ, A₀.act m ≫ f = f ≫ A₀.act m) (hf'_lin : ∀ m : ↥Λ, A₀.act m ≫ f' = f' ≫ A₀.act m)
    (hff' : f ≫ f' = A₀.act ⟨(((r ^ e * ℓ : ℕ) : ℤ) : ℚ), hΛℤ _⟩) (hf'f : f' ≫ f = A₀.act ⟨(((r ^ e * ℓ : ℕ) : ℤ) : ℚ), hΛℤ _⟩)
    (hf_not : ∀ (j : ℕ) (ψ : A₀.A ⟶ A₀.A), ¬ FakeEllipticCurve.IsIsogenyPair (r ^ j) A₀ A₀ f ψ)
    (hf'_not : ∀ (j : ℕ) (ψ : A₀.A ⟶ A₀.A), ¬ FakeEllipticCurve.IsIsogenyPair (r ^ j) A₀ A₀ f' ψ) :
    ∃ W : ZMod ℓ × ZMod ℓ → SchemeHomOver (𝟙 (Spec (CommRingCat.of k₀))) A₀.f,
      Function.Injective W ∧
      (∀ i j : ZMod ℓ × ZMod ℓ, W (i + j) = A₀.L.mul (𝟙 (Spec (CommRingCat.of k₀))) (W i) (W j)) ∧
      ∀ P : SchemeHomOver (𝟙 (Spec (CommRingCat.of k₀))) A₀.f,
        (∃ i : ZMod ℓ × ZMod ℓ, W i = P) ↔
          (nsmulPt A₀.L (𝟙 (Spec (CommRingCat.of k₀))) ℓ P = A₀.L.one (𝟙 (Spec (CommRingCat.of k₀))) ∧
            mapPt f hf P = A₀.L.one (𝟙 (Spec (CommRingCat.of k₀)))) := by
  classical
  letI : CommGroup (Pt A₀) := ptCommGroup A₀
  haveI : Fact ℓ.Prime := ⟨hℓ⟩
  have hO : IsOrder Λ := hΛ.isOrder
  have hℓk : (ℓ : k₀) ≠ 0 := by
    intro h
    have hdvd : r ∣ ℓ := (CharP.cast_eq_zero_iff k₀ r ℓ).mp h
    exact hℓr ((Nat.prime_dvd_prime_iff_eq Fact.out hℓ).mp hdvd).symm

  set fH : Pt A₀ →* Pt A₀ := endHom A₀ f hf hf_hom with hfH
  set Tor : Subgroup (Pt A₀) := (powMonoidHom ℓ).ker with hTor
  set K : Subgroup (Pt A₀) := Tor ⊓ fH.ker with hK
  have memTor : ∀ P : Pt A₀, P ∈ Tor ↔ nsmulPt A₀.L (𝟙 _) ℓ P = A₀.L.one (𝟙 _) := by
    intro P; rw [hTor, MonoidHom.mem_ker, powMonoidHom_apply, ← nsmulPt_eq_pow]; rfl
  have memK : ∀ P : Pt A₀, P ∈ K ↔ nsmulPt A₀.L (𝟙 _) ℓ P = A₀.L.one (𝟙 _) ∧ mapPt f hf P = A₀.L.one (𝟙 _) := by
    intro P; rw [hK, Subgroup.mem_inf, memTor, MonoidHom.mem_ker, hfH, endHom_apply]; rfl

  have hTorSet : (Tor : Set (Pt A₀)) = {P | nsmulPt A₀.L (𝟙 _) ℓ P = A₀.L.one (𝟙 _)} := by
    ext P; exact memTor P
  obtain ⟨hfin, hcard4⟩ := CerednikDrinfeld.QM.FakeEllipticCurve.finite_and_natCard_torsion_eq_pow_four_of_isUnit k₀ A₀ ℓ
    (isUnit_iff_ne_zero.mpr hℓk)
  haveI hTorFinite : Finite Tor := by
    rw [show (↥Tor) = ↥(Tor : Set (Pt A₀)) from rfl, hTorSet]; exact hfin
  have hTorCard : Nat.card Tor = ℓ ^ 4 := by
    rw [show (↥Tor) = ↥(Tor : Set (Pt A₀)) from rfl, hTorSet]; exact hcard4
  have hKle : K ≤ Tor := inf_le_left
  haveI hKFinite : Finite K := Finite.of_injective _ (Subgroup.inclusion_injective hKle)

  have hKstab : ∀ (x : ↥Λ) (g : Pt A₀), g ∈ K → ρ A₀ x g ∈ K := by
    intro x g hg
    rw [memK] at hg ⊢
    have hx : ∀ Q : Pt A₀, ρ A₀ x Q = mapPt (A₀.act x) (A₀.act_over x) Q := fun Q => rfl
    refine ⟨?_, ?_⟩
    · rw [hx, ← mapPt_nsmulPt A₀ (A₀.act x) (A₀.act_over x) (A₀.act_hom x), hg.1]
      exact mapPt_one A₀ _ _ (A₀.act_hom x) _
    · have hc : mapPt f hf (mapPt (A₀.act x) (A₀.act_over x) g) = mapPt (A₀.act x) (A₀.act_over x) (mapPt f hf g) := by
        apply Subtype.ext; simp only [mapPt_coe, Category.assoc, hf_lin x]
      rw [hx, hc, hg.2]; exact mapPt_one A₀ _ _ (A₀.act_hom x) _

  haveI : Finite (↥(K : Set (Pt A₀))) := hKFinite
  obtain ⟨n, ℓs, H, hprime, hH0, hHlast, hmono, hHstab, hidx, hpow, -, hcardK⟩ :=
    QuaternionAlgebra.IsMaximalOrder.exists_chain_subgroup_relIndex_eq_sq hrr hB Λ hΛ (ρ A₀) (ρ_one A₀) (ρ_mul A₀) (ρ_add A₀)
      K (Set.toFinite _) hKstab

  have hKpow : ∀ g : K, g ^ ℓ = 1 := by
    intro g
    have h := ((memK g.1).mp g.2).1
    rw [nsmulPt_eq_pow] at h
    exact Subtype.ext (by rw [Subgroup.coe_pow, Subgroup.coe_one]; exact h)
  have hPG : IsPGroup ℓ K := fun g => ⟨1, by rw [pow_one]; exact hKpow g⟩
  obtain ⟨m, hm⟩ := (IsPGroup.iff_card).mp hPG
  have hℓs : ∀ j, ℓs j = ℓ := by
    intro j
    have hdvd : ℓs j ^ 2 ∣ Nat.card K := by rw [hcardK]; exact Finset.dvd_prod_of_mem _ (Finset.mem_univ j)
    rw [hm] at hdvd
    have h' : ℓs j ∣ ℓ ^ m := (dvd_pow_self (ℓs j) two_ne_zero).trans hdvd
    exact (Nat.prime_dvd_prime_iff_eq (hprime j) hℓ).mp ((hprime j).dvd_of_dvd_pow h')
  have hcardK' : Nat.card K = ℓ ^ (2 * n) := by
    rw [hcardK, Finset.prod_congr rfl (fun j _ => by rw [hℓs j]), Finset.prod_const, Finset.card_univ, Fintype.card_fin,
      ← pow_mul, mul_comm]

  have hK_ne_bot : K ≠ ⊥ := by
    intro hbot
    have hkill : ∀ P : Pt A₀, nsmulPt A₀.L (𝟙 _) ℓ P = A₀.L.one (𝟙 _) → mapPt f' hf' P = A₀.L.one (𝟙 _) := by
      intro P hP
      have hmem : mapPt f' hf' P ∈ K := by
        rw [memK]; constructor
        · rw [← mapPt_nsmulPt A₀ f' hf' hf'_hom, hP]; exact mapPt_one A₀ f' hf' hf'_hom _
        · have h1 : mapPt f hf (mapPt f' hf' P) = mapPt (A₀.act ⟨(((r ^ e * ℓ : ℕ) : ℤ) : ℚ), hΛℤ _⟩) (A₀.act_over _) P := by
            apply Subtype.ext; simp only [mapPt_coe, Category.assoc, hf'f]
          rw [h1, pushPt_act_natCast' A₀ hΛℤ, nsmulPt_eq_pow, pow_mul', ← nsmulPt_eq_pow A₀ ℓ P, hP]
          exact one_pow _
      rw [hbot, Subgroup.mem_bot] at hmem; exact hmem
    obtain ⟨ψ, hψ⟩ := exists_isIsogenyPair_of_forall_point A₀ hΛℤ hO ℓ hℓk (r ^ e) f' f hf' hf hf'_hom hf_hom
      hf'_lin hf_lin hf'f hff' hkill
    exact hf_not e ψ hψ

  have hK_ne_Tor : K ≠ Tor := by
    intro heq
    have hkill : ∀ P : Pt A₀, nsmulPt A₀.L (𝟙 _) ℓ P = A₀.L.one (𝟙 _) → mapPt f hf P = A₀.L.one (𝟙 _) := by
      intro P hP
      have hmem : P ∈ K := by rw [heq, memTor]; exact hP
      exact ((memK P).mp hmem).2
    obtain ⟨ψ, hψ⟩ := exists_isIsogenyPair_of_forall_point A₀ hΛℤ hO ℓ hℓk (r ^ e) f f' hf hf' hf_hom hf'_hom
      hf_lin hf'_lin hff' hf'f hkill
    exact hf'_not e ψ hψ

  have h1lt : 1 < Nat.card K := K.one_lt_card_iff_ne_bot.mpr hK_ne_bot
  have hlt4 : Nat.card K < ℓ ^ 4 := by
    rw [← hTorCard]
    have hlt : K < Tor := lt_of_le_of_ne hKle hK_ne_Tor
    have hss : (K : Set (Pt A₀)) ⊂ (Tor : Set (Pt A₀)) := SetLike.coe_ssubset_coe.mpr hlt
    haveI : Finite (↥(Tor : Set (Pt A₀))) := hTorFinite
    have h := Set.ncard_lt_ncard hss (Set.toFinite _)
    rwa [← Nat.card_coe_set_eq, ← Nat.card_coe_set_eq] at h
  have hn1 : n = 1 := by
    rw [hcardK'] at h1lt hlt4
    have h2 : 2 * n < 4 := (Nat.pow_lt_pow_iff_right hℓ.one_lt).mp hlt4
    have h0 : 2 * n ≠ 0 := by intro h0; rw [h0, pow_zero] at h1lt; exact lt_irrefl _ h1lt
    omega
  have hcardK2 : Nat.card K = ℓ ^ 2 := by rw [hcardK', hn1]

  have hV : ∀ v : Additive K, ℓ • v = 0 := by
    intro v
    have h := congrArg Additive.ofMul (hKpow (Additive.toMul v))
    rwa [ofMul_pow, ofMul_toMul, ofMul_one] at h
  letI inst : Module (ZMod ℓ) (Additive K) := AddCommGroup.zmodModule hV
  haveI : Finite (Additive K) := Finite.of_equiv K Additive.ofMul
  obtain ⟨leqv⟩ := @linEquiv_of_natCard_eq_sq ℓ _ (Additive K) _ inst _ hcardK2
  let eqv : Additive K ≃+ (ZMod ℓ × ZMod ℓ) := leqv.toAddEquiv
  refine ⟨fun i => ((Additive.toMul (eqv.symm i) : K) : Pt A₀), ?_, ?_, ?_⟩
  · intro i j hij
    exact eqv.symm.injective (Additive.toMul.injective (Subtype.val_injective hij))
  · intro i j
    show ((Additive.toMul (eqv.symm (i + j)) : K) : Pt A₀) = ((Additive.toMul (eqv.symm i) : K) : Pt A₀) * ((Additive.toMul (eqv.symm j) : K) : Pt A₀)
    rw [map_add, toMul_add, Subgroup.coe_mul]
  · intro P
    rw [← memK]
    constructor
    · rintro ⟨i, rfl⟩; exact (Additive.toMul (eqv.symm i)).2
    · intro hP
      refine ⟨eqv (Additive.ofMul ⟨P, hP⟩), ?_⟩
      simp

end S_CerednikDrinfeld_QM_FakeEllipticCurve_exists_zmod_prod_injective_mul_iff_nsmulPt_eq_one_and_mapPt_eq_one_of_not_isIsogenyPair
end P2MW
export P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_exists_zmod_prod_injective_mul_iff_nsmulPt_eq_one_and_mapPt_eq_one_of_not_isIsogenyPair (solution)
