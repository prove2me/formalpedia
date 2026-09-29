-- Prove2me | solution 1 for CerednikDrinfeld.QM.FakeEllipticCurve.exists_isAtkinLehnerQuotientVia_epi_and_forall_existsUnique_comp_eq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.141142+00:00
-- url     : https://prove2.me/submissions/7caecf7c-5817-5c2f-be46-ab97503d89df

import Mathlib
import Definitions.Def_CerednikDrinfeld_QMRigidification
import Definitions.Def_CerednikDrinfeld_QMIsogeny
import Definitions.Def_CerednikDrinfeld_ShimuraCurve
import Definitions.Def_QuaternionAlgebra_EichlerOrder
import Definitions.Def_CerednikDrinfeld_QMModuliProps
import Definitions.Def_QuaternionAlgebra_ReducedNorm
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawKernel
import Theorems.Thm_QuaternionAlgebra_IsIndefiniteRamifiedExactlyAt_isUnit_of_ne_zero
import Theorems.Thm_QuaternionAlgebra_IsOrder_exists_intCast_eq_nrd_and_exists_intCast_eq_trd
import Theorems.Thm_QuaternionAlgebra_IsMaximalOrder_exists_generator_ramifiedPrime_of_isIndefiniteRamifiedExactlyAt
import Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_existsUnique_schemeNsmul_comp_eq_of_forall_isTorsionPoint
import Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_isFinite_and_flat_schemeNsmul
import Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_surjective_schemeNsmul
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_exists_isAtkinLehnerQuotientVia_epi_and_forall_existsUnique_comp_eq
p2m_attr_erase "instance" "CerednikDrinfeld.CosetGraph.projGraphAction CerednikDrinfeld.CosetGraph.projVertMulAction CerednikDrinfeld.CosetGraph.awayVertMulAction CerednikDrinfeld.CosetGraph.actionKer_normal CerednikDrinfeld.CosetGraph.vertMulAction GoodReductionJacobian.RelativeGroupLaw.isIso_endKerStr_schemeHomOverId AlgebraicGeometry.Scheme.PresheafOfModules.symmetricCategory SheafOfModules.instFaithfulRingSheafPModToPMod SheafOfModules.symmetricCategory AlgebraicGeometry.Scheme.PresheafOfModules.monoidalCategory AlgebraicGeometry.Scheme.PresheafOfModules.monoidalClosed SheafOfModules.instFullRingSheafPModToPMod SheafOfModules.monoidalCategory AlgebraicGeometry.Scheme.Modules.symmetricCategory SheafOfModules.monoidalClosed SheafOfModules.instIsLocalizationPModRingSheafSheafifyFunctorPresheafW SheafOfModules.sheafifyFunctor_monoidal AlgebraicGeometry.Scheme.Modules.monoidalClosed AlgebraicGeometry.instMonoidalPresheafOfModulesModulesSheafify AlgebraicGeometry.Scheme.Modules.monoidalCategory PresheafOfModules.instMonoidalClosed PresheafOfModules.InternalHom.instModuleCarrierObjOppositeCommRingCatSubtypePiFamilyMemAddSubgroupNaturalFamilies PresheafOfModules.InternalHom.instModuleCarrierObjOppositeRingCatCompCommRingCatForget₂RingHomCarrierCarrierAbPresheaf PresheafOfModules.InternalHom.instSMulCarrierObjOppositeCommRingCatSubtypePiFamilyMemAddSubgroupNaturalFamilies AlgebraicGeometry.Scheme.Hom.opensMapFinal AlgebraicGeometry.RelPicard.RigidifiedLineBundle.setoid AlgebraicGeometry.RelPicard.RigidifiedLineBundle.instInhabited AlgebraicGeometry.OModulePresheaf.isScalarTower AlgebraicGeometry.Scheme.OrderedAffineCover.instLinearOrder AlgebraicGeometry.OModulePresheaf.module AlgebraicGeometry.Scheme.OrderedAffineCover.instFintype AlgebraicGeometry.Scheme.OrderedAffineCover.instFintypeIdx AlgebraicGeometry.OModulePresheaf.addCommGroup AlgebraicGeometry.Scheme.OrderedAffineCover.instDecidableEqIdx AlgebraicGeometry.OModulePresheaf.moduleSections TwoChartCech.Sections.M0_moduleA TwoChartCech.Sections.M1_module TwoChartCech.Cover.A01_algebra TwoChartCech.Cover.A0_algebra TwoChartCech.Cover.A1_commRing"
p2m_attr_erase "instance" "TwoChartCech.Cover.A1_algebra TwoChartCech.Sections.M01_module TwoChartCech.Sections.M0_addCommGroup TwoChartCech.Sections.M0_tower TwoChartCech.Sections.M01_addCommGroup TwoChartCech.Cover.A0_commRing TwoChartCech.Sections.M1_tower TwoChartCech.Sections.M01_moduleA TwoChartCech.Sections.M0_module TwoChartCech.Sections.M1_moduleA TwoChartCech.Sections.M1_addCommGroup TwoChartCech.Cover.A01_commRing TwoChartCech.Sections.M01_tower CoherentBaseChange.TwoTermComplex.C0_module CoherentBaseChange.TwoTermComplex.C0_addCommGroup CoherentBaseChange.TwoTermComplex.C1_module CoherentBaseChange.TwoTermComplex.C1_addCommGroup CoherentBaseChange.TwoTermComplex.C0_free CoherentBaseChange.TwoTermComplex.C1_finite CoherentBaseChange.TwoTermComplex.C0_finite CoherentBaseChange.TwoTermComplex.C1_free AlgebraicGeometry.OModulePresheaf.instSubsingletonObjZero AlgebraicGeometry.Scheme.Modules.preservesBinaryProducts_opensMap AlgebraicGeometry.Scheme.Modules.pullback_monoidal AlgebraicGeometry.Scheme.Modules.sheafify_isLocalization' AlgebraicGeometry.Scheme.Modules.preservesTerminal_opensMap AlgebraicGeometry.Scheme.Modules.pullback₀_monoidal AlgebraicGeometry.Scheme.Modules.preservesFiniteProducts_opensMap AlgebraicGeometry.Scheme.Modules.instLiftingPresheafOfModulesSheafifyPresheafWOpensCarrierCarrierCommRingCatGrothendieckTopologyObjFunctorOppositeIsSheafSheafCompPullback₀Pullback PresheafOfModules.PullbackMonoidal.pullback_monoidal PresheafOfModules.PullbackMonoidal.isIso_δ PresheafOfModules.pushforward_laxMonoidal PresheafOfModules.PullbackMonoidal.isIso_η PresheafOfModules.free_monoidal PresheafOfModules.restrictScalars_laxMonoidal PresheafOfModules.PullbackMonoidal.isIso_δ_gS PresheafOfModules.pullback_oplaxMonoidal PresheafOfModules.PullbackMonoidal.instPreservesColimitsOfSizeCompOppositeCommRingCatRingCatForget₂RingHomCarrierCarrierPb PresheafOfModules.pullback_monoidal' AlgebraicGeometry.SmoothOfRelativeDimension.fiberToSpecResidueField"
p2m_attr_erase "instance" "AlgebraicGeometry.SmoothOfRelativeDimension.pullback_snd AlgebraicGeometry.SmoothOfRelativeDimension.pullback_fst AlgebraicGeometry.SmoothOfRelativeDimension.smooth_one AlgebraicGeometry.SmoothProperCurve.isIntegral_pullback_Spec_field AlgebraicGeometry.IsProper.fiberToSpecResidueField AlgebraicCurve.CurveModel.isProper AlgebraicCurve.CurveModel.isIntegral AlgebraicCurve.CurveModel.smooth AlgebraicGeometry.Scheme.LocalRepresentabilityULift.instIsLocallyInjectiveFunUliftYonedaGluedToSheaf AlgebraicGeometry.Scheme.LocalRepresentabilityULift.instIsLocallySurjectiveFunUliftYonedaGluedToSheafOfIsLocallySurjectiveZariskiTopologyDescFunctorOppositeType AlgebraicGeometry.Scheme.LocalRepresentabilityULift.instIsOpenImmersionToGlued AlgebraicGeometry.Scheme.LocalRepresentabilityULift.instIsIsoSheafZariskiTopologyTypeUliftYonedaGluedToSheaf AlgebraicGeometry.RelPicard.instIsOpenImmersionToGlued AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.instFundamentalIdentityOfSumRamificationInertia AlgebraicCurve.Place.instIsScalarTowerResidueFieldRestrictPushforward AlgebraicCurve.Place.instAlgebraResidueFieldRestrictPushforward AlgebraicCurve.Place.instIsLocalHomRestrictInclusion AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions PresheafOfModules.ExteriorPower.instModulePresheafAb AlgebraicGeometry.RelEffCartierDiv.subsingleton_of_degree_zero AlgebraicGeometry.RelEffCartierDiv.isIso_subschemeIota_snd_of_degree_one AlgebraicGeometry.isIso_ker_graphOver_subschemeIota_snd AlgebraicGeometry.isClosedImmersion_graphOver AlgebraicGeometry.FGSubalgebra.instIsDirectedLe AlgebraicGeometry.FGSubalgebra.instQuasiSeparatedSpaceCarrierCarrierCommRingCatObjOppositeSchemeSpecDiagram AlgebraicGeometry.FGSubalgebra.instIsCofilteredOpposite AlgebraicGeometry.FGSubalgebra.instIsAffineObjOppositeSchemeSpecDiagram AlgebraicGeometry.FGSubalgebra.instNonempty AlgebraicGeometry.FGSubalgebra.instNonemptySubtypeLeSubalgebraValFG AlgebraicGeometry.FGSubalgebra.instCompactSpaceCarrierCarrierCommRingCatObjOppositeSchemeSpecDiagram AlgebraicGeometry.FGSubalgebra.instIsDirectedSubtypeLeSubalgebraValFG AlgebraicGeometry.FGSubalgebra.instIsAffineHomMapOppositeSchemeSpecDiagram AlgebraicGeometry.FGSubalgebra.instIsFiltered"
p2m_attr_erase "instance" "AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instNeg AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instSMulInt AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instAddCommGroup AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instAdd AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instSub AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instModuleCarrierObjOppositeOpensCarrierCarrierCommRingCatPresheafOpOpensTop AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instSMulCarrierObjOppositeOpensCarrierCarrierCommRingCatPresheafOpOpensTop AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instSMulNat AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instZero AlgebraicCurve.instHasLocalResidue_of_hasCanonicalLocalResidueK AlgebraicCurve.instHasCanonicalLocalResidueK_of_hasCanonicalLocalResidueKStar AlgebraicCurve.Place.kw_ffgc_finiteDimensional_adicCompletion instAlgebraSubtypeMemValuationSubring_definitions AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersIntegersCompletion ModularCurve.KwF4gRRTate.instAlgebraKAdicCompletionIntegers AlgebraicCurve.Place.kw_ffgc_continuousSMul_adicCompletionComap AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersCompletionCompletion IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions AlgebraicCurve.instHasCanonicalLocalResidueK AlgebraicCurve.Place.instAlgebra_restrictResidueField AlgebraicCurve.Place.instIsScalarTower_restrictResidueField AlgebraicCurve.instHasLocalResidue AlgebraicCurve.HasSeparableResidue.of_perfectField_of_isCurveOver AlgebraicCurve.HasSeparableResidue.of_perfectField AlgebraicCurve.Place.instIsLocalHom_restrictSubringHom AlgebraicCurve.instHasCanonicalLocalResidueKStar ModularCurve.KwNo6Pin.isLocalRing_completion SheafOfModules.isIso_ihomModelToIhom AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instDecidableEqIdx AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instFintype AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instLinearOrder AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instFintypeIdx AlgebraicGeometry.OModulePresheaf.Leray.relAltC_scalarTower AlgebraicGeometry.OModulePresheaf.Leray.ker_relAltd_modΓ AlgebraicGeometry.OModulePresheaf.Leray.relAltC_modΓ"
p2m_attr_erase "instance" "AlgebraicGeometry.OModulePresheaf.Leray.biC_abGrp AlgebraicGeometry.OModulePresheaf.Leray.relAltH_modΓ AlgebraicGeometry.OModulePresheaf.Leray.ker_relAltd_smul AlgebraicGeometry.OModulePresheaf.Leray.relAltH_scalarTower AlgebraicGeometry.OModulePresheaf.Leray.relAltH_smul AlgebraicGeometry.OModulePresheaf.Leray.biC_module DoubleComplex.instModuleE₂I DoubleComplex.Bounded.modR DoubleComplex.instModuleE₂II DoubleComplex.instAddCommGroupE₂II DoubleComplex.Bounded.abGrp DoubleComplex.instAddCommGroupE₂I AlgebraicGeometry.ChowDatum.hι_closed AlgebraicGeometry.ChowDatumProj.hιN_closed AlgebraicGeometry.ChowDatumProj.hp_proper AlgebraicGeometry.ChowDatum.hp_isoU AlgebraicGeometry.ChowDatum.hp_proper AlgebraicGeometry.ProjSpace.algebraAway AlgebraicGeometry.ProjSpace.instIsProperProdOverπ AlgebraicGeometry.ChowDatumProj.hp_isoU AlgebraicGeometry.ProjSpace.isProper_π AlgebraicGeometry.ProjSpace.finiteType_mvPolynomial ProjSpaceCech.GradedModule.H.module ProjSpaceCech.GradedModule.H.addCommGroup ProjSpaceCech.GradedModule.sec.instAdd ProjSpaceCech.GradedModule.sec.instNeg ProjSpaceCech.GradedModule.acg ProjSpaceCech.GradedModule.Frac.setoid ProjSpaceCech.GradedModule.modR ProjSpaceCech.GradedModule.sec.instModule ProjSpaceCech.GradedModule.sec.instAddCommGroup ProjSpaceCech.GradedModule.sec.instZero ProjSpaceCech.GradedModule.Presentation.fJ ProjSpaceCech.GradedModule.sec.instSMul ProjSpaceCech.Twist.H.module ProjSpaceCech.Idx.instFintype ProjSpaceCech.Twist.H.addCommGroup ProjSpaceCech.Idx.instDecidableEq ProjSpaceCech.Twist.Mon.instDecidableEq ProjSpaceCech.Twist.cochain.instAddCommGroup"
p2m_attr_erase "instance" "ProjSpaceCech.Twist.cochain.instModule AlgebraicGeometry.FGSubalgebra.tensorStage_directedSystem AlgebraicGeometry.RelEffCartierDiv.isClosedImmersion_subschemeι_resProdMap AlgebraicGeometry.RelEffCartierDiv.isOpenImmersion_resProdMap AlgebraicCurve.CurveModel.locallyOfFiniteType_gluedToBase AlgebraicCurve.CurveModel.isFractionRing_overlap AlgebraicCurve.CurveModel.isLocallyNoetherian_glued AlgebraicCurve.CurveModel.jacobsonSpace_glued AlgebraicCurve.CurveModel.isOpenImmersion_ι₀ AlgebraicCurve.CurveModel.isIntegral_glued AlgebraicCurve.CurveModel.quasiSeparated_gluedToBase AlgebraicCurve.CurveModel.compactSpace_glued AlgebraicCurve.CurveModel.isIntegral_adjoin_chartRing AlgebraicCurve.CurveModel.isFractionRing_overlap_functionField AlgebraicCurve.CurveModel.isProper_gluedToBase AlgebraicCurve.CurveModel.isOpenImmersion_ιU AlgebraicCurve.CurveModel.isOpenImmersion_f₀ AlgebraicCurve.CurveModel.isOpenImmersion_fInf AlgebraicCurve.CurveModel.isOpenImmersion_ιInf AlgebraicCurve.CurveModel.algebra_overlap_functionField AlgebraicCurve.CurveModel.quasiCompact_gluedToBase AlgebraicCurve.CurveModel.algebraAdjoin AlgebraicCurve.CurveModel.isDedekindDomain_chartRing AlgebraicCurve.CurveModel.isIntegralClosure AlgebraicCurve.CurveModel.finite_chartRing AlgebraicCurve.CurveModel.centre_isPrime AlgebraicCurve.CurveModel.isFractionRing_chartRing AlgebraicCurve.CurveModel.finiteType_chartRing AlgebraicCurve.CurveModel.isNoetherianRing_chartRing AlgebraicCurve.CurveModel.isScalarTower_base_adjoin AlgebraicCurve.CurveModel.isScalarTower_adjoin AlgebraicCurve.CurveModel.chartRing_finitePresentation instTopologicallyFGOfFiniteType AlgebraicGeometry.ProjSpace.twistObj.addCommGroup AlgebraicGeometry.ProjSpace.twistFam.module AlgebraicGeometry.ProjSpace.twistObj.module AlgebraicGeometry.ProjSpace.twistObj.moduleSections AlgebraicGeometry.ProjSpace.twistFam.addCommGroup kmfloorsGlue_int_three_isPrime kmfloorsGlue_int_bot_isPrime"
p2m_attr_erase "simp" "QuaternionAlgebra.ClassSet.map_mk QuaternionAlgebra.baseChangeRight_tmul QuaternionAlgebra.mapOfAlgebraMapEq_apply QuaternionAlgebra.baseChange_tmul GoodReductionJacobian.RelativeGroupLaw.fibre_inv GoodReductionJacobian.RelativeGroupLaw.fibrePointToBase_coe GoodReductionJacobian.RelativeGroupLaw.fibrePointOfBase_toBase GoodReductionJacobian.RelativeGroupLaw.fibre_mul GoodReductionJacobian.RelativeGroupLaw.fibrePointToBase_ofBase GoodReductionJacobian.RelativeGroupLaw.fibre_one GoodReductionJacobian.RelativeGroupLaw.fibrePointOfBase_coe AlgebraicGeometry.schemeFibreEndo_snd AlgebraicGeometry.schemeFibreEndo_fst GoodReductionJacobian.RelativeGroupLaw.baseChangePointToBase_ofBase GoodReductionJacobian.RelativeGroupLaw.baseChangePointToBase_coe GoodReductionJacobian.RelativeGroupLaw.baseChangePointOfBase_coe GoodReductionJacobian.RelativeGroupLaw.baseChange_inv GoodReductionJacobian.RelativeGroupLaw.baseChangePointOfBase_toBase GoodReductionJacobian.RelativeGroupLaw.baseChange_mul GoodReductionJacobian.RelativeGroupLaw.baseChange_one NeronModelInfra.NeronModelPropertyBundle.endExtensionEquiv_symm_restrict NeronModelInfra.schemeHomOverComp_id_left NeronModelInfra.schemeHomOverComp_id_right NeronModelInfra.schemeHomOverId_coe NeronModelInfra.NeronModelPropertyBundle.endExtensionEquiv_apply NeronModelInfra.NeronModelPropertyBundle.restrict_endExtensionEquiv_symm NeronModelInfra.schemeHomOverComp_coe NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_fst NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_snd NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_fst NeronSpecialFibreInfra.neronEndRestrictEquiv_apply NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_fst_assoc NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_snd NeronSpecialFibreInfra.neronEndExtension_genericFibreRestrict NeronSpecialFibreInfra.specClosedFibreInclusion_eq NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_fst_assoc NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_snd_assoc NeronSpecialFibreInfra.genericFibreRestrict_neronEndExtension NeronSpecialFibreInfra.homOverId_coe NeronSpecialFibreInfra.homOverComp_coe"
p2m_attr_erase "simp" "NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_snd_assoc NeronModelInfra.schemeHomOverNpow_succ NeronModelInfra.schemeHomOverNpow_zero GoodReductionJacobian.relativeGroupLawOfGrpObj_inv GoodReductionJacobian.relativeGroupLawOfGrpObj_mul GoodReductionJacobian.overHomEquivSchemeHomOver_apply_coe GoodReductionJacobian.relativeGroupLawOfGrpObj_one GoodReductionJacobian.overHomEquivSchemeHomOver_symm_apply_left SheafOfModules.tensorUnit_eq AlgebraicGeometry.Scheme.Modules.tensorUnit_eq PresheafOfModules.InternalHom.presheaf_map_apply PresheafOfModules.InternalHom.curryFamily_app PresheafOfModules.InternalHom.add_app PresheafOfModules.InternalHom.smul_app PresheafOfModules.InternalHom.zero_app PresheafOfModules.ihomObj_map_val PresheafOfModules.ihomFunctor_map PresheafOfModules.InternalHom.restrict_app PresheafOfModules.InternalHom.postcomp_app PresheafOfModules.InternalHom.neg_app PresheafOfModules.curry'_app_val PresheafOfModules.InternalHom.presheaf_obj PresheafOfModules.ihomFunctor_obj PresheafOfModules.ihomObj_obj PresheafOfModules.InternalHom.sub_app PresheafOfModules.ihomMap_app_val AlgebraicGeometry.Scheme.Modules.tensorPow_zero AlgebraicGeometry.Scheme.Modules.tensorPow_succ AlgebraicGeometry.RelPicard.RigidifiedLineBundle.mk.sizeOf_spec AlgebraicGeometry.RelPicard.RigidifiedLineBundle.mk.injEq AlgebraicGeometry.Scheme.OrderedAffineCover.mk.injEq AlgebraicGeometry.OModulePresheaf.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCover.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.mk.injEq AlgebraicGeometry.Scheme.TwoAffineOpenCover.mk.injEq AlgebraicGeometry.Scheme.TwoAffineOpenCover.mk.sizeOf_spec AlgebraicGeometry.Scheme.TwoAffineOpenCover.pullback_U1 AlgebraicGeometry.Scheme.TwoAffineOpenCover.pullback_U0 TwoChartCech.Sections.mk.injEq TwoChartCech.Cover.mk.injEq"
p2m_attr_erase "simp" "TwoChartCech.GrothendieckComplex.mk.injEq TwoChartCech.Sections.mk.sizeOf_spec TwoChartCech.Cover.mk.sizeOf_spec TwoChartCech.Cover.lineBundle_r0_apply TwoChartCech.GrothendieckComplex.mk.sizeOf_spec TwoChartCech.Cover.lineBundle_r1_apply CoherentBaseChange.TwoTermComplex.mk.sizeOf_spec CoherentBaseChange.TwoTermComplex.mk.injEq AlgebraicGeometry.OModulePresheaf.prod_obj AlgebraicGeometry.OModulePresheaf.restrOpen_obj AlgebraicGeometry.OModulePresheaf.DevissageStep.mk.injEq AlgebraicGeometry.OModulePresheaf.pushforward_obj AlgebraicGeometry.OModulePresheaf.im_obj AlgebraicGeometry.OModulePresheaf.pow_obj AlgebraicGeometry.OModulePresheaf.fstHom_app AlgebraicGeometry.OModulePresheaf.ker_obj AlgebraicGeometry.OModulePresheaf.coker_obj AlgebraicGeometry.OModulePresheaf.DevissageStep.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCover.preimage_U AlgebraicGeometry.OModulePresheaf.sndHom_app AlgebraicGeometry.OModulePresheaf.Hom.mk.injEq AlgebraicGeometry.OModulePresheaf.Hom.id_app AlgebraicGeometry.OModulePresheaf.AffHom.appSections_apply AlgebraicGeometry.OModulePresheaf.AffHom.comp_app AlgebraicGeometry.OModulePresheaf.AffSES.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.AffHom.kerMap_coe AlgebraicGeometry.OModulePresheaf.AffHom.id_app AlgebraicGeometry.OModulePresheaf.Hom.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.Hom.toAffHom_app AlgebraicGeometry.OModulePresheaf.SES.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.AffHom.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.Hom.comp_app AlgebraicGeometry.OModulePresheaf.SES.mk.injEq AlgebraicGeometry.OModulePresheaf.AffHom.mk.injEq AlgebraicGeometry.OModulePresheaf.Hom.appSections_apply AlgebraicGeometry.OModulePresheaf.AffSES.mk.injEq PresheafOfModules.freeεIso_hom_app PresheafOfModules.freeμIso_hom_app AlgebraicGeometry.RelPicard.RepresentsRelSubPic.mk.injEq AlgebraicGeometry.RelPicard.SubPicCondition.mk.injEq"
p2m_attr_erase "simp" "AlgebraicGeometry.RelPicard.SubPicCondition.mk.sizeOf_spec AlgebraicGeometry.RelPicard.RepresentsRelSubPic.mk.sizeOf_spec AlgebraicGeometry.SmoothProperCurve.sectionBaseChange_coe_snd AlgebraicGeometry.SmoothProperCurve.sectionBaseChange_coe_fst AlgebraicCurve.CurveModel.mk.injEq AlgebraicCurve.CurveModel.mk.sizeOf_spec AlgebraicCurve.mulAdele_apply AlgebraicCurve.residuePairing_apply_coe AlgebraicCurve.mem_adeleBdd AlgebraicCurve.weilSmul_one AlgebraicCurve.diagonalHom_apply AlgebraicCurve.weilSmul_apply AlgebraicCurve.adeleSpaceMul_coe AlgebraicCurve.mulAdele_one AlgebraicGeometry.SmoothProperCurve.FiniteMapData.twoAffineOpenCover_U1 AlgebraicGeometry.SmoothProperCurve.FiniteMapData.mk.injEq AlgebraicGeometry.SmoothProperCurve.FiniteMapData.mk.sizeOf_spec AlgebraicGeometry.SmoothProperCurve.FiniteMapData.twoAffineOpenCover_U0 AlgebraicGeometry.RelPicard.SubPicCondition.onClasses_mk AlgebraicGeometry.RelPicard.relSubPicPresheaf_map_coe CategoryTheory.Functor.OverTotal.ofFibre_fst CategoryTheory.Functor.overTotal_map_fst AlgebraicGeometry.Scheme.LocalRepresentabilityULift.glueData_J AlgebraicGeometry.Scheme.LocalRepresentabilityULift.uliftYoneda_toGlued_uliftYonedaGluedToSheaf AlgebraicGeometry.Scheme.LocalRepresentabilityULift.glueData_t' AlgebraicGeometry.Scheme.LocalRepresentabilityULift.uliftYoneda_toGlued_uliftYonedaGluedToSheaf_assoc AlgebraicGeometry.Scheme.LocalRepresentabilityULift.uliftYonedaGluedToSheaf_app_toGlued AlgebraicGeometry.Scheme.LocalRepresentabilityULift.glueData_openCover_map AlgebraicGeometry.Scheme.LocalRepresentabilityULift.uliftYonedaGluedToSheaf_app_comp AlgebraicGeometry.Scheme.LocalRepresentabilityULift.glueData_V AlgebraicGeometry.Scheme.LocalRepresentabilityULift.glueData_t AlgebraicGeometry.Scheme.LocalRepresentabilityULift.glueData_U AlgebraicGeometry.Scheme.LocalRepresentabilityULift.glueData_f AlgebraicGeometry.RelPicard.designationOfRepresentableBy_P AlgebraicGeometry.RelPicard.designationOfRepresentableBy_toBase AlgebraicGeometry.RelPicard.rigSection_snd AlgebraicGeometry.RelPicard.RigidifiedLineBundle.ofInvertible_L AlgebraicGeometry.RelPicard.rigSection_snd_assoc AlgebraicGeometry.RelPicard.SubPicGroupCondition.mk.injEq AlgebraicGeometry.RelPicard.SubPicGroupCondition.mk.sizeOf_spec"
p2m_attr_erase "simp" "AlgebraicCurve.coe_cechH0Equiv_apply AlgebraicCurve.cechH1ToH1_mk AlgebraicCurve.lSpaceOn_univ AlgebraicCurve.lSpaceOn_empty AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.Divisor.mapRestrict_single AlgebraicCurve.Divisor.pushforward_single AlgebraicCurve.Place.coe_restrictInclusion AlgebraicCurve.Place.mem_fiber AlgebraicCurve.Place.restrict_toValuationSubring AlgebraicCurve.Divisor.degree_pushforward AlgebraicCurve.Place.restrictResidueMap_residue AlgebraicCurve.Pic0.coe_pushforwardDegZeroHom AlgebraicCurve.Pic0.coe_pullbackDegZeroHom AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Divisor.degree_pushforwardAlong"
p2m_attr_erase "simp" "AlgebraicCurve.Pic0.coe_degZeroCorrespondence AlgebraicCurve.Place.mem_fiberAlong AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.jqNModC_one ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one AlgebraicCurve.Place.differentialCoeff_zero AlgebraicCurve.Place.differentialCoeff_dCoord AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.injEq AlgebraicCurve.TranscendenceTower.mk.injEq AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec AlgebraicCurve.PoleDivisorPackage.mk.injEq AlgebraicGeometry.RelPicard.thetaBundle_def AlgebraicGeometry.RelPicard.picardBundle_def AlgebraicGeometry.RelEffCartierDiv.toRelEffDivisor_ofRelEffDivisor AlgebraicGeometry.RelEffCartierDiv.toRelEffDivisor_I AlgebraicGeometry.mapOnProdOver_fst_assoc AlgebraicGeometry.RelEffCartierDiv.mk.sizeOf_spec AlgebraicGeometry.RelEffCartierDiv.mk.injEq AlgebraicGeometry.mapOnProdOver_snd AlgebraicGeometry.mapOnProdOver_fst AlgebraicGeometry.mapOnProdOver_snd_assoc AlgebraicGeometry.mapOnProdOver_id AlgebraicCurve.RelEffDivisor.mk.sizeOf_spec AlgebraicCurve.mapOnProd_fst"
p2m_attr_erase "simp" "AlgebraicCurve.mapOnProd_fst_assoc AlgebraicCurve.mapOnProd_snd AlgebraicCurve.UnivDivisorPack.mk.injEq AlgebraicCurve.RelEffDivisor.mk.injEq AlgebraicCurve.UnivDivisorPack.mk.sizeOf_spec AlgebraicCurve.mapOnProd_snd_assoc AlgebraicGeometry.Scheme.Modules.exteriorPower_obj PresheafOfModules.exteriorPower_map_ιMulti PresheafOfModules.ExteriorPower.appₗ_apply AlgebraicGeometry.prodKerGraph_one AlgebraicGeometry.fibrePowOver.proj_comp AlgebraicGeometry.prodKerGraph_zero AlgebraicGeometry.RelEffCartierDiv.empty_I AlgebraicGeometry.fibrePowOver.proj_comp_assoc AlgebraicGeometry.graphOver_fst_assoc AlgebraicGeometry.RelEffCartierDiv.toPoint_comp AlgebraicGeometry.RelEffCartierDiv.toPoint_comp_assoc AlgebraicGeometry.graphOver_fst AlgebraicGeometry.RelEffCartierDiv.ofPoint_I AlgebraicGeometry.graphOver_snd AlgebraicGeometry.graphOver_snd_assoc AlgebraicCurve.SymmetricPowerPackage.mk.sizeOf_spec AlgebraicCurve.SymmetricPowerPackage.mk.injEq AlgebraicGeometry.FGSubalgebra.cocone_ι_app_apply AlgebraicGeometry.RelPicard.fst_toProdSpec AlgebraicGeometry.RelPicard.toProdSpec_fst_assoc AlgebraicGeometry.RelPicard.pointsSubBasepointModule_cons AlgebraicGeometry.RelPicard.pointsSubBasepointModule_nil AlgebraicGeometry.RelPicard.fst_toProdSpec_assoc AlgebraicGeometry.RelPicard.toProdSpec_fst AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.sub_app AlgebraicGeometry.Scheme.IdealSheafData.sres_sresTop AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.add_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.mk.sizeOf_spec AlgebraicGeometry.Scheme.IdealSheafData.coe_resLE AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.smul_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.coe_ofLE_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.ideal_range AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.zero_app AlgebraicGeometry.Scheme.IdealSheafData.sres_sres"
p2m_attr_erase "simp" "AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.comp_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.neg_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.id_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.coe_mulRight_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.nsmul_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.mk.injEq AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.zsmul_app AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.sizeOf_spec AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.injEq AlgebraicCurve.adeleSingle_coe AlgebraicCurve.kaehlerResidueTermKFam_apply AlgebraicCurve.Place.LocalResidueData.mk.injEq AlgebraicCurve.Place.LocalResidueData.mk.sizeOf_spec AlgebraicCurve.Place.kw_ffgc_adicCompletionComapIntegers_coe AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.sizeOf_spec AlgebraicCurve.Place.mem_simplePoleSubmodule AlgebraicCurve.Place.coe_uniformizerSubring ModularCurve.Lg37.Lg37CompletionSection.mk.injEq AlgebraicCurve.Place.CoefficientFieldSection.mk.injEq AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.injEq ModularCurve.Lg37.Lg37CompletionSection.mk.sizeOf_spec AlgebraicCurve.Place.CoefficientFieldSection.mk.sizeOf_spec AlgebraicCurve.Place.poleSubmodule_one AlgebraicCurve.Place.mem_poleSubmodule AlgebraicGeometry.Scheme.Modules.toUnitSection_ofUnitSection AlgebraicGeometry.Scheme.Modules.pullbackSection_def AlgebraicGeometry.Scheme.Modules.ofUnitSection_toUnitSection PresheafOfModules.InternalHom.IsSheafAux.appAt_toPresheafHom SheafOfModules.ihomSectionsEquivFamily_unit AlgebraicGeometry.Scheme.Modules.restrictHomEquivFamily_apply SheafOfModules.ihomEval_unit_app AlgebraicGeometry.Scheme.Modules.ihomEval_zero_right AlgebraicGeometry.Scheme.Modules.ihomEval_zero_left AlgebraicGeometry.Scheme.Modules.homOfFamily_app_apply SheafOfModules.unit_ihomSectionsEquivFamily AlgebraicGeometry.Scheme.Modules.familyOfHom_app AlgebraicGeometry.Scheme.Modules.restrictUnitIso_hom_app_apply AlgebraicGeometry.Scheme.Modules.restrictUnitIso_inv_app_apply AlgebraicGeometry.Scheme.Modules.restrictHomOfFamily_app_apply AlgebraicGeometry.Scheme.Modules.restrictHomEquivFamily_symm_apply"
p2m_attr_erase "simp" "AlgebraicGeometry.Scheme.Modules.tensorSections_zero_right AlgebraicGeometry.Scheme.Modules.map_unitSection AlgebraicGeometry.Scheme.Modules.tensorSectionsBilin_apply AlgebraicGeometry.Scheme.Modules.tensorPowSection_zero AlgebraicGeometry.Scheme.Modules.tensorSections_zero_left AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_neg AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_zero AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_sub AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_add AlgebraicGeometry.Scheme.OrderedAffineCover.toCoverOf_U AlgebraicGeometry.Scheme.OrderedAffineCoverOf.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCoverOf.mk.injEq AlgebraicGeometry.Scheme.OrderedAffineCover.restrict_U AlgebraicGeometry.OModulePresheaf.Leray.restrictToPreimage_U DoubleComplex.Bounded.mk.injEq DoubleComplex.Bounded.mk.sizeOf_spec DoubleComplex.Convergence.mk.injEq DoubleComplex.Convergence.mk.sizeOf_spec DoubleComplex.SubQuot.mk.sizeOf_spec DoubleComplex.SubQuot.mk.injEq AlgebraicGeometry.ChowDatumProj.mk.sizeOf_spec AlgebraicGeometry.ChowDatum.mk.sizeOf_spec AlgebraicGeometry.ChowDatumProj.mk.injEq AlgebraicGeometry.ChowDatum.mk.injEq ProjSpaceCech.GradedModule.mk.injEq ProjSpaceCech.GradedModule.mk.sizeOf_spec ProjSpaceCech.GradedModule.Frac.mk.sizeOf_spec ProjSpaceCech.GradedModule.Presentation.mk.injEq ProjSpaceCech.GradedModule.Frac.mk.injEq ProjSpaceCech.GradedModule.Presentation.mk.sizeOf_spec ProjSpaceCech.GradedModule.Hom.shift_toLinearMap ProjSpaceCech.GradedModule.Hom.mk.sizeOf_spec ProjSpaceCech.GradedModule.Hom.mk.injEq TwoChartCech.Mumford.dK_apply TwoChartCech.Mumford.ι0_apply TwoChartCech.Mumford.ι1_apply TwoChartCech.KerCoprod.dK_apply TwoChartCech.KerCoprod.ι1_apply TwoChartCech.KerCoprod.ι0_apply AlgebraicGeometry.tilde.functorCompPullbackSpecIso_app"
p2m_attr_erase "simp" "AlgebraicGeometry.RelPicard.algEquivZeroGroupCut_toSubPicCondition AlgebraicGeometry.RelPicard.LFP.stageHom_val AlgebraicGeometry.RelPicard.BaseChange.relSubPicPresheafRestrictIso_hom_app_coe AlgebraicGeometry.RelPicard.BaseChange.relSubPicPresheafRestrictIso_inv_app_coe AlgebraicGeometry.RelPicard.BaseChange.restrict_P AlgebraicGeometry.RelEffCartierDiv.IsUniversal.lift_comp AlgebraicGeometry.RelEffCartierDiv.functor_map_fst AlgebraicGeometry.RelEffCartierDiv.IsUniversal.homEquiv_apply AlgebraicGeometry.RelEffCartierDiv.IsUniversal.lift_pullbackAlong AlgebraicGeometry.RelEffCartierDiv.IsUniversal.homEquiv_symm_apply AlgebraicGeometry.RelEffCartierDiv.IsUniversal.lift_comp_assoc AlgebraicGeometry.RelEffCartierDiv.supportedIn_top AlgebraicGeometry.RelEffCartierDiv.mem_supportedIn_iff AlgebraicGeometry.RelEffCartierDiv.supportedIn_top_eq AlgebraicGeometry.RelEffCartierDiv.restrictAlong_extendAlong AlgebraicGeometry.RelEffCartierDiv.extendAlong_I AlgebraicGeometry.RelEffCartierDiv.resProdMap_snd AlgebraicGeometry.RelEffCartierDiv.restrictAlong_I AlgebraicGeometry.RelEffCartierDiv.extendAlong_restrictAlong AlgebraicGeometry.RelEffCartierDiv.resProdMap_fst_assoc AlgebraicGeometry.RelEffCartierDiv.resProdMap_snd_assoc AlgebraicGeometry.RelEffCartierDiv.resProdMap_fst CoherentBaseChange.FibreH0Family.mk.sizeOf_spec CoherentBaseChange.FibreH0Family.mk.injEq AlgebraicGeometry.Scheme.Modules.ProjPresentation.mk.injEq AlgebraicGeometry.Scheme.Modules.ProjPresentation.mk.sizeOf_spec AlgebraicCurve.CurveModel.coe_gInf AlgebraicCurve.CurveModel.coe_tInvChart AlgebraicCurve.CurveModel.ιInf_gluedToBase_assoc AlgebraicCurve.CurveModel.ιInf_gluedToBase AlgebraicCurve.CurveModel.primeOfι₀_asIdeal AlgebraicCurve.CurveModel.coe_tChart AlgebraicCurve.CurveModel.ι₀_gluedToBase_assoc AlgebraicCurve.CurveModel.primeOfιInf_asIdeal AlgebraicCurve.CurveModel.ι₀_gluedToBase AlgebraicCurve.CurveModel.coe_tma AlgebraicCurve.CurveModel.coe_primeEquivChartPlaces RegularLocalRingQuotientAscent.dualNumberFst_apply AlgebraicGeometry.ProjSpace.twistObj.mk.injEq AlgebraicGeometry.ProjSpace.twistObj.zero_val"
p2m_attr_erase "simp" "AlgebraicGeometry.ProjSpace.twistObj.add_val AlgebraicGeometry.ProjSpace.twist_res_val AlgebraicGeometry.ProjSpace.twist_smul_val AlgebraicGeometry.ProjSpace.twistGradeToObj_val AlgebraicGeometry.ProjSpace.twistObj.smul_val AlgebraicGeometry.ProjSpace.twistGradeEquiv_apply_val AlgebraicGeometry.ProjSpace.twistObj.mk.sizeOf_spec"

set_option autoImplicit false

p2m_open "CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra~schemeHomOverComp~schemeHomOverComp_coe GoodReductionJacobian"
open CerednikDrinfeld CerednikDrinfeld.QM CerednikDrinfeld.QM.FakeEllipticCurve QuaternionAlgebra IsDedekindDomain
open scoped Quaternion TensorProduct NumberField

universe u

namespace ALQUP

variable {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]}

section Conj

variable (π : ℍ[ℚ, a, b]) (hu : IsUnit π) (hnorm : ∀ x ∈ Λ, ∃ y ∈ Λ, π * x = y * π)

noncomputable def conj (x : ↥Λ) : ↥Λ :=
  ⟨(hnorm x x.2).choose, (hnorm x x.2).choose_spec.1⟩

theorem conj_spec (x : ↥Λ) : π * (x : ℍ[ℚ, a, b]) = (conj π hnorm x : ℍ[ℚ, a, b]) * π :=
  (hnorm x x.2).choose_spec.2

include hu in
theorem conj_unique {x : ↥Λ} {y : ℍ[ℚ, a, b]} (h : π * (x : ℍ[ℚ, a, b]) = y * π) :
    (conj π hnorm x : ℍ[ℚ, a, b]) = y :=
  (hu.mul_left_inj).1 ((conj_spec π hnorm x).symm.trans h)

include hu in
theorem conj_one (h1 : (1 : ℍ[ℚ, a, b]) ∈ Λ) : conj π hnorm ⟨1, h1⟩ = ⟨1, h1⟩ :=
  Subtype.ext (conj_unique π hu hnorm (by rw [mul_one, one_mul]))

include hu in
theorem conj_mul (x y : ↥Λ) (h : (x : ℍ[ℚ, a, b]) * (y : ℍ[ℚ, a, b]) ∈ Λ) :
    (conj π hnorm ⟨(x : ℍ[ℚ, a, b]) * (y : ℍ[ℚ, a, b]), h⟩ : ℍ[ℚ, a, b]) =
      (conj π hnorm x : ℍ[ℚ, a, b]) * (conj π hnorm y : ℍ[ℚ, a, b]) :=
  conj_unique π hu hnorm (by
    show π * ((x : ℍ[ℚ, a, b]) * (y : ℍ[ℚ, a, b])) = _
    rw [← mul_assoc, conj_spec π hnorm x, mul_assoc, conj_spec π hnorm y, mul_assoc])

include hu in
theorem conj_add (x y : ↥Λ) : conj π hnorm (x + y) = conj π hnorm x + conj π hnorm y :=
  Subtype.ext (conj_unique π hu hnorm (by
    show π * ((x : ℍ[ℚ, a, b]) + (y : ℍ[ℚ, a, b])) = ((conj π hnorm x : ℍ[ℚ, a, b]) + (conj π hnorm y : ℍ[ℚ, a, b])) * π
    rw [mul_add, add_mul, conj_spec π hnorm x, conj_spec π hnorm y]))

include hu in

theorem conj_coe (c : ℚ) (hc : ((c : ℚ) : ℍ[ℚ, a, b]) ∈ Λ) :
    (conj π hnorm ⟨(c : ℍ[ℚ, a, b]), hc⟩ : ℍ[ℚ, a, b]) = (c : ℍ[ℚ, a, b]) :=
  conj_unique π hu hnorm (by rw [coe_commutes])

include hu in

theorem conj_add_star (m : ↥Λ) (n : ℤ) (hn : (m : ℍ[ℚ, a, b]) + star (m : ℍ[ℚ, a, b]) = ((n : ℚ) : ℍ[ℚ, a, b]))
    (hν : nrd π ≠ 0) :
    (conj π hnorm m : ℍ[ℚ, a, b]) + star (conj π hnorm m : ℍ[ℚ, a, b]) = ((n : ℚ) : ℍ[ℚ, a, b]) := by
  set c : ℍ[ℚ, a, b] := (conj π hnorm m : ℍ[ℚ, a, b]) with hc
  have h1 : π * (m : ℍ[ℚ, a, b]) = c * π := conj_spec π hnorm m

  have h2 : star (m : ℍ[ℚ, a, b]) * star π = star π * star c := by
    rw [← star_mul, ← star_mul, h1]
  have h3 : π * star (m : ℍ[ℚ, a, b]) = star c * π := by
    have e1 : π * (star (m : ℍ[ℚ, a, b]) * star π) * π = π * (star π * star c) * π := by rw [h2]
    have e2 : π * star (m : ℍ[ℚ, a, b]) * ((nrd π : ℚ) : ℍ[ℚ, a, b]) = ((nrd π : ℚ) : ℍ[ℚ, a, b]) * (star c * π) := by
      rw [← star_mul_eq_coe_nrd π]
      calc π * star (m : ℍ[ℚ, a, b]) * (star π * π) = π * (star (m : ℍ[ℚ, a, b]) * star π) * π := by simp only [mul_assoc]
        _ = π * (star π * star c) * π := e1
        _ = (π * star π) * (star c * π) := by simp only [mul_assoc]
        _ = (star π * π) * (star c * π) := by rw [mul_star_eq_coe_nrd, star_mul_eq_coe_nrd]
    rw [← coe_commutes] at e2
    rw [coe_mul_eq_smul, coe_mul_eq_smul] at e2
    exact smul_right_injective ℍ[ℚ, a, b] hν e2
  have h4 : (c + star c) * π = ((n : ℚ) : ℍ[ℚ, a, b]) * π := by
    rw [add_mul, ← h1, ← h3, ← mul_add, hn, coe_commutes]
  exact (hu.mul_left_inj).1 h4

end Conj

theorem pushPt_congr {N : ℕ} {S : Type u} [CommRing S] (E : FakeEllipticCurve Λ N S) {m m' : ↥Λ} (h : m = m')
    {T : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of S)} (P : SchemeHomOver t E.f) :
    pushPt (E.act m) (E.act_over m) P = pushPt (E.act m') (E.act_over m') P := by
  subst h; rfl

noncomputable def twist {N : ℕ} {S : Type u} [CommRing S] (E : FakeEllipticCurve Λ N S)
    (π : ℍ[ℚ, a, b]) (hu : IsUnit π) (hν : nrd π ≠ 0)
    (hnorm : ∀ x ∈ Λ, ∃ y ∈ Λ, π * x = y * π) : FakeEllipticCurve Λ N S where
  A := E.A
  f := E.f
  L := E.L
  comm := E.comm
  bundle := E.bundle
  dim_fibre := E.dim_fibre
  act x := E.act (conj π hnorm x)
  act_over x := E.act_over _
  act_hom x := E.act_hom _
  act_one h := by
    show E.act (conj π hnorm ⟨1, h⟩) = 𝟙 E.A
    rw [conj_one π hu hnorm h]; exact E.act_one h
  act_mul x y h := by
    show E.act (conj π hnorm ⟨_, h⟩) = E.act (conj π hnorm y) ≫ E.act (conj π hnorm x)
    have hm : ((conj π hnorm x : ℍ[ℚ, a, b]) * (conj π hnorm y : ℍ[ℚ, a, b])) ∈ Λ := by
      rw [← conj_mul π hu hnorm x y h]; exact (conj π hnorm _).2
    rw [← E.act_mul (conj π hnorm x) (conj π hnorm y) hm]
    congr 1; exact Subtype.ext (conj_mul π hu hnorm x y h)
  act_add x y := by
    intro T t P
    show pushPt (E.act (conj π hnorm (x + y))) (E.act_over _) P =
      E.L.mul t (pushPt (E.act (conj π hnorm x)) (E.act_over _) P) (pushPt (E.act (conj π hnorm y)) (E.act_over _) P)
    rw [pushPt_congr E (conj_add π hu hnorm x y)]
    exact E.act_add _ _ t P
  act_trace := by
    intro k _ _ sk V _ _ _ τ hτ hrange hadd hscale m Φ hΦ n hn
    exact E.act_trace k sk V τ hτ hrange hadd hscale (conj π hnorm m) Φ hΦ n (conj_add_star π hu hnorm m n hn hν)
  C := E.C
  lev := E.lev
  lev_closed := E.lev_closed
  lev_sub := E.lev_sub
  lev_one := E.lev_one
  lev_torsion := E.lev_torsion
  lev_stable x := E.lev_stable _
  lev_finite := E.lev_finite
  lev_flat := E.lev_flat
  lev_finitePresentation := E.lev_finitePresentation
  lev_rank := E.lev_rank
  lev_fibre := E.lev_fibre

end ALQUP

namespace ALQUPpts

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
      apply Subtype.ext; push_cast; simp [Quaternion.coe_add]
    rw [e, E.act_add, ih, RelativeGroupLaw.nsmul_succ]
    congr 1
    have e1 : (⟨((1 : ℤ) : ℚ), hΛℤ 1⟩ : ↥Λ) = ⟨1, by simpa using hΛℤ 1⟩ := by apply Subtype.ext; simp
    rw [e1]
    apply Subtype.ext; rw [mapPt_coe, E.act_one]; exact Category.comp_id _

theorem act_natCast_eq_schemeNsmul (hΛℤ : ∀ m : ℤ, ((m : ℚ) : ℍ[ℚ, a, b]) ∈ Λ) (q : ℕ) :
    E.act ⟨((q : ℤ) : ℚ), hΛℤ q⟩ = E.L.schemeNsmul q := by
  have h := congrArg Subtype.val (pushPt_act_natCast E hΛℤ q E.f (RelativeGroupLaw.idPoint : SchemeHomOver E.f E.f))
  rw [mapPt_coe] at h
  rw [RelativeGroupLaw.schemeNsmul, ← h]
  exact (Category.id_comp _).symm

theorem comp_schemeNsmul {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of k)) (n : ℕ) (x : SchemeHomOver t E.f) :
    x.1 ≫ E.L.schemeNsmul n = (E.L.nsmul t n x).1 := by
  have h := E.L.nsmul_natural E.f t x.1 x.2 n RelativeGroupLaw.idPoint
  have hx : GoodReductionJacobian.schemeHomOverComp x.1 x.2 (RelativeGroupLaw.idPoint) = x := by
    apply Subtype.ext; rw [GoodReductionJacobian.schemeHomOverComp_coe]; exact Category.comp_id _
  rw [hx] at h
  have := congrArg Subtype.val h
  rw [GoodReductionJacobian.schemeHomOverComp_coe] at this
  exact this

theorem pushPt_nsmul (φ : E.A ⟶ E.A) (hφ : φ ≫ E.f = E.f)
    (hφ_hom : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of k)) (P Q : SchemeHomOver t E.f),
      mapPt φ hφ (E.L.mul t P Q) = E.L.mul t (mapPt φ hφ P) (mapPt φ hφ Q))
    {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of k)) (n : ℕ) (P : SchemeHomOver t E.f) :
    mapPt φ hφ (E.L.nsmul t n P) = E.L.nsmul t n (mapPt φ hφ P) := by
  letI := E.L.pointGroup t
  induction n with
  | zero =>
    rw [RelativeGroupLaw.nsmul_zero, RelativeGroupLaw.nsmul_zero]

    have h := hφ_hom t (E.L.one t) (E.L.one t)
    rw [E.L.one_mul] at h
    have h' : (mapPt φ hφ (E.L.one t) : SchemeHomOver t E.f) = mapPt φ hφ (E.L.one t) * mapPt φ hφ (E.L.one t) := h
    exact mul_eq_left.mp h'.symm
  | succ n ih => rw [RelativeGroupLaw.nsmul_succ, RelativeGroupLaw.nsmul_succ, hφ_hom, ih]

theorem mapPt_comp' {S : Type} [CommRing S] {A A' A'' : Scheme.{0}} {f : A ⟶ Spec (CommRingCat.of S)}
    {f' : A' ⟶ Spec (CommRingCat.of S)} {f'' : A'' ⟶ Spec (CommRingCat.of S)}
    (φ : A ⟶ A') (hφ : φ ≫ f' = f) (ψ : A' ⟶ A'') (hψ : ψ ≫ f'' = f') (hφψ : (φ ≫ ψ) ≫ f'' = f)
    {T : Scheme.{0}} {t : T ⟶ Spec (CommRingCat.of S)} (P : SchemeHomOver t f) :
    mapPt (φ ≫ ψ) hφψ P = mapPt ψ hψ (mapPt φ hφ P) :=
  Subtype.ext (by simp [mapPt_coe, Category.assoc])

end ALQUPpts

open ALQUP ALQUPpts in

theorem solution
    {r rbar N : ℕ} [Fact r.Prime] [Fact rbar.Prime] [NeZero N] (hrr : rbar ≠ r) (hrbarN : ¬ rbar ∣ N)
    {a b : ℚ} (hB : IsIndefiniteRamifiedExactlyAt a b r rbar)
    (Λ : Submodule ℤ ℍ[ℚ, a, b]) (hΛ : IsMaximalOrder Λ)
    (k₀ : Type) [Field k₀] [IsAlgClosed k₀] [CharP k₀ r] (A₀ : FakeEllipticCurve Λ N k₀) :
    ∃ (A₀w : FakeEllipticCurve Λ N k₀)
      (aw : A₀.A ⟶ A₀w.A) (haw : aw ≫ A₀w.f = A₀.f) (aw' : A₀w.A ⟶ A₀.A) (haw' : aw' ≫ A₀.f = A₀w.f),
      FakeEllipticCurve.IsAtkinLehnerQuotientVia rbar A₀ A₀w aw haw aw' haw' ∧ Epi aw ∧
      ∀ (φ : A₀.A ⟶ A₀.A) (hφ : φ ≫ A₀.f = A₀.f),
        (∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of k₀)) (P Q : SchemeHomOver t A₀.f),
        mapPt φ hφ (A₀.L.mul t P Q) = A₀.L.mul t (mapPt φ hφ P) (mapPt φ hφ Q)) →
        (∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of k₀)) (P : SchemeHomOver t A₀.f),
          (∀ (m : ↥Λ) (n : ℤ), (m : ℍ[ℚ, a, b]) * star (m : ℍ[ℚ, a, b]) = (((rbar : ℤ) * n : ℚ) : ℍ[ℚ, a, b]) →
          pushPt (A₀.act m) (A₀.act_over m) P = A₀.L.one t) → mapPt φ hφ P = A₀.L.one t) →
        ∃! χ : SchemeHomOver A₀w.f A₀.f, aw ≫ χ.1 = φ ∧
          (∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of k₀)) (P Q : SchemeHomOver t A₀w.f),
        mapPt χ.1 χ.2 (A₀w.L.mul t P Q) = A₀.L.mul t (mapPt χ.1 χ.2 P) (mapPt χ.1 χ.2 Q)) := by
  classical
  have hO : IsOrder Λ := hΛ.isOrder
  have hΛℤ : ∀ m : ℤ, ((m : ℚ) : ℍ[ℚ, a, b]) ∈ Λ := fun m => by
    have : (((m : ℚ)) : ℍ[ℚ, a, b]) = (m : ℤ) • (1 : ℍ[ℚ, a, b]) := by rw [zsmul_eq_mul, mul_one]; norm_cast
    rw [this]; exact Λ.smul_mem _ hO.one_mem
  obtain ⟨π, hπΛ, hnrd, hnormL, hnormR, hgen⟩ :=
    QuaternionAlgebra.IsMaximalOrder.exists_generator_ramifiedPrime_of_isIndefiniteRamifiedExactlyAt hB Λ hΛ rbar (Or.inr rfl)
  have hrp : rbar.Prime := Fact.out
  have hr0 : (rbar : ℚ) ≠ 0 := by exact_mod_cast hrp.ne_zero
  have hrpos : 0 < rbar := hrp.pos
  have hν : nrd π ≠ 0 := by rcases hnrd with h | h <;> rw [h] <;> simp [hr0]
  have hπ0 : π ≠ 0 := by rintro rfl; exact hν (by simp)
  have hu : IsUnit π := QuaternionAlgebra.IsIndefiniteRamifiedExactlyAt.isUnit_of_ne_zero hB π hπ0

  obtain ⟨s, hs1, hsν⟩ : ∃ s : ℚ, (s = 1 ∨ s = -1) ∧ s * nrd π = rbar := by
    rcases hnrd with h | h
    · exact ⟨1, Or.inl rfl, by rw [h, one_mul]⟩
    · exact ⟨-1, Or.inr rfl, by rw [h]; ring⟩
  have hπbar : star π ∈ Λ := by
    obtain ⟨-, t, ht⟩ := QuaternionAlgebra.IsOrder.exists_intCast_eq_nrd_and_exists_intCast_eq_trd hO hπΛ
    have : star π = ((trd π : ℚ) : ℍ[ℚ, a, b]) - π := by rw [← add_star_eq_coe_trd]; abel
    rw [this, ← ht]
    exact Λ.sub_mem (hΛℤ t) hπΛ
  set πd : ℍ[ℚ, a, b] := (s : ℍ[ℚ, a, b]) * star π with hπd
  have hπdΛ : πd ∈ Λ := by
    rcases hs1 with rfl | rfl
    · simpa [hπd] using hπbar
    · have : πd = -star π := by simp [hπd]
      rw [this]; exact Λ.neg_mem hπbar
  have hππd : π * πd = ((rbar : ℚ) : ℍ[ℚ, a, b]) := by
    rw [hπd, ← mul_assoc, ← coe_commutes s π, mul_assoc, mul_star_eq_coe_nrd, ← coe_mul, hsν]
  have hπdπ : πd * π = ((rbar : ℚ) : ℍ[ℚ, a, b]) := by
    rw [hπd, mul_assoc, star_mul_eq_coe_nrd, ← coe_mul, hsν]
  have hrΛ : ((rbar : ℚ) : ℍ[ℚ, a, b]) ∈ Λ := by exact_mod_cast hΛℤ rbar

  have hcomp₁ : A₀.act ⟨π, hπΛ⟩ ≫ A₀.act ⟨πd, hπdΛ⟩ = A₀.act ⟨((rbar : ℤ) : ℚ), hΛℤ rbar⟩ := by
    rw [← A₀.act_mul ⟨πd, hπdΛ⟩ ⟨π, hπΛ⟩ (hO.mul_mem hπdΛ hπΛ)]
    congr 1; apply Subtype.ext; push_cast; exact hπdπ
  have hcomp₂ : A₀.act ⟨πd, hπdΛ⟩ ≫ A₀.act ⟨π, hπΛ⟩ = A₀.act ⟨((rbar : ℤ) : ℚ), hΛℤ rbar⟩ := by
    rw [← A₀.act_mul ⟨π, hπΛ⟩ ⟨πd, hπdΛ⟩ (hO.mul_mem hπΛ hπdΛ)]
    congr 1; apply Subtype.ext; push_cast; exact hππd

  have hff := GoodReductionJacobian.RelativeGroupLaw.isFinite_and_flat_schemeNsmul A₀.L A₀.bundle (fun t x y => A₀.comm t x y) rbar hrpos
  haveI : IsFinite (A₀.L.schemeNsmul rbar) := hff.1
  haveI : Flat (A₀.L.schemeNsmul rbar) := hff.2
  haveI : Surjective (A₀.L.schemeNsmul rbar) :=
    GoodReductionJacobian.RelativeGroupLaw.surjective_schemeNsmul A₀.L A₀.comm A₀.bundle rbar hrpos
  haveI : QuasiCompact (A₀.L.schemeNsmul rbar) := inferInstance
  haveI hepiN : Epi (A₀.L.schemeNsmul rbar) := Flat.epi_of_flat_of_surjective _
  have hactN : A₀.act ⟨((rbar : ℤ) : ℚ), hΛℤ rbar⟩ = A₀.L.schemeNsmul rbar := act_natCast_eq_schemeNsmul A₀ hΛℤ rbar
  haveI hepiπ : Epi (A₀.act ⟨π, hπΛ⟩) := by
    haveI : Epi (A₀.act ⟨πd, hπdΛ⟩ ≫ A₀.act ⟨π, hπΛ⟩) := by rw [hcomp₂, hactN]; infer_instance
    exact epi_of_epi (A₀.act ⟨πd, hπdΛ⟩) _
  haveI hepiπd : Epi (A₀.act ⟨πd, hπdΛ⟩) := by
    haveI : Epi (A₀.act ⟨π, hπΛ⟩ ≫ A₀.act ⟨πd, hπdΛ⟩) := by rw [hcomp₁, hactN]; infer_instance
    exact epi_of_epi (A₀.act ⟨π, hπΛ⟩) _
  refine ⟨twist A₀ π hu hν hnormL, A₀.act ⟨π, hπΛ⟩, A₀.act_over _, A₀.act ⟨πd, hπdΛ⟩, A₀.act_over _,
    ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, hepiπ, ?_⟩
  · intro T t P Q; exact A₀.act_hom _ t P Q
  · intro T t P Q; exact A₀.act_hom _ t P Q
  ·
    intro x
    show A₀.act x ≫ A₀.act ⟨π, hπΛ⟩ = A₀.act ⟨π, hπΛ⟩ ≫ A₀.act (conj π hnormL x)
    have h1 : π * (x : ℍ[ℚ, a, b]) ∈ Λ := hO.mul_mem hπΛ x.2
    have h2 : (conj π hnormL x : ℍ[ℚ, a, b]) * π ∈ Λ := hO.mul_mem (conj π hnormL x).2 hπΛ
    rw [← A₀.act_mul ⟨π, hπΛ⟩ x h1, ← A₀.act_mul (conj π hnormL x) ⟨π, hπΛ⟩ h2]
    congr 1; exact Subtype.ext (conj_spec π hnormL x)
  ·
    intro x
    show A₀.act (conj π hnormL x) ≫ A₀.act ⟨πd, hπdΛ⟩ = A₀.act ⟨πd, hπdΛ⟩ ≫ A₀.act x
    have h1 : πd * (conj π hnormL x : ℍ[ℚ, a, b]) ∈ Λ := hO.mul_mem hπdΛ (conj π hnormL x).2
    have h2 : (x : ℍ[ℚ, a, b]) * πd ∈ Λ := hO.mul_mem x.2 hπdΛ
    rw [← A₀.act_mul ⟨πd, hπdΛ⟩ (conj π hnormL x) h1, ← A₀.act_mul x ⟨πd, hπdΛ⟩ h2]
    congr 1; apply Subtype.ext
    show πd * (conj π hnormL x : ℍ[ℚ, a, b]) = (x : ℍ[ℚ, a, b]) * πd
    have e : πd * (π * (x : ℍ[ℚ, a, b])) * πd = πd * ((conj π hnormL x : ℍ[ℚ, a, b]) * π) * πd := by
      rw [conj_spec π hnormL x]
    have e' : ((rbar : ℚ) : ℍ[ℚ, a, b]) * ((x : ℍ[ℚ, a, b]) * πd) =
        ((rbar : ℚ) : ℍ[ℚ, a, b]) * (πd * (conj π hnormL x : ℍ[ℚ, a, b])) := by
      calc ((rbar : ℚ) : ℍ[ℚ, a, b]) * ((x : ℍ[ℚ, a, b]) * πd) = (πd * π) * (x : ℍ[ℚ, a, b]) * πd := by
            rw [hπdπ]; simp only [mul_assoc]
        _ = πd * (π * (x : ℍ[ℚ, a, b])) * πd := by simp only [mul_assoc]
        _ = πd * ((conj π hnormL x : ℍ[ℚ, a, b]) * π) * πd := e
        _ = πd * (conj π hnormL x : ℍ[ℚ, a, b]) * (π * πd) := by simp only [mul_assoc]
        _ = ((rbar : ℚ) : ℍ[ℚ, a, b]) * (πd * (conj π hnormL x : ℍ[ℚ, a, b])) := by rw [hππd, ← coe_commutes]
    rw [coe_mul_eq_smul, coe_mul_eq_smul] at e'
    exact (smul_right_injective ℍ[ℚ, a, b] hr0 e').symm
  ·
    intro hrΛ'
    constructor
    · have hm := A₀.act_mul ⟨πd, hπdΛ⟩ ⟨π, hπΛ⟩ (hO.mul_mem hπdΛ hπΛ)
      refine hm.symm.trans ?_
      congr 1; exact Subtype.ext hπdπ
    · show A₀.act ⟨πd, hπdΛ⟩ ≫ A₀.act ⟨π, hπΛ⟩ = A₀.act (conj π hnormL ⟨_, hrΛ'⟩)
      rw [← A₀.act_mul ⟨π, hπΛ⟩ ⟨πd, hπdΛ⟩ (hO.mul_mem hπΛ hπdΛ)]
      congr 1; apply Subtype.ext
      rw [conj_coe π hu hnormL (rbar : ℚ) hrΛ']; exact hππd
  ·
    intro T t P
    constructor
    · intro hP m n hmn
      have hdiv : ∃ n' : ℤ, nrd (m : ℍ[ℚ, a, b]) = (rbar : ℚ) * n' := by
        refine ⟨n, ?_⟩
        have h := hmn
        rw [mul_star_eq_coe_nrd] at h
        have h' := QuaternionAlgebra.coe_injective h
        exact_mod_cast h'
      obtain ⟨l, hl, hml⟩ := (hgen m m.2).1 hdiv
      have hlπ : (l : ℍ[ℚ, a, b]) * π ∈ Λ := hO.mul_mem hl hπΛ
      have hmeq : m = ⟨(l : ℍ[ℚ, a, b]) * π, hlπ⟩ := Subtype.ext hml
      rw [pushPt_congr A₀ hmeq]
      have hsplit : pushPt (A₀.act ⟨(l : ℍ[ℚ, a, b]) * π, hlπ⟩) (A₀.act_over _) P =
          mapPt (A₀.act ⟨l, hl⟩) (A₀.act_over _) (mapPt (A₀.act ⟨π, hπΛ⟩) (A₀.act_over _) P) := by
        apply Subtype.ext
        simp only [pushPt, mapPt_coe, Category.assoc, A₀.act_mul ⟨l, hl⟩ ⟨π, hπΛ⟩ hlπ]
      rw [hsplit, show mapPt (A₀.act ⟨π, hπΛ⟩) (A₀.act_over _) P = A₀.L.one t from hP]
      set x := mapPt (A₀.act ⟨l, hl⟩) (A₀.act_over _) (A₀.L.one t) with hx
      have hxx : A₀.L.mul t x x = x := by rw [hx, ← A₀.act_hom, A₀.L.one_mul]
      letI := A₀.L.pointGroup t
      have h2 : x * x = x * 1 := by rw [mul_one]; exact hxx
      exact mul_left_cancel h2
    · intro hK
      have hss : s * s = 1 := by rcases hs1 with rfl | rfl <;> norm_num
      have hnrds : nrd π = (rbar : ℚ) * s := by
        calc nrd π = s * (s * nrd π) := by rw [← mul_assoc, hss, one_mul]
          _ = (rbar : ℚ) * s := by rw [hsν, mul_comm]
      obtain ⟨z, hz⟩ : ∃ z : ℤ, (z : ℚ) = s := by
        rcases hs1 with rfl | rfl
        · exact ⟨1, by simp⟩
        · exact ⟨-1, by simp⟩
      have hnπ : π * star π = (((rbar : ℤ) * z : ℚ) : ℍ[ℚ, a, b]) := by
        rw [mul_star_eq_coe_nrd, hnrds, ← hz]; norm_cast
      exact hK ⟨π, hπΛ⟩ z hnπ
  · intro T t P hP
    exact A₀.lev_stable _ t P hP
  ·
    intro φ hφ hφ_hom hφ_kill

    have hF : (A₀.act ⟨πd, hπdΛ⟩ ≫ φ) ≫ A₀.f = A₀.f := by rw [Category.assoc, hφ]; exact A₀.act_over _
    have hFhom_pt : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of k₀)) (P Q : SchemeHomOver t A₀.f),
        mapPt (A₀.act ⟨πd, hπdΛ⟩ ≫ φ) hF (A₀.L.mul t P Q) =
          A₀.L.mul t (mapPt (A₀.act ⟨πd, hπdΛ⟩ ≫ φ) hF P) (mapPt (A₀.act ⟨πd, hπdΛ⟩ ≫ φ) hF Q) := by
      intro T t P Q
      rw [mapPt_comp' (A₀.act ⟨πd, hπdΛ⟩) (A₀.act_over _) φ hφ hF, mapPt_comp' (A₀.act ⟨πd, hπdΛ⟩) (A₀.act_over _) φ hφ hF,
        mapPt_comp' (A₀.act ⟨πd, hπdΛ⟩) (A₀.act_over _) φ hφ hF]
      rw [show mapPt (A₀.act ⟨πd, hπdΛ⟩) (A₀.act_over _) (A₀.L.mul t P Q) = _ from A₀.act_hom _ t P Q, hφ_hom]
    have hFker : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of k₀)) (P : SchemeHomOver t A₀.f),
        A₀.L.IsTorsionPoint t rbar P → P.1 ≫ (A₀.act ⟨πd, hπdΛ⟩ ≫ φ) = (A₀.L.one t).1 := by
      intro T t P hP
      have hPone : pushPt (A₀.act ⟨((rbar : ℤ) : ℚ), hΛℤ rbar⟩) (A₀.act_over _) P = A₀.L.one t := by
        rw [pushPt_act_natCast A₀ hΛℤ rbar t P]
        exact (A₀.L.isTorsionPoint_def t rbar P).mp hP
      have hkill := hφ_kill t (mapPt (A₀.act ⟨πd, hπdΛ⟩) (A₀.act_over _) P) (by
        intro m n hmn
        have hdiv : ∃ n' : ℤ, nrd (m : ℍ[ℚ, a, b]) = (rbar : ℚ) * n' := by
          refine ⟨n, ?_⟩
          have h := hmn
          rw [mul_star_eq_coe_nrd] at h
          have h' := QuaternionAlgebra.coe_injective h
          exact_mod_cast h'
        obtain ⟨l, hl, hml⟩ := (hgen m m.2).1 hdiv
        have hlr : (l : ℍ[ℚ, a, b]) * ((rbar : ℤ) : ℚ) ∈ Λ := hO.mul_mem hl (hΛℤ rbar)
        have hmπd : (m : ℍ[ℚ, a, b]) * πd ∈ Λ := hO.mul_mem m.2 hπdΛ
        have hmeq : (⟨(m : ℍ[ℚ, a, b]) * πd, hmπd⟩ : ↥Λ) = ⟨(l : ℍ[ℚ, a, b]) * ((rbar : ℤ) : ℚ), hlr⟩ := by
          apply Subtype.ext
          show (m : ℍ[ℚ, a, b]) * πd = (l : ℍ[ℚ, a, b]) * (((rbar : ℤ) : ℚ) : ℍ[ℚ, a, b])
          rw [hml, mul_assoc, hππd]; push_cast; rfl

        have e1 : pushPt (A₀.act m) (A₀.act_over m) (mapPt (A₀.act ⟨πd, hπdΛ⟩) (A₀.act_over _) P) =
            pushPt (A₀.act ⟨(m : ℍ[ℚ, a, b]) * πd, hmπd⟩) (A₀.act_over _) P := by
          apply Subtype.ext
          simp only [pushPt, mapPt_coe, Category.assoc, A₀.act_mul m ⟨πd, hπdΛ⟩ hmπd]
        have e2 : pushPt (A₀.act ⟨(l : ℍ[ℚ, a, b]) * ((rbar : ℤ) : ℚ), hlr⟩) (A₀.act_over _) P =
            mapPt (A₀.act ⟨l, hl⟩) (A₀.act_over _) (pushPt (A₀.act ⟨((rbar : ℤ) : ℚ), hΛℤ rbar⟩) (A₀.act_over _) P) := by
          apply Subtype.ext
          simp only [pushPt, mapPt_coe, Category.assoc, A₀.act_mul ⟨l, hl⟩ ⟨((rbar : ℤ) : ℚ), hΛℤ rbar⟩ hlr]
        rw [e1, pushPt_congr A₀ hmeq, e2, hPone]
        set x := mapPt (A₀.act ⟨l, hl⟩) (A₀.act_over _) (A₀.L.one t) with hx
        have hxx : A₀.L.mul t x x = x := by rw [hx, ← A₀.act_hom, A₀.L.one_mul]
        letI := A₀.L.pointGroup t
        have h2 : x * x = x * 1 := by rw [mul_one]; exact hxx
        exact mul_left_cancel h2)
      have := congrArg Subtype.val hkill
      simp only [mapPt_coe, Category.assoc] at this
      exact this
    obtain ⟨w, hwF, huniq, hw, hwhom⟩ :=
      GoodReductionJacobian.RelativeGroupLaw.existsUnique_schemeNsmul_comp_eq_of_forall_isTorsionPoint k₀ A₀.f A₀.L A₀.comm rbar
        A₀.f A₀.L (A₀.act ⟨πd, hπdΛ⟩ ≫ φ) hF
        (fun t P Q => by
          have := congrArg Subtype.val (hFhom_pt t P Q)
          rw [mapPt_coe] at this
          exact this)
        hFker
    refine ⟨⟨w, hw⟩, ⟨?_, ?_⟩, ?_⟩
    ·
      show A₀.act ⟨π, hπΛ⟩ ≫ w = φ
      rw [← cancel_epi (A₀.act ⟨πd, hπdΛ⟩), ← Category.assoc, hcomp₂, hactN, hwF]
    · intro T t P Q
      apply Subtype.ext
      rw [mapPt_coe]
      exact hwhom t P Q
    · rintro ⟨w', hw'⟩ ⟨hc', -⟩
      apply Subtype.ext
      show w' = w
      apply huniq
      rw [← hactN, ← hcomp₂, Category.assoc]
      show A₀.act ⟨πd, hπdΛ⟩ ≫ A₀.act ⟨π, hπΛ⟩ ≫ w' = A₀.act ⟨πd, hπdΛ⟩ ≫ φ
      have hc'' : A₀.act ⟨π, hπΛ⟩ ≫ w' = φ := hc'
      rw [hc'']

end S_CerednikDrinfeld_QM_FakeEllipticCurve_exists_isAtkinLehnerQuotientVia_epi_and_forall_existsUnique_comp_eq
end P2MW
export P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_exists_isAtkinLehnerQuotientVia_epi_and_forall_existsUnique_comp_eq (solution)
