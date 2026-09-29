-- Prove2me | solution 1 for CerednikDrinfeld.QM.FakeEllipticCurve.natCard_setOf_forall_pushPt_act_eq_one_of_eq_or_eq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.141142+00:00
-- url     : https://prove2.me/submissions/e822f169-7709-5534-be15-c474abe8ca7a

import Mathlib
import Definitions.Def_CerednikDrinfeld_QMModuli
import Definitions.Def_QuaternionAlgebra_EichlerOrder
import Definitions.Def_QuaternionAlgebra_ReducedNorm
import Definitions.Def_CerednikDrinfeld_ShimuraCurve
import Definitions.Def_QuaternionAlgebra_Order
import Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_exists_generator_torsionPoints_of_isMaximalOrder_of_prime
import Theorems.Thm_QuaternionAlgebra_IsMaximalOrder_leftIdeal_eq_or_eq_or_eq_of_isIndefiniteRamifiedExactlyAt_of_eq_or_eq
import Theorems.Thm_QuaternionAlgebra_IsOrder_relIndex_span_smul_eq_pow_four
import Theorems.Thm_QuaternionAlgebra_IsOrder_exists_intCast_eq_nrd_and_exists_intCast_eq_trd
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_natCard_setOf_forall_pushPt_act_eq_one_of_eq_or_eq
p2m_attr_erase "instance" "GoodReductionJacobian.RelativeGroupLaw.isIso_endKerStr_schemeHomOverId AlgebraicGeometry.Scheme.PresheafOfModules.symmetricCategory SheafOfModules.instFaithfulRingSheafPModToPMod SheafOfModules.symmetricCategory AlgebraicGeometry.Scheme.PresheafOfModules.monoidalCategory AlgebraicGeometry.Scheme.PresheafOfModules.monoidalClosed SheafOfModules.instFullRingSheafPModToPMod SheafOfModules.monoidalCategory AlgebraicGeometry.Scheme.Modules.symmetricCategory SheafOfModules.monoidalClosed SheafOfModules.instIsLocalizationPModRingSheafSheafifyFunctorPresheafW SheafOfModules.sheafifyFunctor_monoidal AlgebraicGeometry.Scheme.Modules.monoidalClosed AlgebraicGeometry.instMonoidalPresheafOfModulesModulesSheafify AlgebraicGeometry.Scheme.Modules.monoidalCategory PresheafOfModules.instMonoidalClosed PresheafOfModules.InternalHom.instModuleCarrierObjOppositeCommRingCatSubtypePiFamilyMemAddSubgroupNaturalFamilies PresheafOfModules.InternalHom.instModuleCarrierObjOppositeRingCatCompCommRingCatForget₂RingHomCarrierCarrierAbPresheaf PresheafOfModules.InternalHom.instSMulCarrierObjOppositeCommRingCatSubtypePiFamilyMemAddSubgroupNaturalFamilies AlgebraicGeometry.Scheme.Hom.opensMapFinal AlgebraicGeometry.RelPicard.RigidifiedLineBundle.setoid AlgebraicGeometry.RelPicard.RigidifiedLineBundle.instInhabited AlgebraicGeometry.OModulePresheaf.isScalarTower AlgebraicGeometry.Scheme.OrderedAffineCover.instLinearOrder AlgebraicGeometry.OModulePresheaf.module AlgebraicGeometry.Scheme.OrderedAffineCover.instFintype AlgebraicGeometry.Scheme.OrderedAffineCover.instFintypeIdx AlgebraicGeometry.OModulePresheaf.addCommGroup AlgebraicGeometry.Scheme.OrderedAffineCover.instDecidableEqIdx AlgebraicGeometry.OModulePresheaf.moduleSections TwoChartCech.Sections.M0_moduleA TwoChartCech.Sections.M1_module TwoChartCech.Cover.A01_algebra TwoChartCech.Cover.A0_algebra TwoChartCech.Cover.A1_commRing TwoChartCech.Cover.A1_algebra TwoChartCech.Sections.M01_module TwoChartCech.Sections.M0_addCommGroup TwoChartCech.Sections.M0_tower TwoChartCech.Sections.M01_addCommGroup"
p2m_attr_erase "instance" "TwoChartCech.Cover.A0_commRing TwoChartCech.Sections.M1_tower TwoChartCech.Sections.M01_moduleA TwoChartCech.Sections.M0_module TwoChartCech.Sections.M1_moduleA TwoChartCech.Sections.M1_addCommGroup TwoChartCech.Cover.A01_commRing TwoChartCech.Sections.M01_tower CoherentBaseChange.TwoTermComplex.C0_module CoherentBaseChange.TwoTermComplex.C0_addCommGroup CoherentBaseChange.TwoTermComplex.C1_module CoherentBaseChange.TwoTermComplex.C1_addCommGroup CoherentBaseChange.TwoTermComplex.C0_free CoherentBaseChange.TwoTermComplex.C1_finite CoherentBaseChange.TwoTermComplex.C0_finite CoherentBaseChange.TwoTermComplex.C1_free AlgebraicGeometry.OModulePresheaf.instSubsingletonObjZero AlgebraicGeometry.Scheme.Modules.preservesBinaryProducts_opensMap AlgebraicGeometry.Scheme.Modules.pullback_monoidal AlgebraicGeometry.Scheme.Modules.sheafify_isLocalization' AlgebraicGeometry.Scheme.Modules.preservesTerminal_opensMap AlgebraicGeometry.Scheme.Modules.pullback₀_monoidal AlgebraicGeometry.Scheme.Modules.preservesFiniteProducts_opensMap AlgebraicGeometry.Scheme.Modules.instLiftingPresheafOfModulesSheafifyPresheafWOpensCarrierCarrierCommRingCatGrothendieckTopologyObjFunctorOppositeIsSheafSheafCompPullback₀Pullback PresheafOfModules.PullbackMonoidal.pullback_monoidal PresheafOfModules.PullbackMonoidal.isIso_δ PresheafOfModules.pushforward_laxMonoidal PresheafOfModules.PullbackMonoidal.isIso_η PresheafOfModules.free_monoidal PresheafOfModules.restrictScalars_laxMonoidal PresheafOfModules.PullbackMonoidal.isIso_δ_gS PresheafOfModules.pullback_oplaxMonoidal PresheafOfModules.PullbackMonoidal.instPreservesColimitsOfSizeCompOppositeCommRingCatRingCatForget₂RingHomCarrierCarrierPb PresheafOfModules.pullback_monoidal' AlgebraicGeometry.SmoothOfRelativeDimension.fiberToSpecResidueField AlgebraicGeometry.SmoothOfRelativeDimension.pullback_snd AlgebraicGeometry.SmoothOfRelativeDimension.pullback_fst AlgebraicGeometry.SmoothOfRelativeDimension.smooth_one AlgebraicGeometry.SmoothProperCurve.isIntegral_pullback_Spec_field AlgebraicGeometry.IsProper.fiberToSpecResidueField"
p2m_attr_erase "instance" "AlgebraicCurve.CurveModel.isProper AlgebraicCurve.CurveModel.isIntegral AlgebraicCurve.CurveModel.smooth AlgebraicGeometry.Scheme.LocalRepresentabilityULift.instIsLocallyInjectiveFunUliftYonedaGluedToSheaf AlgebraicGeometry.Scheme.LocalRepresentabilityULift.instIsLocallySurjectiveFunUliftYonedaGluedToSheafOfIsLocallySurjectiveZariskiTopologyDescFunctorOppositeType AlgebraicGeometry.Scheme.LocalRepresentabilityULift.instIsOpenImmersionToGlued AlgebraicGeometry.Scheme.LocalRepresentabilityULift.instIsIsoSheafZariskiTopologyTypeUliftYonedaGluedToSheaf AlgebraicGeometry.RelPicard.instIsOpenImmersionToGlued AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.instFundamentalIdentityOfSumRamificationInertia AlgebraicCurve.Place.instIsScalarTowerResidueFieldRestrictPushforward AlgebraicCurve.Place.instAlgebraResidueFieldRestrictPushforward AlgebraicCurve.Place.instIsLocalHomRestrictInclusion AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions PresheafOfModules.ExteriorPower.instModulePresheafAb AlgebraicGeometry.RelEffCartierDiv.subsingleton_of_degree_zero AlgebraicGeometry.RelEffCartierDiv.isIso_subschemeIota_snd_of_degree_one AlgebraicGeometry.isIso_ker_graphOver_subschemeIota_snd AlgebraicGeometry.isClosedImmersion_graphOver AlgebraicGeometry.FGSubalgebra.instIsDirectedLe AlgebraicGeometry.FGSubalgebra.instQuasiSeparatedSpaceCarrierCarrierCommRingCatObjOppositeSchemeSpecDiagram AlgebraicGeometry.FGSubalgebra.instIsCofilteredOpposite AlgebraicGeometry.FGSubalgebra.instIsAffineObjOppositeSchemeSpecDiagram AlgebraicGeometry.FGSubalgebra.instNonempty AlgebraicGeometry.FGSubalgebra.instNonemptySubtypeLeSubalgebraValFG AlgebraicGeometry.FGSubalgebra.instCompactSpaceCarrierCarrierCommRingCatObjOppositeSchemeSpecDiagram AlgebraicGeometry.FGSubalgebra.instIsDirectedSubtypeLeSubalgebraValFG AlgebraicGeometry.FGSubalgebra.instIsAffineHomMapOppositeSchemeSpecDiagram AlgebraicGeometry.FGSubalgebra.instIsFiltered AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instNeg AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instSMulInt AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instAddCommGroup AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instAdd AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instSub"
p2m_attr_erase "instance" "AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instModuleCarrierObjOppositeOpensCarrierCarrierCommRingCatPresheafOpOpensTop AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instSMulCarrierObjOppositeOpensCarrierCarrierCommRingCatPresheafOpOpensTop AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instSMulNat AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instZero AlgebraicCurve.instHasLocalResidue_of_hasCanonicalLocalResidueK AlgebraicCurve.instHasCanonicalLocalResidueK_of_hasCanonicalLocalResidueKStar AlgebraicCurve.Place.kw_ffgc_finiteDimensional_adicCompletion instAlgebraSubtypeMemValuationSubring_definitions AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersIntegersCompletion ModularCurve.KwF4gRRTate.instAlgebraKAdicCompletionIntegers AlgebraicCurve.Place.kw_ffgc_continuousSMul_adicCompletionComap AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersCompletionCompletion IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions AlgebraicCurve.instHasCanonicalLocalResidueK AlgebraicCurve.Place.instAlgebra_restrictResidueField AlgebraicCurve.Place.instIsScalarTower_restrictResidueField AlgebraicCurve.instHasLocalResidue AlgebraicCurve.HasSeparableResidue.of_perfectField_of_isCurveOver AlgebraicCurve.HasSeparableResidue.of_perfectField AlgebraicCurve.Place.instIsLocalHom_restrictSubringHom AlgebraicCurve.instHasCanonicalLocalResidueKStar ModularCurve.KwNo6Pin.isLocalRing_completion SheafOfModules.isIso_ihomModelToIhom AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instDecidableEqIdx AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instFintype AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instLinearOrder AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instFintypeIdx AlgebraicGeometry.OModulePresheaf.Leray.relAltC_scalarTower AlgebraicGeometry.OModulePresheaf.Leray.ker_relAltd_modΓ AlgebraicGeometry.OModulePresheaf.Leray.relAltC_modΓ AlgebraicGeometry.OModulePresheaf.Leray.biC_abGrp AlgebraicGeometry.OModulePresheaf.Leray.relAltH_modΓ AlgebraicGeometry.OModulePresheaf.Leray.ker_relAltd_smul AlgebraicGeometry.OModulePresheaf.Leray.relAltH_scalarTower AlgebraicGeometry.OModulePresheaf.Leray.relAltH_smul"
p2m_attr_erase "instance" "AlgebraicGeometry.OModulePresheaf.Leray.biC_module DoubleComplex.instModuleE₂I DoubleComplex.Bounded.modR DoubleComplex.instModuleE₂II DoubleComplex.instAddCommGroupE₂II DoubleComplex.Bounded.abGrp DoubleComplex.instAddCommGroupE₂I AlgebraicGeometry.ChowDatum.hι_closed AlgebraicGeometry.ChowDatumProj.hιN_closed AlgebraicGeometry.ChowDatumProj.hp_proper AlgebraicGeometry.ChowDatum.hp_isoU AlgebraicGeometry.ChowDatum.hp_proper AlgebraicGeometry.ProjSpace.algebraAway AlgebraicGeometry.ProjSpace.instIsProperProdOverπ AlgebraicGeometry.ChowDatumProj.hp_isoU AlgebraicGeometry.ProjSpace.isProper_π AlgebraicGeometry.ProjSpace.finiteType_mvPolynomial ProjSpaceCech.GradedModule.H.module ProjSpaceCech.GradedModule.H.addCommGroup ProjSpaceCech.GradedModule.sec.instAdd ProjSpaceCech.GradedModule.sec.instNeg ProjSpaceCech.GradedModule.acg ProjSpaceCech.GradedModule.Frac.setoid ProjSpaceCech.GradedModule.modR ProjSpaceCech.GradedModule.sec.instModule ProjSpaceCech.GradedModule.sec.instAddCommGroup ProjSpaceCech.GradedModule.sec.instZero ProjSpaceCech.GradedModule.Presentation.fJ ProjSpaceCech.GradedModule.sec.instSMul ProjSpaceCech.Twist.H.module ProjSpaceCech.Idx.instFintype ProjSpaceCech.Twist.H.addCommGroup ProjSpaceCech.Idx.instDecidableEq ProjSpaceCech.Twist.Mon.instDecidableEq ProjSpaceCech.Twist.cochain.instAddCommGroup ProjSpaceCech.Twist.cochain.instModule AlgebraicGeometry.FGSubalgebra.tensorStage_directedSystem AlgebraicGeometry.RelEffCartierDiv.isClosedImmersion_subschemeι_resProdMap AlgebraicGeometry.RelEffCartierDiv.isOpenImmersion_resProdMap AlgebraicCurve.CurveModel.locallyOfFiniteType_gluedToBase"
p2m_attr_erase "instance" "AlgebraicCurve.CurveModel.isFractionRing_overlap AlgebraicCurve.CurveModel.isLocallyNoetherian_glued AlgebraicCurve.CurveModel.jacobsonSpace_glued AlgebraicCurve.CurveModel.isOpenImmersion_ι₀ AlgebraicCurve.CurveModel.isIntegral_glued AlgebraicCurve.CurveModel.quasiSeparated_gluedToBase AlgebraicCurve.CurveModel.compactSpace_glued AlgebraicCurve.CurveModel.isIntegral_adjoin_chartRing AlgebraicCurve.CurveModel.isFractionRing_overlap_functionField AlgebraicCurve.CurveModel.isProper_gluedToBase AlgebraicCurve.CurveModel.isOpenImmersion_ιU AlgebraicCurve.CurveModel.isOpenImmersion_f₀ AlgebraicCurve.CurveModel.isOpenImmersion_fInf AlgebraicCurve.CurveModel.isOpenImmersion_ιInf AlgebraicCurve.CurveModel.algebra_overlap_functionField AlgebraicCurve.CurveModel.quasiCompact_gluedToBase AlgebraicCurve.CurveModel.algebraAdjoin AlgebraicCurve.CurveModel.isDedekindDomain_chartRing AlgebraicCurve.CurveModel.isIntegralClosure AlgebraicCurve.CurveModel.finite_chartRing AlgebraicCurve.CurveModel.centre_isPrime AlgebraicCurve.CurveModel.isFractionRing_chartRing AlgebraicCurve.CurveModel.finiteType_chartRing AlgebraicCurve.CurveModel.isNoetherianRing_chartRing AlgebraicCurve.CurveModel.isScalarTower_base_adjoin AlgebraicCurve.CurveModel.isScalarTower_adjoin AlgebraicCurve.CurveModel.chartRing_finitePresentation instTopologicallyFGOfFiniteType AlgebraicGeometry.ProjSpace.twistObj.addCommGroup AlgebraicGeometry.ProjSpace.twistFam.module AlgebraicGeometry.ProjSpace.twistObj.module AlgebraicGeometry.ProjSpace.twistObj.moduleSections AlgebraicGeometry.ProjSpace.twistFam.addCommGroup"
p2m_attr_erase "simp" "GoodReductionJacobian.RelativeGroupLaw.nsmul_zero GoodReductionJacobian.RelativeGroupLaw.mem_torsionSubset GoodReductionJacobian.RelativeGroupLaw.nsmul_succ NeronModelInfra.NeronModelPropertyBundle.endExtensionEquiv_symm_restrict NeronModelInfra.schemeHomOverComp_id_left NeronModelInfra.schemeHomOverComp_id_right NeronModelInfra.schemeHomOverId_coe NeronModelInfra.NeronModelPropertyBundle.endExtensionEquiv_apply NeronModelInfra.NeronModelPropertyBundle.restrict_endExtensionEquiv_symm NeronModelInfra.schemeHomOverComp_coe NeronModelInfra.schemeHomOverNpow_succ NeronModelInfra.schemeHomOverNpow_zero GoodReductionJacobian.relativeGroupLawOfGrpObj_inv GoodReductionJacobian.relativeGroupLawOfGrpObj_mul GoodReductionJacobian.overHomEquivSchemeHomOver_apply_coe GoodReductionJacobian.relativeGroupLawOfGrpObj_one GoodReductionJacobian.overHomEquivSchemeHomOver_symm_apply_left SheafOfModules.tensorUnit_eq AlgebraicGeometry.Scheme.Modules.tensorUnit_eq PresheafOfModules.InternalHom.presheaf_map_apply PresheafOfModules.InternalHom.curryFamily_app PresheafOfModules.InternalHom.add_app PresheafOfModules.InternalHom.smul_app PresheafOfModules.InternalHom.zero_app PresheafOfModules.ihomObj_map_val PresheafOfModules.ihomFunctor_map PresheafOfModules.InternalHom.restrict_app PresheafOfModules.InternalHom.postcomp_app PresheafOfModules.InternalHom.neg_app PresheafOfModules.curry'_app_val PresheafOfModules.InternalHom.presheaf_obj PresheafOfModules.ihomFunctor_obj PresheafOfModules.ihomObj_obj PresheafOfModules.InternalHom.sub_app PresheafOfModules.ihomMap_app_val AlgebraicGeometry.Scheme.Modules.tensorPow_zero AlgebraicGeometry.Scheme.Modules.tensorPow_succ AlgebraicGeometry.RelPicard.RigidifiedLineBundle.mk.sizeOf_spec AlgebraicGeometry.RelPicard.RigidifiedLineBundle.mk.injEq AlgebraicGeometry.Scheme.OrderedAffineCover.mk.injEq"
p2m_attr_erase "simp" "AlgebraicGeometry.OModulePresheaf.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCover.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.mk.injEq AlgebraicGeometry.Scheme.TwoAffineOpenCover.mk.injEq AlgebraicGeometry.Scheme.TwoAffineOpenCover.mk.sizeOf_spec AlgebraicGeometry.Scheme.TwoAffineOpenCover.pullback_U1 AlgebraicGeometry.Scheme.TwoAffineOpenCover.pullback_U0 TwoChartCech.Sections.mk.injEq TwoChartCech.Cover.mk.injEq TwoChartCech.GrothendieckComplex.mk.injEq TwoChartCech.Sections.mk.sizeOf_spec TwoChartCech.Cover.mk.sizeOf_spec TwoChartCech.Cover.lineBundle_r0_apply TwoChartCech.GrothendieckComplex.mk.sizeOf_spec TwoChartCech.Cover.lineBundle_r1_apply CoherentBaseChange.TwoTermComplex.mk.sizeOf_spec CoherentBaseChange.TwoTermComplex.mk.injEq AlgebraicGeometry.OModulePresheaf.prod_obj AlgebraicGeometry.OModulePresheaf.restrOpen_obj AlgebraicGeometry.OModulePresheaf.DevissageStep.mk.injEq AlgebraicGeometry.OModulePresheaf.pushforward_obj AlgebraicGeometry.OModulePresheaf.im_obj AlgebraicGeometry.OModulePresheaf.pow_obj AlgebraicGeometry.OModulePresheaf.fstHom_app AlgebraicGeometry.OModulePresheaf.ker_obj AlgebraicGeometry.OModulePresheaf.coker_obj AlgebraicGeometry.OModulePresheaf.DevissageStep.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCover.preimage_U AlgebraicGeometry.OModulePresheaf.sndHom_app AlgebraicGeometry.OModulePresheaf.Hom.mk.injEq AlgebraicGeometry.OModulePresheaf.Hom.id_app AlgebraicGeometry.OModulePresheaf.AffHom.appSections_apply AlgebraicGeometry.OModulePresheaf.AffHom.comp_app AlgebraicGeometry.OModulePresheaf.AffSES.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.AffHom.kerMap_coe AlgebraicGeometry.OModulePresheaf.AffHom.id_app AlgebraicGeometry.OModulePresheaf.Hom.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.Hom.toAffHom_app AlgebraicGeometry.OModulePresheaf.SES.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.AffHom.mk.sizeOf_spec"
p2m_attr_erase "simp" "AlgebraicGeometry.OModulePresheaf.Hom.comp_app AlgebraicGeometry.OModulePresheaf.SES.mk.injEq AlgebraicGeometry.OModulePresheaf.AffHom.mk.injEq AlgebraicGeometry.OModulePresheaf.Hom.appSections_apply AlgebraicGeometry.OModulePresheaf.AffSES.mk.injEq PresheafOfModules.freeεIso_hom_app PresheafOfModules.freeμIso_hom_app AlgebraicGeometry.RelPicard.RepresentsRelSubPic.mk.injEq AlgebraicGeometry.RelPicard.SubPicCondition.mk.injEq AlgebraicGeometry.RelPicard.SubPicCondition.mk.sizeOf_spec AlgebraicGeometry.RelPicard.RepresentsRelSubPic.mk.sizeOf_spec AlgebraicGeometry.SmoothProperCurve.sectionBaseChange_coe_snd AlgebraicGeometry.SmoothProperCurve.sectionBaseChange_coe_fst AlgebraicCurve.CurveModel.mk.injEq AlgebraicCurve.CurveModel.mk.sizeOf_spec AlgebraicCurve.mulAdele_apply AlgebraicCurve.residuePairing_apply_coe AlgebraicCurve.mem_adeleBdd AlgebraicCurve.weilSmul_one AlgebraicCurve.diagonalHom_apply AlgebraicCurve.weilSmul_apply AlgebraicCurve.adeleSpaceMul_coe AlgebraicCurve.mulAdele_one AlgebraicGeometry.SmoothProperCurve.FiniteMapData.twoAffineOpenCover_U1 AlgebraicGeometry.SmoothProperCurve.FiniteMapData.mk.injEq AlgebraicGeometry.SmoothProperCurve.FiniteMapData.mk.sizeOf_spec AlgebraicGeometry.SmoothProperCurve.FiniteMapData.twoAffineOpenCover_U0 AlgebraicGeometry.RelPicard.SubPicCondition.onClasses_mk AlgebraicGeometry.RelPicard.relSubPicPresheaf_map_coe CategoryTheory.Functor.OverTotal.ofFibre_fst CategoryTheory.Functor.overTotal_map_fst AlgebraicGeometry.Scheme.LocalRepresentabilityULift.glueData_J AlgebraicGeometry.Scheme.LocalRepresentabilityULift.uliftYoneda_toGlued_uliftYonedaGluedToSheaf AlgebraicGeometry.Scheme.LocalRepresentabilityULift.glueData_t' AlgebraicGeometry.Scheme.LocalRepresentabilityULift.uliftYoneda_toGlued_uliftYonedaGluedToSheaf_assoc AlgebraicGeometry.Scheme.LocalRepresentabilityULift.uliftYonedaGluedToSheaf_app_toGlued AlgebraicGeometry.Scheme.LocalRepresentabilityULift.glueData_openCover_map AlgebraicGeometry.Scheme.LocalRepresentabilityULift.uliftYonedaGluedToSheaf_app_comp AlgebraicGeometry.Scheme.LocalRepresentabilityULift.glueData_V AlgebraicGeometry.Scheme.LocalRepresentabilityULift.glueData_t"
p2m_attr_erase "simp" "AlgebraicGeometry.Scheme.LocalRepresentabilityULift.glueData_U AlgebraicGeometry.Scheme.LocalRepresentabilityULift.glueData_f AlgebraicGeometry.RelPicard.designationOfRepresentableBy_P AlgebraicGeometry.RelPicard.designationOfRepresentableBy_toBase AlgebraicGeometry.RelPicard.rigSection_snd AlgebraicGeometry.RelPicard.RigidifiedLineBundle.ofInvertible_L AlgebraicGeometry.RelPicard.rigSection_snd_assoc AlgebraicGeometry.RelPicard.SubPicGroupCondition.mk.injEq AlgebraicGeometry.RelPicard.SubPicGroupCondition.mk.sizeOf_spec AlgebraicCurve.coe_cechH0Equiv_apply AlgebraicCurve.cechH1ToH1_mk AlgebraicCurve.lSpaceOn_univ AlgebraicCurve.lSpaceOn_empty AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.Divisor.mapRestrict_single AlgebraicCurve.Divisor.pushforward_single AlgebraicCurve.Place.coe_restrictInclusion AlgebraicCurve.Place.mem_fiber AlgebraicCurve.Place.restrict_toValuationSubring AlgebraicCurve.Divisor.degree_pushforward AlgebraicCurve.Place.restrictResidueMap_residue AlgebraicCurve.Pic0.coe_pushforwardDegZeroHom AlgebraicCurve.Pic0.coe_pullbackDegZeroHom AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk"
p2m_attr_erase "simp" "ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Divisor.degree_pushforwardAlong AlgebraicCurve.Pic0.coe_degZeroCorrespondence AlgebraicCurve.Place.mem_fiberAlong AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.jqNModC_one ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one AlgebraicCurve.Place.differentialCoeff_zero AlgebraicCurve.Place.differentialCoeff_dCoord AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.injEq AlgebraicCurve.TranscendenceTower.mk.injEq AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec AlgebraicCurve.PoleDivisorPackage.mk.injEq AlgebraicGeometry.RelPicard.thetaBundle_def AlgebraicGeometry.RelPicard.picardBundle_def AlgebraicGeometry.RelEffCartierDiv.toRelEffDivisor_ofRelEffDivisor AlgebraicGeometry.RelEffCartierDiv.toRelEffDivisor_I"
p2m_attr_erase "simp" "AlgebraicGeometry.mapOnProdOver_fst_assoc AlgebraicGeometry.RelEffCartierDiv.mk.sizeOf_spec AlgebraicGeometry.RelEffCartierDiv.mk.injEq AlgebraicGeometry.mapOnProdOver_snd AlgebraicGeometry.mapOnProdOver_fst AlgebraicGeometry.mapOnProdOver_snd_assoc AlgebraicGeometry.mapOnProdOver_id AlgebraicCurve.RelEffDivisor.mk.sizeOf_spec AlgebraicCurve.mapOnProd_fst AlgebraicCurve.mapOnProd_fst_assoc AlgebraicCurve.mapOnProd_snd AlgebraicCurve.UnivDivisorPack.mk.injEq AlgebraicCurve.RelEffDivisor.mk.injEq AlgebraicCurve.UnivDivisorPack.mk.sizeOf_spec AlgebraicCurve.mapOnProd_snd_assoc AlgebraicGeometry.Scheme.Modules.exteriorPower_obj PresheafOfModules.exteriorPower_map_ιMulti PresheafOfModules.ExteriorPower.appₗ_apply AlgebraicGeometry.prodKerGraph_one AlgebraicGeometry.fibrePowOver.proj_comp AlgebraicGeometry.prodKerGraph_zero AlgebraicGeometry.RelEffCartierDiv.empty_I AlgebraicGeometry.fibrePowOver.proj_comp_assoc AlgebraicGeometry.graphOver_fst_assoc AlgebraicGeometry.RelEffCartierDiv.toPoint_comp AlgebraicGeometry.RelEffCartierDiv.toPoint_comp_assoc AlgebraicGeometry.graphOver_fst AlgebraicGeometry.RelEffCartierDiv.ofPoint_I AlgebraicGeometry.graphOver_snd AlgebraicGeometry.graphOver_snd_assoc AlgebraicCurve.SymmetricPowerPackage.mk.sizeOf_spec AlgebraicCurve.SymmetricPowerPackage.mk.injEq AlgebraicGeometry.FGSubalgebra.cocone_ι_app_apply AlgebraicGeometry.RelPicard.fst_toProdSpec AlgebraicGeometry.RelPicard.toProdSpec_fst_assoc AlgebraicGeometry.RelPicard.pointsSubBasepointModule_cons AlgebraicGeometry.RelPicard.pointsSubBasepointModule_nil AlgebraicGeometry.RelPicard.fst_toProdSpec_assoc AlgebraicGeometry.RelPicard.toProdSpec_fst AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.sub_app"
p2m_attr_erase "simp" "AlgebraicGeometry.Scheme.IdealSheafData.sres_sresTop AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.add_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.mk.sizeOf_spec AlgebraicGeometry.Scheme.IdealSheafData.coe_resLE AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.smul_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.coe_ofLE_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.ideal_range AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.zero_app AlgebraicGeometry.Scheme.IdealSheafData.sres_sres AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.comp_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.neg_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.id_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.coe_mulRight_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.nsmul_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.mk.injEq AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.zsmul_app AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.sizeOf_spec AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.injEq AlgebraicCurve.adeleSingle_coe AlgebraicCurve.kaehlerResidueTermKFam_apply AlgebraicCurve.Place.LocalResidueData.mk.injEq AlgebraicCurve.Place.LocalResidueData.mk.sizeOf_spec AlgebraicCurve.Place.kw_ffgc_adicCompletionComapIntegers_coe AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.sizeOf_spec AlgebraicCurve.Place.mem_simplePoleSubmodule AlgebraicCurve.Place.coe_uniformizerSubring ModularCurve.Lg37.Lg37CompletionSection.mk.injEq AlgebraicCurve.Place.CoefficientFieldSection.mk.injEq AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.injEq ModularCurve.Lg37.Lg37CompletionSection.mk.sizeOf_spec AlgebraicCurve.Place.CoefficientFieldSection.mk.sizeOf_spec AlgebraicCurve.Place.poleSubmodule_one AlgebraicCurve.Place.mem_poleSubmodule AlgebraicGeometry.Scheme.Modules.toUnitSection_ofUnitSection AlgebraicGeometry.Scheme.Modules.pullbackSection_def AlgebraicGeometry.Scheme.Modules.ofUnitSection_toUnitSection PresheafOfModules.InternalHom.IsSheafAux.appAt_toPresheafHom SheafOfModules.ihomSectionsEquivFamily_unit AlgebraicGeometry.Scheme.Modules.restrictHomEquivFamily_apply SheafOfModules.ihomEval_unit_app"
p2m_attr_erase "simp" "AlgebraicGeometry.Scheme.Modules.ihomEval_zero_right AlgebraicGeometry.Scheme.Modules.ihomEval_zero_left AlgebraicGeometry.Scheme.Modules.homOfFamily_app_apply SheafOfModules.unit_ihomSectionsEquivFamily AlgebraicGeometry.Scheme.Modules.familyOfHom_app AlgebraicGeometry.Scheme.Modules.restrictUnitIso_hom_app_apply AlgebraicGeometry.Scheme.Modules.restrictUnitIso_inv_app_apply AlgebraicGeometry.Scheme.Modules.restrictHomOfFamily_app_apply AlgebraicGeometry.Scheme.Modules.restrictHomEquivFamily_symm_apply AlgebraicGeometry.Scheme.Modules.tensorSections_zero_right AlgebraicGeometry.Scheme.Modules.map_unitSection AlgebraicGeometry.Scheme.Modules.tensorSectionsBilin_apply AlgebraicGeometry.Scheme.Modules.tensorPowSection_zero AlgebraicGeometry.Scheme.Modules.tensorSections_zero_left AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_neg AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_zero AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_sub AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_add AlgebraicGeometry.Scheme.OrderedAffineCover.toCoverOf_U AlgebraicGeometry.Scheme.OrderedAffineCoverOf.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCoverOf.mk.injEq AlgebraicGeometry.Scheme.OrderedAffineCover.restrict_U AlgebraicGeometry.OModulePresheaf.Leray.restrictToPreimage_U DoubleComplex.Bounded.mk.injEq DoubleComplex.Bounded.mk.sizeOf_spec DoubleComplex.Convergence.mk.injEq DoubleComplex.Convergence.mk.sizeOf_spec DoubleComplex.SubQuot.mk.sizeOf_spec DoubleComplex.SubQuot.mk.injEq AlgebraicGeometry.ChowDatumProj.mk.sizeOf_spec AlgebraicGeometry.ChowDatum.mk.sizeOf_spec AlgebraicGeometry.ChowDatumProj.mk.injEq AlgebraicGeometry.ChowDatum.mk.injEq ProjSpaceCech.GradedModule.mk.injEq ProjSpaceCech.GradedModule.mk.sizeOf_spec ProjSpaceCech.GradedModule.Frac.mk.sizeOf_spec ProjSpaceCech.GradedModule.Presentation.mk.injEq ProjSpaceCech.GradedModule.Frac.mk.injEq ProjSpaceCech.GradedModule.Presentation.mk.sizeOf_spec ProjSpaceCech.GradedModule.Hom.shift_toLinearMap"
p2m_attr_erase "simp" "ProjSpaceCech.GradedModule.Hom.mk.sizeOf_spec ProjSpaceCech.GradedModule.Hom.mk.injEq TwoChartCech.Mumford.dK_apply TwoChartCech.Mumford.ι0_apply TwoChartCech.Mumford.ι1_apply TwoChartCech.KerCoprod.dK_apply TwoChartCech.KerCoprod.ι1_apply TwoChartCech.KerCoprod.ι0_apply AlgebraicGeometry.tilde.functorCompPullbackSpecIso_app AlgebraicGeometry.RelPicard.algEquivZeroGroupCut_toSubPicCondition AlgebraicGeometry.RelPicard.LFP.stageHom_val AlgebraicGeometry.RelPicard.BaseChange.relSubPicPresheafRestrictIso_hom_app_coe AlgebraicGeometry.RelPicard.BaseChange.relSubPicPresheafRestrictIso_inv_app_coe AlgebraicGeometry.RelPicard.BaseChange.restrict_P AlgebraicGeometry.RelEffCartierDiv.IsUniversal.lift_comp AlgebraicGeometry.RelEffCartierDiv.functor_map_fst AlgebraicGeometry.RelEffCartierDiv.IsUniversal.homEquiv_apply AlgebraicGeometry.RelEffCartierDiv.IsUniversal.lift_pullbackAlong AlgebraicGeometry.RelEffCartierDiv.IsUniversal.homEquiv_symm_apply AlgebraicGeometry.RelEffCartierDiv.IsUniversal.lift_comp_assoc AlgebraicGeometry.RelEffCartierDiv.supportedIn_top AlgebraicGeometry.RelEffCartierDiv.mem_supportedIn_iff AlgebraicGeometry.RelEffCartierDiv.supportedIn_top_eq AlgebraicGeometry.RelEffCartierDiv.restrictAlong_extendAlong AlgebraicGeometry.RelEffCartierDiv.extendAlong_I AlgebraicGeometry.RelEffCartierDiv.resProdMap_snd AlgebraicGeometry.RelEffCartierDiv.restrictAlong_I AlgebraicGeometry.RelEffCartierDiv.extendAlong_restrictAlong AlgebraicGeometry.RelEffCartierDiv.resProdMap_fst_assoc AlgebraicGeometry.RelEffCartierDiv.resProdMap_snd_assoc AlgebraicGeometry.RelEffCartierDiv.resProdMap_fst CoherentBaseChange.FibreH0Family.mk.sizeOf_spec CoherentBaseChange.FibreH0Family.mk.injEq AlgebraicGeometry.Scheme.Modules.ProjPresentation.mk.injEq AlgebraicGeometry.Scheme.Modules.ProjPresentation.mk.sizeOf_spec AlgebraicCurve.CurveModel.coe_gInf AlgebraicCurve.CurveModel.coe_tInvChart AlgebraicCurve.CurveModel.ιInf_gluedToBase_assoc AlgebraicCurve.CurveModel.ιInf_gluedToBase AlgebraicCurve.CurveModel.primeOfι₀_asIdeal"
p2m_attr_erase "simp" "AlgebraicCurve.CurveModel.coe_tChart AlgebraicCurve.CurveModel.ι₀_gluedToBase_assoc AlgebraicCurve.CurveModel.primeOfιInf_asIdeal AlgebraicCurve.CurveModel.ι₀_gluedToBase AlgebraicCurve.CurveModel.coe_tma AlgebraicCurve.CurveModel.coe_primeEquivChartPlaces RegularLocalRingQuotientAscent.dualNumberFst_apply AlgebraicGeometry.ProjSpace.twistObj.mk.injEq AlgebraicGeometry.ProjSpace.twistObj.zero_val AlgebraicGeometry.ProjSpace.twistObj.add_val AlgebraicGeometry.ProjSpace.twist_res_val AlgebraicGeometry.ProjSpace.twist_smul_val AlgebraicGeometry.ProjSpace.twistGradeToObj_val AlgebraicGeometry.ProjSpace.twistObj.smul_val AlgebraicGeometry.ProjSpace.twistGradeEquiv_apply_val AlgebraicGeometry.ProjSpace.twistObj.mk.sizeOf_spec QuaternionAlgebra.baseChangeRight_tmul QuaternionAlgebra.mapOfAlgebraMapEq_apply QuaternionAlgebra.baseChange_tmul QuaternionAlgebra.ClassSet.map_mk"

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 6400000
set_option synthInstance.maxHeartbeats 1600000

open scoped Quaternion
open CategoryTheory AlgebraicGeometry CerednikDrinfeld CerednikDrinfeld.QM QuaternionAlgebra NeronModelInfra GoodReductionJacobian

noncomputable section

namespace CntRam

variable {a b : ℚ}

theorem nrd_mul' (x y : ℍ[ℚ, a, b]) : nrd (x * y) = nrd x * nrd y := by
  obtain ⟨x₀, x₁, x₂, x₃⟩ := x
  obtain ⟨y₀, y₁, y₂, y₃⟩ := y
  simp only [QuaternionAlgebra.mk_mul_mk, nrd_mk]
  ring

theorem zsmul_eq_coe_mul (r : ℕ) (y : ℍ[ℚ, a, b]) : (r : ℤ) • y = ((r : ℚ) : ℍ[ℚ, a, b]) * y := by
  rw [coe_mul_eq_smul, ← Int.cast_smul_eq_zsmul ℚ, Int.cast_natCast]

theorem mul_zsmul_comm' (m z : ℍ[ℚ, a, b]) (c : ℤ) : m * (c • z) = c • (m * z) := by
  rw [← Int.cast_smul_eq_zsmul ℚ, mul_smul_comm, Int.cast_smul_eq_zsmul]

theorem zsmul_mul_assoc' (m z : ℍ[ℚ, a, b]) (c : ℤ) : (c • m) * z = c • (m * z) := by
  rw [← Int.cast_smul_eq_zsmul ℚ, smul_mul_assoc, Int.cast_smul_eq_zsmul]

theorem natCast_eq_coe' (m : ℕ) : ((m : ℕ) : ℍ[ℚ, a, b]) = ((m : ℚ) : ℍ[ℚ, a, b]) := by
  ext <;> simp

theorem star_coe' (c : ℚ) : star ((c : ℚ) : ℍ[ℚ, a, b]) = c := by
  have : ((c : ℚ) : ℍ[ℚ, a, b]) = ⟨c, 0, 0, 0⟩ := rfl
  rw [this, QuaternionAlgebra.star_mk]; ext <;> simp

theorem main {q q' : ℕ} [Fact q.Prime] [Fact q'.Prime] (hqq' : q' ≠ q) (hB : IsIndefiniteRamifiedExactlyAt a b q q')
    (Λ : Submodule ℤ ℍ[ℚ, a, b]) (hΛ : IsMaximalOrder Λ) {N : ℕ}
    (k : Type) [Field k] [IsAlgClosed k] (E : FakeEllipticCurve Λ N k)
    (r : ℕ) (hr : r = q ∨ r = q') (hrk : (r : k) ≠ 0) :
    Nat.card {P : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) E.f //
      ∀ (m : ↥Λ) (n : ℤ), (m : ℍ[ℚ, a, b]) * star (m : ℍ[ℚ, a, b]) = (((r : ℤ) * n : ℚ) : ℍ[ℚ, a, b]) →
        pushPt (E.act m) (E.act_over m) P = E.L.one (𝟙 (Spec (CommRingCat.of k)))} = r ^ 2 := by
  classical
  have hO : IsOrder Λ := hΛ.isOrder
  have hrp : r.Prime := by
    rcases hr with h1 | h1 <;> rw [h1] <;> exact Fact.out
  haveI : Fact r.Prime := ⟨hrp⟩
  haveI : NeZero r := ⟨hrp.ne_zero⟩

  obtain ⟨⟨hleft, hrP, ⟨y, hyΛ, ⟨ny, hny⟩, hynot⟩, ⟨w, hwΛ, hwnot⟩, hsq⟩, htri⟩ :=
    QuaternionAlgebra.IsMaximalOrder.leftIdeal_eq_or_eq_or_eq_of_isIndefiniteRamifiedExactlyAt_of_eq_or_eq hB Λ hΛ r hr
  let InP : ℍ[ℚ, a, b] → Prop := fun x => x ∈ Λ ∧ ∃ n : ℤ, nrd x = (r : ℚ) * n

  have hright : ∀ x, InP x → ∀ l ∈ Λ, InP (x * l) := by
    rintro x ⟨hx, n, hn⟩ l hl
    obtain ⟨⟨nl, hnl⟩, -⟩ := IsOrder.exists_intCast_eq_nrd_and_exists_intCast_eq_trd hO hl
    refine ⟨hO.mul_mem hx hl, n * nl, ?_⟩
    rw [nrd_mul', hn, ← hnl]; push_cast; ring

  set H : AddSubgroup ℍ[ℚ, a, b] :=
    (Submodule.span ℤ ((fun z : ℍ[ℚ, a, b] => (r : ℤ) • z) '' (Λ : Set ℍ[ℚ, a, b]))).toAddSubgroup with hH
  have hindex : H.relIndex Λ.toAddSubgroup = r ^ 4 :=
    QuaternionAlgebra.IsOrder.relIndex_span_smul_eq_pow_four hO r hrp.pos
  have hHmem : ∀ μ ∈ Λ, (r : ℤ) • μ ∈ H := by
    intro μ hμ
    rw [hH, Submodule.mem_toAddSubgroup]
    exact Submodule.subset_span ⟨μ, hμ, rfl⟩
  have hHmem' : ∀ z ∈ H, ∃ μ ∈ Λ, z = (r : ℤ) • μ := by
    intro z hz
    rw [hH, Submodule.mem_toAddSubgroup] at hz
    have hle : Submodule.span ℤ ((fun z : ℍ[ℚ, a, b] => (r : ℤ) • z) '' (Λ : Set ℍ[ℚ, a, b]))
        ≤ Λ.map ((r : ℤ) • (LinearMap.id : ℍ[ℚ, a, b] →ₗ[ℤ] ℍ[ℚ, a, b])) := by
      rw [Submodule.span_le]
      rintro z ⟨μ, hμ, rfl⟩
      exact Submodule.mem_map.2 ⟨μ, hμ, rfl⟩
    obtain ⟨μ, hμ, hμz⟩ := Submodule.mem_map.1 (hle hz)
    exact ⟨μ, hμ, by rw [← hμz]; rfl⟩
  have hHΛ : ∀ z ∈ H, z ∈ Λ := by
    intro z hz
    obtain ⟨μ, hμ, rfl⟩ := hHmem' z hz
    exact Λ.smul_mem _ hμ
  have hHP : ∀ z ∈ H, InP z := by
    intro z hz
    obtain ⟨μ, hμ, rfl⟩ := hHmem' z hz
    exact ⟨Λ.smul_mem _ hμ, hrP μ hμ⟩
  have hHzsmul : ∀ (c : ℤ), ∀ z ∈ H, c • z ∈ H := by
    intro c z hz
    obtain ⟨μ, hμ, rfl⟩ := hHmem' z hz
    rw [smul_comm]
    exact hHmem _ (Λ.smul_mem c hμ)
  have hHmul : ∀ m ∈ Λ, ∀ z ∈ H, m * z ∈ H := by
    intro m hm z hz
    obtain ⟨μ, hμ, rfl⟩ := hHmem' z hz
    rw [mul_zsmul_comm']
    exact hHmem _ (hO.mul_mem hm hμ)
  set N : AddSubgroup ↥Λ.toAddSubgroup := H.addSubgroupOf Λ.toAddSubgroup with hN
  have hcardG : Nat.card (↥Λ.toAddSubgroup ⧸ N) = r ^ 4 := hindex
  haveI hfinG : Finite (↥Λ.toAddSubgroup ⧸ N) :=
    Nat.finite_of_card_ne_zero (by rw [hcardG]; exact pow_ne_zero _ hrp.ne_zero)
  have hmemN : ∀ m : ↥Λ.toAddSubgroup, m ∈ N ↔ (m : ℍ[ℚ, a, b]) ∈ H := fun m => Iff.rfl
  have hmk0 : ∀ m : ↥Λ.toAddSubgroup,
      (QuotientAddGroup.mk m : ↥Λ.toAddSubgroup ⧸ N) = 0 ↔ (m : ℍ[ℚ, a, b]) ∈ H := by
    intro m
    rw [QuotientAddGroup.eq_zero_iff, hmemN]
  have hmkeq : ∀ m m' : ↥Λ.toAddSubgroup,
      (QuotientAddGroup.mk m : ↥Λ.toAddSubgroup ⧸ N) = QuotientAddGroup.mk m' ↔
        (-(m : ℍ[ℚ, a, b]) + (m' : ℍ[ℚ, a, b])) ∈ H := by
    intro m m'
    rw [QuotientAddGroup.eq, hmemN]
    rfl

  let f : ↥Λ.toAddSubgroup →+ ↥Λ.toAddSubgroup :=
    { toFun := fun m => ⟨(m : ℍ[ℚ, a, b]) * y, hO.mul_mem m.2 hyΛ⟩
      map_zero' := by apply Subtype.ext; simp
      map_add' := fun m m' => by apply Subtype.ext; simp [add_mul] }
  have hf : ∀ m : ↥Λ.toAddSubgroup, ((f m : ↥Λ.toAddSubgroup) : ℍ[ℚ, a, b]) = (m : ℍ[ℚ, a, b]) * y :=
    fun _ => rfl
  have hfN : N ≤ N.comap f := by
    intro m hm
    rw [AddSubgroup.mem_comap, hmemN, hf]
    rw [hmemN] at hm
    obtain ⟨μ, hμ, hμe⟩ := hHmem' _ hm
    rw [hμe, zsmul_mul_assoc']
    exact hHmem _ (hO.mul_mem hμ hyΛ)
  let ψ : ↥Λ.toAddSubgroup ⧸ N →+ ↥Λ.toAddSubgroup ⧸ N := QuotientAddGroup.map N N f hfN
  have hψ : ∀ m : ↥Λ.toAddSubgroup, ψ (QuotientAddGroup.mk m) = QuotientAddGroup.mk (f m) := fun _ => rfl

  let J : Submodule ℤ ℍ[ℚ, a, b] :=
    { carrier := {x | ∃ l ∈ Λ, ∃ z ∈ H, x = l * y + z}
      add_mem' := by
        rintro x x' ⟨l, hl, z, hz, rfl⟩ ⟨l', hl', z', hz', rfl⟩
        exact ⟨l + l', Λ.add_mem hl hl', z + z', H.add_mem hz hz', by rw [add_mul]; abel⟩
      zero_mem' := ⟨0, Λ.zero_mem, 0, H.zero_mem, by simp⟩
      smul_mem' := by
        rintro c x ⟨l, hl, z, hz, rfl⟩
        exact ⟨c • l, Λ.smul_mem c hl, c • z, hHzsmul c z hz, by rw [smul_add, zsmul_mul_assoc']⟩ }
  have hJmem : ∀ x, x ∈ J ↔ ∃ l ∈ Λ, ∃ z ∈ H, x = l * y + z := fun x => Iff.rfl

  have hstar : ∀ x ∈ Λ, star x ∈ Λ := by
    intro x hx
    obtain ⟨-, t, ht⟩ := IsOrder.exists_intCast_eq_nrd_and_exists_intCast_eq_trd hO hx
    have hs : star x = ((trd x : ℚ) : ℍ[ℚ, a, b]) - x := by
      rw [← add_star_eq_coe_trd, add_sub_cancel_left]
    have hc : ((trd x : ℚ) : ℍ[ℚ, a, b]) = (t : ℤ) • (1 : ℍ[ℚ, a, b]) := by
      rw [← ht, ← Int.cast_smul_eq_zsmul ℚ, ← coe_mul_eq_smul, mul_one]
    rw [hs, hc]
    exact Λ.sub_mem (Λ.smul_mem _ hO.one_mem) hx
  have hnrd_add : ∀ x x' : ℍ[ℚ, a, b], nrd (x + x') = nrd x + nrd x' + trd (x * star x') := by
    intro x x'
    obtain ⟨x₀, x₁, x₂, x₃⟩ := x
    obtain ⟨y₀, y₁, y₂, y₃⟩ := x'
    simp only [QuaternionAlgebra.mk_add_mk, QuaternionAlgebra.star_mk, QuaternionAlgebra.mk_mul_mk, nrd_mk, trd_mk]
    ring
  have htrd_coe_mul : ∀ (c : ℚ) (x : ℍ[ℚ, a, b]), trd ((c : ℍ[ℚ, a, b]) * x) = c * trd x := by
    intro c x
    obtain ⟨x₀, x₁, x₂, x₃⟩ := x
    have hc : ((c : ℚ) : ℍ[ℚ, a, b]) = ⟨c, 0, 0, 0⟩ := rfl
    rw [hc, QuaternionAlgebra.mk_mul_mk, trd_mk, trd_mk]
    ring
  have haddP : ∀ x x', InP x → InP x' → InP (x + x') := by
    rintro x x' ⟨hx, n, hn⟩ ⟨hx', n', hn'⟩
    refine ⟨Λ.add_mem hx hx', ?_⟩
    obtain ⟨z, hz, hxz⟩ := hsq x hx (star x') (hstar x' hx') ⟨n, hn⟩ ⟨n', by rw [nrd_star, hn']⟩
    obtain ⟨-, tz, htz⟩ := IsOrder.exists_intCast_eq_nrd_and_exists_intCast_eq_trd hO hz
    refine ⟨n + n' + tz, ?_⟩
    rw [hnrd_add, hxz, zsmul_eq_coe_mul, htrd_coe_mul, ← htz, hn, hn']
    push_cast
    ring
  have hJΛ : J ≤ Λ := by
    intro x hx
    obtain ⟨l, hl, z, hz, rfl⟩ := (hJmem x).1 hx
    exact Λ.add_mem (hO.mul_mem hl hyΛ) (hHΛ z hz)
  have hJr : ∀ μ ∈ Λ, (r : ℤ) • μ ∈ J := fun μ hμ =>
    (hJmem _).2 ⟨0, Λ.zero_mem, (r : ℤ) • μ, hHmem μ hμ, by simp⟩
  have hJleft : ∀ m ∈ Λ, ∀ x ∈ J, m * x ∈ J := by
    intro m hm x hx
    obtain ⟨l, hl, z, hz, rfl⟩ := (hJmem x).1 hx
    refine (hJmem _).2 ⟨m * l, hO.mul_mem hm hl, m * z, hHmul m hm z hz, ?_⟩
    rw [mul_add, mul_assoc]
  have hJP : ∀ x ∈ J, InP x := by
    intro x hx
    obtain ⟨l, hl, z, hz, rfl⟩ := (hJmem x).1 hx
    exact haddP _ _ ⟨hO.mul_mem hl hyΛ, hleft l hl y hyΛ ⟨ny, hny⟩⟩ (hHP z hz)
  have hJeq : ∀ x, x ∈ J ↔ x ∈ Λ ∧ ∃ n : ℤ, nrd x = (r : ℚ) * n := by
    rcases htri J hJΛ hJr hJleft with h | h | h
    · exfalso
      apply hynot
      have hyJ : y ∈ J := (hJmem _).2 ⟨1, hO.one_mem, 0, H.zero_mem, by simp⟩
      exact (h y).1 hyJ
    · exact h
    · exfalso
      apply hwnot
      have hwJ : w ∈ J := by rw [h]; exact hwΛ
      exact (hJP w hwJ).2

  have hrange : ∀ m : ↥Λ.toAddSubgroup, (QuotientAddGroup.mk m : ↥Λ.toAddSubgroup ⧸ N) ∈ ψ.range ↔
      InP (m : ℍ[ℚ, a, b]) := by
    intro m
    constructor
    · rintro ⟨g, hg⟩
      induction g using QuotientAddGroup.induction_on with | H l => ?_
      rw [hψ, hmkeq, hf] at hg

      have : (m : ℍ[ℚ, a, b]) ∈ J :=
        (hJmem _).2 ⟨l, l.2, _, hg, by abel⟩
      exact (hJeq _).1 this
    · intro hm
      obtain ⟨l, hl, z, hz, hlz⟩ := (hJeq _).2 hm
      refine ⟨QuotientAddGroup.mk ⟨l, hl⟩, ?_⟩
      rw [hψ, hmkeq, hf]
      have : (-( (l : ℍ[ℚ, a, b]) * y) + (m : ℍ[ℚ, a, b])) = z := by rw [hlz]; abel
      rw [show (((⟨l, hl⟩ : ↥Λ.toAddSubgroup) : ℍ[ℚ, a, b])) = l from rfl, this]
      exact hz

  have hker : ∀ g : ↥Λ.toAddSubgroup ⧸ N, g ∈ ψ.ker ↔ g ∈ ψ.range := by
    intro g
    induction g using QuotientAddGroup.induction_on with | H m => ?_
    rw [AddMonoidHom.mem_ker, hψ, hmk0, hf, hrange]

    let J' : Submodule ℤ ℍ[ℚ, a, b] :=
      { carrier := {x | x ∈ Λ ∧ x * y ∈ H}
        add_mem' := by
          rintro x x' ⟨hx, hxy⟩ ⟨hx', hx'y⟩
          exact ⟨Λ.add_mem hx hx', by rw [add_mul]; exact H.add_mem hxy hx'y⟩
        zero_mem' := ⟨Λ.zero_mem, by rw [zero_mul]; exact H.zero_mem⟩
        smul_mem' := by
          rintro c x ⟨hx, hxy⟩
          exact ⟨Λ.smul_mem c hx, by rw [zsmul_mul_assoc']; exact hHzsmul c _ hxy⟩ }
    have hJ'mem : ∀ x, x ∈ J' ↔ x ∈ Λ ∧ x * y ∈ H := fun x => Iff.rfl
    have hJ'Λ : J' ≤ Λ := fun x hx => ((hJ'mem x).1 hx).1
    have hJ'r : ∀ μ ∈ Λ, (r : ℤ) • μ ∈ J' := fun μ hμ =>
      (hJ'mem _).2 ⟨Λ.smul_mem _ hμ, by rw [zsmul_mul_assoc']; exact hHmem _ (hO.mul_mem hμ hyΛ)⟩
    have hJ'left : ∀ l ∈ Λ, ∀ x ∈ J', l * x ∈ J' := by
      intro l hl x hx
      obtain ⟨hxΛ, hxy⟩ := (hJ'mem x).1 hx
      exact (hJ'mem _).2 ⟨hO.mul_mem hl hxΛ, by rw [mul_assoc]; exact hHmul l hl _ hxy⟩
    have hPJ' : ∀ x, InP x → x ∈ J' := by
      rintro x ⟨hx, n, hn⟩
      obtain ⟨z, hz, hxz⟩ := hsq x hx y hyΛ ⟨n, hn⟩ ⟨ny, hny⟩
      exact (hJ'mem _).2 ⟨hx, by rw [hxz]; exact hHmem z hz⟩
    have hJ'eq : ∀ x, x ∈ J' ↔ x ∈ Λ ∧ ∃ n : ℤ, nrd x = (r : ℚ) * n := by
      rcases htri J' hJ'Λ hJ'r hJ'left with h | h | h
      · exfalso
        apply hynot
        exact (h y).1 (hPJ' y ⟨hyΛ, ny, hny⟩)
      · exact h
      · exfalso
        apply hynot
        have h1 : (1 : ℍ[ℚ, a, b]) ∈ J' := by rw [h]; exact hO.one_mem
        obtain ⟨-, h1y⟩ := (hJ'mem _).1 h1
        rw [one_mul] at h1y
        exact hHmem' y h1y
    constructor
    · intro hmy
      exact (hJ'eq _).1 ((hJ'mem _).2 ⟨m.2, hmy⟩)
    · intro hm
      exact ((hJ'mem _).1 ((hJ'eq _).2 hm)).2
  have hker' : ψ.ker = ψ.range := AddSubgroup.ext hker
  have hcard_mul : Nat.card (↥Λ.toAddSubgroup ⧸ N) = Nat.card ψ.range * Nat.card ψ.ker := by
    rw [AddSubgroup.card_eq_card_quotient_mul_card_addSubgroup ψ.ker,
      Nat.card_congr (QuotientAddGroup.quotientKerEquivRange ψ).toEquiv]
  have hrange_card : Nat.card ψ.range = r ^ 2 := by
    rw [hker', hcardG] at hcard_mul
    have : Nat.card ψ.range * Nat.card ψ.range = r ^ 2 * r ^ 2 := by rw [← hcard_mul]; ring
    exact Nat.mul_self_inj.1 this

  letI grp : Group (SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) E.f) :=
    E.L.pointGroup (𝟙 (Spec (CommRingCat.of k)))
  obtain ⟨P₀, hP₀, hgen, hann⟩ :=
    CerednikDrinfeld.QM.FakeEllipticCurve.exists_generator_torsionPoints_of_isMaximalOrder_of_prime hB Λ hΛ k E r hrk
  let Φ : ↥Λ → SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) E.f := fun m => pushPt (E.act m) (E.act_over m) P₀
  have hΦ : ∀ m : ↥Λ, Φ m = pushPt (E.act m) (E.act_over m) P₀ := fun _ => rfl
  have hΦadd : ∀ x x' : ↥Λ, Φ (x + x') = Φ x * Φ x' := fun x x' => E.act_add x x' _ P₀
  have hΦzero : Φ 0 = 1 := by
    have h := hΦadd 0 0
    rw [add_zero] at h
    exact mul_eq_left.1 h.symm
  have hΦneg : ∀ x : ↥Λ, Φ (-x) = (Φ x)⁻¹ := by
    intro x
    have h := hΦadd x (-x)
    rw [add_neg_cancel, hΦzero] at h
    exact (eq_inv_of_mul_eq_one_right h.symm)
  have hΦker : ∀ m : ↥Λ, Φ m = 1 ↔ (m : ℍ[ℚ, a, b]) ∈ H := by
    intro m
    rw [hΦ]
    change pushPt (E.act m) (E.act_over m) P₀ = E.L.one (𝟙 (Spec (CommRingCat.of k))) ↔ _
    rw [hann m]
    constructor
    · rintro ⟨m', hm'⟩
      rw [hm', ← zsmul_eq_coe_mul]
      exact hHmem _ m'.2
    · intro hm
      obtain ⟨μ, hμ, hμe⟩ := hHmem' _ hm
      exact ⟨⟨μ, hμ⟩, by rw [hμe, zsmul_eq_coe_mul]⟩
  have hΦact : ∀ (m x : ↥Λ), pushPt (E.act m) (E.act_over m) (Φ x) =
      Φ ⟨(m : ℍ[ℚ, a, b]) * (x : ℍ[ℚ, a, b]), hO.mul_mem m.2 x.2⟩ := by
    intro m x
    apply Subtype.ext
    simp only [hΦ, mapPt_coe, E.act_mul m x (hO.mul_mem m.2 x.2), Category.assoc]

  have hΦeq : ∀ m m' : ↥Λ, Φ m = Φ m' ↔ (-(m : ℍ[ℚ, a, b]) + (m' : ℍ[ℚ, a, b])) ∈ H := by
    intro m m'
    rw [show (-(m : ℍ[ℚ, a, b]) + (m' : ℍ[ℚ, a, b])) = ((-m + m' : ↥Λ) : ℍ[ℚ, a, b]) by simp, ← hΦker (-m + m'), hΦadd,
      hΦneg, inv_mul_eq_one]

  let Φbar : ↥Λ.toAddSubgroup ⧸ N → SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) E.f := fun c =>
    Quotient.liftOn' c (fun m => Φ ⟨m, m.2⟩) (by
      intro m₁ m₂ h12
      have hd : -m₁ + m₂ ∈ N := QuotientAddGroup.leftRel_apply.mp h12
      rw [hmemN] at hd
      exact (hΦeq ⟨m₁, m₁.2⟩ ⟨m₂, m₂.2⟩).2 hd)
  have hΦbar : ∀ m : ↥Λ.toAddSubgroup, Φbar (QuotientAddGroup.mk m) = Φ ⟨m, m.2⟩ := fun _ => rfl
  have hΦbar_inj : Function.Injective Φbar := by
    intro c₁ c₂ h
    induction c₁ using QuotientAddGroup.induction_on with | H m₁ => ?_
    induction c₂ using QuotientAddGroup.induction_on with | H m₂ => ?_
    rw [hΦbar, hΦbar] at h
    rw [hmkeq]
    exact (hΦeq ⟨m₁, m₁.2⟩ ⟨m₂, m₂.2⟩).1 h

  set one' : ↥Λ := ⟨1, hO.one_mem⟩ with hone'
  have hone_act : ∀ P : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) E.f,
      pushPt (E.act one') (E.act_over one') P = P := by
    intro P
    apply Subtype.ext
    rw [mapPt_coe, hone', E.act_one hO.one_mem, Category.comp_id]
  have hnsmul : ∀ (n : ℕ) (P : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) E.f),
      pushPt (E.act (n • one')) (E.act_over (n • one')) P = nsmulPt E.L (𝟙 (Spec (CommRingCat.of k))) n P := by
    intro n P
    induction n with
    | zero =>
      have h := E.act_add 0 0 (𝟙 (Spec (CommRingCat.of k))) P
      rw [add_zero] at h
      rw [zero_smul]
      change pushPt (E.act 0) (E.act_over 0) P = (1 : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) E.f)
      exact mul_eq_left.1 h.symm
    | succ n ih =>
      rw [succ_nsmul, E.act_add, ih, hone_act]
      rfl

  have hcond_iff : ∀ m : ↥Λ, (∃ n : ℤ, (m : ℍ[ℚ, a, b]) * star (m : ℍ[ℚ, a, b]) = (((r : ℤ) * n : ℚ) : ℍ[ℚ, a, b])) ↔
      InP (m : ℍ[ℚ, a, b]) := by
    intro m
    rw [mul_star_eq_coe_nrd]
    constructor
    · rintro ⟨n, hn⟩
      refine ⟨m.2, n, ?_⟩
      have := QuaternionAlgebra.coe_injective hn
      rw [this]; push_cast; ring
    · rintro ⟨-, n, hn⟩
      exact ⟨n, by rw [hn]; push_cast; ring_nf⟩

  have hJ2 : ∀ x ∈ Λ, (∀ m : ℍ[ℚ, a, b], InP m → m * x ∈ H) → InP x := by
    let J2 : Submodule ℤ ℍ[ℚ, a, b] :=
      { carrier := {x | x ∈ Λ ∧ ∀ m : ℍ[ℚ, a, b], InP m → m * x ∈ H}
        add_mem' := by
          rintro x x' ⟨hx, hxm⟩ ⟨hx', hx'm⟩
          exact ⟨Λ.add_mem hx hx', fun m hm => by rw [mul_add]; exact H.add_mem (hxm m hm) (hx'm m hm)⟩
        zero_mem' := ⟨Λ.zero_mem, fun m hm => by rw [mul_zero]; exact H.zero_mem⟩
        smul_mem' := by
          rintro c x ⟨hx, hxm⟩
          exact ⟨Λ.smul_mem c hx, fun m hm => by rw [mul_zsmul_comm']; exact hHzsmul c _ (hxm m hm)⟩ }
    have hJ2mem : ∀ x, x ∈ J2 ↔ x ∈ Λ ∧ ∀ m : ℍ[ℚ, a, b], InP m → m * x ∈ H := fun x => Iff.rfl
    have hJ2Λ : J2 ≤ Λ := fun x hx => ((hJ2mem x).1 hx).1
    have hJ2r : ∀ μ ∈ Λ, (r : ℤ) • μ ∈ J2 := fun μ hμ =>
      (hJ2mem _).2 ⟨Λ.smul_mem _ hμ, fun m hm => by rw [mul_zsmul_comm']; exact hHmem _ (hO.mul_mem hm.1 hμ)⟩
    have hJ2left : ∀ l ∈ Λ, ∀ x ∈ J2, l * x ∈ J2 := by
      intro l hl x hx
      obtain ⟨hxΛ, hxm⟩ := (hJ2mem x).1 hx
      refine (hJ2mem _).2 ⟨hO.mul_mem hl hxΛ, fun m hm => ?_⟩
      rw [← mul_assoc]
      exact hxm (m * l) (hright m hm l hl)
    have hJ2eq : ∀ x, x ∈ J2 → InP x := by
      rcases htri J2 hJ2Λ hJ2r hJ2left with h | h | h
      · intro x hx
        obtain ⟨μ, hμ, rfl⟩ := (h x).1 hx
        exact ⟨Λ.smul_mem _ hμ, hrP μ hμ⟩
      · intro x hx; exact (h x).1 hx
      · exfalso
        apply hynot
        have h1 : (1 : ℍ[ℚ, a, b]) ∈ J2 := by rw [h]; exact hO.one_mem
        obtain ⟨-, h1m⟩ := (hJ2mem _).1 h1
        have := h1m y ⟨hyΛ, ny, hny⟩
        rw [mul_one] at this
        exact hHmem' y this
    intro x hx hxm
    exact hJ2eq x ((hJ2mem x).2 ⟨hx, hxm⟩)

  have key : ∀ m : ↥Λ.toAddSubgroup, InP (m : ℍ[ℚ, a, b]) ↔
      ∀ (m' : ↥Λ) (n : ℤ), (m' : ℍ[ℚ, a, b]) * star (m' : ℍ[ℚ, a, b]) = (((r : ℤ) * n : ℚ) : ℍ[ℚ, a, b]) →
        pushPt (E.act m') (E.act_over m') (Φ ⟨m, m.2⟩) = E.L.one (𝟙 (Spec (CommRingCat.of k))) := by
    intro m
    constructor
    · intro hm m' n hn
      have hm' : InP (m' : ℍ[ℚ, a, b]) := (hcond_iff m').1 ⟨n, hn⟩
      rw [hΦact]
      change Φ _ = 1
      rw [hΦker]
      obtain ⟨z, hz, hmz⟩ := hsq _ hm'.1 _ hm.1 hm'.2 hm.2
      show (m' : ℍ[ℚ, a, b]) * (m : ℍ[ℚ, a, b]) ∈ H
      rw [hmz]
      exact hHmem z hz
    · intro hP
      refine hJ2 _ m.2 fun m' hm' => ?_
      obtain ⟨n, hn⟩ := (hcond_iff ⟨m', hm'.1⟩).2 hm'
      have := hP ⟨m', hm'.1⟩ n hn
      rw [hΦact] at this
      change Φ _ = 1 at this
      rw [hΦker] at this
      exact this
  let e : ↥ψ.range → {P : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) E.f //
      ∀ (m : ↥Λ) (n : ℤ), (m : ℍ[ℚ, a, b]) * star (m : ℍ[ℚ, a, b]) = (((r : ℤ) * n : ℚ) : ℍ[ℚ, a, b]) →
        pushPt (E.act m) (E.act_over m) P = E.L.one (𝟙 (Spec (CommRingCat.of k)))} :=
    fun g => ⟨Φbar g.1, by
      obtain ⟨c, hc⟩ := g
      induction c using QuotientAddGroup.induction_on with | H m => ?_
      rw [hΦbar]
      exact (key m).1 ((hrange m).1 hc)⟩
  have he : Function.Bijective e := by
    constructor
    · rintro ⟨c₁, hc₁⟩ ⟨c₂, hc₂⟩ h
      have : Φbar c₁ = Φbar c₂ := congrArg Subtype.val h
      exact Subtype.ext (hΦbar_inj this)
    · rintro ⟨P, hP⟩

      have hrtor : nsmulPt E.L (𝟙 (Spec (CommRingCat.of k))) r P = E.L.one (𝟙 (Spec (CommRingCat.of k))) := by
        rw [← hnsmul]
        refine hP (r • one') r ?_
        have hc : ((r • one' : ↥Λ) : ℍ[ℚ, a, b]) = ((r : ℚ) : ℍ[ℚ, a, b]) := by
          rw [Submodule.coe_smul_of_tower, hone', nsmul_eq_mul, mul_one, natCast_eq_coe']
        rw [hc, star_coe', ← QuaternionAlgebra.coe_mul]
        congr 1
        all_goals push_cast
        all_goals try ring
      obtain ⟨m₀, hm₀⟩ := hgen P hrtor
      have hInP : InP (m₀ : ℍ[ℚ, a, b]) := by
        refine (key ⟨m₀, m₀.2⟩).2 ?_
        intro m' n hn
        have := hP m' n hn
        rwa [hm₀] at this
      refine ⟨⟨QuotientAddGroup.mk ⟨m₀, m₀.2⟩, (hrange _).2 hInP⟩, ?_⟩
      apply Subtype.ext
      show Φbar (QuotientAddGroup.mk ⟨(m₀ : ℍ[ℚ, a, b]), m₀.2⟩) = P
      rw [hΦbar, hm₀]
  rw [← hrange_card]
  exact (Nat.card_congr (Equiv.ofBijective e he)).symm

end CntRam

end

open scoped Quaternion in
open CategoryTheory AlgebraicGeometry CerednikDrinfeld CerednikDrinfeld.QM QuaternionAlgebra NeronModelInfra GoodReductionJacobian in
theorem solution
    {a b : ℚ} {q q' : ℕ} [Fact q.Prime] [Fact q'.Prime] (hqq' : q' ≠ q) (hB : IsIndefiniteRamifiedExactlyAt a b q q')
    (Λ : Submodule ℤ ℍ[ℚ, a, b]) (hΛ : IsMaximalOrder Λ) {N : ℕ}
    (k : Type) [Field k] [IsAlgClosed k] (E : FakeEllipticCurve Λ N k)
    (r : ℕ) (hr : r = q ∨ r = q') (hrk : (r : k) ≠ 0) :
    Nat.card {P : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) E.f //
      ∀ (m : ↥Λ) (n : ℤ), (m : ℍ[ℚ, a, b]) * star (m : ℍ[ℚ, a, b]) = (((r : ℤ) * n : ℚ) : ℍ[ℚ, a, b]) →
        pushPt (E.act m) (E.act_over m) P = E.L.one (𝟙 (Spec (CommRingCat.of k)))} = r ^ 2 :=
  CntRam.main hqq' hB Λ hΛ k E r hr hrk

end S_CerednikDrinfeld_QM_FakeEllipticCurve_natCard_setOf_forall_pushPt_act_eq_one_of_eq_or_eq
end P2MW
export P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_natCard_setOf_forall_pushPt_act_eq_one_of_eq_or_eq (solution)
