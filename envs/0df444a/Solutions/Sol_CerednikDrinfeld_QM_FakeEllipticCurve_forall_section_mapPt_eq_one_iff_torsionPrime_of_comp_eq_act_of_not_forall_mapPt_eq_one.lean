-- Prove2me | solution 1 for CerednikDrinfeld.QM.FakeEllipticCurve.forall_section_mapPt_eq_one_iff_torsionPrime_of_comp_eq_act_of_not_forall_mapPt_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.141142+00:00
-- url     : https://prove2.me/submissions/ec4b6e3f-63db-5552-87cc-069ca7c80d0e

import Mathlib
import Definitions.Def_CerednikDrinfeld_QMModuli
import Definitions.Def_CerednikDrinfeld_QMFineModuli
import Definitions.Def_QuaternionAlgebra_EichlerOrder
import Definitions.Def_QuaternionAlgebra_ReducedNorm
import Definitions.Def_CerednikDrinfeld_ShimuraCurve
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawKernel
import Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_nonempty_fullLevel_of_isMaximalOrder
import Theorems.Thm_QuaternionAlgebra_IsMaximalOrder_leftIdeal_eq_or_eq_or_eq_of_isIndefiniteRamifiedExactlyAt_of_eq_or_eq
import Theorems.Thm_QuaternionAlgebra_IsMaximalOrder_exists_generator_ramifiedPrime_of_isIndefiniteRamifiedExactlyAt
import Theorems.Thm_QuaternionAlgebra_IsOrder_exists_intCast_eq_nrd_and_exists_intCast_eq_trd
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_forall_section_mapPt_eq_one_iff_torsionPrime_of_comp_eq_act_of_not_forall_mapPt_eq_one
p2m_attr_erase "instance" "GoodReductionJacobian.RelativeGroupLaw.isIso_endKerStr_schemeHomOverId AlgebraicGeometry.Scheme.PresheafOfModules.symmetricCategory SheafOfModules.instFaithfulRingSheafPModToPMod SheafOfModules.symmetricCategory AlgebraicGeometry.Scheme.PresheafOfModules.monoidalCategory AlgebraicGeometry.Scheme.PresheafOfModules.monoidalClosed SheafOfModules.instFullRingSheafPModToPMod SheafOfModules.monoidalCategory AlgebraicGeometry.Scheme.Modules.symmetricCategory SheafOfModules.monoidalClosed SheafOfModules.instIsLocalizationPModRingSheafSheafifyFunctorPresheafW SheafOfModules.sheafifyFunctor_monoidal AlgebraicGeometry.Scheme.Modules.monoidalClosed AlgebraicGeometry.instMonoidalPresheafOfModulesModulesSheafify AlgebraicGeometry.Scheme.Modules.monoidalCategory PresheafOfModules.instMonoidalClosed PresheafOfModules.InternalHom.instModuleCarrierObjOppositeCommRingCatSubtypePiFamilyMemAddSubgroupNaturalFamilies PresheafOfModules.InternalHom.instModuleCarrierObjOppositeRingCatCompCommRingCatForget₂RingHomCarrierCarrierAbPresheaf PresheafOfModules.InternalHom.instSMulCarrierObjOppositeCommRingCatSubtypePiFamilyMemAddSubgroupNaturalFamilies AlgebraicGeometry.Scheme.Hom.opensMapFinal AlgebraicGeometry.RelPicard.RigidifiedLineBundle.setoid AlgebraicGeometry.RelPicard.RigidifiedLineBundle.instInhabited AlgebraicGeometry.OModulePresheaf.isScalarTower AlgebraicGeometry.Scheme.OrderedAffineCover.instLinearOrder AlgebraicGeometry.OModulePresheaf.module AlgebraicGeometry.Scheme.OrderedAffineCover.instFintype AlgebraicGeometry.Scheme.OrderedAffineCover.instFintypeIdx AlgebraicGeometry.OModulePresheaf.addCommGroup AlgebraicGeometry.Scheme.OrderedAffineCover.instDecidableEqIdx AlgebraicGeometry.OModulePresheaf.moduleSections TwoChartCech.Sections.M0_moduleA TwoChartCech.Sections.M1_module TwoChartCech.Cover.A01_algebra TwoChartCech.Cover.A0_algebra TwoChartCech.Cover.A1_commRing TwoChartCech.Cover.A1_algebra TwoChartCech.Sections.M01_module TwoChartCech.Sections.M0_addCommGroup TwoChartCech.Sections.M0_tower TwoChartCech.Sections.M01_addCommGroup"
p2m_attr_erase "instance" "TwoChartCech.Cover.A0_commRing TwoChartCech.Sections.M1_tower TwoChartCech.Sections.M01_moduleA TwoChartCech.Sections.M0_module TwoChartCech.Sections.M1_moduleA TwoChartCech.Sections.M1_addCommGroup TwoChartCech.Cover.A01_commRing TwoChartCech.Sections.M01_tower CoherentBaseChange.TwoTermComplex.C0_module CoherentBaseChange.TwoTermComplex.C0_addCommGroup CoherentBaseChange.TwoTermComplex.C1_module CoherentBaseChange.TwoTermComplex.C1_addCommGroup CoherentBaseChange.TwoTermComplex.C0_free CoherentBaseChange.TwoTermComplex.C1_finite CoherentBaseChange.TwoTermComplex.C0_finite CoherentBaseChange.TwoTermComplex.C1_free AlgebraicGeometry.OModulePresheaf.instSubsingletonObjZero AlgebraicGeometry.Scheme.Modules.preservesBinaryProducts_opensMap AlgebraicGeometry.Scheme.Modules.pullback_monoidal AlgebraicGeometry.Scheme.Modules.sheafify_isLocalization' AlgebraicGeometry.Scheme.Modules.preservesTerminal_opensMap AlgebraicGeometry.Scheme.Modules.pullback₀_monoidal AlgebraicGeometry.Scheme.Modules.preservesFiniteProducts_opensMap AlgebraicGeometry.Scheme.Modules.instLiftingPresheafOfModulesSheafifyPresheafWOpensCarrierCarrierCommRingCatGrothendieckTopologyObjFunctorOppositeIsSheafSheafCompPullback₀Pullback PresheafOfModules.PullbackMonoidal.pullback_monoidal PresheafOfModules.PullbackMonoidal.isIso_δ PresheafOfModules.pushforward_laxMonoidal PresheafOfModules.PullbackMonoidal.isIso_η PresheafOfModules.free_monoidal PresheafOfModules.restrictScalars_laxMonoidal PresheafOfModules.PullbackMonoidal.isIso_δ_gS PresheafOfModules.pullback_oplaxMonoidal PresheafOfModules.PullbackMonoidal.instPreservesColimitsOfSizeCompOppositeCommRingCatRingCatForget₂RingHomCarrierCarrierPb PresheafOfModules.pullback_monoidal' AlgebraicGeometry.SmoothOfRelativeDimension.fiberToSpecResidueField AlgebraicGeometry.SmoothOfRelativeDimension.pullback_snd AlgebraicGeometry.SmoothOfRelativeDimension.pullback_fst AlgebraicGeometry.SmoothOfRelativeDimension.smooth_one AlgebraicGeometry.SmoothProperCurve.isIntegral_pullback_Spec_field AlgebraicGeometry.IsProper.fiberToSpecResidueField"
p2m_attr_erase "instance" "AlgebraicCurve.CurveModel.isProper AlgebraicCurve.CurveModel.isIntegral AlgebraicCurve.CurveModel.smooth AlgebraicGeometry.Scheme.LocalRepresentabilityULift.instIsLocallyInjectiveFunUliftYonedaGluedToSheaf AlgebraicGeometry.Scheme.LocalRepresentabilityULift.instIsLocallySurjectiveFunUliftYonedaGluedToSheafOfIsLocallySurjectiveZariskiTopologyDescFunctorOppositeType AlgebraicGeometry.Scheme.LocalRepresentabilityULift.instIsOpenImmersionToGlued AlgebraicGeometry.Scheme.LocalRepresentabilityULift.instIsIsoSheafZariskiTopologyTypeUliftYonedaGluedToSheaf AlgebraicGeometry.RelPicard.instIsOpenImmersionToGlued AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.instFundamentalIdentityOfSumRamificationInertia AlgebraicCurve.Place.instIsScalarTowerResidueFieldRestrictPushforward AlgebraicCurve.Place.instAlgebraResidueFieldRestrictPushforward AlgebraicCurve.Place.instIsLocalHomRestrictInclusion AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions PresheafOfModules.ExteriorPower.instModulePresheafAb AlgebraicGeometry.RelEffCartierDiv.subsingleton_of_degree_zero AlgebraicGeometry.RelEffCartierDiv.isIso_subschemeIota_snd_of_degree_one AlgebraicGeometry.isIso_ker_graphOver_subschemeIota_snd AlgebraicGeometry.isClosedImmersion_graphOver AlgebraicGeometry.FGSubalgebra.instIsDirectedLe AlgebraicGeometry.FGSubalgebra.instQuasiSeparatedSpaceCarrierCarrierCommRingCatObjOppositeSchemeSpecDiagram AlgebraicGeometry.FGSubalgebra.instIsCofilteredOpposite AlgebraicGeometry.FGSubalgebra.instIsAffineObjOppositeSchemeSpecDiagram AlgebraicGeometry.FGSubalgebra.instNonempty AlgebraicGeometry.FGSubalgebra.instNonemptySubtypeLeSubalgebraValFG AlgebraicGeometry.FGSubalgebra.instCompactSpaceCarrierCarrierCommRingCatObjOppositeSchemeSpecDiagram AlgebraicGeometry.FGSubalgebra.instIsDirectedSubtypeLeSubalgebraValFG AlgebraicGeometry.FGSubalgebra.instIsAffineHomMapOppositeSchemeSpecDiagram AlgebraicGeometry.FGSubalgebra.instIsFiltered AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instNeg AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instSMulInt AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instAddCommGroup AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instAdd AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instSub"
p2m_attr_erase "instance" "AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instModuleCarrierObjOppositeOpensCarrierCarrierCommRingCatPresheafOpOpensTop AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instSMulCarrierObjOppositeOpensCarrierCarrierCommRingCatPresheafOpOpensTop AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instSMulNat AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instZero AlgebraicCurve.instHasLocalResidue_of_hasCanonicalLocalResidueK AlgebraicCurve.instHasCanonicalLocalResidueK_of_hasCanonicalLocalResidueKStar AlgebraicCurve.Place.kw_ffgc_finiteDimensional_adicCompletion instAlgebraSubtypeMemValuationSubring_definitions AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersIntegersCompletion ModularCurve.KwF4gRRTate.instAlgebraKAdicCompletionIntegers AlgebraicCurve.Place.kw_ffgc_continuousSMul_adicCompletionComap AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersCompletionCompletion IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions AlgebraicCurve.instHasCanonicalLocalResidueK AlgebraicCurve.Place.instAlgebra_restrictResidueField AlgebraicCurve.Place.instIsScalarTower_restrictResidueField AlgebraicCurve.instHasLocalResidue AlgebraicCurve.HasSeparableResidue.of_perfectField_of_isCurveOver AlgebraicCurve.HasSeparableResidue.of_perfectField AlgebraicCurve.Place.instIsLocalHom_restrictSubringHom AlgebraicCurve.instHasCanonicalLocalResidueKStar ModularCurve.KwNo6Pin.isLocalRing_completion SheafOfModules.isIso_ihomModelToIhom AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instDecidableEqIdx AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instFintype AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instLinearOrder AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instFintypeIdx AlgebraicGeometry.OModulePresheaf.Leray.relAltC_scalarTower AlgebraicGeometry.OModulePresheaf.Leray.ker_relAltd_modΓ AlgebraicGeometry.OModulePresheaf.Leray.relAltC_modΓ AlgebraicGeometry.OModulePresheaf.Leray.biC_abGrp AlgebraicGeometry.OModulePresheaf.Leray.relAltH_modΓ AlgebraicGeometry.OModulePresheaf.Leray.ker_relAltd_smul AlgebraicGeometry.OModulePresheaf.Leray.relAltH_scalarTower AlgebraicGeometry.OModulePresheaf.Leray.relAltH_smul"
p2m_attr_erase "instance" "AlgebraicGeometry.OModulePresheaf.Leray.biC_module DoubleComplex.instModuleE₂I DoubleComplex.Bounded.modR DoubleComplex.instModuleE₂II DoubleComplex.instAddCommGroupE₂II DoubleComplex.Bounded.abGrp DoubleComplex.instAddCommGroupE₂I AlgebraicGeometry.ChowDatum.hι_closed AlgebraicGeometry.ChowDatumProj.hιN_closed AlgebraicGeometry.ChowDatumProj.hp_proper AlgebraicGeometry.ChowDatum.hp_isoU AlgebraicGeometry.ChowDatum.hp_proper AlgebraicGeometry.ProjSpace.algebraAway AlgebraicGeometry.ProjSpace.instIsProperProdOverπ AlgebraicGeometry.ChowDatumProj.hp_isoU AlgebraicGeometry.ProjSpace.isProper_π AlgebraicGeometry.ProjSpace.finiteType_mvPolynomial ProjSpaceCech.GradedModule.H.module ProjSpaceCech.GradedModule.H.addCommGroup ProjSpaceCech.GradedModule.sec.instAdd ProjSpaceCech.GradedModule.sec.instNeg ProjSpaceCech.GradedModule.acg ProjSpaceCech.GradedModule.Frac.setoid ProjSpaceCech.GradedModule.modR ProjSpaceCech.GradedModule.sec.instModule ProjSpaceCech.GradedModule.sec.instAddCommGroup ProjSpaceCech.GradedModule.sec.instZero ProjSpaceCech.GradedModule.Presentation.fJ ProjSpaceCech.GradedModule.sec.instSMul ProjSpaceCech.Twist.H.module ProjSpaceCech.Idx.instFintype ProjSpaceCech.Twist.H.addCommGroup ProjSpaceCech.Idx.instDecidableEq ProjSpaceCech.Twist.Mon.instDecidableEq ProjSpaceCech.Twist.cochain.instAddCommGroup ProjSpaceCech.Twist.cochain.instModule AlgebraicGeometry.FGSubalgebra.tensorStage_directedSystem AlgebraicGeometry.RelEffCartierDiv.isClosedImmersion_subschemeι_resProdMap AlgebraicGeometry.RelEffCartierDiv.isOpenImmersion_resProdMap AlgebraicCurve.CurveModel.locallyOfFiniteType_gluedToBase"
p2m_attr_erase "instance" "AlgebraicCurve.CurveModel.isFractionRing_overlap AlgebraicCurve.CurveModel.isLocallyNoetherian_glued AlgebraicCurve.CurveModel.jacobsonSpace_glued AlgebraicCurve.CurveModel.isOpenImmersion_ι₀ AlgebraicCurve.CurveModel.isIntegral_glued AlgebraicCurve.CurveModel.quasiSeparated_gluedToBase AlgebraicCurve.CurveModel.compactSpace_glued AlgebraicCurve.CurveModel.isIntegral_adjoin_chartRing AlgebraicCurve.CurveModel.isFractionRing_overlap_functionField AlgebraicCurve.CurveModel.isProper_gluedToBase AlgebraicCurve.CurveModel.isOpenImmersion_ιU AlgebraicCurve.CurveModel.isOpenImmersion_f₀ AlgebraicCurve.CurveModel.isOpenImmersion_fInf AlgebraicCurve.CurveModel.isOpenImmersion_ιInf AlgebraicCurve.CurveModel.algebra_overlap_functionField AlgebraicCurve.CurveModel.quasiCompact_gluedToBase AlgebraicCurve.CurveModel.algebraAdjoin AlgebraicCurve.CurveModel.isDedekindDomain_chartRing AlgebraicCurve.CurveModel.isIntegralClosure AlgebraicCurve.CurveModel.finite_chartRing AlgebraicCurve.CurveModel.centre_isPrime AlgebraicCurve.CurveModel.isFractionRing_chartRing AlgebraicCurve.CurveModel.finiteType_chartRing AlgebraicCurve.CurveModel.isNoetherianRing_chartRing AlgebraicCurve.CurveModel.isScalarTower_base_adjoin AlgebraicCurve.CurveModel.isScalarTower_adjoin AlgebraicCurve.CurveModel.chartRing_finitePresentation instTopologicallyFGOfFiniteType AlgebraicGeometry.ProjSpace.twistObj.addCommGroup AlgebraicGeometry.ProjSpace.twistFam.module AlgebraicGeometry.ProjSpace.twistObj.module AlgebraicGeometry.ProjSpace.twistObj.moduleSections AlgebraicGeometry.ProjSpace.twistFam.addCommGroup CerednikDrinfeld.CosetGraph.projGraphAction CerednikDrinfeld.CosetGraph.projVertMulAction CerednikDrinfeld.CosetGraph.awayVertMulAction CerednikDrinfeld.CosetGraph.actionKer_normal CerednikDrinfeld.CosetGraph.vertMulAction CerednikDrinfeld.Mumford.dartAction"
p2m_attr_erase "simp" "NeronModelInfra.NeronModelPropertyBundle.endExtensionEquiv_symm_restrict NeronModelInfra.schemeHomOverComp_id_left NeronModelInfra.schemeHomOverComp_id_right NeronModelInfra.schemeHomOverId_coe NeronModelInfra.NeronModelPropertyBundle.endExtensionEquiv_apply NeronModelInfra.NeronModelPropertyBundle.restrict_endExtensionEquiv_symm NeronModelInfra.schemeHomOverComp_coe NeronModelInfra.schemeHomOverNpow_succ NeronModelInfra.schemeHomOverNpow_zero GoodReductionJacobian.relativeGroupLawOfGrpObj_inv GoodReductionJacobian.relativeGroupLawOfGrpObj_mul GoodReductionJacobian.overHomEquivSchemeHomOver_apply_coe GoodReductionJacobian.relativeGroupLawOfGrpObj_one GoodReductionJacobian.overHomEquivSchemeHomOver_symm_apply_left SheafOfModules.tensorUnit_eq AlgebraicGeometry.Scheme.Modules.tensorUnit_eq PresheafOfModules.InternalHom.presheaf_map_apply PresheafOfModules.InternalHom.curryFamily_app PresheafOfModules.InternalHom.add_app PresheafOfModules.InternalHom.smul_app PresheafOfModules.InternalHom.zero_app PresheafOfModules.ihomObj_map_val PresheafOfModules.ihomFunctor_map PresheafOfModules.InternalHom.restrict_app PresheafOfModules.InternalHom.postcomp_app PresheafOfModules.InternalHom.neg_app PresheafOfModules.curry'_app_val PresheafOfModules.InternalHom.presheaf_obj PresheafOfModules.ihomFunctor_obj PresheafOfModules.ihomObj_obj PresheafOfModules.InternalHom.sub_app PresheafOfModules.ihomMap_app_val AlgebraicGeometry.Scheme.Modules.tensorPow_zero AlgebraicGeometry.Scheme.Modules.tensorPow_succ AlgebraicGeometry.RelPicard.RigidifiedLineBundle.mk.sizeOf_spec AlgebraicGeometry.RelPicard.RigidifiedLineBundle.mk.injEq AlgebraicGeometry.Scheme.OrderedAffineCover.mk.injEq AlgebraicGeometry.OModulePresheaf.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCover.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.mk.injEq"
p2m_attr_erase "simp" "AlgebraicGeometry.Scheme.TwoAffineOpenCover.mk.injEq AlgebraicGeometry.Scheme.TwoAffineOpenCover.mk.sizeOf_spec AlgebraicGeometry.Scheme.TwoAffineOpenCover.pullback_U1 AlgebraicGeometry.Scheme.TwoAffineOpenCover.pullback_U0 TwoChartCech.Sections.mk.injEq TwoChartCech.Cover.mk.injEq TwoChartCech.GrothendieckComplex.mk.injEq TwoChartCech.Sections.mk.sizeOf_spec TwoChartCech.Cover.mk.sizeOf_spec TwoChartCech.Cover.lineBundle_r0_apply TwoChartCech.GrothendieckComplex.mk.sizeOf_spec TwoChartCech.Cover.lineBundle_r1_apply CoherentBaseChange.TwoTermComplex.mk.sizeOf_spec CoherentBaseChange.TwoTermComplex.mk.injEq AlgebraicGeometry.OModulePresheaf.prod_obj AlgebraicGeometry.OModulePresheaf.restrOpen_obj AlgebraicGeometry.OModulePresheaf.DevissageStep.mk.injEq AlgebraicGeometry.OModulePresheaf.pushforward_obj AlgebraicGeometry.OModulePresheaf.im_obj AlgebraicGeometry.OModulePresheaf.pow_obj AlgebraicGeometry.OModulePresheaf.fstHom_app AlgebraicGeometry.OModulePresheaf.ker_obj AlgebraicGeometry.OModulePresheaf.coker_obj AlgebraicGeometry.OModulePresheaf.DevissageStep.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCover.preimage_U AlgebraicGeometry.OModulePresheaf.sndHom_app AlgebraicGeometry.OModulePresheaf.Hom.mk.injEq AlgebraicGeometry.OModulePresheaf.Hom.id_app AlgebraicGeometry.OModulePresheaf.AffHom.appSections_apply AlgebraicGeometry.OModulePresheaf.AffHom.comp_app AlgebraicGeometry.OModulePresheaf.AffSES.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.AffHom.kerMap_coe AlgebraicGeometry.OModulePresheaf.AffHom.id_app AlgebraicGeometry.OModulePresheaf.Hom.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.Hom.toAffHom_app AlgebraicGeometry.OModulePresheaf.SES.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.AffHom.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.Hom.comp_app AlgebraicGeometry.OModulePresheaf.SES.mk.injEq AlgebraicGeometry.OModulePresheaf.AffHom.mk.injEq"
p2m_attr_erase "simp" "AlgebraicGeometry.OModulePresheaf.Hom.appSections_apply AlgebraicGeometry.OModulePresheaf.AffSES.mk.injEq PresheafOfModules.freeεIso_hom_app PresheafOfModules.freeμIso_hom_app AlgebraicGeometry.RelPicard.RepresentsRelSubPic.mk.injEq AlgebraicGeometry.RelPicard.SubPicCondition.mk.injEq AlgebraicGeometry.RelPicard.SubPicCondition.mk.sizeOf_spec AlgebraicGeometry.RelPicard.RepresentsRelSubPic.mk.sizeOf_spec AlgebraicGeometry.SmoothProperCurve.sectionBaseChange_coe_snd AlgebraicGeometry.SmoothProperCurve.sectionBaseChange_coe_fst AlgebraicCurve.CurveModel.mk.injEq AlgebraicCurve.CurveModel.mk.sizeOf_spec AlgebraicCurve.mulAdele_apply AlgebraicCurve.residuePairing_apply_coe AlgebraicCurve.mem_adeleBdd AlgebraicCurve.weilSmul_one AlgebraicCurve.diagonalHom_apply AlgebraicCurve.weilSmul_apply AlgebraicCurve.adeleSpaceMul_coe AlgebraicCurve.mulAdele_one AlgebraicGeometry.SmoothProperCurve.FiniteMapData.twoAffineOpenCover_U1 AlgebraicGeometry.SmoothProperCurve.FiniteMapData.mk.injEq AlgebraicGeometry.SmoothProperCurve.FiniteMapData.mk.sizeOf_spec AlgebraicGeometry.SmoothProperCurve.FiniteMapData.twoAffineOpenCover_U0 AlgebraicGeometry.RelPicard.SubPicCondition.onClasses_mk AlgebraicGeometry.RelPicard.relSubPicPresheaf_map_coe CategoryTheory.Functor.OverTotal.ofFibre_fst CategoryTheory.Functor.overTotal_map_fst AlgebraicGeometry.Scheme.LocalRepresentabilityULift.glueData_J AlgebraicGeometry.Scheme.LocalRepresentabilityULift.uliftYoneda_toGlued_uliftYonedaGluedToSheaf AlgebraicGeometry.Scheme.LocalRepresentabilityULift.glueData_t' AlgebraicGeometry.Scheme.LocalRepresentabilityULift.uliftYoneda_toGlued_uliftYonedaGluedToSheaf_assoc AlgebraicGeometry.Scheme.LocalRepresentabilityULift.uliftYonedaGluedToSheaf_app_toGlued AlgebraicGeometry.Scheme.LocalRepresentabilityULift.glueData_openCover_map AlgebraicGeometry.Scheme.LocalRepresentabilityULift.uliftYonedaGluedToSheaf_app_comp AlgebraicGeometry.Scheme.LocalRepresentabilityULift.glueData_V AlgebraicGeometry.Scheme.LocalRepresentabilityULift.glueData_t AlgebraicGeometry.Scheme.LocalRepresentabilityULift.glueData_U AlgebraicGeometry.Scheme.LocalRepresentabilityULift.glueData_f AlgebraicGeometry.RelPicard.designationOfRepresentableBy_P"
p2m_attr_erase "simp" "AlgebraicGeometry.RelPicard.designationOfRepresentableBy_toBase AlgebraicGeometry.RelPicard.rigSection_snd AlgebraicGeometry.RelPicard.RigidifiedLineBundle.ofInvertible_L AlgebraicGeometry.RelPicard.rigSection_snd_assoc AlgebraicGeometry.RelPicard.SubPicGroupCondition.mk.injEq AlgebraicGeometry.RelPicard.SubPicGroupCondition.mk.sizeOf_spec AlgebraicCurve.coe_cechH0Equiv_apply AlgebraicCurve.cechH1ToH1_mk AlgebraicCurve.lSpaceOn_univ AlgebraicCurve.lSpaceOn_empty AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.Divisor.mapRestrict_single AlgebraicCurve.Divisor.pushforward_single AlgebraicCurve.Place.coe_restrictInclusion AlgebraicCurve.Place.mem_fiber AlgebraicCurve.Place.restrict_toValuationSubring AlgebraicCurve.Divisor.degree_pushforward AlgebraicCurve.Place.restrictResidueMap_residue AlgebraicCurve.Pic0.coe_pushforwardDegZeroHom AlgebraicCurve.Pic0.coe_pullbackDegZeroHom AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk"
p2m_attr_erase "simp" "ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Divisor.degree_pushforwardAlong AlgebraicCurve.Pic0.coe_degZeroCorrespondence AlgebraicCurve.Place.mem_fiberAlong AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.jqNModC_one ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one AlgebraicCurve.Place.differentialCoeff_zero AlgebraicCurve.Place.differentialCoeff_dCoord AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.injEq AlgebraicCurve.TranscendenceTower.mk.injEq AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec AlgebraicCurve.PoleDivisorPackage.mk.injEq AlgebraicGeometry.RelPicard.thetaBundle_def AlgebraicGeometry.RelPicard.picardBundle_def AlgebraicGeometry.RelEffCartierDiv.toRelEffDivisor_ofRelEffDivisor AlgebraicGeometry.RelEffCartierDiv.toRelEffDivisor_I AlgebraicGeometry.mapOnProdOver_fst_assoc AlgebraicGeometry.RelEffCartierDiv.mk.sizeOf_spec AlgebraicGeometry.RelEffCartierDiv.mk.injEq"
p2m_attr_erase "simp" "AlgebraicGeometry.mapOnProdOver_snd AlgebraicGeometry.mapOnProdOver_fst AlgebraicGeometry.mapOnProdOver_snd_assoc AlgebraicGeometry.mapOnProdOver_id AlgebraicCurve.RelEffDivisor.mk.sizeOf_spec AlgebraicCurve.mapOnProd_fst AlgebraicCurve.mapOnProd_fst_assoc AlgebraicCurve.mapOnProd_snd AlgebraicCurve.UnivDivisorPack.mk.injEq AlgebraicCurve.RelEffDivisor.mk.injEq AlgebraicCurve.UnivDivisorPack.mk.sizeOf_spec AlgebraicCurve.mapOnProd_snd_assoc AlgebraicGeometry.Scheme.Modules.exteriorPower_obj PresheafOfModules.exteriorPower_map_ιMulti PresheafOfModules.ExteriorPower.appₗ_apply AlgebraicGeometry.prodKerGraph_one AlgebraicGeometry.fibrePowOver.proj_comp AlgebraicGeometry.prodKerGraph_zero AlgebraicGeometry.RelEffCartierDiv.empty_I AlgebraicGeometry.fibrePowOver.proj_comp_assoc AlgebraicGeometry.graphOver_fst_assoc AlgebraicGeometry.RelEffCartierDiv.toPoint_comp AlgebraicGeometry.RelEffCartierDiv.toPoint_comp_assoc AlgebraicGeometry.graphOver_fst AlgebraicGeometry.RelEffCartierDiv.ofPoint_I AlgebraicGeometry.graphOver_snd AlgebraicGeometry.graphOver_snd_assoc AlgebraicCurve.SymmetricPowerPackage.mk.sizeOf_spec AlgebraicCurve.SymmetricPowerPackage.mk.injEq AlgebraicGeometry.FGSubalgebra.cocone_ι_app_apply AlgebraicGeometry.RelPicard.fst_toProdSpec AlgebraicGeometry.RelPicard.toProdSpec_fst_assoc AlgebraicGeometry.RelPicard.pointsSubBasepointModule_cons AlgebraicGeometry.RelPicard.pointsSubBasepointModule_nil AlgebraicGeometry.RelPicard.fst_toProdSpec_assoc AlgebraicGeometry.RelPicard.toProdSpec_fst AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.sub_app AlgebraicGeometry.Scheme.IdealSheafData.sres_sresTop AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.add_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.mk.sizeOf_spec"
p2m_attr_erase "simp" "AlgebraicGeometry.Scheme.IdealSheafData.coe_resLE AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.smul_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.coe_ofLE_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.ideal_range AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.zero_app AlgebraicGeometry.Scheme.IdealSheafData.sres_sres AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.comp_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.neg_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.id_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.coe_mulRight_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.nsmul_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.mk.injEq AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.zsmul_app AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.sizeOf_spec AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.injEq AlgebraicCurve.adeleSingle_coe AlgebraicCurve.kaehlerResidueTermKFam_apply AlgebraicCurve.Place.LocalResidueData.mk.injEq AlgebraicCurve.Place.LocalResidueData.mk.sizeOf_spec AlgebraicCurve.Place.kw_ffgc_adicCompletionComapIntegers_coe AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.sizeOf_spec AlgebraicCurve.Place.mem_simplePoleSubmodule AlgebraicCurve.Place.coe_uniformizerSubring ModularCurve.Lg37.Lg37CompletionSection.mk.injEq AlgebraicCurve.Place.CoefficientFieldSection.mk.injEq AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.injEq ModularCurve.Lg37.Lg37CompletionSection.mk.sizeOf_spec AlgebraicCurve.Place.CoefficientFieldSection.mk.sizeOf_spec AlgebraicCurve.Place.poleSubmodule_one AlgebraicCurve.Place.mem_poleSubmodule AlgebraicGeometry.Scheme.Modules.toUnitSection_ofUnitSection AlgebraicGeometry.Scheme.Modules.pullbackSection_def AlgebraicGeometry.Scheme.Modules.ofUnitSection_toUnitSection PresheafOfModules.InternalHom.IsSheafAux.appAt_toPresheafHom SheafOfModules.ihomSectionsEquivFamily_unit AlgebraicGeometry.Scheme.Modules.restrictHomEquivFamily_apply SheafOfModules.ihomEval_unit_app AlgebraicGeometry.Scheme.Modules.ihomEval_zero_right AlgebraicGeometry.Scheme.Modules.ihomEval_zero_left AlgebraicGeometry.Scheme.Modules.homOfFamily_app_apply"
p2m_attr_erase "simp" "SheafOfModules.unit_ihomSectionsEquivFamily AlgebraicGeometry.Scheme.Modules.familyOfHom_app AlgebraicGeometry.Scheme.Modules.restrictUnitIso_hom_app_apply AlgebraicGeometry.Scheme.Modules.restrictUnitIso_inv_app_apply AlgebraicGeometry.Scheme.Modules.restrictHomOfFamily_app_apply AlgebraicGeometry.Scheme.Modules.restrictHomEquivFamily_symm_apply AlgebraicGeometry.Scheme.Modules.tensorSections_zero_right AlgebraicGeometry.Scheme.Modules.map_unitSection AlgebraicGeometry.Scheme.Modules.tensorSectionsBilin_apply AlgebraicGeometry.Scheme.Modules.tensorPowSection_zero AlgebraicGeometry.Scheme.Modules.tensorSections_zero_left AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_neg AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_zero AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_sub AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_add AlgebraicGeometry.Scheme.OrderedAffineCover.toCoverOf_U AlgebraicGeometry.Scheme.OrderedAffineCoverOf.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCoverOf.mk.injEq AlgebraicGeometry.Scheme.OrderedAffineCover.restrict_U AlgebraicGeometry.OModulePresheaf.Leray.restrictToPreimage_U DoubleComplex.Bounded.mk.injEq DoubleComplex.Bounded.mk.sizeOf_spec DoubleComplex.Convergence.mk.injEq DoubleComplex.Convergence.mk.sizeOf_spec DoubleComplex.SubQuot.mk.sizeOf_spec DoubleComplex.SubQuot.mk.injEq AlgebraicGeometry.ChowDatumProj.mk.sizeOf_spec AlgebraicGeometry.ChowDatum.mk.sizeOf_spec AlgebraicGeometry.ChowDatumProj.mk.injEq AlgebraicGeometry.ChowDatum.mk.injEq ProjSpaceCech.GradedModule.mk.injEq ProjSpaceCech.GradedModule.mk.sizeOf_spec ProjSpaceCech.GradedModule.Frac.mk.sizeOf_spec ProjSpaceCech.GradedModule.Presentation.mk.injEq ProjSpaceCech.GradedModule.Frac.mk.injEq ProjSpaceCech.GradedModule.Presentation.mk.sizeOf_spec ProjSpaceCech.GradedModule.Hom.shift_toLinearMap ProjSpaceCech.GradedModule.Hom.mk.sizeOf_spec ProjSpaceCech.GradedModule.Hom.mk.injEq TwoChartCech.Mumford.dK_apply"
p2m_attr_erase "simp" "TwoChartCech.Mumford.ι0_apply TwoChartCech.Mumford.ι1_apply TwoChartCech.KerCoprod.dK_apply TwoChartCech.KerCoprod.ι1_apply TwoChartCech.KerCoprod.ι0_apply AlgebraicGeometry.tilde.functorCompPullbackSpecIso_app AlgebraicGeometry.RelPicard.algEquivZeroGroupCut_toSubPicCondition AlgebraicGeometry.RelPicard.LFP.stageHom_val AlgebraicGeometry.RelPicard.BaseChange.relSubPicPresheafRestrictIso_hom_app_coe AlgebraicGeometry.RelPicard.BaseChange.relSubPicPresheafRestrictIso_inv_app_coe AlgebraicGeometry.RelPicard.BaseChange.restrict_P AlgebraicGeometry.RelEffCartierDiv.IsUniversal.lift_comp AlgebraicGeometry.RelEffCartierDiv.functor_map_fst AlgebraicGeometry.RelEffCartierDiv.IsUniversal.homEquiv_apply AlgebraicGeometry.RelEffCartierDiv.IsUniversal.lift_pullbackAlong AlgebraicGeometry.RelEffCartierDiv.IsUniversal.homEquiv_symm_apply AlgebraicGeometry.RelEffCartierDiv.IsUniversal.lift_comp_assoc AlgebraicGeometry.RelEffCartierDiv.supportedIn_top AlgebraicGeometry.RelEffCartierDiv.mem_supportedIn_iff AlgebraicGeometry.RelEffCartierDiv.supportedIn_top_eq AlgebraicGeometry.RelEffCartierDiv.restrictAlong_extendAlong AlgebraicGeometry.RelEffCartierDiv.extendAlong_I AlgebraicGeometry.RelEffCartierDiv.resProdMap_snd AlgebraicGeometry.RelEffCartierDiv.restrictAlong_I AlgebraicGeometry.RelEffCartierDiv.extendAlong_restrictAlong AlgebraicGeometry.RelEffCartierDiv.resProdMap_fst_assoc AlgebraicGeometry.RelEffCartierDiv.resProdMap_snd_assoc AlgebraicGeometry.RelEffCartierDiv.resProdMap_fst CoherentBaseChange.FibreH0Family.mk.sizeOf_spec CoherentBaseChange.FibreH0Family.mk.injEq AlgebraicGeometry.Scheme.Modules.ProjPresentation.mk.injEq AlgebraicGeometry.Scheme.Modules.ProjPresentation.mk.sizeOf_spec AlgebraicCurve.CurveModel.coe_gInf AlgebraicCurve.CurveModel.coe_tInvChart AlgebraicCurve.CurveModel.ιInf_gluedToBase_assoc AlgebraicCurve.CurveModel.ιInf_gluedToBase AlgebraicCurve.CurveModel.primeOfι₀_asIdeal AlgebraicCurve.CurveModel.coe_tChart AlgebraicCurve.CurveModel.ι₀_gluedToBase_assoc AlgebraicCurve.CurveModel.primeOfιInf_asIdeal"
p2m_attr_erase "simp" "AlgebraicCurve.CurveModel.ι₀_gluedToBase AlgebraicCurve.CurveModel.coe_tma AlgebraicCurve.CurveModel.coe_primeEquivChartPlaces RegularLocalRingQuotientAscent.dualNumberFst_apply AlgebraicGeometry.ProjSpace.twistObj.mk.injEq AlgebraicGeometry.ProjSpace.twistObj.zero_val AlgebraicGeometry.ProjSpace.twistObj.add_val AlgebraicGeometry.ProjSpace.twist_res_val AlgebraicGeometry.ProjSpace.twist_smul_val AlgebraicGeometry.ProjSpace.twistGradeToObj_val AlgebraicGeometry.ProjSpace.twistObj.smul_val AlgebraicGeometry.ProjSpace.twistGradeEquiv_apply_val AlgebraicGeometry.ProjSpace.twistObj.mk.sizeOf_spec QuaternionAlgebra.baseChangeRight_tmul QuaternionAlgebra.mapOfAlgebraMapEq_apply QuaternionAlgebra.baseChange_tmul QuaternionAlgebra.ClassSet.map_mk GoodReductionJacobian.RelativeGroupLaw.baseChangePointToBase_ofBase GoodReductionJacobian.RelativeGroupLaw.baseChangePointToBase_coe GoodReductionJacobian.RelativeGroupLaw.baseChangePointOfBase_coe GoodReductionJacobian.RelativeGroupLaw.baseChange_inv GoodReductionJacobian.RelativeGroupLaw.baseChangePointOfBase_toBase GoodReductionJacobian.RelativeGroupLaw.baseChange_mul GoodReductionJacobian.RelativeGroupLaw.baseChange_one NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_fst NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_snd NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_fst NeronSpecialFibreInfra.neronEndRestrictEquiv_apply NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_fst_assoc NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_snd NeronSpecialFibreInfra.neronEndExtension_genericFibreRestrict NeronSpecialFibreInfra.specClosedFibreInclusion_eq NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_fst_assoc NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_snd_assoc NeronSpecialFibreInfra.genericFibreRestrict_neronEndExtension NeronSpecialFibreInfra.homOverId_coe NeronSpecialFibreInfra.homOverComp_coe NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_snd_assoc GoodReductionJacobian.RelativeGroupLaw.fibre_inv GoodReductionJacobian.RelativeGroupLaw.fibrePointToBase_coe"
p2m_attr_erase "simp" "GoodReductionJacobian.RelativeGroupLaw.fibrePointOfBase_toBase GoodReductionJacobian.RelativeGroupLaw.fibre_mul GoodReductionJacobian.RelativeGroupLaw.fibrePointToBase_ofBase GoodReductionJacobian.RelativeGroupLaw.fibre_one GoodReductionJacobian.RelativeGroupLaw.fibrePointOfBase_coe AlgebraicGeometry.schemeFibreEndo_snd AlgebraicGeometry.schemeFibreEndo_fst"

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian QuaternionAlgebra
open CerednikDrinfeld CerednikDrinfeld.QM CerednikDrinfeld.QM.FakeEllipticCurve
open scoped Quaternion

namespace KerPartGeom

theorem nrd_mul' {a b : ℚ} (x y : ℍ[ℚ, a, b]) : nrd (x * y) = nrd x * nrd y := by
  have h : (((nrd (x * y) : ℚ)) : ℍ[ℚ, a, b]) = ((nrd x * nrd y : ℚ) : ℍ[ℚ, a, b]) := by
    rw [← mul_star_eq_coe_nrd, star_mul, coe_mul, ← mul_star_eq_coe_nrd x, ← mul_star_eq_coe_nrd y]
    calc x * y * (star y * star x) = x * (y * star y) * star x := by simp only [mul_assoc]
      _ = x * ((nrd y : ℚ) : ℍ[ℚ, a, b]) * star x := by rw [mul_star_eq_coe_nrd]
      _ = x * star x * ((nrd y : ℚ) : ℍ[ℚ, a, b]) := by rw [mul_assoc, coe_commutes (nrd y) (star x), ← mul_assoc]
      _ = x * star x * (y * star y) := by rw [mul_star_eq_coe_nrd y]
  exact_mod_cast QuaternionAlgebra.coe_injective h

section Pts

variable {S : Type} [CommRing S] {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} {N : ℕ} (E : FakeEllipticCurve Λ N S)

theorem nsmulPt_eq_nsmul {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of S)) (n : ℕ) (P : SchemeHomOver t E.f) :
    nsmulPt E.L t n P = E.L.nsmul t n P := by
  induction n with
  | zero => rfl
  | succ n ih => rw [RelativeGroupLaw.nsmul_succ, ← ih]; rfl

theorem hom_one (φ : E.A ⟶ E.A) (hφ : φ ≫ E.f = E.f)
    (hφ_hom : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of S)) (P Q : SchemeHomOver t E.f),
      mapPt φ hφ (E.L.mul t P Q) = E.L.mul t (mapPt φ hφ P) (mapPt φ hφ Q))
    {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of S)) : mapPt φ hφ (E.L.one t) = E.L.one t := by
  letI := E.L.pointGroup t
  have h := hφ_hom t (E.L.one t) (E.L.one t)
  rw [E.L.one_mul] at h
  have h' : (mapPt φ hφ (E.L.one t) : SchemeHomOver t E.f) = mapPt φ hφ (E.L.one t) * mapPt φ hφ (E.L.one t) := h
  exact mul_eq_left.mp h'.symm

theorem act_one_pt (x : ↥Λ) {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of S)) :
    pushPt (E.act x) (E.act_over x) (E.L.one t) = E.L.one t :=
  hom_one E (E.act x) (E.act_over x) (E.act_hom x) t

theorem act_mul_pt (x y : ℍ[ℚ, a, b]) (hx : x ∈ Λ) (hy : y ∈ Λ) (h : x * y ∈ Λ)
    {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of S)) (P : SchemeHomOver t E.f) :
    pushPt (E.act ⟨x * y, h⟩) (E.act_over _) P =
      pushPt (E.act ⟨x, hx⟩) (E.act_over _) (pushPt (E.act ⟨y, hy⟩) (E.act_over _) P) := by
  apply Subtype.ext
  simp only [pushPt, mapPt_coe, Category.assoc, E.act_mul ⟨x, hx⟩ ⟨y, hy⟩ h]

theorem pushPt_congr {m m' : ↥Λ} (h : m = m')
    {T : Scheme.{0}} {t : T ⟶ Spec (CommRingCat.of S)} (P : SchemeHomOver t E.f) :
    pushPt (E.act m) (E.act_over m) P = pushPt (E.act m') (E.act_over m') P := by
  subst h; rfl

theorem lin_pt (φ : E.A ⟶ E.A) (hφ : φ ≫ E.f = E.f) (hφ_lin : ∀ m : ↥Λ, E.act m ≫ φ = φ ≫ E.act m)
    (x : ↥Λ) {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of S)) (P : SchemeHomOver t E.f) :
    mapPt φ hφ (pushPt (E.act x) (E.act_over x) P) = pushPt (E.act x) (E.act_over x) (mapPt φ hφ P) := by
  apply Subtype.ext
  simp only [pushPt, mapPt_coe, Category.assoc, hφ_lin x]

theorem hom_nsmulPt (φ : E.A ⟶ E.A) (hφ : φ ≫ E.f = E.f)
    (hφ_hom : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of S)) (P Q : SchemeHomOver t E.f),
      mapPt φ hφ (E.L.mul t P Q) = E.L.mul t (mapPt φ hφ P) (mapPt φ hφ Q))
    {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of S)) (n : ℕ) (P : SchemeHomOver t E.f) :
    mapPt φ hφ (nsmulPt E.L t n P) = nsmulPt E.L t n (mapPt φ hφ P) := by
  induction n with
  | zero => exact hom_one E φ hφ hφ_hom t
  | succ n ih =>
    show mapPt φ hφ (E.L.mul t (nsmulPt E.L t n P) P) = E.L.mul t (nsmulPt E.L t n (mapPt φ hφ P)) (mapPt φ hφ P)
    rw [hφ_hom, ih]

theorem mapPt_comp' (φ : E.A ⟶ E.A) (hφ : φ ≫ E.f = E.f) (ψ : E.A ⟶ E.A) (hψ : ψ ≫ E.f = E.f)
    (hφψ : (φ ≫ ψ) ≫ E.f = E.f) {T : Scheme.{0}} {t : T ⟶ Spec (CommRingCat.of S)} (P : SchemeHomOver t E.f) :
    mapPt (φ ≫ ψ) hφψ P = mapPt ψ hψ (mapPt φ hφ P) :=
  Subtype.ext (by simp [mapPt_coe, Category.assoc])

theorem pushPt_act_zero (h0 : (0 : ℍ[ℚ, a, b]) ∈ Λ) {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of S)) (P : SchemeHomOver t E.f) :
    pushPt (E.act ⟨0, h0⟩) (E.act_over _) P = E.L.one t := by
  letI := E.L.pointGroup t
  have h := E.act_add ⟨0, h0⟩ ⟨0, h0⟩ t P
  have e : (⟨0, h0⟩ : ↥Λ) + ⟨0, h0⟩ = ⟨0, h0⟩ := by apply Subtype.ext; simp
  rw [e] at h
  have h' : (pushPt (E.act ⟨0, h0⟩) (E.act_over _) P : SchemeHomOver t E.f) =
      pushPt (E.act ⟨0, h0⟩) (E.act_over _) P * pushPt (E.act ⟨0, h0⟩) (E.act_over _) P := h
  exact mul_eq_left.mp h'.symm

theorem pushPt_act_natCast (hΛℤ : ∀ m : ℤ, ((m : ℚ) : ℍ[ℚ, a, b]) ∈ Λ) (m : ℕ)
    {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of S)) (P : SchemeHomOver t E.f) :
    pushPt (E.act ⟨((m : ℤ) : ℚ), hΛℤ m⟩) (E.act_over _) P = nsmulPt E.L t m P := by
  rw [nsmulPt_eq_nsmul]
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

def ann (hΛℤ : ∀ m : ℤ, ((m : ℚ) : ℍ[ℚ, a, b]) ∈ Λ)
    {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of S)) (R : SchemeHomOver t E.f) :
    Submodule ℤ ℍ[ℚ, a, b] where
  carrier := {x | ∃ hx : x ∈ Λ, pushPt (E.act ⟨x, hx⟩) (E.act_over _) R = E.L.one t}
  zero_mem' := ⟨Λ.zero_mem, pushPt_act_zero E Λ.zero_mem t R⟩
  add_mem' := by
    rintro x y ⟨hx, hxR⟩ ⟨hy, hyR⟩
    refine ⟨Λ.add_mem hx hy, ?_⟩
    have h := E.act_add ⟨x, hx⟩ ⟨y, hy⟩ t R
    rw [hxR, hyR, E.L.one_mul] at h
    exact h
  smul_mem' := by
    rintro c x ⟨hx, hxR⟩
    refine ⟨Λ.smul_mem c hx, ?_⟩
    have hcx : ((c : ℚ) : ℍ[ℚ, a, b]) * x ∈ Λ := by
      have : ((c : ℚ) : ℍ[ℚ, a, b]) * x = c • x := by rw [zsmul_eq_mul]; norm_cast
      rw [this]; exact Λ.smul_mem c hx
    have e : (⟨c • x, Λ.smul_mem c hx⟩ : ↥Λ) = ⟨((c : ℚ) : ℍ[ℚ, a, b]) * x, hcx⟩ := by
      apply Subtype.ext; show c • x = ((c : ℚ) : ℍ[ℚ, a, b]) * x; rw [zsmul_eq_mul]; norm_cast
    rw [pushPt_congr E e, act_mul_pt E _ _ (hΛℤ c) hx hcx, hxR, act_one_pt]

theorem mem_ann (hΛℤ : ∀ m : ℤ, ((m : ℚ) : ℍ[ℚ, a, b]) ∈ Λ)
    {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of S)) (R : SchemeHomOver t E.f) (x : ℍ[ℚ, a, b]) :
    x ∈ ann E hΛℤ t R ↔ ∃ hx : x ∈ Λ, pushPt (E.act ⟨x, hx⟩) (E.act_over _) R = E.L.one t := Iff.rfl

theorem mem_ann' (hΛℤ : ∀ m : ℤ, ((m : ℚ) : ℍ[ℚ, a, b]) ∈ Λ)
    {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of S)) (R : SchemeHomOver t E.f) (x : ↥Λ) :
    (x : ℍ[ℚ, a, b]) ∈ ann E hΛℤ t R ↔ pushPt (E.act x) (E.act_over x) R = E.L.one t :=
  ⟨fun ⟨_, h⟩ => h, fun h => ⟨x.2, h⟩⟩

end Pts

section Core

variable {r rbar N : ℕ} [Fact r.Prime] [Fact rbar.Prime]
    {a b : ℚ} (hB : IsIndefiniteRamifiedExactlyAt a b r rbar)
    (Λ : Submodule ℤ ℍ[ℚ, a, b]) (hΛ : IsMaximalOrder Λ) (hΛℤ : ∀ m : ℤ, ((m : ℚ) : ℍ[ℚ, a, b]) ∈ Λ)
    {k₀ : Type} [Field k₀] (A₀ : FakeEllipticCurve Λ N k₀) (e : ℕ)

theorem dvd_of_mul_star {m : ℍ[ℚ, a, b]} {n : ℤ}
    (hmn : m * star m = (((rbar : ℤ) * n : ℚ) : ℍ[ℚ, a, b])) : ∃ n' : ℤ, nrd m = (rbar : ℚ) * n' := by
  refine ⟨n, ?_⟩
  rw [mul_star_eq_coe_nrd] at hmn
  have h' := QuaternionAlgebra.coe_injective hmn
  exact_mod_cast h'

include hB hΛ in

theorem ann_eq_prime
    {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of k₀)) (P₀ : SchemeHomOver t A₀.f)
    (hgen : ∀ Q : SchemeHomOver t A₀.f, nsmulPt A₀.L t rbar Q = A₀.L.one t →
      ∃ x : ↥Λ, pushPt (A₀.act x) (A₀.act_over x) P₀ = Q)
    (hann : ∀ x : ↥Λ, pushPt (A₀.act x) (A₀.act_over x) P₀ = A₀.L.one t ↔
      ∃ y : ↥Λ, (x : ℍ[ℚ, a, b]) = (rbar : ℚ) • (y : ℍ[ℚ, a, b]))
    (φ ψ : A₀.A ⟶ A₀.A) (hφ : φ ≫ A₀.f = A₀.f) (hψ : ψ ≫ A₀.f = A₀.f)
    (hφ_hom : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of k₀)) (P Q : SchemeHomOver t A₀.f),
      mapPt φ hφ (A₀.L.mul t P Q) = A₀.L.mul t (mapPt φ hφ P) (mapPt φ hφ Q))
    (hψ_hom : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of k₀)) (P Q : SchemeHomOver t A₀.f),
      mapPt ψ hψ (A₀.L.mul t P Q) = A₀.L.mul t (mapPt ψ hψ P) (mapPt ψ hψ Q))
    (hφ_lin : ∀ m : ↥Λ, A₀.act m ≫ φ = φ ≫ A₀.act m) (hψ_lin : ∀ m : ↥Λ, A₀.act m ≫ ψ = ψ ≫ A₀.act m)
    (hψφ : ψ ≫ φ = A₀.act ⟨(((r ^ e * rbar : ℕ) : ℤ) : ℚ), hΛℤ _⟩)
    (hφ_nd : ¬ ∀ Q : SchemeHomOver t A₀.f, nsmulPt A₀.L t rbar Q = A₀.L.one t → mapPt φ hφ Q = A₀.L.one t)
    (hψ_nd : ¬ ∀ Q : SchemeHomOver t A₀.f, nsmulPt A₀.L t rbar Q = A₀.L.one t → mapPt ψ hψ Q = A₀.L.one t) :
    ∀ x : ℍ[ℚ, a, b], x ∈ ann A₀ hΛℤ t (mapPt φ hφ P₀) ↔ x ∈ Λ ∧ ∃ n : ℤ, nrd x = (rbar : ℚ) * n := by
  classical
  have hO : IsOrder Λ := hΛ.isOrder

  have hP₀tor : nsmulPt A₀.L t rbar P₀ = A₀.L.one t := by
    rw [← pushPt_act_natCast A₀ hΛℤ rbar t P₀]
    exact (hann _).2 ⟨⟨_, hΛℤ 1⟩, by
      show (((rbar : ℤ) : ℚ) : ℍ[ℚ, a, b]) = (rbar : ℚ) • (((1 : ℤ) : ℚ) : ℍ[ℚ, a, b])
      rw [← coe_mul_eq_smul, ← coe_mul]; congr 1; push_cast; ring⟩

  have zq : ∀ y : ℍ[ℚ, a, b], ((rbar : ℤ) • y) = (rbar : ℚ) • y := fun y => by
    rw [← Int.cast_smul_eq_zsmul ℚ (rbar : ℤ) y, Int.cast_natCast]

  set J := ann A₀ hΛℤ t (mapPt φ hφ P₀) with hJ
  have hJle : J ≤ Λ := fun x hx => ((mem_ann A₀ hΛℤ t _ x).1 hx).1
  have hJr : ∀ y ∈ Λ, (rbar : ℤ) • y ∈ J := by
    intro y hy
    have hry : (y : ℍ[ℚ, a, b]) * (((rbar : ℤ) : ℚ) : ℍ[ℚ, a, b]) ∈ Λ := hO.mul_mem hy (hΛℤ rbar)
    have e1 : ((rbar : ℤ) • y : ℍ[ℚ, a, b]) = y * (((rbar : ℤ) : ℚ) : ℍ[ℚ, a, b]) := by
      rw [zsmul_eq_mul, (Int.cast_commute (rbar : ℤ) y).eq]; norm_cast
    refine (mem_ann A₀ hΛℤ t _ _).2 ⟨by rw [e1]; exact hry, ?_⟩
    have e2 : (⟨(rbar : ℤ) • y, by rw [e1]; exact hry⟩ : ↥Λ) = ⟨y * (((rbar : ℤ) : ℚ) : ℍ[ℚ, a, b]), hry⟩ := Subtype.ext e1
    rw [pushPt_congr A₀ e2, act_mul_pt A₀ _ _ hy (hΛℤ rbar) hry, pushPt_act_natCast A₀ hΛℤ rbar,
      ← hom_nsmulPt A₀ φ hφ hφ_hom, hP₀tor, hom_one A₀ φ hφ hφ_hom, act_one_pt]
  have hJleft : ∀ m ∈ Λ, ∀ x ∈ J, m * x ∈ J := by
    intro m hm x hx
    obtain ⟨hxΛ, hxR⟩ := (mem_ann A₀ hΛℤ t _ x).1 hx
    refine (mem_ann A₀ hΛℤ t _ _).2 ⟨hO.mul_mem hm hxΛ, ?_⟩
    rw [act_mul_pt A₀ m x hm hxΛ (hO.mul_mem hm hxΛ), hxR, act_one_pt]
  obtain ⟨-, htri⟩ :=
    QuaternionAlgebra.IsMaximalOrder.leftIdeal_eq_or_eq_or_eq_of_isIndefiniteRamifiedExactlyAt_of_eq_or_eq hB Λ hΛ rbar (Or.inr rfl)
  rcases htri J hJle hJr hJleft with hbot | hmid | htop
  ·
    exfalso
    apply hψ_nd
    intro Q hQ
    obtain ⟨x, rfl⟩ := hgen Q hQ
    have htor : nsmulPt A₀.L t rbar (mapPt ψ hψ (pushPt (A₀.act x) (A₀.act_over x) P₀)) = A₀.L.one t := by
      rw [← hom_nsmulPt A₀ ψ hψ hψ_hom, hQ, hom_one A₀ ψ hψ hψ_hom]
    obtain ⟨z, hz⟩ := hgen _ htor
    have hcast : ((((r ^ e * rbar : ℕ) : ℤ) : ℚ) : ℍ[ℚ, a, b]) =
        ((((r ^ e : ℕ) : ℤ) : ℚ) : ℍ[ℚ, a, b]) * ((((rbar : ℕ) : ℤ) : ℚ) : ℍ[ℚ, a, b]) := by push_cast; rfl
    have hmem : ((((r ^ e : ℕ) : ℤ) : ℚ) : ℍ[ℚ, a, b]) * ((((rbar : ℕ) : ℤ) : ℚ) : ℍ[ℚ, a, b]) ∈ Λ := by
      rw [← hcast]; exact hΛℤ _
    have hcomp : mapPt φ hφ (mapPt ψ hψ (pushPt (A₀.act x) (A₀.act_over x) P₀)) = A₀.L.one t := by
      have step1 : mapPt φ hφ (mapPt ψ hψ (pushPt (A₀.act x) (A₀.act_over x) P₀)) =
          pushPt (A₀.act ⟨(((r ^ e * rbar : ℕ) : ℤ) : ℚ), hΛℤ _⟩) (A₀.act_over _) (pushPt (A₀.act x) (A₀.act_over x) P₀) := by
        apply Subtype.ext
        simp only [pushPt, mapPt_coe, Category.assoc, hψφ]
      rw [step1, pushPt_congr A₀ (show (⟨(((r ^ e * rbar : ℕ) : ℤ) : ℚ), hΛℤ _⟩ : ↥Λ) = ⟨_, hmem⟩ from Subtype.ext hcast),
        act_mul_pt A₀ ((((r ^ e : ℕ) : ℤ) : ℚ) : ℍ[ℚ, a, b]) ((((rbar : ℕ) : ℤ) : ℚ) : ℍ[ℚ, a, b]) (hΛℤ _) (hΛℤ _) hmem,
        pushPt_act_natCast A₀ hΛℤ rbar, hQ, act_one_pt]
    rw [← hz, lin_pt A₀ φ hφ hφ_lin] at hcomp
    have hzJ : (z : ℍ[ℚ, a, b]) ∈ J := (mem_ann' A₀ hΛℤ t _ z).2 hcomp
    obtain ⟨y, hy, hzy⟩ := (hbot z).1 hzJ
    rw [← hz]
    exact (hann z).2 ⟨⟨y, hy⟩, by rw [hzy]; exact zq y⟩
  · exact hmid
  ·
    exfalso
    apply hφ_nd
    intro Q hQ
    obtain ⟨x, rfl⟩ := hgen Q hQ
    have h1J : (1 : ℍ[ℚ, a, b]) ∈ J := by rw [htop]; exact hO.one_mem
    obtain ⟨h1Λ, h1R⟩ := (mem_ann A₀ hΛℤ t _ 1).1 h1J
    have hφP₀ : mapPt φ hφ P₀ = A₀.L.one t := by
      rw [← h1R]; apply Subtype.ext; simp only [pushPt, mapPt_coe, A₀.act_one h1Λ, Category.comp_id]
    rw [lin_pt A₀ φ hφ hφ_lin, hφP₀]; exact act_one_pt A₀ x t

include hB hΛ in
theorem clauses_at
  (f f' : A₀.A ⟶ A₀.A) (hf : f ≫ A₀.f = A₀.f) (hf' : f' ≫ A₀.f = A₀.f)
  (hf_hom : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of k₀)) (P Q : SchemeHomOver t A₀.f),
    mapPt f hf (A₀.L.mul t P Q) = A₀.L.mul t (mapPt f hf P) (mapPt f hf Q))
  (hf'_hom : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of k₀)) (P Q : SchemeHomOver t A₀.f),
    mapPt f' hf' (A₀.L.mul t P Q) = A₀.L.mul t (mapPt f' hf' P) (mapPt f' hf' Q))
  (hf_lin : ∀ m : ↥Λ, A₀.act m ≫ f = f ≫ A₀.act m) (hf'_lin : ∀ m : ↥Λ, A₀.act m ≫ f' = f' ≫ A₀.act m)
  (hff' : f ≫ f' = A₀.act ⟨(((r ^ e * rbar : ℕ) : ℤ) : ℚ), hΛℤ _⟩) (hf'f : f' ≫ f = A₀.act ⟨(((r ^ e * rbar : ℕ) : ℤ) : ℚ), hΛℤ _⟩) :
  ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of k₀)) (P₀ : SchemeHomOver t A₀.f),
    (∀ Q : SchemeHomOver t A₀.f, nsmulPt A₀.L t rbar Q = A₀.L.one t →
      ∃ x : ↥Λ, pushPt (A₀.act x) (A₀.act_over x) P₀ = Q) →
    (∀ x : ↥Λ, pushPt (A₀.act x) (A₀.act_over x) P₀ = A₀.L.one t ↔
      ∃ y : ↥Λ, (x : ℍ[ℚ, a, b]) = (rbar : ℚ) • (y : ℍ[ℚ, a, b])) →
    (¬ ∀ Q : SchemeHomOver t A₀.f, nsmulPt A₀.L t rbar Q = A₀.L.one t → mapPt f hf Q = A₀.L.one t) →
    (¬ ∀ Q : SchemeHomOver t A₀.f, nsmulPt A₀.L t rbar Q = A₀.L.one t → mapPt f' hf' Q = A₀.L.one t) →
    ∀ Q : SchemeHomOver t A₀.f,
    ((∀ (m : ↥Λ) (n : ℤ), (m : ℍ[ℚ, a, b]) * star (m : ℍ[ℚ, a, b]) = (((rbar : ℤ) * n : ℚ) : ℍ[ℚ, a, b]) →
          pushPt (A₀.act m) (A₀.act_over m) Q = A₀.L.one t) → mapPt f hf Q = A₀.L.one t) ∧
    (nsmulPt A₀.L t rbar Q = A₀.L.one t → mapPt f hf Q = A₀.L.one t →
      ∀ (m : ↥Λ) (n : ℤ), (m : ℍ[ℚ, a, b]) * star (m : ℍ[ℚ, a, b]) = (((rbar : ℤ) * n : ℚ) : ℍ[ℚ, a, b]) →
          pushPt (A₀.act m) (A₀.act_over m) Q = A₀.L.one t) ∧
    (nsmulPt A₀.L t rbar Q = A₀.L.one t →
      ∀ (m : ↥Λ) (n : ℤ), (m : ℍ[ℚ, a, b]) * star (m : ℍ[ℚ, a, b]) = (((rbar : ℤ) * n : ℚ) : ℍ[ℚ, a, b]) →
          pushPt (A₀.act m) (A₀.act_over m) (mapPt f' hf' Q) = A₀.L.one t) := by
  intro T t P₀ hgen hann hf_nd' hf'_nd'
  classical
  have hO : IsOrder Λ := hΛ.isOrder

  have hJ := ann_eq_prime hB Λ hΛ hΛℤ A₀ e t P₀ hgen hann f f' hf hf' hf_hom hf'_hom hf_lin hf'_lin hf'f hf_nd' hf'_nd'
  have hJ' := ann_eq_prime hB Λ hΛ hΛℤ A₀ e t P₀ hgen hann f' f hf' hf hf'_hom hf_hom hf'_lin hf_lin hff' hf'_nd' hf_nd'

  obtain ⟨⟨-, -, -, -, hPsq⟩, -⟩ :=
    QuaternionAlgebra.IsMaximalOrder.leftIdeal_eq_or_eq_or_eq_of_isIndefiniteRamifiedExactlyAt_of_eq_or_eq hB Λ hΛ rbar (Or.inr rfl)
  obtain ⟨π, hπΛ, hnrd, -, -, -⟩ :=
    QuaternionAlgebra.IsMaximalOrder.exists_generator_ramifiedPrime_of_isIndefiniteRamifiedExactlyAt hB Λ hΛ rbar (Or.inr rfl)
  have zq : ∀ y : ℍ[ℚ, a, b], ((rbar : ℤ) • y) = (rbar : ℚ) • y := fun y => by
    rw [← Int.cast_smul_eq_zsmul ℚ (rbar : ℤ) y, Int.cast_natCast]
  have hr0 : (rbar : ℚ) ≠ 0 := by exact_mod_cast (Fact.out : rbar.Prime).ne_zero

  have hrbar_mem : ((⟨((rbar : ℤ) : ℚ), hΛℤ rbar⟩ : ↥Λ) : ℍ[ℚ, a, b]) * star ((⟨((rbar : ℤ) : ℚ), hΛℤ rbar⟩ : ↥Λ) : ℍ[ℚ, a, b]) =
      (((rbar : ℤ) * (rbar : ℤ) : ℚ) : ℍ[ℚ, a, b]) := by
    show (((rbar : ℤ) : ℚ) : ℍ[ℚ, a, b]) * star (((rbar : ℤ) : ℚ) : ℍ[ℚ, a, b]) = _
    rw [QuaternionAlgebra.star_coe, ← coe_mul]

  obtain ⟨s, hs, hs1⟩ : ∃ s : ℤ, nrd π = (rbar : ℚ) * s ∧ (s : ℚ) * s = 1 := by
    rcases hnrd with h | h
    · exact ⟨1, by rw [h]; simp, by simp⟩
    · exact ⟨-1, by rw [h]; simp, by simp⟩
  have hπ_mem : π * star π = (((rbar : ℤ) * s : ℚ) : ℍ[ℚ, a, b]) := by
    rw [mul_star_eq_coe_nrd, hs]; norm_cast
  intro Q
  refine ⟨?_, ?_, ?_⟩
  ·
    intro hPQ
    have hQtor : nsmulPt A₀.L t rbar Q = A₀.L.one t := by
      rw [← pushPt_act_natCast A₀ hΛℤ rbar t Q]; exact hPQ _ _ hrbar_mem
    obtain ⟨x, rfl⟩ := hgen Q hQtor

    have hπx : pushPt (A₀.act ⟨π * (x : ℍ[ℚ, a, b]), hO.mul_mem hπΛ x.2⟩) (A₀.act_over _) P₀ = A₀.L.one t := by
      rw [act_mul_pt A₀ π x hπΛ x.2]; exact hPQ ⟨π, hπΛ⟩ s hπ_mem
    obtain ⟨y, hy⟩ := (hann ⟨_, hO.mul_mem hπΛ x.2⟩).1 hπx
    have hxP : (x : ℍ[ℚ, a, b]) ∈ Λ ∧ ∃ n : ℤ, nrd (x : ℍ[ℚ, a, b]) = (rbar : ℚ) * n := by
      refine ⟨x.2, ?_⟩
      obtain ⟨⟨ny, hny⟩, -⟩ := QuaternionAlgebra.IsOrder.exists_intCast_eq_nrd_and_exists_intCast_eq_trd hO y.2
      have hy' : π * (x : ℍ[ℚ, a, b]) = ((rbar : ℚ) : ℍ[ℚ, a, b]) * (y : ℍ[ℚ, a, b]) := by
        rw [coe_mul_eq_smul]; exact hy
      have hn : nrd π * nrd (x : ℍ[ℚ, a, b]) = (rbar : ℚ) ^ 2 * nrd (y : ℍ[ℚ, a, b]) := by
        rw [← nrd_mul', hy', nrd_mul', nrd_coe]
      rw [hs, ← hny] at hn

      refine ⟨s * ny, ?_⟩
      have h2 : (s : ℚ) * nrd (x : ℍ[ℚ, a, b]) = (rbar : ℚ) * ny := by
        have := hn
        have h3 : (rbar : ℚ) * ((s : ℚ) * nrd (x : ℍ[ℚ, a, b])) = (rbar : ℚ) * ((rbar : ℚ) * ny) := by
          rw [← mul_assoc, this]; ring
        exact mul_left_cancel₀ hr0 h3
      calc nrd (x : ℍ[ℚ, a, b]) = ((s : ℚ) * s) * nrd (x : ℍ[ℚ, a, b]) := by rw [hs1, one_mul]
        _ = (s : ℚ) * ((s : ℚ) * nrd (x : ℍ[ℚ, a, b])) := by ring
        _ = (s : ℚ) * ((rbar : ℚ) * ny) := by rw [h2]
        _ = (rbar : ℚ) * ((s * ny : ℤ) : ℚ) := by push_cast; ring
    have hxJ := (hJ x).2 hxP
    rw [lin_pt A₀ f hf hf_lin]
    exact (mem_ann' A₀ hΛℤ t _ x).1 hxJ
  ·
    intro hQtor hfQ m n hmn
    obtain ⟨x, rfl⟩ := hgen Q hQtor
    rw [lin_pt A₀ f hf hf_lin] at hfQ
    obtain ⟨-, nx, hnx⟩ := (hJ x).1 ((mem_ann' A₀ hΛℤ t _ x).2 hfQ)
    obtain ⟨y, hy, hmxy⟩ := hPsq m m.2 x x.2 (dvd_of_mul_star hmn) ⟨nx, hnx⟩
    rw [← act_mul_pt A₀ (m : ℍ[ℚ, a, b]) x m.2 x.2 (hO.mul_mem m.2 x.2)]
    exact (hann ⟨_, hO.mul_mem m.2 x.2⟩).2 ⟨⟨y, hy⟩, by show (m : ℍ[ℚ, a, b]) * x = _; rw [hmxy]; exact zq y⟩
  ·
    intro hQtor m n hmn
    obtain ⟨x, rfl⟩ := hgen Q hQtor
    rw [lin_pt A₀ f' hf' hf'_lin, ← act_mul_pt A₀ (m : ℍ[ℚ, a, b]) x m.2 x.2 (hO.mul_mem m.2 x.2)]
    apply (mem_ann' A₀ hΛℤ t _ ⟨_, hO.mul_mem m.2 x.2⟩).1
    apply (hJ' _).2
    refine ⟨hO.mul_mem m.2 x.2, ?_⟩
    obtain ⟨n', hn'⟩ := dvd_of_mul_star hmn
    obtain ⟨⟨nx, hnx⟩, -⟩ := QuaternionAlgebra.IsOrder.exists_intCast_eq_nrd_and_exists_intCast_eq_trd hO x.2
    exact ⟨n' * nx, by rw [nrd_mul', hn', ← hnx]; push_cast; ring⟩

end Core

end KerPartGeom

open KerPartGeom in
theorem solution
    {r rbar N : ℕ} [Fact r.Prime] [Fact rbar.Prime]
    {a b : ℚ} (hB : IsIndefiniteRamifiedExactlyAt a b r rbar)
    (Λ : Submodule ℤ ℍ[ℚ, a, b]) (hΛ : IsMaximalOrder Λ) (hΛℤ : ∀ m : ℤ, ((m : ℚ) : ℍ[ℚ, a, b]) ∈ Λ)
    (k₀ : Type) [Field k₀] [IsAlgClosed k₀] (hrk : (rbar : k₀) ≠ 0) (A₀ : FakeEllipticCurve Λ N k₀) (e : ℕ)
    (f f' : A₀.A ⟶ A₀.A) (hf : f ≫ A₀.f = A₀.f) (hf' : f' ≫ A₀.f = A₀.f)
    (hf_hom : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of k₀)) (P Q : SchemeHomOver t A₀.f),
      mapPt f hf (A₀.L.mul t P Q) = A₀.L.mul t (mapPt f hf P) (mapPt f hf Q))
    (hf'_hom : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of k₀)) (P Q : SchemeHomOver t A₀.f),
      mapPt f' hf' (A₀.L.mul t P Q) = A₀.L.mul t (mapPt f' hf' P) (mapPt f' hf' Q))
    (hf_lin : ∀ m : ↥Λ, A₀.act m ≫ f = f ≫ A₀.act m) (hf'_lin : ∀ m : ↥Λ, A₀.act m ≫ f' = f' ≫ A₀.act m)
    (hff' : f ≫ f' = A₀.act ⟨(((r ^ e * rbar : ℕ) : ℤ) : ℚ), hΛℤ _⟩) (hf'f : f' ≫ f = A₀.act ⟨(((r ^ e * rbar : ℕ) : ℤ) : ℚ), hΛℤ _⟩)
    (hf_nd : ¬ ∀ Q : SchemeHomOver (𝟙 (Spec (CommRingCat.of k₀))) A₀.f,
      nsmulPt A₀.L (𝟙 (Spec (CommRingCat.of k₀))) rbar Q = A₀.L.one (𝟙 (Spec (CommRingCat.of k₀))) →
        mapPt f hf Q = A₀.L.one (𝟙 (Spec (CommRingCat.of k₀))))
    (hf'_nd : ¬ ∀ Q : SchemeHomOver (𝟙 (Spec (CommRingCat.of k₀))) A₀.f,
      nsmulPt A₀.L (𝟙 (Spec (CommRingCat.of k₀))) rbar Q = A₀.L.one (𝟙 (Spec (CommRingCat.of k₀))) →
        mapPt f' hf' Q = A₀.L.one (𝟙 (Spec (CommRingCat.of k₀)))) :
    ∀ Q : SchemeHomOver (𝟙 (Spec (CommRingCat.of k₀))) A₀.f,
      ((∀ (m : ↥Λ) (n : ℤ), (m : ℍ[ℚ, a, b]) * star (m : ℍ[ℚ, a, b]) = (((rbar : ℤ) * n : ℚ) : ℍ[ℚ, a, b]) →
            pushPt (A₀.act m) (A₀.act_over m) Q = A₀.L.one (𝟙 (Spec (CommRingCat.of k₀)))) →
          mapPt f hf Q = A₀.L.one (𝟙 (Spec (CommRingCat.of k₀)))) ∧
      (nsmulPt A₀.L (𝟙 (Spec (CommRingCat.of k₀))) rbar Q = A₀.L.one (𝟙 (Spec (CommRingCat.of k₀))) →
          mapPt f hf Q = A₀.L.one (𝟙 (Spec (CommRingCat.of k₀))) →
        ∀ (m : ↥Λ) (n : ℤ), (m : ℍ[ℚ, a, b]) * star (m : ℍ[ℚ, a, b]) = (((rbar : ℤ) * n : ℚ) : ℍ[ℚ, a, b]) →
            pushPt (A₀.act m) (A₀.act_over m) Q = A₀.L.one (𝟙 (Spec (CommRingCat.of k₀)))) ∧
      (nsmulPt A₀.L (𝟙 (Spec (CommRingCat.of k₀))) rbar Q = A₀.L.one (𝟙 (Spec (CommRingCat.of k₀))) →
        ∀ (m : ↥Λ) (n : ℤ), (m : ℍ[ℚ, a, b]) * star (m : ℍ[ℚ, a, b]) = (((rbar : ℤ) * n : ℚ) : ℍ[ℚ, a, b]) →
            pushPt (A₀.act m) (A₀.act_over m) (mapPt f' hf' Q) = A₀.L.one (𝟙 (Spec (CommRingCat.of k₀)))) := by
  classical

  obtain ⟨FL⟩ := CerednikDrinfeld.QM.FakeEllipticCurve.nonempty_fullLevel_of_isMaximalOrder hB Λ hΛ rbar k₀ hrk A₀
  have hgid : geomPoint k₀ (RingHom.id k₀) = 𝟙 (Spec (CommRingCat.of k₀)) := by
    show Spec.map (CommRingCat.ofHom (RingHom.id k₀)) = 𝟙 _
    rw [CommRingCat.ofHom_id]; exact Spec.map_id _
  have key := clauses_at hB Λ hΛ hΛℤ A₀ e f f' hf hf' hf_hom hf'_hom hf_lin hf'_lin hff' hf'f
    (geomPoint k₀ (RingHom.id k₀)) (FakeEllipticCurve.sectionAt FL.P k₀ (RingHom.id k₀))
    (FL.generates k₀ (RingHom.id k₀)) (FL.annihilator k₀ (RingHom.id k₀))
    (by rw [hgid]; exact hf_nd) (by rw [hgid]; exact hf'_nd)
  rw [hgid] at key
  exact key

end S_CerednikDrinfeld_QM_FakeEllipticCurve_forall_section_mapPt_eq_one_iff_torsionPrime_of_comp_eq_act_of_not_forall_mapPt_eq_one
end P2MW
export P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_forall_section_mapPt_eq_one_iff_torsionPrime_of_comp_eq_act_of_not_forall_mapPt_eq_one (solution)
