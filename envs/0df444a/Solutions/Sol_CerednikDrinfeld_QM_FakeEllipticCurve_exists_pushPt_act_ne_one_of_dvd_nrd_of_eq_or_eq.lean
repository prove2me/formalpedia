-- Prove2me | solution 1 for CerednikDrinfeld.QM.FakeEllipticCurve.exists_pushPt_act_ne_one_of_dvd_nrd_of_eq_or_eq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.141142+00:00
-- url     : https://prove2.me/submissions/ed486a0f-7acb-527e-b2d5-41bbe6dee44a

import Definitions.Def_CerednikDrinfeld_QMModuli
import Definitions.Def_QuaternionAlgebra_ReducedNorm
import Definitions.Def_QuaternionAlgebra_EichlerOrder
import Definitions.Def_CerednikDrinfeld_ShimuraCurve
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawKernel
import Theorems.Thm_QuaternionAlgebra_IsMaximalOrder_exists_mem_dvd_nrd_not_sq_dvd_nrd_of_isIndefiniteRamifiedExactlyAt
import Theorems.Thm_QuaternionAlgebra_IsMaximalOrder_exists_mul_eq_natCast_smul_of_dvd_nrd_of_dvd_nrd_of_isIndefiniteRamifiedExactlyAt
import Theorems.Thm_QuaternionAlgebra_IsMaximalOrder_leftIdeal_eq_or_eq_or_eq_of_isIndefiniteRamifiedExactlyAt_of_eq_or_eq
import Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_natCard_isTorsionPoint_eq_pow_of_natCast_ne_zero
import Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_smoothOfRelativeDimension_two
import Theorems.Thm_QuaternionAlgebra_nrd_mul
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_exists_pushPt_act_ne_one_of_dvd_nrd_of_eq_or_eq
p2m_attr_erase "instance" "GoodReductionJacobian.RelativeGroupLaw.isIso_endKerStr_schemeHomOverId AlgebraicGeometry.Scheme.PresheafOfModules.symmetricCategory SheafOfModules.instFaithfulRingSheafPModToPMod SheafOfModules.symmetricCategory AlgebraicGeometry.Scheme.PresheafOfModules.monoidalCategory AlgebraicGeometry.Scheme.PresheafOfModules.monoidalClosed SheafOfModules.instFullRingSheafPModToPMod SheafOfModules.monoidalCategory AlgebraicGeometry.Scheme.Modules.symmetricCategory SheafOfModules.monoidalClosed SheafOfModules.instIsLocalizationPModRingSheafSheafifyFunctorPresheafW SheafOfModules.sheafifyFunctor_monoidal AlgebraicGeometry.Scheme.Modules.monoidalClosed AlgebraicGeometry.instMonoidalPresheafOfModulesModulesSheafify AlgebraicGeometry.Scheme.Modules.monoidalCategory PresheafOfModules.instMonoidalClosed PresheafOfModules.InternalHom.instModuleCarrierObjOppositeCommRingCatSubtypePiFamilyMemAddSubgroupNaturalFamilies PresheafOfModules.InternalHom.instModuleCarrierObjOppositeRingCatCompCommRingCatForget₂RingHomCarrierCarrierAbPresheaf PresheafOfModules.InternalHom.instSMulCarrierObjOppositeCommRingCatSubtypePiFamilyMemAddSubgroupNaturalFamilies AlgebraicGeometry.Scheme.Hom.opensMapFinal AlgebraicGeometry.RelPicard.RigidifiedLineBundle.setoid AlgebraicGeometry.RelPicard.RigidifiedLineBundle.instInhabited AlgebraicGeometry.OModulePresheaf.isScalarTower AlgebraicGeometry.Scheme.OrderedAffineCover.instLinearOrder AlgebraicGeometry.OModulePresheaf.module AlgebraicGeometry.Scheme.OrderedAffineCover.instFintype AlgebraicGeometry.Scheme.OrderedAffineCover.instFintypeIdx AlgebraicGeometry.OModulePresheaf.addCommGroup AlgebraicGeometry.Scheme.OrderedAffineCover.instDecidableEqIdx AlgebraicGeometry.OModulePresheaf.moduleSections TwoChartCech.Sections.M0_moduleA TwoChartCech.Sections.M1_module TwoChartCech.Cover.A01_algebra TwoChartCech.Cover.A0_algebra TwoChartCech.Cover.A1_commRing TwoChartCech.Cover.A1_algebra TwoChartCech.Sections.M01_module TwoChartCech.Sections.M0_addCommGroup TwoChartCech.Sections.M0_tower TwoChartCech.Sections.M01_addCommGroup"
p2m_attr_erase "instance" "TwoChartCech.Cover.A0_commRing TwoChartCech.Sections.M1_tower TwoChartCech.Sections.M01_moduleA TwoChartCech.Sections.M0_module TwoChartCech.Sections.M1_moduleA TwoChartCech.Sections.M1_addCommGroup TwoChartCech.Cover.A01_commRing TwoChartCech.Sections.M01_tower CoherentBaseChange.TwoTermComplex.C0_module CoherentBaseChange.TwoTermComplex.C0_addCommGroup CoherentBaseChange.TwoTermComplex.C1_module CoherentBaseChange.TwoTermComplex.C1_addCommGroup CoherentBaseChange.TwoTermComplex.C0_free CoherentBaseChange.TwoTermComplex.C1_finite CoherentBaseChange.TwoTermComplex.C0_finite CoherentBaseChange.TwoTermComplex.C1_free AlgebraicGeometry.OModulePresheaf.instSubsingletonObjZero AlgebraicGeometry.Scheme.Modules.preservesBinaryProducts_opensMap AlgebraicGeometry.Scheme.Modules.pullback_monoidal AlgebraicGeometry.Scheme.Modules.sheafify_isLocalization' AlgebraicGeometry.Scheme.Modules.preservesTerminal_opensMap AlgebraicGeometry.Scheme.Modules.pullback₀_monoidal AlgebraicGeometry.Scheme.Modules.preservesFiniteProducts_opensMap AlgebraicGeometry.Scheme.Modules.instLiftingPresheafOfModulesSheafifyPresheafWOpensCarrierCarrierCommRingCatGrothendieckTopologyObjFunctorOppositeIsSheafSheafCompPullback₀Pullback PresheafOfModules.PullbackMonoidal.pullback_monoidal PresheafOfModules.PullbackMonoidal.isIso_δ PresheafOfModules.pushforward_laxMonoidal PresheafOfModules.PullbackMonoidal.isIso_η PresheafOfModules.free_monoidal PresheafOfModules.restrictScalars_laxMonoidal PresheafOfModules.PullbackMonoidal.isIso_δ_gS PresheafOfModules.pullback_oplaxMonoidal PresheafOfModules.PullbackMonoidal.instPreservesColimitsOfSizeCompOppositeCommRingCatRingCatForget₂RingHomCarrierCarrierPb PresheafOfModules.pullback_monoidal' AlgebraicGeometry.SmoothOfRelativeDimension.fiberToSpecResidueField AlgebraicGeometry.SmoothOfRelativeDimension.pullback_snd AlgebraicGeometry.SmoothOfRelativeDimension.pullback_fst AlgebraicGeometry.SmoothOfRelativeDimension.smooth_one AlgebraicGeometry.SmoothProperCurve.isIntegral_pullback_Spec_field AlgebraicGeometry.IsProper.fiberToSpecResidueField"
p2m_attr_erase "instance" "AlgebraicCurve.CurveModel.isProper AlgebraicCurve.CurveModel.isIntegral AlgebraicCurve.CurveModel.smooth AlgebraicGeometry.Scheme.LocalRepresentabilityULift.instIsLocallyInjectiveFunUliftYonedaGluedToSheaf AlgebraicGeometry.Scheme.LocalRepresentabilityULift.instIsLocallySurjectiveFunUliftYonedaGluedToSheafOfIsLocallySurjectiveZariskiTopologyDescFunctorOppositeType AlgebraicGeometry.Scheme.LocalRepresentabilityULift.instIsOpenImmersionToGlued AlgebraicGeometry.Scheme.LocalRepresentabilityULift.instIsIsoSheafZariskiTopologyTypeUliftYonedaGluedToSheaf AlgebraicGeometry.RelPicard.instIsOpenImmersionToGlued AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.instFundamentalIdentityOfSumRamificationInertia AlgebraicCurve.Place.instIsScalarTowerResidueFieldRestrictPushforward AlgebraicCurve.Place.instAlgebraResidueFieldRestrictPushforward AlgebraicCurve.Place.instIsLocalHomRestrictInclusion AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions PresheafOfModules.ExteriorPower.instModulePresheafAb AlgebraicGeometry.RelEffCartierDiv.subsingleton_of_degree_zero AlgebraicGeometry.RelEffCartierDiv.isIso_subschemeIota_snd_of_degree_one AlgebraicGeometry.isIso_ker_graphOver_subschemeIota_snd AlgebraicGeometry.isClosedImmersion_graphOver AlgebraicGeometry.FGSubalgebra.instIsDirectedLe AlgebraicGeometry.FGSubalgebra.instQuasiSeparatedSpaceCarrierCarrierCommRingCatObjOppositeSchemeSpecDiagram AlgebraicGeometry.FGSubalgebra.instIsCofilteredOpposite AlgebraicGeometry.FGSubalgebra.instIsAffineObjOppositeSchemeSpecDiagram AlgebraicGeometry.FGSubalgebra.instNonempty AlgebraicGeometry.FGSubalgebra.instNonemptySubtypeLeSubalgebraValFG AlgebraicGeometry.FGSubalgebra.instCompactSpaceCarrierCarrierCommRingCatObjOppositeSchemeSpecDiagram AlgebraicGeometry.FGSubalgebra.instIsDirectedSubtypeLeSubalgebraValFG AlgebraicGeometry.FGSubalgebra.instIsAffineHomMapOppositeSchemeSpecDiagram AlgebraicGeometry.FGSubalgebra.instIsFiltered AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instNeg AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instSMulInt AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instAddCommGroup AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instAdd AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instSub"
p2m_attr_erase "instance" "AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instModuleCarrierObjOppositeOpensCarrierCarrierCommRingCatPresheafOpOpensTop AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instSMulCarrierObjOppositeOpensCarrierCarrierCommRingCatPresheafOpOpensTop AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instSMulNat AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instZero AlgebraicCurve.instHasLocalResidue_of_hasCanonicalLocalResidueK AlgebraicCurve.instHasCanonicalLocalResidueK_of_hasCanonicalLocalResidueKStar AlgebraicCurve.Place.kw_ffgc_finiteDimensional_adicCompletion instAlgebraSubtypeMemValuationSubring_definitions AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersIntegersCompletion ModularCurve.KwF4gRRTate.instAlgebraKAdicCompletionIntegers AlgebraicCurve.Place.kw_ffgc_continuousSMul_adicCompletionComap AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersCompletionCompletion IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions AlgebraicCurve.instHasCanonicalLocalResidueK AlgebraicCurve.Place.instAlgebra_restrictResidueField AlgebraicCurve.Place.instIsScalarTower_restrictResidueField AlgebraicCurve.instHasLocalResidue AlgebraicCurve.HasSeparableResidue.of_perfectField_of_isCurveOver AlgebraicCurve.HasSeparableResidue.of_perfectField AlgebraicCurve.Place.instIsLocalHom_restrictSubringHom AlgebraicCurve.instHasCanonicalLocalResidueKStar ModularCurve.KwNo6Pin.isLocalRing_completion SheafOfModules.isIso_ihomModelToIhom AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instDecidableEqIdx AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instFintype AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instLinearOrder AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instFintypeIdx AlgebraicGeometry.OModulePresheaf.Leray.relAltC_scalarTower AlgebraicGeometry.OModulePresheaf.Leray.ker_relAltd_modΓ AlgebraicGeometry.OModulePresheaf.Leray.relAltC_modΓ AlgebraicGeometry.OModulePresheaf.Leray.biC_abGrp AlgebraicGeometry.OModulePresheaf.Leray.relAltH_modΓ AlgebraicGeometry.OModulePresheaf.Leray.ker_relAltd_smul AlgebraicGeometry.OModulePresheaf.Leray.relAltH_scalarTower AlgebraicGeometry.OModulePresheaf.Leray.relAltH_smul"
p2m_attr_erase "instance" "AlgebraicGeometry.OModulePresheaf.Leray.biC_module DoubleComplex.instModuleE₂I DoubleComplex.Bounded.modR DoubleComplex.instModuleE₂II DoubleComplex.instAddCommGroupE₂II DoubleComplex.Bounded.abGrp DoubleComplex.instAddCommGroupE₂I AlgebraicGeometry.ChowDatum.hι_closed AlgebraicGeometry.ChowDatumProj.hιN_closed AlgebraicGeometry.ChowDatumProj.hp_proper AlgebraicGeometry.ChowDatum.hp_isoU AlgebraicGeometry.ChowDatum.hp_proper AlgebraicGeometry.ProjSpace.algebraAway AlgebraicGeometry.ProjSpace.instIsProperProdOverπ AlgebraicGeometry.ChowDatumProj.hp_isoU AlgebraicGeometry.ProjSpace.isProper_π AlgebraicGeometry.ProjSpace.finiteType_mvPolynomial ProjSpaceCech.GradedModule.H.module ProjSpaceCech.GradedModule.H.addCommGroup ProjSpaceCech.GradedModule.sec.instAdd ProjSpaceCech.GradedModule.sec.instNeg ProjSpaceCech.GradedModule.acg ProjSpaceCech.GradedModule.Frac.setoid ProjSpaceCech.GradedModule.modR ProjSpaceCech.GradedModule.sec.instModule ProjSpaceCech.GradedModule.sec.instAddCommGroup ProjSpaceCech.GradedModule.sec.instZero ProjSpaceCech.GradedModule.Presentation.fJ ProjSpaceCech.GradedModule.sec.instSMul ProjSpaceCech.Twist.H.module ProjSpaceCech.Idx.instFintype ProjSpaceCech.Twist.H.addCommGroup ProjSpaceCech.Idx.instDecidableEq ProjSpaceCech.Twist.Mon.instDecidableEq ProjSpaceCech.Twist.cochain.instAddCommGroup ProjSpaceCech.Twist.cochain.instModule AlgebraicGeometry.FGSubalgebra.tensorStage_directedSystem AlgebraicGeometry.RelEffCartierDiv.isClosedImmersion_subschemeι_resProdMap AlgebraicGeometry.RelEffCartierDiv.isOpenImmersion_resProdMap AlgebraicCurve.CurveModel.locallyOfFiniteType_gluedToBase"
p2m_attr_erase "instance" "AlgebraicCurve.CurveModel.isFractionRing_overlap AlgebraicCurve.CurveModel.isLocallyNoetherian_glued AlgebraicCurve.CurveModel.jacobsonSpace_glued AlgebraicCurve.CurveModel.isOpenImmersion_ι₀ AlgebraicCurve.CurveModel.isIntegral_glued AlgebraicCurve.CurveModel.quasiSeparated_gluedToBase AlgebraicCurve.CurveModel.compactSpace_glued AlgebraicCurve.CurveModel.isIntegral_adjoin_chartRing AlgebraicCurve.CurveModel.isFractionRing_overlap_functionField AlgebraicCurve.CurveModel.isProper_gluedToBase AlgebraicCurve.CurveModel.isOpenImmersion_ιU AlgebraicCurve.CurveModel.isOpenImmersion_f₀ AlgebraicCurve.CurveModel.isOpenImmersion_fInf AlgebraicCurve.CurveModel.isOpenImmersion_ιInf AlgebraicCurve.CurveModel.algebra_overlap_functionField AlgebraicCurve.CurveModel.quasiCompact_gluedToBase AlgebraicCurve.CurveModel.algebraAdjoin AlgebraicCurve.CurveModel.isDedekindDomain_chartRing AlgebraicCurve.CurveModel.isIntegralClosure AlgebraicCurve.CurveModel.finite_chartRing AlgebraicCurve.CurveModel.centre_isPrime AlgebraicCurve.CurveModel.isFractionRing_chartRing AlgebraicCurve.CurveModel.finiteType_chartRing AlgebraicCurve.CurveModel.isNoetherianRing_chartRing AlgebraicCurve.CurveModel.isScalarTower_base_adjoin AlgebraicCurve.CurveModel.isScalarTower_adjoin AlgebraicCurve.CurveModel.chartRing_finitePresentation instTopologicallyFGOfFiniteType AlgebraicGeometry.ProjSpace.twistObj.addCommGroup AlgebraicGeometry.ProjSpace.twistFam.module AlgebraicGeometry.ProjSpace.twistObj.module AlgebraicGeometry.ProjSpace.twistObj.moduleSections AlgebraicGeometry.ProjSpace.twistFam.addCommGroup"
p2m_attr_erase "simp" "QuaternionAlgebra.ClassSet.map_mk QuaternionAlgebra.baseChangeRight_tmul QuaternionAlgebra.mapOfAlgebraMapEq_apply QuaternionAlgebra.baseChange_tmul NeronModelInfra.NeronModelPropertyBundle.endExtensionEquiv_symm_restrict NeronModelInfra.schemeHomOverComp_id_left NeronModelInfra.schemeHomOverComp_id_right NeronModelInfra.schemeHomOverId_coe NeronModelInfra.NeronModelPropertyBundle.endExtensionEquiv_apply NeronModelInfra.NeronModelPropertyBundle.restrict_endExtensionEquiv_symm NeronModelInfra.schemeHomOverComp_coe NeronModelInfra.schemeHomOverNpow_succ NeronModelInfra.schemeHomOverNpow_zero GoodReductionJacobian.relativeGroupLawOfGrpObj_inv GoodReductionJacobian.relativeGroupLawOfGrpObj_mul GoodReductionJacobian.overHomEquivSchemeHomOver_apply_coe GoodReductionJacobian.relativeGroupLawOfGrpObj_one GoodReductionJacobian.overHomEquivSchemeHomOver_symm_apply_left SheafOfModules.tensorUnit_eq AlgebraicGeometry.Scheme.Modules.tensorUnit_eq PresheafOfModules.InternalHom.presheaf_map_apply PresheafOfModules.InternalHom.curryFamily_app PresheafOfModules.InternalHom.add_app PresheafOfModules.InternalHom.smul_app PresheafOfModules.InternalHom.zero_app PresheafOfModules.ihomObj_map_val PresheafOfModules.ihomFunctor_map PresheafOfModules.InternalHom.restrict_app PresheafOfModules.InternalHom.postcomp_app PresheafOfModules.InternalHom.neg_app PresheafOfModules.curry'_app_val PresheafOfModules.InternalHom.presheaf_obj PresheafOfModules.ihomFunctor_obj PresheafOfModules.ihomObj_obj PresheafOfModules.InternalHom.sub_app PresheafOfModules.ihomMap_app_val AlgebraicGeometry.Scheme.Modules.tensorPow_zero AlgebraicGeometry.Scheme.Modules.tensorPow_succ AlgebraicGeometry.RelPicard.RigidifiedLineBundle.mk.sizeOf_spec AlgebraicGeometry.RelPicard.RigidifiedLineBundle.mk.injEq"
p2m_attr_erase "simp" "AlgebraicGeometry.Scheme.OrderedAffineCover.mk.injEq AlgebraicGeometry.OModulePresheaf.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCover.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.mk.injEq AlgebraicGeometry.Scheme.TwoAffineOpenCover.mk.injEq AlgebraicGeometry.Scheme.TwoAffineOpenCover.mk.sizeOf_spec AlgebraicGeometry.Scheme.TwoAffineOpenCover.pullback_U1 AlgebraicGeometry.Scheme.TwoAffineOpenCover.pullback_U0 TwoChartCech.Sections.mk.injEq TwoChartCech.Cover.mk.injEq TwoChartCech.GrothendieckComplex.mk.injEq TwoChartCech.Sections.mk.sizeOf_spec TwoChartCech.Cover.mk.sizeOf_spec TwoChartCech.Cover.lineBundle_r0_apply TwoChartCech.GrothendieckComplex.mk.sizeOf_spec TwoChartCech.Cover.lineBundle_r1_apply CoherentBaseChange.TwoTermComplex.mk.sizeOf_spec CoherentBaseChange.TwoTermComplex.mk.injEq AlgebraicGeometry.OModulePresheaf.prod_obj AlgebraicGeometry.OModulePresheaf.restrOpen_obj AlgebraicGeometry.OModulePresheaf.DevissageStep.mk.injEq AlgebraicGeometry.OModulePresheaf.pushforward_obj AlgebraicGeometry.OModulePresheaf.im_obj AlgebraicGeometry.OModulePresheaf.pow_obj AlgebraicGeometry.OModulePresheaf.fstHom_app AlgebraicGeometry.OModulePresheaf.ker_obj AlgebraicGeometry.OModulePresheaf.coker_obj AlgebraicGeometry.OModulePresheaf.DevissageStep.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCover.preimage_U AlgebraicGeometry.OModulePresheaf.sndHom_app AlgebraicGeometry.OModulePresheaf.Hom.mk.injEq AlgebraicGeometry.OModulePresheaf.Hom.id_app AlgebraicGeometry.OModulePresheaf.AffHom.appSections_apply AlgebraicGeometry.OModulePresheaf.AffHom.comp_app AlgebraicGeometry.OModulePresheaf.AffSES.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.AffHom.kerMap_coe AlgebraicGeometry.OModulePresheaf.AffHom.id_app AlgebraicGeometry.OModulePresheaf.Hom.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.Hom.toAffHom_app AlgebraicGeometry.OModulePresheaf.SES.mk.sizeOf_spec"
p2m_attr_erase "simp" "AlgebraicGeometry.OModulePresheaf.AffHom.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.Hom.comp_app AlgebraicGeometry.OModulePresheaf.SES.mk.injEq AlgebraicGeometry.OModulePresheaf.AffHom.mk.injEq AlgebraicGeometry.OModulePresheaf.Hom.appSections_apply AlgebraicGeometry.OModulePresheaf.AffSES.mk.injEq PresheafOfModules.freeεIso_hom_app PresheafOfModules.freeμIso_hom_app AlgebraicGeometry.RelPicard.RepresentsRelSubPic.mk.injEq AlgebraicGeometry.RelPicard.SubPicCondition.mk.injEq AlgebraicGeometry.RelPicard.SubPicCondition.mk.sizeOf_spec AlgebraicGeometry.RelPicard.RepresentsRelSubPic.mk.sizeOf_spec AlgebraicGeometry.SmoothProperCurve.sectionBaseChange_coe_snd AlgebraicGeometry.SmoothProperCurve.sectionBaseChange_coe_fst AlgebraicCurve.CurveModel.mk.injEq AlgebraicCurve.CurveModel.mk.sizeOf_spec AlgebraicCurve.mulAdele_apply AlgebraicCurve.residuePairing_apply_coe AlgebraicCurve.mem_adeleBdd AlgebraicCurve.weilSmul_one AlgebraicCurve.diagonalHom_apply AlgebraicCurve.weilSmul_apply AlgebraicCurve.adeleSpaceMul_coe AlgebraicCurve.mulAdele_one AlgebraicGeometry.SmoothProperCurve.FiniteMapData.twoAffineOpenCover_U1 AlgebraicGeometry.SmoothProperCurve.FiniteMapData.mk.injEq AlgebraicGeometry.SmoothProperCurve.FiniteMapData.mk.sizeOf_spec AlgebraicGeometry.SmoothProperCurve.FiniteMapData.twoAffineOpenCover_U0 AlgebraicGeometry.RelPicard.SubPicCondition.onClasses_mk AlgebraicGeometry.RelPicard.relSubPicPresheaf_map_coe CategoryTheory.Functor.OverTotal.ofFibre_fst CategoryTheory.Functor.overTotal_map_fst AlgebraicGeometry.Scheme.LocalRepresentabilityULift.glueData_J AlgebraicGeometry.Scheme.LocalRepresentabilityULift.uliftYoneda_toGlued_uliftYonedaGluedToSheaf AlgebraicGeometry.Scheme.LocalRepresentabilityULift.glueData_t' AlgebraicGeometry.Scheme.LocalRepresentabilityULift.uliftYoneda_toGlued_uliftYonedaGluedToSheaf_assoc AlgebraicGeometry.Scheme.LocalRepresentabilityULift.uliftYonedaGluedToSheaf_app_toGlued AlgebraicGeometry.Scheme.LocalRepresentabilityULift.glueData_openCover_map AlgebraicGeometry.Scheme.LocalRepresentabilityULift.uliftYonedaGluedToSheaf_app_comp AlgebraicGeometry.Scheme.LocalRepresentabilityULift.glueData_V"
p2m_attr_erase "simp" "AlgebraicGeometry.Scheme.LocalRepresentabilityULift.glueData_t AlgebraicGeometry.Scheme.LocalRepresentabilityULift.glueData_U AlgebraicGeometry.Scheme.LocalRepresentabilityULift.glueData_f AlgebraicGeometry.RelPicard.designationOfRepresentableBy_P AlgebraicGeometry.RelPicard.designationOfRepresentableBy_toBase AlgebraicGeometry.RelPicard.rigSection_snd AlgebraicGeometry.RelPicard.RigidifiedLineBundle.ofInvertible_L AlgebraicGeometry.RelPicard.rigSection_snd_assoc AlgebraicGeometry.RelPicard.SubPicGroupCondition.mk.injEq AlgebraicGeometry.RelPicard.SubPicGroupCondition.mk.sizeOf_spec AlgebraicCurve.coe_cechH0Equiv_apply AlgebraicCurve.cechH1ToH1_mk AlgebraicCurve.lSpaceOn_univ AlgebraicCurve.lSpaceOn_empty AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.Divisor.mapRestrict_single AlgebraicCurve.Divisor.pushforward_single AlgebraicCurve.Place.coe_restrictInclusion AlgebraicCurve.Place.mem_fiber AlgebraicCurve.Place.restrict_toValuationSubring AlgebraicCurve.Divisor.degree_pushforward AlgebraicCurve.Place.restrictResidueMap_residue AlgebraicCurve.Pic0.coe_pushforwardDegZeroHom AlgebraicCurve.Pic0.coe_pullbackDegZeroHom AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe"
p2m_attr_erase "simp" "ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Divisor.degree_pushforwardAlong AlgebraicCurve.Pic0.coe_degZeroCorrespondence AlgebraicCurve.Place.mem_fiberAlong AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.jqNModC_one ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one AlgebraicCurve.Place.differentialCoeff_zero AlgebraicCurve.Place.differentialCoeff_dCoord AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.injEq AlgebraicCurve.TranscendenceTower.mk.injEq AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec AlgebraicCurve.PoleDivisorPackage.mk.injEq AlgebraicGeometry.RelPicard.thetaBundle_def AlgebraicGeometry.RelPicard.picardBundle_def AlgebraicGeometry.RelEffCartierDiv.toRelEffDivisor_ofRelEffDivisor"
p2m_attr_erase "simp" "AlgebraicGeometry.RelEffCartierDiv.toRelEffDivisor_I AlgebraicGeometry.mapOnProdOver_fst_assoc AlgebraicGeometry.RelEffCartierDiv.mk.sizeOf_spec AlgebraicGeometry.RelEffCartierDiv.mk.injEq AlgebraicGeometry.mapOnProdOver_snd AlgebraicGeometry.mapOnProdOver_fst AlgebraicGeometry.mapOnProdOver_snd_assoc AlgebraicGeometry.mapOnProdOver_id AlgebraicCurve.RelEffDivisor.mk.sizeOf_spec AlgebraicCurve.mapOnProd_fst AlgebraicCurve.mapOnProd_fst_assoc AlgebraicCurve.mapOnProd_snd AlgebraicCurve.UnivDivisorPack.mk.injEq AlgebraicCurve.RelEffDivisor.mk.injEq AlgebraicCurve.UnivDivisorPack.mk.sizeOf_spec AlgebraicCurve.mapOnProd_snd_assoc AlgebraicGeometry.Scheme.Modules.exteriorPower_obj PresheafOfModules.exteriorPower_map_ιMulti PresheafOfModules.ExteriorPower.appₗ_apply AlgebraicGeometry.prodKerGraph_one AlgebraicGeometry.fibrePowOver.proj_comp AlgebraicGeometry.prodKerGraph_zero AlgebraicGeometry.RelEffCartierDiv.empty_I AlgebraicGeometry.fibrePowOver.proj_comp_assoc AlgebraicGeometry.graphOver_fst_assoc AlgebraicGeometry.RelEffCartierDiv.toPoint_comp AlgebraicGeometry.RelEffCartierDiv.toPoint_comp_assoc AlgebraicGeometry.graphOver_fst AlgebraicGeometry.RelEffCartierDiv.ofPoint_I AlgebraicGeometry.graphOver_snd AlgebraicGeometry.graphOver_snd_assoc AlgebraicCurve.SymmetricPowerPackage.mk.sizeOf_spec AlgebraicCurve.SymmetricPowerPackage.mk.injEq AlgebraicGeometry.FGSubalgebra.cocone_ι_app_apply AlgebraicGeometry.RelPicard.fst_toProdSpec AlgebraicGeometry.RelPicard.toProdSpec_fst_assoc AlgebraicGeometry.RelPicard.pointsSubBasepointModule_cons AlgebraicGeometry.RelPicard.pointsSubBasepointModule_nil AlgebraicGeometry.RelPicard.fst_toProdSpec_assoc AlgebraicGeometry.RelPicard.toProdSpec_fst"
p2m_attr_erase "simp" "AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.sub_app AlgebraicGeometry.Scheme.IdealSheafData.sres_sresTop AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.add_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.mk.sizeOf_spec AlgebraicGeometry.Scheme.IdealSheafData.coe_resLE AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.smul_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.coe_ofLE_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.ideal_range AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.zero_app AlgebraicGeometry.Scheme.IdealSheafData.sres_sres AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.comp_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.neg_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.id_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.coe_mulRight_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.nsmul_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.mk.injEq AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.zsmul_app AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.sizeOf_spec AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.injEq AlgebraicCurve.adeleSingle_coe AlgebraicCurve.kaehlerResidueTermKFam_apply AlgebraicCurve.Place.LocalResidueData.mk.injEq AlgebraicCurve.Place.LocalResidueData.mk.sizeOf_spec AlgebraicCurve.Place.kw_ffgc_adicCompletionComapIntegers_coe AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.sizeOf_spec AlgebraicCurve.Place.mem_simplePoleSubmodule AlgebraicCurve.Place.coe_uniformizerSubring ModularCurve.Lg37.Lg37CompletionSection.mk.injEq AlgebraicCurve.Place.CoefficientFieldSection.mk.injEq AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.injEq ModularCurve.Lg37.Lg37CompletionSection.mk.sizeOf_spec AlgebraicCurve.Place.CoefficientFieldSection.mk.sizeOf_spec AlgebraicCurve.Place.poleSubmodule_one AlgebraicCurve.Place.mem_poleSubmodule AlgebraicGeometry.Scheme.Modules.toUnitSection_ofUnitSection AlgebraicGeometry.Scheme.Modules.pullbackSection_def AlgebraicGeometry.Scheme.Modules.ofUnitSection_toUnitSection PresheafOfModules.InternalHom.IsSheafAux.appAt_toPresheafHom SheafOfModules.ihomSectionsEquivFamily_unit AlgebraicGeometry.Scheme.Modules.restrictHomEquivFamily_apply"
p2m_attr_erase "simp" "SheafOfModules.ihomEval_unit_app AlgebraicGeometry.Scheme.Modules.ihomEval_zero_right AlgebraicGeometry.Scheme.Modules.ihomEval_zero_left AlgebraicGeometry.Scheme.Modules.homOfFamily_app_apply SheafOfModules.unit_ihomSectionsEquivFamily AlgebraicGeometry.Scheme.Modules.familyOfHom_app AlgebraicGeometry.Scheme.Modules.restrictUnitIso_hom_app_apply AlgebraicGeometry.Scheme.Modules.restrictUnitIso_inv_app_apply AlgebraicGeometry.Scheme.Modules.restrictHomOfFamily_app_apply AlgebraicGeometry.Scheme.Modules.restrictHomEquivFamily_symm_apply AlgebraicGeometry.Scheme.Modules.tensorSections_zero_right AlgebraicGeometry.Scheme.Modules.map_unitSection AlgebraicGeometry.Scheme.Modules.tensorSectionsBilin_apply AlgebraicGeometry.Scheme.Modules.tensorPowSection_zero AlgebraicGeometry.Scheme.Modules.tensorSections_zero_left AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_neg AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_zero AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_sub AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_add AlgebraicGeometry.Scheme.OrderedAffineCover.toCoverOf_U AlgebraicGeometry.Scheme.OrderedAffineCoverOf.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCoverOf.mk.injEq AlgebraicGeometry.Scheme.OrderedAffineCover.restrict_U AlgebraicGeometry.OModulePresheaf.Leray.restrictToPreimage_U DoubleComplex.Bounded.mk.injEq DoubleComplex.Bounded.mk.sizeOf_spec DoubleComplex.Convergence.mk.injEq DoubleComplex.Convergence.mk.sizeOf_spec DoubleComplex.SubQuot.mk.sizeOf_spec DoubleComplex.SubQuot.mk.injEq AlgebraicGeometry.ChowDatumProj.mk.sizeOf_spec AlgebraicGeometry.ChowDatum.mk.sizeOf_spec AlgebraicGeometry.ChowDatumProj.mk.injEq AlgebraicGeometry.ChowDatum.mk.injEq ProjSpaceCech.GradedModule.mk.injEq ProjSpaceCech.GradedModule.mk.sizeOf_spec ProjSpaceCech.GradedModule.Frac.mk.sizeOf_spec ProjSpaceCech.GradedModule.Presentation.mk.injEq ProjSpaceCech.GradedModule.Frac.mk.injEq ProjSpaceCech.GradedModule.Presentation.mk.sizeOf_spec"
p2m_attr_erase "simp" "ProjSpaceCech.GradedModule.Hom.shift_toLinearMap ProjSpaceCech.GradedModule.Hom.mk.sizeOf_spec ProjSpaceCech.GradedModule.Hom.mk.injEq TwoChartCech.Mumford.dK_apply TwoChartCech.Mumford.ι0_apply TwoChartCech.Mumford.ι1_apply TwoChartCech.KerCoprod.dK_apply TwoChartCech.KerCoprod.ι1_apply TwoChartCech.KerCoprod.ι0_apply AlgebraicGeometry.tilde.functorCompPullbackSpecIso_app AlgebraicGeometry.RelPicard.algEquivZeroGroupCut_toSubPicCondition AlgebraicGeometry.RelPicard.LFP.stageHom_val AlgebraicGeometry.RelPicard.BaseChange.relSubPicPresheafRestrictIso_hom_app_coe AlgebraicGeometry.RelPicard.BaseChange.relSubPicPresheafRestrictIso_inv_app_coe AlgebraicGeometry.RelPicard.BaseChange.restrict_P AlgebraicGeometry.RelEffCartierDiv.IsUniversal.lift_comp AlgebraicGeometry.RelEffCartierDiv.functor_map_fst AlgebraicGeometry.RelEffCartierDiv.IsUniversal.homEquiv_apply AlgebraicGeometry.RelEffCartierDiv.IsUniversal.lift_pullbackAlong AlgebraicGeometry.RelEffCartierDiv.IsUniversal.homEquiv_symm_apply AlgebraicGeometry.RelEffCartierDiv.IsUniversal.lift_comp_assoc AlgebraicGeometry.RelEffCartierDiv.supportedIn_top AlgebraicGeometry.RelEffCartierDiv.mem_supportedIn_iff AlgebraicGeometry.RelEffCartierDiv.supportedIn_top_eq AlgebraicGeometry.RelEffCartierDiv.restrictAlong_extendAlong AlgebraicGeometry.RelEffCartierDiv.extendAlong_I AlgebraicGeometry.RelEffCartierDiv.resProdMap_snd AlgebraicGeometry.RelEffCartierDiv.restrictAlong_I AlgebraicGeometry.RelEffCartierDiv.extendAlong_restrictAlong AlgebraicGeometry.RelEffCartierDiv.resProdMap_fst_assoc AlgebraicGeometry.RelEffCartierDiv.resProdMap_snd_assoc AlgebraicGeometry.RelEffCartierDiv.resProdMap_fst CoherentBaseChange.FibreH0Family.mk.sizeOf_spec CoherentBaseChange.FibreH0Family.mk.injEq AlgebraicGeometry.Scheme.Modules.ProjPresentation.mk.injEq AlgebraicGeometry.Scheme.Modules.ProjPresentation.mk.sizeOf_spec AlgebraicCurve.CurveModel.coe_gInf AlgebraicCurve.CurveModel.coe_tInvChart AlgebraicCurve.CurveModel.ιInf_gluedToBase_assoc AlgebraicCurve.CurveModel.ιInf_gluedToBase"
p2m_attr_erase "simp" "AlgebraicCurve.CurveModel.primeOfι₀_asIdeal AlgebraicCurve.CurveModel.coe_tChart AlgebraicCurve.CurveModel.ι₀_gluedToBase_assoc AlgebraicCurve.CurveModel.primeOfιInf_asIdeal AlgebraicCurve.CurveModel.ι₀_gluedToBase AlgebraicCurve.CurveModel.coe_tma AlgebraicCurve.CurveModel.coe_primeEquivChartPlaces RegularLocalRingQuotientAscent.dualNumberFst_apply AlgebraicGeometry.ProjSpace.twistObj.mk.injEq AlgebraicGeometry.ProjSpace.twistObj.zero_val AlgebraicGeometry.ProjSpace.twistObj.add_val AlgebraicGeometry.ProjSpace.twist_res_val AlgebraicGeometry.ProjSpace.twist_smul_val AlgebraicGeometry.ProjSpace.twistGradeToObj_val AlgebraicGeometry.ProjSpace.twistObj.smul_val AlgebraicGeometry.ProjSpace.twistGradeEquiv_apply_val AlgebraicGeometry.ProjSpace.twistObj.mk.sizeOf_spec"

set_option autoImplicit false

universe u

open CategoryTheory AlgebraicGeometry NeronModelInfra GoodReductionJacobian
open scoped Quaternion
p2m_open "CerednikDrinfeld P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_exists_pushPt_act_ne_one_of_dvd_nrd_of_eq_or_eq.CerednikDrinfeld CerednikDrinfeld.QM P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_exists_pushPt_act_ne_one_of_dvd_nrd_of_eq_or_eq.CerednikDrinfeld.QM QuaternionAlgebra"

namespace CerednikDrinfeld
p2m_export "CerednikDrinfeld" "QM.FakeEllipticCurve QM.FakeEllipticCurve.smoothOfRelativeDimension_two"
namespace QM
p2m_export "CerednikDrinfeld.QM" "pushPt nsmulPt FakeEllipticCurve FakeEllipticCurve.smoothOfRelativeDimension_two"
namespace FakeEllipticCurve
p2m_export "CerednikDrinfeld.QM.FakeEllipticCurve" "A f act_hom comm act act_one L act_mul act_add act_over bundle smoothOfRelativeDimension_two"
p2m_open "CerednikDrinfeld.QM.FakeEllipticCurve CerednikDrinfeld.QM CerednikDrinfeld"

variable {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} {N : ℕ} {S : Type u} [CommRing S]

def Pts (E : FakeEllipticCurve Λ N S) {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of S)) : Type u :=
  SchemeHomOver t E.f

namespace Pts

variable (E : FakeEllipticCurve Λ N S) {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of S))

def of (P : SchemeHomOver t E.f) : Pts E t := P

def val (P : Pts E t) : SchemeHomOver t E.f := P

@[scoped simp] theorem val_of (P : SchemeHomOver t E.f) : val E t (of E t P) = P := rfl
@[scoped simp] theorem of_val (P : Pts E t) : of E t (val E t P) = P := rfl

def equiv : SchemeHomOver t E.f ≃ Pts E t := Equiv.refl _

scoped instance instZero : Zero (Pts E t) := ⟨E.L.one t⟩
scoped instance instAdd : Add (Pts E t) := ⟨fun P Q => E.L.mul t P Q⟩
scoped instance instNeg : Neg (Pts E t) := ⟨fun P => E.L.inv t P⟩

scoped instance instAddCommGroup : AddCommGroup (Pts E t) where
  add_assoc := E.L.mul_assoc t
  zero_add := E.L.one_mul t
  add_zero := E.L.mul_one t
  nsmul n P := nsmulPt E.L t n P
  nsmul_zero _ := rfl
  nsmul_succ _ _ := rfl
  neg_add_cancel := E.L.inv_mul_cancel t
  add_comm := E.comm t
  zsmul := zsmulRec (fun n P => nsmulPt E.L t n P)

theorem add_def (P Q : Pts E t) : P + Q = E.L.mul t P Q := rfl
theorem zero_def : (0 : Pts E t) = E.L.one t := rfl
theorem neg_def (P : Pts E t) : -P = E.L.inv t P := rfl

theorem nsmul_eq_nsmulPt (n : ℕ) (P : Pts E t) : n • P = nsmulPt E.L t n P := rfl

def actHom (m : ↥Λ) : Pts E t →+ Pts E t where
  toFun P := pushPt (E.act m) (E.act_over m) P
  map_zero' := by
    show pushPt (E.act m) (E.act_over m) (E.L.one t) = E.L.one t
    have h := E.act_hom m t (E.L.one t) (E.L.one t)
    rw [E.L.one_mul] at h

    have := congrArg (E.L.mul t (E.L.inv t (pushPt (E.act m) (E.act_over m) (E.L.one t)))) h
    rw [← E.L.mul_assoc, E.L.inv_mul_cancel, E.L.one_mul] at this
    exact this.symm
  map_add' P Q := E.act_hom m t P Q

theorem actHom_apply (m : ↥Λ) (P : Pts E t) : actHom E t m P = pushPt (E.act m) (E.act_over m) P := rfl

theorem coe_actHom_apply (m : ↥Λ) (P : Pts E t) :
    (val E t (actHom E t m P)).1 = (val E t P).1 ≫ E.act m := rfl

theorem actHom_one (h : (1 : ℍ[ℚ, a, b]) ∈ Λ) : actHom E t ⟨1, h⟩ = AddMonoidHom.id _ := by
  ext P
  apply Subtype.ext
  show (val E t P).1 ≫ E.act ⟨1, h⟩ = (val E t P).1
  rw [E.act_one h, Category.comp_id]

theorem actHom_mul (x y : ↥Λ) (h : (x : ℍ[ℚ, a, b]) * (y : ℍ[ℚ, a, b]) ∈ Λ) :
    actHom E t ⟨(x : ℍ[ℚ, a, b]) * (y : ℍ[ℚ, a, b]), h⟩ = (actHom E t x).comp (actHom E t y) := by
  ext P
  apply Subtype.ext
  show (val E t P).1 ≫ E.act ⟨(x : ℍ[ℚ, a, b]) * (y : ℍ[ℚ, a, b]), h⟩ = ((val E t P).1 ≫ E.act y) ≫ E.act x
  rw [E.act_mul x y h, Category.assoc]

theorem actHom_add (x y : ↥Λ) : actHom E t (x + y) = actHom E t x + actHom E t y := by
  ext P
  exact E.act_add x y t P

theorem natCast_mem (hΛ : IsOrder Λ) (n : ℕ) : ((n : ℚ) : ℍ[ℚ, a, b]) ∈ Λ := by
  have : ((n : ℚ) : ℍ[ℚ, a, b]) = (n : ℤ) • (1 : ℍ[ℚ, a, b]) := by
    rw [zsmul_eq_mul, mul_one]; norm_cast
  rw [this]; exact Λ.smul_mem _ hΛ.one_mem

theorem actHom_natCast (hΛ : IsOrder Λ) (n : ℕ) (hn : ((n : ℚ) : ℍ[ℚ, a, b]) ∈ Λ) (P : Pts E t) :
    actHom E t ⟨((n : ℚ) : ℍ[ℚ, a, b]), hn⟩ P = n • P := by
  induction n with
  | zero =>
    have e : (⟨(((0 : ℕ) : ℚ) : ℍ[ℚ, a, b]), hn⟩ : ↥Λ) = 0 := by apply Subtype.ext; simp
    rw [e, zero_smul]

    have h2 := actHom_add E t (0 : ↥Λ) 0
    rw [add_zero] at h2
    have : actHom E t (0 : ↥Λ) = 0 := by
      have := congrArg (fun f => f - actHom E t (0 : ↥Λ)) h2
      simp only [sub_self, add_sub_cancel_right] at this
      exact this.symm
    rw [this]; rfl
  | succ n ih =>
    have hn' : ((n : ℚ) : ℍ[ℚ, a, b]) ∈ Λ := natCast_mem hΛ n
    have e : (⟨(((n + 1 : ℕ) : ℚ) : ℍ[ℚ, a, b]), hn⟩ : ↥Λ) = ⟨((n : ℚ) : ℍ[ℚ, a, b]), hn'⟩ + ⟨1, hΛ.one_mem⟩ := by
      apply Subtype.ext; push_cast; rfl
    rw [e, actHom_add, AddMonoidHom.add_apply, ih hn', actHom_one, AddMonoidHom.id_apply, succ_nsmul]

end Pts
p2m_reactivate "P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_exists_pushPt_act_ne_one_of_dvd_nrd_of_eq_or_eq.CerednikDrinfeld.QM.FakeEllipticCurve.Pts"

def TorsPts (E : FakeEllipticCurve Λ N S) {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of S)) (n : ℕ) :
    AddSubgroup (Pts E t) where
  carrier := {P | nsmulPt E.L t n P = E.L.one t}
  zero_mem' := by
    change n • (0 : Pts E t) = 0
    exact nsmul_zero n
  add_mem' {P Q} hP hQ := by
    change n • P = 0 at hP
    change n • Q = 0 at hQ
    change n • (P + Q) = 0
    rw [nsmul_add, hP, hQ, add_zero]
  neg_mem' {P} hP := by
    change n • P = 0 at hP
    change n • (-P) = 0
    rw [neg_nsmul, hP, neg_zero]

namespace TorsPts

variable (E : FakeEllipticCurve Λ N S) {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of S)) (n : ℕ)

theorem mem_iff (P : Pts E t) : P ∈ TorsPts E t n ↔ nsmulPt E.L t n P = E.L.one t := Iff.rfl

theorem mem_iff_nsmul_eq_zero (P : Pts E t) : P ∈ TorsPts E t n ↔ n • P = 0 := Iff.rfl

def equivSubtype : ↥(TorsPts E t n) ≃ {P : SchemeHomOver t E.f // nsmulPt E.L t n P = E.L.one t} := Equiv.refl _

theorem natCard_eq :
    Nat.card ↥(TorsPts E t n) = Nat.card {P : SchemeHomOver t E.f // nsmulPt E.L t n P = E.L.one t} := rfl

theorem nsmul_eq_zero (P : ↥(TorsPts E t n)) : n • P = 0 := by
  apply Subtype.ext
  rw [AddSubgroup.coe_nsmul, AddSubgroup.coe_zero]
  exact (mem_iff_nsmul_eq_zero E t n P.1).1 P.2

theorem actHom_mem (m : ↥Λ) {P : Pts E t} (hP : P ∈ TorsPts E t n) : Pts.actHom E t m P ∈ TorsPts E t n := by
  rw [mem_iff_nsmul_eq_zero] at hP ⊢
  rw [← map_nsmul, hP, map_zero]

def torsAct (m : ↥Λ) : ↥(TorsPts E t n) →+ ↥(TorsPts E t n) :=
  ((Pts.actHom E t m).comp (TorsPts E t n).subtype).codRestrict (TorsPts E t n)
    (fun P => actHom_mem E t n m P.2)

@[scoped simp] theorem coe_torsAct (m : ↥Λ) (P : ↥(TorsPts E t n)) :
    ((torsAct E t n m P) : Pts E t) = Pts.actHom E t m P := rfl

theorem torsAct_apply_coe_coe (m : ↥Λ) (P : ↥(TorsPts E t n)) :
    (Pts.val E t (torsAct E t n m P)).1 = (Pts.val E t (P : Pts E t)).1 ≫ E.act m := rfl

theorem val_torsAct (m : ↥Λ) (P : ↥(TorsPts E t n)) :
    Pts.val E t (torsAct E t n m P) = pushPt (E.act m) (E.act_over m) (Pts.val E t (P : Pts E t)) := rfl

theorem torsAct_one (h : (1 : ℍ[ℚ, a, b]) ∈ Λ) : torsAct E t n ⟨1, h⟩ = AddMonoidHom.id _ := by
  ext P; apply Subtype.ext
  rw [coe_torsAct, Pts.actHom_one]; rfl

theorem torsAct_mul (x y : ↥Λ) (h : (x : ℍ[ℚ, a, b]) * (y : ℍ[ℚ, a, b]) ∈ Λ) :
    torsAct E t n ⟨(x : ℍ[ℚ, a, b]) * (y : ℍ[ℚ, a, b]), h⟩ = (torsAct E t n x).comp (torsAct E t n y) := by
  ext P; apply Subtype.ext
  rw [coe_torsAct, Pts.actHom_mul]; rfl

theorem torsAct_add (x y : ↥Λ) : torsAct E t n (x + y) = torsAct E t n x + torsAct E t n y := by
  ext P; apply Subtype.ext
  rw [coe_torsAct, Pts.actHom_add]; rfl

theorem torsAct_natCast (hΛ : IsOrder Λ) (m : ℕ) (hm : ((m : ℚ) : ℍ[ℚ, a, b]) ∈ Λ) (P : ↥(TorsPts E t n)) :
    torsAct E t n ⟨((m : ℚ) : ℍ[ℚ, a, b]), hm⟩ P = m • P := by
  apply Subtype.ext
  rw [coe_torsAct, Pts.actHom_natCast E t hΛ m hm, AddSubgroup.coe_nsmul]

theorem torsAct_self_eq_zero (hΛ : IsOrder Λ) (hn : ((n : ℚ) : ℍ[ℚ, a, b]) ∈ Λ) :
    torsAct E t n ⟨((n : ℚ) : ℍ[ℚ, a, b]), hn⟩ = 0 := by
  ext P
  rw [torsAct_natCast E t n hΛ n hn, nsmul_eq_zero]; rfl

theorem torsAct_eq_zero_of_eq_natCast_mul (hΛ : IsOrder Λ) (m m' : ↥Λ)
    (h : (m : ℍ[ℚ, a, b]) = ((n : ℚ) : ℍ[ℚ, a, b]) * (m' : ℍ[ℚ, a, b])) : torsAct E t n m = 0 := by
  have hn : ((n : ℚ) : ℍ[ℚ, a, b]) ∈ Λ := Pts.natCast_mem hΛ n
  obtain ⟨mv, hmv⟩ := m
  change mv = ((n : ℚ) : ℍ[ℚ, a, b]) * (m' : ℍ[ℚ, a, b]) at h
  subst h
  rw [torsAct_mul E t n ⟨_, hn⟩ m' hmv, torsAct_self_eq_zero E t n hΛ hn, AddMonoidHom.zero_comp]

end TorsPts
p2m_reactivate "P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_exists_pushPt_act_ne_one_of_dvd_nrd_of_eq_or_eq.CerednikDrinfeld.QM.FakeEllipticCurve.Pts P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_exists_pushPt_act_ne_one_of_dvd_nrd_of_eq_or_eq.CerednikDrinfeld.QM.FakeEllipticCurve.TorsPts"

end CerednikDrinfeld.QM.FakeEllipticCurve
p2m_reactivate "P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_exists_pushPt_act_ne_one_of_dvd_nrd_of_eq_or_eq.CerednikDrinfeld.QM.FakeEllipticCurve.Pts P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_exists_pushPt_act_ne_one_of_dvd_nrd_of_eq_or_eq.CerednikDrinfeld.QM.FakeEllipticCurve.TorsPts P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_exists_pushPt_act_ne_one_of_dvd_nrd_of_eq_or_eq.CerednikDrinfeld P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_exists_pushPt_act_ne_one_of_dvd_nrd_of_eq_or_eq.CerednikDrinfeld.QM P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_exists_pushPt_act_ne_one_of_dvd_nrd_of_eq_or_eq.CerednikDrinfeld.QM.FakeEllipticCurve"
p2m_reactivate "P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_exists_pushPt_act_ne_one_of_dvd_nrd_of_eq_or_eq.CerednikDrinfeld.QM.FakeEllipticCurve.Pts P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_exists_pushPt_act_ne_one_of_dvd_nrd_of_eq_or_eq.CerednikDrinfeld.QM.FakeEllipticCurve.TorsPts P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_exists_pushPt_act_ne_one_of_dvd_nrd_of_eq_or_eq.CerednikDrinfeld P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_exists_pushPt_act_ne_one_of_dvd_nrd_of_eq_or_eq.CerednikDrinfeld.QM"
p2m_reactivate "P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_exists_pushPt_act_ne_one_of_dvd_nrd_of_eq_or_eq.CerednikDrinfeld.QM.FakeEllipticCurve.Pts P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_exists_pushPt_act_ne_one_of_dvd_nrd_of_eq_or_eq.CerednikDrinfeld.QM.FakeEllipticCurve.TorsPts P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_exists_pushPt_act_ne_one_of_dvd_nrd_of_eq_or_eq.CerednikDrinfeld"

namespace Hfaith8

p2m_open "CerednikDrinfeld.QM.FakeEllipticCurve P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_exists_pushPt_act_ne_one_of_dvd_nrd_of_eq_or_eq.CerednikDrinfeld.QM.FakeEllipticCurve"

section arith

variable {a b : ℚ}

theorem nrd_zsmul (c : ℤ) (y : ℍ[ℚ, a, b]) : nrd (c • y) = (c : ℚ) ^ 2 * nrd y := by
  rw [zsmul_eq_mul, QuaternionAlgebra.nrd_mul]
  congr 1
  have : ((c : ℤ) : ℍ[ℚ, a, b]) = (((c : ℚ)) : ℍ[ℚ, a, b]) := by norm_cast
  rw [this, nrd_coe]

theorem not_dvd_nrd_of_sq {r : ℕ} (hr : r.Prime) {x y : ℍ[ℚ, a, b]} {n₀ : ℤ} (hn₀ : nrd x = (r : ℚ) * n₀)
    (hnsq : ¬ ∃ n : ℤ, nrd x = (r : ℚ) ^ 2 * n) (hxy : x * x = (r : ℤ) • y) :
    ¬ ∃ m : ℤ, nrd y = (r : ℚ) * m := by
  rintro ⟨m, hm⟩
  have hr0 : (r : ℚ) ≠ 0 := by exact_mod_cast hr.ne_zero
  have h1 : nrd (x * x) = nrd ((r : ℤ) • y) := by rw [hxy]
  rw [QuaternionAlgebra.nrd_mul, nrd_zsmul, hn₀, hm] at h1

  have h2 : ((n₀ : ℤ) : ℚ) * n₀ = (r : ℚ) * m := by
    have : ((r : ℤ) : ℚ) = (r : ℚ) := by norm_cast
    rw [this] at h1
    field_simp at h1
    linear_combination h1
  have h3 : n₀ * n₀ = (r : ℤ) * m := by exact_mod_cast h2
  have h4 : (r : ℤ) ∣ n₀ * n₀ := ⟨m, h3⟩
  have hpr : Prime (r : ℤ) := Nat.prime_iff_prime_int.mp hr
  obtain ⟨k, hk⟩ : (r : ℤ) ∣ n₀ := by
    rcases hpr.dvd_or_dvd h4 with h | h <;> exact h
  exact hnsq ⟨k, by rw [hn₀, hk]; push_cast; ring⟩

end arith
p2m_reactivate "P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_exists_pushPt_act_ne_one_of_dvd_nrd_of_eq_or_eq.CerednikDrinfeld.QM.FakeEllipticCurve.Pts P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_exists_pushPt_act_ne_one_of_dvd_nrd_of_eq_or_eq.CerednikDrinfeld.QM.FakeEllipticCurve.TorsPts P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_exists_pushPt_act_ne_one_of_dvd_nrd_of_eq_or_eq.CerednikDrinfeld P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_exists_pushPt_act_ne_one_of_dvd_nrd_of_eq_or_eq.CerednikDrinfeld.QM P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_exists_pushPt_act_ne_one_of_dvd_nrd_of_eq_or_eq.CerednikDrinfeld.QM.FakeEllipticCurve"

variable {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} {N : ℕ}

noncomputable def actHomHom {S : Type u} [CommRing S] (E : FakeEllipticCurve Λ N S) {T : Scheme.{u}}
    (t : T ⟶ Spec (CommRingCat.of S)) : ↥Λ →+ (Pts E t →+ Pts E t) :=
  AddMonoidHom.mk' (Pts.actHom E t) (Pts.actHom_add E t)

@[scoped simp] theorem actHomHom_apply {S : Type u} [CommRing S] (E : FakeEllipticCurve Λ N S) {T : Scheme.{u}}
    (t : T ⟶ Spec (CommRingCat.of S)) (m : ↥Λ) : actHomHom E t m = Pts.actHom E t m := rfl

theorem actHom_nsmul_apply {S : Type u} [CommRing S] (E : FakeEllipticCurve Λ N S) {T : Scheme.{u}}
    (t : T ⟶ Spec (CommRingCat.of S)) (c : ℕ) (m : ↥Λ) (P : Pts E t) :
    Pts.actHom E t (c • m) P = Pts.actHom E t m (c • P) := by
  rw [map_nsmul]
  induction c with
  | zero =>
    have h0 : Pts.actHom E t 0 = 0 := (actHomHom E t).map_zero
    rw [zero_nsmul, zero_nsmul, h0, AddMonoidHom.zero_apply]
  | succ c ih => rw [succ_nsmul, succ_nsmul, Pts.actHom_add, AddMonoidHom.add_apply, ih]

theorem natCard_torsPts (K : Type u) [Field K] [IsAlgClosed K] (E : FakeEllipticCurve Λ N K) (n : ℕ)
    (hn : (n : K) ≠ 0) : Nat.card ↥(TorsPts E (𝟙 (Spec (CommRingCat.of K))) n) = n ^ 4 := by
  haveI : SmoothOfRelativeDimension 2 E.f := CerednikDrinfeld.QM.FakeEllipticCurve.smoothOfRelativeDimension_two K E
  have h := GoodReductionJacobian.RelativeGroupLaw.natCard_isTorsionPoint_eq_pow_of_natCast_ne_zero K E.f E.L
    E.comm E.bundle 2 n hn
  rw [TorsPts.natCard_eq]
  have hns : ∀ (P : SchemeHomOver (𝟙 (Spec (CommRingCat.of K))) E.f) (m : ℕ),
      nsmulPt E.L (𝟙 (Spec (CommRingCat.of K))) m P = E.L.nsmul (𝟙 (Spec (CommRingCat.of K))) m P := by
    intro P m
    induction m with
    | zero => rfl
    | succ m ih => rw [RelativeGroupLaw.nsmul_succ, ← ih]; rfl
  have e : {P : SchemeHomOver (𝟙 (Spec (CommRingCat.of K))) E.f //
      nsmulPt E.L (𝟙 (Spec (CommRingCat.of K))) n P = E.L.one (𝟙 (Spec (CommRingCat.of K)))} ≃
      {x : SchemeHomOver (𝟙 (Spec (CommRingCat.of K))) E.f // E.L.IsTorsionPoint (𝟙 (Spec (CommRingCat.of K))) n x} :=
    Equiv.subtypeEquivRight (fun P => by rw [RelativeGroupLaw.isTorsionPoint_def, hns])
  rw [Nat.card_congr e, h]

theorem faithful_raw {q q' : ℕ} [Fact q.Prime] [Fact q'.Prime] (hB : IsIndefiniteRamifiedExactlyAt a b q q')
    (Λ : Submodule ℤ ℍ[ℚ, a, b]) (hΛ : IsMaximalOrder Λ) {N : ℕ}
    (K : Type) [Field K] [IsAlgClosed K] (E : FakeEllipticCurve Λ N K)
    (r : ℕ) (hr : r = q ∨ r = q') (hrK : (r : K) ≠ 0) :
    ∃ (P : SchemeHomOver (𝟙 (Spec (CommRingCat.of K))) E.f) (x : ↥Λ),
      nsmulPt E.L (𝟙 (Spec (CommRingCat.of K))) r P = E.L.one (𝟙 (Spec (CommRingCat.of K))) ∧
      (∃ n : ℤ, nrd (x : ℍ[ℚ, a, b]) = (r : ℚ) * n) ∧
      pushPt (E.act x) (E.act_over x) P ≠ E.L.one (𝟙 (Spec (CommRingCat.of K))) := by
  classical
  have hrp : r.Prime := by rcases hr with rfl | rfl <;> exact Fact.out
  have hO : IsOrder Λ := hΛ.isOrder
  by_contra H
  push Not at H

  let t := 𝟙 (Spec (CommRingCat.of K))
  let G := Pts E t
  let ρ : ↥Λ → G →+ G := Pts.actHom E t
  let W : ℕ → AddSubgroup G := fun n => TorsPts E t n

  have hkill : ∀ (x : ℍ[ℚ, a, b]) (hx : x ∈ Λ), (∃ n : ℤ, nrd x = (r : ℚ) * n) →
      ∀ Q : G, Q ∈ W r → ρ ⟨x, hx⟩ Q = 0 := fun x hx hn Q hQ => H Q ⟨x, hx⟩ hQ hn

  have hcard1 : Nat.card ↥(W r) = r ^ 4 := natCard_torsPts K E r hrK
  have hrrK : ((r * r : ℕ) : K) ≠ 0 := by push_cast; exact mul_ne_zero hrK hrK
  have hcard2 : Nat.card ↥(W (r * r)) = (r * r) ^ 4 := natCard_torsPts K E (r * r) hrrK
  haveI : Finite ↥(W r) := Nat.finite_of_card_ne_zero (by rw [hcard1]; exact pow_ne_zero _ hrp.ne_zero)
  haveI : Finite ↥(W (r * r)) :=
    Nat.finite_of_card_ne_zero (by rw [hcard2]; exact pow_ne_zero _ (mul_ne_zero hrp.ne_zero hrp.ne_zero))

  obtain ⟨x, hxΛ, ⟨n₀, hn₀⟩, hnsq⟩ :=
    QuaternionAlgebra.IsMaximalOrder.exists_mem_dvd_nrd_not_sq_dvd_nrd_of_isIndefiniteRamifiedExactlyAt hB Λ hΛ r hr
  obtain ⟨y, hyΛ, hxy⟩ :=
    QuaternionAlgebra.IsMaximalOrder.exists_mul_eq_natCast_smul_of_dvd_nrd_of_dvd_nrd_of_isIndefiniteRamifiedExactlyAt
      hB Λ hΛ r hr x hxΛ x hxΛ ⟨n₀, hn₀⟩ ⟨n₀, hn₀⟩
  have hy_not : ¬ ∃ m : ℤ, nrd y = (r : ℚ) * m := not_dvd_nrd_of_sq hrp hn₀ hnsq hxy

  have hxx : (⟨x * x, hO.mul_mem hxΛ hxΛ⟩ : ↥Λ) = r • ⟨y, hyΛ⟩ := by
    apply Subtype.ext
    show x * x = ((r • ⟨y, hyΛ⟩ : ↥Λ) : ℍ[ℚ, a, b])
    rw [hxy]
    simp
  have hy2 : ∀ P : G, P ∈ W (r * r) → ρ ⟨y, hyΛ⟩ (r • P) = 0 := by
    intro P hP
    have hrP : r • P ∈ W r := by
      rw [TorsPts.mem_iff_nsmul_eq_zero, smul_smul]; exact (TorsPts.mem_iff_nsmul_eq_zero E t _ P).1 hP
    have h1 : ρ ⟨x, hxΛ⟩ (r • P) = 0 := hkill x hxΛ ⟨n₀, hn₀⟩ _ hrP
    have h2 : ρ ⟨x, hxΛ⟩ P ∈ W r := by
      rw [TorsPts.mem_iff_nsmul_eq_zero, ← map_nsmul]; exact h1
    have h3 : ρ ⟨x, hxΛ⟩ (ρ ⟨x, hxΛ⟩ P) = 0 := hkill x hxΛ ⟨n₀, hn₀⟩ _ h2
    have h4 : ρ ⟨x * x, hO.mul_mem hxΛ hxΛ⟩ P = 0 := by
      show Pts.actHom E t ⟨x * x, hO.mul_mem hxΛ hxΛ⟩ P = 0
      rw [Pts.actHom_mul E t ⟨x, hxΛ⟩ ⟨x, hxΛ⟩ (hO.mul_mem hxΛ hxΛ)]; exact h3
    rw [hxx] at h4
    rwa [actHom_nsmul_apply] at h4

  let d : ↥(W (r * r)) →+ ↥(W r) :=
    { toFun := fun P => ⟨r • (P : G), by
        rw [TorsPts.mem_iff_nsmul_eq_zero, smul_smul]; exact (TorsPts.mem_iff_nsmul_eq_zero E t _ P.1).1 P.2⟩
      map_zero' := by apply Subtype.ext; simp
      map_add' := fun P Q => by apply Subtype.ext; simp }
  have hd : ∀ P : ↥(W (r * r)), ((d P : ↥(W r)) : G) = r • (P : G) := fun P => rfl
  have hker_le : Nat.card ↥d.ker ≤ Nat.card ↥(W r) := by
    refine Nat.card_le_card_of_injective (fun P : ↥d.ker => (⟨((P : ↥(W (r * r))) : G), ?_⟩ : ↥(W r))) ?_
    · rw [TorsPts.mem_iff_nsmul_eq_zero, ← hd]
      have := P.2
      rw [AddMonoidHom.mem_ker] at this
      rw [this]; rfl
    · intro P Q h
      dsimp only at h
      have h' := congrArg Subtype.val h
      dsimp only at h'
      exact Subtype.ext (Subtype.ext h')
  have hrange_le : Nat.card ↥d.range ≤ Nat.card ↥(W r) :=
    Nat.card_le_card_of_injective (fun P : ↥d.range => (P : ↥(W r))) Subtype.val_injective
  have hprod : Nat.card ↥(W (r * r)) = Nat.card ↥d.range * Nat.card ↥d.ker := by
    rw [AddSubgroup.card_eq_card_quotient_mul_card_addSubgroup d.ker,
      Nat.card_congr (QuotientAddGroup.quotientKerEquivRange d).toEquiv]
  have hr4 : 0 < r ^ 4 := pow_pos hrp.pos 4
  have hrange : Nat.card ↥d.range = Nat.card ↥(W r) := by
    rw [hcard1] at hker_le hrange_le ⊢
    rw [hcard2] at hprod
    have : (r * r) ^ 4 = r ^ 4 * r ^ 4 := by ring
    rw [this] at hprod
    nlinarith
  haveI : Finite ↥d.range := Nat.finite_of_card_ne_zero (by rw [hrange, hcard1]; exact hr4.ne')
  have hsurj : Function.Surjective d := AddMonoidHom.range_eq_top.mp (AddSubgroup.eq_top_of_card_eq _ hrange)

  have hyW : ∀ Q : G, Q ∈ W r → ρ ⟨y, hyΛ⟩ Q = 0 := by
    intro Q hQ
    obtain ⟨P, hP⟩ := hsurj ⟨Q, hQ⟩
    have : Q = r • (P : G) := by rw [← hd, hP]
    rw [this]; exact hy2 P P.2

  let J₀ : AddSubgroup ℍ[ℚ, a, b] :=
    { carrier := {m | ∃ hm : m ∈ Λ, ∀ Q : G, Q ∈ W r → ρ ⟨m, hm⟩ Q = 0}
      zero_mem' := ⟨Λ.zero_mem, fun Q _ => by
        have h0 : Pts.actHom E t 0 = 0 := (actHomHom E t).map_zero
        show Pts.actHom E t ⟨0, Λ.zero_mem⟩ Q = 0
        rw [show (⟨0, Λ.zero_mem⟩ : ↥Λ) = 0 from rfl, h0, AddMonoidHom.zero_apply]⟩
      add_mem' := fun {m m'} ⟨hm, h⟩ ⟨hm', h'⟩ => ⟨Λ.add_mem hm hm', fun Q hQ => by
        show Pts.actHom E t ⟨m + m', Λ.add_mem hm hm'⟩ Q = 0
        rw [show (⟨m + m', Λ.add_mem hm hm'⟩ : ↥Λ) = ⟨m, hm⟩ + ⟨m', hm'⟩ from rfl, Pts.actHom_add,
          AddMonoidHom.add_apply, h Q hQ, h' Q hQ, add_zero]⟩
      neg_mem' := fun {m} ⟨hm, h⟩ => ⟨Λ.neg_mem hm, fun Q hQ => by
        show Pts.actHom E t ⟨-m, Λ.neg_mem hm⟩ Q = 0
        rw [show (⟨-m, Λ.neg_mem hm⟩ : ↥Λ) = -⟨m, hm⟩ from rfl, ← actHomHom_apply, map_neg,
          AddMonoidHom.neg_apply, actHomHom_apply, h Q hQ, neg_zero]⟩ }
  let J : Submodule ℤ ℍ[ℚ, a, b] := AddSubgroup.toIntSubmodule J₀
  have hJmem : ∀ m, m ∈ J ↔ ∃ hm : m ∈ Λ, ∀ Q : G, Q ∈ W r → ρ ⟨m, hm⟩ Q = 0 := fun m => Iff.rfl
  have hJle : J ≤ Λ := fun m hm => ((hJmem m).1 hm).1
  have hJr : ∀ w ∈ Λ, (r : ℤ) • w ∈ J := fun w hw => (hJmem _).2 ⟨Λ.smul_mem _ hw, fun Q hQ => by
      have e1 : (⟨(r : ℤ) • w, Λ.smul_mem _ hw⟩ : ↥Λ) = r • ⟨w, hw⟩ := by apply Subtype.ext; simp
      show Pts.actHom E t ⟨(r : ℤ) • w, Λ.smul_mem _ hw⟩ Q = 0
      rw [e1, actHom_nsmul_apply, (TorsPts.mem_iff_nsmul_eq_zero E t r Q).1 hQ, map_zero]⟩
  have hJstab : ∀ m ∈ Λ, ∀ z ∈ J, m * z ∈ J := fun m hm z hz => by
      obtain ⟨hzΛ, hz'⟩ := (hJmem z).1 hz
      exact (hJmem _).2 ⟨hO.mul_mem hm hzΛ, fun Q hQ => by
        show Pts.actHom E t ⟨m * z, hO.mul_mem hm hzΛ⟩ Q = 0
        rw [Pts.actHom_mul E t ⟨m, hm⟩ ⟨z, hzΛ⟩ (hO.mul_mem hm hzΛ), AddMonoidHom.comp_apply, hz' Q hQ, map_zero]⟩
  obtain ⟨⟨-, -, ⟨x₁, hx₁Λ, hx₁P, hx₁not⟩, -, -⟩, htri⟩ :=
    QuaternionAlgebra.IsMaximalOrder.leftIdeal_eq_or_eq_or_eq_of_isIndefiniteRamifiedExactlyAt_of_eq_or_eq hB Λ hΛ r hr
  rcases htri J hJle hJr hJstab with h | h | h
  · exact hx₁not ((h x₁).1 ((hJmem x₁).2 ⟨hx₁Λ, hkill x₁ hx₁Λ hx₁P⟩))
  · exact hy_not ((h y).1 ((hJmem y).2 ⟨hyΛ, hyW⟩)).2
  · have h1 : (1 : ℍ[ℚ, a, b]) ∈ J := by rw [h]; exact hO.one_mem
    obtain ⟨h1Λ, hk⟩ := (hJmem 1).1 h1
    have hsub : ∀ Q : ↥(W r), Q = 0 := fun Q => by
      apply Subtype.ext
      have := hk Q.1 Q.2
      rw [show (ρ ⟨1, h1Λ⟩) = Pts.actHom E t ⟨1, h1Λ⟩ from rfl, Pts.actHom_one E t h1Λ] at this
      exact this
    have hone : Nat.card ↥(W r) = 1 := by
      rw [Nat.card_eq_one_iff_unique]; exact ⟨⟨fun P Q => by rw [hsub P, hsub Q]⟩, ⟨0⟩⟩
    rw [hcard1] at hone
    have : 1 < r ^ 4 := Nat.one_lt_pow (by norm_num) hrp.one_lt
    omega

end Hfaith8
p2m_reactivate "P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_exists_pushPt_act_ne_one_of_dvd_nrd_of_eq_or_eq.CerednikDrinfeld.QM.FakeEllipticCurve.Pts P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_exists_pushPt_act_ne_one_of_dvd_nrd_of_eq_or_eq.CerednikDrinfeld.QM.FakeEllipticCurve.TorsPts P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_exists_pushPt_act_ne_one_of_dvd_nrd_of_eq_or_eq.CerednikDrinfeld P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_exists_pushPt_act_ne_one_of_dvd_nrd_of_eq_or_eq.CerednikDrinfeld.QM P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_exists_pushPt_act_ne_one_of_dvd_nrd_of_eq_or_eq.CerednikDrinfeld.QM.FakeEllipticCurve P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_exists_pushPt_act_ne_one_of_dvd_nrd_of_eq_or_eq.Hfaith8"

theorem solution
    {a b : ℚ} {q q' : ℕ} [Fact q.Prime] [Fact q'.Prime] (hB : IsIndefiniteRamifiedExactlyAt a b q q')
    (Λ : Submodule ℤ ℍ[ℚ, a, b]) (hΛ : IsMaximalOrder Λ) {N : ℕ}
    (K : Type) [Field K] [IsAlgClosed K] (E : FakeEllipticCurve Λ N K)
    (r : ℕ) (hr : r = q ∨ r = q') (hrK : (r : K) ≠ 0) :
    ∃ (P : SchemeHomOver (𝟙 (Spec (CommRingCat.of K))) E.f) (x : ↥Λ),
      nsmulPt E.L (𝟙 (Spec (CommRingCat.of K))) r P = E.L.one (𝟙 (Spec (CommRingCat.of K))) ∧
      (∃ n : ℤ, nrd (x : ℍ[ℚ, a, b]) = (r : ℚ) * n) ∧
      pushPt (E.act x) (E.act_over x) P ≠ E.L.one (𝟙 (Spec (CommRingCat.of K))) := by
  exact Hfaith8.faithful_raw hB Λ hΛ K E r hr hrK

end S_CerednikDrinfeld_QM_FakeEllipticCurve_exists_pushPt_act_ne_one_of_dvd_nrd_of_eq_or_eq
end P2MW
export P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_exists_pushPt_act_ne_one_of_dvd_nrd_of_eq_or_eq (solution)
