-- Prove2me | solution 1 for CerednikDrinfeld.QM.FakeEllipticCurve.isAtkinLehnerQuotient_of_quotients_of_card_eq_mul_sq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.141142+00:00
-- url     : https://prove2.me/submissions/2da462c6-55ee-522e-8e2e-a65faa011e2d

import Mathlib
import Definitions.Def_CerednikDrinfeld_QMModuliProps
import Definitions.Def_CerednikDrinfeld_QMFineModuli
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawKernel
import Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_exists_comp_eq_act_comp_of_quotients
import Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_natCard_setOf_forall_pushPt_act_eq_one_of_eq_or_eq
import Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_eq_of_nsmulPt_eq_one_of_forall_comp_eq
import Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_existsUnique_sectionAt_eq_of_nsmulPt_eq_one
import Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_pushPt_act_natCast_eq_nsmulPt
import Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_isFinite_and_etale_schemeKerStr_of_isUnit
import Theorems.Thm_AlgebraicGeometry_isClopen_preimage_diagonal_of_formallyUnramified_of_isSeparated
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_isAtkinLehnerQuotient_of_quotients_of_card_eq_mul_sq
p2m_attr_erase "instance" "GoodReductionJacobian.RelativeGroupLaw.isIso_endKerStr_schemeHomOverId AlgebraicGeometry.Scheme.PresheafOfModules.symmetricCategory SheafOfModules.instFaithfulRingSheafPModToPMod SheafOfModules.symmetricCategory AlgebraicGeometry.Scheme.PresheafOfModules.monoidalCategory AlgebraicGeometry.Scheme.PresheafOfModules.monoidalClosed SheafOfModules.instFullRingSheafPModToPMod SheafOfModules.monoidalCategory AlgebraicGeometry.Scheme.Modules.symmetricCategory SheafOfModules.monoidalClosed SheafOfModules.instIsLocalizationPModRingSheafSheafifyFunctorPresheafW SheafOfModules.sheafifyFunctor_monoidal AlgebraicGeometry.Scheme.Modules.monoidalClosed AlgebraicGeometry.instMonoidalPresheafOfModulesModulesSheafify AlgebraicGeometry.Scheme.Modules.monoidalCategory PresheafOfModules.instMonoidalClosed PresheafOfModules.InternalHom.instModuleCarrierObjOppositeCommRingCatSubtypePiFamilyMemAddSubgroupNaturalFamilies PresheafOfModules.InternalHom.instModuleCarrierObjOppositeRingCatCompCommRingCatForget₂RingHomCarrierCarrierAbPresheaf PresheafOfModules.InternalHom.instSMulCarrierObjOppositeCommRingCatSubtypePiFamilyMemAddSubgroupNaturalFamilies AlgebraicGeometry.Scheme.Hom.opensMapFinal AlgebraicGeometry.RelPicard.RigidifiedLineBundle.setoid AlgebraicGeometry.RelPicard.RigidifiedLineBundle.instInhabited AlgebraicGeometry.OModulePresheaf.isScalarTower AlgebraicGeometry.Scheme.OrderedAffineCover.instLinearOrder AlgebraicGeometry.OModulePresheaf.module AlgebraicGeometry.Scheme.OrderedAffineCover.instFintype AlgebraicGeometry.Scheme.OrderedAffineCover.instFintypeIdx AlgebraicGeometry.OModulePresheaf.addCommGroup AlgebraicGeometry.Scheme.OrderedAffineCover.instDecidableEqIdx AlgebraicGeometry.OModulePresheaf.moduleSections TwoChartCech.Sections.M0_moduleA TwoChartCech.Sections.M1_module TwoChartCech.Cover.A01_algebra TwoChartCech.Cover.A0_algebra TwoChartCech.Cover.A1_commRing TwoChartCech.Cover.A1_algebra TwoChartCech.Sections.M01_module TwoChartCech.Sections.M0_addCommGroup TwoChartCech.Sections.M0_tower TwoChartCech.Sections.M01_addCommGroup"
p2m_attr_erase "instance" "TwoChartCech.Cover.A0_commRing TwoChartCech.Sections.M1_tower TwoChartCech.Sections.M01_moduleA TwoChartCech.Sections.M0_module TwoChartCech.Sections.M1_moduleA TwoChartCech.Sections.M1_addCommGroup TwoChartCech.Cover.A01_commRing TwoChartCech.Sections.M01_tower CoherentBaseChange.TwoTermComplex.C0_module CoherentBaseChange.TwoTermComplex.C0_addCommGroup CoherentBaseChange.TwoTermComplex.C1_module CoherentBaseChange.TwoTermComplex.C1_addCommGroup CoherentBaseChange.TwoTermComplex.C0_free CoherentBaseChange.TwoTermComplex.C1_finite CoherentBaseChange.TwoTermComplex.C0_finite CoherentBaseChange.TwoTermComplex.C1_free AlgebraicGeometry.OModulePresheaf.instSubsingletonObjZero AlgebraicGeometry.Scheme.Modules.preservesBinaryProducts_opensMap AlgebraicGeometry.Scheme.Modules.pullback_monoidal AlgebraicGeometry.Scheme.Modules.sheafify_isLocalization' AlgebraicGeometry.Scheme.Modules.preservesTerminal_opensMap AlgebraicGeometry.Scheme.Modules.pullback₀_monoidal AlgebraicGeometry.Scheme.Modules.preservesFiniteProducts_opensMap AlgebraicGeometry.Scheme.Modules.instLiftingPresheafOfModulesSheafifyPresheafWOpensCarrierCarrierCommRingCatGrothendieckTopologyObjFunctorOppositeIsSheafSheafCompPullback₀Pullback PresheafOfModules.PullbackMonoidal.pullback_monoidal PresheafOfModules.PullbackMonoidal.isIso_δ PresheafOfModules.pushforward_laxMonoidal PresheafOfModules.PullbackMonoidal.isIso_η PresheafOfModules.free_monoidal PresheafOfModules.restrictScalars_laxMonoidal PresheafOfModules.PullbackMonoidal.isIso_δ_gS PresheafOfModules.pullback_oplaxMonoidal PresheafOfModules.PullbackMonoidal.instPreservesColimitsOfSizeCompOppositeCommRingCatRingCatForget₂RingHomCarrierCarrierPb PresheafOfModules.pullback_monoidal' AlgebraicGeometry.SmoothOfRelativeDimension.fiberToSpecResidueField AlgebraicGeometry.SmoothOfRelativeDimension.pullback_snd AlgebraicGeometry.SmoothOfRelativeDimension.pullback_fst AlgebraicGeometry.SmoothOfRelativeDimension.smooth_one AlgebraicGeometry.SmoothProperCurve.isIntegral_pullback_Spec_field AlgebraicGeometry.IsProper.fiberToSpecResidueField"
p2m_attr_erase "instance" "AlgebraicCurve.CurveModel.isProper AlgebraicCurve.CurveModel.isIntegral AlgebraicCurve.CurveModel.smooth AlgebraicGeometry.Scheme.LocalRepresentabilityULift.instIsLocallyInjectiveFunUliftYonedaGluedToSheaf AlgebraicGeometry.Scheme.LocalRepresentabilityULift.instIsLocallySurjectiveFunUliftYonedaGluedToSheafOfIsLocallySurjectiveZariskiTopologyDescFunctorOppositeType AlgebraicGeometry.Scheme.LocalRepresentabilityULift.instIsOpenImmersionToGlued AlgebraicGeometry.Scheme.LocalRepresentabilityULift.instIsIsoSheafZariskiTopologyTypeUliftYonedaGluedToSheaf AlgebraicGeometry.RelPicard.instIsOpenImmersionToGlued AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.instFundamentalIdentityOfSumRamificationInertia AlgebraicCurve.Place.instIsScalarTowerResidueFieldRestrictPushforward AlgebraicCurve.Place.instAlgebraResidueFieldRestrictPushforward AlgebraicCurve.Place.instIsLocalHomRestrictInclusion AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions PresheafOfModules.ExteriorPower.instModulePresheafAb AlgebraicGeometry.RelEffCartierDiv.subsingleton_of_degree_zero AlgebraicGeometry.RelEffCartierDiv.isIso_subschemeIota_snd_of_degree_one AlgebraicGeometry.isIso_ker_graphOver_subschemeIota_snd AlgebraicGeometry.isClosedImmersion_graphOver AlgebraicGeometry.FGSubalgebra.instIsDirectedLe AlgebraicGeometry.FGSubalgebra.instQuasiSeparatedSpaceCarrierCarrierCommRingCatObjOppositeSchemeSpecDiagram AlgebraicGeometry.FGSubalgebra.instIsCofilteredOpposite AlgebraicGeometry.FGSubalgebra.instIsAffineObjOppositeSchemeSpecDiagram AlgebraicGeometry.FGSubalgebra.instNonempty AlgebraicGeometry.FGSubalgebra.instNonemptySubtypeLeSubalgebraValFG AlgebraicGeometry.FGSubalgebra.instCompactSpaceCarrierCarrierCommRingCatObjOppositeSchemeSpecDiagram AlgebraicGeometry.FGSubalgebra.instIsDirectedSubtypeLeSubalgebraValFG AlgebraicGeometry.FGSubalgebra.instIsAffineHomMapOppositeSchemeSpecDiagram AlgebraicGeometry.FGSubalgebra.instIsFiltered AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instNeg AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instSMulInt AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instAddCommGroup AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instAdd AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instSub"
p2m_attr_erase "instance" "AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instModuleCarrierObjOppositeOpensCarrierCarrierCommRingCatPresheafOpOpensTop AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instSMulCarrierObjOppositeOpensCarrierCarrierCommRingCatPresheafOpOpensTop AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instSMulNat AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instZero AlgebraicCurve.instHasLocalResidue_of_hasCanonicalLocalResidueK AlgebraicCurve.instHasCanonicalLocalResidueK_of_hasCanonicalLocalResidueKStar AlgebraicCurve.Place.kw_ffgc_finiteDimensional_adicCompletion instAlgebraSubtypeMemValuationSubring_definitions AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersIntegersCompletion ModularCurve.KwF4gRRTate.instAlgebraKAdicCompletionIntegers AlgebraicCurve.Place.kw_ffgc_continuousSMul_adicCompletionComap AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersCompletionCompletion IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions AlgebraicCurve.instHasCanonicalLocalResidueK AlgebraicCurve.Place.instAlgebra_restrictResidueField AlgebraicCurve.Place.instIsScalarTower_restrictResidueField AlgebraicCurve.instHasLocalResidue AlgebraicCurve.HasSeparableResidue.of_perfectField_of_isCurveOver AlgebraicCurve.HasSeparableResidue.of_perfectField AlgebraicCurve.Place.instIsLocalHom_restrictSubringHom AlgebraicCurve.instHasCanonicalLocalResidueKStar ModularCurve.KwNo6Pin.isLocalRing_completion SheafOfModules.isIso_ihomModelToIhom AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instDecidableEqIdx AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instFintype AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instLinearOrder AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instFintypeIdx AlgebraicGeometry.OModulePresheaf.Leray.relAltC_scalarTower AlgebraicGeometry.OModulePresheaf.Leray.ker_relAltd_modΓ AlgebraicGeometry.OModulePresheaf.Leray.relAltC_modΓ AlgebraicGeometry.OModulePresheaf.Leray.biC_abGrp AlgebraicGeometry.OModulePresheaf.Leray.relAltH_modΓ AlgebraicGeometry.OModulePresheaf.Leray.ker_relAltd_smul AlgebraicGeometry.OModulePresheaf.Leray.relAltH_scalarTower AlgebraicGeometry.OModulePresheaf.Leray.relAltH_smul"
p2m_attr_erase "instance" "AlgebraicGeometry.OModulePresheaf.Leray.biC_module DoubleComplex.instModuleE₂I DoubleComplex.Bounded.modR DoubleComplex.instModuleE₂II DoubleComplex.instAddCommGroupE₂II DoubleComplex.Bounded.abGrp DoubleComplex.instAddCommGroupE₂I AlgebraicGeometry.ChowDatum.hι_closed AlgebraicGeometry.ChowDatumProj.hιN_closed AlgebraicGeometry.ChowDatumProj.hp_proper AlgebraicGeometry.ChowDatum.hp_isoU AlgebraicGeometry.ChowDatum.hp_proper AlgebraicGeometry.ProjSpace.algebraAway AlgebraicGeometry.ProjSpace.instIsProperProdOverπ AlgebraicGeometry.ChowDatumProj.hp_isoU AlgebraicGeometry.ProjSpace.isProper_π AlgebraicGeometry.ProjSpace.finiteType_mvPolynomial ProjSpaceCech.GradedModule.H.module ProjSpaceCech.GradedModule.H.addCommGroup ProjSpaceCech.GradedModule.sec.instAdd ProjSpaceCech.GradedModule.sec.instNeg ProjSpaceCech.GradedModule.acg ProjSpaceCech.GradedModule.Frac.setoid ProjSpaceCech.GradedModule.modR ProjSpaceCech.GradedModule.sec.instModule ProjSpaceCech.GradedModule.sec.instAddCommGroup ProjSpaceCech.GradedModule.sec.instZero ProjSpaceCech.GradedModule.Presentation.fJ ProjSpaceCech.GradedModule.sec.instSMul ProjSpaceCech.Twist.H.module ProjSpaceCech.Idx.instFintype ProjSpaceCech.Twist.H.addCommGroup ProjSpaceCech.Idx.instDecidableEq ProjSpaceCech.Twist.Mon.instDecidableEq ProjSpaceCech.Twist.cochain.instAddCommGroup ProjSpaceCech.Twist.cochain.instModule AlgebraicGeometry.FGSubalgebra.tensorStage_directedSystem AlgebraicGeometry.RelEffCartierDiv.isClosedImmersion_subschemeι_resProdMap AlgebraicGeometry.RelEffCartierDiv.isOpenImmersion_resProdMap AlgebraicCurve.CurveModel.locallyOfFiniteType_gluedToBase"
p2m_attr_erase "instance" "AlgebraicCurve.CurveModel.isFractionRing_overlap AlgebraicCurve.CurveModel.isLocallyNoetherian_glued AlgebraicCurve.CurveModel.jacobsonSpace_glued AlgebraicCurve.CurveModel.isOpenImmersion_ι₀ AlgebraicCurve.CurveModel.isIntegral_glued AlgebraicCurve.CurveModel.quasiSeparated_gluedToBase AlgebraicCurve.CurveModel.compactSpace_glued AlgebraicCurve.CurveModel.isIntegral_adjoin_chartRing AlgebraicCurve.CurveModel.isFractionRing_overlap_functionField AlgebraicCurve.CurveModel.isProper_gluedToBase AlgebraicCurve.CurveModel.isOpenImmersion_ιU AlgebraicCurve.CurveModel.isOpenImmersion_f₀ AlgebraicCurve.CurveModel.isOpenImmersion_fInf AlgebraicCurve.CurveModel.isOpenImmersion_ιInf AlgebraicCurve.CurveModel.algebra_overlap_functionField AlgebraicCurve.CurveModel.quasiCompact_gluedToBase AlgebraicCurve.CurveModel.algebraAdjoin AlgebraicCurve.CurveModel.isDedekindDomain_chartRing AlgebraicCurve.CurveModel.isIntegralClosure AlgebraicCurve.CurveModel.finite_chartRing AlgebraicCurve.CurveModel.centre_isPrime AlgebraicCurve.CurveModel.isFractionRing_chartRing AlgebraicCurve.CurveModel.finiteType_chartRing AlgebraicCurve.CurveModel.isNoetherianRing_chartRing AlgebraicCurve.CurveModel.isScalarTower_base_adjoin AlgebraicCurve.CurveModel.isScalarTower_adjoin AlgebraicCurve.CurveModel.chartRing_finitePresentation instTopologicallyFGOfFiniteType AlgebraicGeometry.ProjSpace.twistObj.addCommGroup AlgebraicGeometry.ProjSpace.twistFam.module AlgebraicGeometry.ProjSpace.twistObj.module AlgebraicGeometry.ProjSpace.twistObj.moduleSections AlgebraicGeometry.ProjSpace.twistFam.addCommGroup"
p2m_attr_erase "simp" "GoodReductionJacobian.relativeGroupLawOfGrpObj_inv GoodReductionJacobian.relativeGroupLawOfGrpObj_mul GoodReductionJacobian.overHomEquivSchemeHomOver_apply_coe GoodReductionJacobian.relativeGroupLawOfGrpObj_one GoodReductionJacobian.overHomEquivSchemeHomOver_symm_apply_left NeronModelInfra.NeronModelPropertyBundle.endExtensionEquiv_symm_restrict NeronModelInfra.schemeHomOverComp_id_left NeronModelInfra.schemeHomOverComp_id_right NeronModelInfra.schemeHomOverId_coe NeronModelInfra.NeronModelPropertyBundle.endExtensionEquiv_apply NeronModelInfra.NeronModelPropertyBundle.restrict_endExtensionEquiv_symm NeronModelInfra.schemeHomOverComp_coe NeronModelInfra.schemeHomOverNpow_succ NeronModelInfra.schemeHomOverNpow_zero SheafOfModules.tensorUnit_eq AlgebraicGeometry.Scheme.Modules.tensorUnit_eq PresheafOfModules.InternalHom.presheaf_map_apply PresheafOfModules.InternalHom.curryFamily_app PresheafOfModules.InternalHom.add_app PresheafOfModules.InternalHom.smul_app PresheafOfModules.InternalHom.zero_app PresheafOfModules.ihomObj_map_val PresheafOfModules.ihomFunctor_map PresheafOfModules.InternalHom.restrict_app PresheafOfModules.InternalHom.postcomp_app PresheafOfModules.InternalHom.neg_app PresheafOfModules.curry'_app_val PresheafOfModules.InternalHom.presheaf_obj PresheafOfModules.ihomFunctor_obj PresheafOfModules.ihomObj_obj PresheafOfModules.InternalHom.sub_app PresheafOfModules.ihomMap_app_val AlgebraicGeometry.Scheme.Modules.tensorPow_zero AlgebraicGeometry.Scheme.Modules.tensorPow_succ AlgebraicGeometry.RelPicard.RigidifiedLineBundle.mk.sizeOf_spec AlgebraicGeometry.RelPicard.RigidifiedLineBundle.mk.injEq AlgebraicGeometry.Scheme.OrderedAffineCover.mk.injEq AlgebraicGeometry.OModulePresheaf.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCover.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.mk.injEq"
p2m_attr_erase "simp" "AlgebraicGeometry.Scheme.TwoAffineOpenCover.mk.injEq AlgebraicGeometry.Scheme.TwoAffineOpenCover.mk.sizeOf_spec AlgebraicGeometry.Scheme.TwoAffineOpenCover.pullback_U1 AlgebraicGeometry.Scheme.TwoAffineOpenCover.pullback_U0 TwoChartCech.Sections.mk.injEq TwoChartCech.Cover.mk.injEq TwoChartCech.GrothendieckComplex.mk.injEq TwoChartCech.Sections.mk.sizeOf_spec TwoChartCech.Cover.mk.sizeOf_spec TwoChartCech.Cover.lineBundle_r0_apply TwoChartCech.GrothendieckComplex.mk.sizeOf_spec TwoChartCech.Cover.lineBundle_r1_apply CoherentBaseChange.TwoTermComplex.mk.sizeOf_spec CoherentBaseChange.TwoTermComplex.mk.injEq AlgebraicGeometry.OModulePresheaf.prod_obj AlgebraicGeometry.OModulePresheaf.restrOpen_obj AlgebraicGeometry.OModulePresheaf.DevissageStep.mk.injEq AlgebraicGeometry.OModulePresheaf.pushforward_obj AlgebraicGeometry.OModulePresheaf.im_obj AlgebraicGeometry.OModulePresheaf.pow_obj AlgebraicGeometry.OModulePresheaf.fstHom_app AlgebraicGeometry.OModulePresheaf.ker_obj AlgebraicGeometry.OModulePresheaf.coker_obj AlgebraicGeometry.OModulePresheaf.DevissageStep.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCover.preimage_U AlgebraicGeometry.OModulePresheaf.sndHom_app AlgebraicGeometry.OModulePresheaf.Hom.mk.injEq AlgebraicGeometry.OModulePresheaf.Hom.id_app AlgebraicGeometry.OModulePresheaf.AffHom.appSections_apply AlgebraicGeometry.OModulePresheaf.AffHom.comp_app AlgebraicGeometry.OModulePresheaf.AffSES.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.AffHom.kerMap_coe AlgebraicGeometry.OModulePresheaf.AffHom.id_app AlgebraicGeometry.OModulePresheaf.Hom.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.Hom.toAffHom_app AlgebraicGeometry.OModulePresheaf.SES.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.AffHom.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.Hom.comp_app AlgebraicGeometry.OModulePresheaf.SES.mk.injEq AlgebraicGeometry.OModulePresheaf.AffHom.mk.injEq"
p2m_attr_erase "simp" "AlgebraicGeometry.OModulePresheaf.Hom.appSections_apply AlgebraicGeometry.OModulePresheaf.AffSES.mk.injEq PresheafOfModules.freeεIso_hom_app PresheafOfModules.freeμIso_hom_app AlgebraicGeometry.RelPicard.RepresentsRelSubPic.mk.injEq AlgebraicGeometry.RelPicard.SubPicCondition.mk.injEq AlgebraicGeometry.RelPicard.SubPicCondition.mk.sizeOf_spec AlgebraicGeometry.RelPicard.RepresentsRelSubPic.mk.sizeOf_spec AlgebraicGeometry.SmoothProperCurve.sectionBaseChange_coe_snd AlgebraicGeometry.SmoothProperCurve.sectionBaseChange_coe_fst AlgebraicCurve.CurveModel.mk.injEq AlgebraicCurve.CurveModel.mk.sizeOf_spec AlgebraicCurve.mulAdele_apply AlgebraicCurve.residuePairing_apply_coe AlgebraicCurve.mem_adeleBdd AlgebraicCurve.weilSmul_one AlgebraicCurve.diagonalHom_apply AlgebraicCurve.weilSmul_apply AlgebraicCurve.adeleSpaceMul_coe AlgebraicCurve.mulAdele_one AlgebraicGeometry.SmoothProperCurve.FiniteMapData.twoAffineOpenCover_U1 AlgebraicGeometry.SmoothProperCurve.FiniteMapData.mk.injEq AlgebraicGeometry.SmoothProperCurve.FiniteMapData.mk.sizeOf_spec AlgebraicGeometry.SmoothProperCurve.FiniteMapData.twoAffineOpenCover_U0 AlgebraicGeometry.RelPicard.SubPicCondition.onClasses_mk AlgebraicGeometry.RelPicard.relSubPicPresheaf_map_coe CategoryTheory.Functor.OverTotal.ofFibre_fst CategoryTheory.Functor.overTotal_map_fst AlgebraicGeometry.Scheme.LocalRepresentabilityULift.glueData_J AlgebraicGeometry.Scheme.LocalRepresentabilityULift.uliftYoneda_toGlued_uliftYonedaGluedToSheaf AlgebraicGeometry.Scheme.LocalRepresentabilityULift.glueData_t' AlgebraicGeometry.Scheme.LocalRepresentabilityULift.uliftYoneda_toGlued_uliftYonedaGluedToSheaf_assoc AlgebraicGeometry.Scheme.LocalRepresentabilityULift.uliftYonedaGluedToSheaf_app_toGlued AlgebraicGeometry.Scheme.LocalRepresentabilityULift.glueData_openCover_map AlgebraicGeometry.Scheme.LocalRepresentabilityULift.uliftYonedaGluedToSheaf_app_comp AlgebraicGeometry.Scheme.LocalRepresentabilityULift.glueData_V AlgebraicGeometry.Scheme.LocalRepresentabilityULift.glueData_t AlgebraicGeometry.Scheme.LocalRepresentabilityULift.glueData_U AlgebraicGeometry.Scheme.LocalRepresentabilityULift.glueData_f AlgebraicGeometry.RelPicard.designationOfRepresentableBy_P"
p2m_attr_erase "simp" "AlgebraicGeometry.RelPicard.designationOfRepresentableBy_toBase AlgebraicGeometry.RelPicard.rigSection_snd AlgebraicGeometry.RelPicard.RigidifiedLineBundle.ofInvertible_L AlgebraicGeometry.RelPicard.rigSection_snd_assoc AlgebraicGeometry.RelPicard.SubPicGroupCondition.mk.injEq AlgebraicGeometry.RelPicard.SubPicGroupCondition.mk.sizeOf_spec AlgebraicCurve.coe_cechH0Equiv_apply AlgebraicCurve.cechH1ToH1_mk AlgebraicCurve.lSpaceOn_univ AlgebraicCurve.lSpaceOn_empty AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.Divisor.mapRestrict_single AlgebraicCurve.Divisor.pushforward_single AlgebraicCurve.Place.coe_restrictInclusion AlgebraicCurve.Place.mem_fiber AlgebraicCurve.Place.restrict_toValuationSubring AlgebraicCurve.Divisor.degree_pushforward AlgebraicCurve.Place.restrictResidueMap_residue AlgebraicCurve.Pic0.coe_pushforwardDegZeroHom AlgebraicCurve.Pic0.coe_pullbackDegZeroHom AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk"
p2m_attr_erase "simp" "ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Divisor.degree_pushforwardAlong AlgebraicCurve.Pic0.coe_degZeroCorrespondence AlgebraicCurve.Place.mem_fiberAlong AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.jqNModC_one ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one AlgebraicCurve.Place.differentialCoeff_zero AlgebraicCurve.Place.differentialCoeff_dCoord AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.injEq AlgebraicCurve.TranscendenceTower.mk.injEq AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec AlgebraicCurve.PoleDivisorPackage.mk.injEq AlgebraicGeometry.RelPicard.thetaBundle_def AlgebraicGeometry.RelPicard.picardBundle_def AlgebraicGeometry.RelEffCartierDiv.toRelEffDivisor_ofRelEffDivisor AlgebraicGeometry.RelEffCartierDiv.toRelEffDivisor_I AlgebraicGeometry.mapOnProdOver_fst_assoc AlgebraicGeometry.RelEffCartierDiv.mk.sizeOf_spec AlgebraicGeometry.RelEffCartierDiv.mk.injEq"
p2m_attr_erase "simp" "AlgebraicGeometry.mapOnProdOver_snd AlgebraicGeometry.mapOnProdOver_fst AlgebraicGeometry.mapOnProdOver_snd_assoc AlgebraicGeometry.mapOnProdOver_id AlgebraicCurve.RelEffDivisor.mk.sizeOf_spec AlgebraicCurve.mapOnProd_fst AlgebraicCurve.mapOnProd_fst_assoc AlgebraicCurve.mapOnProd_snd AlgebraicCurve.UnivDivisorPack.mk.injEq AlgebraicCurve.RelEffDivisor.mk.injEq AlgebraicCurve.UnivDivisorPack.mk.sizeOf_spec AlgebraicCurve.mapOnProd_snd_assoc AlgebraicGeometry.Scheme.Modules.exteriorPower_obj PresheafOfModules.exteriorPower_map_ιMulti PresheafOfModules.ExteriorPower.appₗ_apply AlgebraicGeometry.prodKerGraph_one AlgebraicGeometry.fibrePowOver.proj_comp AlgebraicGeometry.prodKerGraph_zero AlgebraicGeometry.RelEffCartierDiv.empty_I AlgebraicGeometry.fibrePowOver.proj_comp_assoc AlgebraicGeometry.graphOver_fst_assoc AlgebraicGeometry.RelEffCartierDiv.toPoint_comp AlgebraicGeometry.RelEffCartierDiv.toPoint_comp_assoc AlgebraicGeometry.graphOver_fst AlgebraicGeometry.RelEffCartierDiv.ofPoint_I AlgebraicGeometry.graphOver_snd AlgebraicGeometry.graphOver_snd_assoc AlgebraicCurve.SymmetricPowerPackage.mk.sizeOf_spec AlgebraicCurve.SymmetricPowerPackage.mk.injEq AlgebraicGeometry.FGSubalgebra.cocone_ι_app_apply AlgebraicGeometry.RelPicard.fst_toProdSpec AlgebraicGeometry.RelPicard.toProdSpec_fst_assoc AlgebraicGeometry.RelPicard.pointsSubBasepointModule_cons AlgebraicGeometry.RelPicard.pointsSubBasepointModule_nil AlgebraicGeometry.RelPicard.fst_toProdSpec_assoc AlgebraicGeometry.RelPicard.toProdSpec_fst AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.sub_app AlgebraicGeometry.Scheme.IdealSheafData.sres_sresTop AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.add_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.mk.sizeOf_spec"
p2m_attr_erase "simp" "AlgebraicGeometry.Scheme.IdealSheafData.coe_resLE AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.smul_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.coe_ofLE_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.ideal_range AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.zero_app AlgebraicGeometry.Scheme.IdealSheafData.sres_sres AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.comp_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.neg_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.id_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.coe_mulRight_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.nsmul_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.mk.injEq AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.zsmul_app AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.sizeOf_spec AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.injEq AlgebraicCurve.adeleSingle_coe AlgebraicCurve.kaehlerResidueTermKFam_apply AlgebraicCurve.Place.LocalResidueData.mk.injEq AlgebraicCurve.Place.LocalResidueData.mk.sizeOf_spec AlgebraicCurve.Place.kw_ffgc_adicCompletionComapIntegers_coe AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.sizeOf_spec AlgebraicCurve.Place.mem_simplePoleSubmodule AlgebraicCurve.Place.coe_uniformizerSubring ModularCurve.Lg37.Lg37CompletionSection.mk.injEq AlgebraicCurve.Place.CoefficientFieldSection.mk.injEq AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.injEq ModularCurve.Lg37.Lg37CompletionSection.mk.sizeOf_spec AlgebraicCurve.Place.CoefficientFieldSection.mk.sizeOf_spec AlgebraicCurve.Place.poleSubmodule_one AlgebraicCurve.Place.mem_poleSubmodule AlgebraicGeometry.Scheme.Modules.toUnitSection_ofUnitSection AlgebraicGeometry.Scheme.Modules.pullbackSection_def AlgebraicGeometry.Scheme.Modules.ofUnitSection_toUnitSection PresheafOfModules.InternalHom.IsSheafAux.appAt_toPresheafHom SheafOfModules.ihomSectionsEquivFamily_unit AlgebraicGeometry.Scheme.Modules.restrictHomEquivFamily_apply SheafOfModules.ihomEval_unit_app AlgebraicGeometry.Scheme.Modules.ihomEval_zero_right AlgebraicGeometry.Scheme.Modules.ihomEval_zero_left AlgebraicGeometry.Scheme.Modules.homOfFamily_app_apply"
p2m_attr_erase "simp" "SheafOfModules.unit_ihomSectionsEquivFamily AlgebraicGeometry.Scheme.Modules.familyOfHom_app AlgebraicGeometry.Scheme.Modules.restrictUnitIso_hom_app_apply AlgebraicGeometry.Scheme.Modules.restrictUnitIso_inv_app_apply AlgebraicGeometry.Scheme.Modules.restrictHomOfFamily_app_apply AlgebraicGeometry.Scheme.Modules.restrictHomEquivFamily_symm_apply AlgebraicGeometry.Scheme.Modules.tensorSections_zero_right AlgebraicGeometry.Scheme.Modules.map_unitSection AlgebraicGeometry.Scheme.Modules.tensorSectionsBilin_apply AlgebraicGeometry.Scheme.Modules.tensorPowSection_zero AlgebraicGeometry.Scheme.Modules.tensorSections_zero_left AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_neg AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_zero AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_sub AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_add AlgebraicGeometry.Scheme.OrderedAffineCover.toCoverOf_U AlgebraicGeometry.Scheme.OrderedAffineCoverOf.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCoverOf.mk.injEq AlgebraicGeometry.Scheme.OrderedAffineCover.restrict_U AlgebraicGeometry.OModulePresheaf.Leray.restrictToPreimage_U DoubleComplex.Bounded.mk.injEq DoubleComplex.Bounded.mk.sizeOf_spec DoubleComplex.Convergence.mk.injEq DoubleComplex.Convergence.mk.sizeOf_spec DoubleComplex.SubQuot.mk.sizeOf_spec DoubleComplex.SubQuot.mk.injEq AlgebraicGeometry.ChowDatumProj.mk.sizeOf_spec AlgebraicGeometry.ChowDatum.mk.sizeOf_spec AlgebraicGeometry.ChowDatumProj.mk.injEq AlgebraicGeometry.ChowDatum.mk.injEq ProjSpaceCech.GradedModule.mk.injEq ProjSpaceCech.GradedModule.mk.sizeOf_spec ProjSpaceCech.GradedModule.Frac.mk.sizeOf_spec ProjSpaceCech.GradedModule.Presentation.mk.injEq ProjSpaceCech.GradedModule.Frac.mk.injEq ProjSpaceCech.GradedModule.Presentation.mk.sizeOf_spec ProjSpaceCech.GradedModule.Hom.shift_toLinearMap ProjSpaceCech.GradedModule.Hom.mk.sizeOf_spec ProjSpaceCech.GradedModule.Hom.mk.injEq TwoChartCech.Mumford.dK_apply"
p2m_attr_erase "simp" "TwoChartCech.Mumford.ι0_apply TwoChartCech.Mumford.ι1_apply TwoChartCech.KerCoprod.dK_apply TwoChartCech.KerCoprod.ι1_apply TwoChartCech.KerCoprod.ι0_apply AlgebraicGeometry.tilde.functorCompPullbackSpecIso_app AlgebraicGeometry.RelPicard.algEquivZeroGroupCut_toSubPicCondition AlgebraicGeometry.RelPicard.LFP.stageHom_val AlgebraicGeometry.RelPicard.BaseChange.relSubPicPresheafRestrictIso_hom_app_coe AlgebraicGeometry.RelPicard.BaseChange.relSubPicPresheafRestrictIso_inv_app_coe AlgebraicGeometry.RelPicard.BaseChange.restrict_P AlgebraicGeometry.RelEffCartierDiv.IsUniversal.lift_comp AlgebraicGeometry.RelEffCartierDiv.functor_map_fst AlgebraicGeometry.RelEffCartierDiv.IsUniversal.homEquiv_apply AlgebraicGeometry.RelEffCartierDiv.IsUniversal.lift_pullbackAlong AlgebraicGeometry.RelEffCartierDiv.IsUniversal.homEquiv_symm_apply AlgebraicGeometry.RelEffCartierDiv.IsUniversal.lift_comp_assoc AlgebraicGeometry.RelEffCartierDiv.supportedIn_top AlgebraicGeometry.RelEffCartierDiv.mem_supportedIn_iff AlgebraicGeometry.RelEffCartierDiv.supportedIn_top_eq AlgebraicGeometry.RelEffCartierDiv.restrictAlong_extendAlong AlgebraicGeometry.RelEffCartierDiv.extendAlong_I AlgebraicGeometry.RelEffCartierDiv.resProdMap_snd AlgebraicGeometry.RelEffCartierDiv.restrictAlong_I AlgebraicGeometry.RelEffCartierDiv.extendAlong_restrictAlong AlgebraicGeometry.RelEffCartierDiv.resProdMap_fst_assoc AlgebraicGeometry.RelEffCartierDiv.resProdMap_snd_assoc AlgebraicGeometry.RelEffCartierDiv.resProdMap_fst CoherentBaseChange.FibreH0Family.mk.sizeOf_spec CoherentBaseChange.FibreH0Family.mk.injEq AlgebraicGeometry.Scheme.Modules.ProjPresentation.mk.injEq AlgebraicGeometry.Scheme.Modules.ProjPresentation.mk.sizeOf_spec AlgebraicCurve.CurveModel.coe_gInf AlgebraicCurve.CurveModel.coe_tInvChart AlgebraicCurve.CurveModel.ιInf_gluedToBase_assoc AlgebraicCurve.CurveModel.ιInf_gluedToBase AlgebraicCurve.CurveModel.primeOfι₀_asIdeal AlgebraicCurve.CurveModel.coe_tChart AlgebraicCurve.CurveModel.ι₀_gluedToBase_assoc AlgebraicCurve.CurveModel.primeOfιInf_asIdeal"
p2m_attr_erase "simp" "AlgebraicCurve.CurveModel.ι₀_gluedToBase AlgebraicCurve.CurveModel.coe_tma AlgebraicCurve.CurveModel.coe_primeEquivChartPlaces RegularLocalRingQuotientAscent.dualNumberFst_apply AlgebraicGeometry.ProjSpace.twistObj.mk.injEq AlgebraicGeometry.ProjSpace.twistObj.zero_val AlgebraicGeometry.ProjSpace.twistObj.add_val AlgebraicGeometry.ProjSpace.twist_res_val AlgebraicGeometry.ProjSpace.twist_smul_val AlgebraicGeometry.ProjSpace.twistGradeToObj_val AlgebraicGeometry.ProjSpace.twistObj.smul_val AlgebraicGeometry.ProjSpace.twistGradeEquiv_apply_val AlgebraicGeometry.ProjSpace.twistObj.mk.sizeOf_spec QuaternionAlgebra.baseChangeRight_tmul QuaternionAlgebra.mapOfAlgebraMapEq_apply QuaternionAlgebra.baseChange_tmul QuaternionAlgebra.ClassSet.map_mk GoodReductionJacobian.RelativeGroupLaw.baseChangePointToBase_ofBase GoodReductionJacobian.RelativeGroupLaw.baseChangePointToBase_coe GoodReductionJacobian.RelativeGroupLaw.baseChangePointOfBase_coe GoodReductionJacobian.RelativeGroupLaw.baseChange_inv GoodReductionJacobian.RelativeGroupLaw.baseChangePointOfBase_toBase GoodReductionJacobian.RelativeGroupLaw.baseChange_mul GoodReductionJacobian.RelativeGroupLaw.baseChange_one NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_fst NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_snd NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_fst NeronSpecialFibreInfra.neronEndRestrictEquiv_apply NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_fst_assoc NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_snd NeronSpecialFibreInfra.neronEndExtension_genericFibreRestrict NeronSpecialFibreInfra.specClosedFibreInclusion_eq NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_fst_assoc NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_snd_assoc NeronSpecialFibreInfra.genericFibreRestrict_neronEndExtension NeronSpecialFibreInfra.homOverId_coe NeronSpecialFibreInfra.homOverComp_coe NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_snd_assoc GoodReductionJacobian.RelativeGroupLaw.fibre_inv GoodReductionJacobian.RelativeGroupLaw.fibrePointToBase_coe"
p2m_attr_erase "simp" "GoodReductionJacobian.RelativeGroupLaw.fibrePointOfBase_toBase GoodReductionJacobian.RelativeGroupLaw.fibre_mul GoodReductionJacobian.RelativeGroupLaw.fibrePointToBase_ofBase GoodReductionJacobian.RelativeGroupLaw.fibre_one GoodReductionJacobian.RelativeGroupLaw.fibrePointOfBase_coe"

set_option autoImplicit false

open scoped Quaternion
p2m_open "CategoryTheory CategoryTheory.Limits AlgebraicGeometry CerednikDrinfeld CerednikDrinfeld.QM QuaternionAlgebra NeronModelInfra~schemeHomOverComp~schemeHomOverComp_coe GoodReductionJacobian"

universe u

namespace StepRam13

section PointAlgebra
variable {R : Type u} [CommRing R] {A : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of R)}

theorem comp_one (L : RelativeGroupLaw R f)
    {T T' : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (t' : T' ⟶ Spec (CommRingCat.of R)) (ψ : T' ⟶ T)
    (hψ : ψ ≫ t = t') : ψ ≫ (L.one t).1 = (L.one t').1 :=
  congrArg Subtype.val (L.one_natural t t' ψ hψ)

theorem nsmulPt_eq_nsmul (L : RelativeGroupLaw R f) {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (n : ℕ)
    (P : SchemeHomOver t f) : nsmulPt L t n P = L.nsmul t n P := by
  induction n with
  | zero => rfl
  | succ n ih => rw [RelativeGroupLaw.nsmul_succ, ← ih]; rfl

theorem comp_nsmulPt (L : RelativeGroupLaw R f)
    {T T' : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (t' : T' ⟶ Spec (CommRingCat.of R)) (ψ : T' ⟶ T)
    (hψ : ψ ≫ t = t') (n : ℕ) (P : SchemeHomOver t f) :
    ψ ≫ (nsmulPt L t n P).1 = (nsmulPt L t' n (schemeHomOverComp ψ hψ P)).1 := by
  rw [nsmulPt_eq_nsmul, nsmulPt_eq_nsmul, ← L.nsmul_natural t t' ψ hψ n P]
  rfl

theorem nsmulPt_coe (L : RelativeGroupLaw R f) {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (n : ℕ)
    (P : SchemeHomOver t f) : (nsmulPt L t n P).1 = P.1 ≫ L.schemeNsmul n := by
  have h := comp_nsmulPt L f t P.1 P.2 n RelativeGroupLaw.idPoint
  have hid : schemeHomOverComp P.1 P.2 (RelativeGroupLaw.idPoint (f := f)) = P := Subtype.ext (by simp)
  rw [hid] at h
  rw [← h, RelativeGroupLaw.schemeNsmul, nsmulPt_eq_nsmul]

theorem coe_comp_schemeNsmul_of_nsmulPt_eq_one (L : RelativeGroupLaw R f) (n : ℕ) {T : Scheme.{u}}
    (t : T ⟶ Spec (CommRingCat.of R)) (P : SchemeHomOver t f) (hP : nsmulPt L t n P = L.one t) :
    P.1 ≫ L.schemeNsmul n = t ≫ (L.one (𝟙 (Spec (CommRingCat.of R)))).1 := by
  rw [← nsmulPt_coe, hP]
  exact (comp_one L (𝟙 _) t t (Category.comp_id _)).symm

theorem nsmulPt_one (L : RelativeGroupLaw R f) {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (n : ℕ) :
    nsmulPt L t n (L.one t) = L.one t := by
  rw [nsmulPt_eq_nsmul]; exact L.nsmul_unit t n

theorem mapPt_comp {A₂ A₃ : Scheme.{u}} {f₂ : A₂ ⟶ Spec (CommRingCat.of R)}
    {f₃ : A₃ ⟶ Spec (CommRingCat.of R)} (φ : A ⟶ A₂) (hφ : φ ≫ f₂ = f) (ψ : A₂ ⟶ A₃) (hψ : ψ ≫ f₃ = f₂)
    (h : (φ ≫ ψ) ≫ f₃ = f) {T : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of R)} (P : SchemeHomOver t f) :
    mapPt (φ ≫ ψ) h P = mapPt ψ hψ (mapPt φ hφ P) :=
  Subtype.ext (by simp only [mapPt_coe, Category.assoc])

theorem mapPt_congr {A₂ : Scheme.{u}} {f₂ : A₂ ⟶ Spec (CommRingCat.of R)}
    (φ φ' : A ⟶ A₂) (hφ : φ ≫ f₂ = f) (hφ' : φ' ≫ f₂ = f) (e : φ = φ')
    {T : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of R)} (P : SchemeHomOver t f) :
    mapPt φ hφ P = mapPt φ' hφ' P := by subst e; rfl

theorem mapPt_one_of_hom {A₂ : Scheme.{u}} {f₂ : A₂ ⟶ Spec (CommRingCat.of R)}
    (L : RelativeGroupLaw R f) (L₂ : RelativeGroupLaw R f₂) (φ : A ⟶ A₂) (hφ : φ ≫ f₂ = f)
    (hom : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (P Q : SchemeHomOver t f),
      mapPt φ hφ (L.mul t P Q) = L₂.mul t (mapPt φ hφ P) (mapPt φ hφ Q))
    {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) : mapPt φ hφ (L.one t) = L₂.one t := by
  letI := L₂.pointGroup t
  have h := hom t (L.one t) (L.one t)
  rw [L.one_mul] at h
  have h2 : L₂.mul t (mapPt φ hφ (L.one t)) (mapPt φ hφ (L.one t)) = L₂.mul t (mapPt φ hφ (L.one t)) (L₂.one t) := by
    rw [L₂.mul_one]; exact h.symm
  exact mul_left_cancel h2

theorem mapPt_nsmulPt_of_hom {A₂ : Scheme.{u}} {f₂ : A₂ ⟶ Spec (CommRingCat.of R)}
    (L : RelativeGroupLaw R f) (L₂ : RelativeGroupLaw R f₂) (φ : A ⟶ A₂) (hφ : φ ≫ f₂ = f)
    (hom : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (P Q : SchemeHomOver t f),
      mapPt φ hφ (L.mul t P Q) = L₂.mul t (mapPt φ hφ P) (mapPt φ hφ Q))
    {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (n : ℕ) (P : SchemeHomOver t f) :
    mapPt φ hφ (nsmulPt L t n P) = nsmulPt L₂ t n (mapPt φ hφ P) := by
  induction n with
  | zero => exact mapPt_one_of_hom L L₂ φ hφ hom t
  | succ n ih => simp only [nsmulPt]; rw [hom, ih]

theorem mapPt_inv_of_hom {A₂ : Scheme.{u}} {f₂ : A₂ ⟶ Spec (CommRingCat.of R)}
    (L : RelativeGroupLaw R f) (L₂ : RelativeGroupLaw R f₂) (φ : A ⟶ A₂) (hφ : φ ≫ f₂ = f)
    (hom : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (P Q : SchemeHomOver t f),
      mapPt φ hφ (L.mul t P Q) = L₂.mul t (mapPt φ hφ P) (mapPt φ hφ Q))
    {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (P : SchemeHomOver t f) :
    mapPt φ hφ (L.inv t P) = L₂.inv t (mapPt φ hφ P) := by
  letI := L₂.pointGroup t
  have h := hom t (L.inv t P) P
  rw [L.inv_mul_cancel, mapPt_one_of_hom L L₂ φ hφ hom] at h
  exact (eq_inv_of_mul_eq_one_left h.symm)

end PointAlgebra

section Sections
variable {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} {N : ℕ} {k : Type} [Field k]

theorem section_eq_of_comp_eq (C : FakeEllipticCurve Λ N k) (n : ℕ) (hn : IsUnit ((n : ℕ) : k))
    (P₁ P₂ : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) C.f)
    (h₁ : nsmulPt C.L (𝟙 _) n P₁ = C.L.one _) (h₂ : nsmulPt C.L (𝟙 _) n P₂ = C.L.one _)
    {T : Scheme.{0}} [Nonempty ↥T] (g : T ⟶ Spec (CommRingCat.of k)) (hg : g ≫ P₁.1 = g ≫ P₂.1) : P₁ = P₂ := by
  obtain ⟨hfin, het⟩ := CerednikDrinfeld.QM.FakeEllipticCurve.isFinite_and_etale_schemeKerStr_of_isUnit C n hn
  have w₁ := coe_comp_schemeNsmul_of_nsmulPt_eq_one C.L n (𝟙 _) P₁ h₁
  have w₂ := coe_comp_schemeNsmul_of_nsmulPt_eq_one C.L n (𝟙 _) P₂ h₂
  let s₁ : Spec (CommRingCat.of k) ⟶ C.L.schemeKer n := pullback.lift P₁.1 (𝟙 _) w₁
  let s₂ : Spec (CommRingCat.of k) ⟶ C.L.schemeKer n := pullback.lift P₂.1 (𝟙 _) w₂
  have hs₁ : s₁ ≫ C.L.schemeKerStr n = 𝟙 _ := pullback.lift_snd _ _ _
  have hs₂ : s₂ ≫ C.L.schemeKerStr n = 𝟙 _ := pullback.lift_snd _ _ _
  obtain ⟨-, hO⟩ := AlgebraicGeometry.isClopen_preimage_diagonal_of_formallyUnramified_of_isSeparated
    (C.L.schemeKerStr n) s₁ s₂ hs₁ hs₂
  have hgs : g ≫ s₁ = g ≫ s₂ := by
    apply pullback.hom_ext
    · rw [Category.assoc, Category.assoc, pullback.lift_fst, pullback.lift_fst]; exact hg
    · rw [Category.assoc, Category.assoc, pullback.lift_snd, pullback.lift_snd]
  have hsub := (hO g).2 hgs
  obtain ⟨x₀⟩ := (inferInstance : Nonempty ↥T)
  have hpt : ∀ y : ↥(Spec (CommRingCat.of k)), y ∈ ((pullback.lift s₁ s₂ (hs₁.trans hs₂.symm) ⁻¹ᵁ
      (pullback.diagonal (C.L.schemeKerStr n)).opensRange : (Spec (CommRingCat.of k)).Opens) : Set _) := by
    intro y
    rw [Subsingleton.elim y (g.base x₀)]
    exact hsub ⟨x₀, rfl⟩
  have e := (hO (𝟙 _)).1 (by rintro _ ⟨y, rfl⟩; exact hpt _)
  rw [Category.id_comp, Category.id_comp] at e
  apply Subtype.ext
  have := congrArg (fun φ => φ ≫ pullback.fst (C.L.schemeNsmul n) (C.L.one (𝟙 (Spec (CommRingCat.of k)))).1) e
  simpa only [s₁, s₂, pullback.lift_fst] using this

theorem eq_one_of_factorsThrough_lev {S : Type} [CommRing S] (C : FakeEllipticCurve Λ 1 S)
    {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of S)) (P : SchemeHomOver t C.f)
    (hP : FactorsThrough C.lev P) : P = C.L.one t := by
  haveI := C.lev_finite
  haveI := C.lev_flat
  haveI := C.lev_finitePresentation
  haveI : IsIso (C.lev ≫ C.f) := by
    rw [Scheme.Hom.isIso_iff_finrank_eq]
    funext s
    rw [C.lev_rank s]
    simp
  obtain ⟨P₀, hP₀⟩ := hP
  obtain ⟨O₀, hO₀⟩ := C.lev_one t
  have k1 : P₀ = t ≫ inv (C.lev ≫ C.f) := by
    rw [← cancel_mono (C.lev ≫ C.f), Category.assoc, IsIso.inv_hom_id, Category.comp_id, ← Category.assoc, hP₀, P.2]
  have k2 : O₀ = t ≫ inv (C.lev ≫ C.f) := by
    rw [← cancel_mono (C.lev ≫ C.f), Category.assoc, IsIso.inv_hom_id, Category.comp_id, ← Category.assoc, hO₀,
      (C.L.one t).2]
  apply Subtype.ext
  rw [← hP₀, ← hO₀, k1, k2]

end Sections

end StepRam13

open StepRam13 in
set_option maxHeartbeats 1600000 in

theorem solution
    {q q' : ℕ} [Fact q.Prime] [Fact q'.Prime] (hqq' : q' ≠ q)
    {a b : ℚ} (hB : IsIndefiniteRamifiedExactlyAt a b q q')
    (Λ : Submodule ℤ ℍ[ℚ, a, b]) (hΛ : IsMaximalOrder Λ)
    (E : FakeEllipticCurve Λ 1 (AlgebraicClosure ℚ))
    (r : ℕ) (hr : r = q ∨ r = q')
    (H : Set (SchemeHomOver (𝟙 (Spec (CommRingCat.of (AlgebraicClosure ℚ)))) E.f)) (hHfin : H.Finite)
    (hHone : E.L.one (𝟙 (Spec (CommRingCat.of (AlgebraicClosure ℚ)))) ∈ H)
    (hHmul : ∀ P Q, P ∈ H → Q ∈ H → E.L.mul (𝟙 (Spec (CommRingCat.of (AlgebraicClosure ℚ)))) P Q ∈ H)
    (hHinv : ∀ P, P ∈ H → E.L.inv (𝟙 (Spec (CommRingCat.of (AlgebraicClosure ℚ)))) P ∈ H)
    (hHstab : ∀ (x : ↥Λ) P, P ∈ H → pushPt (E.act x) (E.act_over x) P ∈ H)
    (H' : Set (SchemeHomOver (𝟙 (Spec (CommRingCat.of (AlgebraicClosure ℚ)))) E.f)) (hH'fin : H'.Finite)
    (hH'one : E.L.one (𝟙 (Spec (CommRingCat.of (AlgebraicClosure ℚ)))) ∈ H')
    (hH'mul : ∀ P Q, P ∈ H' → Q ∈ H' → E.L.mul (𝟙 (Spec (CommRingCat.of (AlgebraicClosure ℚ)))) P Q ∈ H')
    (hH'inv : ∀ P, P ∈ H' → E.L.inv (𝟙 (Spec (CommRingCat.of (AlgebraicClosure ℚ)))) P ∈ H')
    (hH'stab : ∀ (x : ↥Λ) P, P ∈ H' → pushPt (E.act x) (E.act_over x) P ∈ H')
    (hHH' : H ⊆ H') (hcard : Nat.card ↥H' = r ^ 2 * Nat.card ↥H)
    (hram : ∀ P, P ∈ H' → ∀ (m : ↥Λ) (k : ℤ), (m : ℍ[ℚ, a, b]) * star (m : ℍ[ℚ, a, b]) = (((r : ℤ) * k : ℚ) : ℍ[ℚ, a, b]) →
      pushPt (E.act m) (E.act_over m) P ∈ H)
    (C : FakeEllipticCurve Λ 1 (AlgebraicClosure ℚ)) (p : E.A ⟶ C.A) (hp : p ≫ C.f = E.f) (K : Scheme.{0}) (κ : K ⟶ E.A)
    (hC :
      (∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of (AlgebraicClosure ℚ))) (P Q : SchemeHomOver t E.f),
        mapPt p hp (E.L.mul t P Q) = C.L.mul t (mapPt p hp P) (mapPt p hp Q)) ∧
      (∀ x : ↥Λ, E.act x ≫ p = p ≫ C.act x) ∧
      IsFinite p ∧ Flat p ∧ Surjective p ∧
      (∀ R : SchemeHomOver (𝟙 (Spec (CommRingCat.of (AlgebraicClosure ℚ)))) C.f, ∃ P : SchemeHomOver (𝟙 (Spec (CommRingCat.of (AlgebraicClosure ℚ)))) E.f, mapPt p hp P = R) ∧
      IsClosedImmersion κ ∧ IsReduced K ∧ IsFinite (κ ≫ E.f) ∧
      (∀ P : SchemeHomOver (𝟙 (Spec (CommRingCat.of (AlgebraicClosure ℚ)))) E.f, FactorsThrough κ P ↔ P ∈ H) ∧
      (∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of (AlgebraicClosure ℚ))) (Q : SchemeHomOver t E.f),
        mapPt p hp Q = C.L.one t ↔ FactorsThrough κ Q))
    (C' : FakeEllipticCurve Λ 1 (AlgebraicClosure ℚ)) (p' : E.A ⟶ C'.A) (hp' : p' ≫ C'.f = E.f) (K' : Scheme.{0}) (κ' : K' ⟶ E.A)
    (hC' :
      (∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of (AlgebraicClosure ℚ))) (P Q : SchemeHomOver t E.f),
        mapPt p' hp' (E.L.mul t P Q) = C'.L.mul t (mapPt p' hp' P) (mapPt p' hp' Q)) ∧
      (∀ x : ↥Λ, E.act x ≫ p' = p' ≫ C'.act x) ∧
      IsFinite p' ∧ Flat p' ∧ Surjective p' ∧
      (∀ R : SchemeHomOver (𝟙 (Spec (CommRingCat.of (AlgebraicClosure ℚ)))) C'.f, ∃ P : SchemeHomOver (𝟙 (Spec (CommRingCat.of (AlgebraicClosure ℚ)))) E.f, mapPt p' hp' P = R) ∧
      IsClosedImmersion κ' ∧ IsReduced K' ∧ IsFinite (κ' ≫ E.f) ∧
      (∀ P : SchemeHomOver (𝟙 (Spec (CommRingCat.of (AlgebraicClosure ℚ)))) E.f, FactorsThrough κ' P ↔ P ∈ H') ∧
      (∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of (AlgebraicClosure ℚ))) (Q : SchemeHomOver t E.f),
        mapPt p' hp' Q = C'.L.one t ↔ FactorsThrough κ' Q))
    :
    FakeEllipticCurve.IsAtkinLehnerQuotient r C C' := by
  classical

  obtain ⟨p_hom, p_act, -, -, -, p_pts, -, -, -, κ_pts, p_ker⟩ := id hC
  obtain ⟨-, p'_act, -, -, -, -, -, -, -, κ'_pts, p'_ker⟩ := id hC'
  have hO : IsOrder Λ := hΛ.isOrder
  have one_mem : (1 : ℍ[ℚ, a, b]) ∈ Λ := hO.one_mem
  have r_mem : ((r : ℚ) : ℍ[ℚ, a, b]) ∈ Λ := by
    have : ((r : ℚ) : ℍ[ℚ, a, b]) = (r : ℚ) • (1 : ℍ[ℚ, a, b]) := by
      rw [← QuaternionAlgebra.coe_mul_eq_smul, mul_one]
    rw [this, Nat.cast_smul_eq_nsmul]
    exact nsmul_mem one_mem r
  have hrprime : r.Prime := by rcases hr with rfl | rfl <;> exact Fact.out
  have hr0 : ((r : ℕ) : AlgebraicClosure ℚ) ≠ 0 := by exact_mod_cast hrprime.ne_zero
  have hrunit : IsUnit ((r : ℕ) : AlgebraicClosure ℚ) := isUnit_iff_ne_zero.mpr hr0
  have r_ram : ((⟨((r : ℚ) : ℍ[ℚ, a, b]), r_mem⟩ : ↥Λ) : ℍ[ℚ, a, b]) * star ((⟨((r : ℚ) : ℍ[ℚ, a, b]), r_mem⟩ : ↥Λ) : ℍ[ℚ, a, b]) =
      (((r : ℤ) * (r : ℤ) : ℚ) : ℍ[ℚ, a, b]) := by
    show ((r : ℚ) : ℍ[ℚ, a, b]) * star ((r : ℚ) : ℍ[ℚ, a, b]) = _
    rw [QuaternionAlgebra.star_coe, ← QuaternionAlgebra.coe_mul]
    norm_cast

  have h1H : ∀ P, P ∈ H → pushPt (E.act ⟨1, one_mem⟩) (E.act_over _) P ∈ H' := by
    intro P hP
    have : pushPt (E.act ⟨1, one_mem⟩) (E.act_over _) P = P := Subtype.ext (by
      simp only [pushPt, mapPt_coe, E.act_one one_mem, Category.comp_id])
    rw [this]; exact hHH' hP
  obtain ⟨φ, hφ, hpφ, φ_hom, φ_uniq, φ_lin⟩ :=
    CerednikDrinfeld.QM.FakeEllipticCurve.exists_comp_eq_act_comp_of_quotients (AlgebraicClosure ℚ) E
      H C p hp K κ hC H' C' p' hp' K' κ' hC' ⟨1, one_mem⟩ h1H
  have hpφ' : p ≫ φ = p' := by rw [hpφ, E.act_one one_mem, Category.id_comp]

  obtain ⟨ψ, hψ, hpψ, ψ_hom, ψ_uniq, ψ_lin⟩ :=
    CerednikDrinfeld.QM.FakeEllipticCurve.exists_comp_eq_act_comp_of_quotients (AlgebraicClosure ℚ) E
      H' C' p' hp' K' κ' hC' H C p hp K κ hC ⟨((r : ℚ) : ℍ[ℚ, a, b]), r_mem⟩
      (fun P hP => hram P hP _ (r : ℤ) r_ram)

  have hcomm_r : ∀ x : ↥Λ, E.act ⟨((r : ℚ) : ℍ[ℚ, a, b]), r_mem⟩ ≫ E.act x =
      E.act x ≫ E.act ⟨((r : ℚ) : ℍ[ℚ, a, b]), r_mem⟩ := by
    intro x
    have hxr : (x : ℍ[ℚ, a, b]) * ((r : ℚ) : ℍ[ℚ, a, b]) ∈ Λ := hO.mul_mem x.2 r_mem
    have hrx : ((r : ℚ) : ℍ[ℚ, a, b]) * (x : ℍ[ℚ, a, b]) ∈ Λ := hO.mul_mem r_mem x.2
    have e1 := E.act_mul x ⟨((r : ℚ) : ℍ[ℚ, a, b]), r_mem⟩ hxr
    have e2 := E.act_mul ⟨((r : ℚ) : ℍ[ℚ, a, b]), r_mem⟩ x hrx
    have e3 : (⟨(x : ℍ[ℚ, a, b]) * ((r : ℚ) : ℍ[ℚ, a, b]), hxr⟩ : ↥Λ) = ⟨((r : ℚ) : ℍ[ℚ, a, b]) * (x : ℍ[ℚ, a, b]), hrx⟩ :=
      Subtype.ext (by simp only [QuaternionAlgebra.coe_mul_eq_smul, QuaternionAlgebra.mul_coe_eq_smul])
    rw [← e1, e3, e2]
  refine ⟨φ, hφ, ψ, hψ, φ_hom, ψ_hom, ?_, ?_, ?_, ?_, ?_⟩
  ·
    intro x
    exact φ_lin x (by rw [E.act_one one_mem, Category.id_comp, Category.comp_id]) (fun P hP => hHstab x P hP)
  ·
    intro x
    exact ψ_lin x (hcomm_r x) (fun P hP => hH'stab x P hP)
  ·
    intro hr'
    obtain ⟨θ₁, -, -, -, u₁, -⟩ :=
      CerednikDrinfeld.QM.FakeEllipticCurve.exists_comp_eq_act_comp_of_quotients (AlgebraicClosure ℚ) E
        H C p hp K κ hC H C p hp K κ hC ⟨((r : ℚ) : ℍ[ℚ, a, b]), hr'⟩ (fun P hP => hHstab _ P hP)
    obtain ⟨θ₂, -, -, -, u₂, -⟩ :=
      CerednikDrinfeld.QM.FakeEllipticCurve.exists_comp_eq_act_comp_of_quotients (AlgebraicClosure ℚ) E
        H' C' p' hp' K' κ' hC' H' C' p' hp' K' κ' hC' ⟨((r : ℚ) : ℍ[ℚ, a, b]), hr'⟩ (fun P hP => hH'stab _ P hP)
    constructor
    · rw [u₁ (φ ≫ ψ) (by rw [Category.assoc, hψ, hφ]) (by rw [← Category.assoc, hpφ', hpψ]),
        u₁ (C.act _) (C.act_over _) (by rw [p_act])]
    · rw [u₂ (ψ ≫ φ) (by rw [Category.assoc, hφ, hψ]) (by rw [← Category.assoc, hpψ, Category.assoc, hpφ']),
        u₂ (C'.act _) (C'.act_over _) (by rw [p'_act])]
  ·
    intro T t P
    constructor
    · intro hφP m n hmn
      obtain ⟨θm, hθm, hpθm, θm_hom, -, -⟩ :=
        CerednikDrinfeld.QM.FakeEllipticCurve.exists_comp_eq_act_comp_of_quotients (AlgebraicClosure ℚ) E
          H' C' p' hp' K' κ' hC' H C p hp K κ hC m (fun P hP => hram P hP m n hmn)
      obtain ⟨θ₂, -, -, -, u₂, -⟩ :=
        CerednikDrinfeld.QM.FakeEllipticCurve.exists_comp_eq_act_comp_of_quotients (AlgebraicClosure ℚ) E
          H C p hp K κ hC H C p hp K κ hC m (fun P hP => hHstab m P hP)
      have e1 : φ ≫ θm = θ₂ := u₂ _ (by rw [Category.assoc, hθm, hφ]) (by rw [← Category.assoc, hpφ', hpθm])
      have e2 : C.act m = θ₂ := u₂ _ (C.act_over m) (by rw [p_act])
      have e3 : pushPt (C.act m) (C.act_over m) P = mapPt θm hθm (mapPt φ hφ P) :=
        Subtype.ext (by simp only [pushPt, mapPt_coe, Category.assoc]; rw [e2, ← e1])
      rw [e3, hφP, mapPt_one_of_hom C'.L C.L θm hθm θm_hom]
    · intro hP

      have hPr : nsmulPt C.L t r P = C.L.one t := by
        rw [← CerednikDrinfeld.QM.FakeEllipticCurve.pushPt_act_natCast_eq_nsmulPt C one_mem r r_mem]
        exact hP _ (r : ℤ) r_ram
      have hQr : nsmulPt C'.L t r (mapPt φ hφ P) = C'.L.one t := by
        rw [← mapPt_nsmulPt_of_hom C.L C'.L φ hφ φ_hom, hPr, mapPt_one_of_hom C.L C'.L φ hφ φ_hom]
      obtain ⟨hfin', het'⟩ := CerednikDrinfeld.QM.FakeEllipticCurve.isFinite_and_etale_schemeKerStr_of_isUnit C' r hrunit
      apply GoodReductionJacobian.RelativeGroupLaw.eq_of_nsmulPt_eq_one_of_forall_comp_eq C'.L r t _ _ hQr
        (nsmulPt_one C'.L t r)
      intro k' _ _ τ

      obtain ⟨φk, hφk⟩ := Spec.map_surjective (τ ≫ t)
      have hτt : τ ≫ t = geomPoint k' φk.hom := by rw [← hφk]; rfl
      let P' : SchemeHomOver (geomPoint k' φk.hom) C.f := GoodReductionJacobian.schemeHomOverComp τ hτt P
      have hP'r : nsmulPt C.L (geomPoint k' φk.hom) r P' = C.L.one _ := by
        apply Subtype.ext
        rw [← comp_nsmulPt C.L t _ τ hτt r P, hPr, comp_one C.L t _ τ hτt]
      have hP'm : ∀ (m : ↥Λ) (n : ℤ), (m : ℍ[ℚ, a, b]) * star (m : ℍ[ℚ, a, b]) = (((r : ℤ) * n : ℚ) : ℍ[ℚ, a, b]) →
          pushPt (C.act m) (C.act_over m) P' = C.L.one (geomPoint k' φk.hom) := by
        intro m n hmn
        apply Subtype.ext
        have := congrArg (fun Q : SchemeHomOver t C.f => τ ≫ Q.1) (hP m n hmn)
        simp only [pushPt, mapPt_coe] at this
        simp only [pushPt, mapPt_coe, P', GoodReductionJacobian.schemeHomOverComp_coe, Category.assoc]
        rw [this, comp_one C.L t _ τ hτt]

      obtain ⟨P₁, ⟨hP₁r, hP₁s⟩, -⟩ :=
        CerednikDrinfeld.QM.FakeEllipticCurve.existsUnique_sectionAt_eq_of_nsmulPt_eq_one (AlgebraicClosure ℚ) C r hr0
          k' φk.hom P' hP'r
      have hP₁s' : geomPoint k' φk.hom ≫ P₁.1 = τ ≫ P.1 := by
        have := congrArg Subtype.val hP₁s
        exact this

      have hP₁m : ∀ (m : ↥Λ) (n : ℤ), (m : ℍ[ℚ, a, b]) * star (m : ℍ[ℚ, a, b]) = (((r : ℤ) * n : ℚ) : ℍ[ℚ, a, b]) →
          pushPt (C.act m) (C.act_over m) P₁ = C.L.one _ := by
        intro m n hmn
        refine section_eq_of_comp_eq C r hrunit _ _ ?_ (nsmulPt_one C.L _ r) (geomPoint k' φk.hom) ?_
        · rw [← CerednikDrinfeld.QM.FakeEllipticCurve.pushPt_act_natCast_eq_nsmulPt C one_mem r r_mem]
          have hrm : (⟨((r : ℚ) : ℍ[ℚ, a, b]), r_mem⟩ : ↥Λ) = ⟨_, r_mem⟩ := rfl

          rw [CerednikDrinfeld.QM.FakeEllipticCurve.pushPt_act_natCast_eq_nsmulPt C one_mem r r_mem]
          show nsmulPt C.L _ r (mapPt (C.act m) (C.act_over m) P₁) = _
          rw [← mapPt_nsmulPt_of_hom C.L C.L (C.act m) (C.act_over m) (C.act_hom m), hP₁r,
            mapPt_one_of_hom C.L C.L (C.act m) (C.act_over m) (C.act_hom m)]
        · have := congrArg Subtype.val (hP'm m n hmn)
          simp only [pushPt, mapPt_coe, P', GoodReductionJacobian.schemeHomOverComp_coe, Category.assoc] at this
          simp only [pushPt, mapPt_coe]
          rw [← Category.assoc, hP₁s', Category.assoc, this, comp_one C.L (𝟙 _) _ _ (Category.comp_id _)]

      obtain ⟨Q₁, hQ₁⟩ := p_pts P₁
      let Hs : Set (SchemeHomOver (𝟙 (Spec (CommRingCat.of (AlgebraicClosure ℚ)))) E.f) :=
        {Q | ∀ (m : ↥Λ) (n : ℤ), (m : ℍ[ℚ, a, b]) * star (m : ℍ[ℚ, a, b]) = (((r : ℤ) * n : ℚ) : ℍ[ℚ, a, b]) →
          pushPt (E.act m) (E.act_over m) Q ∈ H}
      have hQ₁Hs : Q₁ ∈ Hs := by
        intro m n hmn
        rw [← κ_pts, ← p_ker]
        have : mapPt p hp (pushPt (E.act m) (E.act_over m) Q₁) = pushPt (C.act m) (C.act_over m) (mapPt p hp Q₁) :=
          Subtype.ext (by simp only [pushPt, mapPt_coe, Category.assoc, p_act])
        rw [this, hQ₁]
        exact hP₁m m n hmn
      have hH'Hs : H' ⊆ Hs := fun Q hQ m n hmn => hram Q hQ m n hmn

      let CP := {P : SchemeHomOver (𝟙 (Spec (CommRingCat.of (AlgebraicClosure ℚ)))) C.f //
        ∀ (m : ↥Λ) (n : ℤ), (m : ℍ[ℚ, a, b]) * star (m : ℍ[ℚ, a, b]) = (((r : ℤ) * n : ℚ) : ℍ[ℚ, a, b]) →
          pushPt (C.act m) (C.act_over m) P = C.L.one (𝟙 (Spec (CommRingCat.of (AlgebraicClosure ℚ))))}
      have hCP : Nat.card CP = r ^ 2 :=
        CerednikDrinfeld.QM.FakeEllipticCurve.natCard_setOf_forall_pushPt_act_eq_one_of_eq_or_eq hqq' hB Λ hΛ
          (AlgebraicClosure ℚ) C r hr hr0
      haveI : Finite CP := Nat.finite_of_card_ne_zero (by rw [hCP]; exact pow_ne_zero 2 hrprime.ne_zero)
      haveI : Finite ↥H := hHfin.to_subtype
      have hpHs : ∀ Q, Q ∈ Hs → ∀ (m : ↥Λ) (n : ℤ), (m : ℍ[ℚ, a, b]) * star (m : ℍ[ℚ, a, b]) = (((r : ℤ) * n : ℚ) : ℍ[ℚ, a, b]) →
          pushPt (C.act m) (C.act_over m) (mapPt p hp Q) = C.L.one _ := by
        intro Q hQ m n hmn
        have : pushPt (C.act m) (C.act_over m) (mapPt p hp Q) = mapPt p hp (pushPt (E.act m) (E.act_over m) Q) :=
          Subtype.ext (by simp only [pushPt, mapPt_coe, Category.assoc, p_act])
        rw [this, p_ker, κ_pts]
        exact hQ m n hmn
      letI grpE := E.L.pointGroup (𝟙 (Spec (CommRingCat.of (AlgebraicClosure ℚ))))
      letI grpC := C.L.pointGroup (𝟙 (Spec (CommRingCat.of (AlgebraicClosure ℚ))))

      let σ : CP → SchemeHomOver (𝟙 (Spec (CommRingCat.of (AlgebraicClosure ℚ)))) E.f := fun R =>
        if h : ∃ Q, Q ∈ Hs ∧ mapPt p hp Q = R.1 then h.choose else E.L.one _
      have hσ : ∀ Q (hQ : Q ∈ Hs), σ ⟨mapPt p hp Q, hpHs Q hQ⟩ ∈ Hs ∧ mapPt p hp (σ ⟨mapPt p hp Q, hpHs Q hQ⟩) = mapPt p hp Q := by
        intro Q hQ
        have h : ∃ Q', Q' ∈ Hs ∧ mapPt p hp Q' = mapPt p hp Q := ⟨Q, hQ, rfl⟩
        simp only [σ, dif_pos h]
        exact h.choose_spec
      have hkerH : ∀ Q Q', mapPt p hp Q = mapPt p hp Q' → Q * Q'⁻¹ ∈ H := by
        intro Q Q' hQQ'
        rw [← κ_pts, ← p_ker]
        show mapPt p hp (E.L.mul _ Q (E.L.inv _ Q')) = _
        rw [p_hom, mapPt_inv_of_hom E.L C.L p hp p_hom, hQQ']
        exact C.L.mul_inv_cancel _ _
      let ι : ↥Hs → CP × ↥H := fun Q =>
        ⟨⟨mapPt p hp Q.1, hpHs Q.1 Q.2⟩, ⟨Q.1 * (σ ⟨mapPt p hp Q.1, hpHs Q.1 Q.2⟩)⁻¹, hkerH _ _ (hσ Q.1 Q.2).2.symm⟩⟩
      have hι : Function.Injective ι := by
        intro Q Q' h
        simp only [ι, Prod.mk.injEq, Subtype.mk.injEq] at h
        obtain ⟨h1, h2⟩ := h
        apply Subtype.ext
        have : (σ ⟨mapPt p hp Q.1, hpHs Q.1 Q.2⟩) = σ ⟨mapPt p hp Q'.1, hpHs Q'.1 Q'.2⟩ :=
          congrArg σ h1
        rw [this] at h2
        exact mul_right_cancel h2
      haveI : Finite ↥Hs := Finite.of_injective ι hι
      have hcardHs : Nat.card ↥Hs ≤ Nat.card ↥H' := by
        rw [hcard, ← hCP, ← Nat.card_prod]
        exact Nat.card_le_card_of_injective ι hι
      have hHsH' : Hs = H' := by
        haveI : Finite ↥H' := hH'fin.to_subtype
        letI : Fintype ↥Hs := Fintype.ofFinite _
        letI : Fintype ↥H' := Fintype.ofFinite _
        refine (Set.eq_of_subset_of_card_le hH'Hs ?_).symm
        rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card]
        exact hcardHs
      have hQ₁H' : Q₁ ∈ H' := by rw [← hHsH']; exact hQ₁Hs

      have hφP₁ : mapPt φ hφ P₁ = C'.L.one _ := by
        rw [← hQ₁, ← mapPt_comp p hp φ hφ (by rw [Category.assoc, hφ, hp])]
        rw [mapPt_congr (p ≫ φ) p' (by rw [Category.assoc, hφ, hp]) hp' hpφ', p'_ker, κ'_pts]
        exact hQ₁H'
      have := congrArg Subtype.val hφP₁
      simp only [mapPt_coe] at this
      rw [mapPt_coe, ← Category.assoc, ← hP₁s', Category.assoc, this,
        comp_one C'.L (𝟙 _) _ (geomPoint k' φk.hom) (Category.comp_id _), ← comp_one C'.L t _ τ hτt]
  ·
    intro T t P hP
    rw [eq_one_of_factorsThrough_lev C t P hP, mapPt_one_of_hom C.L C'.L φ hφ φ_hom]
    exact C'.lev_one t

end S_CerednikDrinfeld_QM_FakeEllipticCurve_isAtkinLehnerQuotient_of_quotients_of_card_eq_mul_sq
end P2MW
export P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_isAtkinLehnerQuotient_of_quotients_of_card_eq_mul_sq (solution)
