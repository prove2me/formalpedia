-- Prove2me | solution 1 for CerednikDrinfeld.QM.FakeEllipticCurve.FullLevel.existsUnique_comp_eq_of_isPullback_of_isUnit
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.837917+00:00
-- url     : https://prove2.me/submissions/8299e43e-cce9-5c29-9de9-56c0391b9e1e

import Definitions.Def_CerednikDrinfeld_QMFineModuli
import Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_exists_isPullback_levelIff
import Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_smoothOfRelativeDimension_two
import Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_natCard_isTorsionPoint_eq_pow_of_natCast_ne_zero
import Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_eq_of_isTorsionPoint_of_comp_eq
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_FullLevel_existsUnique_comp_eq_of_isPullback_of_isUnit
p2m_attr_erase "instance" "GoodReductionJacobian.RelativeGroupLaw.isIso_endKerStr_schemeHomOverId AlgebraicGeometry.Scheme.PresheafOfModules.symmetricCategory SheafOfModules.instFaithfulRingSheafPModToPMod SheafOfModules.symmetricCategory AlgebraicGeometry.Scheme.PresheafOfModules.monoidalCategory AlgebraicGeometry.Scheme.PresheafOfModules.monoidalClosed SheafOfModules.instFullRingSheafPModToPMod SheafOfModules.monoidalCategory AlgebraicGeometry.Scheme.Modules.symmetricCategory SheafOfModules.monoidalClosed SheafOfModules.instIsLocalizationPModRingSheafSheafifyFunctorPresheafW SheafOfModules.sheafifyFunctor_monoidal AlgebraicGeometry.Scheme.Modules.monoidalClosed AlgebraicGeometry.instMonoidalPresheafOfModulesModulesSheafify AlgebraicGeometry.Scheme.Modules.monoidalCategory PresheafOfModules.instMonoidalClosed PresheafOfModules.InternalHom.instModuleCarrierObjOppositeCommRingCatSubtypePiFamilyMemAddSubgroupNaturalFamilies PresheafOfModules.InternalHom.instModuleCarrierObjOppositeRingCatCompCommRingCatForget₂RingHomCarrierCarrierAbPresheaf PresheafOfModules.InternalHom.instSMulCarrierObjOppositeCommRingCatSubtypePiFamilyMemAddSubgroupNaturalFamilies AlgebraicGeometry.Scheme.Hom.opensMapFinal AlgebraicGeometry.RelPicard.RigidifiedLineBundle.setoid AlgebraicGeometry.RelPicard.RigidifiedLineBundle.instInhabited AlgebraicGeometry.OModulePresheaf.isScalarTower AlgebraicGeometry.Scheme.OrderedAffineCover.instLinearOrder AlgebraicGeometry.OModulePresheaf.module AlgebraicGeometry.Scheme.OrderedAffineCover.instFintype AlgebraicGeometry.Scheme.OrderedAffineCover.instFintypeIdx AlgebraicGeometry.OModulePresheaf.addCommGroup AlgebraicGeometry.Scheme.OrderedAffineCover.instDecidableEqIdx AlgebraicGeometry.OModulePresheaf.moduleSections TwoChartCech.Sections.M0_moduleA TwoChartCech.Sections.M1_module TwoChartCech.Cover.A01_algebra TwoChartCech.Cover.A0_algebra TwoChartCech.Cover.A1_commRing TwoChartCech.Cover.A1_algebra TwoChartCech.Sections.M01_module TwoChartCech.Sections.M0_addCommGroup TwoChartCech.Sections.M0_tower TwoChartCech.Sections.M01_addCommGroup"
p2m_attr_erase "instance" "TwoChartCech.Cover.A0_commRing TwoChartCech.Sections.M1_tower TwoChartCech.Sections.M01_moduleA TwoChartCech.Sections.M0_module TwoChartCech.Sections.M1_moduleA TwoChartCech.Sections.M1_addCommGroup TwoChartCech.Cover.A01_commRing TwoChartCech.Sections.M01_tower CoherentBaseChange.TwoTermComplex.C0_module CoherentBaseChange.TwoTermComplex.C0_addCommGroup CoherentBaseChange.TwoTermComplex.C1_module CoherentBaseChange.TwoTermComplex.C1_addCommGroup CoherentBaseChange.TwoTermComplex.C0_free CoherentBaseChange.TwoTermComplex.C1_finite CoherentBaseChange.TwoTermComplex.C0_finite CoherentBaseChange.TwoTermComplex.C1_free AlgebraicGeometry.OModulePresheaf.instSubsingletonObjZero AlgebraicGeometry.Scheme.Modules.preservesBinaryProducts_opensMap AlgebraicGeometry.Scheme.Modules.pullback_monoidal AlgebraicGeometry.Scheme.Modules.sheafify_isLocalization' AlgebraicGeometry.Scheme.Modules.preservesTerminal_opensMap AlgebraicGeometry.Scheme.Modules.pullback₀_monoidal AlgebraicGeometry.Scheme.Modules.preservesFiniteProducts_opensMap AlgebraicGeometry.Scheme.Modules.instLiftingPresheafOfModulesSheafifyPresheafWOpensCarrierCarrierCommRingCatGrothendieckTopologyObjFunctorOppositeIsSheafSheafCompPullback₀Pullback PresheafOfModules.PullbackMonoidal.pullback_monoidal PresheafOfModules.PullbackMonoidal.isIso_δ PresheafOfModules.pushforward_laxMonoidal PresheafOfModules.PullbackMonoidal.isIso_η PresheafOfModules.free_monoidal PresheafOfModules.restrictScalars_laxMonoidal PresheafOfModules.PullbackMonoidal.isIso_δ_gS PresheafOfModules.pullback_oplaxMonoidal PresheafOfModules.PullbackMonoidal.instPreservesColimitsOfSizeCompOppositeCommRingCatRingCatForget₂RingHomCarrierCarrierPb PresheafOfModules.pullback_monoidal' AlgebraicGeometry.SmoothOfRelativeDimension.fiberToSpecResidueField AlgebraicGeometry.SmoothOfRelativeDimension.pullback_snd AlgebraicGeometry.SmoothOfRelativeDimension.pullback_fst AlgebraicGeometry.SmoothOfRelativeDimension.smooth_one AlgebraicGeometry.SmoothProperCurve.isIntegral_pullback_Spec_field AlgebraicGeometry.IsProper.fiberToSpecResidueField"
p2m_attr_erase "instance" "AlgebraicCurve.CurveModel.isProper AlgebraicCurve.CurveModel.isIntegral AlgebraicCurve.CurveModel.smooth AlgebraicGeometry.Scheme.LocalRepresentabilityULift.instIsLocallyInjectiveFunUliftYonedaGluedToSheaf AlgebraicGeometry.Scheme.LocalRepresentabilityULift.instIsLocallySurjectiveFunUliftYonedaGluedToSheafOfIsLocallySurjectiveZariskiTopologyDescFunctorOppositeType AlgebraicGeometry.Scheme.LocalRepresentabilityULift.instIsOpenImmersionToGlued AlgebraicGeometry.Scheme.LocalRepresentabilityULift.instIsIsoSheafZariskiTopologyTypeUliftYonedaGluedToSheaf AlgebraicGeometry.RelPicard.instIsOpenImmersionToGlued AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.instFundamentalIdentityOfSumRamificationInertia AlgebraicCurve.Place.instIsScalarTowerResidueFieldRestrictPushforward AlgebraicCurve.Place.instAlgebraResidueFieldRestrictPushforward AlgebraicCurve.Place.instIsLocalHomRestrictInclusion AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions PresheafOfModules.ExteriorPower.instModulePresheafAb AlgebraicGeometry.RelEffCartierDiv.subsingleton_of_degree_zero AlgebraicGeometry.RelEffCartierDiv.isIso_subschemeIota_snd_of_degree_one AlgebraicGeometry.isIso_ker_graphOver_subschemeIota_snd AlgebraicGeometry.isClosedImmersion_graphOver AlgebraicGeometry.FGSubalgebra.instIsDirectedLe AlgebraicGeometry.FGSubalgebra.instQuasiSeparatedSpaceCarrierCarrierCommRingCatObjOppositeSchemeSpecDiagram AlgebraicGeometry.FGSubalgebra.instIsCofilteredOpposite AlgebraicGeometry.FGSubalgebra.instIsAffineObjOppositeSchemeSpecDiagram AlgebraicGeometry.FGSubalgebra.instNonempty AlgebraicGeometry.FGSubalgebra.instNonemptySubtypeLeSubalgebraValFG AlgebraicGeometry.FGSubalgebra.instCompactSpaceCarrierCarrierCommRingCatObjOppositeSchemeSpecDiagram AlgebraicGeometry.FGSubalgebra.instIsDirectedSubtypeLeSubalgebraValFG AlgebraicGeometry.FGSubalgebra.instIsAffineHomMapOppositeSchemeSpecDiagram AlgebraicGeometry.FGSubalgebra.instIsFiltered AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instNeg AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instSMulInt AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instAddCommGroup AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instAdd AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instSub"
p2m_attr_erase "instance" "AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instModuleCarrierObjOppositeOpensCarrierCarrierCommRingCatPresheafOpOpensTop AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instSMulCarrierObjOppositeOpensCarrierCarrierCommRingCatPresheafOpOpensTop AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instSMulNat AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instZero AlgebraicCurve.instHasLocalResidue_of_hasCanonicalLocalResidueK AlgebraicCurve.instHasCanonicalLocalResidueK_of_hasCanonicalLocalResidueKStar AlgebraicCurve.Place.kw_ffgc_finiteDimensional_adicCompletion instAlgebraSubtypeMemValuationSubring_definitions AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersIntegersCompletion ModularCurve.KwF4gRRTate.instAlgebraKAdicCompletionIntegers AlgebraicCurve.Place.kw_ffgc_continuousSMul_adicCompletionComap AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersCompletionCompletion IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions AlgebraicCurve.instHasCanonicalLocalResidueK AlgebraicCurve.Place.instAlgebra_restrictResidueField AlgebraicCurve.Place.instIsScalarTower_restrictResidueField AlgebraicCurve.instHasLocalResidue AlgebraicCurve.HasSeparableResidue.of_perfectField_of_isCurveOver AlgebraicCurve.HasSeparableResidue.of_perfectField AlgebraicCurve.Place.instIsLocalHom_restrictSubringHom AlgebraicCurve.instHasCanonicalLocalResidueKStar ModularCurve.KwNo6Pin.isLocalRing_completion SheafOfModules.isIso_ihomModelToIhom AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instDecidableEqIdx AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instFintype AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instLinearOrder AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instFintypeIdx AlgebraicGeometry.OModulePresheaf.Leray.relAltC_scalarTower AlgebraicGeometry.OModulePresheaf.Leray.ker_relAltd_modΓ AlgebraicGeometry.OModulePresheaf.Leray.relAltC_modΓ AlgebraicGeometry.OModulePresheaf.Leray.biC_abGrp AlgebraicGeometry.OModulePresheaf.Leray.relAltH_modΓ AlgebraicGeometry.OModulePresheaf.Leray.ker_relAltd_smul AlgebraicGeometry.OModulePresheaf.Leray.relAltH_scalarTower AlgebraicGeometry.OModulePresheaf.Leray.relAltH_smul"
p2m_attr_erase "instance" "AlgebraicGeometry.OModulePresheaf.Leray.biC_module DoubleComplex.instModuleE₂I DoubleComplex.Bounded.modR DoubleComplex.instModuleE₂II DoubleComplex.instAddCommGroupE₂II DoubleComplex.Bounded.abGrp DoubleComplex.instAddCommGroupE₂I AlgebraicGeometry.ChowDatum.hι_closed AlgebraicGeometry.ChowDatumProj.hιN_closed AlgebraicGeometry.ChowDatumProj.hp_proper AlgebraicGeometry.ChowDatum.hp_isoU AlgebraicGeometry.ChowDatum.hp_proper AlgebraicGeometry.ProjSpace.algebraAway AlgebraicGeometry.ProjSpace.instIsProperProdOverπ AlgebraicGeometry.ChowDatumProj.hp_isoU AlgebraicGeometry.ProjSpace.isProper_π AlgebraicGeometry.ProjSpace.finiteType_mvPolynomial ProjSpaceCech.GradedModule.H.module ProjSpaceCech.GradedModule.H.addCommGroup ProjSpaceCech.GradedModule.sec.instAdd ProjSpaceCech.GradedModule.sec.instNeg ProjSpaceCech.GradedModule.acg ProjSpaceCech.GradedModule.Frac.setoid ProjSpaceCech.GradedModule.modR ProjSpaceCech.GradedModule.sec.instModule ProjSpaceCech.GradedModule.sec.instAddCommGroup ProjSpaceCech.GradedModule.sec.instZero ProjSpaceCech.GradedModule.Presentation.fJ ProjSpaceCech.GradedModule.sec.instSMul ProjSpaceCech.Twist.H.module ProjSpaceCech.Idx.instFintype ProjSpaceCech.Twist.H.addCommGroup ProjSpaceCech.Idx.instDecidableEq ProjSpaceCech.Twist.Mon.instDecidableEq ProjSpaceCech.Twist.cochain.instAddCommGroup ProjSpaceCech.Twist.cochain.instModule AlgebraicGeometry.FGSubalgebra.tensorStage_directedSystem AlgebraicGeometry.RelEffCartierDiv.isClosedImmersion_subschemeι_resProdMap AlgebraicGeometry.RelEffCartierDiv.isOpenImmersion_resProdMap AlgebraicCurve.CurveModel.locallyOfFiniteType_gluedToBase"
p2m_attr_erase "instance" "AlgebraicCurve.CurveModel.isFractionRing_overlap AlgebraicCurve.CurveModel.isLocallyNoetherian_glued AlgebraicCurve.CurveModel.jacobsonSpace_glued AlgebraicCurve.CurveModel.isOpenImmersion_ι₀ AlgebraicCurve.CurveModel.isIntegral_glued AlgebraicCurve.CurveModel.quasiSeparated_gluedToBase AlgebraicCurve.CurveModel.compactSpace_glued AlgebraicCurve.CurveModel.isIntegral_adjoin_chartRing AlgebraicCurve.CurveModel.isFractionRing_overlap_functionField AlgebraicCurve.CurveModel.isProper_gluedToBase AlgebraicCurve.CurveModel.isOpenImmersion_ιU AlgebraicCurve.CurveModel.isOpenImmersion_f₀ AlgebraicCurve.CurveModel.isOpenImmersion_fInf AlgebraicCurve.CurveModel.isOpenImmersion_ιInf AlgebraicCurve.CurveModel.algebra_overlap_functionField AlgebraicCurve.CurveModel.quasiCompact_gluedToBase AlgebraicCurve.CurveModel.algebraAdjoin AlgebraicCurve.CurveModel.isDedekindDomain_chartRing AlgebraicCurve.CurveModel.isIntegralClosure AlgebraicCurve.CurveModel.finite_chartRing AlgebraicCurve.CurveModel.centre_isPrime AlgebraicCurve.CurveModel.isFractionRing_chartRing AlgebraicCurve.CurveModel.finiteType_chartRing AlgebraicCurve.CurveModel.isNoetherianRing_chartRing AlgebraicCurve.CurveModel.isScalarTower_base_adjoin AlgebraicCurve.CurveModel.isScalarTower_adjoin AlgebraicCurve.CurveModel.chartRing_finitePresentation instTopologicallyFGOfFiniteType AlgebraicGeometry.ProjSpace.twistObj.addCommGroup AlgebraicGeometry.ProjSpace.twistFam.module AlgebraicGeometry.ProjSpace.twistObj.module AlgebraicGeometry.ProjSpace.twistObj.moduleSections AlgebraicGeometry.ProjSpace.twistFam.addCommGroup"
p2m_attr_erase "simp" "GoodReductionJacobian.RelativeGroupLaw.baseChangePointToBase_ofBase GoodReductionJacobian.RelativeGroupLaw.baseChangePointToBase_coe GoodReductionJacobian.RelativeGroupLaw.baseChangePointOfBase_coe GoodReductionJacobian.RelativeGroupLaw.baseChange_inv GoodReductionJacobian.RelativeGroupLaw.baseChangePointOfBase_toBase GoodReductionJacobian.RelativeGroupLaw.baseChange_mul GoodReductionJacobian.RelativeGroupLaw.baseChange_one NeronModelInfra.NeronModelPropertyBundle.endExtensionEquiv_symm_restrict NeronModelInfra.schemeHomOverComp_id_left NeronModelInfra.schemeHomOverComp_id_right NeronModelInfra.schemeHomOverId_coe NeronModelInfra.NeronModelPropertyBundle.endExtensionEquiv_apply NeronModelInfra.NeronModelPropertyBundle.restrict_endExtensionEquiv_symm NeronModelInfra.schemeHomOverComp_coe NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_fst NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_snd NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_fst NeronSpecialFibreInfra.neronEndRestrictEquiv_apply NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_fst_assoc NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_snd NeronSpecialFibreInfra.neronEndExtension_genericFibreRestrict NeronSpecialFibreInfra.specClosedFibreInclusion_eq NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_fst_assoc NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_snd_assoc NeronSpecialFibreInfra.genericFibreRestrict_neronEndExtension NeronSpecialFibreInfra.homOverId_coe NeronSpecialFibreInfra.homOverComp_coe NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_snd_assoc GoodReductionJacobian.RelativeGroupLaw.fibre_inv GoodReductionJacobian.RelativeGroupLaw.fibrePointToBase_coe GoodReductionJacobian.RelativeGroupLaw.fibrePointOfBase_toBase GoodReductionJacobian.RelativeGroupLaw.fibre_mul GoodReductionJacobian.RelativeGroupLaw.fibrePointToBase_ofBase GoodReductionJacobian.RelativeGroupLaw.fibre_one GoodReductionJacobian.RelativeGroupLaw.fibrePointOfBase_coe AlgebraicGeometry.schemeFibreEndo_snd AlgebraicGeometry.schemeFibreEndo_fst RegularLocalRingQuotientAscent.dualNumberFst_apply NeronModelInfra.schemeHomOverNpow_succ NeronModelInfra.schemeHomOverNpow_zero"
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

noncomputable section

open scoped TensorProduct Quaternion NumberField
p2m_open "CategoryTheory CategoryTheory.Limits AlgebraicGeometry QuaternionAlgebra CerednikDrinfeld P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_FullLevel_existsUnique_comp_eq_of_isPullback_of_isUnit.CerednikDrinfeld CerednikDrinfeld.QM P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_FullLevel_existsUnique_comp_eq_of_isPullback_of_isUnit.CerednikDrinfeld.QM NeronModelInfra~schemeHomOverComp~schemeHomOverComp_coe GoodReductionJacobian CerednikDrinfeld.QM.FakeEllipticCurve P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_FullLevel_existsUnique_comp_eq_of_isPullback_of_isUnit.CerednikDrinfeld.QM.FakeEllipticCurve"

universe u

namespace CerednikDrinfeld
p2m_export "CerednikDrinfeld" "QM.FakeEllipticCurve.FullLevel QM.FakeEllipticCurve QM.FakeEllipticCurve.exists_isPullback_levelIff QM.FakeEllipticCurve.smoothOfRelativeDimension_two"
namespace QM
p2m_export "CerednikDrinfeld.QM" "FakeEllipticCurve.FullLevel pushPt nsmulPt geomPoint FakeEllipticCurve FakeEllipticCurve.exists_isPullback_levelIff FakeEllipticCurve.smoothOfRelativeDimension_two"
namespace FakeEllipticCurve
p2m_export "CerednikDrinfeld.QM.FakeEllipticCurve" "sectionAt FullLevel IsPullback A f mk act_hom comm act L act_add act_over bundle exists_isPullback_levelIff smoothOfRelativeDimension_two"
namespace R4LevelExtends
p2m_open "CerednikDrinfeld.QM.FakeEllipticCurve CerednikDrinfeld.QM CerednikDrinfeld"

variable {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} {N : ℕ}

section OneCurve

variable {S : Type u} [CommRing S] (F : FakeEllipticCurve Λ N S)

theorem nsmulPt_eq_nsmul {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of S)) (n : ℕ) (P : SchemeHomOver t F.f) :
    nsmulPt F.L t n P = F.L.nsmul t n P := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [RelativeGroupLaw.nsmul_succ, ← ih]
      rfl

theorem eq_one_of_mul_self_eq {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of S)) (x : SchemeHomOver t F.f)
    (h : F.L.mul t x x = x) : x = F.L.one t := by
  calc x = F.L.mul t (F.L.one t) x := (F.L.one_mul t x).symm
    _ = F.L.mul t (F.L.mul t (F.L.inv t x) x) x := by rw [F.L.inv_mul_cancel]
    _ = F.L.mul t (F.L.inv t x) (F.L.mul t x x) := by rw [F.L.mul_assoc]
    _ = F.L.mul t (F.L.inv t x) x := by rw [h]
    _ = F.L.one t := F.L.inv_mul_cancel t x

theorem mul_left_cancel' {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of S)) (c x y : SchemeHomOver t F.f)
    (h : F.L.mul t c x = F.L.mul t c y) : x = y := by
  calc x = F.L.mul t (F.L.one t) x := (F.L.one_mul t x).symm
    _ = F.L.mul t (F.L.mul t (F.L.inv t c) c) x := by rw [F.L.inv_mul_cancel]
    _ = F.L.mul t (F.L.inv t c) (F.L.mul t c x) := by rw [F.L.mul_assoc]
    _ = F.L.mul t (F.L.inv t c) (F.L.mul t c y) := by rw [h]
    _ = F.L.mul t (F.L.mul t (F.L.inv t c) c) y := by rw [F.L.mul_assoc]
    _ = y := by rw [F.L.inv_mul_cancel, F.L.one_mul]

abbrev actPt (x : ↥Λ) {T : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of S)} (P : SchemeHomOver t F.f) :
    SchemeHomOver t F.f :=
  pushPt (F.act x) (F.act_over x) P

@[scoped simp] theorem actPt_coe (x : ↥Λ) {T : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of S)} (P : SchemeHomOver t F.f) :
    (actPt F x P).1 = P.1 ≫ F.act x := rfl

theorem actPt_mul (x : ↥Λ) {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of S)) (P Q : SchemeHomOver t F.f) :
    actPt F x (F.L.mul t P Q) = F.L.mul t (actPt F x P) (actPt F x Q) :=
  F.act_hom x t P Q

theorem actPt_one (x : ↥Λ) {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of S)) :
    actPt F x (F.L.one t) = F.L.one t := by
  apply eq_one_of_mul_self_eq F t
  rw [← actPt_mul, F.L.one_mul]

theorem actPt_nsmulPt (x : ↥Λ) {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of S)) (n : ℕ)
    (P : SchemeHomOver t F.f) :
    actPt F x (nsmulPt F.L t n P) = nsmulPt F.L t n (actPt F x P) := by
  induction n with
  | zero => exact actPt_one F x t
  | succ n ih =>
      show actPt F x (F.L.mul t (nsmulPt F.L t n P) P) = F.L.mul t (nsmulPt F.L t n (actPt F x P)) (actPt F x P)
      rw [actPt_mul, ih]

theorem actPt_add (x y : ↥Λ) {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of S)) (P : SchemeHomOver t F.f) :
    actPt F (x + y) P = F.L.mul t (actPt F x P) (actPt F y P) :=
  F.act_add x y t P

theorem actPt_zero {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of S)) (P : SchemeHomOver t F.f) :
    actPt F 0 P = F.L.one t := by
  apply eq_one_of_mul_self_eq F t
  have h := actPt_add F 0 0 t P
  simp only [add_zero] at h
  exact h.symm

theorem actPt_natSmul (n : ℕ) (y : ↥Λ) {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of S))
    (P : SchemeHomOver t F.f) :
    actPt F (n • y) P = nsmulPt F.L t n (actPt F y P) := by
  induction n with
  | zero => rw [zero_smul]; exact actPt_zero F t P
  | succ n ih =>
      rw [succ_nsmul, actPt_add, ih]
      rfl

def MΛ (Λ : Submodule ℤ ℍ[ℚ, a, b]) (m : ℕ) : AddSubgroup ↥Λ where
  carrier := {x | ∃ y : ↥Λ, (x : ℍ[ℚ, a, b]) = (m : ℚ) • (y : ℍ[ℚ, a, b])}
  zero_mem' := ⟨0, by simp⟩
  add_mem' := by
    rintro x x' ⟨y, hy⟩ ⟨y', hy'⟩
    refine ⟨y + y', ?_⟩
    rw [Submodule.coe_add, Submodule.coe_add, hy, hy', smul_add]
  neg_mem' := by
    rintro x ⟨y, hy⟩
    refine ⟨-y, ?_⟩
    rw [Submodule.coe_neg, Submodule.coe_neg, hy, smul_neg]

theorem mem_MΛ_iff (m : ℕ) (x : ↥Λ) :
    x ∈ MΛ Λ m ↔ ∃ y : ↥Λ, (x : ℍ[ℚ, a, b]) = (m : ℚ) • (y : ℍ[ℚ, a, b]) :=
  Iff.rfl

theorem eq_natSmul_of_mem_MΛ {m : ℕ} {x : ↥Λ} (hx : x ∈ MΛ Λ m) : ∃ y : ↥Λ, x = m • y := by
  obtain ⟨y, hy⟩ := hx
  refine ⟨y, Subtype.ext ?_⟩
  rw [hy, Submodule.coe_smul_of_tower, Nat.cast_smul_eq_nsmul]

theorem actPt_eq_one_of_mem_MΛ {m : ℕ} {x : ↥Λ} (hx : x ∈ MΛ Λ m) {T : Scheme.{u}}
    (t : T ⟶ Spec (CommRingCat.of S)) (P : SchemeHomOver t F.f) (hP : nsmulPt F.L t m P = F.L.one t) :
    actPt F x P = F.L.one t := by
  obtain ⟨y, rfl⟩ := eq_natSmul_of_mem_MΛ hx
  rw [actPt_natSmul, ← actPt_nsmulPt, hP, actPt_one]

theorem res_one {T T' : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of S)) (t' : T' ⟶ Spec (CommRingCat.of S))
    (ψ : T' ⟶ T) (hψ : ψ ≫ t = t') :
    GoodReductionJacobian.schemeHomOverComp ψ hψ (F.L.one t) = F.L.one t' :=
  F.L.one_natural t t' ψ hψ

theorem res_nsmulPt {T T' : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of S)) (t' : T' ⟶ Spec (CommRingCat.of S))
    (ψ : T' ⟶ T) (hψ : ψ ≫ t = t') (n : ℕ) (P : SchemeHomOver t F.f) :
    GoodReductionJacobian.schemeHomOverComp ψ hψ (nsmulPt F.L t n P) =
      nsmulPt F.L t' n (GoodReductionJacobian.schemeHomOverComp ψ hψ P) := by
  rw [nsmulPt_eq_nsmul, nsmulPt_eq_nsmul]
  exact F.L.nsmul_natural t t' ψ hψ n P

theorem res_actPt {T T' : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of S)) (t' : T' ⟶ Spec (CommRingCat.of S))
    (ψ : T' ⟶ T) (hψ : ψ ≫ t = t') (x : ↥Λ) (P : SchemeHomOver t F.f) :
    GoodReductionJacobian.schemeHomOverComp ψ hψ (actPt F x P) =
      actPt F x (GoodReductionJacobian.schemeHomOverComp ψ hψ P) :=
  Subtype.ext (Category.assoc _ _ _).symm

theorem sectionAt_torsion {m : ℕ} (P : SchemeHomOver (𝟙 (Spec (CommRingCat.of S))) F.f)
    (hP : nsmulPt F.L (𝟙 _) m P = F.L.one _) (k : Type u) [Field k] (sk : S →+* k) :
    nsmulPt F.L (geomPoint k sk) m (sectionAt P k sk) = F.L.one (geomPoint k sk) := by
  unfold sectionAt
  rw [← res_nsmulPt, hP, res_one]

theorem sectionAt_actPt (x : ↥Λ) (P : SchemeHomOver (𝟙 (Spec (CommRingCat.of S))) F.f)
    (k : Type u) [Field k] (sk : S →+* k) :
    sectionAt (actPt F x P) k sk = actPt F x (sectionAt P k sk) :=
  res_actPt F _ _ _ _ x P

theorem sectionAt_one (k : Type u) [Field k] (sk : S →+* k) :
    sectionAt (F.L.one (𝟙 (Spec (CommRingCat.of S)))) k sk = F.L.one (geomPoint k sk) :=
  res_one F _ _ _ _

theorem natCast_ne_zero_of_isUnit {m : ℕ} (hm : IsUnit ((m : ℕ) : S)) (k : Type u) [Field k] (sk : S →+* k) :
    (m : k) ≠ 0 := by
  have h := hm.map sk
  rw [map_natCast] at h
  exact h.ne_zero

end OneCurve

section BaseChange

variable {S S' : Type u} [CommRing S] [CommRing S'] {φ : S →+* S'}
  {E : FakeEllipticCurve Λ N S} {E' : FakeEllipticCurve Λ N S'}
  {g : E'.A ⟶ E.A} (hg : CategoryTheory.IsPullback g E'.f E.f (Spec.map (CommRingCat.ofHom φ)))

def bcPt {T : Scheme.{u}} {t' : T ⟶ Spec (CommRingCat.of S')} {t : T ⟶ Spec (CommRingCat.of S)}
    (ht : t' ≫ Spec.map (CommRingCat.ofHom φ) = t) (P : SchemeHomOver t' E'.f) : SchemeHomOver t E.f :=
  ⟨P.1 ≫ g, by rw [Category.assoc, hg.w, ← Category.assoc, P.2, ht]⟩

@[scoped simp] theorem bcPt_coe {T : Scheme.{u}} {t' : T ⟶ Spec (CommRingCat.of S')} {t : T ⟶ Spec (CommRingCat.of S)}
    (ht : t' ≫ Spec.map (CommRingCat.ofHom φ) = t) (P : SchemeHomOver t' E'.f) : (bcPt hg ht P).1 = P.1 ≫ g :=
  rfl

theorem bcPt_injective {T : Scheme.{u}} {t' : T ⟶ Spec (CommRingCat.of S')} {t : T ⟶ Spec (CommRingCat.of S)}
    (ht : t' ≫ Spec.map (CommRingCat.ofHom φ) = t) : Function.Injective (bcPt hg ht (E := E) (E' := E')) := by
  intro P Q h
  apply Subtype.ext
  apply hg.hom_ext
  · exact congrArg Subtype.val h
  · rw [P.2, Q.2]

theorem bcPt_surjective {T : Scheme.{u}} {t' : T ⟶ Spec (CommRingCat.of S')} {t : T ⟶ Spec (CommRingCat.of S)}
    (ht : t' ≫ Spec.map (CommRingCat.ofHom φ) = t) : Function.Surjective (bcPt hg ht (E := E) (E' := E')) := by
  intro Q
  have w : Q.1 ≫ E.f = t' ≫ Spec.map (CommRingCat.ofHom φ) := by rw [Q.2, ht]
  refine ⟨⟨hg.lift Q.1 t' w, hg.lift_snd _ _ _⟩, Subtype.ext ?_⟩
  exact hg.lift_fst _ _ _

def bcEquiv {T : Scheme.{u}} {t' : T ⟶ Spec (CommRingCat.of S')} {t : T ⟶ Spec (CommRingCat.of S)}
    (ht : t' ≫ Spec.map (CommRingCat.ofHom φ) = t) : SchemeHomOver t' E'.f ≃ SchemeHomOver t E.f :=
  Equiv.ofBijective (bcPt hg ht) ⟨bcPt_injective hg ht, bcPt_surjective hg ht⟩

variable
  (hg_mul : ∀ {T : Scheme.{u}} (t' : T ⟶ Spec (CommRingCat.of S')) (P Q : SchemeHomOver t' E'.f),
      (E'.L.mul t' P Q).1 ≫ g =
        (E.L.mul (t' ≫ Spec.map (CommRingCat.ofHom φ))
          ⟨P.1 ≫ g, by rw [Category.assoc, hg.w, ← Category.assoc, P.2]⟩
          ⟨Q.1 ≫ g, by rw [Category.assoc, hg.w, ← Category.assoc, Q.2]⟩).1)

include hg_mul in
theorem bcPt_mul {T : Scheme.{u}} {t' : T ⟶ Spec (CommRingCat.of S')} {t : T ⟶ Spec (CommRingCat.of S)}
    (ht : t' ≫ Spec.map (CommRingCat.ofHom φ) = t) (P Q : SchemeHomOver t' E'.f) :
    bcPt hg ht (E'.L.mul t' P Q) = E.L.mul t (bcPt hg ht P) (bcPt hg ht Q) := by
  subst ht
  exact Subtype.ext (hg_mul t' P Q)

include hg_mul in
theorem bcPt_one {T : Scheme.{u}} {t' : T ⟶ Spec (CommRingCat.of S')} {t : T ⟶ Spec (CommRingCat.of S)}
    (ht : t' ≫ Spec.map (CommRingCat.ofHom φ) = t) :
    bcPt hg ht (E'.L.one t') = E.L.one t := by
  apply eq_one_of_mul_self_eq E t
  rw [← bcPt_mul hg hg_mul, E'.L.one_mul]

include hg_mul in
theorem bcPt_nsmulPt {T : Scheme.{u}} {t' : T ⟶ Spec (CommRingCat.of S')} {t : T ⟶ Spec (CommRingCat.of S)}
    (ht : t' ≫ Spec.map (CommRingCat.ofHom φ) = t) (n : ℕ) (P : SchemeHomOver t' E'.f) :
    bcPt hg ht (nsmulPt E'.L t' n P) = nsmulPt E.L t n (bcPt hg ht P) := by
  induction n with
  | zero => exact bcPt_one hg hg_mul ht
  | succ n ih =>
      show bcPt hg ht (E'.L.mul t' (nsmulPt E'.L t' n P) P) = E.L.mul t (nsmulPt E.L t n (bcPt hg ht P)) (bcPt hg ht P)
      rw [bcPt_mul hg hg_mul, ih]

include hg_mul in

theorem bcPt_torsion_iff {T : Scheme.{u}} {t' : T ⟶ Spec (CommRingCat.of S')} {t : T ⟶ Spec (CommRingCat.of S)}
    (ht : t' ≫ Spec.map (CommRingCat.ofHom φ) = t) (n : ℕ) (P : SchemeHomOver t' E'.f) :
    nsmulPt E'.L t' n P = E'.L.one t' ↔ nsmulPt E.L t n (bcPt hg ht P) = E.L.one t := by
  constructor
  · intro h
    rw [← bcPt_nsmulPt hg hg_mul, h, bcPt_one hg hg_mul]
  · intro h
    apply bcPt_injective hg ht
    rw [bcPt_nsmulPt hg hg_mul, h, bcPt_one hg hg_mul]

theorem bcPt_actPt (hg_act : ∀ x : ↥Λ, E'.act x ≫ g = g ≫ E.act x)
    {T : Scheme.{u}} {t' : T ⟶ Spec (CommRingCat.of S')} {t : T ⟶ Spec (CommRingCat.of S)}
    (ht : t' ≫ Spec.map (CommRingCat.ofHom φ) = t) (x : ↥Λ) (P : SchemeHomOver t' E'.f) :
    bcPt hg ht (actPt E' x P) = actPt E x (bcPt hg ht P) := by
  apply Subtype.ext
  simp only [bcPt_coe, actPt_coe, Category.assoc, hg_act x]

end BaseChange

section Count

variable {S : Type u} [CommRing S]

abbrev TorsAt (F : FakeEllipticCurve Λ N S) (k : Type u) [Field k] (sk : S →+* k) (m : ℕ) : Type u :=
  {Q : SchemeHomOver (geomPoint k sk) F.f // nsmulPt F.L (geomPoint k sk) m Q = F.L.one (geomPoint k sk)}

theorem natCard_torsAt (F : FakeEllipticCurve Λ N S) (k : Type u) [Field k] [IsAlgClosed k] (sk : S →+* k)
    (m : ℕ) (hm : (m : k) ≠ 0) : Nat.card (TorsAt F k sk m) = m ^ 4 := by
  obtain ⟨Fk, gk, hgk, hmul, -, -, -⟩ := FakeEllipticCurve.exists_isPullback_levelIff sk F
  haveI := FakeEllipticCurve.smoothOfRelativeDimension_two k Fk
  have hcard := GoodReductionJacobian.RelativeGroupLaw.natCard_isTorsionPoint_eq_pow_of_natCast_ne_zero k Fk.f Fk.L
    Fk.comm Fk.bundle 2 m hm
  have ht : 𝟙 _ ≫ Spec.map (CommRingCat.ofHom sk) = geomPoint k sk := Category.id_comp _
  rw [show m ^ 4 = m ^ (2 * 2) by norm_num, ← hcard]
  symm
  refine Nat.card_congr ((bcEquiv hgk ht).subtypeEquiv ?_)
  intro Q
  show Fk.L.nsmul _ m Q = _ ↔ _
  rw [← nsmulPt_eq_nsmul]
  exact bcPt_torsion_iff hgk hmul ht m Q

end Count

section LevelMap

variable {S : Type u} [CommRing S] (F : FakeEllipticCurve Λ N S) {m : ℕ}
  (P : SchemeHomOver (𝟙 (Spec (CommRingCat.of S))) F.f) (hP : nsmulPt F.L (𝟙 _) m P = F.L.one _)
  (k : Type u) [Field k] (sk : S →+* k)
  (hann : ∀ x : ↥Λ, actPt F x (sectionAt P k sk) = F.L.one (geomPoint k sk) ↔ x ∈ MΛ Λ m)

include hP in

def levelMap (x : ↥Λ) : TorsAt F k sk m :=
  ⟨actPt F x (sectionAt P k sk), by rw [← actPt_nsmulPt, sectionAt_torsion F P hP k sk, actPt_one]⟩

include hP hann in
theorem levelMap_eq_iff (x y : ↥Λ) : levelMap F P hP k sk x = levelMap F P hP k sk y ↔ -x + y ∈ MΛ Λ m := by
  rw [← hann]
  constructor
  · intro h
    have h' : actPt F x (sectionAt P k sk) = actPt F y (sectionAt P k sk) := congrArg Subtype.val h
    have h1 : actPt F (-x + y) (sectionAt P k sk) =
        F.L.mul _ (actPt F (-x) (sectionAt P k sk)) (actPt F x (sectionAt P k sk)) := by
      rw [actPt_add, h']
    rw [h1, ← actPt_add, neg_add_cancel, actPt_zero]
  · intro h
    apply Subtype.ext
    show actPt F x (sectionAt P k sk) = actPt F y (sectionAt P k sk)
    have hy : y = x + (-x + y) := by abel
    rw [hy, actPt_add F x (-x + y), h, F.L.mul_one]

include hP hann in

def levelMapBar : ↥Λ ⧸ MΛ Λ m → TorsAt F k sk m :=
  Quotient.lift (s := QuotientAddGroup.leftRel (MΛ Λ m)) (levelMap F P hP k sk) (by
    intro x y hxy
    exact (levelMap_eq_iff F P hP k sk hann x y).mpr (QuotientAddGroup.leftRel_apply.mp hxy))

include hP hann in
theorem levelMapBar_mk (x : ↥Λ) :
    levelMapBar F P hP k sk hann (QuotientAddGroup.mk x) = levelMap F P hP k sk x :=
  rfl

include hP hann in
theorem levelMapBar_injective : Function.Injective (levelMapBar F P hP k sk hann) := by
  intro X Y h
  induction X using QuotientAddGroup.induction_on with
  | H x =>
    induction Y using QuotientAddGroup.induction_on with
    | H y =>
      rw [levelMapBar_mk, levelMapBar_mk, levelMap_eq_iff F P hP k sk hann] at h
      exact QuotientAddGroup.eq.mpr h

include hP hann in

theorem natCard_quotient_eq_of_generates
    (hgen : ∀ Q : SchemeHomOver (geomPoint k sk) F.f, nsmulPt F.L (geomPoint k sk) m Q = F.L.one (geomPoint k sk) →
      ∃ x : ↥Λ, actPt F x (sectionAt P k sk) = Q) :
    Nat.card (↥Λ ⧸ MΛ Λ m) = Nat.card (TorsAt F k sk m) := by
  apply Nat.card_eq_of_bijective (levelMapBar F P hP k sk hann)
  refine ⟨levelMapBar_injective F P hP k sk hann, ?_⟩
  rintro ⟨Q, hQ⟩
  obtain ⟨x, hx⟩ := hgen Q hQ
  exact ⟨QuotientAddGroup.mk x, Subtype.ext hx⟩

include hP hann in

theorem generates_of_natCard_eq (hcard : Nat.card (↥Λ ⧸ MΛ Λ m) = Nat.card (TorsAt F k sk m))
    (hne : Nat.card (TorsAt F k sk m) ≠ 0)
    (Q : SchemeHomOver (geomPoint k sk) F.f) (hQ : nsmulPt F.L (geomPoint k sk) m Q = F.L.one (geomPoint k sk)) :
    ∃ x : ↥Λ, actPt F x (sectionAt P k sk) = Q := by
  haveI : Finite (TorsAt F k sk m) := Nat.finite_of_card_ne_zero hne
  have hbij := (levelMapBar_injective F P hP k sk hann).bijective_of_nat_card_le hcard.symm.le
  obtain ⟨X, hX⟩ := hbij.2 ⟨Q, hQ⟩
  induction X using QuotientAddGroup.induction_on with
  | H x => exact ⟨x, congrArg Subtype.val hX⟩

end LevelMap

section DVR

variable {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  {K : Type u} [Field K] [Algebra R K] [IsFractionRing R K]

omit [IsDomain R] [IsDiscreteValuationRing R] in

theorem isDominant_specMap_algebraMap : IsDominant (Spec.map (CommRingCat.ofHom (algebraMap R K))) := by
  constructor
  rw [Spec.map_base]
  change DenseRange (PrimeSpectrum.comap (algebraMap R K))
  rw [PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical,
    (RingHom.injective_iff_ker_eq_bot _).mp (IsFractionRing.injective R K)]
  exact bot_le

omit [IsDiscreteValuationRing R] in

theorem section_ext (𝒜 : FakeEllipticCurve Λ N R) (P Q : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) 𝒜.f)
    (h : Spec.map (CommRingCat.ofHom (algebraMap R K)) ≫ P.1 = Spec.map (CommRingCat.ofHom (algebraMap R K)) ≫ Q.1) :
    P = Q := by
  haveI : IsProper 𝒜.f := 𝒜.bundle.proper
  haveI := isDominant_specMap_algebraMap (R := R) (K := K)
  apply Subtype.ext
  refine ext_of_isDominant_of_isSeparated 𝒜.f ?_ (Spec.map (CommRingCat.ofHom (algebraMap R K))) h
  rw [P.2, Q.2]

theorem exists_section (𝒜 : FakeEllipticCurve Λ N R) (i₁ : Spec (CommRingCat.of K) ⟶ 𝒜.A)
    (hi₁ : i₁ ≫ 𝒜.f = Spec.map (CommRingCat.ofHom (algebraMap R K))) :
    ∃ P : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) 𝒜.f,
      Spec.map (CommRingCat.ofHom (algebraMap R K)) ≫ P.1 = i₁ := by
  haveI : IsProper 𝒜.f := 𝒜.bundle.proper
  have hex : ValuativeCriterion.Existence 𝒜.f := by
    have h : (ValuativeCriterion.Existence ⊓ @QuasiCompact) 𝒜.f := by
      rw [← UniversallyClosed.eq_valuativeCriterion]
      infer_instance
    exact h.1
  let sq : ValuativeCommSq 𝒜.f :=
    { R := R, K := K, i₁ := i₁, i₂ := 𝟙 _, commSq := ⟨by rw [hi₁, Category.comp_id]⟩ }
  obtain ⟨l⟩ := (hex sq).exists_lift
  exact ⟨⟨l.l, l.fac_right⟩, l.fac_left⟩

theorem main (m : ℕ) (hm : IsUnit ((m : ℕ) : R))
    (𝒜 : FakeEllipticCurve Λ N R) (E : FakeEllipticCurve Λ N K)
    (g : E.A ⟶ 𝒜.A) (hg : CategoryTheory.IsPullback g E.f 𝒜.f (Spec.map (CommRingCat.ofHom (algebraMap R K))))
    (hg_mul : ∀ {T : Scheme.{u}} (t' : T ⟶ Spec (CommRingCat.of K)) (P Q : SchemeHomOver t' E.f),
      (E.L.mul t' P Q).1 ≫ g =
        (𝒜.L.mul (t' ≫ Spec.map (CommRingCat.ofHom (algebraMap R K)))
          ⟨P.1 ≫ g, by rw [Category.assoc, hg.w, ← Category.assoc, P.2]⟩
          ⟨Q.1 ≫ g, by rw [Category.assoc, hg.w, ← Category.assoc, Q.2]⟩).1)
    (hg_act : ∀ x : ↥Λ, E.act x ≫ g = g ≫ 𝒜.act x)
    (PK : E.FullLevel m) :
    ∃! P : 𝒜.FullLevel m,
      (PK.P).1 ≫ g = Spec.map (CommRingCat.ofHom (algebraMap R K)) ≫ (P.P).1 := by
  have hι1 : 𝟙 _ ≫ Spec.map (CommRingCat.ofHom (algebraMap R K)) = Spec.map (CommRingCat.ofHom (algebraMap R K)) :=
    Category.id_comp _
  haveI : IsProper 𝒜.f := 𝒜.bundle.proper

  obtain ⟨P, hP⟩ := exists_section (K := K) 𝒜 ((PK.P).1 ≫ g)
    (by rw [Category.assoc, hg.w, ← Category.assoc, PK.P.2, Category.id_comp])

  have hres : GoodReductionJacobian.schemeHomOverComp (Spec.map (CommRingCat.ofHom (algebraMap R K)))
      (Category.comp_id _) P = bcPt hg hι1 PK.P :=
    Subtype.ext hP

  have hPtors : nsmulPt 𝒜.L (𝟙 _) m P = 𝒜.L.one (𝟙 _) := by
    apply section_ext (K := K) 𝒜
    have h1 := congrArg Subtype.val
      (res_nsmulPt 𝒜 (𝟙 _) _ (Spec.map (CommRingCat.ofHom (algebraMap R K))) (Category.comp_id _) m P)
    have h2 := congrArg Subtype.val
      (res_one 𝒜 (𝟙 _) _ (Spec.map (CommRingCat.ofHom (algebraMap R K))) (Category.comp_id _))
    simp only [GoodReductionJacobian.schemeHomOverComp_coe] at h1 h2
    rw [h1, h2, hres, ← bcPt_nsmulPt hg hg_mul hι1, PK.torsion, bcPt_one hg hg_mul hι1]

  have hann : ∀ (k : Type u) [Field k] [IsAlgClosed k] (sk : R →+* k) (x : ↥Λ),
      actPt 𝒜 x (sectionAt P k sk) = 𝒜.L.one (geomPoint k sk) ↔ x ∈ MΛ Λ m := by
    intro k _ _ sk x
    constructor
    · intro hx

      have hσ : nsmulPt 𝒜.L (𝟙 _) m (actPt 𝒜 x P) = 𝒜.L.one _ := by
        rw [← actPt_nsmulPt, hPtors, actPt_one]

      have hσ1 : actPt 𝒜 x P = 𝒜.L.one (𝟙 _) := by
        refine GoodReductionJacobian.RelativeGroupLaw.eq_of_isTorsionPoint_of_comp_eq 𝒜.L 𝒜.comm m hm (𝟙 _)
          (actPt 𝒜 x P) (𝒜.L.one _) ?_ (𝒜.L.isTorsionPoint_unit _ m) (geomPoint k sk) ?_
        · show 𝒜.L.nsmul _ m _ = _
          rw [← nsmulPt_eq_nsmul]
          exact hσ
        · have h1 := congrArg Subtype.val (sectionAt_actPt 𝒜 x P k sk)
          have h2 := congrArg Subtype.val (sectionAt_one 𝒜 k sk)
          change geomPoint k sk ≫ (actPt 𝒜 x P).1 = (actPt 𝒜 x (sectionAt P k sk)).1 at h1
          change geomPoint k sk ≫ (𝒜.L.one _).1 = (𝒜.L.one (geomPoint k sk)).1 at h2
          rw [h1, h2, hx]

      have hK : actPt E x PK.P = E.L.one (𝟙 _) := by
        apply bcPt_injective hg hι1
        rw [bcPt_actPt hg hg_act hι1, ← hres, ← res_actPt, hσ1, res_one, bcPt_one hg hg_mul hι1]

      rw [mem_MΛ_iff]
      apply (PK.annihilator (AlgebraicClosure K) (algebraMap K (AlgebraicClosure K)) x).mp
      show actPt E x (sectionAt PK.P (AlgebraicClosure K) (algebraMap K (AlgebraicClosure K))) = _
      rw [← sectionAt_actPt, hK, sectionAt_one]
    · intro hx
      exact actPt_eq_one_of_mem_MΛ 𝒜 hx _ _ (sectionAt_torsion 𝒜 P hPtors k sk)

  have hcardΛ : Nat.card (↥Λ ⧸ MΛ Λ m) = m ^ 4 := by
    have hmK : ((m : ℕ) : AlgebraicClosure K) ≠ 0 :=
      natCast_ne_zero_of_isUnit hm (AlgebraicClosure K) ((algebraMap K (AlgebraicClosure K)).comp (algebraMap R K))
    rw [← natCard_torsAt E (AlgebraicClosure K) (algebraMap K (AlgebraicClosure K)) m hmK]
    exact natCard_quotient_eq_of_generates E PK.P PK.torsion (AlgebraicClosure K) (algebraMap K (AlgebraicClosure K))
      (fun x => PK.annihilator (AlgebraicClosure K) _ x) (fun Q hQ => PK.generates (AlgebraicClosure K) _ Q hQ)

  let Pfull : 𝒜.FullLevel m :=
    { P := P
      torsion := hPtors
      generates := fun k _ _ sk Q hQ => by
        have hmk : (m : k) ≠ 0 := natCast_ne_zero_of_isUnit hm k sk
        have hm0 : m ≠ 0 := by
          rintro rfl
          exact hmk (by simp)
        have hc := natCard_torsAt 𝒜 k sk m hmk
        exact generates_of_natCard_eq 𝒜 P hPtors k sk (hann k sk) (hcardΛ.trans hc.symm)
          (by rw [hc]; exact pow_ne_zero 4 hm0) Q hQ
      annihilator := fun k _ _ sk x => hann k sk x }

  refine ⟨Pfull, hP.symm, ?_⟩
  intro P' hP'
  have hPP : P'.P = P := by
    apply section_ext (K := K) 𝒜
    rw [← hP', hP]
  rcases P' with ⟨P'P, t', g', a'⟩
  change P'P = P at hPP
  subst hPP
  rfl

end DVR

end CerednikDrinfeld.QM.FakeEllipticCurve.R4LevelExtends
p2m_reactivate "P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_FullLevel_existsUnique_comp_eq_of_isPullback_of_isUnit.CerednikDrinfeld P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_FullLevel_existsUnique_comp_eq_of_isPullback_of_isUnit.CerednikDrinfeld.QM P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_FullLevel_existsUnique_comp_eq_of_isPullback_of_isUnit.CerednikDrinfeld.QM.FakeEllipticCurve P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_FullLevel_existsUnique_comp_eq_of_isPullback_of_isUnit.CerednikDrinfeld.QM.FakeEllipticCurve.R4LevelExtends"
p2m_reactivate "P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_FullLevel_existsUnique_comp_eq_of_isPullback_of_isUnit.CerednikDrinfeld P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_FullLevel_existsUnique_comp_eq_of_isPullback_of_isUnit.CerednikDrinfeld.QM P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_FullLevel_existsUnique_comp_eq_of_isPullback_of_isUnit.CerednikDrinfeld.QM.FakeEllipticCurve"
p2m_reactivate "P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_FullLevel_existsUnique_comp_eq_of_isPullback_of_isUnit.CerednikDrinfeld P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_FullLevel_existsUnique_comp_eq_of_isPullback_of_isUnit.CerednikDrinfeld.QM"
p2m_reactivate "P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_FullLevel_existsUnique_comp_eq_of_isPullback_of_isUnit.CerednikDrinfeld"

theorem solution
    {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} {N : ℕ} (m : ℕ)
    {R : Type} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    {K : Type} [Field K] [Algebra R K] [IsFractionRing R K] (hm : IsUnit ((m : ℕ) : R))
    (𝒜 : FakeEllipticCurve Λ N R) (E : FakeEllipticCurve Λ N K)
    (g : E.A ⟶ 𝒜.A) (hg : CategoryTheory.IsPullback g E.f 𝒜.f (Spec.map (CommRingCat.ofHom (algebraMap R K))))
    (hg_mul : ∀ {T : Scheme.{0}} (t' : T ⟶ Spec (CommRingCat.of K)) (P Q : SchemeHomOver t' E.f),
      (E.L.mul t' P Q).1 ≫ g =
        (𝒜.L.mul (t' ≫ Spec.map (CommRingCat.ofHom (algebraMap R K)))
          ⟨P.1 ≫ g, by rw [Category.assoc, hg.w, ← Category.assoc, P.2]⟩
          ⟨Q.1 ≫ g, by rw [Category.assoc, hg.w, ← Category.assoc, Q.2]⟩).1)
    (hg_act : ∀ x : ↥Λ, E.act x ≫ g = g ≫ 𝒜.act x)
    (PK : E.FullLevel m) :
    ∃! P : 𝒜.FullLevel m, (PK.P).1 ≫ g = Spec.map (CommRingCat.ofHom (algebraMap R K)) ≫ (P.P).1 :=
  CerednikDrinfeld.QM.FakeEllipticCurve.R4LevelExtends.main m hm 𝒜 E g hg hg_mul hg_act PK

end
p2m_reactivate "P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_FullLevel_existsUnique_comp_eq_of_isPullback_of_isUnit.CerednikDrinfeld P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_FullLevel_existsUnique_comp_eq_of_isPullback_of_isUnit.CerednikDrinfeld.QM P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_FullLevel_existsUnique_comp_eq_of_isPullback_of_isUnit.CerednikDrinfeld.QM.FakeEllipticCurve P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_FullLevel_existsUnique_comp_eq_of_isPullback_of_isUnit.CerednikDrinfeld.QM.FakeEllipticCurve.R4LevelExtends"

end S_CerednikDrinfeld_QM_FakeEllipticCurve_FullLevel_existsUnique_comp_eq_of_isPullback_of_isUnit
end P2MW
export P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_FullLevel_existsUnique_comp_eq_of_isPullback_of_isUnit (solution)
