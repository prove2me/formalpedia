-- Prove2me | solution 1 for CerednikDrinfeld.QM.FakeEllipticCurve.exists_flat_surjective_withFullLevel_isPullback
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.837917+00:00
-- url     : https://prove2.me/submissions/37b291f5-65b7-56a1-b629-6e724d3200fd

import Mathlib
import Definitions.Def_CerednikDrinfeld_QMFineModuli
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawKernel
import Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_isFinite_and_etale_schemeKerStr_of_isUnit
import Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_exists_isPullback_levelIff
import Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_nonempty_fullLevel_of_isMaximalOrder
import Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_exists_isClopen_genLocus_schemeKer
import Theorems.Thm_AlgebraicGeometry_exists_iso_Spec_of_isClopen_of_isFinite_of_flat
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_exists_flat_surjective_withFullLevel_isPullback
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
p2m_attr_erase "simp" "AlgebraicGeometry.ProjSpace.twistObj.smul_val AlgebraicGeometry.ProjSpace.twistGradeEquiv_apply_val AlgebraicGeometry.ProjSpace.twistObj.mk.sizeOf_spec QuaternionAlgebra.baseChangeRight_tmul QuaternionAlgebra.mapOfAlgebraMapEq_apply QuaternionAlgebra.baseChange_tmul QuaternionAlgebra.ClassSet.map_mk"

set_option autoImplicit false

p2m_open "CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra~schemeHomOverComp~schemeHomOverComp_coe GoodReductionJacobian QuaternionAlgebra CerednikDrinfeld CerednikDrinfeld.QM"
open scoped Quaternion

noncomputable section

namespace LLX

section generic
variable {R : Type} [CommRing R] {A : Scheme.{0}} {f : A ⟶ Spec (CommRingCat.of R)} (L : RelativeGroupLaw R f)

theorem one_coe_congr {T : Scheme.{0}} {t₁ t₂ : T ⟶ Spec (CommRingCat.of R)} (h : t₁ = t₂) :
    (L.one t₂).1 = (L.one t₁).1 := by subst h; rfl

theorem nsmulPt_coe_congr {T : Scheme.{0}} {t₁ t₂ : T ⟶ Spec (CommRingCat.of R)} (h : t₁ = t₂) (n : ℕ)
    (P : SchemeHomOver t₁ f) (P' : SchemeHomOver t₂ f) (hPP' : P'.1 = P.1) :
    (nsmulPt L t₂ n P').1 = (nsmulPt L t₁ n P).1 := by
  subst h
  obtain rfl : P' = P := Subtype.ext hPP'
  rfl

theorem eq_one_of_mul_self {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of R)) (y : SchemeHomOver t f)
    (h : L.mul t y y = y) : y = L.one t := by
  have := congrArg (L.mul t (L.inv t y)) h
  rw [← L.mul_assoc, L.inv_mul_cancel, L.one_mul] at this
  exact this

theorem nsmulPt_natural' {T T' : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of R))
    (t' : T' ⟶ Spec (CommRingCat.of R)) (ψ : T' ⟶ T) (hψ : ψ ≫ t = t') (n : ℕ) (P : SchemeHomOver t f) :
    GoodReductionJacobian.schemeHomOverComp ψ hψ (nsmulPt L t n P) =
      nsmulPt L t' n (GoodReductionJacobian.schemeHomOverComp ψ hψ P) := by
  induction n with
  | zero => exact L.one_natural t t' ψ hψ
  | succ n ih =>
    show GoodReductionJacobian.schemeHomOverComp ψ hψ (L.mul t (nsmulPt L t n P) P) =
      L.mul t' (nsmulPt L t' n (GoodReductionJacobian.schemeHomOverComp ψ hψ P)) _
    rw [L.mul_natural, ih]

theorem one_coe_natural {T T' : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of R))
    (t' : T' ⟶ Spec (CommRingCat.of R)) (ψ : T' ⟶ T) (hψ : ψ ≫ t = t') :
    (L.one t').1 = ψ ≫ (L.one t).1 := by
  have := congrArg Subtype.val (L.one_natural t t' ψ hψ)
  rw [GoodReductionJacobian.schemeHomOverComp_coe] at this
  exact this.symm

end generic

section transport

variable {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} {N : ℕ} {S S' : Type} [CommRing S] [CommRing S'] {φ : S →+* S'}
  {E : FakeEllipticCurve Λ N S} {E' : FakeEllipticCurve Λ N S'} {g : E'.A ⟶ E.A}
  (hg : IsPullback g E'.f E.f (Spec.map (CommRingCat.ofHom φ)))

def gpt {T : Scheme.{0}} (t' : T ⟶ Spec (CommRingCat.of S')) (Q : SchemeHomOver t' E'.f) :
    SchemeHomOver (t' ≫ Spec.map (CommRingCat.ofHom φ)) E.f :=
  ⟨Q.1 ≫ g, by rw [Category.assoc, hg.w, ← Category.assoc, Q.2]⟩

@[scoped simp] theorem gpt_coe {T : Scheme.{0}} (t' : T ⟶ Spec (CommRingCat.of S')) (Q : SchemeHomOver t' E'.f) :
    (gpt hg t' Q).1 = Q.1 ≫ g := rfl

include hg in
theorem ginj {T : Scheme.{0}} (t' : T ⟶ Spec (CommRingCat.of S')) (Q Q' : SchemeHomOver t' E'.f)
    (h : Q.1 ≫ g = Q'.1 ≫ g) : Q = Q' :=
  Subtype.ext (hg.hom_ext h (by rw [Q.2, Q'.2]))

variable (hmul : ∀ {T : Scheme.{0}} (t' : T ⟶ Spec (CommRingCat.of S')) (P Q : SchemeHomOver t' E'.f),
    (E'.L.mul t' P Q).1 ≫ g =
      (E.L.mul (t' ≫ Spec.map (CommRingCat.ofHom φ))
        ⟨P.1 ≫ g, by rw [Category.assoc, hg.w, ← Category.assoc, P.2]⟩
        ⟨Q.1 ≫ g, by rw [Category.assoc, hg.w, ← Category.assoc, Q.2]⟩).1)

include hmul in
theorem gmul {T : Scheme.{0}} (t' : T ⟶ Spec (CommRingCat.of S')) (P Q : SchemeHomOver t' E'.f) :
    gpt hg t' (E'.L.mul t' P Q) = E.L.mul _ (gpt hg t' P) (gpt hg t' Q) := Subtype.ext (hmul t' P Q)

include hmul in
theorem gone {T : Scheme.{0}} (t' : T ⟶ Spec (CommRingCat.of S')) : gpt hg t' (E'.L.one t') = E.L.one _ := by
  apply eq_one_of_mul_self
  rw [← gmul hg hmul, E'.L.one_mul]

include hmul in
theorem gnsmul {T : Scheme.{0}} (t' : T ⟶ Spec (CommRingCat.of S')) (n : ℕ) (Q : SchemeHomOver t' E'.f) :
    gpt hg t' (nsmulPt E'.L t' n Q) = nsmulPt E.L _ n (gpt hg t' Q) := by
  induction n with
  | zero => exact gone hg hmul t'
  | succ n ih => simp only [nsmulPt]; rw [gmul hg hmul, ih]

theorem gact (hact : ∀ x : ↥Λ, E'.act x ≫ g = g ≫ E.act x)
    {T : Scheme.{0}} (t' : T ⟶ Spec (CommRingCat.of S')) (x : ↥Λ) (Q : SchemeHomOver t' E'.f) :
    gpt hg t' (pushPt (E'.act x) (E'.act_over x) Q) = pushPt (E.act x) (E.act_over x) (gpt hg t' Q) := by
  apply Subtype.ext
  simp only [gpt_coe, mapPt_coe, Category.assoc, hact x]

omit hg in
theorem hgeom (k : Type) [Field k] (sk : S' →+* k) :
    geomPoint k sk ≫ Spec.map (CommRingCat.ofHom φ) = geomPoint k (sk.comp φ) := by
  show Spec.map (CommRingCat.ofHom sk) ≫ Spec.map (CommRingCat.ofHom φ) = Spec.map (CommRingCat.ofHom (sk.comp φ))
  rw [← Spec.map_comp]; rfl

end transport

section kernel

variable {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} {N : ℕ} {S : Type} [CommRing S] (E : FakeEllipticCurve Λ N S) (m : ℕ)

theorem nsmul_eq_nsmulPt {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of S)) (n : ℕ) (P : SchemeHomOver t E.f) :
    E.L.nsmul t n P = nsmulPt E.L t n P := by
  induction n with
  | zero => rfl
  | succ n ih => rw [GoodReductionJacobian.RelativeGroupLaw.nsmul_succ, ih]; rfl

theorem comp_nsmul_idPoint {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of S)) (n : ℕ) (P : SchemeHomOver t E.f) :
    GoodReductionJacobian.schemeHomOverComp P.1 P.2 (E.L.nsmul E.f n RelativeGroupLaw.idPoint) = E.L.nsmul t n P := by
  induction n with
  | zero =>
    rw [GoodReductionJacobian.RelativeGroupLaw.nsmul_zero, GoodReductionJacobian.RelativeGroupLaw.nsmul_zero]
    exact E.L.one_natural E.f t P.1 P.2
  | succ n ih =>
    rw [GoodReductionJacobian.RelativeGroupLaw.nsmul_succ, GoodReductionJacobian.RelativeGroupLaw.nsmul_succ,
      E.L.mul_natural E.f t P.1 P.2, ih]
    congr 1

theorem mapPt_schemeNsmul (n : ℕ) {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of S)) (P : SchemeHomOver t E.f) :
    mapPt (E.L.schemeNsmul n) (E.L.schemeNsmul_over n) P = nsmulPt E.L t n P := by
  rw [← nsmul_eq_nsmulPt, ← comp_nsmul_idPoint]
  exact Subtype.ext rfl

theorem nsmulPt_coe (n : ℕ) {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of S)) (P : SchemeHomOver t E.f) :
    (nsmulPt E.L t n P).1 = P.1 ≫ E.L.schemeNsmul n := by
  rw [← mapPt_schemeNsmul]; rfl

theorem fst_f : pullback.fst (E.L.schemeNsmul m) (E.L.one (𝟙 (Spec (CommRingCat.of S)))).1 ≫ E.f = E.L.schemeKerStr m := by
  calc pullback.fst (E.L.schemeNsmul m) (E.L.one (𝟙 (Spec (CommRingCat.of S)))).1 ≫ E.f
      = pullback.fst (E.L.schemeNsmul m) (E.L.one (𝟙 (Spec (CommRingCat.of S)))).1 ≫ (E.L.schemeNsmul m ≫ E.f) := by
          rw [E.L.schemeNsmul_over]
    _ = (pullback.fst (E.L.schemeNsmul m) (E.L.one (𝟙 (Spec (CommRingCat.of S)))).1 ≫ E.L.schemeNsmul m) ≫ E.f :=
          (Category.assoc _ _ _).symm
    _ = (pullback.snd (E.L.schemeNsmul m) (E.L.one (𝟙 (Spec (CommRingCat.of S)))).1 ≫
          (E.L.one (𝟙 (Spec (CommRingCat.of S)))).1) ≫ E.f := by rw [pullback.condition]
    _ = E.L.schemeKerStr m := by
          rw [Category.assoc, (E.L.one (𝟙 (Spec (CommRingCat.of S)))).2, Category.comp_id]

def kerPt {T : Scheme.{0}} (σ : T ⟶ E.L.schemeKer m) (t : T ⟶ Spec (CommRingCat.of S))
    (ht : σ ≫ E.L.schemeKerStr m = t) : SchemeHomOver t E.f :=
  ⟨σ ≫ pullback.fst (E.L.schemeNsmul m) (E.L.one (𝟙 (Spec (CommRingCat.of S)))).1,
    by rw [Category.assoc, fst_f, ht]⟩

@[scoped simp] theorem kerPt_coe {T : Scheme.{0}} (σ : T ⟶ E.L.schemeKer m) (t : T ⟶ Spec (CommRingCat.of S))
    (ht : σ ≫ E.L.schemeKerStr m = t) :
    (kerPt E m σ t ht).1 = σ ≫ pullback.fst (E.L.schemeNsmul m) (E.L.one (𝟙 (Spec (CommRingCat.of S)))).1 := rfl

theorem kerPt_torsion {T : Scheme.{0}} (σ : T ⟶ E.L.schemeKer m) (t : T ⟶ Spec (CommRingCat.of S))
    (ht : σ ≫ E.L.schemeKerStr m = t) : nsmulPt E.L t m (kerPt E m σ t ht) = E.L.one t := by
  apply Subtype.ext
  rw [nsmulPt_coe, kerPt_coe, Category.assoc, pullback.condition, ← Category.assoc]
  show (σ ≫ E.L.schemeKerStr m) ≫ _ = _
  rw [ht]
  exact (one_coe_natural E.L (𝟙 _) t t (Category.comp_id t)).symm

end kernel

section field

variable {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} {N : ℕ} {S : Type} [CommRing S] {E : FakeEllipticCurve Λ N S}
  {k : Type} [Field k] [IsAlgClosed k] {sk : S →+* k}
  {Ek : FakeEllipticCurve Λ N k} {g : Ek.A ⟶ E.A}
  (hg : IsPullback g Ek.f E.f (Spec.map (CommRingCat.ofHom sk)))
  (hmul : ∀ {T : Scheme.{0}} (t' : T ⟶ Spec (CommRingCat.of k)) (P Q : SchemeHomOver t' Ek.f),
    (Ek.L.mul t' P Q).1 ≫ g =
      (E.L.mul (t' ≫ Spec.map (CommRingCat.ofHom sk))
        ⟨P.1 ≫ g, by rw [Category.assoc, hg.w, ← Category.assoc, P.2]⟩
        ⟨Q.1 ≫ g, by rw [Category.assoc, hg.w, ← Category.assoc, Q.2]⟩).1)
  (hact : ∀ x : ↥Λ, Ek.act x ≫ g = g ≫ E.act x)

omit hg in
theorem geomPoint_id : geomPoint k (RingHom.id k) = 𝟙 _ := by simp [geomPoint]

omit hg in
theorem id_geom : 𝟙 _ ≫ Spec.map (CommRingCat.ofHom sk) = geomPoint k sk := Category.id_comp _

def downPt {m : ℕ} (PP : Ek.FullLevel m) : SchemeHomOver (geomPoint k sk) E.f :=
  ⟨PP.P.1 ≫ g, by rw [Category.assoc, hg.w, ← Category.assoc, PP.P.2]; exact id_geom⟩

@[scoped simp] theorem downPt_coe {m : ℕ} (PP : Ek.FullLevel m) : (downPt hg PP).1 = PP.P.1 ≫ g := rfl

include hmul in
theorem downPt_torsion {m : ℕ} (PP : Ek.FullLevel m) :
    nsmulPt E.L (geomPoint k sk) m (downPt hg PP) = E.L.one (geomPoint k sk) := by
  apply Subtype.ext
  have h1 := congrArg Subtype.val (gnsmul hg hmul (𝟙 _) m PP.P)
  rw [PP.torsion, gone hg hmul] at h1
  exact (nsmulPt_coe_congr E.L id_geom m (gpt hg _ PP.P) (downPt hg PP) rfl).trans
    (h1.symm.trans (one_coe_congr E.L id_geom).symm)

include hmul hact in
theorem downPt_generates {m : ℕ} (PP : Ek.FullLevel m) (Q : SchemeHomOver (geomPoint k sk) E.f)
    (hQ : nsmulPt E.L (geomPoint k sk) m Q = E.L.one (geomPoint k sk)) :
    ∃ x : ↥Λ, pushPt (E.act x) (E.act_over x) (downPt hg PP) = Q := by
  let Qt : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) Ek.f :=
    ⟨hg.lift Q.1 (𝟙 _) (by rw [Q.2]; exact id_geom.symm), hg.lift_snd _ _ _⟩
  have hQt : Qt.1 ≫ g = Q.1 := hg.lift_fst _ _ _
  have hQt_tors : nsmulPt Ek.L (𝟙 _) m Qt = Ek.L.one (𝟙 _) := by
    apply ginj hg
    have h1 := congrArg Subtype.val (gnsmul hg hmul (𝟙 _) m Qt)
    have h2 := congrArg Subtype.val (gone hg hmul (𝟙 (Spec (CommRingCat.of k))))
    rw [gpt_coe] at h1 h2
    rw [h1, h2, ← nsmulPt_coe_congr E.L id_geom m (gpt hg _ Qt) Q hQt.symm, hQ]
    exact one_coe_congr E.L id_geom
  have hQs_tors : nsmulPt Ek.L (geomPoint k (RingHom.id k)) m (FakeEllipticCurve.sectionAt Qt k (RingHom.id k)) =
      Ek.L.one (geomPoint k (RingHom.id k)) := by
    show nsmulPt Ek.L _ m (GoodReductionJacobian.schemeHomOverComp (geomPoint k (RingHom.id k)) (Category.comp_id _) Qt) = _
    rw [← nsmulPt_natural', hQt_tors, Ek.L.one_natural]
  obtain ⟨x, hx⟩ := PP.generates k (RingHom.id k) (FakeEllipticCurve.sectionAt Qt k (RingHom.id k)) hQs_tors
  refine ⟨x, Subtype.ext ?_⟩
  have h := congrArg Subtype.val hx
  simp only [mapPt_coe, FakeEllipticCurve.sectionAt, GoodReductionJacobian.schemeHomOverComp_coe,
    Category.assoc] at h
  rw [geomPoint_id, Category.id_comp, Category.id_comp] at h
  simp only [mapPt_coe, downPt_coe, Category.assoc]
  rw [← hact x, ← Category.assoc, h, hQt]

include hmul hact in
theorem downPt_annihilator {m : ℕ} (PP : Ek.FullLevel m) (x : ↥Λ) :
    pushPt (E.act x) (E.act_over x) (downPt hg PP) = E.L.one (geomPoint k sk) ↔
      ∃ y : ↥Λ, (x : ℍ[ℚ, a, b]) = (m : ℚ) • (y : ℍ[ℚ, a, b]) := by
  rw [← PP.annihilator k (RingHom.id k) x]
  have hsec : ∀ X : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) Ek.f,
      (FakeEllipticCurve.sectionAt X k (RingHom.id k)).1 = X.1 := by
    intro X
    show geomPoint k (RingHom.id k) ≫ X.1 = X.1
    rw [geomPoint_id, Category.id_comp]
  have hone_k : (Ek.L.one (geomPoint k (RingHom.id k))).1 = (Ek.L.one (𝟙 _)).1 := by
    rw [one_coe_natural Ek.L (𝟙 _) (geomPoint k (RingHom.id k)) (geomPoint k (RingHom.id k)) (Category.comp_id _),
      geomPoint_id, Category.id_comp]
  have hE_one : (E.L.one (geomPoint k sk)).1 = (Ek.L.one (𝟙 _)).1 ≫ g := by
    have h2 := congrArg Subtype.val (gone hg hmul (𝟙 (Spec (CommRingCat.of k))))
    rw [gpt_coe] at h2
    rw [h2]; exact one_coe_congr E.L id_geom
  constructor
  · intro h
    apply Subtype.ext
    rw [mapPt_coe, hsec, hone_k]
    apply hg.hom_ext
    · have h1 := congrArg Subtype.val h
      simp only [mapPt_coe, downPt_coe, Category.assoc] at h1
      rw [Category.assoc, hact x, h1, hE_one]
    · rw [Category.assoc, Ek.act_over x, PP.P.2, (Ek.L.one (𝟙 _)).2]
  · intro h
    have h1 := congrArg Subtype.val h
    rw [mapPt_coe, hsec, hone_k] at h1
    apply Subtype.ext
    simp only [mapPt_coe, downPt_coe, Category.assoc]
    rw [← hact x, ← Category.assoc, h1, hE_one]

end field

section cover

variable {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} {N : ℕ} {S S' : Type} [CommRing S] [CommRing S'] {φ : S →+* S'}
  {E : FakeEllipticCurve Λ N S} {E' : FakeEllipticCurve Λ N S'} {g : E'.A ⟶ E.A}
  (hg : IsPullback g E'.f E.f (Spec.map (CommRingCat.ofHom φ)))
  (hmul : ∀ {T : Scheme.{0}} (t' : T ⟶ Spec (CommRingCat.of S')) (P Q : SchemeHomOver t' E'.f),
    (E'.L.mul t' P Q).1 ≫ g =
      (E.L.mul (t' ≫ Spec.map (CommRingCat.ofHom φ))
        ⟨P.1 ≫ g, by rw [Category.assoc, hg.w, ← Category.assoc, P.2]⟩
        ⟨Q.1 ≫ g, by rw [Category.assoc, hg.w, ← Category.assoc, Q.2]⟩).1)
  (hact : ∀ x : ↥Λ, E'.act x ≫ g = g ≫ E.act x)
  {m : ℕ} (σ : Spec (CommRingCat.of S') ⟶ E.L.schemeKer m)
  (hσ : σ ≫ E.L.schemeKerStr m = Spec.map (CommRingCat.ofHom φ))

noncomputable def secP : SchemeHomOver (𝟙 (Spec (CommRingCat.of S'))) E'.f :=
  ⟨hg.lift (σ ≫ pullback.fst (E.L.schemeNsmul m) (E.L.one (𝟙 (Spec (CommRingCat.of S)))).1) (𝟙 _)
    (by rw [Category.assoc, fst_f, hσ, Category.id_comp]), hg.lift_snd _ _ _⟩

theorem secP_g : (secP hg σ hσ).1 ≫ g =
    σ ≫ pullback.fst (E.L.schemeNsmul m) (E.L.one (𝟙 (Spec (CommRingCat.of S)))).1 := hg.lift_fst _ _ _

theorem secP_g_assoc {Z : Scheme.{0}} (h : E.A ⟶ Z) : (secP hg σ hσ).1 ≫ g ≫ h =
    σ ≫ pullback.fst (E.L.schemeNsmul m) (E.L.one (𝟙 (Spec (CommRingCat.of S)))).1 ≫ h := by
  rw [← Category.assoc, secP_g, Category.assoc]

include hmul in
theorem secP_torsion : nsmulPt E'.L (𝟙 _) m (secP hg σ hσ) = E'.L.one (𝟙 _) := by
  apply ginj hg
  have h1 := congrArg Subtype.val (gnsmul hg hmul (𝟙 _) m (secP hg σ hσ))
  have h2 := congrArg Subtype.val (gone hg hmul (𝟙 (Spec (CommRingCat.of S'))))
  rw [gpt_coe] at h1 h2
  rw [h1, h2]
  have hσ' : σ ≫ E.L.schemeKerStr m = 𝟙 _ ≫ Spec.map (CommRingCat.ofHom φ) := by rw [hσ, Category.id_comp]
  have hpt : gpt hg _ (secP hg σ hσ) = kerPt E m σ _ hσ' := Subtype.ext (secP_g hg σ hσ)
  rw [hpt, kerPt_torsion]

def geomKerPt (k : Type) [Field k] (sk' : S' →+* k) : SchemeHomOver (geomPoint k (sk'.comp φ)) E.f :=
  kerPt E m (geomPoint k sk' ≫ σ) (geomPoint k (sk'.comp φ)) (by rw [Category.assoc, hσ, hgeom])

theorem geomKerPt_coe (k : Type) [Field k] (sk' : S' →+* k) :
    (geomKerPt (φ := φ) (E := E) σ hσ k sk').1 =
      geomPoint k sk' ≫ σ ≫ pullback.fst (E.L.schemeNsmul m) (E.L.one (𝟙 (Spec (CommRingCat.of S)))).1 := by
  show (geomPoint k sk' ≫ σ) ≫ _ = _
  rw [Category.assoc]

theorem geomKerPt_torsion (k : Type) [Field k] (sk' : S' →+* k) :
    nsmulPt E.L _ m (geomKerPt (φ := φ) (E := E) σ hσ k sk') = E.L.one _ := kerPt_torsion E m _ _ _

theorem gsec (k : Type) [Field k] (sk' : S' →+* k) :
    (gpt hg _ (FakeEllipticCurve.sectionAt (secP hg σ hσ) k sk')).1 = (geomKerPt (φ := φ) (E := E) σ hσ k sk').1 := by
  rw [geomKerPt_coe, gpt_coe]
  show (geomPoint k sk' ≫ (secP hg σ hσ).1) ≫ g = _
  rw [Category.assoc, secP_g]

variable (𝒢 : (E.L.schemeKer m).Opens) (hσ𝒢 : Set.range σ ⊆ (𝒢 : Set ↥(E.L.schemeKer m)))
  (h𝒢 : ∀ (k : Type) [Field k] [IsAlgClosed k] (sk : S →+* k) (P : SchemeHomOver (geomPoint k sk) E.f),
        nsmulPt E.L (geomPoint k sk) m P = E.L.one (geomPoint k sk) →
        ((∃ κ : Spec (CommRingCat.of k) ⟶ E.L.schemeKer m,
            κ ≫ pullback.fst (E.L.schemeNsmul m) (E.L.one (𝟙 (Spec (CommRingCat.of S)))).1 = P.1 ∧
            Set.range κ ⊆ (𝒢 : Set ↥(E.L.schemeKer m))) ↔
          ((∀ Q : SchemeHomOver (geomPoint k sk) E.f, nsmulPt E.L (geomPoint k sk) m Q = E.L.one (geomPoint k sk) →
              ∃ x : ↥Λ, pushPt (E.act x) (E.act_over x) P = Q) ∧
           (∀ x : ↥Λ, pushPt (E.act x) (E.act_over x) P = E.L.one (geomPoint k sk) ↔
              ∃ y : ↥Λ, (x : ℍ[ℚ, a, b]) = (m : ℚ) • (y : ℍ[ℚ, a, b])))))

include hσ𝒢 h𝒢 in
theorem geomKerPt_clauses (k : Type) [Field k] [IsAlgClosed k] (sk' : S' →+* k) :
    (∀ Q : SchemeHomOver (geomPoint k (sk'.comp φ)) E.f,
        nsmulPt E.L (geomPoint k (sk'.comp φ)) m Q = E.L.one (geomPoint k (sk'.comp φ)) →
        ∃ x : ↥Λ, pushPt (E.act x) (E.act_over x) (geomKerPt (φ := φ) (E := E) σ hσ k sk') = Q) ∧
    (∀ x : ↥Λ, pushPt (E.act x) (E.act_over x) (geomKerPt (φ := φ) (E := E) σ hσ k sk') =
        E.L.one (geomPoint k (sk'.comp φ)) ↔
        ∃ y : ↥Λ, (x : ℍ[ℚ, a, b]) = (m : ℚ) • (y : ℍ[ℚ, a, b])) := by
  refine (h𝒢 k (sk'.comp φ) (geomKerPt (φ := φ) (E := E) σ hσ k sk') (geomKerPt_torsion σ hσ k sk')).1
    ⟨geomPoint k sk' ≫ σ, rfl, ?_⟩
  rintro _ ⟨z, rfl⟩
  rw [Scheme.Hom.comp_apply]
  exact hσ𝒢 ⟨_, rfl⟩

include hmul hact hσ𝒢 h𝒢 in
theorem secP_generates (k : Type) [Field k] [IsAlgClosed k] (sk' : S' →+* k)
    (Q : SchemeHomOver (geomPoint k sk') E'.f)
    (hQ : nsmulPt E'.L (geomPoint k sk') m Q = E'.L.one (geomPoint k sk')) :
    ∃ x : ↥Λ, pushPt (E'.act x) (E'.act_over x) (FakeEllipticCurve.sectionAt (secP hg σ hσ) k sk') = Q := by
  let Qg : SchemeHomOver (geomPoint k (sk'.comp φ)) E.f :=
    ⟨Q.1 ≫ g, by rw [Category.assoc, hg.w, ← Category.assoc, Q.2, hgeom]⟩
  have hQg : nsmulPt E.L (geomPoint k (sk'.comp φ)) m Qg = E.L.one _ := by
    apply Subtype.ext
    have h1 := congrArg Subtype.val (gnsmul hg hmul _ m Q)
    rw [hQ, gone hg hmul] at h1
    exact (nsmulPt_coe_congr E.L (hgeom k sk') m (gpt hg _ Q) Qg rfl).trans
      (h1.symm.trans (one_coe_congr E.L (hgeom k sk')).symm)
  obtain ⟨x, hx⟩ := (geomKerPt_clauses σ hσ 𝒢 hσ𝒢 h𝒢 k sk').1 Qg hQg
  refine ⟨x, ginj hg _ _ _ ?_⟩
  have h := congrArg Subtype.val hx
  simp only [mapPt_coe] at h ⊢
  rw [← gsec hg σ hσ k sk'] at h
  simp only [gpt_coe, Category.assoc] at h
  rw [Category.assoc, hact x]
  exact h

include hmul hact hσ𝒢 h𝒢 in
theorem secP_annihilator (k : Type) [Field k] [IsAlgClosed k] (sk' : S' →+* k) (x : ↥Λ) :
    pushPt (E'.act x) (E'.act_over x) (FakeEllipticCurve.sectionAt (secP hg σ hσ) k sk') = E'.L.one (geomPoint k sk') ↔
      ∃ y : ↥Λ, (x : ℍ[ℚ, a, b]) = (m : ℚ) • (y : ℍ[ℚ, a, b]) := by
  rw [← (geomKerPt_clauses σ hσ 𝒢 hσ𝒢 h𝒢 k sk').2 x]
  constructor
  · intro h
    apply Subtype.ext
    have h1 := congrArg Subtype.val (congrArg (gpt hg _) h)
    rw [gact hg hact, gone hg hmul] at h1
    simp only [mapPt_coe] at h1 ⊢
    rw [gsec hg σ hσ k sk'] at h1
    rw [one_coe_congr E.L (hgeom k sk')]
    exact h1
  · intro h
    apply ginj hg
    have h1 := congrArg Subtype.val (gact hg hact _ x (FakeEllipticCurve.sectionAt (secP hg σ hσ) k sk'))
    have h2 := congrArg Subtype.val (gone hg hmul (geomPoint k sk'))
    rw [gpt_coe] at h1 h2
    rw [h1, h2]
    have h3 := congrArg Subtype.val h
    simp only [mapPt_coe] at h3 ⊢
    rw [gsec hg σ hσ k sk', h3, one_coe_congr E.L (hgeom k sk')]

noncomputable def fullLevel : E'.FullLevel m :=
  ⟨secP hg σ hσ, secP_torsion hg hmul σ hσ, secP_generates hg hmul hact σ hσ 𝒢 hσ𝒢 h𝒢,
    secP_annihilator hg hmul hact σ hσ 𝒢 hσ𝒢 h𝒢⟩

end cover

end LLX
p2m_reactivate "P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_exists_flat_surjective_withFullLevel_isPullback.LLX"

theorem solution
    {a b : ℚ} {q q' : ℕ} [Fact q.Prime] [Fact q'.Prime] (hB : IsIndefiniteRamifiedExactlyAt a b q q')
    (Λ : Submodule ℤ ℍ[ℚ, a, b]) (hΛ : IsMaximalOrder Λ) {N : ℕ} (m : ℕ)
    (S : Type) [CommRing S] (hm : IsUnit ((m : ℕ) : S)) (E : FakeEllipticCurve Λ N S) :
    ∃ (S' : Type) (_ : CommRing S') (φ : S →+* S'),
      Flat (Spec.map (CommRingCat.ofHom φ)) ∧ Surjective (Spec.map (CommRingCat.ofHom φ)) ∧
      ∃ u' : FakeEllipticCurve.WithFullLevel Λ N m S', FakeEllipticCurve.IsPullback φ E u'.1 := by
  classical

  obtain ⟨𝒢, h𝒢cl, h𝒢⟩ := CerednikDrinfeld.QM.FakeEllipticCurve.exists_isClopen_genLocus_schemeKer hB Λ hΛ m hm E

  obtain ⟨hfin, het⟩ := CerednikDrinfeld.QM.FakeEllipticCurve.isFinite_and_etale_schemeKerStr_of_isUnit E m hm
  haveI := hfin; haveI := het

  obtain ⟨S', instS', φ, e, he, hflat, hsurj⟩ :=
    AlgebraicGeometry.exists_iso_Spec_of_isClopen_of_isFinite_of_flat (E.L.schemeKerStr m) 𝒢 h𝒢cl

  have hsurj𝒢 : Surjective (𝒢.ι ≫ E.L.schemeKerStr m) := by
    constructor
    intro s
    let κ₀ := s.asIdeal.ResidueField
    let k := AlgebraicClosure κ₀
    let sk : S →+* k := (algebraMap κ₀ k).comp (algebraMap S κ₀)
    obtain ⟨Ek, gk, hgk, hmulk, hactk, -, -⟩ := CerednikDrinfeld.QM.FakeEllipticCurve.exists_isPullback_levelIff sk E
    have hmk : (m : k) ≠ 0 := by
      have h := hm.map sk
      rw [map_natCast] at h
      exact h.ne_zero
    obtain ⟨PP⟩ := CerednikDrinfeld.QM.FakeEllipticCurve.nonempty_fullLevel_of_isMaximalOrder hB Λ hΛ m k hmk Ek
    obtain ⟨κ, hκ1, hκ𝒢⟩ := (h𝒢 k sk (LLX.downPt hgk PP) (LLX.downPt_torsion hgk hmulk PP)).2
      ⟨LLX.downPt_generates hgk hmulk hactk PP, LLX.downPt_annihilator hgk hmulk hactk PP⟩
    have hκ2 : κ ≫ E.L.schemeKerStr m = geomPoint k sk := by
      rw [← LLX.fst_f E m, ← Category.assoc, hκ1]
      exact (LLX.downPt hgk PP).2
    have hs : s ∈ Set.range (geomPoint k sk) := by
      refine ⟨⟨⊥, Ideal.isPrime_bot⟩, ?_⟩
      apply PrimeSpectrum.ext
      show Ideal.comap sk ⊥ = s.asIdeal
      rw [← RingHom.ker_eq_comap_bot, RingHom.ker_comp_of_injective _ (algebraMap κ₀ k).injective,
        Ideal.ker_algebraMap_residueField]
    obtain ⟨pt, hpt⟩ := hs
    have hκpt : κ pt ∈ (𝒢 : Set ↥(E.L.schemeKer m)) := hκ𝒢 ⟨pt, rfl⟩
    rw [← Scheme.Opens.range_ι] at hκpt
    obtain ⟨y, hy⟩ := hκpt
    refine ⟨y, ?_⟩
    rw [Scheme.Hom.comp_apply, hy, ← Scheme.Hom.comp_apply, hκ2, hpt]

  obtain ⟨E', gA, hgA, hmul, hact, hlev, -⟩ := CerednikDrinfeld.QM.FakeEllipticCurve.exists_isPullback_levelIff φ E
  have hσ : (e.hom ≫ 𝒢.ι) ≫ E.L.schemeKerStr m = Spec.map (CommRingCat.ofHom φ) := by
    rw [Category.assoc]; exact he
  have hσ𝒢 : Set.range (e.hom ≫ 𝒢.ι) ⊆ (𝒢 : Set ↥(E.L.schemeKer m)) := by
    rintro _ ⟨z, rfl⟩
    rw [Scheme.Hom.comp_apply, ← Scheme.Opens.range_ι]
    exact ⟨_, rfl⟩
  exact ⟨S', instS', φ, hflat, hsurj hsurj𝒢, ⟨E', LLX.fullLevel hgA hmul hact (e.hom ≫ 𝒢.ι) hσ 𝒢 hσ𝒢 h𝒢⟩,
    gA, hgA, hmul, hact, hlev⟩

end
p2m_reactivate "P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_exists_flat_surjective_withFullLevel_isPullback.LLX"

end S_CerednikDrinfeld_QM_FakeEllipticCurve_exists_flat_surjective_withFullLevel_isPullback
end P2MW
export P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_exists_flat_surjective_withFullLevel_isPullback (solution)
