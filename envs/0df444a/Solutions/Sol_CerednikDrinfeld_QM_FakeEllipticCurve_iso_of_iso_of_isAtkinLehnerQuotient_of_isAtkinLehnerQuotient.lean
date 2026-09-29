-- Prove2me | solution 1 for CerednikDrinfeld.QM.FakeEllipticCurve.iso_of_iso_of_isAtkinLehnerQuotient_of_isAtkinLehnerQuotient
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.141142+00:00
-- url     : https://prove2.me/submissions/baaa811c-97db-5990-aea5-f3eb61a92e22

import Mathlib
import Definitions.Def_CerednikDrinfeld_QMModuliProps
import Definitions.Def_CerednikDrinfeld_FakeEllipticFrobenius
import Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_isFinite_flat_surjective_of_mapPt_mapPt_eq_nsmulPt
import Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_factorsThrough_lev_iff_exists_mapPt_eq_of_coprime
import Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_pushPt_act_natCast_eq_nsmulPt
import Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_isAtkinLehnerQuotient_of_iso_of_iso
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_iso_of_iso_of_isAtkinLehnerQuotient_of_isAtkinLehnerQuotient
p2m_attr_erase "instance" "instTopologicallyFGOfFiniteType GoodReductionJacobian.RelativeGroupLaw.isIso_endKerStr_schemeHomOverId AlgebraicGeometry.Scheme.PresheafOfModules.symmetricCategory SheafOfModules.instFaithfulRingSheafPModToPMod SheafOfModules.symmetricCategory AlgebraicGeometry.Scheme.PresheafOfModules.monoidalCategory AlgebraicGeometry.Scheme.PresheafOfModules.monoidalClosed SheafOfModules.instFullRingSheafPModToPMod SheafOfModules.monoidalCategory AlgebraicGeometry.Scheme.Modules.symmetricCategory SheafOfModules.monoidalClosed SheafOfModules.instIsLocalizationPModRingSheafSheafifyFunctorPresheafW SheafOfModules.sheafifyFunctor_monoidal AlgebraicGeometry.Scheme.Modules.monoidalClosed AlgebraicGeometry.instMonoidalPresheafOfModulesModulesSheafify AlgebraicGeometry.Scheme.Modules.monoidalCategory PresheafOfModules.instMonoidalClosed PresheafOfModules.InternalHom.instModuleCarrierObjOppositeCommRingCatSubtypePiFamilyMemAddSubgroupNaturalFamilies PresheafOfModules.InternalHom.instModuleCarrierObjOppositeRingCatCompCommRingCatForget₂RingHomCarrierCarrierAbPresheaf PresheafOfModules.InternalHom.instSMulCarrierObjOppositeCommRingCatSubtypePiFamilyMemAddSubgroupNaturalFamilies AlgebraicGeometry.Scheme.Hom.opensMapFinal AlgebraicGeometry.RelPicard.RigidifiedLineBundle.setoid AlgebraicGeometry.RelPicard.RigidifiedLineBundle.instInhabited AlgebraicGeometry.OModulePresheaf.isScalarTower AlgebraicGeometry.Scheme.OrderedAffineCover.instLinearOrder AlgebraicGeometry.OModulePresheaf.module AlgebraicGeometry.Scheme.OrderedAffineCover.instFintype AlgebraicGeometry.Scheme.OrderedAffineCover.instFintypeIdx AlgebraicGeometry.OModulePresheaf.addCommGroup AlgebraicGeometry.Scheme.OrderedAffineCover.instDecidableEqIdx AlgebraicGeometry.OModulePresheaf.moduleSections TwoChartCech.Sections.M0_moduleA TwoChartCech.Sections.M1_module TwoChartCech.Cover.A01_algebra TwoChartCech.Cover.A0_algebra TwoChartCech.Cover.A1_commRing TwoChartCech.Cover.A1_algebra TwoChartCech.Sections.M01_module TwoChartCech.Sections.M0_addCommGroup TwoChartCech.Sections.M0_tower"
p2m_attr_erase "instance" "TwoChartCech.Sections.M01_addCommGroup TwoChartCech.Cover.A0_commRing TwoChartCech.Sections.M1_tower TwoChartCech.Sections.M01_moduleA TwoChartCech.Sections.M0_module TwoChartCech.Sections.M1_moduleA TwoChartCech.Sections.M1_addCommGroup TwoChartCech.Cover.A01_commRing TwoChartCech.Sections.M01_tower CoherentBaseChange.TwoTermComplex.C0_module CoherentBaseChange.TwoTermComplex.C0_addCommGroup CoherentBaseChange.TwoTermComplex.C1_module CoherentBaseChange.TwoTermComplex.C1_addCommGroup CoherentBaseChange.TwoTermComplex.C0_free CoherentBaseChange.TwoTermComplex.C1_finite CoherentBaseChange.TwoTermComplex.C0_finite CoherentBaseChange.TwoTermComplex.C1_free AlgebraicGeometry.OModulePresheaf.instSubsingletonObjZero AlgebraicGeometry.Scheme.Modules.preservesBinaryProducts_opensMap AlgebraicGeometry.Scheme.Modules.pullback_monoidal AlgebraicGeometry.Scheme.Modules.sheafify_isLocalization' AlgebraicGeometry.Scheme.Modules.preservesTerminal_opensMap AlgebraicGeometry.Scheme.Modules.pullback₀_monoidal AlgebraicGeometry.Scheme.Modules.preservesFiniteProducts_opensMap AlgebraicGeometry.Scheme.Modules.instLiftingPresheafOfModulesSheafifyPresheafWOpensCarrierCarrierCommRingCatGrothendieckTopologyObjFunctorOppositeIsSheafSheafCompPullback₀Pullback PresheafOfModules.PullbackMonoidal.pullback_monoidal PresheafOfModules.PullbackMonoidal.isIso_δ PresheafOfModules.pushforward_laxMonoidal PresheafOfModules.PullbackMonoidal.isIso_η PresheafOfModules.free_monoidal PresheafOfModules.restrictScalars_laxMonoidal PresheafOfModules.PullbackMonoidal.isIso_δ_gS PresheafOfModules.pullback_oplaxMonoidal PresheafOfModules.PullbackMonoidal.instPreservesColimitsOfSizeCompOppositeCommRingCatRingCatForget₂RingHomCarrierCarrierPb PresheafOfModules.pullback_monoidal' AlgebraicGeometry.SmoothOfRelativeDimension.fiberToSpecResidueField AlgebraicGeometry.SmoothOfRelativeDimension.pullback_snd AlgebraicGeometry.SmoothOfRelativeDimension.pullback_fst AlgebraicGeometry.SmoothOfRelativeDimension.smooth_one AlgebraicGeometry.SmoothProperCurve.isIntegral_pullback_Spec_field"
p2m_attr_erase "instance" "AlgebraicGeometry.IsProper.fiberToSpecResidueField AlgebraicCurve.CurveModel.isProper AlgebraicCurve.CurveModel.isIntegral AlgebraicCurve.CurveModel.smooth AlgebraicGeometry.Scheme.LocalRepresentabilityULift.instIsLocallyInjectiveFunUliftYonedaGluedToSheaf AlgebraicGeometry.Scheme.LocalRepresentabilityULift.instIsLocallySurjectiveFunUliftYonedaGluedToSheafOfIsLocallySurjectiveZariskiTopologyDescFunctorOppositeType AlgebraicGeometry.Scheme.LocalRepresentabilityULift.instIsOpenImmersionToGlued AlgebraicGeometry.Scheme.LocalRepresentabilityULift.instIsIsoSheafZariskiTopologyTypeUliftYonedaGluedToSheaf AlgebraicGeometry.RelPicard.instIsOpenImmersionToGlued AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.instFundamentalIdentityOfSumRamificationInertia AlgebraicCurve.Place.instIsScalarTowerResidueFieldRestrictPushforward AlgebraicCurve.Place.instAlgebraResidueFieldRestrictPushforward AlgebraicCurve.Place.instIsLocalHomRestrictInclusion AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions PresheafOfModules.ExteriorPower.instModulePresheafAb AlgebraicGeometry.RelEffCartierDiv.subsingleton_of_degree_zero AlgebraicGeometry.RelEffCartierDiv.isIso_subschemeIota_snd_of_degree_one AlgebraicGeometry.isIso_ker_graphOver_subschemeIota_snd AlgebraicGeometry.isClosedImmersion_graphOver AlgebraicGeometry.FGSubalgebra.instIsDirectedLe AlgebraicGeometry.FGSubalgebra.instQuasiSeparatedSpaceCarrierCarrierCommRingCatObjOppositeSchemeSpecDiagram AlgebraicGeometry.FGSubalgebra.instIsCofilteredOpposite AlgebraicGeometry.FGSubalgebra.instIsAffineObjOppositeSchemeSpecDiagram AlgebraicGeometry.FGSubalgebra.instNonempty AlgebraicGeometry.FGSubalgebra.instNonemptySubtypeLeSubalgebraValFG AlgebraicGeometry.FGSubalgebra.instCompactSpaceCarrierCarrierCommRingCatObjOppositeSchemeSpecDiagram AlgebraicGeometry.FGSubalgebra.instIsDirectedSubtypeLeSubalgebraValFG AlgebraicGeometry.FGSubalgebra.instIsAffineHomMapOppositeSchemeSpecDiagram AlgebraicGeometry.FGSubalgebra.instIsFiltered AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instNeg AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instSMulInt AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instAddCommGroup AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instAdd"
p2m_attr_erase "instance" "AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instSub AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instModuleCarrierObjOppositeOpensCarrierCarrierCommRingCatPresheafOpOpensTop AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instSMulCarrierObjOppositeOpensCarrierCarrierCommRingCatPresheafOpOpensTop AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instSMulNat AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instZero AlgebraicCurve.instHasLocalResidue_of_hasCanonicalLocalResidueK AlgebraicCurve.instHasCanonicalLocalResidueK_of_hasCanonicalLocalResidueKStar AlgebraicCurve.Place.kw_ffgc_finiteDimensional_adicCompletion instAlgebraSubtypeMemValuationSubring_definitions AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersIntegersCompletion ModularCurve.KwF4gRRTate.instAlgebraKAdicCompletionIntegers AlgebraicCurve.Place.kw_ffgc_continuousSMul_adicCompletionComap AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersCompletionCompletion IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions AlgebraicCurve.instHasCanonicalLocalResidueK AlgebraicCurve.Place.instAlgebra_restrictResidueField AlgebraicCurve.Place.instIsScalarTower_restrictResidueField AlgebraicCurve.instHasLocalResidue AlgebraicCurve.HasSeparableResidue.of_perfectField_of_isCurveOver AlgebraicCurve.HasSeparableResidue.of_perfectField AlgebraicCurve.Place.instIsLocalHom_restrictSubringHom AlgebraicCurve.instHasCanonicalLocalResidueKStar ModularCurve.KwNo6Pin.isLocalRing_completion SheafOfModules.isIso_ihomModelToIhom AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instDecidableEqIdx AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instFintype AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instLinearOrder AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instFintypeIdx AlgebraicGeometry.OModulePresheaf.Leray.relAltC_scalarTower AlgebraicGeometry.OModulePresheaf.Leray.ker_relAltd_modΓ AlgebraicGeometry.OModulePresheaf.Leray.relAltC_modΓ AlgebraicGeometry.OModulePresheaf.Leray.biC_abGrp AlgebraicGeometry.OModulePresheaf.Leray.relAltH_modΓ AlgebraicGeometry.OModulePresheaf.Leray.ker_relAltd_smul AlgebraicGeometry.OModulePresheaf.Leray.relAltH_scalarTower"
p2m_attr_erase "instance" "AlgebraicGeometry.OModulePresheaf.Leray.relAltH_smul AlgebraicGeometry.OModulePresheaf.Leray.biC_module DoubleComplex.instModuleE₂I DoubleComplex.Bounded.modR DoubleComplex.instModuleE₂II DoubleComplex.instAddCommGroupE₂II DoubleComplex.Bounded.abGrp DoubleComplex.instAddCommGroupE₂I AlgebraicGeometry.ChowDatum.hι_closed AlgebraicGeometry.ChowDatumProj.hιN_closed AlgebraicGeometry.ChowDatumProj.hp_proper AlgebraicGeometry.ChowDatum.hp_isoU AlgebraicGeometry.ChowDatum.hp_proper AlgebraicGeometry.ProjSpace.algebraAway AlgebraicGeometry.ProjSpace.instIsProperProdOverπ AlgebraicGeometry.ChowDatumProj.hp_isoU AlgebraicGeometry.ProjSpace.isProper_π AlgebraicGeometry.ProjSpace.finiteType_mvPolynomial ProjSpaceCech.GradedModule.H.module ProjSpaceCech.GradedModule.H.addCommGroup ProjSpaceCech.GradedModule.sec.instAdd ProjSpaceCech.GradedModule.sec.instNeg ProjSpaceCech.GradedModule.acg ProjSpaceCech.GradedModule.Frac.setoid ProjSpaceCech.GradedModule.modR ProjSpaceCech.GradedModule.sec.instModule ProjSpaceCech.GradedModule.sec.instAddCommGroup ProjSpaceCech.GradedModule.sec.instZero ProjSpaceCech.GradedModule.Presentation.fJ ProjSpaceCech.GradedModule.sec.instSMul ProjSpaceCech.Twist.H.module ProjSpaceCech.Idx.instFintype ProjSpaceCech.Twist.H.addCommGroup ProjSpaceCech.Idx.instDecidableEq ProjSpaceCech.Twist.Mon.instDecidableEq ProjSpaceCech.Twist.cochain.instAddCommGroup ProjSpaceCech.Twist.cochain.instModule AlgebraicGeometry.FGSubalgebra.tensorStage_directedSystem AlgebraicGeometry.RelEffCartierDiv.isClosedImmersion_subschemeι_resProdMap AlgebraicGeometry.RelEffCartierDiv.isOpenImmersion_resProdMap"
p2m_attr_erase "instance" "AlgebraicCurve.CurveModel.locallyOfFiniteType_gluedToBase AlgebraicCurve.CurveModel.isFractionRing_overlap AlgebraicCurve.CurveModel.isLocallyNoetherian_glued AlgebraicCurve.CurveModel.jacobsonSpace_glued AlgebraicCurve.CurveModel.isOpenImmersion_ι₀ AlgebraicCurve.CurveModel.isIntegral_glued AlgebraicCurve.CurveModel.quasiSeparated_gluedToBase AlgebraicCurve.CurveModel.compactSpace_glued AlgebraicCurve.CurveModel.isIntegral_adjoin_chartRing AlgebraicCurve.CurveModel.isFractionRing_overlap_functionField AlgebraicCurve.CurveModel.isProper_gluedToBase AlgebraicCurve.CurveModel.isOpenImmersion_ιU AlgebraicCurve.CurveModel.isOpenImmersion_f₀ AlgebraicCurve.CurveModel.isOpenImmersion_fInf AlgebraicCurve.CurveModel.isOpenImmersion_ιInf AlgebraicCurve.CurveModel.algebra_overlap_functionField AlgebraicCurve.CurveModel.quasiCompact_gluedToBase AlgebraicCurve.CurveModel.algebraAdjoin AlgebraicCurve.CurveModel.isDedekindDomain_chartRing AlgebraicCurve.CurveModel.isIntegralClosure AlgebraicCurve.CurveModel.finite_chartRing AlgebraicCurve.CurveModel.centre_isPrime AlgebraicCurve.CurveModel.isFractionRing_chartRing AlgebraicCurve.CurveModel.finiteType_chartRing AlgebraicCurve.CurveModel.isNoetherianRing_chartRing AlgebraicCurve.CurveModel.isScalarTower_base_adjoin AlgebraicCurve.CurveModel.isScalarTower_adjoin AlgebraicCurve.CurveModel.chartRing_finitePresentation AlgebraicGeometry.ProjSpace.twistObj.addCommGroup AlgebraicGeometry.ProjSpace.twistFam.module AlgebraicGeometry.ProjSpace.twistObj.module AlgebraicGeometry.ProjSpace.twistObj.moduleSections AlgebraicGeometry.ProjSpace.twistFam.addCommGroup"
p2m_attr_erase "simp" "RegularLocalRingQuotientAscent.dualNumberFst_apply GoodReductionJacobian.RelativeGroupLaw.fibre_inv GoodReductionJacobian.RelativeGroupLaw.fibrePointToBase_coe GoodReductionJacobian.RelativeGroupLaw.fibrePointOfBase_toBase GoodReductionJacobian.RelativeGroupLaw.fibre_mul GoodReductionJacobian.RelativeGroupLaw.fibrePointToBase_ofBase GoodReductionJacobian.RelativeGroupLaw.fibre_one GoodReductionJacobian.RelativeGroupLaw.fibrePointOfBase_coe GoodReductionJacobian.RelativeGroupLaw.nsmul_zero GoodReductionJacobian.RelativeGroupLaw.mem_torsionSubset GoodReductionJacobian.RelativeGroupLaw.nsmul_succ GoodReductionJacobian.RelativeGroupLaw.baseChangePointToBase_ofBase GoodReductionJacobian.RelativeGroupLaw.baseChangePointToBase_coe GoodReductionJacobian.RelativeGroupLaw.baseChangePointOfBase_coe GoodReductionJacobian.RelativeGroupLaw.baseChange_inv GoodReductionJacobian.RelativeGroupLaw.baseChangePointOfBase_toBase GoodReductionJacobian.RelativeGroupLaw.baseChange_mul GoodReductionJacobian.RelativeGroupLaw.baseChange_one NeronModelInfra.NeronModelPropertyBundle.endExtensionEquiv_symm_restrict NeronModelInfra.schemeHomOverComp_id_left NeronModelInfra.schemeHomOverComp_id_right NeronModelInfra.schemeHomOverId_coe NeronModelInfra.NeronModelPropertyBundle.endExtensionEquiv_apply NeronModelInfra.NeronModelPropertyBundle.restrict_endExtensionEquiv_symm NeronModelInfra.schemeHomOverComp_coe NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_fst NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_snd NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_fst NeronSpecialFibreInfra.neronEndRestrictEquiv_apply NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_fst_assoc NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_snd NeronSpecialFibreInfra.neronEndExtension_genericFibreRestrict NeronSpecialFibreInfra.specClosedFibreInclusion_eq NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_fst_assoc NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_snd_assoc NeronSpecialFibreInfra.genericFibreRestrict_neronEndExtension NeronSpecialFibreInfra.homOverId_coe NeronSpecialFibreInfra.homOverComp_coe NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_snd_assoc NeronModelInfra.schemeHomOverNpow_succ"
p2m_attr_erase "simp" "NeronModelInfra.schemeHomOverNpow_zero GoodReductionJacobian.relativeGroupLawOfGrpObj_inv GoodReductionJacobian.relativeGroupLawOfGrpObj_mul GoodReductionJacobian.overHomEquivSchemeHomOver_apply_coe GoodReductionJacobian.relativeGroupLawOfGrpObj_one GoodReductionJacobian.overHomEquivSchemeHomOver_symm_apply_left SheafOfModules.tensorUnit_eq AlgebraicGeometry.Scheme.Modules.tensorUnit_eq PresheafOfModules.InternalHom.presheaf_map_apply PresheafOfModules.InternalHom.curryFamily_app PresheafOfModules.InternalHom.add_app PresheafOfModules.InternalHom.smul_app PresheafOfModules.InternalHom.zero_app PresheafOfModules.ihomObj_map_val PresheafOfModules.ihomFunctor_map PresheafOfModules.InternalHom.restrict_app PresheafOfModules.InternalHom.postcomp_app PresheafOfModules.InternalHom.neg_app PresheafOfModules.curry'_app_val PresheafOfModules.InternalHom.presheaf_obj PresheafOfModules.ihomFunctor_obj PresheafOfModules.ihomObj_obj PresheafOfModules.InternalHom.sub_app PresheafOfModules.ihomMap_app_val AlgebraicGeometry.Scheme.Modules.tensorPow_zero AlgebraicGeometry.Scheme.Modules.tensorPow_succ AlgebraicGeometry.RelPicard.RigidifiedLineBundle.mk.sizeOf_spec AlgebraicGeometry.RelPicard.RigidifiedLineBundle.mk.injEq AlgebraicGeometry.Scheme.OrderedAffineCover.mk.injEq AlgebraicGeometry.OModulePresheaf.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCover.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.mk.injEq AlgebraicGeometry.Scheme.TwoAffineOpenCover.mk.injEq AlgebraicGeometry.Scheme.TwoAffineOpenCover.mk.sizeOf_spec AlgebraicGeometry.Scheme.TwoAffineOpenCover.pullback_U1 AlgebraicGeometry.Scheme.TwoAffineOpenCover.pullback_U0 TwoChartCech.Sections.mk.injEq TwoChartCech.Cover.mk.injEq TwoChartCech.GrothendieckComplex.mk.injEq TwoChartCech.Sections.mk.sizeOf_spec"
p2m_attr_erase "simp" "TwoChartCech.Cover.mk.sizeOf_spec TwoChartCech.Cover.lineBundle_r0_apply TwoChartCech.GrothendieckComplex.mk.sizeOf_spec TwoChartCech.Cover.lineBundle_r1_apply CoherentBaseChange.TwoTermComplex.mk.sizeOf_spec CoherentBaseChange.TwoTermComplex.mk.injEq AlgebraicGeometry.OModulePresheaf.prod_obj AlgebraicGeometry.OModulePresheaf.restrOpen_obj AlgebraicGeometry.OModulePresheaf.DevissageStep.mk.injEq AlgebraicGeometry.OModulePresheaf.pushforward_obj AlgebraicGeometry.OModulePresheaf.im_obj AlgebraicGeometry.OModulePresheaf.pow_obj AlgebraicGeometry.OModulePresheaf.fstHom_app AlgebraicGeometry.OModulePresheaf.ker_obj AlgebraicGeometry.OModulePresheaf.coker_obj AlgebraicGeometry.OModulePresheaf.DevissageStep.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCover.preimage_U AlgebraicGeometry.OModulePresheaf.sndHom_app AlgebraicGeometry.OModulePresheaf.Hom.mk.injEq AlgebraicGeometry.OModulePresheaf.Hom.id_app AlgebraicGeometry.OModulePresheaf.AffHom.appSections_apply AlgebraicGeometry.OModulePresheaf.AffHom.comp_app AlgebraicGeometry.OModulePresheaf.AffSES.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.AffHom.kerMap_coe AlgebraicGeometry.OModulePresheaf.AffHom.id_app AlgebraicGeometry.OModulePresheaf.Hom.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.Hom.toAffHom_app AlgebraicGeometry.OModulePresheaf.SES.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.AffHom.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.Hom.comp_app AlgebraicGeometry.OModulePresheaf.SES.mk.injEq AlgebraicGeometry.OModulePresheaf.AffHom.mk.injEq AlgebraicGeometry.OModulePresheaf.Hom.appSections_apply AlgebraicGeometry.OModulePresheaf.AffSES.mk.injEq PresheafOfModules.freeεIso_hom_app PresheafOfModules.freeμIso_hom_app AlgebraicGeometry.RelPicard.RepresentsRelSubPic.mk.injEq AlgebraicGeometry.RelPicard.SubPicCondition.mk.injEq AlgebraicGeometry.RelPicard.SubPicCondition.mk.sizeOf_spec AlgebraicGeometry.RelPicard.RepresentsRelSubPic.mk.sizeOf_spec"
p2m_attr_erase "simp" "AlgebraicGeometry.SmoothProperCurve.sectionBaseChange_coe_snd AlgebraicGeometry.SmoothProperCurve.sectionBaseChange_coe_fst AlgebraicCurve.CurveModel.mk.injEq AlgebraicCurve.CurveModel.mk.sizeOf_spec AlgebraicCurve.mulAdele_apply AlgebraicCurve.residuePairing_apply_coe AlgebraicCurve.mem_adeleBdd AlgebraicCurve.weilSmul_one AlgebraicCurve.diagonalHom_apply AlgebraicCurve.weilSmul_apply AlgebraicCurve.adeleSpaceMul_coe AlgebraicCurve.mulAdele_one AlgebraicGeometry.SmoothProperCurve.FiniteMapData.twoAffineOpenCover_U1 AlgebraicGeometry.SmoothProperCurve.FiniteMapData.mk.injEq AlgebraicGeometry.SmoothProperCurve.FiniteMapData.mk.sizeOf_spec AlgebraicGeometry.SmoothProperCurve.FiniteMapData.twoAffineOpenCover_U0 AlgebraicGeometry.RelPicard.SubPicCondition.onClasses_mk AlgebraicGeometry.RelPicard.relSubPicPresheaf_map_coe CategoryTheory.Functor.OverTotal.ofFibre_fst CategoryTheory.Functor.overTotal_map_fst AlgebraicGeometry.Scheme.LocalRepresentabilityULift.glueData_J AlgebraicGeometry.Scheme.LocalRepresentabilityULift.uliftYoneda_toGlued_uliftYonedaGluedToSheaf AlgebraicGeometry.Scheme.LocalRepresentabilityULift.glueData_t' AlgebraicGeometry.Scheme.LocalRepresentabilityULift.uliftYoneda_toGlued_uliftYonedaGluedToSheaf_assoc AlgebraicGeometry.Scheme.LocalRepresentabilityULift.uliftYonedaGluedToSheaf_app_toGlued AlgebraicGeometry.Scheme.LocalRepresentabilityULift.glueData_openCover_map AlgebraicGeometry.Scheme.LocalRepresentabilityULift.uliftYonedaGluedToSheaf_app_comp AlgebraicGeometry.Scheme.LocalRepresentabilityULift.glueData_V AlgebraicGeometry.Scheme.LocalRepresentabilityULift.glueData_t AlgebraicGeometry.Scheme.LocalRepresentabilityULift.glueData_U AlgebraicGeometry.Scheme.LocalRepresentabilityULift.glueData_f AlgebraicGeometry.RelPicard.designationOfRepresentableBy_P AlgebraicGeometry.RelPicard.designationOfRepresentableBy_toBase AlgebraicGeometry.RelPicard.rigSection_snd AlgebraicGeometry.RelPicard.RigidifiedLineBundle.ofInvertible_L AlgebraicGeometry.RelPicard.rigSection_snd_assoc AlgebraicGeometry.RelPicard.SubPicGroupCondition.mk.injEq AlgebraicGeometry.RelPicard.SubPicGroupCondition.mk.sizeOf_spec AlgebraicCurve.coe_cechH0Equiv_apply AlgebraicCurve.cechH1ToH1_mk"
p2m_attr_erase "simp" "AlgebraicCurve.lSpaceOn_univ AlgebraicCurve.lSpaceOn_empty AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.Divisor.mapRestrict_single AlgebraicCurve.Divisor.pushforward_single AlgebraicCurve.Place.coe_restrictInclusion AlgebraicCurve.Place.mem_fiber AlgebraicCurve.Place.restrict_toValuationSubring AlgebraicCurve.Divisor.degree_pushforward AlgebraicCurve.Place.restrictResidueMap_residue AlgebraicCurve.Pic0.coe_pushforwardDegZeroHom AlgebraicCurve.Pic0.coe_pullbackDegZeroHom AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Divisor.degree_pushforwardAlong AlgebraicCurve.Pic0.coe_degZeroCorrespondence AlgebraicCurve.Place.mem_fiberAlong"
p2m_attr_erase "simp" "AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.jqNModC_one ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one AlgebraicCurve.Place.differentialCoeff_zero AlgebraicCurve.Place.differentialCoeff_dCoord AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.injEq AlgebraicCurve.TranscendenceTower.mk.injEq AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec AlgebraicCurve.PoleDivisorPackage.mk.injEq AlgebraicGeometry.RelPicard.thetaBundle_def AlgebraicGeometry.RelPicard.picardBundle_def AlgebraicGeometry.RelEffCartierDiv.toRelEffDivisor_ofRelEffDivisor AlgebraicGeometry.RelEffCartierDiv.toRelEffDivisor_I AlgebraicGeometry.mapOnProdOver_fst_assoc AlgebraicGeometry.RelEffCartierDiv.mk.sizeOf_spec AlgebraicGeometry.RelEffCartierDiv.mk.injEq AlgebraicGeometry.mapOnProdOver_snd AlgebraicGeometry.mapOnProdOver_fst AlgebraicGeometry.mapOnProdOver_snd_assoc AlgebraicGeometry.mapOnProdOver_id AlgebraicCurve.RelEffDivisor.mk.sizeOf_spec AlgebraicCurve.mapOnProd_fst AlgebraicCurve.mapOnProd_fst_assoc AlgebraicCurve.mapOnProd_snd"
p2m_attr_erase "simp" "AlgebraicCurve.UnivDivisorPack.mk.injEq AlgebraicCurve.RelEffDivisor.mk.injEq AlgebraicCurve.UnivDivisorPack.mk.sizeOf_spec AlgebraicCurve.mapOnProd_snd_assoc AlgebraicGeometry.Scheme.Modules.exteriorPower_obj PresheafOfModules.exteriorPower_map_ιMulti PresheafOfModules.ExteriorPower.appₗ_apply AlgebraicGeometry.prodKerGraph_one AlgebraicGeometry.fibrePowOver.proj_comp AlgebraicGeometry.prodKerGraph_zero AlgebraicGeometry.RelEffCartierDiv.empty_I AlgebraicGeometry.fibrePowOver.proj_comp_assoc AlgebraicGeometry.graphOver_fst_assoc AlgebraicGeometry.RelEffCartierDiv.toPoint_comp AlgebraicGeometry.RelEffCartierDiv.toPoint_comp_assoc AlgebraicGeometry.graphOver_fst AlgebraicGeometry.RelEffCartierDiv.ofPoint_I AlgebraicGeometry.graphOver_snd AlgebraicGeometry.graphOver_snd_assoc AlgebraicCurve.SymmetricPowerPackage.mk.sizeOf_spec AlgebraicCurve.SymmetricPowerPackage.mk.injEq AlgebraicGeometry.FGSubalgebra.cocone_ι_app_apply AlgebraicGeometry.RelPicard.fst_toProdSpec AlgebraicGeometry.RelPicard.toProdSpec_fst_assoc AlgebraicGeometry.RelPicard.pointsSubBasepointModule_cons AlgebraicGeometry.RelPicard.pointsSubBasepointModule_nil AlgebraicGeometry.RelPicard.fst_toProdSpec_assoc AlgebraicGeometry.RelPicard.toProdSpec_fst AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.sub_app AlgebraicGeometry.Scheme.IdealSheafData.sres_sresTop AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.add_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.mk.sizeOf_spec AlgebraicGeometry.Scheme.IdealSheafData.coe_resLE AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.smul_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.coe_ofLE_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.ideal_range AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.zero_app AlgebraicGeometry.Scheme.IdealSheafData.sres_sres AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.comp_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.neg_app"
p2m_attr_erase "simp" "AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.id_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.coe_mulRight_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.nsmul_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.mk.injEq AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.zsmul_app AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.sizeOf_spec AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.injEq AlgebraicCurve.adeleSingle_coe AlgebraicCurve.kaehlerResidueTermKFam_apply AlgebraicCurve.Place.LocalResidueData.mk.injEq AlgebraicCurve.Place.LocalResidueData.mk.sizeOf_spec AlgebraicCurve.Place.kw_ffgc_adicCompletionComapIntegers_coe AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.sizeOf_spec AlgebraicCurve.Place.mem_simplePoleSubmodule AlgebraicCurve.Place.coe_uniformizerSubring ModularCurve.Lg37.Lg37CompletionSection.mk.injEq AlgebraicCurve.Place.CoefficientFieldSection.mk.injEq AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.injEq ModularCurve.Lg37.Lg37CompletionSection.mk.sizeOf_spec AlgebraicCurve.Place.CoefficientFieldSection.mk.sizeOf_spec AlgebraicCurve.Place.poleSubmodule_one AlgebraicCurve.Place.mem_poleSubmodule AlgebraicGeometry.Scheme.Modules.toUnitSection_ofUnitSection AlgebraicGeometry.Scheme.Modules.pullbackSection_def AlgebraicGeometry.Scheme.Modules.ofUnitSection_toUnitSection PresheafOfModules.InternalHom.IsSheafAux.appAt_toPresheafHom SheafOfModules.ihomSectionsEquivFamily_unit AlgebraicGeometry.Scheme.Modules.restrictHomEquivFamily_apply SheafOfModules.ihomEval_unit_app AlgebraicGeometry.Scheme.Modules.ihomEval_zero_right AlgebraicGeometry.Scheme.Modules.ihomEval_zero_left AlgebraicGeometry.Scheme.Modules.homOfFamily_app_apply SheafOfModules.unit_ihomSectionsEquivFamily AlgebraicGeometry.Scheme.Modules.familyOfHom_app AlgebraicGeometry.Scheme.Modules.restrictUnitIso_hom_app_apply AlgebraicGeometry.Scheme.Modules.restrictUnitIso_inv_app_apply AlgebraicGeometry.Scheme.Modules.restrictHomOfFamily_app_apply AlgebraicGeometry.Scheme.Modules.restrictHomEquivFamily_symm_apply AlgebraicGeometry.Scheme.Modules.tensorSections_zero_right AlgebraicGeometry.Scheme.Modules.map_unitSection"
p2m_attr_erase "simp" "AlgebraicGeometry.Scheme.Modules.tensorSectionsBilin_apply AlgebraicGeometry.Scheme.Modules.tensorPowSection_zero AlgebraicGeometry.Scheme.Modules.tensorSections_zero_left AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_neg AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_zero AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_sub AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_add AlgebraicGeometry.Scheme.OrderedAffineCover.toCoverOf_U AlgebraicGeometry.Scheme.OrderedAffineCoverOf.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCoverOf.mk.injEq AlgebraicGeometry.Scheme.OrderedAffineCover.restrict_U AlgebraicGeometry.OModulePresheaf.Leray.restrictToPreimage_U DoubleComplex.Bounded.mk.injEq DoubleComplex.Bounded.mk.sizeOf_spec DoubleComplex.Convergence.mk.injEq DoubleComplex.Convergence.mk.sizeOf_spec DoubleComplex.SubQuot.mk.sizeOf_spec DoubleComplex.SubQuot.mk.injEq AlgebraicGeometry.ChowDatumProj.mk.sizeOf_spec AlgebraicGeometry.ChowDatum.mk.sizeOf_spec AlgebraicGeometry.ChowDatumProj.mk.injEq AlgebraicGeometry.ChowDatum.mk.injEq ProjSpaceCech.GradedModule.mk.injEq ProjSpaceCech.GradedModule.mk.sizeOf_spec ProjSpaceCech.GradedModule.Frac.mk.sizeOf_spec ProjSpaceCech.GradedModule.Presentation.mk.injEq ProjSpaceCech.GradedModule.Frac.mk.injEq ProjSpaceCech.GradedModule.Presentation.mk.sizeOf_spec ProjSpaceCech.GradedModule.Hom.shift_toLinearMap ProjSpaceCech.GradedModule.Hom.mk.sizeOf_spec ProjSpaceCech.GradedModule.Hom.mk.injEq TwoChartCech.Mumford.dK_apply TwoChartCech.Mumford.ι0_apply TwoChartCech.Mumford.ι1_apply TwoChartCech.KerCoprod.dK_apply TwoChartCech.KerCoprod.ι1_apply TwoChartCech.KerCoprod.ι0_apply AlgebraicGeometry.tilde.functorCompPullbackSpecIso_app AlgebraicGeometry.RelPicard.algEquivZeroGroupCut_toSubPicCondition AlgebraicGeometry.RelPicard.LFP.stageHom_val"
p2m_attr_erase "simp" "AlgebraicGeometry.RelPicard.BaseChange.relSubPicPresheafRestrictIso_hom_app_coe AlgebraicGeometry.RelPicard.BaseChange.relSubPicPresheafRestrictIso_inv_app_coe AlgebraicGeometry.RelPicard.BaseChange.restrict_P AlgebraicGeometry.RelEffCartierDiv.IsUniversal.lift_comp AlgebraicGeometry.RelEffCartierDiv.functor_map_fst AlgebraicGeometry.RelEffCartierDiv.IsUniversal.homEquiv_apply AlgebraicGeometry.RelEffCartierDiv.IsUniversal.lift_pullbackAlong AlgebraicGeometry.RelEffCartierDiv.IsUniversal.homEquiv_symm_apply AlgebraicGeometry.RelEffCartierDiv.IsUniversal.lift_comp_assoc AlgebraicGeometry.RelEffCartierDiv.supportedIn_top AlgebraicGeometry.RelEffCartierDiv.mem_supportedIn_iff AlgebraicGeometry.RelEffCartierDiv.supportedIn_top_eq AlgebraicGeometry.RelEffCartierDiv.restrictAlong_extendAlong AlgebraicGeometry.RelEffCartierDiv.extendAlong_I AlgebraicGeometry.RelEffCartierDiv.resProdMap_snd AlgebraicGeometry.RelEffCartierDiv.restrictAlong_I AlgebraicGeometry.RelEffCartierDiv.extendAlong_restrictAlong AlgebraicGeometry.RelEffCartierDiv.resProdMap_fst_assoc AlgebraicGeometry.RelEffCartierDiv.resProdMap_snd_assoc AlgebraicGeometry.RelEffCartierDiv.resProdMap_fst CoherentBaseChange.FibreH0Family.mk.sizeOf_spec CoherentBaseChange.FibreH0Family.mk.injEq AlgebraicGeometry.Scheme.Modules.ProjPresentation.mk.injEq AlgebraicGeometry.Scheme.Modules.ProjPresentation.mk.sizeOf_spec AlgebraicCurve.CurveModel.coe_gInf AlgebraicCurve.CurveModel.coe_tInvChart AlgebraicCurve.CurveModel.ιInf_gluedToBase_assoc AlgebraicCurve.CurveModel.ιInf_gluedToBase AlgebraicCurve.CurveModel.primeOfι₀_asIdeal AlgebraicCurve.CurveModel.coe_tChart AlgebraicCurve.CurveModel.ι₀_gluedToBase_assoc AlgebraicCurve.CurveModel.primeOfιInf_asIdeal AlgebraicCurve.CurveModel.ι₀_gluedToBase AlgebraicCurve.CurveModel.coe_tma AlgebraicCurve.CurveModel.coe_primeEquivChartPlaces AlgebraicGeometry.ProjSpace.twistObj.mk.injEq AlgebraicGeometry.ProjSpace.twistObj.zero_val AlgebraicGeometry.ProjSpace.twistObj.add_val AlgebraicGeometry.ProjSpace.twist_res_val AlgebraicGeometry.ProjSpace.twist_smul_val"
p2m_attr_erase "simp" "AlgebraicGeometry.ProjSpace.twistGradeToObj_val AlgebraicGeometry.ProjSpace.twistObj.smul_val AlgebraicGeometry.ProjSpace.twistGradeEquiv_apply_val AlgebraicGeometry.ProjSpace.twistObj.mk.sizeOf_spec AlgebraicGeometry.schemeFibreEndo_snd AlgebraicGeometry.schemeFibreEndo_fst"

set_option autoImplicit false

universe u

p2m_open "CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra~schemeHomOverComp~schemeHomOverComp_coe GoodReductionJacobian"
open CerednikDrinfeld.QM CerednikDrinfeld.QM.FakeEllipticCurve
open scoped Quaternion

namespace ALGlue

variable {S : Type u} [CommRing S]

section IsoPts

variable {A A' : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of S)} {f' : A' ⟶ Spec (CommRingCat.of S)}

theorem inv_over (e : A ≅ A') (he : e.hom ≫ f' = f) : e.inv ≫ f = f' := by
  rw [← he, Iso.inv_hom_id_assoc]

@[scoped simp] theorem mapPt_inv_hom (e : A ≅ A') (he : e.hom ≫ f' = f) {T : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of S)}
    (P : SchemeHomOver t f) : mapPt e.inv (inv_over e he) (mapPt e.hom he P) = P := by
  apply Subtype.ext; simp [mapPt_coe]

@[scoped simp] theorem mapPt_hom_inv (e : A ≅ A') (he : e.hom ≫ f' = f) {T : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of S)}
    (P : SchemeHomOver t f') : mapPt e.hom he (mapPt e.inv (inv_over e he) P) = P := by
  apply Subtype.ext; simp [mapPt_coe]

theorem mapPt_hom_injective (e : A ≅ A') (he : e.hom ≫ f' = f) {T : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of S)} :
    Function.Injective (mapPt (T := T) (t := t) e.hom he) := by
  intro P Q h
  rw [← mapPt_inv_hom e he P, h, mapPt_inv_hom]

theorem mapPt_comp {A'' : Scheme.{u}} {f'' : A'' ⟶ Spec (CommRingCat.of S)} (θ : A ⟶ A') (hθ : θ ≫ f' = f)
    (θ' : A' ⟶ A'') (hθ' : θ' ≫ f'' = f') {T : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of S)} (P : SchemeHomOver t f) :
    mapPt (θ ≫ θ') (by rw [Category.assoc, hθ', hθ]) P = mapPt θ' hθ' (mapPt θ hθ P) := by
  apply Subtype.ext; simp [mapPt_coe]

end IsoPts

variable {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} {N : ℕ}

theorem inv_mul {E E' : FakeEllipticCurve Λ N S} (e : E.A ≅ E'.A) (he : e.hom ≫ E'.f = E.f)
    (hmul : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of S)) (P Q : SchemeHomOver t E.f),
      mapPt e.hom he (E.L.mul t P Q) = E'.L.mul t (mapPt e.hom he P) (mapPt e.hom he Q))
    {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of S)) (P Q : SchemeHomOver t E'.f) :
    mapPt e.inv (inv_over e he) (E'.L.mul t P Q) = E.L.mul t (mapPt e.inv (inv_over e he) P) (mapPt e.inv (inv_over e he) Q) := by
  apply mapPt_hom_injective e he
  rw [mapPt_hom_inv, hmul, mapPt_hom_inv, mapPt_hom_inv]

theorem inv_act {E E' : FakeEllipticCurve Λ N S} (e : E.A ≅ E'.A)
    (hact : ∀ x : ↥Λ, E.act x ≫ e.hom = e.hom ≫ E'.act x) (x : ↥Λ) :
    E'.act x ≫ e.inv = e.inv ≫ E.act x := by
  rw [← cancel_epi e.hom, ← Category.assoc, ← hact x, Category.assoc, e.hom_inv_id, Category.comp_id, e.hom_inv_id_assoc]

theorem iso_symm {E E' : FakeEllipticCurve Λ N S} (h : FakeEllipticCurve.Iso E E') : FakeEllipticCurve.Iso E' E := by
  obtain ⟨e, he, hmul, hact, hlev⟩ := h
  refine ⟨e.symm, inv_over e he, ?_, ?_, ?_⟩
  · intro T t P Q; exact inv_mul e he hmul t P Q
  · intro x; exact inv_act e hact x
  · intro T t P
    change FactorsThrough E'.lev P ↔ FactorsThrough E.lev (mapPt e.inv (inv_over e he) P)
    rw [hlev t (mapPt e.inv (inv_over e he) P), mapPt_hom_inv]

theorem iso_trans {E E' E'' : FakeEllipticCurve Λ N S} (h : FakeEllipticCurve.Iso E E') (h' : FakeEllipticCurve.Iso E' E'') :
    FakeEllipticCurve.Iso E E'' := by
  obtain ⟨e, he, hmul, hact, hlev⟩ := h
  obtain ⟨e', he', hmul', hact', hlev'⟩ := h'
  have hee : (e ≪≫ e').hom ≫ E''.f = E.f := by rw [Iso.trans_hom, Category.assoc, he', he]
  have hpt : ∀ {T : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of S)} (P : SchemeHomOver t E.f),
      mapPt (e ≪≫ e').hom hee P = mapPt e'.hom he' (mapPt e.hom he P) := fun P => by
    apply Subtype.ext; simp [mapPt_coe]
  refine ⟨e ≪≫ e', hee, ?_, ?_, ?_⟩
  · intro T t P Q; rw [hpt, hpt, hpt, hmul, hmul']
  · intro x; rw [Iso.trans_hom, ← Category.assoc, hact, Category.assoc, hact', Category.assoc]
  · intro T t P; rw [hpt, hlev, hlev']

theorem iso_refl (E : FakeEllipticCurve Λ N S) : FakeEllipticCurve.Iso E E := by
  have h1 : (Iso.refl E.A).hom ≫ E.f = E.f := by simp
  have hid : ∀ {T : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of S)} (P : SchemeHomOver t E.f),
      mapPt (Iso.refl E.A).hom h1 P = P := fun P => Subtype.ext (by simp [mapPt_coe])
  refine ⟨Iso.refl _, h1, ?_, ?_, ?_⟩
  · intro T t P Q; rw [hid, hid, hid]
  · intro x; simp
  · intro T t P; rw [hid]

theorem isAtkinLehnerQuotient_congr (r : ℕ) {E E₁ F F₁ : FakeEllipticCurve Λ N S}
    (h : E.IsAtkinLehnerQuotient r E₁) (hE : FakeEllipticCurve.Iso E F) (hE₁ : FakeEllipticCurve.Iso E₁ F₁) :
    F.IsAtkinLehnerQuotient r F₁ := by
  obtain ⟨e, he, emul, eact, elev⟩ := hE
  obtain ⟨e₁, he₁, e₁mul, e₁act, e₁lev⟩ := hE₁
  obtain ⟨φr, hφr, ψr, hψr, hφhom, hψhom, hφlin, hψlin, hcomp, hker, hlev⟩ := h
  have hφ' : (e.inv ≫ φr ≫ e₁.hom) ≫ F₁.f = F.f := by
    rw [Category.assoc, Category.assoc, he₁, hφr, inv_over e he]
  have hψ' : (e₁.inv ≫ ψr ≫ e.hom) ≫ F.f = F₁.f := by
    rw [Category.assoc, Category.assoc, he, hψr, inv_over e₁ he₁]

  have tφ : ∀ {T : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of S)} (P : SchemeHomOver t F.f),
      mapPt (e.inv ≫ φr ≫ e₁.hom) hφ' P = mapPt e₁.hom he₁ (mapPt φr hφr (mapPt e.inv (inv_over e he) P)) :=
    fun P => Subtype.ext (by simp [mapPt_coe])
  have tψ : ∀ {T : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of S)} (P : SchemeHomOver t F₁.f),
      mapPt (e₁.inv ≫ ψr ≫ e.hom) hψ' P = mapPt e.hom he (mapPt ψr hψr (mapPt e₁.inv (inv_over e₁ he₁) P)) :=
    fun P => Subtype.ext (by simp [mapPt_coe])

  have one_e : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of S)), mapPt e.inv (inv_over e he) (F.L.one t) = E.L.one t := by
    intro T t
    set x := mapPt e.inv (inv_over e he) (F.L.one t) with hx
    have hxx : E.L.mul t x x = x := by rw [hx, ← inv_mul e he emul, F.L.one_mul]
    letI := E.L.pointGroup t
    have h2 : x * x = x * 1 := by rw [mul_one]; exact hxx
    exact mul_left_cancel h2
  have one_e₁ : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of S)), mapPt e₁.hom he₁ (E₁.L.one t) = F₁.L.one t := by
    intro T t
    set x := mapPt e₁.hom he₁ (E₁.L.one t) with hx
    have hxx : F₁.L.mul t x x = x := by rw [hx, ← e₁mul, E₁.L.one_mul]
    letI := F₁.L.pointGroup t
    have h2 : x * x = x * 1 := by rw [mul_one]; exact hxx
    exact mul_left_cancel h2
  refine ⟨e.inv ≫ φr ≫ e₁.hom, hφ', e₁.inv ≫ ψr ≫ e.hom, hψ', ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro T t P Q
    rw [tφ, tφ, tφ, inv_mul e he emul, hφhom, e₁mul]
  · intro T t P Q
    rw [tψ, tψ, tψ, inv_mul e₁ he₁ e₁mul, hψhom, emul]
  · intro x
    calc F.act x ≫ (e.inv ≫ φr ≫ e₁.hom) = (F.act x ≫ e.inv) ≫ φr ≫ e₁.hom := by simp only [Category.assoc]
      _ = e.inv ≫ (E.act x ≫ φr) ≫ e₁.hom := by rw [inv_act e eact x]; simp only [Category.assoc]
      _ = e.inv ≫ φr ≫ (E₁.act x ≫ e₁.hom) := by rw [hφlin x]; simp only [Category.assoc]
      _ = (e.inv ≫ φr ≫ e₁.hom) ≫ F₁.act x := by rw [e₁act x]; simp only [Category.assoc]
  · intro x
    calc F₁.act x ≫ (e₁.inv ≫ ψr ≫ e.hom) = (F₁.act x ≫ e₁.inv) ≫ ψr ≫ e.hom := by simp only [Category.assoc]
      _ = e₁.inv ≫ (E₁.act x ≫ ψr) ≫ e.hom := by rw [inv_act e₁ e₁act x]; simp only [Category.assoc]
      _ = e₁.inv ≫ ψr ≫ (E.act x ≫ e.hom) := by rw [hψlin x]; simp only [Category.assoc]
      _ = (e₁.inv ≫ ψr ≫ e.hom) ≫ F.act x := by rw [eact x]; simp only [Category.assoc]
  · intro hr
    obtain ⟨h1, h2⟩ := hcomp hr
    constructor
    · simp only [Category.assoc]
      rw [e₁.hom_inv_id_assoc, ← Category.assoc φr, h1, eact, e.inv_hom_id_assoc]
    · simp only [Category.assoc]
      rw [e.hom_inv_id_assoc, ← Category.assoc ψr, h2, e₁act, e₁.inv_hom_id_assoc]
  · intro T t P
    rw [tφ, ← one_e₁ t, (mapPt_hom_injective e₁ he₁).eq_iff, hker]
    refine forall_congr' fun m => forall_congr' fun n => forall_congr' fun _ => ?_

    have hconj : pushPt (E.act m) (E.act_over m) (mapPt e.inv (inv_over e he) P) =
        mapPt e.inv (inv_over e he) (pushPt (F.act m) (F.act_over m) P) := by
      apply Subtype.ext
      simp only [pushPt, mapPt_coe, Category.assoc, inv_act e eact m]
    rw [hconj, ← one_e t]
    constructor
    · intro hP
      have := congrArg (mapPt e.hom he) hP
      rwa [mapPt_hom_inv, mapPt_hom_inv] at this
    · intro hP; rw [hP]
  · intro T t P hP
    rw [tφ, ← e₁lev]
    apply hlev
    rw [elev, mapPt_hom_inv]
    exact hP

end ALGlue
p2m_reactivate "P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_iso_of_iso_of_isAtkinLehnerQuotient_of_isAtkinLehnerQuotient.ALGlue"

namespace ALQUniqueGen
p2m_open "CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra~schemeHomOverComp~schemeHomOverComp_coe GoodReductionJacobian"
open CerednikDrinfeld CerednikDrinfeld.QM CerednikDrinfeld.QM.FakeEllipticCurve QuaternionAlgebra ALGlue
open scoped Quaternion

variable {S : Type} [CommRing S] {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} {N : ℕ}

theorem mapPt_one {E E' : FakeEllipticCurve Λ N S} (φ : E.A ⟶ E'.A) (hφ : φ ≫ E'.f = E.f)
    (hmul : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of S)) (P Q : SchemeHomOver t E.f),
      mapPt φ hφ (E.L.mul t P Q) = E'.L.mul t (mapPt φ hφ P) (mapPt φ hφ Q))
    {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of S)) : mapPt φ hφ (E.L.one t) = E'.L.one t := by
  set x := mapPt φ hφ (E.L.one t) with hx
  have hxx : E'.L.mul t x x = x := by rw [hx, ← hmul, E.L.one_mul]
  letI := E'.L.pointGroup t
  have h2 : x * x = x * 1 := by rw [mul_one]; exact hxx
  exact mul_left_cancel h2

theorem mapPt_comp {E E' : FakeEllipticCurve Λ N S} (φ : E.A ⟶ E'.A) (hφ : φ ≫ E'.f = E.f)
    {T T' : Scheme.{0}} {t : T ⟶ Spec (CommRingCat.of S)} {t' : T' ⟶ Spec (CommRingCat.of S)} (ψ : T' ⟶ T) (hψ : ψ ≫ t = t')
    (P : SchemeHomOver t E.f) :
    mapPt φ hφ (schemeHomOverComp ψ hψ P) = schemeHomOverComp ψ hψ (mapPt φ hφ P) :=
  Subtype.ext (by simp only [mapPt_coe, schemeHomOverComp_coe, Category.assoc])

theorem core
    {N q q' : ℕ} [NeZero N] [Fact q.Prime] [Fact q'.Prime] (hqN : ¬ q ∣ N) (hq'N : ¬ q' ∣ N)
    {Λ : Submodule ℤ ℍ[ℚ, a, b]} (hΛ : IsMaximalOrder Λ) (r : ℕ) (hr : r = q ∨ r = q')
    (E E' E'' : FakeEllipticCurve Λ N S)
    (h' : E.IsAtkinLehnerQuotient r E') (h'' : E.IsAtkinLehnerQuotient r E'') : FakeEllipticCurve.Iso E' E'' := by
  classical
  obtain ⟨φ', hφ', ψ', hψ', mφ', mψ', aφ', aψ', c', k', l'⟩ := h'
  obtain ⟨φ'', hφ'', ψ'', hψ'', mφ'', mψ'', aφ'', aψ'', c'', k'', l''⟩ := h''
  have hO : IsOrder Λ := hΛ.isOrder
  have hrp : r.Prime := by rcases hr with rfl | rfl <;> exact Fact.out
  have hrN : ¬ r ∣ N := by rcases hr with rfl | rfl <;> assumption
  have hcopN : Nat.Coprime r N := (Nat.Prime.coprime_iff_not_dvd hrp).2 hrN
  have hrΛ : ((r : ℚ) : ℍ[ℚ, a, b]) ∈ Λ := by
    have : ((r : ℚ) : ℍ[ℚ, a, b]) = (r : ℤ) • (1 : ℍ[ℚ, a, b]) := by rw [zsmul_eq_mul, mul_one]; norm_cast
    rw [this]; exact Λ.smul_mem _ hO.one_mem

  have nsm : ∀ (A B : FakeEllipticCurve Λ N S) (φ : A.A ⟶ B.A) (hφ : φ ≫ B.f = A.f)
      (ψ : B.A ⟶ A.A) (hψ : ψ ≫ A.f = B.f) (hc : φ ≫ ψ = A.act ⟨((r : ℚ) : ℍ[ℚ, a, b]), hrΛ⟩)
      {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of S)) (P : SchemeHomOver t A.f),
      mapPt ψ hψ (mapPt φ hφ P) = nsmulPt A.L t r P := by
    intro A B φ hφ ψ hψ hc T t P
    rw [← pushPt_act_natCast_eq_nsmulPt A hO.one_mem r hrΛ t P]
    apply Subtype.ext
    simp only [mapPt_coe, pushPt, Category.assoc, hc]
  have hψφ' := fun {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of S)) (P : SchemeHomOver t E.f) => nsm E E' φ' hφ' ψ' hψ' (c' hrΛ).1 t P
  have hφψ' := fun {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of S)) (P : SchemeHomOver t E'.f) => nsm E' E ψ' hψ' φ' hφ' (c' hrΛ).2 t P
  have hψφ'' := fun {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of S)) (P : SchemeHomOver t E.f) => nsm E E'' φ'' hφ'' ψ'' hψ'' (c'' hrΛ).1 t P
  have hφψ'' := fun {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of S)) (P : SchemeHomOver t E''.f) => nsm E'' E ψ'' hψ'' φ'' hφ'' (c'' hrΛ).2 t P

  obtain ⟨hfin', hfl', -, hsur'⟩ := CerednikDrinfeld.QM.FakeEllipticCurve.isFinite_flat_surjective_of_mapPt_mapPt_eq_nsmulPt
    E E' φ' hφ' mφ' ψ' hψ' r hrp.pos hψφ' hφψ'
  obtain ⟨hfin'', hfl'', -, hsur''⟩ := CerednikDrinfeld.QM.FakeEllipticCurve.isFinite_flat_surjective_of_mapPt_mapPt_eq_nsmulPt
    E E'' φ'' hφ'' mφ'' ψ'' hψ'' r hrp.pos hψφ'' hφψ''
  haveI := hfin'; haveI := hfl'; haveI := hsur'; haveI := hfin''; haveI := hfl''; haveI := hsur''
  haveI : EffectiveEpi φ' := inferInstance
  haveI : EffectiveEpi φ'' := inferInstance

  have coeq : ∀ (A B C : FakeEllipticCurve Λ N S) (α : A.A ⟶ B.A) (hα : α ≫ B.f = A.f) (β : A.A ⟶ C.A) (hβ : β ≫ C.f = A.f)
      (mα : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of S)) (P Q : SchemeHomOver t A.f),
        mapPt α hα (A.L.mul t P Q) = B.L.mul t (mapPt α hα P) (mapPt α hα Q))
      (mβ : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of S)) (P Q : SchemeHomOver t A.f),
        mapPt β hβ (A.L.mul t P Q) = C.L.mul t (mapPt β hβ P) (mapPt β hβ Q))
      (hker : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of S)) (P : SchemeHomOver t A.f),
        mapPt α hα P = B.L.one t → mapPt β hβ P = C.L.one t)
      {Z : Scheme.{0}} (g₁ g₂ : Z ⟶ A.A), g₁ ≫ α = g₂ ≫ α → g₁ ≫ β = g₂ ≫ β := by
    intro A B C α hα β hβ mα mβ hker Z g₁ g₂ hg
    let t : Z ⟶ Spec (CommRingCat.of S) := g₁ ≫ A.f
    have hg₂ : g₂ ≫ A.f = t := by
      show g₂ ≫ A.f = g₁ ≫ A.f
      rw [← hα, ← Category.assoc, ← hg, Category.assoc]
    let P : SchemeHomOver t A.f := ⟨g₁, rfl⟩
    let Q : SchemeHomOver t A.f := ⟨g₂, hg₂⟩
    letI := A.L.pointGroup t; letI := B.L.pointGroup t; letI := C.L.pointGroup t
    let Fα : SchemeHomOver t A.f →* SchemeHomOver t B.f :=
      { toFun := mapPt α hα, map_one' := mapPt_one α hα mα t, map_mul' := fun X Y => mα t X Y }
    let Fβ : SchemeHomOver t A.f →* SchemeHomOver t C.f :=
      { toFun := mapPt β hβ, map_one' := mapPt_one β hβ mβ t, map_mul' := fun X Y => mβ t X Y }
    have hPQ : Fα P = Fα Q := Subtype.ext hg
    have h1 : Fα (P * Q⁻¹) = 1 := by rw [map_mul, map_inv, hPQ, mul_inv_cancel]
    have h2 : Fβ (P * Q⁻¹) = 1 := hker t _ h1
    have h3 : Fβ P = Fβ Q := by
      rw [map_mul, map_inv] at h2
      exact mul_inv_eq_one.1 h2
    exact congrArg Subtype.val h3
  have k12 : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of S)) (P : SchemeHomOver t E.f),
      mapPt φ' hφ' P = E'.L.one t → mapPt φ'' hφ'' P = E''.L.one t := fun t P h => (k'' t P).2 ((k' t P).1 h)
  have k21 : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of S)) (P : SchemeHomOver t E.f),
      mapPt φ'' hφ'' P = E''.L.one t → mapPt φ' hφ' P = E'.L.one t := fun t P h => (k' t P).2 ((k'' t P).1 h)

  let χ : E'.A ⟶ E''.A := EffectiveEpi.desc φ' φ'' (coeq E E' E'' φ' hφ' φ'' hφ'' mφ' mφ'' k12)
  have hφχ : φ' ≫ χ = φ'' := EffectiveEpi.fac φ' φ'' _
  let χ' : E''.A ⟶ E'.A := EffectiveEpi.desc φ'' φ' (coeq E E'' E' φ'' hφ'' φ' hφ' mφ'' mφ' k21)
  have hφχ' : φ'' ≫ χ' = φ' := EffectiveEpi.fac φ'' φ' _
  have hχχ' : χ ≫ χ' = 𝟙 _ := by
    rw [← cancel_epi φ', ← Category.assoc, hφχ, hφχ', Category.comp_id]
  have hχ'χ : χ' ≫ χ = 𝟙 _ := by
    rw [← cancel_epi φ'', ← Category.assoc, hφχ', hφχ, Category.comp_id]
  have hχ : χ ≫ E''.f = E'.f := by
    rw [← cancel_epi φ', ← Category.assoc, hφχ, hφ'', hφ']
  let e : E'.A ≅ E''.A := ⟨χ, χ', hχχ', hχ'χ⟩

  have tχ : ∀ {T : Scheme.{0}} {t : T ⟶ Spec (CommRingCat.of S)} (P : SchemeHomOver t E.f),
      mapPt χ hχ (mapPt φ' hφ' P) = mapPt φ'' hφ'' P :=
    fun P => Subtype.ext (by simp only [mapPt_coe, Category.assoc, hφχ])
  refine ⟨e, hχ, ?_, ?_, ?_⟩
  ·
    intro T t P Q
    show mapPt χ hχ (E'.L.mul t P Q) = E''.L.mul t (mapPt χ hχ P) (mapPt χ hχ Q)

    let T₁ := pullback P.1 φ'
    let π₁ : T₁ ⟶ T := pullback.fst P.1 φ'
    haveI : Flat π₁ := inferInstance
    haveI : Surjective π₁ := inferInstance

    let T₂ := pullback (π₁ ≫ Q.1) φ'
    let π₂ : T₂ ⟶ T₁ := pullback.fst (π₁ ≫ Q.1) φ'
    haveI : Flat π₂ := inferInstance
    haveI : Surjective π₂ := inferInstance
    let ψ : T₂ ⟶ T := π₂ ≫ π₁
    haveI : Epi π₁ := Flat.epi_of_flat_of_surjective π₁
    haveI : Epi π₂ := Flat.epi_of_flat_of_surjective π₂
    haveI : Epi ψ := epi_comp π₂ π₁
    have hψt : ψ ≫ t = ψ ≫ t := rfl

    let Pl : SchemeHomOver (ψ ≫ t) E.f := ⟨π₂ ≫ pullback.snd P.1 φ', by
      show (π₂ ≫ pullback.snd P.1 φ') ≫ E.f = (π₂ ≫ π₁) ≫ t
      rw [← hφ']; simp only [Category.assoc]
      rw [← pullback.condition_assoc, P.2]⟩
    let Ql : SchemeHomOver (ψ ≫ t) E.f := ⟨pullback.snd (π₁ ≫ Q.1) φ', by
      show pullback.snd (π₁ ≫ Q.1) φ' ≫ E.f = (π₂ ≫ π₁) ≫ t
      rw [← hφ', ← pullback.condition_assoc]; simp only [Category.assoc]; rw [Q.2]⟩
    have hPl : mapPt φ' hφ' Pl = schemeHomOverComp ψ hψt P := by
      apply Subtype.ext
      show (π₂ ≫ pullback.snd P.1 φ') ≫ φ' = (π₂ ≫ π₁) ≫ P.1
      simp only [Category.assoc]
      rw [pullback.condition]
    have hQl : mapPt φ' hφ' Ql = schemeHomOverComp ψ hψt Q := by
      apply Subtype.ext
      show pullback.snd (π₁ ≫ Q.1) φ' ≫ φ' = (π₂ ≫ π₁) ≫ Q.1
      rw [Category.assoc, ← pullback.condition]

    have key : schemeHomOverComp ψ hψt (mapPt χ hχ (E'.L.mul t P Q)) =
        schemeHomOverComp ψ hψt (E''.L.mul t (mapPt χ hχ P) (mapPt χ hχ Q)) := by
      rw [← mapPt_comp, E'.L.mul_natural t (ψ ≫ t) ψ hψt, ← hPl, ← hQl, ← mφ', tχ, mφ'', ← tχ, ← tχ, hPl, hQl,
        mapPt_comp, mapPt_comp, ← E''.L.mul_natural t (ψ ≫ t) ψ hψt]
    apply Subtype.ext
    rw [← cancel_epi ψ]
    exact congrArg Subtype.val key
  ·
    intro x
    rw [← cancel_epi φ']
    show φ' ≫ E'.act x ≫ χ = φ' ≫ χ ≫ E''.act x
    rw [← Category.assoc, ← aφ' x, Category.assoc, hφχ, aφ'' x, ← Category.assoc φ' χ, hφχ]
  ·
    intro T t R
    show FactorsThrough E'.lev R ↔ FactorsThrough E''.lev (mapPt χ hχ R)
    have LO' := CerednikDrinfeld.QM.FakeEllipticCurve.factorsThrough_lev_iff_exists_mapPt_eq_of_coprime
      E E' φ' hφ' mφ' ψ' hψ' r hcopN hψφ' l' t R
    have LO'' := fun (R'' : SchemeHomOver t E''.f) =>
      CerednikDrinfeld.QM.FakeEllipticCurve.factorsThrough_lev_iff_exists_mapPt_eq_of_coprime
        E E'' φ'' hφ'' mφ'' ψ'' hψ'' r hcopN hψφ'' l'' t R''
    have χinj : ∀ (X Y : SchemeHomOver t E'.f), mapPt χ hχ X = mapPt χ hχ Y → X = Y := by
      intro X Y hXY
      apply Subtype.ext
      haveI : IsIso χ := ⟨⟨χ', hχχ', hχ'χ⟩⟩
      rw [← cancel_mono χ]
      exact congrArg Subtype.val hXY
    constructor
    · intro hR
      obtain ⟨P, hP, rfl⟩ := LO'.1 hR
      show FactorsThrough E''.lev (mapPt χ hχ (mapPt φ' hφ' P))
      rw [tχ]; exact l'' t P hP
    · intro hR
      obtain ⟨P, hP, hPe⟩ := (LO'' (mapPt χ hχ R)).1 hR
      have : mapPt φ' hφ' P = R := χinj _ _ (by rw [tχ, hPe])
      rw [← this]; exact l' t P hP

end ALQUniqueGen
p2m_reactivate "P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_iso_of_iso_of_isAtkinLehnerQuotient_of_isAtkinLehnerQuotient.ALGlue"

open ALQUniqueGen ALGlue CerednikDrinfeld CerednikDrinfeld.QM QuaternionAlgebra in
theorem solution
    {q q' : ℕ} [Fact q.Prime] [Fact q'.Prime] (hqq' : q' ≠ q)
    {a b : ℚ} (hB : IsIndefiniteRamifiedExactlyAt a b q q')
    (Λ : Submodule ℤ ℍ[ℚ, a, b]) (hΛ : IsMaximalOrder Λ) {N : ℕ} [NeZero N] (hqN : ¬ q ∣ N) (hq'N : ¬ q' ∣ N)
    (r : ℕ) (hr : r = q ∨ r = q')
    (S : Type) [CommRing S] (E E₁ E' E₁' : QM.FakeEllipticCurve Λ N S)
    (hE : QM.FakeEllipticCurve.Iso E E₁) (h : QM.FakeEllipticCurve.IsAtkinLehnerQuotient r E E')
    (h₁ : QM.FakeEllipticCurve.IsAtkinLehnerQuotient r E₁ E₁') :
    QM.FakeEllipticCurve.Iso E' E₁' := by

  have h₁' : QM.FakeEllipticCurve.IsAtkinLehnerQuotient r E E₁' :=
    CerednikDrinfeld.QM.FakeEllipticCurve.isAtkinLehnerQuotient_of_iso_of_iso r E₁ E₁' E E₁' h₁ (ALGlue.iso_symm hE) (ALGlue.iso_refl E₁')
  exact core hqN hq'N hΛ r hr E E' E₁' h h₁'

end S_CerednikDrinfeld_QM_FakeEllipticCurve_iso_of_iso_of_isAtkinLehnerQuotient_of_isAtkinLehnerQuotient
end P2MW
export P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_iso_of_iso_of_isAtkinLehnerQuotient_of_isAtkinLehnerQuotient (solution)
