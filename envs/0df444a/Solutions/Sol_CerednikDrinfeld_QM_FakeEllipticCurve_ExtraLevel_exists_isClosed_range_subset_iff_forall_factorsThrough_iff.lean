-- Prove2me | solution 1 for CerednikDrinfeld.QM.FakeEllipticCurve.ExtraLevel.exists_isClosed_range_subset_iff_forall_factorsThrough_iff
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.837917+00:00
-- url     : https://prove2.me/submissions/40b025ad-b7fb-5838-856a-88b66f43e14c

import Definitions.Def_CerednikDrinfeld_QMModuli
import Definitions.Def_CerednikDrinfeld_QMFineModuli
import Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_exists_opens_schemeKer_iso_of_isClosedImmersion_of_nsmulPt_eq_one
import Theorems.Thm_AlgebraicGeometry_eq_of_base_closedPoint_eq_and_exists_base_closedPoint_eq_and_isClosed_of_isAlgClosed
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawKernel
import Mathlib
import Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_isFinite_and_etale_schemeKerStr_of_isUnit
import Theorems.Thm_AlgebraicGeometry_isClopen_preimage_diagonal_of_formallyUnramified_of_isSeparated
import Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_pushPt_act_natCast_eq_nsmulPt
import Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_exists_isPullback_levelIff
import Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_finite_and_natCard_torsion_eq_pow_four_of_isUnit
import Theorems.Thm_QuaternionAlgebra_IsOrder_relIndex_span_smul_eq_pow_four
import Theorems.Thm_AlgebraicGeometry_exists_comp_fromSpecResidueField_eq_of_range_subset_singleton
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_ExtraLevel_exists_isClosed_range_subset_iff_forall_factorsThrough_iff
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

p2m_open "CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra~schemeHomOverComp~schemeHomOverComp_coe GoodReductionJacobian QuaternionAlgebra CerednikDrinfeld CerednikDrinfeld.QM"
open scoped Quaternion

universe u

namespace GenLocus10

section PointAlgebra
variable {R : Type u} [CommRing R] {A : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of R)}

theorem comp_one (L : RelativeGroupLaw R f)
    {T T' : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (t' : T' ⟶ Spec (CommRingCat.of R)) (ψ : T' ⟶ T)
    (hψ : ψ ≫ t = t') : ψ ≫ (L.one t).1 = (L.one t').1 := by
  have hm := L.mul_natural t t' ψ hψ
  have h : schemeHomOverComp ψ hψ (L.one t) =
      L.mul t' (schemeHomOverComp ψ hψ (L.one t)) (schemeHomOverComp ψ hψ (L.one t)) := by
    conv_lhs => rw [← L.one_mul t (L.one t)]
    exact hm _ _
  have : schemeHomOverComp ψ hψ (L.one t) = L.one t' := by
    calc schemeHomOverComp ψ hψ (L.one t)
        = L.mul t' (L.one t') (schemeHomOverComp ψ hψ (L.one t)) := (L.one_mul t' _).symm
      _ = L.mul t' (L.mul t' (L.inv t' (schemeHomOverComp ψ hψ (L.one t))) (schemeHomOverComp ψ hψ (L.one t)))
            (schemeHomOverComp ψ hψ (L.one t)) := by rw [L.inv_mul_cancel]
      _ = L.mul t' (L.inv t' (schemeHomOverComp ψ hψ (L.one t)))
            (L.mul t' (schemeHomOverComp ψ hψ (L.one t)) (schemeHomOverComp ψ hψ (L.one t))) := by rw [L.mul_assoc]
      _ = L.mul t' (L.inv t' (schemeHomOverComp ψ hψ (L.one t))) (schemeHomOverComp ψ hψ (L.one t)) := by rw [← h]
      _ = L.one t' := L.inv_mul_cancel t' _
  exact congrArg Subtype.val this

theorem nsmulPt_eq_nsmul (L : RelativeGroupLaw R f) {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (n : ℕ)
    (P : SchemeHomOver t f) : nsmulPt L t n P = L.nsmul t n P := by
  induction n with
  | zero => rfl
  | succ n ih => rw [RelativeGroupLaw.nsmul_succ, ← ih]; rfl

theorem comp_nsmulPt (L : RelativeGroupLaw R f)
    {T T' : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (t' : T' ⟶ Spec (CommRingCat.of R)) (ψ : T' ⟶ T)
    (hψ : ψ ≫ t = t') (n : ℕ) (P : SchemeHomOver t f) :
    ψ ≫ (nsmulPt L t n P).1 = (nsmulPt L t' n (schemeHomOverComp ψ hψ P)).1 := by
  induction n with
  | zero => exact comp_one L t t' ψ hψ
  | succ n ih =>
    simp only [nsmulPt]
    have := congrArg Subtype.val (L.mul_natural t t' ψ hψ (nsmulPt L t n P) P)
    rw [schemeHomOverComp_coe] at this
    rw [this]
    congr 2
    exact Subtype.ext (by rw [schemeHomOverComp_coe, ih])

theorem nsmulPt_coe (L : RelativeGroupLaw R f) {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (n : ℕ)
    (P : SchemeHomOver t f) : (nsmulPt L t n P).1 = P.1 ≫ L.schemeNsmul n := by
  have h := comp_nsmulPt L f t P.1 P.2 n RelativeGroupLaw.idPoint
  have hid : schemeHomOverComp P.1 P.2 (RelativeGroupLaw.idPoint (f := f)) = P := Subtype.ext (by simp)
  rw [hid] at h
  rw [← h, RelativeGroupLaw.schemeNsmul, nsmulPt_eq_nsmul]

end PointAlgebra

section FEC
variable {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} {N : ℕ} {S : Type} [CommRing S] (E : FakeEllipticCurve Λ N S)

theorem pushPt_one (x : ↥Λ) {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of S)) :
    pushPt (E.act x) (E.act_over x) (E.L.one t) = E.L.one t := by
  letI := E.L.pointGroup t
  have h := E.act_hom x t (E.L.one t) (E.L.one t)
  rw [E.L.one_mul] at h
  have := congrArg (E.L.mul t (E.L.inv t (pushPt (E.act x) (E.act_over x) (E.L.one t)))) h
  rw [← E.L.mul_assoc, E.L.inv_mul_cancel, E.L.one_mul] at this
  exact this.symm

theorem pushPt_nsmulPt (x : ↥Λ) {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of S)) (n : ℕ) (P : SchemeHomOver t E.f) :
    pushPt (E.act x) (E.act_over x) (nsmulPt E.L t n P) = nsmulPt E.L t n (pushPt (E.act x) (E.act_over x) P) := by
  induction n with
  | zero => exact pushPt_one E x t
  | succ n ih => simp only [nsmulPt]; rw [E.act_hom, ih]

end FEC

section Locus
variable {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} {N : ℕ} {S : Type} [CommRing S] (E : FakeEllipticCurve Λ N S) (m : ℕ)

theorem schemeKerStr_eq : E.L.schemeKerStr m = pullback.fst (E.L.schemeNsmul m) (E.L.one (𝟙 _)).1 ≫ E.f := by
  show pullback.snd (E.L.schemeNsmul m) (E.L.one (𝟙 _)).1 = _
  have h1 : pullback.fst (E.L.schemeNsmul m) (E.L.one (𝟙 _)).1 ≫ E.f =
      pullback.fst (E.L.schemeNsmul m) (E.L.one (𝟙 _)).1 ≫ (E.L.schemeNsmul m ≫ E.f) := by rw [E.L.schemeNsmul_over]
  rw [h1, ← Category.assoc, pullback.condition, Category.assoc, (E.L.one (𝟙 _)).2, Category.comp_id]

noncomputable def Q₀ : SchemeHomOver (E.L.schemeKerStr m) E.f :=
  ⟨pullback.fst (E.L.schemeNsmul m) (E.L.one (𝟙 _)).1, (schemeKerStr_eq E m).symm⟩

@[scoped simp] theorem Q₀_coe : (Q₀ E m).1 = pullback.fst (E.L.schemeNsmul m) (E.L.one (𝟙 _)).1 := rfl

theorem coe_comp_schemeNsmul_of_nsmulPt_eq_one {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of S))
    (P : SchemeHomOver t E.f) (hP : nsmulPt E.L t m P = E.L.one t) :
    P.1 ≫ E.L.schemeNsmul m = t ≫ (E.L.one (𝟙 _)).1 := by
  rw [← nsmulPt_coe, hP]
  exact (comp_one E.L (𝟙 _) t t (Category.comp_id _)).symm

theorem Q₀_torsion : nsmulPt E.L (E.L.schemeKerStr m) m (Q₀ E m) = E.L.one (E.L.schemeKerStr m) := by
  apply Subtype.ext
  rw [nsmulPt_coe, Q₀_coe, pullback.condition]
  exact comp_one E.L (𝟙 _) _ _ (Category.comp_id _)

theorem xQ₀_torsion (x : ↥Λ) :
    nsmulPt E.L (E.L.schemeKerStr m) m (pushPt (E.act x) (E.act_over x) (Q₀ E m)) = E.L.one (E.L.schemeKerStr m) := by
  rw [← pushPt_nsmulPt, Q₀_torsion, pushPt_one]

noncomputable def sx (x : ↥Λ) : E.L.schemeKer m ⟶ E.L.schemeKer m :=
  pullback.lift (pushPt (E.act x) (E.act_over x) (Q₀ E m)).1 (E.L.schemeKerStr m)
    (coe_comp_schemeNsmul_of_nsmulPt_eq_one E m _ _ (xQ₀_torsion E m x))

noncomputable def s1 : E.L.schemeKer m ⟶ E.L.schemeKer m :=
  pullback.lift (E.L.one (E.L.schemeKerStr m)).1 (E.L.schemeKerStr m)
    (coe_comp_schemeNsmul_of_nsmulPt_eq_one E m _ _ (by
      rw [nsmulPt_eq_nsmul]; exact RelativeGroupLaw.nsmul_unit _ _ _))

theorem sx_snd (x : ↥Λ) : sx E m x ≫ E.L.schemeKerStr m = E.L.schemeKerStr m := pullback.lift_snd _ _ _
theorem s1_snd : s1 E m ≫ E.L.schemeKerStr m = E.L.schemeKerStr m := pullback.lift_snd _ _ _
theorem sx_fst (x : ↥Λ) : sx E m x ≫ pullback.fst (E.L.schemeNsmul m) (E.L.one (𝟙 _)).1 =
    (pushPt (E.act x) (E.act_over x) (Q₀ E m)).1 := pullback.lift_fst _ _ _
theorem s1_fst : s1 E m ≫ pullback.fst (E.L.schemeNsmul m) (E.L.one (𝟙 _)).1 =
    (E.L.one (E.L.schemeKerStr m)).1 := pullback.lift_fst _ _ _

theorem exists_locus (hm : IsUnit ((m : ℕ) : S)) (x : ↥Λ) :
    ∃ U : (E.L.schemeKer m).Opens, IsClosed (U : Set ↥(E.L.schemeKer m)) ∧
      ∀ {T : Scheme.{0}} (g : T ⟶ E.L.schemeKer m),
        Set.range g ⊆ (U : Set ↥(E.L.schemeKer m)) ↔
          g ≫ (pushPt (E.act x) (E.act_over x) (Q₀ E m)).1 = g ≫ (E.L.one (E.L.schemeKerStr m)).1 := by
  obtain ⟨hfin, het⟩ := CerednikDrinfeld.QM.FakeEllipticCurve.isFinite_and_etale_schemeKerStr_of_isUnit E m hm
  haveI := hfin; haveI := het
  let p : pullback (E.L.schemeKerStr m) (E.L.schemeKerStr m) ⟶ E.L.schemeKer m := pullback.fst _ _
  haveI : FormallyUnramified p := inferInstance
  haveI : LocallyOfFiniteType p := inferInstance
  haveI : IsSeparated p := inferInstance
  let σ : E.L.schemeKer m ⟶ pullback (E.L.schemeKerStr m) (E.L.schemeKerStr m) :=
    pullback.lift (𝟙 _) (sx E m x) (by rw [Category.id_comp, sx_snd])
  let τ : E.L.schemeKer m ⟶ pullback (E.L.schemeKerStr m) (E.L.schemeKerStr m) :=
    pullback.lift (𝟙 _) (s1 E m) (by rw [Category.id_comp, s1_snd])
  have hσ : σ ≫ p = 𝟙 _ := pullback.lift_fst _ _ _
  have hτ : τ ≫ p = 𝟙 _ := pullback.lift_fst _ _ _
  obtain ⟨hclopen, hpts⟩ :=
    AlgebraicGeometry.isClopen_preimage_diagonal_of_formallyUnramified_of_isSeparated p σ τ hσ hτ
  have hσ2 : σ ≫ pullback.snd _ _ = sx E m x := pullback.lift_snd _ _ _
  have hτ2 : τ ≫ pullback.snd _ _ = s1 E m := pullback.lift_snd _ _ _
  refine ⟨_, hclopen.1, fun g => ?_⟩
  rw [hpts g]
  constructor
  · intro h
    have h2 := congrArg (fun φ => φ ≫ pullback.snd _ _ ≫ pullback.fst (E.L.schemeNsmul m) (E.L.one (𝟙 _)).1) h
    simp only [Category.assoc] at h2
    rw [← Category.assoc σ, ← Category.assoc τ, hσ2, hτ2, sx_fst, s1_fst] at h2
    exact h2
  · intro h
    apply pullback.hom_ext
    · show (g ≫ σ) ≫ p = (g ≫ τ) ≫ p
      rw [Category.assoc, Category.assoc, hσ, hτ]
    · rw [Category.assoc, Category.assoc, hσ2, hτ2]
      apply pullback.hom_ext
      · rw [Category.assoc, Category.assoc, sx_fst, s1_fst]; exact h
      · rw [Category.assoc, Category.assoc, sx_snd, s1_snd]

theorem range_subset_iff {U : (E.L.schemeKer m).Opens} {x : ↥Λ}
    (hU : ∀ {T : Scheme.{0}} (g : T ⟶ E.L.schemeKer m),
        Set.range g ⊆ (U : Set ↥(E.L.schemeKer m)) ↔
          g ≫ (pushPt (E.act x) (E.act_over x) (Q₀ E m)).1 = g ≫ (E.L.one (E.L.schemeKerStr m)).1)
    {k : Type} [Field k] (sk : S →+* k) (P : SchemeHomOver (geomPoint k sk) E.f)
    (κ : Spec (CommRingCat.of k) ⟶ E.L.schemeKer m)
    (hκ : κ ≫ pullback.fst (E.L.schemeNsmul m) (E.L.one (𝟙 (Spec (CommRingCat.of S)))).1 = P.1) :
    Set.range κ ⊆ (U : Set ↥(E.L.schemeKer m)) ↔ pushPt (E.act x) (E.act_over x) P = E.L.one (geomPoint k sk) := by
  rw [hU κ]
  have hκt : κ ≫ E.L.schemeKerStr m = geomPoint k sk := by
    rw [schemeKerStr_eq, ← Category.assoc, hκ]; exact P.2
  rw [Subtype.ext_iff, pushPt, mapPt_coe, pushPt, mapPt_coe, Q₀_coe, ← Category.assoc, hκ,
    comp_one E.L _ _ κ hκt]

end Locus

end GenLocus10
p2m_reactivate "P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_ExtraLevel_exists_isClosed_range_subset_iff_forall_factorsThrough_iff.GenLocus10"

namespace GenLocus10

section Algebra
variable {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} {N : ℕ} {S : Type} [CommRing S] (E : FakeEllipticCurve Λ N S)

theorem pushPt_act_congr {x y : ↥Λ} (h : x = y) {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of S)) (P : SchemeHomOver t E.f) :
    pushPt (E.act x) (E.act_over x) P = pushPt (E.act y) (E.act_over y) P := by subst h; rfl

theorem pushPt_act_zero {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of S)) (P : SchemeHomOver t E.f) :
    pushPt (E.act 0) (E.act_over 0) P = E.L.one t := by
  have h := E.act_add 0 0 t P
  rw [pushPt_act_congr E (add_zero 0)] at h
  have := congrArg (E.L.mul t (E.L.inv t (pushPt (E.act 0) (E.act_over 0) P))) h
  rw [← E.L.mul_assoc, E.L.inv_mul_cancel, E.L.one_mul] at this
  exact this.symm

theorem pushPt_act_neg (x : ↥Λ) {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of S)) (P : SchemeHomOver t E.f) :
    pushPt (E.act (-x)) (E.act_over (-x)) P = E.L.inv t (pushPt (E.act x) (E.act_over x) P) := by
  letI := E.L.pointGroup t
  have h := E.act_add (-x) x t P
  rw [pushPt_act_congr E (neg_add_cancel x), pushPt_act_zero] at h
  exact eq_inv_of_mul_eq_one_left h.symm

theorem pushPt_act_comp (x y : ↥Λ) (h : (x : ℍ[ℚ, a, b]) * (y : ℍ[ℚ, a, b]) ∈ Λ)
    {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of S)) (P : SchemeHomOver t E.f) :
    pushPt (E.act ⟨(x : ℍ[ℚ, a, b]) * (y : ℍ[ℚ, a, b]), h⟩) (E.act_over _) P =
      pushPt (E.act x) (E.act_over x) (pushPt (E.act y) (E.act_over y) P) := by
  apply Subtype.ext
  simp only [pushPt, mapPt_coe, Category.assoc, E.act_mul x y h]

theorem natCast_mem (hΛ : IsOrder Λ) (m : ℕ) : ((m : ℚ) : ℍ[ℚ, a, b]) ∈ Λ := by
  have : ((m : ℚ) : ℍ[ℚ, a, b]) = (m : ℚ) • (1 : ℍ[ℚ, a, b]) := by
    rw [← QuaternionAlgebra.coe_mul_eq_smul, mul_one]
  rw [this, Nat.cast_smul_eq_nsmul]
  exact nsmul_mem hΛ.one_mem m

private theorem _root_.GenLocus10.smul_mem (m : ℕ) (y : ↥Λ) : (m : ℚ) • (y : ℍ[ℚ, a, b]) ∈ Λ := by
  rw [Nat.cast_smul_eq_nsmul]; exact nsmul_mem y.2 m

p2m_export "GenLocus10" "smul_mem"

theorem pushPt_torsion (x : ↥Λ) (m : ℕ) {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of S)) (P : SchemeHomOver t E.f)
    (hP : nsmulPt E.L t m P = E.L.one t) :
    nsmulPt E.L t m (pushPt (E.act x) (E.act_over x) P) = E.L.one t := by
  rw [← pushPt_nsmulPt, hP, pushPt_one]

theorem pushPt_act_smul_eq_one (hΛ : IsOrder Λ) (m : ℕ) (y : ↥Λ) (hmy : (m : ℚ) • (y : ℍ[ℚ, a, b]) ∈ Λ)
    {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of S)) (P : SchemeHomOver t E.f)
    (hP : nsmulPt E.L t m P = E.L.one t) :
    pushPt (E.act ⟨(m : ℚ) • (y : ℍ[ℚ, a, b]), hmy⟩) (E.act_over _) P = E.L.one t := by
  have hm := natCast_mem hΛ m
  have hxy : (((m : ℚ) : ℍ[ℚ, a, b]) * (y : ℍ[ℚ, a, b])) ∈ Λ := hΛ.mul_mem hm y.2
  have e : (⟨(m : ℚ) • (y : ℍ[ℚ, a, b]), hmy⟩ : ↥Λ) = ⟨((m : ℚ) : ℍ[ℚ, a, b]) * (y : ℍ[ℚ, a, b]), hxy⟩ :=
    Subtype.ext (QuaternionAlgebra.coe_mul_eq_smul _ _).symm
  rw [pushPt_act_congr E e, pushPt_act_comp E ⟨_, hm⟩ y hxy,
    CerednikDrinfeld.QM.FakeEllipticCurve.pushPt_act_natCast_eq_nsmulPt E hΛ.one_mem m hm,
    pushPt_torsion E y m t P hP]

theorem pushPt_eq_of_congr (hΛ : IsOrder Λ) (m : ℕ) {x x' : ↥Λ}
    (h : ∃ y : ↥Λ, (x : ℍ[ℚ, a, b]) - (x' : ℍ[ℚ, a, b]) = (m : ℚ) • (y : ℍ[ℚ, a, b]))
    {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of S)) (P : SchemeHomOver t E.f)
    (hP : nsmulPt E.L t m P = E.L.one t) :
    pushPt (E.act x) (E.act_over x) P = pushPt (E.act x') (E.act_over x') P := by
  obtain ⟨y, hy⟩ := h
  have e : x = x' + ⟨(m : ℚ) • (y : ℍ[ℚ, a, b]), smul_mem m y⟩ := by
    apply Subtype.ext
    simp only [Submodule.coe_add, Submodule.coe_mk, ← hy]; abel
  rw [pushPt_act_congr E e, E.act_add, pushPt_act_smul_eq_one E hΛ m y _ t P hP, E.L.mul_one]

end Algebra
p2m_reactivate "P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_ExtraLevel_exists_isClosed_range_subset_iff_forall_factorsThrough_iff.GenLocus10"

section Count
variable {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} {N : ℕ} {S : Type} [CommRing S] (E : FakeEllipticCurve Λ N S)

theorem mul_coe_congr_base {T : Scheme.{0}} {t t' : T ⟶ Spec (CommRingCat.of S)} (h : t = t')
    (P Q : SchemeHomOver t E.f) :
    (E.L.mul t P Q).1 = (E.L.mul t' ⟨P.1, h ▸ P.2⟩ ⟨Q.1, h ▸ Q.2⟩).1 := by
  subst h; rfl

theorem card_torsion_geomPoint (k : Type) [Field k] [IsAlgClosed k] (sk : S →+* k) (m : ℕ) (hm : IsUnit ((m : ℕ) : k)) :
    Finite {Q : SchemeHomOver (geomPoint k sk) E.f // nsmulPt E.L (geomPoint k sk) m Q = E.L.one (geomPoint k sk)} ∧
    Nat.card {Q : SchemeHomOver (geomPoint k sk) E.f // nsmulPt E.L (geomPoint k sk) m Q = E.L.one (geomPoint k sk)} = m ^ 4 := by
  obtain ⟨E', g, hg, hmul, -, -, -⟩ := CerednikDrinfeld.QM.FakeEllipticCurve.exists_isPullback_levelIff sk E
  have hbase : 𝟙 _ ≫ Spec.map (CommRingCat.ofHom sk) = geomPoint k sk := Category.id_comp _
  let toE : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) E'.f → SchemeHomOver (geomPoint k sk) E.f := fun P' =>
    ⟨P'.1 ≫ g, by rw [Category.assoc, hg.w, ← Category.assoc, P'.2, Category.id_comp]; rfl⟩
  have toE_coe : ∀ P', (toE P').1 = P'.1 ≫ g := fun _ => rfl
  have toE_mul : ∀ P' Q', toE (E'.L.mul _ P' Q') = E.L.mul _ (toE P') (toE Q') := by
    intro P' Q'
    apply Subtype.ext
    rw [toE_coe, hmul, mul_coe_congr_base E hbase]
  have toE_inj : Function.Injective toE := by
    intro P' Q' h
    apply Subtype.ext
    apply hg.hom_ext
    · exact congrArg Subtype.val h
    · rw [P'.2, Q'.2]
  have toE_surj : Function.Surjective toE := by
    intro Q
    refine ⟨⟨hg.lift Q.1 (𝟙 _) (by rw [Q.2, Category.id_comp]; rfl), hg.lift_snd _ _ _⟩, ?_⟩
    exact Subtype.ext (hg.lift_fst _ _ _)
  have toE_one : toE (E'.L.one _) = E.L.one _ := by
    have h := toE_mul (E'.L.one _) (E'.L.one _)
    rw [E'.L.one_mul] at h
    have := congrArg (E.L.mul _ (E.L.inv _ (toE (E'.L.one _)))) h
    rw [← E.L.mul_assoc, E.L.inv_mul_cancel, E.L.one_mul] at this
    exact this.symm
  have toE_nsmulPt : ∀ n P', toE (nsmulPt E'.L _ n P') = nsmulPt E.L _ n (toE P') := by
    intro n P'
    induction n with
    | zero => exact toE_one
    | succ n ih => simp only [nsmulPt]; rw [toE_mul, ih]
  obtain ⟨hfin, hcard⟩ := CerednikDrinfeld.QM.FakeEllipticCurve.finite_and_natCard_torsion_eq_pow_four_of_isUnit k E' m hm
  let e : {P' : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) E'.f //
        nsmulPt E'.L (𝟙 (Spec (CommRingCat.of k))) m P' = E'.L.one (𝟙 (Spec (CommRingCat.of k)))} ≃
      {Q : SchemeHomOver (geomPoint k sk) E.f // nsmulPt E.L (geomPoint k sk) m Q = E.L.one (geomPoint k sk)} :=
    (Equiv.ofBijective toE ⟨toE_inj, toE_surj⟩).subtypeEquiv (fun P' => by
      show _ ↔ nsmulPt E.L (geomPoint k sk) m (toE P') = E.L.one (geomPoint k sk)
      rw [← toE_nsmulPt, ← toE_one]
      exact ⟨fun h => by rw [h], fun h => toE_inj h⟩)
  haveI := hfin
  exact ⟨Finite.of_equiv _ e, by rw [← hcard]; exact (Nat.card_congr e).symm⟩

end Count
p2m_reactivate "P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_ExtraLevel_exists_isClosed_range_subset_iff_forall_factorsThrough_iff.GenLocus10"

end GenLocus10
p2m_reactivate "P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_ExtraLevel_exists_isClosed_range_subset_iff_forall_factorsThrough_iff.GenLocus10"

namespace GenLocus10

section Lattice
variable {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]}

theorem mem_span_smul_iff (m : ℕ) (x : ℍ[ℚ, a, b]) :
    x ∈ Submodule.span ℤ ((fun y : ℍ[ℚ, a, b] => (m : ℤ) • y) '' (Λ : Set ℍ[ℚ, a, b])) ↔
      ∃ y : ↥Λ, x = (m : ℚ) • (y : ℍ[ℚ, a, b]) := by
  have hsmul : ∀ y : ℍ[ℚ, a, b], (m : ℤ) • y = (m : ℚ) • y := fun y => by
    rw [natCast_zsmul, Nat.cast_smul_eq_nsmul]
  constructor
  · intro hx
    induction hx using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨y, hy, rfl⟩ := hx
      exact ⟨⟨y, hy⟩, hsmul y⟩
    | zero => exact ⟨0, by simp⟩
    | add x y _ _ hx hy =>
      obtain ⟨u, rfl⟩ := hx; obtain ⟨v, rfl⟩ := hy
      exact ⟨u + v, by simp [smul_add]⟩
    | smul c x _ hx =>
      obtain ⟨u, rfl⟩ := hx
      exact ⟨c • u, by rw [Submodule.coe_smul, smul_comm]⟩
  · rintro ⟨y, rfl⟩
    rw [← hsmul]
    exact Submodule.subset_span ⟨y, y.2, rfl⟩

end Lattice
p2m_reactivate "P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_ExtraLevel_exists_isClosed_range_subset_iff_forall_factorsThrough_iff.GenLocus10"

end GenLocus10
p2m_reactivate "P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_ExtraLevel_exists_isClosed_range_subset_iff_forall_factorsThrough_iff.GenLocus10"

open GenLocus10 in
/-!

                                                 -/

namespace GLUEaux

variable {R : Type u} [CommRing R]

theorem eq_one_of_mul_self {A : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of R)} (L : RelativeGroupLaw R f)
    {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (y : SchemeHomOver t f) (h : L.mul t y y = y) :
    y = L.one t := by
  have := congrArg (L.mul t (L.inv t y)) h
  rw [← L.mul_assoc, L.inv_mul_cancel, L.one_mul] at this
  exact this

theorem map_one_of_hom {A A' : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of R)} {f' : A' ⟶ Spec (CommRingCat.of R)}
    (L : RelativeGroupLaw R f) (L' : RelativeGroupLaw R f') (φ : A ⟶ A') (hφ : φ ≫ f' = f)
    (hhom : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (P Q : SchemeHomOver t f),
      mapPt φ hφ (L.mul t P Q) = L'.mul t (mapPt φ hφ P) (mapPt φ hφ Q))
    {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) :
    mapPt φ hφ (L.one t) = L'.one t := by
  apply eq_one_of_mul_self
  rw [← hhom, L.one_mul]

theorem map_nsmulPt_of_hom {A A' : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of R)} {f' : A' ⟶ Spec (CommRingCat.of R)}
    (L : RelativeGroupLaw R f) (L' : RelativeGroupLaw R f') (φ : A ⟶ A') (hφ : φ ≫ f' = f)
    (hhom : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (P Q : SchemeHomOver t f),
      mapPt φ hφ (L.mul t P Q) = L'.mul t (mapPt φ hφ P) (mapPt φ hφ Q))
    {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (n : ℕ) (P : SchemeHomOver t f) :
    mapPt φ hφ (nsmulPt L t n P) = nsmulPt L' t n (mapPt φ hφ P) := by
  induction n with
  | zero => exact map_one_of_hom L L' φ hφ hhom t
  | succ n ih => simp only [nsmulPt]; rw [hhom, ih]

theorem mapPt_mapPt {A A' A'' : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of R)} {f' : A' ⟶ Spec (CommRingCat.of R)}
    {f'' : A'' ⟶ Spec (CommRingCat.of R)} (φ : A ⟶ A') (hφ : φ ≫ f' = f) (ψ : A' ⟶ A'') (hψ : ψ ≫ f'' = f')
    {T : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of R)} (P : SchemeHomOver t f) :
    mapPt ψ hψ (mapPt φ hφ P) = mapPt (φ ≫ ψ) (by rw [Category.assoc, hψ, hφ]) P := by
  apply Subtype.ext; simp [mapPt, Category.assoc]

theorem mapPt_congr {A A' : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of R)} {f' : A' ⟶ Spec (CommRingCat.of R)}
    {φ φ' : A ⟶ A'} (h : φ = φ') (hφ : φ ≫ f' = f) (hφ' : φ' ≫ f' = f)
    {T : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of R)} (P : SchemeHomOver t f) :
    mapPt φ hφ P = mapPt φ' hφ' P := by
  subst h; rfl

theorem mapPt_injective_of_isIso {A A' : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of R)} {f' : A' ⟶ Spec (CommRingCat.of R)}
    (φ : A ⟶ A') (hφ : φ ≫ f' = f) [IsIso φ]
    {T : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of R)} {P Q : SchemeHomOver t f} (h : mapPt φ hφ P = mapPt φ hφ Q) :
    P = Q := by
  apply Subtype.ext
  have := congrArg Subtype.val h
  simp only [mapPt] at this
  exact (cancel_mono φ).1 this

end GLUEaux
p2m_reactivate "P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_ExtraLevel_exists_isClosed_range_subset_iff_forall_factorsThrough_iff.GenLocus10"

namespace GLUEact

variable {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} {N : ℕ} {S : Type u} [CommRing S]

theorem natCast_mem (hΛ : IsOrder Λ) (n : ℕ) : ((n : ℚ) : ℍ[ℚ, a, b]) ∈ Λ := by
  have : ((n : ℚ) : ℍ[ℚ, a, b]) = (n : ℤ) • (1 : ℍ[ℚ, a, b]) := by
    rw [zsmul_eq_mul, mul_one]; norm_cast
  rw [this]; exact Λ.smul_mem _ hΛ.one_mem

theorem act_zero_apply (E : FakeEllipticCurve Λ N S) (h0 : (0 : ℍ[ℚ, a, b]) ∈ Λ)
    {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of S)) (P : SchemeHomOver t E.f) :
    pushPt (E.act ⟨0, h0⟩) (E.act_over _) P = E.L.one t := by
  apply GLUEaux.eq_one_of_mul_self
  have := E.act_add ⟨0, h0⟩ ⟨0, h0⟩ t P
  have e : (⟨0, h0⟩ + ⟨0, h0⟩ : ↥Λ) = ⟨0, h0⟩ := by apply Subtype.ext; simp
  rw [e] at this
  exact this.symm

theorem act_natCast_apply (E : FakeEllipticCurve Λ N S) (hΛ : IsOrder Λ) (n : ℕ)
    {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of S)) (P : SchemeHomOver t E.f) :
    pushPt (E.act ⟨((n : ℚ) : ℍ[ℚ, a, b]), natCast_mem hΛ n⟩) (E.act_over _) P = nsmulPt E.L t n P := by
  induction n with
  | zero =>
    have e : (⟨((0 : ℕ) : ℚ), natCast_mem hΛ 0⟩ : ↥Λ) = ⟨0, by simpa using natCast_mem hΛ 0⟩ := by
      apply Subtype.ext; simp
    rw [show pushPt (E.act ⟨(((0 : ℕ) : ℚ) : ℍ[ℚ, a, b]), natCast_mem hΛ 0⟩) (E.act_over _) P =
        pushPt (E.act ⟨0, by simpa using natCast_mem hΛ 0⟩) (E.act_over _) P from by
          simp only [pushPt]; exact GLUEaux.mapPt_congr (by rw [e]) _ _ P]
    exact act_zero_apply E _ t P
  | succ n ih =>
    have e : (⟨(((n + 1 : ℕ) : ℚ) : ℍ[ℚ, a, b]), natCast_mem hΛ (n + 1)⟩ : ↥Λ) =
        ⟨((n : ℚ) : ℍ[ℚ, a, b]), natCast_mem hΛ n⟩ + ⟨1, hΛ.one_mem⟩ := by
      apply Subtype.ext; push_cast; rfl
    rw [show pushPt (E.act ⟨(((n + 1 : ℕ) : ℚ) : ℍ[ℚ, a, b]), natCast_mem hΛ (n + 1)⟩) (E.act_over _) P =
        pushPt (E.act (⟨((n : ℚ) : ℍ[ℚ, a, b]), natCast_mem hΛ n⟩ + ⟨1, hΛ.one_mem⟩)) (E.act_over _) P from by
          simp only [pushPt]; exact GLUEaux.mapPt_congr (by rw [e]) _ _ P]
    rw [E.act_add, ih]
    simp only [nsmulPt]
    congr 1
    simp only [pushPt]
    rw [GLUEaux.mapPt_congr (E.act_one hΛ.one_mem) _ (by simp) P]
    apply Subtype.ext; simp [mapPt]

end GLUEact
p2m_reactivate "P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_ExtraLevel_exists_isClosed_range_subset_iff_forall_factorsThrough_iff.GenLocus10"

namespace GLUEgrp

variable {R : Type u} [CommRing R] {A : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of R)} (L : RelativeGroupLaw R f)
  {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R))

theorem inv_inv (x : SchemeHomOver t f) : L.inv t (L.inv t x) = x := by
  calc L.inv t (L.inv t x) = L.mul t (L.inv t (L.inv t x)) (L.one t) := (L.mul_one t _).symm
    _ = L.mul t (L.inv t (L.inv t x)) (L.mul t (L.inv t x) x) := by rw [L.inv_mul_cancel]
    _ = L.mul t (L.mul t (L.inv t (L.inv t x)) (L.inv t x)) x := by rw [L.mul_assoc]
    _ = x := by rw [L.inv_mul_cancel, L.one_mul]

theorem mul_inv_cancel (x : SchemeHomOver t f) : L.mul t x (L.inv t x) = L.one t := by
  have := L.inv_mul_cancel t (L.inv t x)
  rwa [inv_inv] at this

theorem eq_of_mul_inv_eq_one {x y : SchemeHomOver t f} (h : L.mul t x (L.inv t y) = L.one t) : x = y := by
  have := congrArg (fun z => L.mul t z y) h
  rw [L.mul_assoc, L.inv_mul_cancel, L.mul_one, L.one_mul] at this
  exact this

theorem nsmulPt_add (n m : ℕ) (P : SchemeHomOver t f) :
    nsmulPt L t (n + m) P = L.mul t (nsmulPt L t n P) (nsmulPt L t m P) := by
  induction m with
  | zero => simp [nsmulPt, L.mul_one]
  | succ m ih => rw [Nat.add_succ]; simp only [nsmulPt]; rw [ih, L.mul_assoc]

theorem nsmulPt_one_pt (n : ℕ) : nsmulPt L t n (L.one t) = L.one t := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [nsmulPt]; rw [ih, L.one_mul]

theorem nsmulPt_mul (n m : ℕ) (P : SchemeHomOver t f) :
    nsmulPt L t (n * m) P = nsmulPt L t n (nsmulPt L t m P) := by
  induction n with
  | zero => simp [nsmulPt]
  | succ n ih => rw [Nat.succ_mul, nsmulPt_add, ih]; simp only [nsmulPt]

theorem nsmulPt_mod_eq_one {n m : ℕ} (P : SchemeHomOver t f)
    (hn : nsmulPt L t n P = L.one t) (hm : nsmulPt L t m P = L.one t) : nsmulPt L t (n % m) P = L.one t := by
  have e : n = n / m * m + n % m := (Nat.div_add_mod' n m).symm
  have := hn
  rw [e, nsmulPt_add, nsmulPt_mul, hm, nsmulPt_one_pt, L.one_mul] at this
  exact this

theorem eq_one_of_nsmulPt_eq_one_of_coprime {r N : ℕ} (hc : Nat.Coprime r N) (P : SchemeHomOver t f)
    (hr : nsmulPt L t r P = L.one t) (hN : nsmulPt L t N P = L.one t) : P = L.one t := by
  have key : ∀ a b : ℕ, nsmulPt L t a P = L.one t → nsmulPt L t b P = L.one t → nsmulPt L t (Nat.gcd a b) P = L.one t := by
    intro a b
    refine Nat.gcd.induction a b (fun n _ hn => by simpa using hn) (fun m n _ ih hm hn => ?_)
    rw [Nat.gcd_rec]
    exact ih (nsmulPt_mod_eq_one L t P hn hm) hm
  have := key r N hr hN
  rw [hc] at this
  simpa [nsmulPt, L.one_mul] using this

end GLUEgrp
p2m_reactivate "P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_ExtraLevel_exists_isClosed_range_subset_iff_forall_factorsThrough_iff.GenLocus10"

namespace GLUEbc

section A

variable {K : Type u} [Field K] [IsAlgClosed K]

theorem discreteTopology_of_isFinite {Z : Scheme.{u}} (g : Z ⟶ Spec (CommRingCat.of K)) [IsFinite g] :
    DiscreteTopology ↥Z := by
  have h0 : DiscreteTopology ↥(Spec (CommRingCat.of K)) := ⟨Subsingleton.elim _ _⟩
  have h1 : _root_.IsDiscrete (Set.univ : Set ↥(Spec (CommRingCat.of K))) := isDiscrete_univ_iff.mpr h0
  have h2 := g.isDiscrete_preimage h1
  rw [Set.preimage_univ] at h2
  exact isDiscrete_univ_iff.mp h2

theorem isClosed_singleton_of_isFinite {Z : Scheme.{u}} (g : Z ⟶ Spec (CommRingCat.of K)) [IsFinite g] (x : ↥Z) :
    IsClosed ({x} : Set ↥Z) := by
  haveI := discreteTopology_of_isFinite g
  exact isClosed_discrete _

theorem eq_specMap_comp_pointOfClosedPoint {Z : Scheme.{u}} (g : Z ⟶ Spec (CommRingCat.of K)) [IsFinite g]
    (k' : Type u) [Field k'] (sk : K →+* k')
    (z : Spec (CommRingCat.of k') ⟶ Z) (hz : z ≫ g = Spec.map (CommRingCat.ofHom sk)) :
    z = Spec.map (CommRingCat.ofHom sk) ≫
      pointOfClosedPoint g (z.base (IsLocalRing.closedPoint k')) (isClosed_singleton_of_isFinite g _) := by
  set x := z.base (IsLocalRing.closedPoint k') with hx
  have hxc : IsClosed ({x} : Set ↥Z) := isClosed_singleton_of_isFinite g _
  haveI : IsAffine Z := isAffine_of_isAffineHom g
  have hrange : Set.range z.base ⊆ {x} := by
    rintro _ ⟨p, rfl⟩
    rw [Set.mem_singleton_iff, Subsingleton.elim p (IsLocalRing.closedPoint k')]
  obtain ⟨t, ht⟩ :=
    AlgebraicGeometry.exists_comp_fromSpecResidueField_eq_of_range_subset_singleton z x hxc hrange
  have hfrom : Z.fromSpecResidueField x =
      Spec.map (residueFieldIsoBase g x hxc).inv ≫ pointOfClosedPoint g x hxc := by
    rw [pointOfClosedPoint, ← Category.assoc, ← Spec.map_comp, Iso.hom_inv_id, Spec.map_id, Category.id_comp]
  have ht' : t ≫ Spec.map (residueFieldIsoBase g x hxc).inv = Spec.map (CommRingCat.ofHom sk) := by
    have := hz
    rw [← ht, hfrom, Category.assoc, Category.assoc, pointOfClosedPoint_comp, Category.comp_id] at this
    exact this
  rw [← ht', Category.assoc, ← hfrom, ht]

theorem ext_of_base_eq {Z : Scheme.{u}} (g : Z ⟶ Spec (CommRingCat.of K)) [IsFinite g]
    (k' : Type u) [Field k'] (sk : K →+* k')
    {z₁ z₂ : Spec (CommRingCat.of k') ⟶ Z} (h₁ : z₁ ≫ g = Spec.map (CommRingCat.ofHom sk))
    (h₂ : z₂ ≫ g = Spec.map (CommRingCat.ofHom sk))
    (h : z₁.base (IsLocalRing.closedPoint k') = z₂.base (IsLocalRing.closedPoint k')) : z₁ = z₂ := by
  rw [eq_specMap_comp_pointOfClosedPoint g k' sk z₁ h₁, eq_specMap_comp_pointOfClosedPoint g k' sk z₂ h₂]
  congr 1
  exact congrArg (fun y => pointOfClosedPoint g y (isClosed_singleton_of_isFinite g y)) h

theorem base_specMap_comp {Z : Scheme.{u}} (k' : Type u) [Field k'] (sk : K →+* k')
    (p : Spec (CommRingCat.of K) ⟶ Z) :
    (Spec.map (CommRingCat.ofHom sk) ≫ p).base (IsLocalRing.closedPoint k') = p.base (IsLocalRing.closedPoint K) := by
  rw [Scheme.Hom.comp_base, TopCat.coe_comp, Function.comp_apply,
    Subsingleton.elim ((Spec.map (CommRingCat.ofHom sk)).base (IsLocalRing.closedPoint k')) (IsLocalRing.closedPoint K)]

theorem bijective_specMap_comp {Z : Scheme.{u}} (g : Z ⟶ Spec (CommRingCat.of K)) [IsFinite g]
    (k' : Type u) [Field k'] (sk : K →+* k') :
    Function.Bijective (fun p : {p : Spec (CommRingCat.of K) ⟶ Z // p ≫ g = 𝟙 _} =>
      (⟨Spec.map (CommRingCat.ofHom sk) ≫ p.1, by rw [Category.assoc, p.2, Category.comp_id]⟩ :
        {z : Spec (CommRingCat.of k') ⟶ Z // z ≫ g = Spec.map (CommRingCat.ofHom sk)})) := by
  constructor
  · rintro ⟨p₁, hp₁⟩ ⟨p₂, hp₂⟩ h
    have h' := congrArg (fun z : {z : Spec (CommRingCat.of k') ⟶ Z // z ≫ g = Spec.map (CommRingCat.ofHom sk)} =>
      z.1.base (IsLocalRing.closedPoint k')) h
    simp only [base_specMap_comp] at h'
    exact Subtype.ext (ext_of_apply_closedPoint_eq g hp₁ hp₂ h')
  · rintro ⟨z, hz⟩
    refine ⟨⟨pointOfClosedPoint g (z.base (IsLocalRing.closedPoint k')) (isClosed_singleton_of_isFinite g _),
      pointOfClosedPoint_comp _ _ _⟩, Subtype.ext ?_⟩
    exact (eq_specMap_comp_pointOfClosedPoint g k' sk z hz).symm

end A
p2m_reactivate "P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_ExtraLevel_exists_isClosed_range_subset_iff_forall_factorsThrough_iff.GenLocus10"

end GLUEbc
p2m_reactivate "P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_ExtraLevel_exists_isClosed_range_subset_iff_forall_factorsThrough_iff.GenLocus10"

namespace T2a5
open GenLocus10

variable {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} {N : ℕ} {S : Type} [CommRing S] (E : FakeEllipticCurve Λ N S) (n : ℕ)

theorem exists_locus₂ (hn : IsUnit ((n : ℕ) : S)) (Qa Qb : SchemeHomOver (E.L.schemeKerStr n) E.f)
    (ha : nsmulPt E.L _ n Qa = E.L.one _) (hb : nsmulPt E.L _ n Qb = E.L.one _) :
    ∃ U : (E.L.schemeKer n).Opens, IsClosed (U : Set ↥(E.L.schemeKer n)) ∧
      ∀ {T : Scheme.{0}} (g : T ⟶ E.L.schemeKer n),
        Set.range g ⊆ (U : Set ↥(E.L.schemeKer n)) ↔ g ≫ Qa.1 = g ≫ Qb.1 := by
  obtain ⟨hfin, het⟩ := CerednikDrinfeld.QM.FakeEllipticCurve.isFinite_and_etale_schemeKerStr_of_isUnit E n hn
  haveI := hfin; haveI := het
  let p : pullback (E.L.schemeKerStr n) (E.L.schemeKerStr n) ⟶ E.L.schemeKer n := pullback.fst _ _
  haveI : FormallyUnramified p := inferInstance
  haveI : LocallyOfFiniteType p := inferInstance
  haveI : IsSeparated p := inferInstance
  let sa : E.L.schemeKer n ⟶ E.L.schemeKer n :=
    pullback.lift Qa.1 (E.L.schemeKerStr n) (coe_comp_schemeNsmul_of_nsmulPt_eq_one E n _ _ ha)
  let sb : E.L.schemeKer n ⟶ E.L.schemeKer n :=
    pullback.lift Qb.1 (E.L.schemeKerStr n) (coe_comp_schemeNsmul_of_nsmulPt_eq_one E n _ _ hb)
  have sa_snd : sa ≫ E.L.schemeKerStr n = E.L.schemeKerStr n := pullback.lift_snd _ _ _
  have sb_snd : sb ≫ E.L.schemeKerStr n = E.L.schemeKerStr n := pullback.lift_snd _ _ _
  have sa_fst : sa ≫ pullback.fst (E.L.schemeNsmul n) (E.L.one (𝟙 _)).1 = Qa.1 := pullback.lift_fst _ _ _
  have sb_fst : sb ≫ pullback.fst (E.L.schemeNsmul n) (E.L.one (𝟙 _)).1 = Qb.1 := pullback.lift_fst _ _ _
  let σ : E.L.schemeKer n ⟶ pullback (E.L.schemeKerStr n) (E.L.schemeKerStr n) :=
    pullback.lift (𝟙 _) sa (by rw [Category.id_comp, sa_snd])
  let τ : E.L.schemeKer n ⟶ pullback (E.L.schemeKerStr n) (E.L.schemeKerStr n) :=
    pullback.lift (𝟙 _) sb (by rw [Category.id_comp, sb_snd])
  have hσ : σ ≫ p = 𝟙 _ := pullback.lift_fst _ _ _
  have hτ : τ ≫ p = 𝟙 _ := pullback.lift_fst _ _ _
  obtain ⟨hclopen, hpts⟩ :=
    AlgebraicGeometry.isClopen_preimage_diagonal_of_formallyUnramified_of_isSeparated p σ τ hσ hτ
  have hσ2 : σ ≫ pullback.snd _ _ = sa := pullback.lift_snd _ _ _
  have hτ2 : τ ≫ pullback.snd _ _ = sb := pullback.lift_snd _ _ _
  refine ⟨_, hclopen.1, fun g => ?_⟩
  rw [hpts g]
  constructor
  · intro h
    have h2 := congrArg (fun φ => φ ≫ pullback.snd _ _ ≫ pullback.fst (E.L.schemeNsmul n) (E.L.one (𝟙 _)).1) h
    simp only [Category.assoc] at h2
    rw [← Category.assoc σ, ← Category.assoc τ, hσ2, hτ2, sa_fst, sb_fst] at h2
    exact h2
  · intro h
    apply pullback.hom_ext
    · show (g ≫ σ) ≫ p = (g ≫ τ) ≫ p
      rw [Category.assoc, Category.assoc, hσ, hτ]
    · rw [Category.assoc, Category.assoc, hσ2, hτ2]
      apply pullback.hom_ext
      · rw [Category.assoc, Category.assoc, sa_fst, sb_fst]; exact h
      · rw [Category.assoc, Category.assoc, sa_snd, sb_snd]

end T2a5
p2m_reactivate "P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_ExtraLevel_exists_isClosed_range_subset_iff_forall_factorsThrough_iff.GenLocus10"

theorem solution
    {q q' : ℕ} [Fact q.Prime] [Fact q'.Prime] {a b : ℚ} (hB : IsIndefiniteRamifiedExactlyAt a b q q')
    (Λ : Submodule ℤ ℍ[ℚ, a, b]) (hΛ : IsMaximalOrder Λ) {N : ℕ} (m ℓ : ℕ) (hℓ : ℓ.Prime) (hℓm : ℓ ∣ m)
    (L₀ : Submodule ℤ ℍ[ℚ, a, b]) (hL₀ : L₀ ≤ Λ) (hℓL₀ : ∀ x : ↥Λ, (ℓ : ℚ) • (x : ℍ[ℚ, a, b]) ∈ L₀)
    {S : Type} [CommRing S] (hm : IsUnit ((m : ℕ) : S)) (E : FakeEllipticCurve Λ N S) (P : E.FullLevel m)
    (K : E.ExtraLevel ℓ) :
    ∃ V : (Spec (CommRingCat.of S)).Opens, IsClosed (V : Set ↥(Spec (CommRingCat.of S))) ∧
      ∀ (k : Type) [Field k] [IsAlgClosed k] (sk : S →+* k),
        Set.range (geomPoint k sk) ⊆ (V : Set ↥(Spec (CommRingCat.of S))) ↔
          ∀ Q : SchemeHomOver (geomPoint k sk) E.f,
            FactorsThrough K.levK Q ↔
              ∃ x : ↥Λ, (x : ℍ[ℚ, a, b]) ∈ L₀ ∧
                pushPt (E.act x) (E.act_over x)
                  (nsmulPt E.L (geomPoint k sk) (m / ℓ) (FakeEllipticCurve.sectionAt P.P k sk)) = Q := by

  classical
  have hO : IsOrder Λ := hΛ.isOrder
  obtain ⟨m', hm'⟩ := hℓm

  rcases Nat.eq_zero_or_pos m with hm0 | hm0
  · subst hm0
    refine ⟨⊤, by simpa using isClosed_univ, fun k _ _ sk => ?_⟩
    have h01 : (0 : S) = 1 := by simpa [isUnit_zero_iff] using hm
    have := congrArg sk h01
    simp at this
  have hℓ0 : ℓ ≠ 0 := by rintro rfl; simp at hm'; omega
  have hdiv : m / ℓ = m' := by rw [hm', Nat.mul_div_cancel_left _ (Nat.pos_of_ne_zero hℓ0)]
  have hℓu : IsUnit ((ℓ : ℕ) : S) := by
    have : ((m : ℕ) : S) = (ℓ : S) * (m' : S) := by rw [hm']; push_cast; ring
    rw [this] at hm; exact isUnit_of_mul_isUnit_left hm

  obtain ⟨hfin, het⟩ := CerednikDrinfeld.QM.FakeEllipticCurve.isFinite_and_etale_schemeKerStr_of_isUnit E ℓ hℓu
  haveI := hfin; haveI := het
  set π := E.L.schemeKerStr ℓ with hπ
  set ι := pullback.fst (E.L.schemeNsmul ℓ) (E.L.one (𝟙 (Spec (CommRingCat.of S)))).1 with hι
  have hιπ : ι ≫ E.f = π := (GenLocus10.schemeKerStr_eq E ℓ).symm

  haveI := K.levK_closed; haveI := K.levK_flat; haveI := K.levK_finitePresentation
  obtain ⟨U, eU, hUcl, -, hUpts⟩ := GoodReductionJacobian.RelativeGroupLaw.exists_opens_schemeKer_iso_of_isClosedImmersion_of_nsmulPt_eq_one
    E.L ℓ K.levK (fun t P hP => K.levK_torsion t P hP)

  let R₀ : SchemeHomOver (𝟙 (Spec (CommRingCat.of S))) E.f := nsmulPt E.L _ (m / ℓ) P.P
  have hR₀ℓ : nsmulPt E.L _ ℓ R₀ = E.L.one _ := by
    show nsmulPt E.L _ ℓ (nsmulPt E.L _ (m / ℓ) P.P) = _
    rw [hdiv, ← GLUEgrp.nsmulPt_mul]
    have : ℓ * m' = m := hm'.symm
    rw [this]; exact P.torsion

  let bcT : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of S)),
      SchemeHomOver (𝟙 (Spec (CommRingCat.of S))) E.f → SchemeHomOver t E.f :=
    fun t R => schemeHomOverComp t (Category.comp_id _) R
  have bcT_val : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of S)) (R), (bcT t R).1 = t ≫ R.1 := fun t R => rfl
  have bcT_one : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of S)), bcT t (E.L.one _) = E.L.one t :=
    fun t => E.L.one_natural _ _ t (Category.comp_id _)
  have bcT_nsmul : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of S)) (n : ℕ) (R), bcT t (nsmulPt E.L _ n R) = nsmulPt E.L t n (bcT t R) := by
    intro T t n R
    induction n with
    | zero => exact bcT_one t
    | succ n ih => show schemeHomOverComp _ _ (E.L.mul _ _ _) = _; rw [E.L.mul_natural]; simp only [nsmulPt]; rw [← ih]
  have bcT_act : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of S)) (x : ↥Λ) (R),
      bcT t (pushPt (E.act x) (E.act_over x) R) = pushPt (E.act x) (E.act_over x) (bcT t R) := by
    intro T t x R; apply Subtype.ext; simp [bcT, schemeHomOverComp, pushPt, mapPt, Category.assoc]

  let Rx : ↥Λ → SchemeHomOver (𝟙 (Spec (CommRingCat.of S))) E.f := fun x => pushPt (E.act x) (E.act_over x) R₀
  have hRxℓ : ∀ x, nsmulPt E.L _ ℓ (Rx x) = E.L.one _ := by
    intro x; show nsmulPt E.L _ ℓ (pushPt (E.act x) (E.act_over x) R₀) = _
    rw [← GenLocus10.pushPt_nsmulPt, hR₀ℓ, GenLocus10.pushPt_one]
  have hπRxℓ : ∀ x, nsmulPt E.L π ℓ (bcT π (Rx x)) = E.L.one π := by
    intro x; rw [← bcT_nsmul, hRxℓ, bcT_one]
  have hWex := fun x : ↥Λ => T2a5.exists_locus₂ E ℓ hℓu (GenLocus10.Q₀ E ℓ) (bcT π (Rx x)) (GenLocus10.Q₀_torsion E ℓ) (hπRxℓ x)
  choose Wx hWxcl hWxpts using hWex

  let ℓΛ : Submodule ℤ ℍ[ℚ, a, b] := Submodule.span ℤ ((fun y : ℍ[ℚ, a, b] => (ℓ : ℤ) • y) '' (Λ : Set ℍ[ℚ, a, b]))
  let H : AddSubgroup ↥Λ.toAddSubgroup := ℓΛ.toAddSubgroup.addSubgroupOf Λ.toAddSubgroup
  have hHidx : H.index = ℓ ^ 4 := QuaternionAlgebra.IsOrder.relIndex_span_smul_eq_pow_four hO ℓ (Nat.pos_of_ne_zero hℓ0)
  haveI : Fintype (↥Λ.toAddSubgroup ⧸ H) := AddSubgroup.fintypeOfIndexNeZero (by rw [hHidx]; positivity)
  have memH : ∀ h : ↥Λ.toAddSubgroup, h ∈ H ↔ ∃ y : ↥Λ, (h : ℍ[ℚ, a, b]) = (ℓ : ℚ) • (y : ℍ[ℚ, a, b]) := by
    intro h
    rw [AddSubgroup.mem_addSubgroupOf, Submodule.mem_toAddSubgroup]
    exact GenLocus10.mem_span_smul_iff ℓ _
  let rep : ↥Λ.toAddSubgroup ⧸ H → ↥Λ := fun q => ⟨(Quotient.out q : ↥Λ.toAddSubgroup).1, (Quotient.out q).2⟩
  have hrep : ∀ x : ↥Λ, ∃ y : ↥Λ, ((rep (QuotientAddGroup.mk ⟨x.1, x.2⟩) : ↥Λ) : ℍ[ℚ, a, b]) - (x : ℍ[ℚ, a, b]) =
      (ℓ : ℚ) • (y : ℍ[ℚ, a, b]) := by
    intro x
    obtain ⟨h, hh⟩ := QuotientAddGroup.mk_out_eq_mul H (⟨x.1, x.2⟩ : ↥Λ.toAddSubgroup)
    obtain ⟨y, hy⟩ := (memH h).1 h.2
    refine ⟨y, ?_⟩
    have : ((rep (QuotientAddGroup.mk ⟨x.1, x.2⟩) : ↥Λ) : ℍ[ℚ, a, b]) = (x : ℍ[ℚ, a, b]) + (h : ↥Λ.toAddSubgroup) := by
      show ((Quotient.out (QuotientAddGroup.mk (⟨x.1, x.2⟩ : ↥Λ.toAddSubgroup)) : ↥Λ.toAddSubgroup) : ℍ[ℚ, a, b]) = _
      rw [hh]; rfl
    rw [this, ← hy]; abel
  let Rset : Finset ↥Λ := (Finset.univ.image rep).filter (fun r => (r : ℍ[ℚ, a, b]) ∈ L₀)

  let A := E.L.schemeKer ℓ
  let Wset : Set ↥A := ⋃ x ∈ Rset, (Wx x : Set ↥A)
  have hWop : IsOpen Wset := isOpen_biUnion (fun x _ => (Wx x).2)
  have hWcl : IsClosed Wset := Set.Finite.isClosed_biUnion (Finset.finite_toSet Rset) (fun x _ => hWxcl x)
  let Dset : Set ↥A := ((U : Set ↥A) ∩ Wsetᶜ) ∪ (Wset ∩ (U : Set ↥A)ᶜ)
  have hDop : IsOpen Dset := ((U.2).inter (isOpen_compl_iff.2 hWcl)).union (hWop.inter (isOpen_compl_iff.2 hUcl))
  have hDcl : IsClosed Dset := (hUcl.inter (isClosed_compl_iff.2 hWop)).union (hWcl.inter (isClosed_compl_iff.2 U.2))
  have hπcl : IsClosedMap π.base := π.isClosedMap
  have hπop : IsOpenMap π.base := π.isOpenMap
  let V : (Spec (CommRingCat.of S)).Opens := ⟨(π.base '' Dset)ᶜ, isOpen_compl_iff.2 (hπcl _ hDcl)⟩
  refine ⟨V, isClosed_compl_iff.2 (hπop _ hDop), fun k _ _ sk => ?_⟩

  let s₀ : ↥(Spec (CommRingCat.of S)) := (geomPoint k sk).base (IsLocalRing.closedPoint k)
  have hpt : ∀ p : ↥(Spec (CommRingCat.of k)), p = IsLocalRing.closedPoint k := fun p => Subsingleton.elim _ _
  have hrange : ∀ {Y : Scheme.{0}} (g : Spec (CommRingCat.of k) ⟶ Y) (Z : Set ↥Y),
      Set.range g.base ⊆ Z ↔ g.base (IsLocalRing.closedPoint k) ∈ Z := by
    intro Y g Z
    constructor
    · intro h; exact h ⟨_, rfl⟩
    · rintro h _ ⟨p, rfl⟩; rw [hpt p]; exact h

  have hlift : ∀ y : ↥A, π.base y = s₀ → ∃ κ : Spec (CommRingCat.of k) ⟶ A, κ ≫ π = geomPoint k sk ∧ κ.base (IsLocalRing.closedPoint k) = y := by
    intro y hy
    obtain ⟨z, hz1, hz2⟩ := Scheme.Pullback.exists_preimage_pullback (f := π) (g := geomPoint k sk) y (IsLocalRing.closedPoint k) hy
    haveI : IsFinite (pullback.snd π (geomPoint k sk)) := inferInstance
    haveI : LocallyOfFiniteType (pullback.snd π (geomPoint k sk)) := inferInstance
    have hzcl : IsClosed ({z} : Set ↥(pullback π (geomPoint k sk))) := GLUEbc.isClosed_singleton_of_isFinite (pullback.snd π (geomPoint k sk)) z
    obtain ⟨-, hsec, -⟩ := AlgebraicGeometry.eq_of_base_closedPoint_eq_and_exists_base_closedPoint_eq_and_isClosed_of_isAlgClosed k
      (pullback.snd π (geomPoint k sk))
    obtain ⟨zs, hzs1, hzs2⟩ := hsec z hzcl
    refine ⟨zs ≫ pullback.fst π (geomPoint k sk), ?_, ?_⟩
    · rw [Category.assoc, pullback.condition, ← Category.assoc, hzs1, Category.id_comp]
    · show (pullback.fst π (geomPoint k sk)).base (zs.base _) = y; rw [hzs2, hz1]

  have Qof_prop : ∀ (κ : Spec (CommRingCat.of k) ⟶ A), κ ≫ π = geomPoint k sk → (κ ≫ ι) ≫ E.f = geomPoint k sk := by
    intro κ hκ; rw [Category.assoc, hιπ, hκ]

  have memU : ∀ (κ : Spec (CommRingCat.of k) ⟶ A) (hκ : κ ≫ π = geomPoint k sk),
      κ.base (IsLocalRing.closedPoint k) ∈ (U : Set ↥A) ↔ FactorsThrough K.levK (⟨κ ≫ ι, Qof_prop κ hκ⟩ : SchemeHomOver (geomPoint k sk) E.f) := by
    intro κ hκ
    rw [hUpts, ← hrange]
    constructor
    · intro h; exact ⟨κ, rfl, h⟩
    · rintro ⟨κ', hκ'1, hκ'2⟩
      have : κ' = κ := by
        apply pullback.hom_ext
        · exact hκ'1
        · show κ' ≫ π = κ ≫ π
          rw [← hιπ, ← Category.assoc, hκ'1, Category.assoc]
      rw [← this]; exact hκ'2

  have hsecRx : ∀ x : ↥Λ, bcT (geomPoint k sk) (Rx x) =
      pushPt (E.act x) (E.act_over x) (nsmulPt E.L (geomPoint k sk) (m / ℓ) (FakeEllipticCurve.sectionAt P.P k sk)) := by
    intro x
    show bcT (geomPoint k sk) (pushPt (E.act x) (E.act_over x) (nsmulPt E.L _ (m / ℓ) P.P)) = _
    rw [bcT_act, bcT_nsmul]; rfl
  have memWx : ∀ (x : ↥Λ) (κ : Spec (CommRingCat.of k) ⟶ A) (hκ : κ ≫ π = geomPoint k sk),
      κ.base (IsLocalRing.closedPoint k) ∈ (Wx x : Set ↥A) ↔
        (⟨κ ≫ ι, Qof_prop κ hκ⟩ : SchemeHomOver (geomPoint k sk) E.f) =
          pushPt (E.act x) (E.act_over x) (nsmulPt E.L (geomPoint k sk) (m / ℓ) (FakeEllipticCurve.sectionAt P.P k sk)) := by
    intro x κ hκ
    rw [← hrange, hWxpts x κ, ← hsecRx, Subtype.ext_iff]
    show κ ≫ (GenLocus10.Q₀ E ℓ).1 = κ ≫ π ≫ (Rx x).1 ↔ κ ≫ ι = geomPoint k sk ≫ (Rx x).1
    rw [← hκ, Category.assoc]
    exact Iff.rfl

  have hcongr : ∀ (x x' : ↥Λ), (∃ y : ↥Λ, (x : ℍ[ℚ, a, b]) - (x' : ℍ[ℚ, a, b]) = (ℓ : ℚ) • (y : ℍ[ℚ, a, b])) →
      pushPt (E.act x) (E.act_over x) (nsmulPt E.L (geomPoint k sk) (m / ℓ) (FakeEllipticCurve.sectionAt P.P k sk)) =
      pushPt (E.act x') (E.act_over x') (nsmulPt E.L (geomPoint k sk) (m / ℓ) (FakeEllipticCurve.sectionAt P.P k sk)) := by
    intro x x' h
    apply GenLocus10.pushPt_eq_of_congr E hO ℓ h
    have : nsmulPt E.L (geomPoint k sk) (m / ℓ) (FakeEllipticCurve.sectionAt P.P k sk) = bcT (geomPoint k sk) R₀ := by
      rw [show R₀ = nsmulPt E.L _ (m / ℓ) P.P from rfl, bcT_nsmul]; rfl
    rw [this, ← bcT_nsmul, hR₀ℓ, bcT_one]

  have memW : ∀ (κ : Spec (CommRingCat.of k) ⟶ A) (hκ : κ ≫ π = geomPoint k sk),
      κ.base (IsLocalRing.closedPoint k) ∈ Wset ↔
        ∃ x : ↥Λ, (x : ℍ[ℚ, a, b]) ∈ L₀ ∧
          pushPt (E.act x) (E.act_over x) (nsmulPt E.L (geomPoint k sk) (m / ℓ) (FakeEllipticCurve.sectionAt P.P k sk)) =
            ⟨κ ≫ ι, Qof_prop κ hκ⟩ := by
    intro κ hκ
    simp only [Wset, Set.mem_iUnion, exists_prop]
    constructor
    · rintro ⟨r, hr, hmem⟩
      obtain ⟨-, hrL⟩ := Finset.mem_filter.1 hr
      exact ⟨r, hrL, ((memWx r κ hκ).1 hmem).symm⟩
    · rintro ⟨x, hxL, hx⟩
      obtain ⟨y, hy⟩ := hrep x
      refine ⟨rep (QuotientAddGroup.mk ⟨x.1, x.2⟩), Finset.mem_filter.2 ⟨Finset.mem_image.2 ⟨_, Finset.mem_univ _, rfl⟩, ?_⟩, ?_⟩
      · have : ((rep (QuotientAddGroup.mk ⟨x.1, x.2⟩) : ↥Λ) : ℍ[ℚ, a, b]) = (x : ℍ[ℚ, a, b]) + (ℓ : ℚ) • (y : ℍ[ℚ, a, b]) := by
          rw [← hy]; abel
        rw [this]; exact L₀.add_mem hxL (hℓL₀ y)
      · rw [memWx _ κ hκ, ← hx]; exact (hcongr _ _ ⟨y, hy⟩).symm

  have hκof : ∀ (Q : SchemeHomOver (geomPoint k sk) E.f), nsmulPt E.L _ ℓ Q = E.L.one _ →
      ∃ κ : Spec (CommRingCat.of k) ⟶ A, ∃ hκ : κ ≫ π = geomPoint k sk, (⟨κ ≫ ι, Qof_prop κ hκ⟩ : SchemeHomOver (geomPoint k sk) E.f) = Q := by
    intro Q hQ
    refine ⟨pullback.lift Q.1 (geomPoint k sk) (GenLocus10.coe_comp_schemeNsmul_of_nsmulPt_eq_one E ℓ _ _ hQ), pullback.lift_snd _ _ _, ?_⟩
    apply Subtype.ext; exact pullback.lift_fst _ _ _
  have htorsL : ∀ (x : ↥Λ), nsmulPt E.L (geomPoint k sk) ℓ
      (pushPt (E.act x) (E.act_over x) (nsmulPt E.L (geomPoint k sk) (m / ℓ) (FakeEllipticCurve.sectionAt P.P k sk))) = E.L.one _ := by
    intro x; rw [← hsecRx, ← bcT_nsmul, hRxℓ, bcT_one]

  have hV : Set.range (geomPoint k sk).base ⊆ (V : Set ↥(Spec (CommRingCat.of S))) ↔
      ∀ y : ↥A, π.base y = s₀ → (y ∈ (U : Set ↥A) ↔ y ∈ Wset) := by
    rw [hrange]
    show s₀ ∈ (π.base '' Dset)ᶜ ↔ _
    rw [Set.mem_compl_iff, Set.mem_image, not_exists]
    constructor
    · intro h y hy
      have hyD : y ∉ Dset := fun hD => h y ⟨hD, hy⟩
      simp only [Dset, Set.mem_union, Set.mem_inter_iff, Set.mem_compl_iff, not_or, not_and, not_not] at hyD
      tauto
    · rintro h y ⟨hD, hy⟩
      have := h y hy
      simp only [Dset, Set.mem_union, Set.mem_inter_iff, Set.mem_compl_iff] at hD
      tauto
  rw [hV]
  constructor
  · intro h Q
    constructor
    · intro hQ
      obtain ⟨κ, hκ, rfl⟩ := hκof Q (K.levK_torsion _ Q hQ)
      have hy := (h _ (by show (κ ≫ π).base _ = s₀; rw [hκ])).1 ((memU κ hκ).2 hQ)
      exact (memW κ hκ).1 hy
    · rintro ⟨x, hxL, hx⟩
      obtain ⟨κ, hκ, hκQ⟩ := hκof Q (by rw [← hx]; exact htorsL x)
      rw [← hκQ]
      exact (memU κ hκ).1 ((h _ (by show (κ ≫ π).base _ = s₀; rw [hκ])).2 ((memW κ hκ).2 ⟨x, hxL, by rw [hκQ]; exact hx⟩))
  · intro h y hy
    obtain ⟨κ, hκ, rfl⟩ := hlift y hy
    rw [memU κ hκ, memW κ hκ, h]

end S_CerednikDrinfeld_QM_FakeEllipticCurve_ExtraLevel_exists_isClosed_range_subset_iff_forall_factorsThrough_iff
end P2MW
export P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_ExtraLevel_exists_isClosed_range_subset_iff_forall_factorsThrough_iff (solution)
