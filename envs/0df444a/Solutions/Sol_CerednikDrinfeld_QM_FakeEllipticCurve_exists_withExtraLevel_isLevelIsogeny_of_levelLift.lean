-- Prove2me | solution 1 for CerednikDrinfeld.QM.FakeEllipticCurve.exists_withExtraLevel_isLevelIsogeny_of_levelLift
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.141142+00:00
-- url     : https://prove2.me/submissions/4d371e43-5699-5646-ac06-0303579e8276

import Definitions.Def_CerednikDrinfeld_QMModuliProps
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawKernel
import Definitions.Def_AlgebraicGeometry_NeronModelEndomorphismExtension
import Definitions.Def_AlgebraicGeometry_RelativeGroupLawEndDegree
import Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_exists_quotient_core_of_isAlgClosed
import Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_exists_image_closedSubgroup_of_isFinite
import Theorems.Thm_CerednikDrinfeld_QM_isReduced_of_mapPt_mapPt_eq_nsmulPt_of_natCast_ne_zero
import Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_isReduced_pullback_one_of_natCast_ne_zero
import Theorems.Thm_CerednikDrinfeld_QM_exists_comp_eq_of_forall_factorsThrough_of_isReduced
import Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_smoothOfRelativeDimension_two
import Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_etale_schemeNsmul_of_isUnit_of_smoothOfRelativeDimension
import Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_exists_relativeGroupLaw_comp_eq_mul_and_forall_exists_comp_eq_of_isClosedImmersion
import Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_exists_extraLevel_of_isClosedImmersion_of_equiv_points
import Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_isFinite_endKerStr_and_natCard_eq_endDegree_of_etale
import Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_endDegree_nsmul_idPoint_eq_pow
import Theorems.Thm_AddCommGroup_nonempty_zmod_prod_addEquiv_torsionBy_of_card_torsionBy_eq_sq
import Theorems.Thm_AlgebraicGeometry_exists_comp_fromSpecResidueField_eq_of_range_subset_singleton
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_exists_withExtraLevel_isLevelIsogeny_of_levelLift
p2m_attr_erase "instance" "AlgebraicGeometry.Scheme.PresheafOfModules.symmetricCategory SheafOfModules.instFaithfulRingSheafPModToPMod SheafOfModules.symmetricCategory AlgebraicGeometry.Scheme.PresheafOfModules.monoidalCategory AlgebraicGeometry.Scheme.PresheafOfModules.monoidalClosed SheafOfModules.instFullRingSheafPModToPMod SheafOfModules.monoidalCategory AlgebraicGeometry.Scheme.Modules.symmetricCategory SheafOfModules.monoidalClosed SheafOfModules.instIsLocalizationPModRingSheafSheafifyFunctorPresheafW SheafOfModules.sheafifyFunctor_monoidal AlgebraicGeometry.Scheme.Modules.monoidalClosed AlgebraicGeometry.instMonoidalPresheafOfModulesModulesSheafify AlgebraicGeometry.Scheme.Modules.monoidalCategory PresheafOfModules.instMonoidalClosed PresheafOfModules.InternalHom.instModuleCarrierObjOppositeCommRingCatSubtypePiFamilyMemAddSubgroupNaturalFamilies PresheafOfModules.InternalHom.instModuleCarrierObjOppositeRingCatCompCommRingCatForget₂RingHomCarrierCarrierAbPresheaf PresheafOfModules.InternalHom.instSMulCarrierObjOppositeCommRingCatSubtypePiFamilyMemAddSubgroupNaturalFamilies AlgebraicGeometry.Scheme.Hom.opensMapFinal AlgebraicGeometry.RelPicard.RigidifiedLineBundle.setoid AlgebraicGeometry.RelPicard.RigidifiedLineBundle.instInhabited AlgebraicGeometry.OModulePresheaf.isScalarTower AlgebraicGeometry.Scheme.OrderedAffineCover.instLinearOrder AlgebraicGeometry.OModulePresheaf.module AlgebraicGeometry.Scheme.OrderedAffineCover.instFintype AlgebraicGeometry.Scheme.OrderedAffineCover.instFintypeIdx AlgebraicGeometry.OModulePresheaf.addCommGroup AlgebraicGeometry.Scheme.OrderedAffineCover.instDecidableEqIdx AlgebraicGeometry.OModulePresheaf.moduleSections TwoChartCech.Sections.M0_moduleA TwoChartCech.Sections.M1_module TwoChartCech.Cover.A01_algebra TwoChartCech.Cover.A0_algebra TwoChartCech.Cover.A1_commRing TwoChartCech.Cover.A1_algebra TwoChartCech.Sections.M01_module TwoChartCech.Sections.M0_addCommGroup TwoChartCech.Sections.M0_tower TwoChartCech.Sections.M01_addCommGroup TwoChartCech.Cover.A0_commRing"
p2m_attr_erase "instance" "TwoChartCech.Sections.M1_tower TwoChartCech.Sections.M01_moduleA TwoChartCech.Sections.M0_module TwoChartCech.Sections.M1_moduleA TwoChartCech.Sections.M1_addCommGroup TwoChartCech.Cover.A01_commRing TwoChartCech.Sections.M01_tower CoherentBaseChange.TwoTermComplex.C0_module CoherentBaseChange.TwoTermComplex.C0_addCommGroup CoherentBaseChange.TwoTermComplex.C1_module CoherentBaseChange.TwoTermComplex.C1_addCommGroup CoherentBaseChange.TwoTermComplex.C0_free CoherentBaseChange.TwoTermComplex.C1_finite CoherentBaseChange.TwoTermComplex.C0_finite CoherentBaseChange.TwoTermComplex.C1_free AlgebraicGeometry.OModulePresheaf.instSubsingletonObjZero AlgebraicGeometry.Scheme.Modules.preservesBinaryProducts_opensMap AlgebraicGeometry.Scheme.Modules.pullback_monoidal AlgebraicGeometry.Scheme.Modules.sheafify_isLocalization' AlgebraicGeometry.Scheme.Modules.preservesTerminal_opensMap AlgebraicGeometry.Scheme.Modules.pullback₀_monoidal AlgebraicGeometry.Scheme.Modules.preservesFiniteProducts_opensMap AlgebraicGeometry.Scheme.Modules.instLiftingPresheafOfModulesSheafifyPresheafWOpensCarrierCarrierCommRingCatGrothendieckTopologyObjFunctorOppositeIsSheafSheafCompPullback₀Pullback PresheafOfModules.PullbackMonoidal.pullback_monoidal PresheafOfModules.PullbackMonoidal.isIso_δ PresheafOfModules.pushforward_laxMonoidal PresheafOfModules.PullbackMonoidal.isIso_η PresheafOfModules.free_monoidal PresheafOfModules.restrictScalars_laxMonoidal PresheafOfModules.PullbackMonoidal.isIso_δ_gS PresheafOfModules.pullback_oplaxMonoidal PresheafOfModules.PullbackMonoidal.instPreservesColimitsOfSizeCompOppositeCommRingCatRingCatForget₂RingHomCarrierCarrierPb PresheafOfModules.pullback_monoidal' AlgebraicGeometry.SmoothOfRelativeDimension.fiberToSpecResidueField AlgebraicGeometry.SmoothOfRelativeDimension.pullback_snd AlgebraicGeometry.SmoothOfRelativeDimension.pullback_fst AlgebraicGeometry.SmoothOfRelativeDimension.smooth_one AlgebraicGeometry.SmoothProperCurve.isIntegral_pullback_Spec_field AlgebraicGeometry.IsProper.fiberToSpecResidueField AlgebraicCurve.CurveModel.isProper"
p2m_attr_erase "instance" "AlgebraicCurve.CurveModel.isIntegral AlgebraicCurve.CurveModel.smooth AlgebraicGeometry.Scheme.LocalRepresentabilityULift.instIsLocallyInjectiveFunUliftYonedaGluedToSheaf AlgebraicGeometry.Scheme.LocalRepresentabilityULift.instIsLocallySurjectiveFunUliftYonedaGluedToSheafOfIsLocallySurjectiveZariskiTopologyDescFunctorOppositeType AlgebraicGeometry.Scheme.LocalRepresentabilityULift.instIsOpenImmersionToGlued AlgebraicGeometry.Scheme.LocalRepresentabilityULift.instIsIsoSheafZariskiTopologyTypeUliftYonedaGluedToSheaf AlgebraicGeometry.RelPicard.instIsOpenImmersionToGlued AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.instFundamentalIdentityOfSumRamificationInertia AlgebraicCurve.Place.instIsScalarTowerResidueFieldRestrictPushforward AlgebraicCurve.Place.instAlgebraResidueFieldRestrictPushforward AlgebraicCurve.Place.instIsLocalHomRestrictInclusion AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions PresheafOfModules.ExteriorPower.instModulePresheafAb AlgebraicGeometry.RelEffCartierDiv.subsingleton_of_degree_zero AlgebraicGeometry.RelEffCartierDiv.isIso_subschemeIota_snd_of_degree_one AlgebraicGeometry.isIso_ker_graphOver_subschemeIota_snd AlgebraicGeometry.isClosedImmersion_graphOver AlgebraicGeometry.FGSubalgebra.instIsDirectedLe AlgebraicGeometry.FGSubalgebra.instQuasiSeparatedSpaceCarrierCarrierCommRingCatObjOppositeSchemeSpecDiagram AlgebraicGeometry.FGSubalgebra.instIsCofilteredOpposite AlgebraicGeometry.FGSubalgebra.instIsAffineObjOppositeSchemeSpecDiagram AlgebraicGeometry.FGSubalgebra.instNonempty AlgebraicGeometry.FGSubalgebra.instNonemptySubtypeLeSubalgebraValFG AlgebraicGeometry.FGSubalgebra.instCompactSpaceCarrierCarrierCommRingCatObjOppositeSchemeSpecDiagram AlgebraicGeometry.FGSubalgebra.instIsDirectedSubtypeLeSubalgebraValFG AlgebraicGeometry.FGSubalgebra.instIsAffineHomMapOppositeSchemeSpecDiagram AlgebraicGeometry.FGSubalgebra.instIsFiltered AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instNeg AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instSMulInt AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instAddCommGroup AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instAdd AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instSub AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instModuleCarrierObjOppositeOpensCarrierCarrierCommRingCatPresheafOpOpensTop"
p2m_attr_erase "instance" "AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instSMulCarrierObjOppositeOpensCarrierCarrierCommRingCatPresheafOpOpensTop AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instSMulNat AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instZero AlgebraicCurve.instHasLocalResidue_of_hasCanonicalLocalResidueK AlgebraicCurve.instHasCanonicalLocalResidueK_of_hasCanonicalLocalResidueKStar AlgebraicCurve.Place.kw_ffgc_finiteDimensional_adicCompletion instAlgebraSubtypeMemValuationSubring_definitions AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersIntegersCompletion ModularCurve.KwF4gRRTate.instAlgebraKAdicCompletionIntegers AlgebraicCurve.Place.kw_ffgc_continuousSMul_adicCompletionComap AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersCompletionCompletion IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions AlgebraicCurve.instHasCanonicalLocalResidueK AlgebraicCurve.Place.instAlgebra_restrictResidueField AlgebraicCurve.Place.instIsScalarTower_restrictResidueField AlgebraicCurve.instHasLocalResidue AlgebraicCurve.HasSeparableResidue.of_perfectField_of_isCurveOver AlgebraicCurve.HasSeparableResidue.of_perfectField AlgebraicCurve.Place.instIsLocalHom_restrictSubringHom AlgebraicCurve.instHasCanonicalLocalResidueKStar ModularCurve.KwNo6Pin.isLocalRing_completion SheafOfModules.isIso_ihomModelToIhom AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instDecidableEqIdx AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instFintype AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instLinearOrder AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instFintypeIdx AlgebraicGeometry.OModulePresheaf.Leray.relAltC_scalarTower AlgebraicGeometry.OModulePresheaf.Leray.ker_relAltd_modΓ AlgebraicGeometry.OModulePresheaf.Leray.relAltC_modΓ AlgebraicGeometry.OModulePresheaf.Leray.biC_abGrp AlgebraicGeometry.OModulePresheaf.Leray.relAltH_modΓ AlgebraicGeometry.OModulePresheaf.Leray.ker_relAltd_smul AlgebraicGeometry.OModulePresheaf.Leray.relAltH_scalarTower AlgebraicGeometry.OModulePresheaf.Leray.relAltH_smul AlgebraicGeometry.OModulePresheaf.Leray.biC_module"
p2m_attr_erase "instance" "DoubleComplex.instModuleE₂I DoubleComplex.Bounded.modR DoubleComplex.instModuleE₂II DoubleComplex.instAddCommGroupE₂II DoubleComplex.Bounded.abGrp DoubleComplex.instAddCommGroupE₂I AlgebraicGeometry.ChowDatum.hι_closed AlgebraicGeometry.ChowDatumProj.hιN_closed AlgebraicGeometry.ChowDatumProj.hp_proper AlgebraicGeometry.ChowDatum.hp_isoU AlgebraicGeometry.ChowDatum.hp_proper AlgebraicGeometry.ProjSpace.algebraAway AlgebraicGeometry.ProjSpace.instIsProperProdOverπ AlgebraicGeometry.ChowDatumProj.hp_isoU AlgebraicGeometry.ProjSpace.isProper_π AlgebraicGeometry.ProjSpace.finiteType_mvPolynomial ProjSpaceCech.GradedModule.H.module ProjSpaceCech.GradedModule.H.addCommGroup ProjSpaceCech.GradedModule.sec.instAdd ProjSpaceCech.GradedModule.sec.instNeg ProjSpaceCech.GradedModule.acg ProjSpaceCech.GradedModule.Frac.setoid ProjSpaceCech.GradedModule.modR ProjSpaceCech.GradedModule.sec.instModule ProjSpaceCech.GradedModule.sec.instAddCommGroup ProjSpaceCech.GradedModule.sec.instZero ProjSpaceCech.GradedModule.Presentation.fJ ProjSpaceCech.GradedModule.sec.instSMul ProjSpaceCech.Twist.H.module ProjSpaceCech.Idx.instFintype ProjSpaceCech.Twist.H.addCommGroup ProjSpaceCech.Idx.instDecidableEq ProjSpaceCech.Twist.Mon.instDecidableEq ProjSpaceCech.Twist.cochain.instAddCommGroup ProjSpaceCech.Twist.cochain.instModule AlgebraicGeometry.FGSubalgebra.tensorStage_directedSystem AlgebraicGeometry.RelEffCartierDiv.isClosedImmersion_subschemeι_resProdMap AlgebraicGeometry.RelEffCartierDiv.isOpenImmersion_resProdMap AlgebraicCurve.CurveModel.locallyOfFiniteType_gluedToBase AlgebraicCurve.CurveModel.isFractionRing_overlap"
p2m_attr_erase "instance" "AlgebraicCurve.CurveModel.isLocallyNoetherian_glued AlgebraicCurve.CurveModel.jacobsonSpace_glued AlgebraicCurve.CurveModel.isOpenImmersion_ι₀ AlgebraicCurve.CurveModel.isIntegral_glued AlgebraicCurve.CurveModel.quasiSeparated_gluedToBase AlgebraicCurve.CurveModel.compactSpace_glued AlgebraicCurve.CurveModel.isIntegral_adjoin_chartRing AlgebraicCurve.CurveModel.isFractionRing_overlap_functionField AlgebraicCurve.CurveModel.isProper_gluedToBase AlgebraicCurve.CurveModel.isOpenImmersion_ιU AlgebraicCurve.CurveModel.isOpenImmersion_f₀ AlgebraicCurve.CurveModel.isOpenImmersion_fInf AlgebraicCurve.CurveModel.isOpenImmersion_ιInf AlgebraicCurve.CurveModel.algebra_overlap_functionField AlgebraicCurve.CurveModel.quasiCompact_gluedToBase AlgebraicCurve.CurveModel.algebraAdjoin AlgebraicCurve.CurveModel.isDedekindDomain_chartRing AlgebraicCurve.CurveModel.isIntegralClosure AlgebraicCurve.CurveModel.finite_chartRing AlgebraicCurve.CurveModel.centre_isPrime AlgebraicCurve.CurveModel.isFractionRing_chartRing AlgebraicCurve.CurveModel.finiteType_chartRing AlgebraicCurve.CurveModel.isNoetherianRing_chartRing AlgebraicCurve.CurveModel.isScalarTower_base_adjoin AlgebraicCurve.CurveModel.isScalarTower_adjoin AlgebraicCurve.CurveModel.chartRing_finitePresentation instTopologicallyFGOfFiniteType AlgebraicGeometry.ProjSpace.twistObj.addCommGroup AlgebraicGeometry.ProjSpace.twistFam.module AlgebraicGeometry.ProjSpace.twistObj.module AlgebraicGeometry.ProjSpace.twistObj.moduleSections AlgebraicGeometry.ProjSpace.twistFam.addCommGroup"
p2m_attr_erase "simp" "GoodReductionJacobian.RelativeGroupLaw.actionSndPoint_coe GoodReductionJacobian.RelativeGroupLaw.actionFstPoint_coe GoodReductionJacobian.RelativeGroupLaw.fibre_inv GoodReductionJacobian.RelativeGroupLaw.fibrePointToBase_coe GoodReductionJacobian.RelativeGroupLaw.fibrePointOfBase_toBase GoodReductionJacobian.RelativeGroupLaw.fibre_mul GoodReductionJacobian.RelativeGroupLaw.fibrePointToBase_ofBase GoodReductionJacobian.RelativeGroupLaw.fibre_one GoodReductionJacobian.RelativeGroupLaw.fibrePointOfBase_coe GoodReductionJacobian.relativeGroupLawOfGrpObj_inv GoodReductionJacobian.relativeGroupLawOfGrpObj_mul GoodReductionJacobian.overHomEquivSchemeHomOver_apply_coe GoodReductionJacobian.relativeGroupLawOfGrpObj_one GoodReductionJacobian.overHomEquivSchemeHomOver_symm_apply_left RegularLocalRingQuotientAscent.dualNumberFst_apply GoodReductionJacobian.RelativeGroupLaw.baseChangePointToBase_ofBase GoodReductionJacobian.RelativeGroupLaw.baseChangePointToBase_coe GoodReductionJacobian.RelativeGroupLaw.baseChangePointOfBase_coe GoodReductionJacobian.RelativeGroupLaw.baseChange_inv GoodReductionJacobian.RelativeGroupLaw.baseChangePointOfBase_toBase GoodReductionJacobian.RelativeGroupLaw.baseChange_mul GoodReductionJacobian.RelativeGroupLaw.baseChange_one NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_fst NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_snd NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_fst NeronSpecialFibreInfra.neronEndRestrictEquiv_apply NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_fst_assoc NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_snd NeronSpecialFibreInfra.neronEndExtension_genericFibreRestrict NeronSpecialFibreInfra.specClosedFibreInclusion_eq NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_fst_assoc NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_snd_assoc NeronSpecialFibreInfra.genericFibreRestrict_neronEndExtension NeronSpecialFibreInfra.homOverId_coe NeronSpecialFibreInfra.homOverComp_coe NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_snd_assoc SheafOfModules.tensorUnit_eq AlgebraicGeometry.Scheme.Modules.tensorUnit_eq PresheafOfModules.InternalHom.presheaf_map_apply PresheafOfModules.InternalHom.curryFamily_app"
p2m_attr_erase "simp" "PresheafOfModules.InternalHom.add_app PresheafOfModules.InternalHom.smul_app PresheafOfModules.InternalHom.zero_app PresheafOfModules.ihomObj_map_val PresheafOfModules.ihomFunctor_map PresheafOfModules.InternalHom.restrict_app PresheafOfModules.InternalHom.postcomp_app PresheafOfModules.InternalHom.neg_app PresheafOfModules.curry'_app_val PresheafOfModules.InternalHom.presheaf_obj PresheafOfModules.ihomFunctor_obj PresheafOfModules.ihomObj_obj PresheafOfModules.InternalHom.sub_app PresheafOfModules.ihomMap_app_val AlgebraicGeometry.Scheme.Modules.tensorPow_zero AlgebraicGeometry.Scheme.Modules.tensorPow_succ AlgebraicGeometry.RelPicard.RigidifiedLineBundle.mk.sizeOf_spec AlgebraicGeometry.RelPicard.RigidifiedLineBundle.mk.injEq AlgebraicGeometry.Scheme.OrderedAffineCover.mk.injEq AlgebraicGeometry.OModulePresheaf.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCover.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.mk.injEq AlgebraicGeometry.Scheme.TwoAffineOpenCover.mk.injEq AlgebraicGeometry.Scheme.TwoAffineOpenCover.mk.sizeOf_spec AlgebraicGeometry.Scheme.TwoAffineOpenCover.pullback_U1 AlgebraicGeometry.Scheme.TwoAffineOpenCover.pullback_U0 TwoChartCech.Sections.mk.injEq TwoChartCech.Cover.mk.injEq TwoChartCech.GrothendieckComplex.mk.injEq TwoChartCech.Sections.mk.sizeOf_spec TwoChartCech.Cover.mk.sizeOf_spec TwoChartCech.Cover.lineBundle_r0_apply TwoChartCech.GrothendieckComplex.mk.sizeOf_spec TwoChartCech.Cover.lineBundle_r1_apply CoherentBaseChange.TwoTermComplex.mk.sizeOf_spec CoherentBaseChange.TwoTermComplex.mk.injEq AlgebraicGeometry.OModulePresheaf.prod_obj AlgebraicGeometry.OModulePresheaf.restrOpen_obj AlgebraicGeometry.OModulePresheaf.DevissageStep.mk.injEq AlgebraicGeometry.OModulePresheaf.pushforward_obj"
p2m_attr_erase "simp" "AlgebraicGeometry.OModulePresheaf.im_obj AlgebraicGeometry.OModulePresheaf.pow_obj AlgebraicGeometry.OModulePresheaf.fstHom_app AlgebraicGeometry.OModulePresheaf.ker_obj AlgebraicGeometry.OModulePresheaf.coker_obj AlgebraicGeometry.OModulePresheaf.DevissageStep.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCover.preimage_U AlgebraicGeometry.OModulePresheaf.sndHom_app AlgebraicGeometry.OModulePresheaf.Hom.mk.injEq AlgebraicGeometry.OModulePresheaf.Hom.id_app AlgebraicGeometry.OModulePresheaf.AffHom.appSections_apply AlgebraicGeometry.OModulePresheaf.AffHom.comp_app AlgebraicGeometry.OModulePresheaf.AffSES.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.AffHom.kerMap_coe AlgebraicGeometry.OModulePresheaf.AffHom.id_app AlgebraicGeometry.OModulePresheaf.Hom.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.Hom.toAffHom_app AlgebraicGeometry.OModulePresheaf.SES.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.AffHom.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.Hom.comp_app AlgebraicGeometry.OModulePresheaf.SES.mk.injEq AlgebraicGeometry.OModulePresheaf.AffHom.mk.injEq AlgebraicGeometry.OModulePresheaf.Hom.appSections_apply AlgebraicGeometry.OModulePresheaf.AffSES.mk.injEq PresheafOfModules.freeεIso_hom_app PresheafOfModules.freeμIso_hom_app AlgebraicGeometry.RelPicard.RepresentsRelSubPic.mk.injEq AlgebraicGeometry.RelPicard.SubPicCondition.mk.injEq AlgebraicGeometry.RelPicard.SubPicCondition.mk.sizeOf_spec AlgebraicGeometry.RelPicard.RepresentsRelSubPic.mk.sizeOf_spec AlgebraicGeometry.SmoothProperCurve.sectionBaseChange_coe_snd AlgebraicGeometry.SmoothProperCurve.sectionBaseChange_coe_fst AlgebraicCurve.CurveModel.mk.injEq AlgebraicCurve.CurveModel.mk.sizeOf_spec AlgebraicCurve.mulAdele_apply AlgebraicCurve.residuePairing_apply_coe AlgebraicCurve.mem_adeleBdd AlgebraicCurve.weilSmul_one AlgebraicCurve.diagonalHom_apply AlgebraicCurve.weilSmul_apply"
p2m_attr_erase "simp" "AlgebraicCurve.adeleSpaceMul_coe AlgebraicCurve.mulAdele_one AlgebraicGeometry.SmoothProperCurve.FiniteMapData.twoAffineOpenCover_U1 AlgebraicGeometry.SmoothProperCurve.FiniteMapData.mk.injEq AlgebraicGeometry.SmoothProperCurve.FiniteMapData.mk.sizeOf_spec AlgebraicGeometry.SmoothProperCurve.FiniteMapData.twoAffineOpenCover_U0 AlgebraicGeometry.RelPicard.SubPicCondition.onClasses_mk AlgebraicGeometry.RelPicard.relSubPicPresheaf_map_coe CategoryTheory.Functor.OverTotal.ofFibre_fst CategoryTheory.Functor.overTotal_map_fst AlgebraicGeometry.Scheme.LocalRepresentabilityULift.glueData_J AlgebraicGeometry.Scheme.LocalRepresentabilityULift.uliftYoneda_toGlued_uliftYonedaGluedToSheaf AlgebraicGeometry.Scheme.LocalRepresentabilityULift.glueData_t' AlgebraicGeometry.Scheme.LocalRepresentabilityULift.uliftYoneda_toGlued_uliftYonedaGluedToSheaf_assoc AlgebraicGeometry.Scheme.LocalRepresentabilityULift.uliftYonedaGluedToSheaf_app_toGlued AlgebraicGeometry.Scheme.LocalRepresentabilityULift.glueData_openCover_map AlgebraicGeometry.Scheme.LocalRepresentabilityULift.uliftYonedaGluedToSheaf_app_comp AlgebraicGeometry.Scheme.LocalRepresentabilityULift.glueData_V AlgebraicGeometry.Scheme.LocalRepresentabilityULift.glueData_t AlgebraicGeometry.Scheme.LocalRepresentabilityULift.glueData_U AlgebraicGeometry.Scheme.LocalRepresentabilityULift.glueData_f AlgebraicGeometry.RelPicard.designationOfRepresentableBy_P AlgebraicGeometry.RelPicard.designationOfRepresentableBy_toBase AlgebraicGeometry.RelPicard.rigSection_snd AlgebraicGeometry.RelPicard.RigidifiedLineBundle.ofInvertible_L AlgebraicGeometry.RelPicard.rigSection_snd_assoc AlgebraicGeometry.RelPicard.SubPicGroupCondition.mk.injEq AlgebraicGeometry.RelPicard.SubPicGroupCondition.mk.sizeOf_spec AlgebraicCurve.coe_cechH0Equiv_apply AlgebraicCurve.cechH1ToH1_mk AlgebraicCurve.lSpaceOn_univ AlgebraicCurve.lSpaceOn_empty AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.Divisor.mapRestrict_single AlgebraicCurve.Divisor.pushforward_single"
p2m_attr_erase "simp" "AlgebraicCurve.Place.coe_restrictInclusion AlgebraicCurve.Place.mem_fiber AlgebraicCurve.Place.restrict_toValuationSubring AlgebraicCurve.Divisor.degree_pushforward AlgebraicCurve.Place.restrictResidueMap_residue AlgebraicCurve.Pic0.coe_pushforwardDegZeroHom AlgebraicCurve.Pic0.coe_pullbackDegZeroHom AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Divisor.degree_pushforwardAlong AlgebraicCurve.Pic0.coe_degZeroCorrespondence AlgebraicCurve.Place.mem_fiberAlong AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.jqNModC_one ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one"
p2m_attr_erase "simp" "AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one AlgebraicCurve.Place.differentialCoeff_zero AlgebraicCurve.Place.differentialCoeff_dCoord AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.injEq AlgebraicCurve.TranscendenceTower.mk.injEq AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec AlgebraicCurve.PoleDivisorPackage.mk.injEq AlgebraicGeometry.RelPicard.thetaBundle_def AlgebraicGeometry.RelPicard.picardBundle_def AlgebraicGeometry.RelEffCartierDiv.toRelEffDivisor_ofRelEffDivisor AlgebraicGeometry.RelEffCartierDiv.toRelEffDivisor_I AlgebraicGeometry.mapOnProdOver_fst_assoc AlgebraicGeometry.RelEffCartierDiv.mk.sizeOf_spec AlgebraicGeometry.RelEffCartierDiv.mk.injEq AlgebraicGeometry.mapOnProdOver_snd AlgebraicGeometry.mapOnProdOver_fst AlgebraicGeometry.mapOnProdOver_snd_assoc AlgebraicGeometry.mapOnProdOver_id AlgebraicCurve.RelEffDivisor.mk.sizeOf_spec AlgebraicCurve.mapOnProd_fst AlgebraicCurve.mapOnProd_fst_assoc AlgebraicCurve.mapOnProd_snd AlgebraicCurve.UnivDivisorPack.mk.injEq AlgebraicCurve.RelEffDivisor.mk.injEq AlgebraicCurve.UnivDivisorPack.mk.sizeOf_spec AlgebraicCurve.mapOnProd_snd_assoc AlgebraicGeometry.Scheme.Modules.exteriorPower_obj PresheafOfModules.exteriorPower_map_ιMulti PresheafOfModules.ExteriorPower.appₗ_apply AlgebraicGeometry.prodKerGraph_one AlgebraicGeometry.fibrePowOver.proj_comp AlgebraicGeometry.prodKerGraph_zero"
p2m_attr_erase "simp" "AlgebraicGeometry.RelEffCartierDiv.empty_I AlgebraicGeometry.fibrePowOver.proj_comp_assoc AlgebraicGeometry.graphOver_fst_assoc AlgebraicGeometry.RelEffCartierDiv.toPoint_comp AlgebraicGeometry.RelEffCartierDiv.toPoint_comp_assoc AlgebraicGeometry.graphOver_fst AlgebraicGeometry.RelEffCartierDiv.ofPoint_I AlgebraicGeometry.graphOver_snd AlgebraicGeometry.graphOver_snd_assoc AlgebraicCurve.SymmetricPowerPackage.mk.sizeOf_spec AlgebraicCurve.SymmetricPowerPackage.mk.injEq AlgebraicGeometry.FGSubalgebra.cocone_ι_app_apply AlgebraicGeometry.RelPicard.fst_toProdSpec AlgebraicGeometry.RelPicard.toProdSpec_fst_assoc AlgebraicGeometry.RelPicard.pointsSubBasepointModule_cons AlgebraicGeometry.RelPicard.pointsSubBasepointModule_nil AlgebraicGeometry.RelPicard.fst_toProdSpec_assoc AlgebraicGeometry.RelPicard.toProdSpec_fst AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.sub_app AlgebraicGeometry.Scheme.IdealSheafData.sres_sresTop AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.add_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.mk.sizeOf_spec AlgebraicGeometry.Scheme.IdealSheafData.coe_resLE AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.smul_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.coe_ofLE_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.ideal_range AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.zero_app AlgebraicGeometry.Scheme.IdealSheafData.sres_sres AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.comp_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.neg_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.id_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.coe_mulRight_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.nsmul_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.mk.injEq AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.zsmul_app AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.sizeOf_spec AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.injEq AlgebraicCurve.adeleSingle_coe AlgebraicCurve.kaehlerResidueTermKFam_apply AlgebraicCurve.Place.LocalResidueData.mk.injEq"
p2m_attr_erase "simp" "AlgebraicCurve.Place.LocalResidueData.mk.sizeOf_spec AlgebraicCurve.Place.kw_ffgc_adicCompletionComapIntegers_coe AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.sizeOf_spec AlgebraicCurve.Place.mem_simplePoleSubmodule AlgebraicCurve.Place.coe_uniformizerSubring ModularCurve.Lg37.Lg37CompletionSection.mk.injEq AlgebraicCurve.Place.CoefficientFieldSection.mk.injEq AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.injEq ModularCurve.Lg37.Lg37CompletionSection.mk.sizeOf_spec AlgebraicCurve.Place.CoefficientFieldSection.mk.sizeOf_spec AlgebraicCurve.Place.poleSubmodule_one AlgebraicCurve.Place.mem_poleSubmodule AlgebraicGeometry.Scheme.Modules.toUnitSection_ofUnitSection AlgebraicGeometry.Scheme.Modules.pullbackSection_def AlgebraicGeometry.Scheme.Modules.ofUnitSection_toUnitSection PresheafOfModules.InternalHom.IsSheafAux.appAt_toPresheafHom SheafOfModules.ihomSectionsEquivFamily_unit AlgebraicGeometry.Scheme.Modules.restrictHomEquivFamily_apply SheafOfModules.ihomEval_unit_app AlgebraicGeometry.Scheme.Modules.ihomEval_zero_right AlgebraicGeometry.Scheme.Modules.ihomEval_zero_left AlgebraicGeometry.Scheme.Modules.homOfFamily_app_apply SheafOfModules.unit_ihomSectionsEquivFamily AlgebraicGeometry.Scheme.Modules.familyOfHom_app AlgebraicGeometry.Scheme.Modules.restrictUnitIso_hom_app_apply AlgebraicGeometry.Scheme.Modules.restrictUnitIso_inv_app_apply AlgebraicGeometry.Scheme.Modules.restrictHomOfFamily_app_apply AlgebraicGeometry.Scheme.Modules.restrictHomEquivFamily_symm_apply AlgebraicGeometry.Scheme.Modules.tensorSections_zero_right AlgebraicGeometry.Scheme.Modules.map_unitSection AlgebraicGeometry.Scheme.Modules.tensorSectionsBilin_apply AlgebraicGeometry.Scheme.Modules.tensorPowSection_zero AlgebraicGeometry.Scheme.Modules.tensorSections_zero_left AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_neg AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_zero AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_sub AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_add AlgebraicGeometry.Scheme.OrderedAffineCover.toCoverOf_U AlgebraicGeometry.Scheme.OrderedAffineCoverOf.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCoverOf.mk.injEq"
p2m_attr_erase "simp" "AlgebraicGeometry.Scheme.OrderedAffineCover.restrict_U AlgebraicGeometry.OModulePresheaf.Leray.restrictToPreimage_U DoubleComplex.Bounded.mk.injEq DoubleComplex.Bounded.mk.sizeOf_spec DoubleComplex.Convergence.mk.injEq DoubleComplex.Convergence.mk.sizeOf_spec DoubleComplex.SubQuot.mk.sizeOf_spec DoubleComplex.SubQuot.mk.injEq AlgebraicGeometry.ChowDatumProj.mk.sizeOf_spec AlgebraicGeometry.ChowDatum.mk.sizeOf_spec AlgebraicGeometry.ChowDatumProj.mk.injEq AlgebraicGeometry.ChowDatum.mk.injEq ProjSpaceCech.GradedModule.mk.injEq ProjSpaceCech.GradedModule.mk.sizeOf_spec ProjSpaceCech.GradedModule.Frac.mk.sizeOf_spec ProjSpaceCech.GradedModule.Presentation.mk.injEq ProjSpaceCech.GradedModule.Frac.mk.injEq ProjSpaceCech.GradedModule.Presentation.mk.sizeOf_spec ProjSpaceCech.GradedModule.Hom.shift_toLinearMap ProjSpaceCech.GradedModule.Hom.mk.sizeOf_spec ProjSpaceCech.GradedModule.Hom.mk.injEq TwoChartCech.Mumford.dK_apply TwoChartCech.Mumford.ι0_apply TwoChartCech.Mumford.ι1_apply TwoChartCech.KerCoprod.dK_apply TwoChartCech.KerCoprod.ι1_apply TwoChartCech.KerCoprod.ι0_apply AlgebraicGeometry.tilde.functorCompPullbackSpecIso_app AlgebraicGeometry.RelPicard.algEquivZeroGroupCut_toSubPicCondition AlgebraicGeometry.RelPicard.LFP.stageHom_val AlgebraicGeometry.RelPicard.BaseChange.relSubPicPresheafRestrictIso_hom_app_coe AlgebraicGeometry.RelPicard.BaseChange.relSubPicPresheafRestrictIso_inv_app_coe AlgebraicGeometry.RelPicard.BaseChange.restrict_P AlgebraicGeometry.RelEffCartierDiv.IsUniversal.lift_comp AlgebraicGeometry.RelEffCartierDiv.functor_map_fst AlgebraicGeometry.RelEffCartierDiv.IsUniversal.homEquiv_apply AlgebraicGeometry.RelEffCartierDiv.IsUniversal.lift_pullbackAlong AlgebraicGeometry.RelEffCartierDiv.IsUniversal.homEquiv_symm_apply AlgebraicGeometry.RelEffCartierDiv.IsUniversal.lift_comp_assoc AlgebraicGeometry.RelEffCartierDiv.supportedIn_top"
p2m_attr_erase "simp" "AlgebraicGeometry.RelEffCartierDiv.mem_supportedIn_iff AlgebraicGeometry.RelEffCartierDiv.supportedIn_top_eq AlgebraicGeometry.RelEffCartierDiv.restrictAlong_extendAlong AlgebraicGeometry.RelEffCartierDiv.extendAlong_I AlgebraicGeometry.RelEffCartierDiv.resProdMap_snd AlgebraicGeometry.RelEffCartierDiv.restrictAlong_I AlgebraicGeometry.RelEffCartierDiv.extendAlong_restrictAlong AlgebraicGeometry.RelEffCartierDiv.resProdMap_fst_assoc AlgebraicGeometry.RelEffCartierDiv.resProdMap_snd_assoc AlgebraicGeometry.RelEffCartierDiv.resProdMap_fst CoherentBaseChange.FibreH0Family.mk.sizeOf_spec CoherentBaseChange.FibreH0Family.mk.injEq AlgebraicGeometry.Scheme.Modules.ProjPresentation.mk.injEq AlgebraicGeometry.Scheme.Modules.ProjPresentation.mk.sizeOf_spec AlgebraicCurve.CurveModel.coe_gInf AlgebraicCurve.CurveModel.coe_tInvChart AlgebraicCurve.CurveModel.ιInf_gluedToBase_assoc AlgebraicCurve.CurveModel.ιInf_gluedToBase AlgebraicCurve.CurveModel.primeOfι₀_asIdeal AlgebraicCurve.CurveModel.coe_tChart AlgebraicCurve.CurveModel.ι₀_gluedToBase_assoc AlgebraicCurve.CurveModel.primeOfιInf_asIdeal AlgebraicCurve.CurveModel.ι₀_gluedToBase AlgebraicCurve.CurveModel.coe_tma AlgebraicCurve.CurveModel.coe_primeEquivChartPlaces AlgebraicGeometry.ProjSpace.twistObj.mk.injEq AlgebraicGeometry.ProjSpace.twistObj.zero_val AlgebraicGeometry.ProjSpace.twistObj.add_val AlgebraicGeometry.ProjSpace.twist_res_val AlgebraicGeometry.ProjSpace.twist_smul_val AlgebraicGeometry.ProjSpace.twistGradeToObj_val AlgebraicGeometry.ProjSpace.twistObj.smul_val AlgebraicGeometry.ProjSpace.twistGradeEquiv_apply_val AlgebraicGeometry.ProjSpace.twistObj.mk.sizeOf_spec"

set_option autoImplicit false

open scoped TensorProduct Quaternion NumberField
open CategoryTheory AlgebraicGeometry QuaternionAlgebra CerednikDrinfeld CerednikDrinfeld.QM NeronModelInfra

section QLBookWrap
universe u
open CategoryTheory AlgebraicGeometry NeronModelInfra GoodReductionJacobian CerednikDrinfeld.QM

namespace QLBook21

section Kit

variable {R : Type u} [CommRing R]
variable {A₀ A : Scheme.{u}} {f₀ : A₀ ⟶ Spec (CommRingCat.of R)} {f : A ⟶ Spec (CommRingCat.of R)}

theorem nsmulPt_zero (L : RelativeGroupLaw R f) {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R))
    (P : SchemeHomOver t f) : nsmulPt L t 0 P = L.one t := rfl

theorem nsmulPt_succ (L : RelativeGroupLaw R f) {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R))
    (n : ℕ) (P : SchemeHomOver t f) : nsmulPt L t (n + 1) P = L.mul t (nsmulPt L t n P) P := rfl

private theorem _root_.QLBook21.mapPt_one (L₀ : RelativeGroupLaw R f₀) (L : RelativeGroupLaw R f) (φ : A₀ ⟶ A) (hφ : φ ≫ f = f₀)
    (hφ_hom : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (P Q : SchemeHomOver t f₀),
      mapPt φ hφ (L₀.mul t P Q) = L.mul t (mapPt φ hφ P) (mapPt φ hφ Q))
    {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) :
    mapPt φ hφ (L₀.one t) = L.one t := by
  have h := hφ_hom t (L₀.one t) (L₀.one t)
  rw [L₀.one_mul] at h
  letI := L.pointGroup t
  have h' : (mapPt φ hφ (L₀.one t)) * (mapPt φ hφ (L₀.one t)) = (mapPt φ hφ (L₀.one t)) * 1 := by
    rw [mul_one]; exact h.symm
  exact mul_left_cancel h'

p2m_export "QLBook21" "mapPt_one"

private theorem _root_.QLBook21.mapPt_nsmulPt (L₀ : RelativeGroupLaw R f₀) (L : RelativeGroupLaw R f) (φ : A₀ ⟶ A) (hφ : φ ≫ f = f₀)
    (hφ_hom : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (P Q : SchemeHomOver t f₀),
      mapPt φ hφ (L₀.mul t P Q) = L.mul t (mapPt φ hφ P) (mapPt φ hφ Q))
    {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (n : ℕ) (P : SchemeHomOver t f₀) :
    mapPt φ hφ (nsmulPt L₀ t n P) = nsmulPt L t n (mapPt φ hφ P) := by
  induction n with
  | zero => exact mapPt_one L₀ L φ hφ hφ_hom t
  | succ n ih => rw [nsmulPt_succ, nsmulPt_succ, hφ_hom, ih]

p2m_export "QLBook21" "mapPt_nsmulPt"
theorem nsmulPt_one (L : RelativeGroupLaw R f) {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (n : ℕ) :
    nsmulPt L t n (L.one t) = L.one t := by
  induction n with
  | zero => rfl
  | succ n ih => rw [nsmulPt_succ, ih, L.mul_one]

theorem nsmulPt_add (L : RelativeGroupLaw R f) {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R))
    (m n : ℕ) (P : SchemeHomOver t f) :
    nsmulPt L t (m + n) P = L.mul t (nsmulPt L t m P) (nsmulPt L t n P) := by
  induction n with
  | zero => rw [Nat.add_zero, nsmulPt_zero, L.mul_one]
  | succ n ih => rw [Nat.add_succ, nsmulPt_succ, nsmulPt_succ, ih, L.mul_assoc]

private theorem _root_.QLBook21.nsmulPt_mul (L : RelativeGroupLaw R f) {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R))
    (m n : ℕ) (P : SchemeHomOver t f) :
    nsmulPt L t (m * n) P = nsmulPt L t n (nsmulPt L t m P) := by
  induction n with
  | zero => rw [Nat.mul_zero, nsmulPt_zero, nsmulPt_zero]
  | succ n ih => rw [Nat.mul_succ, nsmulPt_add, ih, nsmulPt_succ]

p2m_export "QLBook21" "nsmulPt_mul"

theorem pred_nsmulPt (L : RelativeGroupLaw R f) {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R))
    (S : SchemeHomOver t f → Prop) (hone : S (L.one t)) (hmul : ∀ P Q, S P → S Q → S (L.mul t P Q))
    (n : ℕ) (P : SchemeHomOver t f) (hP : S P) : S (nsmulPt L t n P) := by
  induction n with
  | zero => exact hone
  | succ n ih => exact hmul _ _ ih hP

def castPt {B T : Scheme.{u}} {s s' : T ⟶ B} (h : s = s') {X : Scheme.{u}} {g : X ⟶ B}
    (P : SchemeHomOver s g) : SchemeHomOver s' g := ⟨P.1, h ▸ P.2⟩

@[scoped simp] theorem castPt_coe {B T : Scheme.{u}} {s s' : T ⟶ B} (h : s = s') {X : Scheme.{u}} {g : X ⟶ B}
    (P : SchemeHomOver s g) : (castPt h P).1 = P.1 := rfl

theorem geomPoint_id (k : Type u) [Field k] :
    geomPoint k (RingHom.id k) = 𝟙 (Spec (CommRingCat.of k)) := by
  show Spec.map (CommRingCat.ofHom (RingHom.id k)) = 𝟙 _
  rw [CommRingCat.ofHom_id]; exact Spec.map_id _

end Kit

section Transverse

variable {k : Type} [Field k]
variable {A₀ A : Scheme.{0}} {f₀ : A₀ ⟶ Spec (CommRingCat.of k)} {f : A ⟶ Spec (CommRingCat.of k)}
variable (L₀ : RelativeGroupLaw k f₀) (L : RelativeGroupLaw k f)
variable (p : A₀ ⟶ A) (hp : p ≫ f = f₀)
variable {Ct : Scheme.{0}} (levt : Ct ⟶ A₀) {K₀ : Scheme.{0}} (levK : K₀ ⟶ A₀)

theorem nsmulPt_mapPt_eq_one_of_levelLift
    (hp_hom : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of k)) (P Q : SchemeHomOver t f₀),
      mapPt p hp (L₀.mul t P Q) = L.mul t (mapPt p hp P) (mapPt p hp Q))
    (N ℓ : ℕ)
    (hCt_one : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of k)), FactorsThrough levt (L₀.one t))
    (hCt_sub : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of k)) (P Q : SchemeHomOver t f₀),
        FactorsThrough levt P → FactorsThrough levt Q →
          FactorsThrough levt (L₀.mul t P Q) ∧ FactorsThrough levt (L₀.inv t P))
    (hCt_torsion : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of k)) (P : SchemeHomOver t f₀),
        FactorsThrough levt P → nsmulPt L₀ t (N * ℓ) P = L₀.one t)
    (hK_points : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of k)) (P : SchemeHomOver t f₀),
        FactorsThrough levK P ↔ (FactorsThrough levt P ∧ nsmulPt L₀ t ℓ P = L₀.one t))
    (p_ker : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of k)) (P : SchemeHomOver t f₀),
        mapPt p hp P = L.one t ↔ FactorsThrough levK P)
    {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of k)) (P : SchemeHomOver t f₀) (hP : FactorsThrough levt P) :
    nsmulPt L t N (mapPt p hp P) = L.one t := by
  rw [← mapPt_nsmulPt L₀ L p hp hp_hom, p_ker, hK_points]
  refine ⟨pred_nsmulPt L₀ t (FactorsThrough levt) (hCt_one t) (fun P Q hP hQ => (hCt_sub t P Q hP hQ).1) N P hP, ?_⟩
  rw [← nsmulPt_mul, hCt_torsion t P hP]

theorem mapPt_eq_one_of_levelLift_of_mapPt_mapPt_eq_one
    (ψ : A ⟶ A₀) (hψ : ψ ≫ f₀ = f) (ℓ : ℕ)
    (hψp : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of k)) (P : SchemeHomOver t f₀),
        mapPt ψ hψ (mapPt p hp P) = nsmulPt L₀ t ℓ P)
    (hK_points : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of k)) (P : SchemeHomOver t f₀),
        FactorsThrough levK P ↔ (FactorsThrough levt P ∧ nsmulPt L₀ t ℓ P = L₀.one t))
    (p_ker : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of k)) (P : SchemeHomOver t f₀),
        mapPt p hp P = L.one t ↔ FactorsThrough levK P)
    {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of k)) (P : SchemeHomOver t f₀) (hP : FactorsThrough levt P)
    (hker : mapPt ψ hψ (mapPt p hp P) = L₀.one t) :
    mapPt p hp P = L.one t := by
  rw [p_ker, hK_points]
  exact ⟨hP, by rw [← hψp, hker]⟩

theorem factorsThrough_lev₀_mapPt_of_image [IsAlgClosed k]
    (ψ : A ⟶ A₀) (hψ : ψ ≫ f₀ = f) (ℓ : ℕ)
    (hψp : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of k)) (P : SchemeHomOver t f₀),
        mapPt ψ hψ (mapPt p hp P) = nsmulPt L₀ t ℓ P)
    {C₀ : Scheme.{0}} (lev₀ : C₀ ⟶ A₀) [IsClosedImmersion lev₀]
    (hCt_lev : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of k)) (P : SchemeHomOver t f₀),
        FactorsThrough levt P → FactorsThrough lev₀ (nsmulPt L₀ t ℓ P))
    {C : Scheme.{0}} (lev : C ⟶ A) [IsReduced C] [LocallyOfFiniteType (lev ≫ f)]
    (lev_pts : ∀ (k' : Type) [Field k'] [IsAlgClosed k'] (sk : k →+* k') (Q : SchemeHomOver (geomPoint k' sk) f),
        FactorsThrough lev Q ↔ ∃ P : SchemeHomOver (geomPoint k' sk) f₀, FactorsThrough levt P ∧ mapPt p hp P = Q)
    {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of k)) (Q : SchemeHomOver t f) (hQ : FactorsThrough lev Q) :
    FactorsThrough lev₀ (mapPt ψ hψ Q) := by

  have hφ : (lev ≫ ψ) ≫ f₀ = lev ≫ f := by rw [Category.assoc, hψ]
  obtain ⟨φ₀, hφ₀⟩ := CerednikDrinfeld.QM.exists_comp_eq_of_forall_factorsThrough_of_isReduced k (lev ≫ f) f₀ lev₀
    (lev ≫ ψ) hφ (by
      intro z

      let Q₁ : SchemeHomOver (geomPoint k (RingHom.id k)) f :=
        castPt (geomPoint_id k).symm ⟨z.1 ≫ lev, by rw [Category.assoc]; exact z.2⟩
      have hQ₁ : FactorsThrough lev Q₁ := ⟨z.1, rfl⟩
      obtain ⟨P, hPt, hPQ⟩ := (lev_pts k (RingHom.id k) Q₁).mp hQ₁
      have h1 := hCt_lev _ P hPt
      rw [← hψp] at h1
      obtain ⟨P₀, hP₀⟩ := h1
      refine ⟨P₀, ?_⟩
      rw [hP₀]
      have e1 : P.1 ≫ p = z.1 ≫ lev := by
        have := congrArg Subtype.val hPQ
        simpa only [mapPt_coe, castPt_coe, Q₁] using this
      show (mapPt ψ hψ (mapPt p hp P)).1 = (mapPt (lev ≫ ψ) hφ z).1
      simp only [mapPt_coe, ← Category.assoc, e1])
  obtain ⟨Q₀, hQ₀⟩ := hQ
  exact ⟨Q₀ ≫ φ₀, by rw [Category.assoc, hφ₀, ← Category.assoc, hQ₀]; rfl⟩

end Transverse

section Count

theorem castHom_eq_zero_iff (N ℓ : ℕ) [NeZero N] (hℓ : ℓ ≠ 0) (x : ZMod (N * ℓ)) :
    (ZMod.castHom (dvd_mul_right N ℓ) (ZMod N) x = 0) ↔ ℓ • x = 0 := by
  haveI : NeZero (N * ℓ) := ⟨mul_ne_zero (NeZero.ne N) hℓ⟩
  obtain ⟨a, rfl⟩ := ZMod.natCast_zmod_surjective x
  rw [map_natCast, ZMod.natCast_eq_zero_iff, nsmul_eq_mul, ← Nat.cast_mul, ZMod.natCast_eq_zero_iff]
  constructor
  · rintro ⟨c, hc⟩; exact ⟨c, by rw [hc]; ring⟩
  · rintro ⟨c, hc⟩
    refine ⟨c, Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero hℓ) ?_⟩
    rw [hc]; ring

theorem nonempty_addEquiv_of_ker_eq_torsion (N ℓ : ℕ) [NeZero N] (hℓ : ℓ ≠ 0)
    {G H : Type*} [AddCommGroup G] [AddCommGroup H]
    (e : G ≃+ ZMod (N * ℓ) × ZMod (N * ℓ)) (π : G →+ H) (hπ : Function.Surjective π)
    (hker : ∀ g : G, π g = 0 ↔ ℓ • g = 0) :
    Nonempty (H ≃+ ZMod N × ZMod N) := by
  classical
  let r : ZMod (N * ℓ) →+ ZMod N := (ZMod.castHom (dvd_mul_right N ℓ) (ZMod N)).toAddMonoidHom
  let ρ : G →+ ZMod N × ZMod N := (AddMonoidHom.prodMap r r).comp e.toAddMonoidHom
  have hr : Function.Surjective r := ZMod.castHom_surjective (dvd_mul_right N ℓ)
  have hρsurj : Function.Surjective ρ := by
    intro y
    obtain ⟨a, ha⟩ := hr y.1
    obtain ⟨b, hb⟩ := hr y.2
    refine ⟨e.symm (a, b), ?_⟩
    simp only [ρ, AddMonoidHom.coe_comp, Function.comp_apply, AddEquiv.coe_toAddMonoidHom, AddEquiv.apply_symm_apply,
      AddMonoidHom.prodMap, AddMonoidHom.prod_apply, AddMonoidHom.coe_comp, AddMonoidHom.coe_fst, AddMonoidHom.coe_snd,
      Function.comp_apply, ha, hb]
  have hρker : ∀ g : G, ρ g = 0 ↔ ℓ • g = 0 := by
    intro g
    have h2 : ℓ • g = 0 ↔ ℓ • e g = 0 := by
      rw [← map_nsmul, ← e.map_zero]; exact e.injective.eq_iff.symm
    rw [h2]
    show (r (e g).1, r (e g).2) = (0 : ZMod N × ZMod N) ↔ ℓ • e g = 0
    rw [Prod.ext_iff, Prod.ext_iff, Prod.smul_fst, Prod.smul_snd, Prod.fst_zero, Prod.snd_zero]
    exact Iff.and (castHom_eq_zero_iff N ℓ hℓ _) (castHom_eq_zero_iff N ℓ hℓ _)
  have hkk : π.ker = ρ.ker := by
    ext g; rw [AddMonoidHom.mem_ker, AddMonoidHom.mem_ker, hker, hρker]
  exact ⟨((QuotientAddGroup.quotientKerEquivOfSurjective π hπ).symm.trans
    (QuotientAddGroup.quotientAddEquivOfEq hkk)).trans (QuotientAddGroup.quotientKerEquivOfSurjective ρ hρsurj)⟩

end Count

end QLBook21
p2m_reactivate "P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_exists_withExtraLevel_isLevelIsogeny_of_levelLift.QLBook21"

end QLBookWrap
p2m_reactivate "P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_exists_withExtraLevel_isLevelIsogeny_of_levelLift.QLBook21"

namespace QLpts
open CategoryTheory AlgebraicGeometry

section ptsA

variable {K : Type} [Field K] [IsAlgClosed K]

theorem discreteTopology_of_isFinite {Z : Scheme.{0}} (g : Z ⟶ Spec (CommRingCat.of K)) [IsFinite g] :
    DiscreteTopology ↥Z := by
  have h0 : DiscreteTopology ↥(Spec (CommRingCat.of K)) := ⟨Subsingleton.elim _ _⟩
  have h1 : _root_.IsDiscrete (Set.univ : Set ↥(Spec (CommRingCat.of K))) := isDiscrete_univ_iff.mpr h0
  have h2 := g.isDiscrete_preimage h1
  rw [Set.preimage_univ] at h2
  exact isDiscrete_univ_iff.mp h2

theorem isClosed_singleton_of_isFinite {Z : Scheme.{0}} (g : Z ⟶ Spec (CommRingCat.of K)) [IsFinite g] (x : ↥Z) :
    IsClosed ({x} : Set ↥Z) := by
  haveI := discreteTopology_of_isFinite g
  exact isClosed_discrete _

theorem eq_specMap_comp_pointOfClosedPoint {Z : Scheme.{0}} (g : Z ⟶ Spec (CommRingCat.of K)) [IsFinite g]
    (k' : Type) [Field k'] (sk : K →+* k')
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

omit [IsAlgClosed K] in
theorem base_specMap_comp {Z : Scheme.{0}} (k' : Type) [Field k'] (sk : K →+* k')
    (p : Spec (CommRingCat.of K) ⟶ Z) :
    (Spec.map (CommRingCat.ofHom sk) ≫ p).base (IsLocalRing.closedPoint k') = p.base (IsLocalRing.closedPoint K) := by
  rw [Scheme.Hom.comp_base, TopCat.coe_comp, Function.comp_apply,
    Subsingleton.elim ((Spec.map (CommRingCat.ofHom sk)).base (IsLocalRing.closedPoint k')) (IsLocalRing.closedPoint K)]

theorem bijective_specMap_comp {Z : Scheme.{0}} (g : Z ⟶ Spec (CommRingCat.of K)) [IsFinite g]
    (k' : Type) [Field k'] (sk : K →+* k') :
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

end ptsA
p2m_reactivate "P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_exists_withExtraLevel_isLevelIsogeny_of_levelLift.QLBook21"

end QLpts
p2m_reactivate "P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_exists_withExtraLevel_isLevelIsogeny_of_levelLift.QLBook21"

namespace QL
open CerednikDrinfeld.QM.FakeEllipticCurve GoodReductionJacobian CategoryTheory.Limits

variable {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} {N : ℕ} {S : Type} [CommRing S]

theorem natCast_mem (hΛ : IsOrder Λ) (n : ℕ) : ((n : ℚ) : ℍ[ℚ, a, b]) ∈ Λ := by
  have : ((n : ℚ) : ℍ[ℚ, a, b]) = (n : ℤ) • (1 : ℍ[ℚ, a, b]) := by
    rw [zsmul_eq_mul, mul_one]; norm_cast
  rw [this]; exact Λ.smul_mem _ hΛ.one_mem

theorem nsmulPt_coe {A : Scheme.{0}} {f : A ⟶ Spec (CommRingCat.of S)} (L : RelativeGroupLaw S f)
    {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of S)) (n : ℕ) (x : SchemeHomOver t f) :
    (nsmulPt L t n x).1 = x.1 ≫ (nsmulPt L f n ⟨𝟙 A, Category.id_comp f⟩).1 := by
  have hnat : ∀ (m : ℕ) (y : SchemeHomOver f f),
      schemeHomOverComp x.1 x.2 (nsmulPt L f m y) = nsmulPt L t m (schemeHomOverComp x.1 x.2 y) := by
    intro m y
    induction m with
    | zero => exact L.one_natural f t x.1 x.2
    | succ m ih =>
      show schemeHomOverComp x.1 x.2 (L.mul f (nsmulPt L f m y) y) = L.mul t (nsmulPt L t m _) _
      rw [L.mul_natural, ih]
  have hx : schemeHomOverComp x.1 x.2 (⟨𝟙 A, Category.id_comp f⟩ : SchemeHomOver f f) = x :=
    Subtype.ext (Category.comp_id _)
  have h := hnat n ⟨𝟙 A, Category.id_comp f⟩
  rw [hx] at h
  rw [← h]
  rfl

theorem eq_of_mapPt_id {A B : Scheme.{0}} {f : A ⟶ Spec (CommRingCat.of S)} {g : B ⟶ Spec (CommRingCat.of S)}
    (α β : A ⟶ B) (hα : α ≫ g = f) (hβ : β ≫ g = f)
    (h : mapPt α hα (⟨𝟙 A, Category.id_comp f⟩ : SchemeHomOver f f) = mapPt β hβ ⟨𝟙 A, Category.id_comp f⟩) : α = β := by
  have := congrArg Subtype.val h
  simpa [mapPt] using this

end QL
p2m_reactivate "P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_exists_withExtraLevel_isLevelIsogeny_of_levelLift.QLBook21"

namespace QL
open CerednikDrinfeld.QM.FakeEllipticCurve GoodReductionJacobian CategoryTheory.Limits

variable {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} {N : ℕ} {S : Type} [CommRing S]

section Generic
variable {A : Scheme.{0}} {f : A ⟶ Spec (CommRingCat.of S)} (L : RelativeGroupLaw S f)
  {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of S))

theorem nsmulPt_eq_pow (n : ℕ) (P : SchemeHomOver t f) :
    letI := L.pointGroup t
    nsmulPt L t n P = P ^ n := by
  letI := L.pointGroup t
  induction n with
  | zero => rw [pow_zero]; rfl
  | succ n ih =>
    show L.mul t (nsmulPt L t n P) P = P ^ (n + 1)
    rw [pow_succ, ih]; rfl

theorem nsmulPt_one (n : ℕ) : nsmulPt L t n (L.one t) = L.one t := by
  letI := L.pointGroup t
  rw [nsmulPt_eq_pow]; exact one_pow n

theorem nsmulPt_mul (hc : L.IsCommutative) (n : ℕ) (P Q : SchemeHomOver t f) :
    nsmulPt L t n (L.mul t P Q) = L.mul t (nsmulPt L t n P) (nsmulPt L t n Q) := by
  letI := L.pointGroup t
  rw [nsmulPt_eq_pow, nsmulPt_eq_pow, nsmulPt_eq_pow]
  show (P * Q) ^ n = P ^ n * Q ^ n
  exact (show Commute P Q from hc t P Q).mul_pow n

theorem nsmulPt_inv (n : ℕ) (P : SchemeHomOver t f) :
    nsmulPt L t n (L.inv t P) = L.inv t (nsmulPt L t n P) := by
  letI := L.pointGroup t
  rw [nsmulPt_eq_pow, nsmulPt_eq_pow]
  show (P⁻¹) ^ n = (P ^ n)⁻¹
  exact inv_pow P n

theorem nsmulPt_nsmulPt (m n : ℕ) (P : SchemeHomOver t f) :
    nsmulPt L t m (nsmulPt L t n P) = nsmulPt L t (n * m) P := by
  letI := L.pointGroup t
  rw [nsmulPt_eq_pow, nsmulPt_eq_pow, nsmulPt_eq_pow]
  exact (pow_mul P n m).symm

theorem one_coe (t : T ⟶ Spec (CommRingCat.of S)) :
    (L.one t).1 = t ≫ (L.one (𝟙 (Spec (CommRingCat.of S)))).1 :=
  (congrArg Subtype.val (L.one_natural (𝟙 _) t t (Category.comp_id _))).symm

theorem factorsThrough_pullback_fst_one_iff (m : A ⟶ A) (hm : m ≫ f = f) (P : SchemeHomOver t f) :
    FactorsThrough (pullback.fst m (L.one (𝟙 (Spec (CommRingCat.of S)))).1) P ↔ mapPt m hm P = L.one t := by
  constructor
  · rintro ⟨Q₀, hQ₀⟩
    apply Subtype.ext
    rw [one_coe]
    show P.1 ≫ m = _
    have h2 : Q₀ ≫ pullback.snd m (L.one (𝟙 (Spec (CommRingCat.of S)))).1 = t := by
      symm
      calc t = P.1 ≫ f := P.2.symm
        _ = (Q₀ ≫ pullback.fst m (L.one (𝟙 (Spec (CommRingCat.of S)))).1) ≫ (m ≫ f) := by rw [hQ₀, hm]
        _ = Q₀ ≫ (pullback.fst m (L.one (𝟙 (Spec (CommRingCat.of S)))).1 ≫ m) ≫ f := by
          simp only [Category.assoc]
        _ = Q₀ ≫ (pullback.snd m (L.one (𝟙 (Spec (CommRingCat.of S)))).1 ≫ (L.one (𝟙 (Spec (CommRingCat.of S)))).1) ≫ f := by
          rw [pullback.condition]
        _ = Q₀ ≫ pullback.snd m (L.one (𝟙 (Spec (CommRingCat.of S)))).1 := by
          rw [Category.assoc, (L.one _).2, Category.comp_id]
    rw [← hQ₀, Category.assoc, pullback.condition, ← Category.assoc, h2]
  · intro h
    have h1 : P.1 ≫ m = t ≫ (L.one (𝟙 (Spec (CommRingCat.of S)))).1 := by
      rw [← one_coe]; exact congrArg Subtype.val h
    exact ⟨pullback.lift P.1 t h1, pullback.lift_fst _ _ _⟩

end Generic
p2m_reactivate "P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_exists_withExtraLevel_isLevelIsogeny_of_levelLift.QLBook21"

section Hom
variable {A A' : Scheme.{0}} {f : A ⟶ Spec (CommRingCat.of S)} {f' : A' ⟶ Spec (CommRingCat.of S)}
  (L : RelativeGroupLaw S f) (L' : RelativeGroupLaw S f') (φ : A ⟶ A') (hφ : φ ≫ f' = f)
  (hom : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of S)) (P Q : SchemeHomOver t f),
    mapPt φ hφ (L.mul t P Q) = L'.mul t (mapPt φ hφ P) (mapPt φ hφ Q))
  {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of S))

include hom in
theorem mapPt_one : mapPt φ hφ (L.one t) = L'.one t := by
  letI := L'.pointGroup t
  have h : mapPt φ hφ (L.one t) * mapPt φ hφ (L.one t) = mapPt φ hφ (L.one t) := by
    show L'.mul t _ _ = _
    rw [← hom, L.one_mul]
  exact mul_eq_right.mp h

include hom in
theorem mapPt_nsmulPt (n : ℕ) (P : SchemeHomOver t f) :
    mapPt φ hφ (nsmulPt L t n P) = nsmulPt L' t n (mapPt φ hφ P) := by
  induction n with
  | zero => exact mapPt_one L L' φ hφ hom t
  | succ n ih =>
    show mapPt φ hφ (L.mul t (nsmulPt L t n P) P) = L'.mul t (nsmulPt L' t n _) _
    rw [hom, ih]

end Hom
p2m_reactivate "P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_exists_withExtraLevel_isLevelIsogeny_of_levelLift.QLBook21"

theorem pushPt_act_natCast (hΛ : IsOrder Λ) (E : FakeEllipticCurve Λ N S) (n : ℕ)
    {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of S)) (P : SchemeHomOver t E.f) :
    pushPt (E.act ⟨((n : ℚ) : ℍ[ℚ, a, b]), natCast_mem hΛ n⟩) (E.act_over _) P = nsmulPt E.L t n P := by
  letI := E.L.pointGroup t
  induction n with
  | zero =>
    have e : (⟨(((0 : ℕ) : ℚ) : ℍ[ℚ, a, b]), natCast_mem hΛ 0⟩ : ↥Λ) = 0 := by apply Subtype.ext; simp
    have h2 := E.act_add (0 : ↥Λ) 0 t P
    rw [add_zero] at h2
    have h3 : pushPt (E.act (0 : ↥Λ)) (E.act_over 0) P = E.L.one t := by
      have := mul_eq_right.mp (h2.symm.trans rfl : E.L.mul t _ _ = _)
      exact this
    rw [e]; exact h3
  | succ n ih =>
    have e : (⟨(((n + 1 : ℕ) : ℚ) : ℍ[ℚ, a, b]), natCast_mem hΛ (n + 1)⟩ : ↥Λ) =
        ⟨((n : ℚ) : ℍ[ℚ, a, b]), natCast_mem hΛ n⟩ + ⟨1, hΛ.one_mem⟩ := by
      apply Subtype.ext; push_cast; rfl
    rw [e, E.act_add, ih]
    show E.L.mul t (nsmulPt E.L t n P) (pushPt (E.act ⟨1, hΛ.one_mem⟩) _ P) = E.L.mul t (nsmulPt E.L t n P) P
    congr 1
    apply Subtype.ext
    show P.1 ≫ E.act ⟨1, hΛ.one_mem⟩ = P.1
    rw [E.act_one hΛ.one_mem, Category.comp_id]

end QL
p2m_reactivate "P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_exists_withExtraLevel_isLevelIsogeny_of_levelLift.QLBook21"

namespace QL
open CerednikDrinfeld.QM.FakeEllipticCurve GoodReductionJacobian CategoryTheory.Limits

variable {S : Type} [CommRing S] {A A' : Scheme.{0}} {f : A ⟶ Spec (CommRingCat.of S)} {f' : A' ⟶ Spec (CommRingCat.of S)}

theorem factorsThrough_ker_iff (L' : RelativeGroupLaw S f') (ψ : A ⟶ A') (hψ : ψ ≫ f' = f)
    {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of S)) (P : SchemeHomOver t f) :
    FactorsThrough (pullback.fst ψ (L'.one (𝟙 (Spec (CommRingCat.of S)))).1) P ↔ mapPt ψ hψ P = L'.one t := by
  constructor
  · rintro ⟨Q₀, hQ₀⟩
    apply Subtype.ext
    rw [one_coe]
    show P.1 ≫ ψ = _
    have h2 : Q₀ ≫ pullback.snd ψ (L'.one (𝟙 (Spec (CommRingCat.of S)))).1 = t := by
      symm
      calc t = P.1 ≫ f := P.2.symm
        _ = (Q₀ ≫ pullback.fst ψ (L'.one (𝟙 (Spec (CommRingCat.of S)))).1) ≫ (ψ ≫ f') := by rw [hQ₀, hψ]
        _ = Q₀ ≫ (pullback.fst ψ (L'.one (𝟙 (Spec (CommRingCat.of S)))).1 ≫ ψ) ≫ f' := by simp only [Category.assoc]
        _ = Q₀ ≫ (pullback.snd ψ (L'.one (𝟙 (Spec (CommRingCat.of S)))).1 ≫ (L'.one (𝟙 (Spec (CommRingCat.of S)))).1) ≫ f' := by
          rw [pullback.condition]
        _ = Q₀ ≫ pullback.snd ψ (L'.one (𝟙 (Spec (CommRingCat.of S)))).1 := by
          rw [Category.assoc, (L'.one _).2, Category.comp_id]
    rw [← hQ₀, Category.assoc, pullback.condition, ← Category.assoc, h2]
  · intro h
    have h1 : P.1 ≫ ψ = t ≫ (L'.one (𝟙 (Spec (CommRingCat.of S)))).1 := by
      rw [← one_coe]; exact congrArg Subtype.val h
    exact ⟨pullback.lift P.1 t h1, pullback.lift_fst _ _ _⟩

theorem mapPt_inv (L : RelativeGroupLaw S f) (L' : RelativeGroupLaw S f') (φ : A ⟶ A') (hφ : φ ≫ f' = f)
    (hom : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of S)) (P Q : SchemeHomOver t f),
      mapPt φ hφ (L.mul t P Q) = L'.mul t (mapPt φ hφ P) (mapPt φ hφ Q))
    {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of S)) (P : SchemeHomOver t f) :
    mapPt φ hφ (L.inv t P) = L'.inv t (mapPt φ hφ P) := by
  letI := L.pointGroup t
  letI := L'.pointGroup t
  have h : mapPt φ hφ (L.inv t P) * mapPt φ hφ P = 1 := by
    show L'.mul t _ _ = L'.one t
    rw [← hom, L.inv_mul_cancel]
    exact mapPt_one L L' φ hφ hom t
  exact eq_inv_of_mul_eq_one_left h

theorem nsmul_eq_nsmulPt (L : RelativeGroupLaw S f) {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of S)) (n : ℕ)
    (x : SchemeHomOver t f) : L.nsmul t n x = nsmulPt L t n x := by
  induction n with
  | zero => rfl
  | succ n ih =>
    show L.mul t (L.nsmul t n x) x = L.mul t (nsmulPt L t n x) x
    rw [ih]

end QL
p2m_reactivate "P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_exists_withExtraLevel_isLevelIsogeny_of_levelLift.QLBook21"

namespace QL
open CerednikDrinfeld.QM.FakeEllipticCurve GoodReductionJacobian CategoryTheory.Limits

theorem exists_comp_eq_of_isFinite_of_surjective {k' : Type} [Field k'] [IsAlgClosed k'] {X Y : Scheme.{0}}
    (φ : X ⟶ Y) [IsFinite φ] [Surjective φ] (Q : Spec (CommRingCat.of k') ⟶ Y) :
    ∃ P : Spec (CommRingCat.of k') ⟶ X, P ≫ φ = Q := by
  let z : pullback φ Q ⟶ Spec (CommRingCat.of k') := pullback.snd φ Q
  have hne : Nonempty ↥(pullback φ Q) := by
    obtain ⟨x, -⟩ := z.surjective (IsLocalRing.closedPoint k')
    exact ⟨x⟩
  haveI : CompactSpace ↥(pullback φ Q) := by
    constructor
    have h := QuasiCompact.isCompact_preimage (f := z) (Set.univ) isOpen_univ isCompact_univ
    simpa using h
  haveI := hne
  obtain ⟨x, -, hx⟩ := IsClosed.exists_closed_singleton (X := ↥(pullback φ Q)) isClosed_univ Set.univ_nonempty
  let p := (pointEquivClosedPoint z).symm ⟨x, mem_closedPoints_iff.mpr hx⟩
  refine ⟨p.1 ≫ pullback.fst φ Q, ?_⟩
  rw [Category.assoc, pullback.condition, ← Category.assoc, p.2, Category.id_comp]

variable {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} {N : ℕ}

theorem natCard_torsion_eq_pow_four (K : Type) [Field K] [IsAlgClosed K] (E : FakeEllipticCurve Λ N K)
    (ℓ : ℕ) [hℓ : Fact ℓ.Prime] (hℓK : (ℓ : K) ≠ 0) :
    Nat.card {P : SchemeHomOver (𝟙 (Spec (CommRingCat.of K))) E.f //
        nsmulPt E.L (𝟙 (Spec (CommRingCat.of K))) ℓ P = E.L.one (𝟙 (Spec (CommRingCat.of K)))} = ℓ ^ 4 := by
  haveI : IsProper E.f := E.bundle.proper
  haveI : SmoothOfRelativeDimension 2 E.f := smoothOfRelativeDimension_two K E
  let β : SchemeHomOver E.f E.f := E.L.nsmul E.f ℓ RelativeGroupLaw.idPoint
  haveI hét : Etale (E.L.schemeNsmul ℓ) :=
    RelativeGroupLaw.etale_schemeNsmul_of_isUnit_of_smoothOfRelativeDimension E.L (fun t x y => E.comm t x y) 2 ℓ
      (isUnit_iff_ne_zero.mpr hℓK)
  haveI : Etale (E.L.endKerStr β) := by
    show Etale (pullback.snd (E.L.schemeNsmul ℓ) (E.L.one (𝟙 (Spec (CommRingCat.of K)))).1)
    infer_instance
  obtain ⟨-, -, hcard⟩ := RelativeGroupLaw.isFinite_endKerStr_and_natCard_eq_endDegree_of_etale K E.f E.L β
  rw [RelativeGroupLaw.endDegree_nsmul_idPoint_eq_pow K E.f E.L E.comm E.bundle 2 ℓ hℓ.out.pos] at hcard
  rw [← hcard]
  apply Nat.card_congr
  apply Equiv.subtypeEquivRight
  intro P
  have : NeronModelInfra.schemeHomOverComp P β = nsmulPt E.L (𝟙 _) ℓ P := by
    apply Subtype.ext
    rw [nsmulPt_coe E.L (𝟙 _) ℓ P]
    show P.1 ≫ (E.L.nsmul E.f ℓ RelativeGroupLaw.idPoint).1 = P.1 ≫ (nsmulPt E.L E.f ℓ ⟨𝟙 E.A, _⟩).1
    rw [nsmul_eq_nsmulPt]
  rw [this]

theorem natCard_torsion_zmod_prod (N ℓ : ℕ) [NeZero N] (hℓ : ℓ ≠ 0) :
    Nat.card {x : ZMod (N * ℓ) × ZMod (N * ℓ) // ℓ • x = 0} = ℓ ^ 2 := by
  haveI : NeZero (N * ℓ) := ⟨mul_ne_zero (NeZero.ne N) hℓ⟩
  let r : ZMod (N * ℓ) →+ ZMod N := (ZMod.castHom (dvd_mul_right N ℓ) (ZMod N)).toAddMonoidHom
  have hr : Function.Surjective r := ZMod.castHom_surjective (dvd_mul_right N ℓ)
  have hker : ∀ x : ZMod (N * ℓ), x ∈ r.ker ↔ ℓ • x = 0 := fun x =>
    (AddMonoidHom.mem_ker).trans (QLBook21.castHom_eq_zero_iff N ℓ hℓ x)
  have hk : Nat.card r.ker = ℓ := by
    have h1 := AddSubgroup.card_eq_card_quotient_mul_card_addSubgroup r.ker
    rw [Nat.card_congr (QuotientAddGroup.quotientKerEquivOfSurjective r hr).toEquiv, Nat.card_zmod, Nat.card_zmod] at h1
    have h2 : N * ℓ = N * Nat.card r.ker := h1
    exact (Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero (NeZero.ne N)) h2).symm
  have e : {x : ZMod (N * ℓ) × ZMod (N * ℓ) // ℓ • x = 0} ≃ r.ker × r.ker :=
    { toFun := fun x => ⟨⟨x.1.1, (hker _).mpr (by have h := congrArg Prod.fst x.2; rwa [Prod.smul_fst, Prod.fst_zero] at h)⟩,
        ⟨x.1.2, (hker _).mpr (by have h := congrArg Prod.snd x.2; rwa [Prod.smul_snd, Prod.snd_zero] at h)⟩⟩
      invFun := fun y => ⟨(y.1.1, y.2.1), by
        rw [Prod.smul_mk, Prod.mk_eq_zero]; exact ⟨(hker _).mp y.1.2, (hker _).mp y.2.2⟩⟩
      left_inv := fun x => rfl
      right_inv := fun y => rfl }
  rw [Nat.card_congr e, Nat.card_prod, hk, pow_two]

end QL
p2m_reactivate "P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_exists_withExtraLevel_isLevelIsogeny_of_levelLift.QLBook21"

namespace QL
open CerednikDrinfeld.QM.FakeEllipticCurve GoodReductionJacobian CategoryTheory.Limits

variable {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} {N : ℕ}

theorem exists_zmod_prod_equiv_kerPoints [NeZero N]
    (k : Type) [Field k] [IsAlgClosed k] (ℓ : ℕ) [hℓ : Fact ℓ.Prime] (hℓk : (ℓ : k) ≠ 0)
    (E₀ : FakeEllipticCurve Λ N k) {A : Scheme.{0}} {f : A ⟶ Spec (CommRingCat.of k)} (L : RelativeGroupLaw k f)
    (hc : L.IsCommutative)
    (p : E₀.A ⟶ A) (hp : p ≫ f = E₀.f)
    (p_hom : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of k)) (P Q : SchemeHomOver t E₀.f),
      mapPt p hp (E₀.L.mul t P Q) = L.mul t (mapPt p hp P) (mapPt p hp Q))
    [IsFinite p] [Surjective p]
    (ψ : A ⟶ E₀.A) (hψ : ψ ≫ E₀.f = f)
    (ψ_hom : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of k)) (P Q : SchemeHomOver t f),
      mapPt ψ hψ (L.mul t P Q) = E₀.L.mul t (mapPt ψ hψ P) (mapPt ψ hψ Q))
    (hψp : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of k)) (P : SchemeHomOver t E₀.f),
      mapPt ψ hψ (mapPt p hp P) = nsmulPt E₀.L t ℓ P)
    (hpψ : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of k)) (Q : SchemeHomOver t f),
      mapPt p hp (mapPt ψ hψ Q) = nsmulPt L t ℓ Q)
    {Ct : Scheme.{0}} (levt : Ct ⟶ E₀.A) {K₀ : Scheme.{0}} (levK : K₀ ⟶ E₀.A)
    (hCt_points : ∃ e : ZMod (N * ℓ) × ZMod (N * ℓ) ≃ {P : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) E₀.f // FactorsThrough levt P},
        ∀ x y : ZMod (N * ℓ) × ZMod (N * ℓ),
          (e (x + y) : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) E₀.f) = E₀.L.mul (𝟙 (Spec (CommRingCat.of k))) (e x) (e y))
    (hK_points : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of k)) (P : SchemeHomOver t E₀.f),
        FactorsThrough levK P ↔ (FactorsThrough levt P ∧ nsmulPt E₀.L t ℓ P = E₀.L.one t))
    (p_ker : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of k)) (P : SchemeHomOver t E₀.f),
        mapPt p hp P = L.one t ↔ FactorsThrough levK P) :
    ∃ e : ZMod ℓ × ZMod ℓ ≃ {P : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) f // mapPt ψ hψ P = E₀.L.one _},
      ∀ x y : ZMod ℓ × ZMod ℓ,
        (e (x + y) : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) f) = L.mul _ (e x) (e y) := by
  have hℓp : ℓ.Prime := hℓ.out
  letI instG : CommGroup (SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) E₀.f) :=
    { E₀.L.pointGroup _ with mul_comm := E₀.comm _ }
  letI instH : CommGroup (SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) f) :=
    { L.pointGroup _ with mul_comm := hc _ }
  let Φ : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) E₀.f →* SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) f :=
    { toFun := fun P => mapPt p hp P
      map_one' := mapPt_one E₀.L L p hp p_hom _
      map_mul' := fun P Q => p_hom _ P Q }
  let Ψ : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) f →* SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) E₀.f :=
    { toFun := fun Q => mapPt ψ hψ Q
      map_one' := mapPt_one L E₀.L ψ hψ ψ_hom _
      map_mul' := fun P Q => ψ_hom _ P Q }
  let T : Subgroup (SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) E₀.f) :=
    { carrier := {P | nsmulPt E₀.L _ ℓ P = E₀.L.one _}
      mul_mem' := by
        intro P Q hP hQ
        show nsmulPt E₀.L _ ℓ (E₀.L.mul _ P Q) = E₀.L.one _
        rw [nsmulPt_mul E₀.L _ E₀.comm, hP, hQ]; exact E₀.L.one_mul _ _
      one_mem' := nsmulPt_one E₀.L _ ℓ
      inv_mem' := by
        intro P hP
        show nsmulPt E₀.L _ ℓ (E₀.L.inv _ P) = E₀.L.one _
        rw [nsmulPt_inv, hP]; exact inv_one }
  have hmemT : ∀ P, P ∈ T ↔ nsmulPt E₀.L _ ℓ P = E₀.L.one _ := fun P => Iff.rfl
  let Kψ : Subgroup (SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) f) := Ψ.ker
  have hmemK : ∀ Q, Q ∈ Kψ ↔ mapPt ψ hψ Q = E₀.L.one _ := fun Q => MonoidHom.mem_ker
  have hΦT : ∀ P : ↥T, (Φ.domRestrict T) P ∈ Kψ := by
    intro P
    rw [hmemK]
    show mapPt ψ hψ (mapPt p hp P.1) = E₀.L.one _
    rw [hψp]; exact P.2
  let ΦT : ↥T →* ↥Kψ := (Φ.domRestrict T).codRestrict Kψ hΦT
  have hΦTval : ∀ P : ↥T, ((ΦT P : ↥Kψ) : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) f) = mapPt p hp P.1 :=
    fun P => rfl
  have hsurjT : Function.Surjective ΦT := by
    rintro ⟨Q, hQ⟩
    obtain ⟨P1, hP1⟩ := exists_comp_eq_of_isFinite_of_surjective p Q.1
    let P : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) E₀.f := ⟨P1, by rw [← hp, ← Category.assoc, hP1]; exact Q.2⟩
    have hPQ : mapPt p hp P = Q := Subtype.ext hP1
    have hPT : P ∈ T := by
      rw [hmemT, ← hψp, hPQ]; exact (hmemK Q).mp hQ
    exact ⟨⟨P, hPT⟩, Subtype.ext (by rw [hΦTval]; exact hPQ)⟩
  have hT : Nat.card ↥T = ℓ ^ 4 := natCard_torsion_eq_pow_four k E₀ ℓ hℓk

  obtain ⟨eC, heC⟩ := hCt_points
  have heC_one : (eC 0).1 = E₀.L.one _ := by
    have h := heC 0 0
    rw [add_zero] at h
    exact mul_eq_right.mp (show (eC 0).1 * (eC 0).1 = (eC 0).1 from h.symm)
  have heC_nsmul : ∀ (n : ℕ) (x : ZMod (N * ℓ) × ZMod (N * ℓ)),
      (eC (n • x)).1 = nsmulPt E₀.L _ n (eC x).1 := by
    intro n x
    induction n with
    | zero => rw [zero_smul]; exact heC_one
    | succ n ih => rw [succ_nsmul, heC, ih]; rfl
  have hkerT : Nat.card ↥ΦT.ker = ℓ ^ 2 := by
    rw [← natCard_torsion_zmod_prod N ℓ hℓp.ne_zero]
    apply Nat.card_congr
    refine ⟨fun x => ⟨eC.symm ⟨x.1.1, ?_⟩, ?_⟩, fun y => ⟨⟨(eC y.1).1, ?_⟩, ?_⟩, ?_, ?_⟩
    ·
      have hx : ΦT x.1 = 1 := x.2
      have h1 : mapPt p hp x.1.1 = L.one _ := by rw [← hΦTval x.1, hx]; rfl
      exact ((hK_points _ _).mp ((p_ker _ _).mp h1)).1
    ·
      apply eC.injective
      apply Subtype.ext
      rw [heC_nsmul, Equiv.apply_symm_apply]
      show nsmulPt E₀.L _ ℓ x.1.1 = (eC 0).1
      rw [heC_one]; exact x.1.2
    · rw [hmemT, ← heC_nsmul, y.2, heC_one]
    · show ΦT _ = 1
      apply Subtype.ext
      rw [hΦTval]
      show mapPt p hp (eC y.1).1 = L.one _
      rw [p_ker, hK_points]
      exact ⟨(eC y.1).2, by rw [← heC_nsmul, y.2, heC_one]⟩
    · intro x
      apply Subtype.ext; apply Subtype.ext
      simp only [Equiv.apply_symm_apply]
    · intro y
      apply Subtype.ext
      show eC.symm ⟨(eC y.1).1, _⟩ = y.1
      rw [Equiv.symm_apply_eq]
  have hK : Nat.card ↥Kψ = ℓ ^ 2 := by
    have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup ΦT.ker
    have hr : ΦT.range = ⊤ := MonoidHom.range_eq_top.mpr hsurjT
    have h2 : Nat.card (↥T ⧸ ΦT.ker) = Nat.card ↥Kψ := by
      rw [Nat.card_congr (QuotientGroup.quotientKerEquivRange ΦT).toEquiv, hr]
      exact Nat.card_congr Subgroup.topEquiv.toEquiv
    rw [hT, h2, hkerT, show ℓ ^ 4 = ℓ ^ 2 * ℓ ^ 2 by ring] at h1
    exact (Nat.eq_of_mul_eq_mul_right (pow_pos hℓp.pos 2) h1).symm
  have hexp : ∀ Q : ↥Kψ, Q ^ ℓ = 1 := by
    intro Q
    apply Subtype.ext
    show ((Q : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) f)) ^ ℓ = L.one _
    rw [← nsmulPt_eq_pow, ← hpψ, (hmemK _).mp Q.2]
    exact mapPt_one E₀.L L p hp p_hom _
  have hA : ∀ x : Additive ↥Kψ, ℓ • x = 0 := fun x => by
    show Additive.ofMul ((Additive.toMul x) ^ ℓ) = 0
    rw [hexp]; rfl
  have hcardA : ∀ d : ℕ, d ∣ ℓ → Nat.card ↥(Submodule.torsionBy ℤ (Additive ↥Kψ) d) = d ^ 2 := by
    intro d hd
    rcases (Nat.dvd_prime hℓp).mp hd with h1 | h1
    · subst h1
      rw [Nat.cast_one, Submodule.torsionBy_one]
      simp
    · rw [h1]
      have htop : Submodule.torsionBy ℤ (Additive ↥Kψ) (ℓ : ℕ) = ⊤ := by
        ext x
        simp only [Submodule.mem_torsionBy_iff, Submodule.mem_top, iff_true]
        exact_mod_cast hA x
      rw [htop]
      first | simpa using hK | (simp at hK ⊢; exact hK) | exact hK
  obtain ⟨eA⟩ := AddCommGroup.nonempty_zmod_prod_addEquiv_torsionBy_of_card_torsionBy_eq_sq hℓp.ne_zero hcardA
  let toK : ZMod ℓ × ZMod ℓ → ↥Kψ := fun x => Additive.toMul ((eA x : ↥(Submodule.torsionBy ℤ (Additive ↥Kψ) ℓ)) : Additive ↥Kψ)
  have toK_add : ∀ x y, toK (x + y) = toK x * toK y := by
    intro x y
    show Additive.toMul (((eA (x + y)) : Additive ↥Kψ)) = _
    rw [map_add]
    rfl
  have toK_bij : Function.Bijective toK := by
    constructor
    · intro x y h
      apply eA.injective
      apply Subtype.ext
      exact Additive.toMul.injective h
    · intro Q
      have hQ : (Additive.ofMul Q) ∈ Submodule.torsionBy ℤ (Additive ↥Kψ) ℓ := by
        rw [Submodule.mem_torsionBy_iff]; exact_mod_cast hA _
      obtain ⟨x, hx⟩ := eA.surjective ⟨Additive.ofMul Q, hQ⟩
      exact ⟨x, by show Additive.toMul ((eA x : _) : Additive ↥Kψ) = Q; rw [hx]; rfl⟩
  let eK : ZMod ℓ × ZMod ℓ ≃ ↥Kψ := Equiv.ofBijective toK toK_bij
  refine ⟨eK.trans ⟨fun Q => ⟨Q.1, (hmemK _).mp Q.2⟩, fun Q => ⟨Q.1, (hmemK _).mpr Q.2⟩, fun _ => rfl, fun _ => rfl⟩, ?_⟩
  intro x y
  show ((toK (x + y) : ↥Kψ) : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) f) = L.mul _ (toK x : ↥Kψ) (toK y : ↥Kψ)
  rw [toK_add]
  rfl

end QL
p2m_reactivate "P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_exists_withExtraLevel_isLevelIsogeny_of_levelLift.QLBook21"

namespace QL
open CerednikDrinfeld.QM.FakeEllipticCurve GoodReductionJacobian CategoryTheory.Limits

variable {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} {N : ℕ}

theorem exists_zmod_prod_equiv_imagePoints [NeZero N]
    (k : Type) [Field k] [IsAlgClosed k] (ℓ : ℕ) (hℓ : ℓ ≠ 0)
    (E₀ : FakeEllipticCurve Λ N k) {A : Scheme.{0}} {f : A ⟶ Spec (CommRingCat.of k)} (L : RelativeGroupLaw k f)
    (hc : L.IsCommutative)
    (p : E₀.A ⟶ A) (hp : p ≫ f = E₀.f)
    (p_hom : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of k)) (P Q : SchemeHomOver t E₀.f),
      mapPt p hp (E₀.L.mul t P Q) = L.mul t (mapPt p hp P) (mapPt p hp Q))
    {Ct : Scheme.{0}} (levt : Ct ⟶ E₀.A) {K₀ : Scheme.{0}} (levK : K₀ ⟶ E₀.A)
    (hCt_one : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of k)), FactorsThrough levt (E₀.L.one t))
    (hCt_sub : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of k)) (P Q : SchemeHomOver t E₀.f),
        FactorsThrough levt P → FactorsThrough levt Q →
          FactorsThrough levt (E₀.L.mul t P Q) ∧ FactorsThrough levt (E₀.L.inv t P))
    (hCt_points : ∃ e : ZMod (N * ℓ) × ZMod (N * ℓ) ≃ {P : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) E₀.f // FactorsThrough levt P},
        ∀ x y : ZMod (N * ℓ) × ZMod (N * ℓ),
          (e (x + y) : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) E₀.f) = E₀.L.mul (𝟙 (Spec (CommRingCat.of k))) (e x) (e y))
    (hK_points : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of k)) (P : SchemeHomOver t E₀.f),
        FactorsThrough levK P ↔ (FactorsThrough levt P ∧ nsmulPt E₀.L t ℓ P = E₀.L.one t))
    (p_ker : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of k)) (P : SchemeHomOver t E₀.f),
        mapPt p hp P = L.one t ↔ FactorsThrough levK P)
    {C : Scheme.{0}} (lev : C ⟶ A)
    (lev_one : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of k)), FactorsThrough lev (L.one t))
    (lev_sub : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of k)) (P Q : SchemeHomOver t f),
        FactorsThrough lev P → FactorsThrough lev Q → FactorsThrough lev (L.mul t P Q) ∧ FactorsThrough lev (L.inv t P))
    (lev_img : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of k)) (P : SchemeHomOver t E₀.f),
        FactorsThrough levt P → FactorsThrough lev (mapPt p hp P))
    (lev_pts : ∀ (k' : Type) [Field k'] [IsAlgClosed k'] (sk : k →+* k') (Q : SchemeHomOver (geomPoint k' sk) f),
        FactorsThrough lev Q ↔ ∃ P : SchemeHomOver (geomPoint k' sk) E₀.f, FactorsThrough levt P ∧ mapPt p hp P = Q) :
    ∃ e : ZMod N × ZMod N ≃ {Q : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) f // FactorsThrough lev Q},
      ∀ x y : ZMod N × ZMod N,
        (e (x + y) : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) f) = L.mul _ (e x) (e y) := by
  letI instG : CommGroup (SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) E₀.f) :=
    { E₀.L.pointGroup _ with mul_comm := E₀.comm _ }
  letI instH : CommGroup (SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) f) :=
    { L.pointGroup _ with mul_comm := hc _ }
  let Gs : Subgroup (SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) E₀.f) :=
    { carrier := {P | FactorsThrough levt P}
      mul_mem' := fun hP hQ => (hCt_sub _ _ _ hP hQ).1
      one_mem' := hCt_one _
      inv_mem' := fun {P} hP => (hCt_sub _ _ P hP hP).2 }
  let Hs : Subgroup (SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) f) :=
    { carrier := {Q | FactorsThrough lev Q}
      mul_mem' := fun hP hQ => (lev_sub _ _ _ hP hQ).1
      one_mem' := lev_one _
      inv_mem' := fun {P} hP => (lev_sub _ _ P hP hP).2 }
  let Φ : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) E₀.f →* SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) f :=
    { toFun := fun P => mapPt p hp P
      map_one' := mapPt_one E₀.L L p hp p_hom _
      map_mul' := fun P Q => p_hom _ P Q }
  have hΦG : ∀ P : ↥Gs, (Φ.domRestrict Gs) P ∈ Hs := fun P => lev_img _ P.1 P.2
  let π : ↥Gs →* ↥Hs := (Φ.domRestrict Gs).codRestrict Hs hΦG
  have hπval : ∀ P : ↥Gs, ((π P : ↥Hs) : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) f) = mapPt p hp P.1 := fun P => rfl
  have hπsurj : Function.Surjective π := by
    rintro ⟨Q, hQ⟩
    let Q₁ : SchemeHomOver (geomPoint k (RingHom.id k)) f := QLBook21.castPt (QLBook21.geomPoint_id k).symm Q
    obtain ⟨P₁, hP₁t, hP₁⟩ := (lev_pts k (RingHom.id k) Q₁).mp hQ
    let P : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) E₀.f := QLBook21.castPt (QLBook21.geomPoint_id k) P₁
    refine ⟨⟨P, hP₁t⟩, Subtype.ext (Subtype.ext ?_)⟩
    show (P.1 ≫ p) = Q.1
    exact congrArg Subtype.val hP₁
  have hπker : ∀ g : ↥Gs, π g = 1 ↔ g.1 ^ ℓ = 1 := by
    intro g
    rw [← nsmulPt_eq_pow]
    constructor
    · intro h
      have h1 : mapPt p hp g.1 = L.one _ := by rw [← hπval g, h]; rfl
      exact ((hK_points _ _).mp ((p_ker _ _).mp h1)).2
    · intro h
      apply Subtype.ext
      rw [hπval]
      exact (p_ker _ _).mpr ((hK_points _ _).mpr ⟨g.2, h⟩)

  obtain ⟨eC, heC⟩ := hCt_points
  let eG : Additive ↥Gs ≃+ ZMod (N * ℓ) × ZMod (N * ℓ) :=
    AddEquiv.symm
      { toFun := fun x => Additive.ofMul (⟨(eC x).1, (eC x).2⟩ : ↥Gs)
        invFun := fun y => eC.symm ⟨(Additive.toMul y).1, (Additive.toMul y).2⟩
        left_inv := fun x => by simp
        right_inv := fun y => by simp
        map_add' := fun x y => by
          apply Additive.toMul.injective
          apply Subtype.ext
          show (eC (x + y)).1 = E₀.L.mul _ (eC x).1 (eC y).1
          exact heC x y }
  let πa : Additive ↥Gs →+ Additive ↥Hs := MonoidHom.toAdditive π
  have hπa_surj : Function.Surjective πa := hπsurj
  have hπa_ker : ∀ g : Additive ↥Gs, πa g = 0 ↔ ℓ • g = 0 := by
    intro g
    show π (Additive.toMul g) = 1 ↔ (Additive.toMul g) ^ ℓ = 1
    rw [hπker, ← OneMemClass.coe_eq_one (x := Additive.toMul g ^ ℓ), Subgroup.coe_pow]
  obtain ⟨eH⟩ := QLBook21.nonempty_addEquiv_of_ker_eq_torsion N ℓ hℓ eG πa hπa_surj hπa_ker
  refine ⟨⟨fun x => ⟨(Additive.toMul (eH.symm x)).1, (Additive.toMul (eH.symm x)).2⟩,
    fun Q => eH (Additive.ofMul ⟨Q.1, Q.2⟩), fun x => by simp, fun Q => by simp⟩, ?_⟩
  intro x y
  show (Additive.toMul (eH.symm (x + y)) : ↥Hs).1 = L.mul _ (Additive.toMul (eH.symm x) : ↥Hs).1 (Additive.toMul (eH.symm y) : ↥Hs).1
  rw [map_add]
  rfl

theorem exists_point_comp_eq_of_geomPoint
    (k : Type) [Field k] [IsAlgClosed k] {A C : Scheme.{0}} (f : A ⟶ Spec (CommRingCat.of k)) (lev : C ⟶ A)
    [IsReduced C] [IsFinite (lev ≫ f)]
    (k' : Type) [Field k'] [IsAlgClosed k'] (sk : k →+* k') (Q : SchemeHomOver (geomPoint k' sk) f) (hQ : FactorsThrough lev Q) :
    ∃ Q₀ : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) f, FactorsThrough lev Q₀ ∧ geomPoint k' sk ≫ Q₀.1 = Q.1 := by
  obtain ⟨z, hz⟩ := hQ
  have hz' : z ≫ (lev ≫ f) = Spec.map (CommRingCat.ofHom sk) := by
    rw [← Category.assoc, hz]; exact Q.2
  obtain ⟨⟨p, hp⟩, hpz⟩ := (QLpts.bijective_specMap_comp (lev ≫ f) k' sk).2 ⟨z, hz'⟩
  refine ⟨⟨p ≫ lev, by rw [Category.assoc, hp]⟩, ⟨p, rfl⟩, ?_⟩
  have := congrArg Subtype.val hpz
  show geomPoint k' sk ≫ p ≫ lev = Q.1
  rw [← hz, ← Category.assoc]
  exact congrArg (· ≫ lev) this

end QL
p2m_reactivate "P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_exists_withExtraLevel_isLevelIsogeny_of_levelLift.QLBook21"

theorem solution
    {q q' : ℕ} [Fact q.Prime] [Fact q'.Prime] (hqq' : q' ≠ q)
    {a b : ℚ} (hB : IsIndefiniteRamifiedExactlyAt a b q q')
    (Λ : Submodule ℤ ℍ[ℚ, a, b]) (hΛ : IsMaximalOrder Λ) {N : ℕ} [NeZero N]
    (ℓ : ℕ) [Fact ℓ.Prime] (hℓq : ℓ ≠ q) (hℓq' : ℓ ≠ q')
    (k : Type) [Field k] [IsAlgClosed k] (hℓk : (ℓ : k) ≠ 0) (hNk : (N : k) ≠ 0)
    (E₀ : FakeEllipticCurve Λ N k)
    (Ct : Scheme.{0}) (levt : Ct ⟶ E₀.A) (K₀ : Scheme.{0}) (levK : K₀ ⟶ E₀.A)
    (hCt_closed : IsClosedImmersion levt)
    (hCt_finite : IsFinite (levt ≫ E₀.f))
    (hCt_flat : Flat (levt ≫ E₀.f))
    (hCt_fp : LocallyOfFinitePresentation (levt ≫ E₀.f))
    (hCt_one : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of k)), FactorsThrough levt (E₀.L.one t))
    (hCt_sub : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of k)) (P Q : SchemeHomOver t E₀.f),
        FactorsThrough levt P → FactorsThrough levt Q →
          FactorsThrough levt (E₀.L.mul t P Q) ∧ FactorsThrough levt (E₀.L.inv t P))
    (hCt_stable : ∀ (x : ↥Λ) {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of k)) (P : SchemeHomOver t E₀.f),
        FactorsThrough levt P → FactorsThrough levt (pushPt (E₀.act x) (E₀.act_over x) P))
    (hCt_torsion : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of k)) (P : SchemeHomOver t E₀.f),
        FactorsThrough levt P → nsmulPt E₀.L t (N * ℓ) P = E₀.L.one t)
    (hCt_lev : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of k)) (P : SchemeHomOver t E₀.f),
        FactorsThrough levt P → FactorsThrough E₀.lev (nsmulPt E₀.L t ℓ P))
    (hCt_points : ∃ e : ZMod (N * ℓ) × ZMod (N * ℓ) ≃ {P : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) E₀.f // FactorsThrough levt P},
        ∀ x y : ZMod (N * ℓ) × ZMod (N * ℓ),
          (e (x + y) : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) E₀.f) = E₀.L.mul (𝟙 (Spec (CommRingCat.of k))) (e x) (e y))
    (hK_closed : IsClosedImmersion levK)
    (hK_finite : IsFinite (levK ≫ E₀.f))
    (hK_flat : Flat (levK ≫ E₀.f))
    (hK_fp : LocallyOfFinitePresentation (levK ≫ E₀.f))
    (hK_rank : ∀ s : ↥(Spec (CommRingCat.of k)), (levK ≫ E₀.f).finrank s = ℓ ^ 2)
    (hK_one : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of k)), FactorsThrough levK (E₀.L.one t))
    (hK_sub : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of k)) (P Q : SchemeHomOver t E₀.f),
        FactorsThrough levK P → FactorsThrough levK Q →
          FactorsThrough levK (E₀.L.mul t P Q) ∧ FactorsThrough levK (E₀.L.inv t P))
    (hK_stable : ∀ (x : ↥Λ) {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of k)) (P : SchemeHomOver t E₀.f),
        FactorsThrough levK P → FactorsThrough levK (pushPt (E₀.act x) (E₀.act_over x) P))
    (hK_points : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of k)) (P : SchemeHomOver t E₀.f),
        FactorsThrough levK P ↔ (FactorsThrough levt P ∧ nsmulPt E₀.L t ℓ P = E₀.L.one t)) :
    ∃ u : FakeEllipticCurve.WithExtraLevel Λ N ℓ k, FakeEllipticCurve.IsLevelIsogeny ℓ u E₀ := by
  have hord : IsOrder Λ := hΛ.1
  have hℓp : ℓ.Prime := Fact.out

  obtain ⟨A, f, L, act, hact, p, hp, ψ, hψ, hcomm, hbundle, hdim, act_hom, act_one, act_mul, act_add, act_trace,
      p_hom, p_act, p_fin, p_flat, p_lfp, p_surj, p_et, p_rank, p_ker, ψ_hom, ψ_act, hψp, hpψ, huniv⟩ :=
    FakeEllipticCurve.exists_quotient_core_of_isAlgClosed k E₀ hord ℓ hℓk K₀ levK hK_closed hK_finite hK_flat hK_fp hK_one hK_sub
      hK_stable (fun t P h => ((hK_points t P).mp h).2)
  haveI : IsProper f := hbundle.proper
  haveI : IsProper E₀.f := E₀.bundle.proper
  have hA_sep : IsSeparated f := inferInstance
  have hA_lft : LocallyOfFiniteType f := inferInstance

  let idA₀ : SchemeHomOver E₀.f E₀.f := ⟨𝟙 E₀.A, Category.id_comp _⟩
  have hm_over : ∀ n : ℕ, (nsmulPt E₀.L E₀.f n idA₀).1 ≫ E₀.f = E₀.f := fun n => (nsmulPt E₀.L E₀.f n idA₀).2
  have hm_pt : ∀ (n : ℕ) {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of k)) (P : SchemeHomOver t E₀.f),
      mapPt (nsmulPt E₀.L E₀.f n idA₀).1 (hm_over n) P = nsmulPt E₀.L t n P := by
    intro n T t P
    exact Subtype.ext (QL.nsmulPt_coe E₀.L t n P).symm
  have hm_hom : ∀ (n : ℕ) {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of k)) (P Q : SchemeHomOver t E₀.f),
      mapPt (nsmulPt E₀.L E₀.f n idA₀).1 (hm_over n) (E₀.L.mul t P Q) =
        E₀.L.mul t (mapPt (nsmulPt E₀.L E₀.f n idA₀).1 (hm_over n) P) (mapPt (nsmulPt E₀.L E₀.f n idA₀).1 (hm_over n) Q) := by
    intro n T t P Q
    rw [hm_pt, hm_pt, hm_pt]
    exact QL.nsmulPt_mul E₀.L t E₀.comm n P Q
  have hm_id : ∀ (n : ℕ) {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of k)) (P : SchemeHomOver t E₀.f),
      mapPt (𝟙 E₀.A) (Category.id_comp _) (mapPt (nsmulPt E₀.L E₀.f n idA₀).1 (hm_over n) P) = nsmulPt E₀.L t n P := by
    intro n T t P
    rw [← hm_pt n t P]
    exact Subtype.ext (Category.comp_id _)

  have hCt_red : IsReduced Ct := by
    haveI := hCt_closed
    exact CerednikDrinfeld.QM.isReduced_of_mapPt_mapPt_eq_nsmulPt_of_natCast_ne_zero E₀.L E₀.comm E₀.L
      (nsmulPt E₀.L E₀.f (N * ℓ) idA₀).1 (hm_over _) (hm_hom _) (𝟙 E₀.A) (Category.id_comp _) (N * ℓ)
      (by push_cast; exact mul_ne_zero hNk hℓk) (hm_id _) levt (fun t P h => by rw [hm_pt]; exact hCt_torsion t P h)
  obtain ⟨C, lev, lev_closed, lev_fin, lev_flat, lev_fp, lev_red, lev_one, lev_sub, lev_img, lev_pts, lev_rank, lev_tors,
      lev_equiv⟩ :=
    GoodReductionJacobian.RelativeGroupLaw.exists_image_closedSubgroup_of_isFinite E₀.L L hA_sep hA_lft p hp p_hom p_fin p_flat
      p_lfp Ct levt hCt_closed hCt_finite hCt_red hCt_one hCt_sub

  let E : FakeEllipticCurve Λ N k :=
    { A := A, f := f, L := L, comm := hcomm, bundle := hbundle, dim_fibre := hdim
      act := act, act_over := hact, act_hom := act_hom, act_one := act_one, act_mul := act_mul, act_add := act_add
      act_trace := act_trace
      C := C, lev := lev, lev_closed := lev_closed, lev_sub := lev_sub, lev_one := lev_one
      lev_torsion := lev_tors N (by
        intro T t P hP
        rw [← QL.mapPt_nsmulPt E₀.L L p hp p_hom, p_ker, hK_points]
        refine ⟨?_, ?_⟩
        ·
          have hcl : ∀ m : ℕ, FactorsThrough levt (nsmulPt E₀.L t m P) := by
            intro m
            induction m with
            | zero => exact hCt_one t
            | succ n ih => exact (hCt_sub t _ _ ih hP).1
          exact hcl N
        · rw [QL.nsmulPt_nsmulPt]; exact hCt_torsion t P hP)
      lev_stable := by
        intro x T t P hP
        exact lev_equiv (E₀.act x) (E₀.act_over x) (act x) (hact x) (p_act x) (fun t P h => hCt_stable x t P h) t P hP
      lev_finite := lev_fin, lev_flat := lev_flat, lev_finitePresentation := lev_fp
      lev_rank := by
        intro s
        haveI := p_fin; haveI := p_surj
        obtain ⟨eN, -⟩ := QL.exists_zmod_prod_equiv_imagePoints k ℓ hℓp.ne_zero E₀ L hcomm p hp p_hom levt levK hCt_one hCt_sub
          hCt_points hK_points p_ker lev lev_one lev_sub lev_img lev_pts
        rw [lev_rank s, ← Nat.card_congr eN, Nat.card_prod, Nat.card_zmod, pow_two]
      lev_fibre := by
        intro k' _ _ sk hNk'
        haveI := p_fin; haveI := p_surj
        haveI := lev_red; haveI := lev_fin
        obtain ⟨eN, heN⟩ := QL.exists_zmod_prod_equiv_imagePoints k ℓ hℓp.ne_zero E₀ L hcomm p hp p_hom levt levK hCt_one hCt_sub
          hCt_points hK_points p_ker lev lev_one lev_sub lev_img lev_pts

        let bc : {Q : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) f // FactorsThrough lev Q} →
            {Q : SchemeHomOver (geomPoint k' sk) f // FactorsThrough lev Q} := fun Q =>
          ⟨⟨geomPoint k' sk ≫ Q.1.1, by rw [Category.assoc, Q.1.2, Category.comp_id]⟩,
            by obtain ⟨Q₀, hQ₀⟩ := Q.2; exact ⟨geomPoint k' sk ≫ Q₀, by rw [Category.assoc, hQ₀]⟩⟩
        have bc_inj : Function.Injective bc := by
          intro Q Q' h
          apply Subtype.ext; apply Subtype.ext
          have h1 := congrArg (fun x => x.1.1) h
          haveI : Epi (geomPoint k' sk) := by
            show Epi (Spec.map (CommRingCat.ofHom sk))
            infer_instance
          exact (cancel_epi (geomPoint k' sk)).mp h1
        have bc_surj : Function.Surjective bc := by
          intro Q
          obtain ⟨Q₀, hQ₀, h⟩ := QL.exists_point_comp_eq_of_geomPoint k f lev k' sk Q.1 Q.2
          exact ⟨⟨Q₀, hQ₀⟩, Subtype.ext (Subtype.ext h)⟩
        have bc_mul : ∀ Q Q' : {Q : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) f // FactorsThrough lev Q},
            (bc ⟨⟨(L.mul _ Q.1 Q'.1).1, (L.mul _ Q.1 Q'.1).2⟩, (lev_sub _ _ _ Q.2 Q'.2).1⟩).1 = L.mul _ (bc Q).1 (bc Q').1 := by
          intro Q Q'
          have hnat := L.mul_natural (𝟙 _) (geomPoint k' sk) (geomPoint k' sk) (Category.comp_id _) Q.1 Q'.1
          exact hnat
        refine ⟨eN.trans (Equiv.ofBijective bc ⟨bc_inj, bc_surj⟩), ?_⟩
        intro x y
        show (bc (eN (x + y))).1 = L.mul _ (bc (eN x)).1 (bc (eN y)).1
        rw [← bc_mul]
        congr 2
        apply Subtype.ext
        exact heN x y
    }

  have hℓmem : ((ℓ : ℚ) : ℍ[ℚ, a, b]) ∈ Λ := QL.natCast_mem hord ℓ

  have hψp_eq : ψ ≫ p = E.act ⟨((ℓ : ℚ) : ℍ[ℚ, a, b]), hℓmem⟩ := by
    apply QL.eq_of_mapPt_id (f := f) (g := f) _ _ (by rw [Category.assoc, hp, hψ]) (E.act_over _)
    show mapPt (ψ ≫ p) _ (⟨𝟙 A, Category.id_comp f⟩ : SchemeHomOver f f) = pushPt (E.act ⟨_, hℓmem⟩) (E.act_over _) ⟨𝟙 A, _⟩
    rw [QL.pushPt_act_natCast hord E ℓ, ← hpψ]
    rfl
  have hpψ_eq : p ≫ ψ = E₀.act ⟨((ℓ : ℚ) : ℍ[ℚ, a, b]), hℓmem⟩ := by
    apply QL.eq_of_mapPt_id (f := E₀.f) (g := E₀.f) _ _ (by rw [Category.assoc, hψ, hp]) (E₀.act_over _)
    show mapPt (p ≫ ψ) _ idA₀ = pushPt (E₀.act ⟨_, hℓmem⟩) (E₀.act_over _) idA₀
    rw [QL.pushPt_act_natCast hord E₀ ℓ, ← hψp]
    rfl

  have hψ_et : Etale ψ := by
    haveI : SmoothOfRelativeDimension 2 f := FakeEllipticCurve.smoothOfRelativeDimension_two k E
    have h1 : Etale (E.L.schemeNsmul ℓ) :=
      GoodReductionJacobian.RelativeGroupLaw.etale_schemeNsmul_of_isUnit_of_smoothOfRelativeDimension E.L (fun t x y => hcomm t x y) 2 ℓ
        (isUnit_iff_ne_zero.mpr hℓk)
    have h2 : E.act ⟨((ℓ : ℚ) : ℍ[ℚ, a, b]), hℓmem⟩ = E.L.schemeNsmul ℓ := by
      apply QL.eq_of_mapPt_id (f := f) (g := f) _ _ (E.act_over _) (E.L.schemeNsmul_over ℓ)
      show pushPt (E.act ⟨_, hℓmem⟩) (E.act_over _) ⟨𝟙 A, Category.id_comp f⟩ = _
      rw [QL.pushPt_act_natCast hord E ℓ]
      apply Subtype.ext
      rw [QL.nsmulPt_coe]
      show _ = 𝟙 A ≫ E.L.schemeNsmul ℓ
      rw [Category.id_comp]
      show (⟨𝟙 A, Category.id_comp f⟩ : SchemeHomOver f f).1 ≫ _ = _
      rw [Category.id_comp]

      show (nsmulPt E.L f ℓ ⟨𝟙 A, _⟩).1 = (E.L.nsmul f ℓ GoodReductionJacobian.RelativeGroupLaw.idPoint).1
      congr 1
      exact (QL.nsmul_eq_nsmulPt E.L f ℓ _).symm
    haveI : Etale (ψ ≫ p) := by rw [hψp_eq, h2]; exact h1
    haveI : Etale p := p_et
    exact Etale.of_comp ψ p

  let one₀ : Spec (CommRingCat.of k) ⟶ E₀.A := (E₀.L.one (𝟙 (Spec (CommRingCat.of k)))).1
  let gB : CategoryTheory.Limits.pullback ψ one₀ ⟶ Spec (CommRingCat.of k) := CategoryTheory.Limits.pullback.snd ψ one₀
  let iB : SchemeHomOver gB f := ⟨CategoryTheory.Limits.pullback.fst ψ one₀, by
    show CategoryTheory.Limits.pullback.fst ψ one₀ ≫ f = CategoryTheory.Limits.pullback.snd ψ one₀
    rw [← hψ, ← Category.assoc, CategoryTheory.Limits.pullback.condition, Category.assoc, (E₀.L.one _).2, Category.comp_id]⟩
  have hBpts : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of k)) (P : SchemeHomOver t f),
      FactorsThrough iB.1 P ↔ mapPt ψ hψ P = E₀.L.one t := fun t P => QL.factorsThrough_ker_iff E₀.L ψ hψ t P
  haveI hiB_ci : IsClosedImmersion iB.1 := by
    haveI : IsClosedImmersion one₀ := by
      have h1 : IsClosedImmersion (one₀ ≫ E₀.f) := by
        show IsClosedImmersion ((E₀.L.one _).1 ≫ E₀.f)
        rw [(E₀.L.one _).2]; infer_instance
      exact IsClosedImmersion.of_comp _ E₀.f
    show IsClosedImmersion (CategoryTheory.Limits.pullback.fst ψ one₀)
    infer_instance
  have hget : Etale gB := by haveI := hψ_et; show Etale (CategoryTheory.Limits.pullback.snd ψ one₀); infer_instance
  obtain ⟨hBred, -, hBfin'⟩ :=
    FakeEllipticCurve.isReduced_pullback_one_of_natCast_ne_zero k E E₀ ψ hψ ψ_hom ψ_act p hp ℓ hℓk hpψ hψp
  have hBfin : IsFinite gB := by
    have : gB = iB.1 ≫ f := iB.2.symm
    rw [this]; exact hBfin'

  obtain ⟨LB, -, hLBhom, -⟩ :=
    GoodReductionJacobian.RelativeGroupLaw.exists_relativeGroupLaw_comp_eq_mul_and_forall_exists_comp_eq_of_isClosedImmersion
      E.L E.comm gB iB (by
        intro T s
        have lift : ∀ w : SchemeHomOver s f, mapPt ψ hψ w = E₀.L.one s →
            ∃ z : SchemeHomOver s gB, NeronModelInfra.schemeHomOverComp z iB = w := by
          intro w hw
          obtain ⟨z₀, hz₀⟩ := (hBpts s w).mpr hw
          refine ⟨⟨z₀, ?_⟩, Subtype.ext hz₀⟩
          show z₀ ≫ gB = s
          rw [← iB.2, ← Category.assoc, hz₀]; exact w.2
        refine ⟨lift _ (QL.mapPt_one E.L E₀.L ψ hψ ψ_hom s), fun x y => lift _ ?_, fun x => lift _ ?_⟩
        · rw [ψ_hom, (hBpts s _).mp ⟨x.1, rfl⟩, (hBpts s _).mp ⟨y.1, rfl⟩, E₀.L.one_mul]
        · rw [QL.mapPt_inv E.L E₀.L ψ hψ ψ_hom, (hBpts s _).mp ⟨x.1, rfl⟩]
          letI := E₀.L.pointGroup s
          exact inv_one)

  let Sk : Set (SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) f) := {P | mapPt ψ hψ P = E₀.L.one _}
  let eB : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) gB ≃ ↥Sk :=
    { toFun := fun y => ⟨NeronModelInfra.schemeHomOverComp y iB, (hBpts _ _).mp ⟨y.1, rfl⟩⟩
      invFun := fun P => ⟨CategoryTheory.Limits.pullback.lift P.1.1 (𝟙 _) (by
          have := congrArg Subtype.val P.2
          rw [QL.one_coe] at this
          exact this), CategoryTheory.Limits.pullback.lift_snd _ _ _⟩
      left_inv := fun y => by
        apply Subtype.ext
        apply CategoryTheory.Limits.pullback.hom_ext
        · rw [CategoryTheory.Limits.pullback.lift_fst]; rfl
        · rw [CategoryTheory.Limits.pullback.lift_snd]; exact y.2.symm
      right_inv := fun P => Subtype.ext (Subtype.ext (CategoryTheory.Limits.pullback.lift_fst _ _ _)) }
  have heB : ∀ y, ((eB y : ↥Sk) : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) f) = NeronModelInfra.schemeHomOverComp y iB :=
    fun y => rfl
  have hSk : ∃ e : ZMod ℓ × ZMod ℓ ≃ ↥Sk, ∀ x y : ZMod ℓ × ZMod ℓ,
      ((e (x + y) : ↥Sk) : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) f) = E.L.mul _ (e x) (e y) := by
    haveI := p_fin
    haveI := p_surj
    exact QL.exists_zmod_prod_equiv_kerPoints k ℓ hℓk E₀ L hcomm p hp p_hom ψ hψ ψ_hom hψp hpψ levt levK hCt_points
      hK_points p_ker
  obtain ⟨eS, heS⟩ := hSk
  have hstab : ∀ (m : ↥Λ) (P : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) f), P ∈ Sk →
      pushPt (E.act m) (E.act_over m) P ∈ Sk := by
    intro m P hP
    show mapPt ψ hψ (pushPt (act m) (hact m) P) = E₀.L.one _
    have : mapPt ψ hψ (pushPt (act m) (hact m) P) = pushPt (E₀.act m) (E₀.act_over m) (mapPt ψ hψ P) :=
      Subtype.ext (by show (P.1 ≫ act m) ≫ ψ = (P.1 ≫ ψ) ≫ E₀.act m; rw [Category.assoc, ψ_act, Category.assoc])
    rw [this, show mapPt ψ hψ P = E₀.L.one _ from hP]
    exact QL.mapPt_one E₀.L E₀.L (E₀.act m) (E₀.act_over m) (E₀.act_hom m) _
  have hdisj : ∀ P : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) f, P ∈ Sk → FactorsThrough E.lev P →
      P = E.L.one _ := by
    intro P hP hPC

    let P₁ : SchemeHomOver (geomPoint k (RingHom.id k)) f := QLBook21.castPt (QLBook21.geomPoint_id k).symm P
    have hP₁ : FactorsThrough lev P₁ := hPC
    obtain ⟨P₀, hP₀t, hP₀⟩ := (lev_pts k (RingHom.id k) P₁).mp hP₁
    have hker : mapPt ψ hψ (mapPt p hp P₀) = E₀.L.one _ := by
      rw [hP₀]
      apply Subtype.ext
      have := congrArg Subtype.val hP
      rw [QL.one_coe] at this ⊢
      first | simpa [QLBook21.geomPoint_id] using this | (simp [QLBook21.geomPoint_id] at this ⊢; exact this) | exact this
    have h1 := QLBook21.mapPt_eq_one_of_levelLift_of_mapPt_mapPt_eq_one E₀.L L p hp levt levK ψ hψ ℓ hψp hK_points p_ker
      _ P₀ hP₀t hker
    rw [hP₀] at h1
    apply Subtype.ext
    have := congrArg Subtype.val h1
    rw [QL.one_coe] at this ⊢
    first | simpa [QLBook21.geomPoint_id] using this | (simp [QLBook21.geomPoint_id] at this ⊢; exact this) | exact this
  obtain ⟨K, hKpts, -⟩ := FakeEllipticCurve.exists_extraLevel_of_isClosedImmersion_of_equiv_points Λ ℓ k hℓk E _ gB LB iB
    hBred hBfin hget hiB_ci hLBhom Sk eB heB eS heS hstab hdisj

  refine ⟨⟨E, K⟩, ψ, hψ, p, hp, ψ_hom, p_hom, ?_, ?_, ?_, ?_, ?_⟩
  · intro x; exact ψ_act x
  · intro x; exact p_act x
  · intro hℓ'
    have e1 : (⟨((ℓ : ℚ) : ℍ[ℚ, a, b]), hℓ'⟩ : ↥Λ) = ⟨((ℓ : ℚ) : ℍ[ℚ, a, b]), hℓmem⟩ := rfl
    rw [e1]
    exact ⟨hψp_eq, hpψ_eq⟩
  ·
    intro T t P
    rw [hKpts, hBpts]
  ·
    intro T t P hP
    haveI := E₀.lev_closed
    haveI := lev_red
    haveI := lev_fin
    exact QLBook21.factorsThrough_lev₀_mapPt_of_image E₀.L p hp levt ψ hψ ℓ hψp E₀.lev hCt_lev lev lev_pts t P hP

end S_CerednikDrinfeld_QM_FakeEllipticCurve_exists_withExtraLevel_isLevelIsogeny_of_levelLift
end P2MW
export P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_exists_withExtraLevel_isLevelIsogeny_of_levelLift (solution)
