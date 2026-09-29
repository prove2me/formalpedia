-- Prove2me | solution 1 for CerednikDrinfeld.QM.ModuliTowerWitness.tower_laws_of_two_mul_dvd
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.141142+00:00
-- url     : https://prove2.me/submissions/4732136b-284d-5252-8075-9575921300dc

import Definitions.Def_CerednikDrinfeld_QMModuli
import Definitions.Def_CerednikDrinfeld_QMModuliProps
import Definitions.Def_CerednikDrinfeld_HeckeTower
import Definitions.Def_AlgebraicCurve_CurveModel
import Definitions.Def_AlgebraicCurve_Correspondence
import Definitions.Def_CerednikDrinfeld_QMModuliTower
import Definitions.Def_CerednikDrinfeld_QMModuliTowerD
import Definitions.Def_AlgebraicCurve_BaseChangeGalois
import Theorems.Thm_AlgebraicCurve_CurveModel_place_eq_of_pointEquivPlace_symm_comp_eq
import Theorems.Thm_QuaternionAlgebra_IsOrder_exists_intCast_eq_nrd_and_exists_intCast_eq_trd
import Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_exists_unique_comp_eq_of_forall_mapPt_eq_one
import Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_factorsThrough_lev_iff_exists_mapPt_eq_of_coprime
import Theorems.Thm_QuaternionAlgebra_IsMaximalOrder_span_mul_ramifiedPrime_eq_of_isIndefiniteRamifiedExactlyAt
import Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_iso_of_isAtkinLehnerQuotient_comm
import Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_isAtkinLehnerQuotient_of_isPullback
import Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_pushPt_act_natCast_eq_nsmulPt
import Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_WithExtraLevel_iso_of_isAtkinLehnerQuotient_comp
import Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_WithExtraLevel_iso_of_isAtkinLehnerQuotient_comm
import Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_WithExtraLevel_isAtkinLehnerQuotient_of_isPullback
import Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_WithExtraLevel_isAtkinLehnerQuotient_of_iso_of_iso
import Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_WithExtraLevel_iso_of_isAtkinLehnerQuotient_of_isAtkinLehnerQuotient
import Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_factorsThrough_lev_of_exists_comp_eq_of_isPullback
import Theorems.Thm_AlgebraicGeometry_isIso_of_isClosedImmersion_of_finrank_comp_eq
import Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_exists_extraLevel_isLevelIsogeny_of_isPullback
import Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_isLevelIsogeny_of_iso_of_isLevelIsogeny
import Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_iso_of_isLevelIsogeny_of_iso_of_isOrder
import Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_iso_of_isPullback_of_isPullback
import Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_isAtkinLehnerQuotient_of_isLevelIsogeny_of_isLevelIsogeny
import Theorems.Thm_AlgebraicCurve_SemilinearAut_eq_of_forall_smul_place_eq
import Theorems.Thm_AlgebraicCurve_algHom_eq_of_forall_restrictAlong_eq_of_charZero
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_QM_ModuliTowerWitness_tower_laws_of_two_mul_dvd
p2m_attr_erase "instance" "GoodReductionJacobian.RelativeGroupLaw.isIso_endKerStr_schemeHomOverId AlgebraicGeometry.Scheme.PresheafOfModules.symmetricCategory SheafOfModules.instFaithfulRingSheafPModToPMod SheafOfModules.symmetricCategory AlgebraicGeometry.Scheme.PresheafOfModules.monoidalCategory AlgebraicGeometry.Scheme.PresheafOfModules.monoidalClosed SheafOfModules.instFullRingSheafPModToPMod SheafOfModules.monoidalCategory AlgebraicGeometry.Scheme.Modules.symmetricCategory SheafOfModules.monoidalClosed SheafOfModules.instIsLocalizationPModRingSheafSheafifyFunctorPresheafW SheafOfModules.sheafifyFunctor_monoidal AlgebraicGeometry.Scheme.Modules.monoidalClosed AlgebraicGeometry.instMonoidalPresheafOfModulesModulesSheafify AlgebraicGeometry.Scheme.Modules.monoidalCategory PresheafOfModules.instMonoidalClosed PresheafOfModules.InternalHom.instModuleCarrierObjOppositeCommRingCatSubtypePiFamilyMemAddSubgroupNaturalFamilies PresheafOfModules.InternalHom.instModuleCarrierObjOppositeRingCatCompCommRingCatForget₂RingHomCarrierCarrierAbPresheaf PresheafOfModules.InternalHom.instSMulCarrierObjOppositeCommRingCatSubtypePiFamilyMemAddSubgroupNaturalFamilies AlgebraicGeometry.Scheme.Hom.opensMapFinal AlgebraicGeometry.RelPicard.RigidifiedLineBundle.setoid AlgebraicGeometry.RelPicard.RigidifiedLineBundle.instInhabited AlgebraicGeometry.OModulePresheaf.isScalarTower AlgebraicGeometry.Scheme.OrderedAffineCover.instLinearOrder AlgebraicGeometry.OModulePresheaf.module AlgebraicGeometry.Scheme.OrderedAffineCover.instFintype AlgebraicGeometry.Scheme.OrderedAffineCover.instFintypeIdx AlgebraicGeometry.OModulePresheaf.addCommGroup AlgebraicGeometry.Scheme.OrderedAffineCover.instDecidableEqIdx AlgebraicGeometry.OModulePresheaf.moduleSections TwoChartCech.Sections.M0_moduleA TwoChartCech.Sections.M1_module TwoChartCech.Cover.A01_algebra TwoChartCech.Cover.A0_algebra TwoChartCech.Cover.A1_commRing TwoChartCech.Cover.A1_algebra TwoChartCech.Sections.M01_module TwoChartCech.Sections.M0_addCommGroup TwoChartCech.Sections.M0_tower TwoChartCech.Sections.M01_addCommGroup"
p2m_attr_erase "instance" "TwoChartCech.Cover.A0_commRing TwoChartCech.Sections.M1_tower TwoChartCech.Sections.M01_moduleA TwoChartCech.Sections.M0_module TwoChartCech.Sections.M1_moduleA TwoChartCech.Sections.M1_addCommGroup TwoChartCech.Cover.A01_commRing TwoChartCech.Sections.M01_tower CoherentBaseChange.TwoTermComplex.C0_module CoherentBaseChange.TwoTermComplex.C0_addCommGroup CoherentBaseChange.TwoTermComplex.C1_module CoherentBaseChange.TwoTermComplex.C1_addCommGroup CoherentBaseChange.TwoTermComplex.C0_free CoherentBaseChange.TwoTermComplex.C1_finite CoherentBaseChange.TwoTermComplex.C0_finite CoherentBaseChange.TwoTermComplex.C1_free AlgebraicGeometry.Scheme.Modules.preservesBinaryProducts_opensMap AlgebraicGeometry.Scheme.Modules.pullback_monoidal AlgebraicGeometry.Scheme.Modules.sheafify_isLocalization' AlgebraicGeometry.Scheme.Modules.preservesTerminal_opensMap AlgebraicGeometry.Scheme.Modules.pullback₀_monoidal AlgebraicGeometry.Scheme.Modules.preservesFiniteProducts_opensMap AlgebraicGeometry.Scheme.Modules.instLiftingPresheafOfModulesSheafifyPresheafWOpensCarrierCarrierCommRingCatGrothendieckTopologyObjFunctorOppositeIsSheafSheafCompPullback₀Pullback PresheafOfModules.PullbackMonoidal.pullback_monoidal PresheafOfModules.PullbackMonoidal.isIso_δ PresheafOfModules.pushforward_laxMonoidal PresheafOfModules.PullbackMonoidal.isIso_η PresheafOfModules.free_monoidal PresheafOfModules.restrictScalars_laxMonoidal PresheafOfModules.PullbackMonoidal.isIso_δ_gS PresheafOfModules.pullback_oplaxMonoidal PresheafOfModules.PullbackMonoidal.instPreservesColimitsOfSizeCompOppositeCommRingCatRingCatForget₂RingHomCarrierCarrierPb PresheafOfModules.pullback_monoidal' AlgebraicGeometry.SmoothOfRelativeDimension.fiberToSpecResidueField AlgebraicGeometry.SmoothOfRelativeDimension.pullback_snd AlgebraicGeometry.SmoothOfRelativeDimension.pullback_fst AlgebraicGeometry.SmoothOfRelativeDimension.smooth_one AlgebraicGeometry.SmoothProperCurve.isIntegral_pullback_Spec_field AlgebraicGeometry.IsProper.fiberToSpecResidueField AlgebraicGeometry.Scheme.LocalRepresentabilityULift.instIsLocallyInjectiveFunUliftYonedaGluedToSheaf"
p2m_attr_erase "instance" "AlgebraicGeometry.Scheme.LocalRepresentabilityULift.instIsLocallySurjectiveFunUliftYonedaGluedToSheafOfIsLocallySurjectiveZariskiTopologyDescFunctorOppositeType AlgebraicGeometry.Scheme.LocalRepresentabilityULift.instIsOpenImmersionToGlued AlgebraicGeometry.Scheme.LocalRepresentabilityULift.instIsIsoSheafZariskiTopologyTypeUliftYonedaGluedToSheaf AlgebraicGeometry.RelPicard.instIsOpenImmersionToGlued AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions PresheafOfModules.ExteriorPower.instModulePresheafAb AlgebraicGeometry.RelEffCartierDiv.subsingleton_of_degree_zero AlgebraicGeometry.RelEffCartierDiv.isIso_subschemeIota_snd_of_degree_one AlgebraicGeometry.isIso_ker_graphOver_subschemeIota_snd AlgebraicGeometry.isClosedImmersion_graphOver AlgebraicGeometry.FGSubalgebra.instIsDirectedLe AlgebraicGeometry.FGSubalgebra.instQuasiSeparatedSpaceCarrierCarrierCommRingCatObjOppositeSchemeSpecDiagram AlgebraicGeometry.FGSubalgebra.instIsCofilteredOpposite AlgebraicGeometry.FGSubalgebra.instIsAffineObjOppositeSchemeSpecDiagram AlgebraicGeometry.FGSubalgebra.instNonempty AlgebraicGeometry.FGSubalgebra.instNonemptySubtypeLeSubalgebraValFG AlgebraicGeometry.FGSubalgebra.instCompactSpaceCarrierCarrierCommRingCatObjOppositeSchemeSpecDiagram AlgebraicGeometry.FGSubalgebra.instIsDirectedSubtypeLeSubalgebraValFG AlgebraicGeometry.FGSubalgebra.instIsAffineHomMapOppositeSchemeSpecDiagram AlgebraicGeometry.FGSubalgebra.instIsFiltered AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instNeg AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instSMulInt AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instAddCommGroup AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instAdd AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instSub AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instModuleCarrierObjOppositeOpensCarrierCarrierCommRingCatPresheafOpOpensTop AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instSMulCarrierObjOppositeOpensCarrierCarrierCommRingCatPresheafOpOpensTop AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instSMulNat AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instZero AlgebraicCurve.instHasLocalResidue_of_hasCanonicalLocalResidueK AlgebraicCurve.instHasCanonicalLocalResidueK_of_hasCanonicalLocalResidueKStar AlgebraicCurve.Place.kw_ffgc_finiteDimensional_adicCompletion instAlgebraSubtypeMemValuationSubring_definitions"
p2m_attr_erase "instance" "AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersIntegersCompletion ModularCurve.KwF4gRRTate.instAlgebraKAdicCompletionIntegers AlgebraicCurve.Place.kw_ffgc_continuousSMul_adicCompletionComap AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersCompletionCompletion IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions AlgebraicCurve.instHasCanonicalLocalResidueK AlgebraicCurve.Place.instAlgebra_restrictResidueField AlgebraicCurve.Place.instIsScalarTower_restrictResidueField AlgebraicCurve.instHasLocalResidue AlgebraicCurve.HasSeparableResidue.of_perfectField_of_isCurveOver AlgebraicCurve.HasSeparableResidue.of_perfectField AlgebraicCurve.Place.instIsLocalHom_restrictSubringHom AlgebraicCurve.instHasCanonicalLocalResidueKStar ModularCurve.KwNo6Pin.isLocalRing_completion SheafOfModules.isIso_ihomModelToIhom AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instDecidableEqIdx AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instFintype AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instLinearOrder AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instFintypeIdx AlgebraicGeometry.OModulePresheaf.instSubsingletonObjZero AlgebraicGeometry.OModulePresheaf.Leray.relAltC_scalarTower AlgebraicGeometry.OModulePresheaf.Leray.ker_relAltd_modΓ AlgebraicGeometry.OModulePresheaf.Leray.relAltC_modΓ AlgebraicGeometry.OModulePresheaf.Leray.biC_abGrp AlgebraicGeometry.OModulePresheaf.Leray.relAltH_modΓ AlgebraicGeometry.OModulePresheaf.Leray.ker_relAltd_smul AlgebraicGeometry.OModulePresheaf.Leray.relAltH_scalarTower AlgebraicGeometry.OModulePresheaf.Leray.relAltH_smul AlgebraicGeometry.OModulePresheaf.Leray.biC_module DoubleComplex.instModuleE₂I DoubleComplex.Bounded.modR DoubleComplex.instModuleE₂II DoubleComplex.instAddCommGroupE₂II DoubleComplex.Bounded.abGrp DoubleComplex.instAddCommGroupE₂I"
p2m_attr_erase "instance" "AlgebraicGeometry.ChowDatum.hι_closed AlgebraicGeometry.ChowDatumProj.hιN_closed AlgebraicGeometry.ChowDatumProj.hp_proper AlgebraicGeometry.ChowDatum.hp_isoU AlgebraicGeometry.ChowDatum.hp_proper AlgebraicGeometry.ProjSpace.algebraAway AlgebraicGeometry.ProjSpace.instIsProperProdOverπ AlgebraicGeometry.ChowDatumProj.hp_isoU AlgebraicGeometry.ProjSpace.isProper_π AlgebraicGeometry.ProjSpace.finiteType_mvPolynomial ProjSpaceCech.GradedModule.H.module ProjSpaceCech.GradedModule.H.addCommGroup ProjSpaceCech.GradedModule.sec.instAdd ProjSpaceCech.GradedModule.sec.instNeg ProjSpaceCech.GradedModule.acg ProjSpaceCech.GradedModule.Frac.setoid ProjSpaceCech.GradedModule.modR ProjSpaceCech.GradedModule.sec.instModule ProjSpaceCech.GradedModule.sec.instAddCommGroup ProjSpaceCech.GradedModule.sec.instZero ProjSpaceCech.GradedModule.Presentation.fJ ProjSpaceCech.GradedModule.sec.instSMul ProjSpaceCech.Twist.H.module ProjSpaceCech.Idx.instFintype ProjSpaceCech.Twist.H.addCommGroup ProjSpaceCech.Idx.instDecidableEq ProjSpaceCech.Twist.Mon.instDecidableEq ProjSpaceCech.Twist.cochain.instAddCommGroup ProjSpaceCech.Twist.cochain.instModule AlgebraicGeometry.FGSubalgebra.tensorStage_directedSystem AlgebraicGeometry.RelEffCartierDiv.isClosedImmersion_subschemeι_resProdMap AlgebraicGeometry.RelEffCartierDiv.isOpenImmersion_resProdMap AlgebraicCurve.CurveModel.locallyOfFiniteType_gluedToBase AlgebraicCurve.CurveModel.isFractionRing_overlap AlgebraicCurve.CurveModel.isLocallyNoetherian_glued AlgebraicCurve.CurveModel.jacobsonSpace_glued AlgebraicCurve.CurveModel.isOpenImmersion_ι₀ AlgebraicCurve.CurveModel.isIntegral_glued AlgebraicCurve.CurveModel.quasiSeparated_gluedToBase AlgebraicCurve.CurveModel.compactSpace_glued"
p2m_attr_erase "instance" "AlgebraicCurve.CurveModel.isIntegral_adjoin_chartRing AlgebraicCurve.CurveModel.isFractionRing_overlap_functionField AlgebraicCurve.CurveModel.isProper_gluedToBase AlgebraicCurve.CurveModel.isOpenImmersion_ιU AlgebraicCurve.CurveModel.isOpenImmersion_f₀ AlgebraicCurve.CurveModel.isOpenImmersion_fInf AlgebraicCurve.CurveModel.isOpenImmersion_ιInf AlgebraicCurve.CurveModel.algebra_overlap_functionField AlgebraicCurve.CurveModel.quasiCompact_gluedToBase AlgebraicCurve.CurveModel.algebraAdjoin AlgebraicCurve.CurveModel.isDedekindDomain_chartRing AlgebraicCurve.CurveModel.isIntegralClosure AlgebraicCurve.CurveModel.finite_chartRing AlgebraicCurve.CurveModel.centre_isPrime AlgebraicCurve.CurveModel.isFractionRing_chartRing AlgebraicCurve.CurveModel.finiteType_chartRing AlgebraicCurve.CurveModel.isNoetherianRing_chartRing AlgebraicCurve.CurveModel.isScalarTower_base_adjoin AlgebraicCurve.CurveModel.isScalarTower_adjoin AlgebraicCurve.CurveModel.chartRing_finitePresentation instTopologicallyFGOfFiniteType AlgebraicGeometry.ProjSpace.twistObj.addCommGroup AlgebraicGeometry.ProjSpace.twistFam.module AlgebraicGeometry.ProjSpace.twistObj.module AlgebraicGeometry.ProjSpace.twistObj.moduleSections AlgebraicGeometry.ProjSpace.twistFam.addCommGroup kmfloorsGlue_int_three_isPrime kmfloorsGlue_int_bot_isPrime"
p2m_attr_erase "simp" "GoodReductionJacobian.relativeGroupLawOfGrpObj_inv GoodReductionJacobian.relativeGroupLawOfGrpObj_mul GoodReductionJacobian.overHomEquivSchemeHomOver_apply_coe GoodReductionJacobian.relativeGroupLawOfGrpObj_one GoodReductionJacobian.overHomEquivSchemeHomOver_symm_apply_left NeronModelInfra.schemeHomOverNpow_succ NeronModelInfra.schemeHomOverNpow_zero GoodReductionJacobian.RelativeGroupLaw.nsmul_zero GoodReductionJacobian.RelativeGroupLaw.mem_torsionSubset GoodReductionJacobian.RelativeGroupLaw.nsmul_succ NeronModelInfra.NeronModelPropertyBundle.endExtensionEquiv_symm_restrict NeronModelInfra.schemeHomOverComp_id_left NeronModelInfra.schemeHomOverComp_id_right NeronModelInfra.schemeHomOverId_coe NeronModelInfra.NeronModelPropertyBundle.endExtensionEquiv_apply NeronModelInfra.NeronModelPropertyBundle.restrict_endExtensionEquiv_symm NeronModelInfra.schemeHomOverComp_coe SheafOfModules.tensorUnit_eq AlgebraicGeometry.Scheme.Modules.tensorUnit_eq PresheafOfModules.InternalHom.presheaf_map_apply PresheafOfModules.InternalHom.curryFamily_app PresheafOfModules.InternalHom.add_app PresheafOfModules.InternalHom.smul_app PresheafOfModules.InternalHom.zero_app PresheafOfModules.ihomObj_map_val PresheafOfModules.ihomFunctor_map PresheafOfModules.InternalHom.restrict_app PresheafOfModules.InternalHom.postcomp_app PresheafOfModules.InternalHom.neg_app PresheafOfModules.curry'_app_val PresheafOfModules.InternalHom.presheaf_obj PresheafOfModules.ihomFunctor_obj PresheafOfModules.ihomObj_obj PresheafOfModules.InternalHom.sub_app PresheafOfModules.ihomMap_app_val AlgebraicGeometry.Scheme.Modules.tensorPow_zero AlgebraicGeometry.Scheme.Modules.tensorPow_succ AlgebraicGeometry.RelPicard.RigidifiedLineBundle.mk.sizeOf_spec AlgebraicGeometry.RelPicard.RigidifiedLineBundle.mk.injEq AlgebraicGeometry.Scheme.OrderedAffineCover.mk.injEq"
p2m_attr_erase "simp" "AlgebraicGeometry.OModulePresheaf.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCover.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.mk.injEq AlgebraicGeometry.Scheme.TwoAffineOpenCover.mk.injEq AlgebraicGeometry.Scheme.TwoAffineOpenCover.mk.sizeOf_spec AlgebraicGeometry.Scheme.TwoAffineOpenCover.pullback_U1 AlgebraicGeometry.Scheme.TwoAffineOpenCover.pullback_U0 TwoChartCech.Sections.mk.injEq TwoChartCech.Cover.mk.injEq TwoChartCech.GrothendieckComplex.mk.injEq TwoChartCech.Sections.mk.sizeOf_spec TwoChartCech.Cover.mk.sizeOf_spec TwoChartCech.Cover.lineBundle_r0_apply TwoChartCech.GrothendieckComplex.mk.sizeOf_spec TwoChartCech.Cover.lineBundle_r1_apply CoherentBaseChange.TwoTermComplex.mk.sizeOf_spec CoherentBaseChange.TwoTermComplex.mk.injEq PresheafOfModules.freeεIso_hom_app PresheafOfModules.freeμIso_hom_app AlgebraicGeometry.RelPicard.RepresentsRelSubPic.mk.injEq AlgebraicGeometry.RelPicard.SubPicCondition.mk.injEq AlgebraicGeometry.RelPicard.SubPicCondition.mk.sizeOf_spec AlgebraicGeometry.RelPicard.RepresentsRelSubPic.mk.sizeOf_spec AlgebraicGeometry.SmoothProperCurve.sectionBaseChange_coe_snd AlgebraicGeometry.SmoothProperCurve.sectionBaseChange_coe_fst AlgebraicCurve.mulAdele_apply AlgebraicCurve.residuePairing_apply_coe AlgebraicCurve.mem_adeleBdd AlgebraicCurve.weilSmul_one AlgebraicCurve.diagonalHom_apply AlgebraicCurve.weilSmul_apply AlgebraicCurve.adeleSpaceMul_coe AlgebraicCurve.mulAdele_one AlgebraicGeometry.SmoothProperCurve.FiniteMapData.twoAffineOpenCover_U1 AlgebraicGeometry.SmoothProperCurve.FiniteMapData.mk.injEq AlgebraicGeometry.SmoothProperCurve.FiniteMapData.mk.sizeOf_spec AlgebraicGeometry.SmoothProperCurve.FiniteMapData.twoAffineOpenCover_U0 AlgebraicGeometry.RelPicard.SubPicCondition.onClasses_mk AlgebraicGeometry.RelPicard.relSubPicPresheaf_map_coe CategoryTheory.Functor.OverTotal.ofFibre_fst"
p2m_attr_erase "simp" "CategoryTheory.Functor.overTotal_map_fst AlgebraicGeometry.Scheme.LocalRepresentabilityULift.glueData_J AlgebraicGeometry.Scheme.LocalRepresentabilityULift.uliftYoneda_toGlued_uliftYonedaGluedToSheaf AlgebraicGeometry.Scheme.LocalRepresentabilityULift.glueData_t' AlgebraicGeometry.Scheme.LocalRepresentabilityULift.uliftYoneda_toGlued_uliftYonedaGluedToSheaf_assoc AlgebraicGeometry.Scheme.LocalRepresentabilityULift.uliftYonedaGluedToSheaf_app_toGlued AlgebraicGeometry.Scheme.LocalRepresentabilityULift.glueData_openCover_map AlgebraicGeometry.Scheme.LocalRepresentabilityULift.uliftYonedaGluedToSheaf_app_comp AlgebraicGeometry.Scheme.LocalRepresentabilityULift.glueData_V AlgebraicGeometry.Scheme.LocalRepresentabilityULift.glueData_t AlgebraicGeometry.Scheme.LocalRepresentabilityULift.glueData_U AlgebraicGeometry.Scheme.LocalRepresentabilityULift.glueData_f AlgebraicGeometry.RelPicard.designationOfRepresentableBy_P AlgebraicGeometry.RelPicard.designationOfRepresentableBy_toBase AlgebraicGeometry.RelPicard.rigSection_snd AlgebraicGeometry.RelPicard.RigidifiedLineBundle.ofInvertible_L AlgebraicGeometry.RelPicard.rigSection_snd_assoc AlgebraicGeometry.RelPicard.SubPicGroupCondition.mk.injEq AlgebraicGeometry.RelPicard.SubPicGroupCondition.mk.sizeOf_spec AlgebraicCurve.coe_cechH0Equiv_apply AlgebraicCurve.cechH1ToH1_mk AlgebraicCurve.lSpaceOn_univ AlgebraicCurve.lSpaceOn_empty AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe"
p2m_attr_erase "simp" "ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.jqNModC_one ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one AlgebraicCurve.Place.differentialCoeff_zero AlgebraicCurve.Place.differentialCoeff_dCoord AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.injEq AlgebraicCurve.TranscendenceTower.mk.injEq AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec AlgebraicCurve.PoleDivisorPackage.mk.injEq AlgebraicGeometry.RelPicard.thetaBundle_def AlgebraicGeometry.RelPicard.picardBundle_def AlgebraicGeometry.RelEffCartierDiv.toRelEffDivisor_ofRelEffDivisor AlgebraicGeometry.RelEffCartierDiv.toRelEffDivisor_I AlgebraicGeometry.mapOnProdOver_fst_assoc AlgebraicGeometry.RelEffCartierDiv.mk.sizeOf_spec"
p2m_attr_erase "simp" "AlgebraicGeometry.RelEffCartierDiv.mk.injEq AlgebraicGeometry.mapOnProdOver_snd AlgebraicGeometry.mapOnProdOver_fst AlgebraicGeometry.mapOnProdOver_snd_assoc AlgebraicGeometry.mapOnProdOver_id AlgebraicCurve.RelEffDivisor.mk.sizeOf_spec AlgebraicCurve.mapOnProd_fst AlgebraicCurve.mapOnProd_fst_assoc AlgebraicCurve.mapOnProd_snd AlgebraicCurve.UnivDivisorPack.mk.injEq AlgebraicCurve.RelEffDivisor.mk.injEq AlgebraicCurve.UnivDivisorPack.mk.sizeOf_spec AlgebraicCurve.mapOnProd_snd_assoc AlgebraicGeometry.Scheme.Modules.exteriorPower_obj PresheafOfModules.exteriorPower_map_ιMulti PresheafOfModules.ExteriorPower.appₗ_apply AlgebraicGeometry.prodKerGraph_one AlgebraicGeometry.fibrePowOver.proj_comp AlgebraicGeometry.prodKerGraph_zero AlgebraicGeometry.RelEffCartierDiv.empty_I AlgebraicGeometry.fibrePowOver.proj_comp_assoc AlgebraicGeometry.graphOver_fst_assoc AlgebraicGeometry.RelEffCartierDiv.toPoint_comp AlgebraicGeometry.RelEffCartierDiv.toPoint_comp_assoc AlgebraicGeometry.graphOver_fst AlgebraicGeometry.RelEffCartierDiv.ofPoint_I AlgebraicGeometry.graphOver_snd AlgebraicGeometry.graphOver_snd_assoc AlgebraicCurve.SymmetricPowerPackage.mk.sizeOf_spec AlgebraicCurve.SymmetricPowerPackage.mk.injEq AlgebraicGeometry.FGSubalgebra.cocone_ι_app_apply AlgebraicGeometry.RelPicard.fst_toProdSpec AlgebraicGeometry.RelPicard.toProdSpec_fst_assoc AlgebraicGeometry.RelPicard.pointsSubBasepointModule_cons AlgebraicGeometry.RelPicard.pointsSubBasepointModule_nil AlgebraicGeometry.RelPicard.fst_toProdSpec_assoc AlgebraicGeometry.RelPicard.toProdSpec_fst AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.sub_app AlgebraicGeometry.Scheme.IdealSheafData.sres_sresTop AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.add_app"
p2m_attr_erase "simp" "AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.mk.sizeOf_spec AlgebraicGeometry.Scheme.IdealSheafData.coe_resLE AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.smul_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.coe_ofLE_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.ideal_range AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.zero_app AlgebraicGeometry.Scheme.IdealSheafData.sres_sres AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.comp_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.neg_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.id_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.coe_mulRight_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.nsmul_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.mk.injEq AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.zsmul_app AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.sizeOf_spec AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.injEq AlgebraicCurve.adeleSingle_coe AlgebraicCurve.kaehlerResidueTermKFam_apply AlgebraicCurve.Place.LocalResidueData.mk.injEq AlgebraicCurve.Place.LocalResidueData.mk.sizeOf_spec AlgebraicCurve.Place.kw_ffgc_adicCompletionComapIntegers_coe AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.sizeOf_spec AlgebraicCurve.Place.mem_simplePoleSubmodule AlgebraicCurve.Place.coe_uniformizerSubring ModularCurve.Lg37.Lg37CompletionSection.mk.injEq AlgebraicCurve.Place.CoefficientFieldSection.mk.injEq AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.injEq ModularCurve.Lg37.Lg37CompletionSection.mk.sizeOf_spec AlgebraicCurve.Place.CoefficientFieldSection.mk.sizeOf_spec AlgebraicCurve.Place.poleSubmodule_one AlgebraicCurve.Place.mem_poleSubmodule AlgebraicGeometry.Scheme.Modules.toUnitSection_ofUnitSection AlgebraicGeometry.Scheme.Modules.pullbackSection_def AlgebraicGeometry.Scheme.Modules.ofUnitSection_toUnitSection PresheafOfModules.InternalHom.IsSheafAux.appAt_toPresheafHom SheafOfModules.ihomSectionsEquivFamily_unit AlgebraicGeometry.Scheme.Modules.restrictHomEquivFamily_apply SheafOfModules.ihomEval_unit_app AlgebraicGeometry.Scheme.Modules.ihomEval_zero_right AlgebraicGeometry.Scheme.Modules.ihomEval_zero_left"
p2m_attr_erase "simp" "AlgebraicGeometry.Scheme.Modules.homOfFamily_app_apply SheafOfModules.unit_ihomSectionsEquivFamily AlgebraicGeometry.Scheme.Modules.familyOfHom_app AlgebraicGeometry.Scheme.Modules.restrictUnitIso_hom_app_apply AlgebraicGeometry.Scheme.Modules.restrictUnitIso_inv_app_apply AlgebraicGeometry.Scheme.Modules.restrictHomOfFamily_app_apply AlgebraicGeometry.Scheme.Modules.restrictHomEquivFamily_symm_apply AlgebraicGeometry.Scheme.Modules.tensorSections_zero_right AlgebraicGeometry.Scheme.Modules.map_unitSection AlgebraicGeometry.Scheme.Modules.tensorSectionsBilin_apply AlgebraicGeometry.Scheme.Modules.tensorPowSection_zero AlgebraicGeometry.Scheme.Modules.tensorSections_zero_left AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_neg AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_zero AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_sub AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_add AlgebraicGeometry.Scheme.OrderedAffineCover.toCoverOf_U AlgebraicGeometry.Scheme.OrderedAffineCoverOf.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCoverOf.mk.injEq AlgebraicGeometry.Scheme.OrderedAffineCover.restrict_U AlgebraicGeometry.OModulePresheaf.Hom.mk.injEq AlgebraicGeometry.OModulePresheaf.Hom.id_app AlgebraicGeometry.OModulePresheaf.AffHom.appSections_apply AlgebraicGeometry.OModulePresheaf.AffHom.comp_app AlgebraicGeometry.OModulePresheaf.AffSES.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.AffHom.kerMap_coe AlgebraicGeometry.OModulePresheaf.AffHom.id_app AlgebraicGeometry.OModulePresheaf.Hom.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.Hom.toAffHom_app AlgebraicGeometry.OModulePresheaf.SES.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.AffHom.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.Hom.comp_app AlgebraicGeometry.OModulePresheaf.SES.mk.injEq AlgebraicGeometry.OModulePresheaf.AffHom.mk.injEq AlgebraicGeometry.OModulePresheaf.Hom.appSections_apply AlgebraicGeometry.OModulePresheaf.AffSES.mk.injEq AlgebraicGeometry.OModulePresheaf.prod_obj AlgebraicGeometry.OModulePresheaf.restrOpen_obj AlgebraicGeometry.OModulePresheaf.DevissageStep.mk.injEq AlgebraicGeometry.OModulePresheaf.pushforward_obj"
p2m_attr_erase "simp" "AlgebraicGeometry.OModulePresheaf.im_obj AlgebraicGeometry.OModulePresheaf.pow_obj AlgebraicGeometry.OModulePresheaf.fstHom_app AlgebraicGeometry.OModulePresheaf.ker_obj AlgebraicGeometry.OModulePresheaf.coker_obj AlgebraicGeometry.OModulePresheaf.DevissageStep.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCover.preimage_U AlgebraicGeometry.OModulePresheaf.sndHom_app AlgebraicGeometry.OModulePresheaf.Leray.restrictToPreimage_U DoubleComplex.Bounded.mk.injEq DoubleComplex.Bounded.mk.sizeOf_spec DoubleComplex.Convergence.mk.injEq DoubleComplex.Convergence.mk.sizeOf_spec DoubleComplex.SubQuot.mk.sizeOf_spec DoubleComplex.SubQuot.mk.injEq AlgebraicGeometry.ChowDatumProj.mk.sizeOf_spec AlgebraicGeometry.ChowDatum.mk.sizeOf_spec AlgebraicGeometry.ChowDatumProj.mk.injEq AlgebraicGeometry.ChowDatum.mk.injEq ProjSpaceCech.GradedModule.mk.injEq ProjSpaceCech.GradedModule.mk.sizeOf_spec ProjSpaceCech.GradedModule.Frac.mk.sizeOf_spec ProjSpaceCech.GradedModule.Presentation.mk.injEq ProjSpaceCech.GradedModule.Frac.mk.injEq ProjSpaceCech.GradedModule.Presentation.mk.sizeOf_spec ProjSpaceCech.GradedModule.Hom.shift_toLinearMap ProjSpaceCech.GradedModule.Hom.mk.sizeOf_spec ProjSpaceCech.GradedModule.Hom.mk.injEq TwoChartCech.Mumford.dK_apply TwoChartCech.Mumford.ι0_apply TwoChartCech.Mumford.ι1_apply TwoChartCech.KerCoprod.dK_apply TwoChartCech.KerCoprod.ι1_apply TwoChartCech.KerCoprod.ι0_apply AlgebraicGeometry.tilde.functorCompPullbackSpecIso_app AlgebraicGeometry.RelPicard.algEquivZeroGroupCut_toSubPicCondition AlgebraicGeometry.RelPicard.LFP.stageHom_val AlgebraicGeometry.RelPicard.BaseChange.relSubPicPresheafRestrictIso_hom_app_coe AlgebraicGeometry.RelPicard.BaseChange.relSubPicPresheafRestrictIso_inv_app_coe AlgebraicGeometry.RelPicard.BaseChange.restrict_P"
p2m_attr_erase "simp" "AlgebraicGeometry.RelEffCartierDiv.IsUniversal.lift_comp AlgebraicGeometry.RelEffCartierDiv.functor_map_fst AlgebraicGeometry.RelEffCartierDiv.IsUniversal.homEquiv_apply AlgebraicGeometry.RelEffCartierDiv.IsUniversal.lift_pullbackAlong AlgebraicGeometry.RelEffCartierDiv.IsUniversal.homEquiv_symm_apply AlgebraicGeometry.RelEffCartierDiv.IsUniversal.lift_comp_assoc AlgebraicGeometry.RelEffCartierDiv.supportedIn_top AlgebraicGeometry.RelEffCartierDiv.mem_supportedIn_iff AlgebraicGeometry.RelEffCartierDiv.supportedIn_top_eq AlgebraicGeometry.RelEffCartierDiv.restrictAlong_extendAlong AlgebraicGeometry.RelEffCartierDiv.extendAlong_I AlgebraicGeometry.RelEffCartierDiv.resProdMap_snd AlgebraicGeometry.RelEffCartierDiv.restrictAlong_I AlgebraicGeometry.RelEffCartierDiv.extendAlong_restrictAlong AlgebraicGeometry.RelEffCartierDiv.resProdMap_fst_assoc AlgebraicGeometry.RelEffCartierDiv.resProdMap_snd_assoc AlgebraicGeometry.RelEffCartierDiv.resProdMap_fst CoherentBaseChange.FibreH0Family.mk.sizeOf_spec CoherentBaseChange.FibreH0Family.mk.injEq AlgebraicGeometry.Scheme.Modules.ProjPresentation.mk.injEq AlgebraicGeometry.Scheme.Modules.ProjPresentation.mk.sizeOf_spec AlgebraicCurve.CurveModel.coe_gInf AlgebraicCurve.CurveModel.coe_tInvChart AlgebraicCurve.CurveModel.ιInf_gluedToBase_assoc AlgebraicCurve.CurveModel.ιInf_gluedToBase AlgebraicCurve.CurveModel.primeOfι₀_asIdeal AlgebraicCurve.CurveModel.coe_tChart AlgebraicCurve.CurveModel.ι₀_gluedToBase_assoc AlgebraicCurve.CurveModel.primeOfιInf_asIdeal AlgebraicCurve.CurveModel.ι₀_gluedToBase AlgebraicCurve.CurveModel.coe_tma AlgebraicCurve.CurveModel.coe_primeEquivChartPlaces RegularLocalRingQuotientAscent.dualNumberFst_apply AlgebraicGeometry.ProjSpace.twistObj.mk.injEq AlgebraicGeometry.ProjSpace.twistObj.zero_val AlgebraicGeometry.ProjSpace.twistObj.add_val AlgebraicGeometry.ProjSpace.twist_res_val AlgebraicGeometry.ProjSpace.twist_smul_val AlgebraicGeometry.ProjSpace.twistGradeToObj_val AlgebraicGeometry.ProjSpace.twistObj.smul_val"
p2m_attr_erase "simp" "AlgebraicGeometry.ProjSpace.twistGradeEquiv_apply_val AlgebraicGeometry.ProjSpace.twistObj.mk.sizeOf_spec GoodReductionJacobian.RelativeGroupLaw.fibre_inv GoodReductionJacobian.RelativeGroupLaw.fibrePointToBase_coe GoodReductionJacobian.RelativeGroupLaw.fibrePointOfBase_toBase GoodReductionJacobian.RelativeGroupLaw.fibre_mul GoodReductionJacobian.RelativeGroupLaw.fibrePointToBase_ofBase GoodReductionJacobian.RelativeGroupLaw.fibre_one GoodReductionJacobian.RelativeGroupLaw.fibrePointOfBase_coe AlgebraicGeometry.schemeFibreEndo_snd AlgebraicGeometry.schemeFibreEndo_fst QuaternionAlgebra.ClassSet.map_mk QuaternionAlgebra.baseChangeRight_tmul QuaternionAlgebra.mapOfAlgebraMapEq_apply QuaternionAlgebra.baseChange_tmul"

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry NeronModelInfra GoodReductionJacobian IsDedekindDomain AlgebraicCurve QuaternionAlgebra CerednikDrinfeld CerednikDrinfeld.QM
open scoped Quaternion TensorProduct NumberField

namespace Ws23TL
namespace L1

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry NeronModelInfra GoodReductionJacobian IsDedekindDomain AlgebraicCurve QuaternionAlgebra CerednikDrinfeld CerednikDrinfeld.QM
open scoped Quaternion TensorProduct NumberField

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian
open CerednikDrinfeld CerednikDrinfeld.QM CerednikDrinfeld.QM.FakeEllipticCurve QuaternionAlgebra
open scoped Quaternion

namespace ALComm

variable {S : Type u} [CommRing S] {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} {N : ℕ}

abbrev aP (E : FakeEllipticCurve Λ N S) (m : ↥Λ) {T : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of S)}
    (P : SchemeHomOver t E.f) : SchemeHomOver t E.f :=
  pushPt (E.act m) (E.act_over m) P

section Action

variable (E : FakeEllipticCurve Λ N S) {T : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of S)}

theorem aP_coe (m : ↥Λ) (P : SchemeHomOver t E.f) : (aP E m P).1 = P.1 ≫ E.act m := rfl

theorem aP_mul (x y : ↥Λ) (h : (x : ℍ[ℚ, a, b]) * (y : ℍ[ℚ, a, b]) ∈ Λ) (P : SchemeHomOver t E.f) :
    aP E x (aP E y P) = aP E ⟨(x : ℍ[ℚ, a, b]) * (y : ℍ[ℚ, a, b]), h⟩ P := by
  apply Subtype.ext
  simp only [aP_coe, Category.assoc, E.act_mul x y h]

theorem aP_congr {x y : ↥Λ} (h : (x : ℍ[ℚ, a, b]) = (y : ℍ[ℚ, a, b])) (P : SchemeHomOver t E.f) :
    aP E x P = aP E y P := by
  obtain rfl : x = y := Subtype.ext h; rfl

theorem aP_add (x y : ↥Λ) (P : SchemeHomOver t E.f) :
    aP E (x + y) P = E.L.mul t (aP E x P) (aP E y P) := E.act_add x y t P

theorem aP_hom (m : ↥Λ) (P Q : SchemeHomOver t E.f) :
    aP E m (E.L.mul t P Q) = E.L.mul t (aP E m P) (aP E m Q) := E.act_hom m t P Q

theorem aP_one (m : ↥Λ) : aP E m (E.L.one t) = E.L.one t := by
  set x := aP E m (E.L.one t) with hx
  have hxx : E.L.mul t x x = x := by rw [hx, ← aP_hom, E.L.one_mul]
  letI := E.L.pointGroup t
  have h2 : x * x = x * 1 := by rw [mul_one]; exact hxx
  exact mul_left_cancel h2

theorem aP_unit (h1 : (1 : ℍ[ℚ, a, b]) ∈ Λ) (P : SchemeHomOver t E.f) : aP E ⟨1, h1⟩ P = P := by
  apply Subtype.ext
  simp only [aP_coe, E.act_one h1, Category.comp_id]

theorem aP_zero (P : SchemeHomOver t E.f) : aP E 0 P = E.L.one t := by
  have h := aP_add E 0 0 P
  rw [add_zero] at h
  letI := E.L.pointGroup t
  have h2 : aP E 0 P * aP E 0 P = aP E 0 P * 1 := by rw [mul_one]; exact h.symm
  exact mul_left_cancel h2

end Action

section Arithmetic

theorem intCast_mem (hΛ : IsOrder Λ) (z : ℤ) : (((z : ℚ)) : ℍ[ℚ, a, b]) ∈ Λ := by
  have : (((z : ℚ)) : ℍ[ℚ, a, b]) = z • (1 : ℍ[ℚ, a, b]) := by
    rw [zsmul_eq_mul, mul_one, coe_intCast]
  rw [this]; exact Λ.smul_mem z hΛ.one_mem

theorem natCast_mem (hΛ : IsOrder Λ) (n : ℕ) : (((n : ℚ)) : ℍ[ℚ, a, b]) ∈ Λ := by
  have := intCast_mem hΛ (n : ℤ); push_cast at this; exact this

def PCond (r : ℕ) (m : ℍ[ℚ, a, b]) : Prop :=
  ∃ n : ℤ, m * star m = ((((r : ℤ) * n : ℚ)) : ℍ[ℚ, a, b])

theorem pcond_natCast (r : ℕ) : PCond (a := a) (b := b) r ((r : ℚ) : ℍ[ℚ, a, b]) :=
  ⟨r, by rw [star_coe, ← coe_mul]; exact congrArg (fun x : ℚ => (x : ℍ[ℚ, a, b])) (by norm_cast)⟩

theorem pcond_intCast_mul (r : ℕ) (z : ℤ) : PCond (a := a) (b := b) r (((z * r : ℤ) : ℚ) : ℍ[ℚ, a, b]) :=
  ⟨z * z * r, by rw [star_coe, ← coe_mul]; congr 1; push_cast; ring⟩

theorem pcond_mul (hΛ : IsOrder Λ) (r : ℕ) {m m' : ℍ[ℚ, a, b]} (hm : PCond r m) (hm' : m' ∈ Λ) :
    PCond r (m * m') := by
  obtain ⟨n, hn⟩ := hm
  obtain ⟨⟨k, hk⟩, -⟩ := QuaternionAlgebra.IsOrder.exists_intCast_eq_nrd_and_exists_intCast_eq_trd hΛ hm'
  refine ⟨n * k, ?_⟩
  calc m * m' * star (m * m') = m * (m' * star m') * star m := by rw [star_mul]; simp only [mul_assoc]
    _ = m * ((nrd m' : ℚ) : ℍ[ℚ, a, b]) * star m := by rw [mul_star_eq_coe_nrd, mul_assoc]
    _ = ((k : ℚ) : ℍ[ℚ, a, b]) * (m * star m) := by rw [← hk, ← coe_commutes, mul_assoc]
    _ = (((((r : ℤ) : ℚ) * ((n * k : ℤ) : ℚ) : ℚ)) : ℍ[ℚ, a, b]) := by
        rw [hn, ← coe_mul]; exact congrArg (fun x : ℚ => (x : ℍ[ℚ, a, b])) (by push_cast; ring)

end Arithmetic

section Kernel

variable (E : FakeEllipticCurve Λ N S) {T : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of S)}

def Kill (r : ℕ) (P : SchemeHomOver t E.f) : Prop :=
  ∀ (m : ↥Λ) (n : ℤ), (m : ℍ[ℚ, a, b]) * star (m : ℍ[ℚ, a, b]) = ((((r : ℤ) * n : ℚ)) : ℍ[ℚ, a, b]) →
    aP E m P = E.L.one t

theorem kill_iff (r : ℕ) (P : SchemeHomOver t E.f) :
    Kill E r P ↔ ∀ m : ↥Λ, PCond r (m : ℍ[ℚ, a, b]) → aP E m P = E.L.one t :=
  ⟨fun h m ⟨n, hn⟩ => h m n hn, fun h m n hn => h m ⟨n, hn⟩⟩

theorem swap (hΛ : IsOrder Λ) (q q' : ℕ) (hqq' : Nat.Coprime q q') (P : SchemeHomOver t E.f)
    (A1 : ∀ m : ↥Λ, PCond q' (m : ℍ[ℚ, a, b]) → Kill E q (aP E m P)) :
    ∀ m' : ↥Λ, PCond q (m' : ℍ[ℚ, a, b]) → Kill E q' (aP E m' P) := by
  classical

  obtain ⟨A, B, hAB⟩ := hqq'.isCoprime

  let e₁ : ↥Λ := ⟨(((A * q : ℤ) : ℚ) : ℍ[ℚ, a, b]), intCast_mem hΛ _⟩
  let e₂ : ↥Λ := ⟨(((B * q' : ℤ) : ℚ) : ℍ[ℚ, a, b]), intCast_mem hΛ _⟩
  have he : e₁ + e₂ = ⟨1, hΛ.one_mem⟩ := by
    apply Subtype.ext
    show (((A * q : ℤ) : ℚ) : ℍ[ℚ, a, b]) + (((B * q' : ℤ) : ℚ) : ℍ[ℚ, a, b]) = 1
    rw [← coe_add, ← coe_one]; congr 1; exact_mod_cast hAB
  let cq : ↥Λ := ⟨((q : ℚ) : ℍ[ℚ, a, b]), natCast_mem hΛ q⟩
  let cA : ↥Λ := ⟨((A : ℚ) : ℍ[ℚ, a, b]), intCast_mem hΛ A⟩

  have hP₁ : Kill E q' (aP E e₁ P) := by
    rw [kill_iff]
    intro m hm

    have h1 : aP E cq (aP E m P) = E.L.one t := by
      have := A1 m hm; rw [kill_iff] at this
      exact this cq (pcond_natCast q)
    have hmem : ((q : ℚ) : ℍ[ℚ, a, b]) * (m : ℍ[ℚ, a, b]) ∈ Λ := hΛ.mul_mem cq.2 m.2
    rw [aP_mul E cq m hmem] at h1
    have hmem2 : ((A : ℚ) : ℍ[ℚ, a, b]) * (((q : ℚ) : ℍ[ℚ, a, b]) * (m : ℍ[ℚ, a, b])) ∈ Λ := hΛ.mul_mem cA.2 hmem
    have h2 : aP E ⟨_, hmem2⟩ P = E.L.one t := by
      rw [← aP_mul E cA ⟨_, hmem⟩ hmem2, h1, aP_one]
    rw [aP_mul E m e₁ (hΛ.mul_mem m.2 e₁.2), ← h2]
    apply aP_congr
    show (m : ℍ[ℚ, a, b]) * (((A * q : ℤ) : ℚ) : ℍ[ℚ, a, b]) = ((A : ℚ) : ℍ[ℚ, a, b]) * (((q : ℚ) : ℍ[ℚ, a, b]) * (m : ℍ[ℚ, a, b]))
    simp only [mul_coe_eq_smul, coe_mul_eq_smul, smul_smul]
    congr 1
    push_cast
    ring

  have hP₂ : ∀ m' : ↥Λ, PCond q (m' : ℍ[ℚ, a, b]) → aP E m' (aP E e₂ P) = E.L.one t := by
    intro m' hm'
    have := A1 e₂ (pcond_intCast_mul (a := a) (b := b) q' B); rw [kill_iff] at this
    exact this m' hm'

  intro m' hm'
  rw [kill_iff]
  intro m hm
  have hsplit : P = E.L.mul t (aP E e₁ P) (aP E e₂ P) := by
    rw [← aP_add, he, aP_unit]
  rw [hsplit, aP_hom, hP₂ m' hm', E.L.mul_one, aP_mul E m m' (hΛ.mul_mem m.2 m'.2)]
  rw [kill_iff] at hP₁
  exact hP₁ _ (pcond_mul hΛ q' hm m'.2)

theorem swap_iff (hΛ : IsOrder Λ) (q q' : ℕ) (hqq' : Nat.Coprime q q') (P : SchemeHomOver t E.f) :
    (∀ m : ↥Λ, PCond q' (m : ℍ[ℚ, a, b]) → Kill E q (aP E m P)) ↔
      (∀ m' : ↥Λ, PCond q (m' : ℍ[ℚ, a, b]) → Kill E q' (aP E m' P)) :=
  ⟨swap E hΛ q q' hqq' P, swap E hΛ q' q hqq'.symm P⟩

end Kernel

section Composite

variable {E E₁ E₁₂ : FakeEllipticCurve Λ N S}

theorem comp_eq_one_iff (r r' : ℕ)
    (φ₁ : E.A ⟶ E₁.A) (hφ₁ : φ₁ ≫ E₁.f = E.f) (φ₁₂ : E₁.A ⟶ E₁₂.A) (hφ₁₂ : φ₁₂ ≫ E₁₂.f = E₁.f)
    (hlin₁ : ∀ x : ↥Λ, E.act x ≫ φ₁ = φ₁ ≫ E₁.act x)
    (hker₁ : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of S)) (P : SchemeHomOver t E.f),
      mapPt φ₁ hφ₁ P = E₁.L.one t ↔ Kill E r P)
    (hker₁₂ : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of S)) (Q : SchemeHomOver t E₁.f),
      mapPt φ₁₂ hφ₁₂ Q = E₁₂.L.one t ↔ Kill E₁ r' Q)
    {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of S)) (P : SchemeHomOver t E.f) :
    mapPt (φ₁ ≫ φ₁₂) (by rw [Category.assoc, hφ₁₂, hφ₁]) P = E₁₂.L.one t ↔
      ∀ m : ↥Λ, PCond r' (m : ℍ[ℚ, a, b]) → Kill E r (aP E m P) := by
  have hc : mapPt (φ₁ ≫ φ₁₂) (by rw [Category.assoc, hφ₁₂, hφ₁]) P = mapPt φ₁₂ hφ₁₂ (mapPt φ₁ hφ₁ P) :=
    Subtype.ext (by simp only [mapPt_coe, Category.assoc])
  rw [hc, hker₁₂, kill_iff]
  refine forall_congr' fun m => forall_congr' fun _ => ?_
  have hl : aP E₁ m (mapPt φ₁ hφ₁ P) = mapPt φ₁ hφ₁ (aP E m P) :=
    Subtype.ext (by simp only [mapPt_coe, Category.assoc, hlin₁ m])
  rw [hl, hker₁]

end Composite

end ALComm

namespace ALComm

section ActNat

variable {S : Type u} [CommRing S] {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} {N : ℕ}
  (E : FakeEllipticCurve Λ N S) {T : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of S)}

theorem aP_natCast (hΛ : IsOrder Λ) (n : ℕ) (P : SchemeHomOver t E.f) :
    aP E ⟨((n : ℚ) : ℍ[ℚ, a, b]), natCast_mem hΛ n⟩ P = nsmulPt E.L t n P := by
  induction n with
  | zero =>
    have h0 : (⟨(((0 : ℕ) : ℚ) : ℍ[ℚ, a, b]), natCast_mem hΛ 0⟩ : ↥Λ) = 0 := Subtype.ext (by push_cast; rfl)
    rw [h0, aP_zero]; rfl
  | succ n ih =>
    have hs : (⟨(((n + 1 : ℕ) : ℚ) : ℍ[ℚ, a, b]), natCast_mem hΛ (n + 1)⟩ : ↥Λ) =
        ⟨((n : ℚ) : ℍ[ℚ, a, b]), natCast_mem hΛ n⟩ + ⟨1, hΛ.one_mem⟩ := Subtype.ext (by push_cast; rfl)
    rw [hs, aP_add, ih, aP_unit]; rfl

theorem comp_dual_eq_nsmul (hΛ : IsOrder Λ) {E₁ E₁₂ : FakeEllipticCurve Λ N S} (r r' : ℕ)
    (φ₁ : E.A ⟶ E₁.A) (hφ₁ : φ₁ ≫ E₁.f = E.f) (ψ₁ : E₁.A ⟶ E.A) (hψ₁ : ψ₁ ≫ E.f = E₁.f)
    (φ₁₂ : E₁.A ⟶ E₁₂.A) (hφ₁₂ : φ₁₂ ≫ E₁₂.f = E₁.f) (ψ₁₂ : E₁₂.A ⟶ E₁.A) (hψ₁₂ : ψ₁₂ ≫ E₁.f = E₁₂.f)
    (hlin₁ : ∀ x : ↥Λ, E.act x ≫ φ₁ = φ₁ ≫ E₁.act x)
    (hc₁ : φ₁ ≫ ψ₁ = E.act ⟨((r : ℚ) : ℍ[ℚ, a, b]), natCast_mem hΛ r⟩)
    (hc₁₂ : φ₁₂ ≫ ψ₁₂ = E₁.act ⟨((r' : ℚ) : ℍ[ℚ, a, b]), natCast_mem hΛ r'⟩)
    (P : SchemeHomOver t E.f) :
    mapPt (ψ₁₂ ≫ ψ₁) (by rw [Category.assoc, hψ₁, hψ₁₂])
      (mapPt (φ₁ ≫ φ₁₂) (by rw [Category.assoc, hφ₁₂, hφ₁]) P) = nsmulPt E.L t (r * r') P := by
  have hrr : (⟨((((r * r' : ℕ) : ℚ)) : ℍ[ℚ, a, b]), natCast_mem hΛ (r * r')⟩ : ↥Λ) =
      ⟨((r : ℚ) : ℍ[ℚ, a, b]) * ((r' : ℚ) : ℍ[ℚ, a, b]), hΛ.mul_mem (natCast_mem hΛ r) (natCast_mem hΛ r')⟩ :=
    Subtype.ext (by simp only [Nat.cast_mul, coe_mul])
  rw [← aP_natCast E hΛ, hrr]
  apply Subtype.ext
  simp only [mapPt_coe, Category.assoc]
  rw [← Category.assoc φ₁₂ ψ₁₂ ψ₁, hc₁₂, ← Category.assoc φ₁, ← hlin₁, Category.assoc, hc₁,
    E.act_mul ⟨((r : ℚ) : ℍ[ℚ, a, b]), natCast_mem hΛ r⟩ ⟨((r' : ℚ) : ℍ[ℚ, a, b]), natCast_mem hΛ r'⟩]

end ActNat

end ALComm

namespace ALTSq
open ALComm

variable {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]}

theorem pcond_iff_nrd (r : ℕ) (m : ℍ[ℚ, a, b]) :
    PCond r m ↔ ∃ n : ℤ, nrd m = (r : ℚ) * n := by
  unfold PCond
  rw [mul_star_eq_coe_nrd]
  constructor
  · rintro ⟨n, hn⟩
    refine ⟨n, ?_⟩
    have h := QuaternionAlgebra.coe_injective hn
    exact_mod_cast h
  · rintro ⟨n, hn⟩
    refine ⟨n, ?_⟩
    rw [hn]
    norm_cast

end ALTSq

open ALComm ALTSq in
theorem BaseAL.iso_of_alq_comp
    {N q q' : ℕ} [NeZero N] [Fact q.Prime] [Fact q'.Prime] (hqN : ¬ q ∣ N) (hq'N : ¬ q' ∣ N) (hqq' : q' ≠ q)
    {a b : ℚ} (hB : IsIndefiniteRamifiedExactlyAt a b q q')
    (Λ : Submodule ℤ ℍ[ℚ, a, b]) (hΛ : IsMaximalOrder Λ)
    (r : ℕ) (hr : r = q ∨ r = q')
    (u u' u'' : QM.FakeEllipticCurve Λ N (AlgebraicClosure ℚ))
    (h : QM.FakeEllipticCurve.IsAtkinLehnerQuotient r u u')
    (h' : QM.FakeEllipticCurve.IsAtkinLehnerQuotient r u' u'') :
    QM.FakeEllipticCurve.Iso u u'' := by
  classical
  have hO : IsOrder Λ := hΛ.isOrder
  have hrp : r.Prime := by rcases hr with rfl | rfl <;> exact Fact.out
  have hrN : ¬ r ∣ N := by rcases hr with rfl | rfl <;> assumption
  have hcopN : Nat.Coprime r N := (Nat.Prime.coprime_iff_not_dvd hrp).2 hrN
  have hcopN2 : Nat.Coprime (r * r) N := Nat.Coprime.mul_left hcopN hcopN
  have hrΛ : ((r : ℚ) : ℍ[ℚ, a, b]) ∈ Λ := natCast_mem hO r
  obtain ⟨φ₁, hφ₁, ψ₁, hψ₁, m₁, mψ₁, l₁, lψ₁, c₁, k₁, v₁⟩ := h
  obtain ⟨φ₂, hφ₂, ψ₂, hψ₂, m₂, mψ₂, l₂, lψ₂, c₂, k₂, v₂⟩ := h'

  obtain ⟨RAM1, RAM2⟩ := QuaternionAlgebra.IsMaximalOrder.span_mul_ramifiedPrime_eq_of_isIndefiniteRamifiedExactlyAt hB Λ hΛ r hr

  have hΦ : (φ₁ ≫ φ₂) ≫ u''.f = u.f := by rw [Category.assoc, hφ₂, hφ₁]
  have hΨ : (ψ₂ ≫ ψ₁) ≫ u.f = u''.f := by rw [Category.assoc, hψ₁, hψ₂]
  have mc : ∀ {A B C : Scheme.{0}} {fA : A ⟶ Spec (CommRingCat.of (AlgebraicClosure ℚ))} {fB : B ⟶ Spec (CommRingCat.of (AlgebraicClosure ℚ))}
      {fC : C ⟶ Spec (CommRingCat.of (AlgebraicClosure ℚ))} (θ : A ⟶ B) (hθ : θ ≫ fB = fA) (θ' : B ⟶ C) (hθ' : θ' ≫ fC = fB)
      (hθθ' : (θ ≫ θ') ≫ fC = fA) {T : Scheme.{0}} {t : T ⟶ Spec (CommRingCat.of (AlgebraicClosure ℚ))} (P : SchemeHomOver t fA),
      mapPt (θ ≫ θ') hθθ' P = mapPt θ' hθ' (mapPt θ hθ P) := by
    intro A B C fA fB fC θ hθ θ' hθ' hθθ' T t P
    exact Subtype.ext (by simp only [mapPt_coe, Category.assoc])
  have MΦ : ∀ {T : Scheme} (t : T ⟶ Spec (CommRingCat.of (AlgebraicClosure ℚ))) (P Q : SchemeHomOver t u.f),
      mapPt (φ₁ ≫ φ₂) hΦ (u.L.mul t P Q) = u''.L.mul t (mapPt (φ₁ ≫ φ₂) hΦ P) (mapPt (φ₁ ≫ φ₂) hΦ Q) := by
    intro T t P Q; rw [mc φ₁ hφ₁ φ₂ hφ₂, mc φ₁ hφ₁ φ₂ hφ₂, mc φ₁ hφ₁ φ₂ hφ₂, m₁, m₂]
  have LΦ : ∀ x : ↥Λ, u.act x ≫ (φ₁ ≫ φ₂) = (φ₁ ≫ φ₂) ≫ u''.act x := by
    intro x; rw [← Category.assoc, l₁, Category.assoc, l₂, Category.assoc]
  have DΦ : ∀ {T : Scheme} (t : T ⟶ Spec (CommRingCat.of (AlgebraicClosure ℚ))) (P : SchemeHomOver t u.f),
      mapPt (ψ₂ ≫ ψ₁) hΨ (mapPt (φ₁ ≫ φ₂) hΦ P) = nsmulPt u.L t (r * r) P :=
    fun t P => comp_dual_eq_nsmul u hO r r φ₁ hφ₁ ψ₁ hψ₁ φ₂ hφ₂ ψ₂ hψ₂ l₁ (c₁ hrΛ).1 (c₂ hrΛ).1 P
  have DΦ' : ∀ {T : Scheme} (t : T ⟶ Spec (CommRingCat.of (AlgebraicClosure ℚ))) (Q : SchemeHomOver t u''.f),
      mapPt (φ₁ ≫ φ₂) hΦ (mapPt (ψ₂ ≫ ψ₁) hΨ Q) = nsmulPt u''.L t (r * r) Q :=
    fun t Q => comp_dual_eq_nsmul u'' hO r r ψ₂ hψ₂ φ₂ hφ₂ ψ₁ hψ₁ φ₁ hφ₁ lψ₂ (c₂ hrΛ).2 (c₁ hrΛ).2 Q

  let ρ : u.A ⟶ u.A := u.act ⟨((r : ℚ) : ℍ[ℚ, a, b]), hrΛ⟩
  have hρ : ρ ≫ u.f = u.f := u.act_over _
  have hid : (𝟙 u.A) ≫ u.f = u.f := Category.id_comp _
  have ρpt : ∀ {T : Scheme} (t : T ⟶ Spec (CommRingCat.of (AlgebraicClosure ℚ))) (P : SchemeHomOver t u.f), mapPt ρ hρ P = aP u ⟨((r : ℚ) : ℍ[ℚ, a, b]), hrΛ⟩ P :=
    fun t P => rfl
  have idpt : ∀ {T : Scheme} (t : T ⟶ Spec (CommRingCat.of (AlgebraicClosure ℚ))) (P : SchemeHomOver t u.f), mapPt (𝟙 u.A) hid P = P :=
    fun t P => Subtype.ext (by simp only [mapPt_coe, Category.comp_id])
  have Mρ : ∀ {T : Scheme} (t : T ⟶ Spec (CommRingCat.of (AlgebraicClosure ℚ))) (P Q : SchemeHomOver t u.f),
      mapPt ρ hρ (u.L.mul t P Q) = u.L.mul t (mapPt ρ hρ P) (mapPt ρ hρ Q) :=
    fun t P Q => aP_hom u _ P Q
  have Lρ : ∀ x : ↥Λ, u.act x ≫ ρ = ρ ≫ u.act x := by
    intro x
    show u.act x ≫ u.act ⟨_, hrΛ⟩ = u.act ⟨_, hrΛ⟩ ≫ u.act x
    rw [← u.act_mul ⟨_, hrΛ⟩ x (hO.mul_mem hrΛ x.2), ← u.act_mul x ⟨_, hrΛ⟩ (hO.mul_mem x.2 hrΛ)]
    congr 1; apply Subtype.ext
    show ((r : ℚ) : ℍ[ℚ, a, b]) * (x : ℍ[ℚ, a, b]) = (x : ℍ[ℚ, a, b]) * ((r : ℚ) : ℍ[ℚ, a, b])
    rw [coe_commutes]
  have Dρ : ∀ {T : Scheme} (t : T ⟶ Spec (CommRingCat.of (AlgebraicClosure ℚ))) (P : SchemeHomOver t u.f), mapPt (𝟙 u.A) hid (mapPt ρ hρ P) = nsmulPt u.L t r P := by
    intro T t P; rw [idpt, ρpt, aP_natCast u hO]
  have Dρ' : ∀ {T : Scheme} (t : T ⟶ Spec (CommRingCat.of (AlgebraicClosure ℚ))) (P : SchemeHomOver t u.f), mapPt ρ hρ (mapPt (𝟙 u.A) hid P) = nsmulPt u.L t r P := by
    intro T t P; rw [idpt, ρpt, aP_natCast u hO]

  have K : ∀ {T : Scheme} (t : T ⟶ Spec (CommRingCat.of (AlgebraicClosure ℚ))) (P : SchemeHomOver t u.f),
      mapPt ρ hρ P = u.L.one t ↔ mapPt (φ₁ ≫ φ₂) hΦ P = u''.L.one t := by
    intro T t P
    rw [comp_eq_one_iff r r φ₁ hφ₁ φ₂ hφ₂ l₁ k₁ k₂ t P, ρpt]
    constructor
    ·
      intro hP m hm
      rw [kill_iff]
      intro m' hm'
      rw [aP_mul u m' m (hO.mul_mem m'.2 m.2)]
      obtain ⟨y, hy, hxy⟩ := RAM1 (m' : ℍ[ℚ, a, b]) m'.2 (m : ℍ[ℚ, a, b]) m.2
        ((pcond_iff_nrd r _).1 hm') ((pcond_iff_nrd r _).1 hm)
      have hry : ((r : ℚ) : ℍ[ℚ, a, b]) * y ∈ Λ := hO.mul_mem hrΛ hy
      have heq : (⟨(m' : ℍ[ℚ, a, b]) * (m : ℍ[ℚ, a, b]), hO.mul_mem m'.2 m.2⟩ : ↥Λ) =
          ⟨(y : ℍ[ℚ, a, b]) * ((r : ℚ) : ℍ[ℚ, a, b]), hO.mul_mem hy hrΛ⟩ := by
        apply Subtype.ext
        show (m' : ℍ[ℚ, a, b]) * (m : ℍ[ℚ, a, b]) = y * ((r : ℚ) : ℍ[ℚ, a, b])
        rw [hxy, zsmul_eq_mul, ← coe_commutes]; push_cast; ring_nf
      rw [heq, ← aP_mul u ⟨y, hy⟩ ⟨_, hrΛ⟩, hP, aP_one]
    ·
      intro hP
      have gen : ∀ z ∈ Submodule.span ℤ {z : ℍ[ℚ, a, b] | ∃ x ∈ Λ, ∃ x' ∈ Λ,
            (∃ n : ℤ, nrd x = (r : ℚ) * n) ∧ (∃ n : ℤ, nrd x' = (r : ℚ) * n) ∧ z = x * x'},
          ∃ hz : z ∈ Λ, aP u ⟨z, hz⟩ P = u.L.one t := by
        intro z hz
        induction hz using Submodule.span_induction with
        | mem z hz =>
          obtain ⟨x, hx, x', hx', hnx, hnx', rfl⟩ := hz
          refine ⟨hO.mul_mem hx hx', ?_⟩
          rw [← aP_mul u ⟨x, hx⟩ ⟨x', hx'⟩]
          have := hP ⟨x', hx'⟩ ((pcond_iff_nrd r _).2 hnx')
          rw [kill_iff] at this
          exact this ⟨x, hx⟩ ((pcond_iff_nrd r _).2 hnx)
        | zero => exact ⟨Λ.zero_mem, aP_zero u P⟩
        | add x y _ _ hx hy =>
          obtain ⟨hx, hxP⟩ := hx; obtain ⟨hy, hyP⟩ := hy
          refine ⟨Λ.add_mem hx hy, ?_⟩
          have : (⟨x + y, Λ.add_mem hx hy⟩ : ↥Λ) = ⟨x, hx⟩ + ⟨y, hy⟩ := rfl
          rw [this, aP_add, hxP, hyP, u.L.one_mul]
        | smul n x _ hx =>
          obtain ⟨hx, hxP⟩ := hx
          refine ⟨Λ.smul_mem n hx, ?_⟩
          have hmem : (((n : ℚ)) : ℍ[ℚ, a, b]) * x ∈ Λ := hO.mul_mem (intCast_mem hO n) hx
          have : (⟨n • x, Λ.smul_mem n hx⟩ : ↥Λ) = ⟨(((n : ℚ)) : ℍ[ℚ, a, b]) * x, hmem⟩ := by
            apply Subtype.ext; show n • x = (((n : ℚ)) : ℍ[ℚ, a, b]) * x
            rw [zsmul_eq_mul]; push_cast; rfl
          rw [this, ← aP_mul u ⟨_, intCast_mem hO n⟩ ⟨x, hx⟩, hxP, aP_one]
      obtain ⟨h1, h1P⟩ := gen _ (RAM2 1 hO.one_mem)
      have : (⟨(r : ℤ) • (1 : ℍ[ℚ, a, b]), h1⟩ : ↥Λ) = ⟨((r : ℚ) : ℍ[ℚ, a, b]), hrΛ⟩ := by
        apply Subtype.ext; show (r : ℤ) • (1 : ℍ[ℚ, a, b]) = ((r : ℚ) : ℍ[ℚ, a, b])
        rw [zsmul_eq_mul, mul_one]; push_cast; rfl
      rw [← this]; exact h1P

  obtain ⟨χ, hχ, hcomp, -, χmul, χact, χiso⟩ :=
    CerednikDrinfeld.QM.FakeEllipticCurve.exists_unique_comp_eq_of_forall_mapPt_eq_one (AlgebraicClosure ℚ) u u u''
      ρ hρ Mρ Lρ (𝟙 u.A) hid r hrp.pos Dρ Dρ'
      (φ₁ ≫ φ₂) hΦ MΦ LΦ (ψ₂ ≫ ψ₁) hΨ (r * r) (Nat.mul_pos hrp.pos hrp.pos) DΦ DΦ'
      (fun t P => (K t P).1)
  haveI : IsIso χ := χiso (fun t P => (K t P).2)

  have Vρ : ∀ {T : Scheme} (t : T ⟶ Spec (CommRingCat.of (AlgebraicClosure ℚ))) (P : SchemeHomOver t u.f), FactorsThrough u.lev P → FactorsThrough u.lev (mapPt ρ hρ P) :=
    fun t P hP => u.lev_stable _ t P hP
  have VΦ : ∀ {T : Scheme} (t : T ⟶ Spec (CommRingCat.of (AlgebraicClosure ℚ))) (P : SchemeHomOver t u.f), FactorsThrough u.lev P → FactorsThrough u''.lev (mapPt (φ₁ ≫ φ₂) hΦ P) := by
    intro T t P hP; rw [mc φ₁ hφ₁ φ₂ hφ₂]; exact v₂ t _ (v₁ t P hP)
  have Oρ := fun {T : Scheme} (t : T ⟶ Spec (CommRingCat.of (AlgebraicClosure ℚ))) (Q : SchemeHomOver t u.f) =>
    CerednikDrinfeld.QM.FakeEllipticCurve.factorsThrough_lev_iff_exists_mapPt_eq_of_coprime u u ρ hρ Mρ (𝟙 u.A) hid r hcopN Dρ Vρ t Q
  have OΦ := fun {T : Scheme} (t : T ⟶ Spec (CommRingCat.of (AlgebraicClosure ℚ))) (Q : SchemeHomOver t u''.f) =>
    CerednikDrinfeld.QM.FakeEllipticCurve.factorsThrough_lev_iff_exists_mapPt_eq_of_coprime u u'' (φ₁ ≫ φ₂) hΦ MΦ (ψ₂ ≫ ψ₁) hΨ
      (r * r) hcopN2 DΦ VΦ t Q
  have hχρ : ∀ {T : Scheme} {t : T ⟶ Spec (CommRingCat.of (AlgebraicClosure ℚ))} (P : SchemeHomOver t u.f),
      mapPt χ hχ (mapPt ρ hρ P) = mapPt (φ₁ ≫ φ₂) hΦ P :=
    fun P => Subtype.ext (by simp only [mapPt_coe, Category.assoc, hcomp])
  have hχinj : ∀ {T : Scheme} {t : T ⟶ Spec (CommRingCat.of (AlgebraicClosure ℚ))} {P Q : SchemeHomOver t u.f},
      mapPt χ hχ P = mapPt χ hχ Q → P = Q := by
    intro T t P Q h
    apply Subtype.ext
    rw [← cancel_mono χ]
    exact congrArg Subtype.val h
  refine ⟨asIso χ, hχ, ?_, χact, ?_⟩
  · intro T t P Q; exact χmul hχ t P Q
  · intro T t P
    constructor
    · intro hP
      obtain ⟨P₀, hP₀, rfl⟩ := (Oρ t P).1 hP
      show FactorsThrough u''.lev (mapPt χ hχ (mapPt ρ hρ P₀))
      rw [hχρ]; exact VΦ t P₀ hP₀
    · intro hP
      obtain ⟨P₀, hP₀, h0⟩ := (OΦ t _).1 hP
      rw [← hχρ] at h0
      rw [← hχinj h0]; exact Vρ t P₀ hP₀

private theorem _root_.Ws23TL.L1.main
    {N q q' : ℕ} [NeZero N] [Fact q.Prime] [Fact q'.Prime] (hqN : ¬ q ∣ N) (hq'N : ¬ q' ∣ N) (hqq' : q' ≠ q)
    (D : ℕ) [NeZero D] (hD : 2 * N * q * q' ∣ D)
    {a b : ℚ} (hB : IsIndefiniteRamifiedExactlyAt a b q q')
    (Λ : Submodule ℤ ℍ[ℚ, a, b]) (hΛ : IsMaximalOrder Λ)

    (X : Scheme.{0}) [hXint : IsIntegral X]
    (πX : X ⟶ Spec (CommRingCat.of (Localization.Away ((D : ℕ) : ℤ))))
    (pt : ∀ (S : Type) [CommRing S]
      (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of (Localization.Away ((D : ℕ) : ℤ)))),
      FakeEllipticCurve Λ N S → SchemeHomOver s πX)
    (hsmooth : Smooth πX) (hproper : IsProper πX)
    (pt_iso : ∀ (S : Type) [CommRing S] (s : Spec (CommRingCat.of S) ⟶ _) (E E' : FakeEllipticCurve Λ N S),
      FakeEllipticCurve.Iso E E' → pt S s E = pt S s E')
    (pt_pullback : ∀ (S S' : Type) [CommRing S] [CommRing S'] (φ : S →+* S')
      (s : Spec (CommRingCat.of S) ⟶ _) (s' : Spec (CommRingCat.of S') ⟶ _),
      Spec.map (CommRingCat.ofHom φ) ≫ s = s' → ∀ (E : FakeEllipticCurve Λ N S) (E' : FakeEllipticCurve Λ N S'),
      FakeEllipticCurve.IsPullback φ E E' → (pt S' s' E').1 = Spec.map (CommRingCat.ofHom φ) ≫ (pt S s E).1)
    (pt_surjective : ∀ (k : Type) [Field k] [IsAlgClosed k] (s : Spec (CommRingCat.of k) ⟶ _) (P : SchemeHomOver s πX),
      ∃ E : FakeEllipticCurve Λ N k, pt k s E = P)
    (pt_injective : ∀ (k : Type) [Field k] [IsAlgClosed k] (s : Spec (CommRingCat.of k) ⟶ _)
      (E E' : FakeEllipticCurve Λ N k), pt k s E = pt k s E' → FakeEllipticCurve.Iso E E')
    (hsmooth1 : SmoothOfRelativeDimension 1 πX)
    (hgeom : ∀ (k : Type) [Field k] [IsAlgClosed k]
      (s : Spec (CommRingCat.of k) ⟶ Spec (CommRingCat.of (Localization.Away ((D : ℕ) : ℤ)))),
      IsIntegral (CategoryTheory.Limits.pullback πX s))
    (sbar : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ Spec (CommRingCat.of (Localization.Away ((D : ℕ) : ℤ))))
    (sbar_over : sbar ≫ Spec.map (CommRingCat.ofHom (algebraMap ℤ (Localization.Away ((D : ℕ) : ℤ)))) =
      Spec.map (CommRingCat.ofHom (algebraMap ℤ (AlgebraicClosure ℚ))))

    (Fbar : Type) [Field Fbar] [Algebra (AlgebraicClosure ℚ) Fbar]
    [IsCurveOver (AlgebraicClosure ℚ) Fbar] [Algebra.EssFiniteType (AlgebraicClosure ℚ) Fbar]
    (gal : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) →* SemilinearAut (AlgebraicClosure ℚ) Fbar)
    (𝔐 : AlgebraicCurve.CurveModel (AlgebraicClosure ℚ) Fbar)
    (e𝔐 : 𝔐.C ⟶ CategoryTheory.Limits.pullback πX sbar) (he𝔐 : IsIso e𝔐)
    (he𝔐_snd : e𝔐 ≫ CategoryTheory.Limits.pullback.snd πX sbar = 𝔐.toBase)

    (𝕋 : HeckeTower.TowerData q q' Fbar)
    (galT : ∀ ℓ : HeckeTower.AwayPrime q q', (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) →* SemilinearAut (AlgebraicClosure ℚ) (𝕋.F ℓ))
    (W : Fin 2 → SemilinearAut (AlgebraicClosure ℚ) Fbar) (WT : ∀ ℓ : HeckeTower.AwayPrime q q', Fin 2 → SemilinearAut (AlgebraicClosure ℚ) (𝕋.F ℓ))
    (tw : ModuliTowerWitnessD Λ N q q' D Fbar X πX sbar pt 𝔐 e𝔐 gal 𝕋 galT W WT) :
    ∀ (i : Fin 2) (P : Place (AlgebraicClosure ℚ) Fbar), W i • (W i • P) = P := by
  classical
  have place_of_iso : ∀ P Q : Place (AlgebraicClosure ℚ) Fbar, FakeEllipticCurve.Iso (tw.rep P) (tw.rep Q) → P = Q := by
    intro P Q hPQ
    apply AlgebraicCurve.CurveModel.place_eq_of_pointEquivPlace_symm_comp_eq 𝔐 πX sbar e𝔐 he𝔐 he𝔐_snd
    rw [← tw.pt_rep P, ← tw.pt_rep Q, pt_iso _ sbar _ _ hPQ]
  intro i P
  have hrep : ∃ r : ℕ, (r = q ∨ r = q') ∧ ∀ Q : Place (AlgebraicClosure ℚ) Fbar,
      (tw.rep Q).IsAtkinLehnerQuotient r (tw.rep (W i • Q)) := by
    fin_cases i
    · exact ⟨q, Or.inl rfl, tw.W_zero_rep⟩
    · exact ⟨q', Or.inr rfl, tw.W_one_rep⟩
  obtain ⟨r, hr, hW⟩ := hrep
  exact (place_of_iso _ _ (BaseAL.iso_of_alq_comp hqN hq'N hqq' hB Λ hΛ r hr _ _ _ (hW P) (hW (W i • P)))).symm

p2m_export "Ws23TL.L1" "main"
end Ws23TL.L1

namespace Ws23TL
namespace L2

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry NeronModelInfra GoodReductionJacobian IsDedekindDomain AlgebraicCurve QuaternionAlgebra CerednikDrinfeld CerednikDrinfeld.QM
open scoped Quaternion TensorProduct NumberField

universe u

namespace PLW

variable {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} {N : ℕ}

theorem heckeNeighbour_symm {S : Type u} [CommRing S] {ℓ : ℕ} {E E' : FakeEllipticCurve Λ N S}
    (h : FakeEllipticCurve.HeckeNeighbour ℓ E E') : FakeEllipticCurve.HeckeNeighbour ℓ E' E := by
  obtain ⟨φ, hφ, ψ, hψ, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ := h
  exact ⟨ψ, hψ, φ, hφ, h2, h1, h4, h3, h6, h5, fun hℓ => ⟨(h7 hℓ).2, (h7 hℓ).1⟩, h9, h8⟩

end PLW

private theorem _root_.Ws23TL.L2.main
    {N q q' : ℕ} [NeZero N] [Fact q.Prime] [Fact q'.Prime] (hqN : ¬ q ∣ N) (hq'N : ¬ q' ∣ N) (hqq' : q' ≠ q)
    (D : ℕ) [NeZero D] (hD : 2 * N * q * q' ∣ D)
    {a b : ℚ} (hB : IsIndefiniteRamifiedExactlyAt a b q q')
    (Λ : Submodule ℤ ℍ[ℚ, a, b]) (hΛ : IsMaximalOrder Λ)

    (X : Scheme.{0}) [hXint : IsIntegral X]
    (πX : X ⟶ Spec (CommRingCat.of (Localization.Away ((D : ℕ) : ℤ))))
    (pt : ∀ (S : Type) [CommRing S]
      (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of (Localization.Away ((D : ℕ) : ℤ)))),
      FakeEllipticCurve Λ N S → SchemeHomOver s πX)
    (hsmooth : Smooth πX) (hproper : IsProper πX)
    (pt_iso : ∀ (S : Type) [CommRing S] (s : Spec (CommRingCat.of S) ⟶ _) (E E' : FakeEllipticCurve Λ N S),
      FakeEllipticCurve.Iso E E' → pt S s E = pt S s E')
    (pt_pullback : ∀ (S S' : Type) [CommRing S] [CommRing S'] (φ : S →+* S')
      (s : Spec (CommRingCat.of S) ⟶ _) (s' : Spec (CommRingCat.of S') ⟶ _),
      Spec.map (CommRingCat.ofHom φ) ≫ s = s' → ∀ (E : FakeEllipticCurve Λ N S) (E' : FakeEllipticCurve Λ N S'),
      FakeEllipticCurve.IsPullback φ E E' → (pt S' s' E').1 = Spec.map (CommRingCat.ofHom φ) ≫ (pt S s E).1)
    (pt_surjective : ∀ (k : Type) [Field k] [IsAlgClosed k] (s : Spec (CommRingCat.of k) ⟶ _) (P : SchemeHomOver s πX),
      ∃ E : FakeEllipticCurve Λ N k, pt k s E = P)
    (pt_injective : ∀ (k : Type) [Field k] [IsAlgClosed k] (s : Spec (CommRingCat.of k) ⟶ _)
      (E E' : FakeEllipticCurve Λ N k), pt k s E = pt k s E' → FakeEllipticCurve.Iso E E')
    (hsmooth1 : SmoothOfRelativeDimension 1 πX)
    (hgeom : ∀ (k : Type) [Field k] [IsAlgClosed k]
      (s : Spec (CommRingCat.of k) ⟶ Spec (CommRingCat.of (Localization.Away ((D : ℕ) : ℤ)))),
      IsIntegral (CategoryTheory.Limits.pullback πX s))
    (sbar : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ Spec (CommRingCat.of (Localization.Away ((D : ℕ) : ℤ))))
    (sbar_over : sbar ≫ Spec.map (CommRingCat.ofHom (algebraMap ℤ (Localization.Away ((D : ℕ) : ℤ)))) =
      Spec.map (CommRingCat.ofHom (algebraMap ℤ (AlgebraicClosure ℚ))))

    (Fbar : Type) [Field Fbar] [Algebra (AlgebraicClosure ℚ) Fbar]
    [IsCurveOver (AlgebraicClosure ℚ) Fbar] [Algebra.EssFiniteType (AlgebraicClosure ℚ) Fbar]
    (gal : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) →* SemilinearAut (AlgebraicClosure ℚ) Fbar)
    (𝔐 : AlgebraicCurve.CurveModel (AlgebraicClosure ℚ) Fbar)
    (e𝔐 : 𝔐.C ⟶ CategoryTheory.Limits.pullback πX sbar) (he𝔐 : IsIso e𝔐)
    (he𝔐_snd : e𝔐 ≫ CategoryTheory.Limits.pullback.snd πX sbar = 𝔐.toBase)

    (𝕋 : HeckeTower.TowerData q q' Fbar)
    (galT : ∀ ℓ : HeckeTower.AwayPrime q q', (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) →* SemilinearAut (AlgebraicClosure ℚ) (𝕋.F ℓ))
    (W : Fin 2 → SemilinearAut (AlgebraicClosure ℚ) Fbar) (WT : ∀ ℓ : HeckeTower.AwayPrime q q', Fin 2 → SemilinearAut (AlgebraicClosure ℚ) (𝕋.F ℓ))
    (tw : ModuliTowerWitnessD Λ N q q' D Fbar X πX sbar pt 𝔐 e𝔐 gal 𝕋 galT W WT) :
    ∀ P : Place (AlgebraicClosure ℚ) Fbar, W 0 • (W 1 • P) = W 1 • (W 0 • P) := by
  classical

  have place_of_iso : ∀ P Q : Place (AlgebraicClosure ℚ) Fbar, FakeEllipticCurve.Iso (tw.rep P) (tw.rep Q) → P = Q := by
    intro P Q hPQ
    apply AlgebraicCurve.CurveModel.place_eq_of_pointEquivPlace_symm_comp_eq 𝔐 πX sbar e𝔐 he𝔐 he𝔐_snd
    rw [← tw.pt_rep P, ← tw.pt_rep Q, pt_iso _ sbar _ _ hPQ]
  intro P
  have h3 := FakeEllipticCurve.iso_of_isAtkinLehnerQuotient_comm hqN hq'N hqq' hB Λ hΛ
    (tw.rep P) (tw.rep (W 0 • P)) (tw.rep (W 1 • (W 0 • P))) (tw.rep (W 1 • P)) (tw.rep (W 0 • (W 1 • P)))
    (tw.W_zero_rep P) (tw.W_one_rep (W 0 • P)) (tw.W_one_rep P) (tw.W_zero_rep (W 1 • P))
  exact (place_of_iso _ _ h3).symm

p2m_export "Ws23TL.L2" "main"
end Ws23TL.L2

namespace Ws23TL
namespace L3

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry NeronModelInfra GoodReductionJacobian IsDedekindDomain AlgebraicCurve QuaternionAlgebra CerednikDrinfeld CerednikDrinfeld.QM
open scoped Quaternion TensorProduct NumberField

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian
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
p2m_reactivate "P2MW.S_CerednikDrinfeld_QM_ModuliTowerWitness_tower_laws_of_two_mul_dvd.Ws23TL.L3.ALGlue"

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian
open CerednikDrinfeld CerednikDrinfeld.QM CerednikDrinfeld.QM.FakeEllipticCurve QuaternionAlgebra
open scoped Quaternion

theorem BaseAL.iso_of_alq_of_alq
    {N q q' : ℕ} [NeZero N] [Fact q.Prime] [Fact q'.Prime] (hqN : ¬ q ∣ N) (hq'N : ¬ q' ∣ N) (hqq' : q' ≠ q)
    {a b : ℚ} (hB : IsIndefiniteRamifiedExactlyAt a b q q')
    (Λ : Submodule ℤ ℍ[ℚ, a, b]) (hΛ : IsMaximalOrder Λ)
    (r : ℕ) (hr : r = q ∨ r = q')
    (u u' u'' : QM.FakeEllipticCurve Λ N (AlgebraicClosure ℚ))
    (h' : QM.FakeEllipticCurve.IsAtkinLehnerQuotient r u u')
    (h'' : QM.FakeEllipticCurve.IsAtkinLehnerQuotient r u u'') :
    QM.FakeEllipticCurve.Iso u' u'' := by
  classical
  obtain ⟨φ', hφ', ψ', hψ', mφ', mψ', aφ', aψ', c', k', l'⟩ := h'
  obtain ⟨φ'', hφ'', ψ'', hψ'', mφ'', mψ'', aφ'', aψ'', c'', k'', l''⟩ := h''
  have hO : IsOrder Λ := hΛ.isOrder
  have hrprime : r.Prime := by rcases hr with rfl | rfl <;> exact Fact.out
  have hrN : ¬ r ∣ N := by rcases hr with rfl | rfl <;> assumption
  have hcopN : Nat.Coprime r N := (Nat.Prime.coprime_iff_not_dvd hrprime).2 hrN
  have hrΛ : ((r : ℚ) : ℍ[ℚ, a, b]) ∈ Λ := by
    have : ((r : ℚ) : ℍ[ℚ, a, b]) = (r : ℤ) • (1 : ℍ[ℚ, a, b]) := by
      rw [zsmul_eq_mul, mul_one]; norm_cast
    rw [this]; exact Λ.smul_mem _ hO.one_mem

  have nsm : ∀ (E E' : FakeEllipticCurve Λ N (AlgebraicClosure ℚ)) (φ : E.A ⟶ E'.A) (hφ : φ ≫ E'.f = E.f)
      (ψ : E'.A ⟶ E.A) (hψ : ψ ≫ E.f = E'.f) (hc : φ ≫ ψ = E.act ⟨((r : ℚ) : ℍ[ℚ, a, b]), hrΛ⟩)
      {T : Scheme} (t : T ⟶ Spec (CommRingCat.of (AlgebraicClosure ℚ))) (P : SchemeHomOver t E.f),
      mapPt ψ hψ (mapPt φ hφ P) = nsmulPt E.L t r P := by
    intro E E' φ hφ ψ hψ hc T t P
    rw [← pushPt_act_natCast_eq_nsmulPt E hO.one_mem r hrΛ t P]
    apply Subtype.ext
    simp only [mapPt_coe, pushPt, Category.assoc, hc]
  have hψφ' := fun {T : Scheme} (t : T ⟶ Spec (CommRingCat.of (AlgebraicClosure ℚ))) (P : SchemeHomOver t u.f) => nsm u u' φ' hφ' ψ' hψ' (c' hrΛ).1 t P
  have hφψ' := fun {T : Scheme} (t : T ⟶ Spec (CommRingCat.of (AlgebraicClosure ℚ))) (P : SchemeHomOver t u'.f) => nsm u' u ψ' hψ' φ' hφ' (c' hrΛ).2 t P
  have hψφ'' := fun {T : Scheme} (t : T ⟶ Spec (CommRingCat.of (AlgebraicClosure ℚ))) (P : SchemeHomOver t u.f) => nsm u u'' φ'' hφ'' ψ'' hψ'' (c'' hrΛ).1 t P
  have hφψ'' := fun {T : Scheme} (t : T ⟶ Spec (CommRingCat.of (AlgebraicClosure ℚ))) (P : SchemeHomOver t u''.f) => nsm u'' u ψ'' hψ'' φ'' hφ'' (c'' hrΛ).2 t P
  have hker1 : ∀ {T : Scheme} (t : T ⟶ Spec (CommRingCat.of (AlgebraicClosure ℚ))) (P : SchemeHomOver t u.f),
      mapPt φ' hφ' P = u'.L.one t → mapPt φ'' hφ'' P = u''.L.one t :=
    fun t P h => (k'' t P).2 ((k' t P).1 h)
  have hker2 : ∀ {T : Scheme} (t : T ⟶ Spec (CommRingCat.of (AlgebraicClosure ℚ))) (P : SchemeHomOver t u.f),
      mapPt φ'' hφ'' P = u''.L.one t → mapPt φ' hφ' P = u'.L.one t :=
    fun t P h => (k' t P).2 ((k'' t P).1 h)
  obtain ⟨χ, hχ, hφχ, -, χmul, χact, hisoχ⟩ :=
    CerednikDrinfeld.QM.FakeEllipticCurve.exists_unique_comp_eq_of_forall_mapPt_eq_one (AlgebraicClosure ℚ) u u' u''
      φ' hφ' mφ' aφ' ψ' hψ' r hrprime.pos hψφ' hφψ' φ'' hφ'' mφ'' aφ'' ψ'' hψ'' r hrprime.pos hψφ'' hφψ'' hker1
  haveI : IsIso χ := hisoχ hker2
  have LO' := fun {T : Scheme} (t : T ⟶ Spec (CommRingCat.of (AlgebraicClosure ℚ))) (Q : SchemeHomOver t u'.f) =>
    CerednikDrinfeld.QM.FakeEllipticCurve.factorsThrough_lev_iff_exists_mapPt_eq_of_coprime
      u u' φ' hφ' mφ' ψ' hψ' r hcopN hψφ' l' t Q
  have LO'' := fun {T : Scheme} (t : T ⟶ Spec (CommRingCat.of (AlgebraicClosure ℚ))) (Q : SchemeHomOver t u''.f) =>
    CerednikDrinfeld.QM.FakeEllipticCurve.factorsThrough_lev_iff_exists_mapPt_eq_of_coprime
      u u'' φ'' hφ'' mφ'' ψ'' hψ'' r hcopN hψφ'' l'' t Q
  have tχ : ∀ {T : Scheme} {t : T ⟶ Spec (CommRingCat.of (AlgebraicClosure ℚ))} (P : SchemeHomOver t u.f),
      mapPt χ hχ (mapPt φ' hφ' P) = mapPt φ'' hφ'' P :=
    fun P => Subtype.ext (by simp only [mapPt_coe, Category.assoc, hφχ])
  have χinj : ∀ {T : Scheme} {t : T ⟶ Spec (CommRingCat.of (AlgebraicClosure ℚ))} (Q Q' : SchemeHomOver t u'.f),
      mapPt χ hχ Q = mapPt χ hχ Q' → Q = Q' := by
    intro T t Q Q' h
    apply Subtype.ext
    rw [← cancel_mono χ]
    exact congrArg Subtype.val h
  refine ⟨asIso χ, hχ, ?_, χact, ?_⟩
  · intro T t P Q; exact χmul hχ t P Q
  · intro T t Q
    constructor
    · intro hQ
      obtain ⟨P, hP, rfl⟩ := (LO' t Q).1 hQ
      show FactorsThrough u''.lev (mapPt χ hχ (mapPt φ' hφ' P))
      rw [tχ]; exact l'' t P hP
    · intro hQ
      obtain ⟨P, hP, hPe⟩ := (LO'' t (mapPt χ hχ Q)).1 hQ
      have hPQ : mapPt φ' hφ' P = Q := χinj _ _ (by rw [tχ, hPe])
      rw [← hPQ]; exact l' t P hP

private theorem _root_.Ws23TL.L3.main
    {N q q' : ℕ} [NeZero N] [Fact q.Prime] [Fact q'.Prime] (hqN : ¬ q ∣ N) (hq'N : ¬ q' ∣ N) (hqq' : q' ≠ q)
    (D : ℕ) [NeZero D] (hD : 2 * N * q * q' ∣ D)
    {a b : ℚ} (hB : IsIndefiniteRamifiedExactlyAt a b q q')
    (Λ : Submodule ℤ ℍ[ℚ, a, b]) (hΛ : IsMaximalOrder Λ)

    (X : Scheme.{0}) [hXint : IsIntegral X]
    (πX : X ⟶ Spec (CommRingCat.of (Localization.Away ((D : ℕ) : ℤ))))
    (pt : ∀ (S : Type) [CommRing S]
      (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of (Localization.Away ((D : ℕ) : ℤ)))),
      FakeEllipticCurve Λ N S → SchemeHomOver s πX)
    (hsmooth : Smooth πX) (hproper : IsProper πX)
    (pt_iso : ∀ (S : Type) [CommRing S] (s : Spec (CommRingCat.of S) ⟶ _) (E E' : FakeEllipticCurve Λ N S),
      FakeEllipticCurve.Iso E E' → pt S s E = pt S s E')
    (pt_pullback : ∀ (S S' : Type) [CommRing S] [CommRing S'] (φ : S →+* S')
      (s : Spec (CommRingCat.of S) ⟶ _) (s' : Spec (CommRingCat.of S') ⟶ _),
      Spec.map (CommRingCat.ofHom φ) ≫ s = s' → ∀ (E : FakeEllipticCurve Λ N S) (E' : FakeEllipticCurve Λ N S'),
      FakeEllipticCurve.IsPullback φ E E' → (pt S' s' E').1 = Spec.map (CommRingCat.ofHom φ) ≫ (pt S s E).1)
    (pt_surjective : ∀ (k : Type) [Field k] [IsAlgClosed k] (s : Spec (CommRingCat.of k) ⟶ _) (P : SchemeHomOver s πX),
      ∃ E : FakeEllipticCurve Λ N k, pt k s E = P)
    (pt_injective : ∀ (k : Type) [Field k] [IsAlgClosed k] (s : Spec (CommRingCat.of k) ⟶ _)
      (E E' : FakeEllipticCurve Λ N k), pt k s E = pt k s E' → FakeEllipticCurve.Iso E E')
    (hsmooth1 : SmoothOfRelativeDimension 1 πX)
    (hgeom : ∀ (k : Type) [Field k] [IsAlgClosed k]
      (s : Spec (CommRingCat.of k) ⟶ Spec (CommRingCat.of (Localization.Away ((D : ℕ) : ℤ)))),
      IsIntegral (CategoryTheory.Limits.pullback πX s))
    (sbar : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ Spec (CommRingCat.of (Localization.Away ((D : ℕ) : ℤ))))
    (sbar_over : sbar ≫ Spec.map (CommRingCat.ofHom (algebraMap ℤ (Localization.Away ((D : ℕ) : ℤ)))) =
      Spec.map (CommRingCat.ofHom (algebraMap ℤ (AlgebraicClosure ℚ))))

    (Fbar : Type) [Field Fbar] [Algebra (AlgebraicClosure ℚ) Fbar]
    [IsCurveOver (AlgebraicClosure ℚ) Fbar] [Algebra.EssFiniteType (AlgebraicClosure ℚ) Fbar]
    (gal : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) →* SemilinearAut (AlgebraicClosure ℚ) Fbar)
    (𝔐 : AlgebraicCurve.CurveModel (AlgebraicClosure ℚ) Fbar)
    (e𝔐 : 𝔐.C ⟶ CategoryTheory.Limits.pullback πX sbar) (he𝔐 : IsIso e𝔐)
    (he𝔐_snd : e𝔐 ≫ CategoryTheory.Limits.pullback.snd πX sbar = 𝔐.toBase)

    (𝕋 : HeckeTower.TowerData q q' Fbar)
    (galT : ∀ ℓ : HeckeTower.AwayPrime q q', (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) →* SemilinearAut (AlgebraicClosure ℚ) (𝕋.F ℓ))
    (W : Fin 2 → SemilinearAut (AlgebraicClosure ℚ) Fbar) (WT : ∀ ℓ : HeckeTower.AwayPrime q q', Fin 2 → SemilinearAut (AlgebraicClosure ℚ) (𝕋.F ℓ))
    (tw : ModuliTowerWitnessD Λ N q q' D Fbar X πX sbar pt 𝔐 e𝔐 gal 𝕋 galT W WT) :
    ∀ (i : Fin 2) (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (P : Place (AlgebraicClosure ℚ) Fbar),
      W i • (gal σ • P) = gal σ • (W i • P) := by
  classical
  have place_of_iso : ∀ P Q : Place (AlgebraicClosure ℚ) Fbar, FakeEllipticCurve.Iso (tw.rep P) (tw.rep Q) → P = Q := by
    intro P Q hPQ
    apply AlgebraicCurve.CurveModel.place_eq_of_pointEquivPlace_symm_comp_eq 𝔐 πX sbar e𝔐 he𝔐 he𝔐_snd
    rw [← tw.pt_rep P, ← tw.pt_rep Q, pt_iso _ sbar _ _ hPQ]
  intro i σ P
  have hrep : ∃ r : ℕ, (r = q ∨ r = q') ∧ ∀ Q : Place (AlgebraicClosure ℚ) Fbar,
      (tw.rep Q).IsAtkinLehnerQuotient r (tw.rep (W i • Q)) := by
    fin_cases i
    · exact ⟨q, Or.inl rfl, tw.W_zero_rep⟩
    · exact ⟨q', Or.inr rfl, tw.W_one_rep⟩
  obtain ⟨r, hr, hW⟩ := hrep
  obtain ⟨E, hE, hEiso⟩ := tw.gal_rep σ P
  obtain ⟨E₁, hE₁, hE₁iso⟩ := tw.gal_rep σ (W i • P)
  have hbc := FakeEllipticCurve.isAtkinLehnerQuotient_of_isPullback
    (σ : AlgebraicClosure ℚ →+* AlgebraicClosure ℚ) r (tw.rep P) (tw.rep (W i • P)) E E₁ hE hE₁ (hW P)
  have hcg := ALGlue.isAtkinLehnerQuotient_congr r hbc hEiso hE₁iso
  exact (place_of_iso _ _ (BaseAL.iso_of_alq_of_alq hqN hq'N hqq' hB Λ hΛ r hr _ _ _ hcg (hW (gal σ • P)))).symm

p2m_export "Ws23TL.L3" "main"
end Ws23TL.L3
p2m_reactivate "P2MW.S_CerednikDrinfeld_QM_ModuliTowerWitness_tower_laws_of_two_mul_dvd.Ws23TL.L3.ALGlue P2MW.S_CerednikDrinfeld_QM_ModuliTowerWitness_tower_laws_of_two_mul_dvd.Ws23TL P2MW.S_CerednikDrinfeld_QM_ModuliTowerWitness_tower_laws_of_two_mul_dvd.Ws23TL.L3"
p2m_reactivate "P2MW.S_CerednikDrinfeld_QM_ModuliTowerWitness_tower_laws_of_two_mul_dvd.Ws23TL.L3.ALGlue P2MW.S_CerednikDrinfeld_QM_ModuliTowerWitness_tower_laws_of_two_mul_dvd.Ws23TL"

namespace Ws23TL
namespace L4

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry NeronModelInfra GoodReductionJacobian IsDedekindDomain AlgebraicCurve QuaternionAlgebra CerednikDrinfeld CerednikDrinfeld.QM
open scoped Quaternion TensorProduct NumberField

private theorem _root_.Ws23TL.L4.main
    {N q q' : ℕ} [NeZero N] [Fact q.Prime] [Fact q'.Prime] (hqN : ¬ q ∣ N) (hq'N : ¬ q' ∣ N) (hqq' : q' ≠ q)
    (D : ℕ) [NeZero D] (hD : 2 * N * q * q' ∣ D)
    {a b : ℚ} (hB : IsIndefiniteRamifiedExactlyAt a b q q')
    (Λ : Submodule ℤ ℍ[ℚ, a, b]) (hΛ : IsMaximalOrder Λ)

    (X : Scheme.{0}) [hXint : IsIntegral X]
    (πX : X ⟶ Spec (CommRingCat.of (Localization.Away ((D : ℕ) : ℤ))))
    (pt : ∀ (S : Type) [CommRing S]
      (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of (Localization.Away ((D : ℕ) : ℤ)))),
      FakeEllipticCurve Λ N S → SchemeHomOver s πX)
    (hsmooth : Smooth πX) (hproper : IsProper πX)
    (pt_iso : ∀ (S : Type) [CommRing S] (s : Spec (CommRingCat.of S) ⟶ _) (E E' : FakeEllipticCurve Λ N S),
      FakeEllipticCurve.Iso E E' → pt S s E = pt S s E')
    (pt_pullback : ∀ (S S' : Type) [CommRing S] [CommRing S'] (φ : S →+* S')
      (s : Spec (CommRingCat.of S) ⟶ _) (s' : Spec (CommRingCat.of S') ⟶ _),
      Spec.map (CommRingCat.ofHom φ) ≫ s = s' → ∀ (E : FakeEllipticCurve Λ N S) (E' : FakeEllipticCurve Λ N S'),
      FakeEllipticCurve.IsPullback φ E E' → (pt S' s' E').1 = Spec.map (CommRingCat.ofHom φ) ≫ (pt S s E).1)
    (pt_surjective : ∀ (k : Type) [Field k] [IsAlgClosed k] (s : Spec (CommRingCat.of k) ⟶ _) (P : SchemeHomOver s πX),
      ∃ E : FakeEllipticCurve Λ N k, pt k s E = P)
    (pt_injective : ∀ (k : Type) [Field k] [IsAlgClosed k] (s : Spec (CommRingCat.of k) ⟶ _)
      (E E' : FakeEllipticCurve Λ N k), pt k s E = pt k s E' → FakeEllipticCurve.Iso E E')
    (hsmooth1 : SmoothOfRelativeDimension 1 πX)
    (hgeom : ∀ (k : Type) [Field k] [IsAlgClosed k]
      (s : Spec (CommRingCat.of k) ⟶ Spec (CommRingCat.of (Localization.Away ((D : ℕ) : ℤ)))),
      IsIntegral (CategoryTheory.Limits.pullback πX s))
    (sbar : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ Spec (CommRingCat.of (Localization.Away ((D : ℕ) : ℤ))))
    (sbar_over : sbar ≫ Spec.map (CommRingCat.ofHom (algebraMap ℤ (Localization.Away ((D : ℕ) : ℤ)))) =
      Spec.map (CommRingCat.ofHom (algebraMap ℤ (AlgebraicClosure ℚ))))

    (Fbar : Type) [Field Fbar] [Algebra (AlgebraicClosure ℚ) Fbar]
    [IsCurveOver (AlgebraicClosure ℚ) Fbar] [Algebra.EssFiniteType (AlgebraicClosure ℚ) Fbar]
    (gal : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) →* SemilinearAut (AlgebraicClosure ℚ) Fbar)
    (𝔐 : AlgebraicCurve.CurveModel (AlgebraicClosure ℚ) Fbar)
    (e𝔐 : 𝔐.C ⟶ CategoryTheory.Limits.pullback πX sbar) (he𝔐 : IsIso e𝔐)
    (he𝔐_snd : e𝔐 ≫ CategoryTheory.Limits.pullback.snd πX sbar = 𝔐.toBase)

    (𝕋 : HeckeTower.TowerData q q' Fbar)
    (galT : ∀ ℓ : HeckeTower.AwayPrime q q', (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) →* SemilinearAut (AlgebraicClosure ℚ) (𝕋.F ℓ))
    (W : Fin 2 → SemilinearAut (AlgebraicClosure ℚ) Fbar) (WT : ∀ ℓ : HeckeTower.AwayPrime q q', Fin 2 → SemilinearAut (AlgebraicClosure ℚ) (𝕋.F ℓ))
    (tw : ModuliTowerWitnessD Λ N q q' D Fbar X πX sbar pt 𝔐 e𝔐 gal 𝕋 galT W WT) :
    ∀ (ℓ : HeckeTower.AwayPrime q q') (i : Fin 2) (P : Place (AlgebraicClosure ℚ) (𝕋.F ℓ)),
      WT ℓ i • (WT ℓ i • P) = P := by
  intro ℓ i P
  symm
  apply tw.repT_injective ℓ
  fin_cases i
  · exact CerednikDrinfeld.QM.FakeEllipticCurve.WithExtraLevel.iso_of_isAtkinLehnerQuotient_comp hqN hq'N hqq' hB Λ hΛ
      (ℓ.1 : ℕ) ℓ.1.2 ℓ.2.1 ℓ.2.2 q (Or.inl rfl) _ _ _ (tw.WT_zero_rep ℓ P) (tw.WT_zero_rep ℓ (WT ℓ 0 • P))
  · exact CerednikDrinfeld.QM.FakeEllipticCurve.WithExtraLevel.iso_of_isAtkinLehnerQuotient_comp hqN hq'N hqq' hB Λ hΛ
      (ℓ.1 : ℕ) ℓ.1.2 ℓ.2.1 ℓ.2.2 q' (Or.inr rfl) _ _ _ (tw.WT_one_rep ℓ P) (tw.WT_one_rep ℓ (WT ℓ 1 • P))

p2m_export "Ws23TL.L4" "main"
end Ws23TL.L4
p2m_reactivate "P2MW.S_CerednikDrinfeld_QM_ModuliTowerWitness_tower_laws_of_two_mul_dvd.Ws23TL.L3.ALGlue P2MW.S_CerednikDrinfeld_QM_ModuliTowerWitness_tower_laws_of_two_mul_dvd.Ws23TL P2MW.S_CerednikDrinfeld_QM_ModuliTowerWitness_tower_laws_of_two_mul_dvd.Ws23TL.L3"
p2m_reactivate "P2MW.S_CerednikDrinfeld_QM_ModuliTowerWitness_tower_laws_of_two_mul_dvd.Ws23TL.L3.ALGlue P2MW.S_CerednikDrinfeld_QM_ModuliTowerWitness_tower_laws_of_two_mul_dvd.Ws23TL P2MW.S_CerednikDrinfeld_QM_ModuliTowerWitness_tower_laws_of_two_mul_dvd.Ws23TL.L3"

namespace Ws23TL
namespace L5

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry NeronModelInfra GoodReductionJacobian IsDedekindDomain AlgebraicCurve QuaternionAlgebra CerednikDrinfeld CerednikDrinfeld.QM
open scoped Quaternion TensorProduct NumberField

private theorem _root_.Ws23TL.L5.main
    {N q q' : ℕ} [NeZero N] [Fact q.Prime] [Fact q'.Prime] (hqN : ¬ q ∣ N) (hq'N : ¬ q' ∣ N) (hqq' : q' ≠ q)
    (D : ℕ) [NeZero D] (hD : 2 * N * q * q' ∣ D)
    {a b : ℚ} (hB : IsIndefiniteRamifiedExactlyAt a b q q')
    (Λ : Submodule ℤ ℍ[ℚ, a, b]) (hΛ : IsMaximalOrder Λ)

    (X : Scheme.{0}) [hXint : IsIntegral X]
    (πX : X ⟶ Spec (CommRingCat.of (Localization.Away ((D : ℕ) : ℤ))))
    (pt : ∀ (S : Type) [CommRing S]
      (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of (Localization.Away ((D : ℕ) : ℤ)))),
      FakeEllipticCurve Λ N S → SchemeHomOver s πX)
    (hsmooth : Smooth πX) (hproper : IsProper πX)
    (pt_iso : ∀ (S : Type) [CommRing S] (s : Spec (CommRingCat.of S) ⟶ _) (E E' : FakeEllipticCurve Λ N S),
      FakeEllipticCurve.Iso E E' → pt S s E = pt S s E')
    (pt_pullback : ∀ (S S' : Type) [CommRing S] [CommRing S'] (φ : S →+* S')
      (s : Spec (CommRingCat.of S) ⟶ _) (s' : Spec (CommRingCat.of S') ⟶ _),
      Spec.map (CommRingCat.ofHom φ) ≫ s = s' → ∀ (E : FakeEllipticCurve Λ N S) (E' : FakeEllipticCurve Λ N S'),
      FakeEllipticCurve.IsPullback φ E E' → (pt S' s' E').1 = Spec.map (CommRingCat.ofHom φ) ≫ (pt S s E).1)
    (pt_surjective : ∀ (k : Type) [Field k] [IsAlgClosed k] (s : Spec (CommRingCat.of k) ⟶ _) (P : SchemeHomOver s πX),
      ∃ E : FakeEllipticCurve Λ N k, pt k s E = P)
    (pt_injective : ∀ (k : Type) [Field k] [IsAlgClosed k] (s : Spec (CommRingCat.of k) ⟶ _)
      (E E' : FakeEllipticCurve Λ N k), pt k s E = pt k s E' → FakeEllipticCurve.Iso E E')
    (hsmooth1 : SmoothOfRelativeDimension 1 πX)
    (hgeom : ∀ (k : Type) [Field k] [IsAlgClosed k]
      (s : Spec (CommRingCat.of k) ⟶ Spec (CommRingCat.of (Localization.Away ((D : ℕ) : ℤ)))),
      IsIntegral (CategoryTheory.Limits.pullback πX s))
    (sbar : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ Spec (CommRingCat.of (Localization.Away ((D : ℕ) : ℤ))))
    (sbar_over : sbar ≫ Spec.map (CommRingCat.ofHom (algebraMap ℤ (Localization.Away ((D : ℕ) : ℤ)))) =
      Spec.map (CommRingCat.ofHom (algebraMap ℤ (AlgebraicClosure ℚ))))

    (Fbar : Type) [Field Fbar] [Algebra (AlgebraicClosure ℚ) Fbar]
    [IsCurveOver (AlgebraicClosure ℚ) Fbar] [Algebra.EssFiniteType (AlgebraicClosure ℚ) Fbar]
    (gal : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) →* SemilinearAut (AlgebraicClosure ℚ) Fbar)
    (𝔐 : AlgebraicCurve.CurveModel (AlgebraicClosure ℚ) Fbar)
    (e𝔐 : 𝔐.C ⟶ CategoryTheory.Limits.pullback πX sbar) (he𝔐 : IsIso e𝔐)
    (he𝔐_snd : e𝔐 ≫ CategoryTheory.Limits.pullback.snd πX sbar = 𝔐.toBase)

    (𝕋 : HeckeTower.TowerData q q' Fbar)
    (galT : ∀ ℓ : HeckeTower.AwayPrime q q', (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) →* SemilinearAut (AlgebraicClosure ℚ) (𝕋.F ℓ))
    (W : Fin 2 → SemilinearAut (AlgebraicClosure ℚ) Fbar) (WT : ∀ ℓ : HeckeTower.AwayPrime q q', Fin 2 → SemilinearAut (AlgebraicClosure ℚ) (𝕋.F ℓ))
    (tw : ModuliTowerWitnessD Λ N q q' D Fbar X πX sbar pt 𝔐 e𝔐 gal 𝕋 galT W WT) :
    ∀ (ℓ : HeckeTower.AwayPrime q q') (P : Place (AlgebraicClosure ℚ) (𝕋.F ℓ)),
      WT ℓ 0 • (WT ℓ 1 • P) = WT ℓ 1 • (WT ℓ 0 • P) := by
  intro ℓ P
  symm
  apply tw.repT_injective ℓ
  exact CerednikDrinfeld.QM.FakeEllipticCurve.WithExtraLevel.iso_of_isAtkinLehnerQuotient_comm hqN hq'N hqq' hB Λ hΛ
    (ℓ.1 : ℕ) ℓ.1.2 ℓ.2.1 ℓ.2.2 (tw.repT ℓ P) _ _ _ _
    (tw.WT_zero_rep ℓ P) (tw.WT_one_rep ℓ (WT ℓ 0 • P)) (tw.WT_one_rep ℓ P) (tw.WT_zero_rep ℓ (WT ℓ 1 • P))

p2m_export "Ws23TL.L5" "main"
end Ws23TL.L5
p2m_reactivate "P2MW.S_CerednikDrinfeld_QM_ModuliTowerWitness_tower_laws_of_two_mul_dvd.Ws23TL.L3.ALGlue P2MW.S_CerednikDrinfeld_QM_ModuliTowerWitness_tower_laws_of_two_mul_dvd.Ws23TL P2MW.S_CerednikDrinfeld_QM_ModuliTowerWitness_tower_laws_of_two_mul_dvd.Ws23TL.L3"
p2m_reactivate "P2MW.S_CerednikDrinfeld_QM_ModuliTowerWitness_tower_laws_of_two_mul_dvd.Ws23TL.L3.ALGlue P2MW.S_CerednikDrinfeld_QM_ModuliTowerWitness_tower_laws_of_two_mul_dvd.Ws23TL P2MW.S_CerednikDrinfeld_QM_ModuliTowerWitness_tower_laws_of_two_mul_dvd.Ws23TL.L3"

namespace Ws23TL
namespace L6

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry NeronModelInfra GoodReductionJacobian IsDedekindDomain AlgebraicCurve QuaternionAlgebra CerednikDrinfeld CerednikDrinfeld.QM
open scoped Quaternion TensorProduct NumberField

private theorem _root_.Ws23TL.L6.main
    {N q q' : ℕ} [NeZero N] [Fact q.Prime] [Fact q'.Prime] (hqN : ¬ q ∣ N) (hq'N : ¬ q' ∣ N) (hqq' : q' ≠ q)
    (D : ℕ) [NeZero D] (hD : 2 * N * q * q' ∣ D)
    {a b : ℚ} (hB : IsIndefiniteRamifiedExactlyAt a b q q')
    (Λ : Submodule ℤ ℍ[ℚ, a, b]) (hΛ : IsMaximalOrder Λ)

    (X : Scheme.{0}) [hXint : IsIntegral X]
    (πX : X ⟶ Spec (CommRingCat.of (Localization.Away ((D : ℕ) : ℤ))))
    (pt : ∀ (S : Type) [CommRing S]
      (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of (Localization.Away ((D : ℕ) : ℤ)))),
      FakeEllipticCurve Λ N S → SchemeHomOver s πX)
    (hsmooth : Smooth πX) (hproper : IsProper πX)
    (pt_iso : ∀ (S : Type) [CommRing S] (s : Spec (CommRingCat.of S) ⟶ _) (E E' : FakeEllipticCurve Λ N S),
      FakeEllipticCurve.Iso E E' → pt S s E = pt S s E')
    (pt_pullback : ∀ (S S' : Type) [CommRing S] [CommRing S'] (φ : S →+* S')
      (s : Spec (CommRingCat.of S) ⟶ _) (s' : Spec (CommRingCat.of S') ⟶ _),
      Spec.map (CommRingCat.ofHom φ) ≫ s = s' → ∀ (E : FakeEllipticCurve Λ N S) (E' : FakeEllipticCurve Λ N S'),
      FakeEllipticCurve.IsPullback φ E E' → (pt S' s' E').1 = Spec.map (CommRingCat.ofHom φ) ≫ (pt S s E).1)
    (pt_surjective : ∀ (k : Type) [Field k] [IsAlgClosed k] (s : Spec (CommRingCat.of k) ⟶ _) (P : SchemeHomOver s πX),
      ∃ E : FakeEllipticCurve Λ N k, pt k s E = P)
    (pt_injective : ∀ (k : Type) [Field k] [IsAlgClosed k] (s : Spec (CommRingCat.of k) ⟶ _)
      (E E' : FakeEllipticCurve Λ N k), pt k s E = pt k s E' → FakeEllipticCurve.Iso E E')
    (hsmooth1 : SmoothOfRelativeDimension 1 πX)
    (hgeom : ∀ (k : Type) [Field k] [IsAlgClosed k]
      (s : Spec (CommRingCat.of k) ⟶ Spec (CommRingCat.of (Localization.Away ((D : ℕ) : ℤ)))),
      IsIntegral (CategoryTheory.Limits.pullback πX s))
    (sbar : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ Spec (CommRingCat.of (Localization.Away ((D : ℕ) : ℤ))))
    (sbar_over : sbar ≫ Spec.map (CommRingCat.ofHom (algebraMap ℤ (Localization.Away ((D : ℕ) : ℤ)))) =
      Spec.map (CommRingCat.ofHom (algebraMap ℤ (AlgebraicClosure ℚ))))

    (Fbar : Type) [Field Fbar] [Algebra (AlgebraicClosure ℚ) Fbar]
    [IsCurveOver (AlgebraicClosure ℚ) Fbar] [Algebra.EssFiniteType (AlgebraicClosure ℚ) Fbar]
    (gal : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) →* SemilinearAut (AlgebraicClosure ℚ) Fbar)
    (𝔐 : AlgebraicCurve.CurveModel (AlgebraicClosure ℚ) Fbar)
    (e𝔐 : 𝔐.C ⟶ CategoryTheory.Limits.pullback πX sbar) (he𝔐 : IsIso e𝔐)
    (he𝔐_snd : e𝔐 ≫ CategoryTheory.Limits.pullback.snd πX sbar = 𝔐.toBase)

    (𝕋 : HeckeTower.TowerData q q' Fbar)
    (galT : ∀ ℓ : HeckeTower.AwayPrime q q', (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) →* SemilinearAut (AlgebraicClosure ℚ) (𝕋.F ℓ))
    (W : Fin 2 → SemilinearAut (AlgebraicClosure ℚ) Fbar) (WT : ∀ ℓ : HeckeTower.AwayPrime q q', Fin 2 → SemilinearAut (AlgebraicClosure ℚ) (𝕋.F ℓ))
    (tw : ModuliTowerWitnessD Λ N q q' D Fbar X πX sbar pt 𝔐 e𝔐 gal 𝕋 galT W WT) :
    ∀ (ℓ : HeckeTower.AwayPrime q q') (i : Fin 2) (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)
      (P : Place (AlgebraicClosure ℚ) (𝕋.F ℓ)), WT ℓ i • (galT ℓ σ • P) = galT ℓ σ • (WT ℓ i • P) := by
  intro ℓ i σ P
  obtain ⟨u, g, hg, h1, h2, h3, hiso⟩ := tw.galT_rep ℓ σ P
  obtain ⟨u₁, g₁, hg₁, k1, k2, k3, hiso₁⟩ := tw.galT_rep ℓ σ (WT ℓ i • P)
  have hr : ∃ r : ℕ, (r = q ∨ r = q') ∧ ∀ Q : Place (AlgebraicClosure ℚ) (𝕋.F ℓ),
      FakeEllipticCurve.WithExtraLevel.IsAtkinLehnerQuotient r (tw.repT ℓ Q) (tw.repT ℓ (WT ℓ i • Q)) := by
    fin_cases i
    · exact ⟨q, Or.inl rfl, tw.WT_zero_rep ℓ⟩
    · exact ⟨q', Or.inr rfl, tw.WT_one_rep ℓ⟩
  obtain ⟨r, hr, hW⟩ := hr
  have hB' := CerednikDrinfeld.QM.FakeEllipticCurve.WithExtraLevel.isAtkinLehnerQuotient_of_isPullback
    (σ : AlgebraicClosure ℚ →+* AlgebraicClosure ℚ) r (tw.repT ℓ P) (tw.repT ℓ (WT ℓ i • P)) u u₁
    ⟨g, hg, h1, h2, h3⟩ ⟨g₁, hg₁, k1, k2, k3⟩ (hW P)
  have hC := CerednikDrinfeld.QM.FakeEllipticCurve.WithExtraLevel.isAtkinLehnerQuotient_of_iso_of_iso r u u₁ _ _ hB' hiso hiso₁
  have hE := CerednikDrinfeld.QM.FakeEllipticCurve.WithExtraLevel.iso_of_isAtkinLehnerQuotient_of_isAtkinLehnerQuotient
    hqN hq'N hqq' hB Λ hΛ (ℓ.1 : ℕ) ℓ.1.2 ℓ.2.1 ℓ.2.2 r hr _ _ _ hC (hW (galT ℓ σ • P))
  exact (tw.repT_injective ℓ _ _ hE).symm

p2m_export "Ws23TL.L6" "main"
end Ws23TL.L6
p2m_reactivate "P2MW.S_CerednikDrinfeld_QM_ModuliTowerWitness_tower_laws_of_two_mul_dvd.Ws23TL.L3.ALGlue P2MW.S_CerednikDrinfeld_QM_ModuliTowerWitness_tower_laws_of_two_mul_dvd.Ws23TL P2MW.S_CerednikDrinfeld_QM_ModuliTowerWitness_tower_laws_of_two_mul_dvd.Ws23TL.L3"
p2m_reactivate "P2MW.S_CerednikDrinfeld_QM_ModuliTowerWitness_tower_laws_of_two_mul_dvd.Ws23TL.L3.ALGlue P2MW.S_CerednikDrinfeld_QM_ModuliTowerWitness_tower_laws_of_two_mul_dvd.Ws23TL P2MW.S_CerednikDrinfeld_QM_ModuliTowerWitness_tower_laws_of_two_mul_dvd.Ws23TL.L3"

namespace Ws23TL
namespace L7

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry NeronModelInfra GoodReductionJacobian IsDedekindDomain AlgebraicCurve QuaternionAlgebra CerednikDrinfeld CerednikDrinfeld.QM
open scoped Quaternion TensorProduct NumberField

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian
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
p2m_reactivate "P2MW.S_CerednikDrinfeld_QM_ModuliTowerWitness_tower_laws_of_two_mul_dvd.Ws23TL.L3.ALGlue P2MW.S_CerednikDrinfeld_QM_ModuliTowerWitness_tower_laws_of_two_mul_dvd.Ws23TL P2MW.S_CerednikDrinfeld_QM_ModuliTowerWitness_tower_laws_of_two_mul_dvd.Ws23TL.L3"

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
p2m_reactivate "P2MW.S_CerednikDrinfeld_QM_ModuliTowerWitness_tower_laws_of_two_mul_dvd.Ws23TL.L3.ALGlue P2MW.S_CerednikDrinfeld_QM_ModuliTowerWitness_tower_laws_of_two_mul_dvd.Ws23TL P2MW.S_CerednikDrinfeld_QM_ModuliTowerWitness_tower_laws_of_two_mul_dvd.Ws23TL.L3 P2MW.S_CerednikDrinfeld_QM_ModuliTowerWitness_tower_laws_of_two_mul_dvd.Ws23TL.L7.ALGlue"

namespace ALTBaseChange

open CerednikDrinfeld.QM.FakeEllipticCurve

theorem factorsThrough_levK_of_exists_comp_eq
    {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} {N ℓ : ℕ} {S S' : Type u} [CommRing S] [CommRing S'] (φ : S →+* S')
    (u : WithExtraLevel Λ N ℓ S) (u' : WithExtraLevel Λ N ℓ S')
    (g : u'.1.A ⟶ u.1.A) (hg : CategoryTheory.IsPullback g u'.1.f u.1.f (Spec.map (CommRingCat.ofHom φ)))
    (hg_levK : ∀ {T : Scheme.{u}} (t' : T ⟶ Spec (CommRingCat.of S')) (P : SchemeHomOver t' u'.1.f),
      FactorsThrough u'.2.levK P → ∃ P₀ : T ⟶ u.2.K, P₀ ≫ u.2.levK = P.1 ≫ g)
    {T : Scheme.{u}} (t' : T ⟶ Spec (CommRingCat.of S')) (P : SchemeHomOver t' u'.1.f)
    (hP : ∃ P₀ : T ⟶ u.2.K, P₀ ≫ u.2.levK = P.1 ≫ g) : FactorsThrough u'.2.levK P := by
  classical
  haveI := u.2.levK_closed
  haveI := u'.2.levK_closed
  haveI := u.2.levK_finite
  haveI := u.2.levK_flat
  haveI := u.2.levK_finitePresentation
  haveI := u'.2.levK_finite
  haveI := u'.2.levK_flat
  haveI := u'.2.levK_finitePresentation
  have hB : IsPullback (pullback.fst u.2.levK g) (pullback.snd u.2.levK g ≫ u'.1.f) (u.2.levK ≫ u.1.f)
      (Spec.map (CommRingCat.ofHom φ)) :=
    ((IsPullback.of_hasPullback u.2.levK g).flip.paste_horiz hg.flip).flip
  haveI hYfin : IsFinite (pullback.snd u.2.levK g ≫ u'.1.f) := MorphismProperty.of_isPullback hB u.2.levK_finite
  haveI hYfl : Flat (pullback.snd u.2.levK g ≫ u'.1.f) := MorphismProperty.of_isPullback hB u.2.levK_flat
  haveI hYfp : LocallyOfFinitePresentation (pullback.snd u.2.levK g ≫ u'.1.f) :=
    MorphismProperty.of_isPullback hB u.2.levK_finitePresentation
  obtain ⟨c₀, hc₀⟩ := hg_levK (u'.2.levK ≫ u'.1.f) ⟨u'.2.levK, rfl⟩ ⟨𝟙 _, Category.id_comp _⟩
  let i : u'.2.K ⟶ pullback u.2.levK g := pullback.lift c₀ u'.2.levK hc₀
  have hi : i ≫ pullback.snd u.2.levK g = u'.2.levK := pullback.lift_snd _ _ _
  haveI : IsClosedImmersion (i ≫ pullback.snd u.2.levK g) := by rw [hi]; exact u'.2.levK_closed
  haveI : IsClosedImmersion i := IsClosedImmersion.of_comp_isClosedImmersion i (pullback.snd u.2.levK g)
  have hw : i ≫ (pullback.snd u.2.levK g ≫ u'.1.f) = u'.2.levK ≫ u'.1.f := by rw [← Category.assoc, hi]
  have hrk : ∀ s : ↥(Spec (CommRingCat.of S')),
      (u'.2.levK ≫ u'.1.f).finrank s = (pullback.snd u.2.levK g ≫ u'.1.f).finrank s := by
    intro s
    rw [u'.2.levK_rank s, Scheme.Hom.finrank_of_isPullback _ _ _ _ hB s, u.2.levK_rank]
  haveI hiso : IsIso i :=
    AlgebraicGeometry.isIso_of_isClosedImmersion_of_finrank_comp_eq i (pullback.snd u.2.levK g ≫ u'.1.f) (u'.2.levK ≫ u'.1.f)
      hw hrk
  obtain ⟨P₀, hP₀⟩ := hP
  refine ⟨pullback.lift P₀ P.1 hP₀ ≫ inv i, ?_⟩
  rw [Category.assoc, ← hi, IsIso.inv_hom_id_assoc, pullback.lift_snd]

end ALTBaseChange
p2m_reactivate "P2MW.S_CerednikDrinfeld_QM_ModuliTowerWitness_tower_laws_of_two_mul_dvd.Ws23TL.L3.ALGlue P2MW.S_CerednikDrinfeld_QM_ModuliTowerWitness_tower_laws_of_two_mul_dvd.Ws23TL P2MW.S_CerednikDrinfeld_QM_ModuliTowerWitness_tower_laws_of_two_mul_dvd.Ws23TL.L3 P2MW.S_CerednikDrinfeld_QM_ModuliTowerWitness_tower_laws_of_two_mul_dvd.Ws23TL.L7.ALGlue"

namespace PLPhiGal
open CerednikDrinfeld.QM.FakeEllipticCurve ALGlue

variable {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} {N : ℕ} {S : Type u} [CommRing S]

theorem isoT_fst {ℓ : ℕ} {u u' : WithExtraLevel Λ N ℓ S} (h : WithExtraLevel.Iso u u') : FakeEllipticCurve.Iso u.1 u'.1 := by
  obtain ⟨e, he, hmul, hact, hlev, -⟩ := h
  exact ⟨e, he, hmul, hact, hlev⟩

theorem isoT_symm {ℓ : ℕ} {u u' : WithExtraLevel Λ N ℓ S} (h : WithExtraLevel.Iso u u') : WithExtraLevel.Iso u' u := by
  obtain ⟨e, he, hmul, hact, hlev, hlevK⟩ := h
  refine ⟨e.symm, inv_over e he, ?_, ?_, ?_, ?_⟩
  · intro T t P Q; exact inv_mul e he hmul t P Q
  · intro x; exact inv_act e hact x
  · intro T t P
    change FactorsThrough u'.1.lev P ↔ FactorsThrough u.1.lev (mapPt e.inv (inv_over e he) P)
    rw [hlev t (mapPt e.inv (inv_over e he) P), mapPt_hom_inv]
  · intro T t P
    change FactorsThrough u'.2.levK P ↔ FactorsThrough u.2.levK (mapPt e.inv (inv_over e he) P)
    rw [hlevK t (mapPt e.inv (inv_over e he) P), mapPt_hom_inv]

theorem isoT_trans {ℓ : ℕ} {u u' u'' : WithExtraLevel Λ N ℓ S} (h : WithExtraLevel.Iso u u') (h' : WithExtraLevel.Iso u' u'') :
    WithExtraLevel.Iso u u'' := by
  obtain ⟨e, he, hmul, hact, hlev, hlevK⟩ := h
  obtain ⟨e', he', hmul', hact', hlev', hlevK'⟩ := h'
  have hee : (e ≪≫ e').hom ≫ u''.1.f = u.1.f := by rw [Iso.trans_hom, Category.assoc, he', he]
  have hpt : ∀ {T : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of S)} (P : SchemeHomOver t u.1.f),
      mapPt (e ≪≫ e').hom hee P = mapPt e'.hom he' (mapPt e.hom he P) := fun P => by
    apply Subtype.ext; simp [mapPt_coe]
  refine ⟨e ≪≫ e', hee, ?_, ?_, ?_, ?_⟩
  · intro T t P Q; rw [hpt, hpt, hpt, hmul, hmul']
  · intro x; rw [Iso.trans_hom, ← Category.assoc, hact, Category.assoc, hact', Category.assoc]
  · intro T t P; rw [hpt, hlev, hlev']
  · intro T t P; rw [hpt, hlevK, hlevK']

theorem isoT_of_levK_iff {ℓ : ℕ} (E : FakeEllipticCurve Λ N S) (K K' : E.ExtraLevel ℓ)
    (hKK' : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of S)) (P : SchemeHomOver t E.f),
      FactorsThrough K.levK P ↔ FactorsThrough K'.levK P) :
    WithExtraLevel.Iso (⟨E, K⟩ : WithExtraLevel Λ N ℓ S) ⟨E, K'⟩ := by
  have h1 : (Iso.refl E.A).hom ≫ E.f = E.f := by simp
  have hid : ∀ {T : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of S)} (P : SchemeHomOver t E.f),
      mapPt (Iso.refl E.A).hom h1 P = P := fun P => Subtype.ext (by simp [mapPt_coe])
  refine ⟨Iso.refl _, h1, ?_, ?_, ?_, ?_⟩
  · intro T t P Q; rw [hid, hid, hid]
  · intro x; simp
  · intro T t P; rw [hid]
  · intro T t P; rw [hid]; exact hKK' t P

theorem isPullback_congr_left {S' : Type u} [CommRing S'] {φ : S →+* S'} {E₁ E₂ : FakeEllipticCurve Λ N S}
    {E' : FakeEllipticCurve Λ N S'} (h : IsPullback φ E₁ E') (h₁₂ : FakeEllipticCurve.Iso E₁ E₂) :
    IsPullback φ E₂ E' := by
  obtain ⟨g, hg, hmul, hact, hlev⟩ := h
  obtain ⟨e, he, emul, eact, elev⟩ := h₁₂
  have hge : CategoryTheory.IsPullback (g ≫ e.hom) E'.f E₂.f (Spec.map (CommRingCat.ofHom φ)) := by
    refine IsPullback.of_iso hg (Iso.refl _) e (Iso.refl _) (Iso.refl _) ?_ ?_ ?_ ?_ <;> simp [he]
  refine ⟨g ≫ e.hom, hge, ?_, ?_, ?_⟩
  · intro T t' P Q
    have key := congrArg Subtype.val (emul _
      ⟨P.1 ≫ g, by rw [Category.assoc, hg.w, ← Category.assoc, P.2]⟩
      ⟨Q.1 ≫ g, by rw [Category.assoc, hg.w, ← Category.assoc, Q.2]⟩)
    simp only [mapPt_coe] at key
    rw [← Category.assoc, hmul t' P Q, key]
    congr 1
  · intro x
    rw [← Category.assoc, hact, Category.assoc, eact, Category.assoc]
  · intro T t' P hP
    obtain ⟨P₀, hP₀⟩ := hlev t' P hP
    have hft : FactorsThrough E₁.lev (⟨P.1 ≫ g, by rw [Category.assoc, hg.w, ← Category.assoc, P.2]⟩ :
        SchemeHomOver (t' ≫ Spec.map (CommRingCat.ofHom φ)) E₁.f) := ⟨P₀, hP₀⟩
    obtain ⟨P₁, hP₁⟩ := (elev _ _).mp hft
    exact ⟨P₁, by rw [hP₁, mapPt_coe, Category.assoc]⟩

end PLPhiGal
p2m_reactivate "P2MW.S_CerednikDrinfeld_QM_ModuliTowerWitness_tower_laws_of_two_mul_dvd.Ws23TL.L3.ALGlue P2MW.S_CerednikDrinfeld_QM_ModuliTowerWitness_tower_laws_of_two_mul_dvd.Ws23TL P2MW.S_CerednikDrinfeld_QM_ModuliTowerWitness_tower_laws_of_two_mul_dvd.Ws23TL.L3 P2MW.S_CerednikDrinfeld_QM_ModuliTowerWitness_tower_laws_of_two_mul_dvd.Ws23TL.L7.ALGlue"

private theorem _root_.Ws23TL.L7.main
    {N q q' : ℕ} [NeZero N] [Fact q.Prime] [Fact q'.Prime] (hqN : ¬ q ∣ N) (hq'N : ¬ q' ∣ N) (hqq' : q' ≠ q)
    (D : ℕ) [NeZero D] (hD : 2 * N * q * q' ∣ D)
    {a b : ℚ} (hB : IsIndefiniteRamifiedExactlyAt a b q q')
    (Λ : Submodule ℤ ℍ[ℚ, a, b]) (hΛ : IsMaximalOrder Λ)

    (X : Scheme.{0}) [hXint : IsIntegral X]
    (πX : X ⟶ Spec (CommRingCat.of (Localization.Away ((D : ℕ) : ℤ))))
    (pt : ∀ (S : Type) [CommRing S]
      (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of (Localization.Away ((D : ℕ) : ℤ)))),
      FakeEllipticCurve Λ N S → SchemeHomOver s πX)
    (hsmooth : Smooth πX) (hproper : IsProper πX)
    (pt_iso : ∀ (S : Type) [CommRing S] (s : Spec (CommRingCat.of S) ⟶ _) (E E' : FakeEllipticCurve Λ N S),
      FakeEllipticCurve.Iso E E' → pt S s E = pt S s E')
    (pt_pullback : ∀ (S S' : Type) [CommRing S] [CommRing S'] (φ : S →+* S')
      (s : Spec (CommRingCat.of S) ⟶ _) (s' : Spec (CommRingCat.of S') ⟶ _),
      Spec.map (CommRingCat.ofHom φ) ≫ s = s' → ∀ (E : FakeEllipticCurve Λ N S) (E' : FakeEllipticCurve Λ N S'),
      FakeEllipticCurve.IsPullback φ E E' → (pt S' s' E').1 = Spec.map (CommRingCat.ofHom φ) ≫ (pt S s E).1)
    (pt_surjective : ∀ (k : Type) [Field k] [IsAlgClosed k] (s : Spec (CommRingCat.of k) ⟶ _) (P : SchemeHomOver s πX),
      ∃ E : FakeEllipticCurve Λ N k, pt k s E = P)
    (pt_injective : ∀ (k : Type) [Field k] [IsAlgClosed k] (s : Spec (CommRingCat.of k) ⟶ _)
      (E E' : FakeEllipticCurve Λ N k), pt k s E = pt k s E' → FakeEllipticCurve.Iso E E')
    (hsmooth1 : SmoothOfRelativeDimension 1 πX)
    (hgeom : ∀ (k : Type) [Field k] [IsAlgClosed k]
      (s : Spec (CommRingCat.of k) ⟶ Spec (CommRingCat.of (Localization.Away ((D : ℕ) : ℤ)))),
      IsIntegral (CategoryTheory.Limits.pullback πX s))
    (sbar : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ Spec (CommRingCat.of (Localization.Away ((D : ℕ) : ℤ))))
    (sbar_over : sbar ≫ Spec.map (CommRingCat.ofHom (algebraMap ℤ (Localization.Away ((D : ℕ) : ℤ)))) =
      Spec.map (CommRingCat.ofHom (algebraMap ℤ (AlgebraicClosure ℚ))))

    (Fbar : Type) [Field Fbar] [Algebra (AlgebraicClosure ℚ) Fbar]
    [IsCurveOver (AlgebraicClosure ℚ) Fbar] [Algebra.EssFiniteType (AlgebraicClosure ℚ) Fbar]
    (gal : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) →* SemilinearAut (AlgebraicClosure ℚ) Fbar)
    (𝔐 : AlgebraicCurve.CurveModel (AlgebraicClosure ℚ) Fbar)
    (e𝔐 : 𝔐.C ⟶ CategoryTheory.Limits.pullback πX sbar) (he𝔐 : IsIso e𝔐)
    (he𝔐_snd : e𝔐 ≫ CategoryTheory.Limits.pullback.snd πX sbar = 𝔐.toBase)

    (𝕋 : HeckeTower.TowerData q q' Fbar)
    (galT : ∀ ℓ : HeckeTower.AwayPrime q q', (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) →* SemilinearAut (AlgebraicClosure ℚ) (𝕋.F ℓ))
    (W : Fin 2 → SemilinearAut (AlgebraicClosure ℚ) Fbar) (WT : ∀ ℓ : HeckeTower.AwayPrime q q', Fin 2 → SemilinearAut (AlgebraicClosure ℚ) (𝕋.F ℓ))
    (tw : ModuliTowerWitnessD Λ N q q' D Fbar X πX sbar pt 𝔐 e𝔐 gal 𝕋 galT W WT) :
    ∀ (α : HeckeTower.Arr q q') (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (P' : Place (AlgebraicClosure ℚ) (𝕋.F α.1)),
      (galT α.1 σ • P').restrictAlong (𝕋.φ α) (𝕋.integral α) = gal σ • P'.restrictAlong (𝕋.φ α) (𝕋.integral α) := by
  classical
  have place_of_iso : ∀ P Q : Place (AlgebraicClosure ℚ) Fbar, FakeEllipticCurve.Iso (tw.rep P) (tw.rep Q) → P = Q := by
    intro P Q hPQ
    apply AlgebraicCurve.CurveModel.place_eq_of_pointEquivPlace_symm_comp_eq 𝔐 πX sbar e𝔐 he𝔐 he𝔐_snd
    rw [← tw.pt_rep P, ← tw.pt_rep Q, pt_iso _ sbar _ _ hPQ]
  rintro ⟨ℓ, j⟩ σ P'
  obtain ⟨u', g, hg, h1, h2, h3, hisoT⟩ := tw.galT_rep ℓ σ P'
  have hlv := fun {T : Scheme} (t' : T ⟶ Spec (CommRingCat.of (AlgebraicClosure ℚ))) (Q : SchemeHomOver t' u'.1.f) => (h3 t' Q).1
  have hlvK := fun {T : Scheme} (t' : T ⟶ Spec (CommRingCat.of (AlgebraicClosure ℚ))) (Q : SchemeHomOver t' u'.1.f) => (h3 t' Q).2
  have hPBu : FakeEllipticCurve.IsPullback (σ : AlgebraicClosure ℚ →+* AlgebraicClosure ℚ) (tw.repT ℓ P').1 u'.1 :=
    ⟨g, hg, h1, h2, hlv⟩
  fin_cases j
  ·
    obtain ⟨E, hPB, hEiso⟩ := tw.gal_rep σ (P'.restrictAlong (𝕋.φ (ℓ, 0)) (𝕋.integral (ℓ, 0)))
    have r0 : FakeEllipticCurve.Iso (tw.repT ℓ P').1
        (tw.rep (P'.restrictAlong (𝕋.φ (ℓ, 0)) (𝕋.integral (ℓ, 0)))) := tw.restrict_zero ℓ P'
    have r0' : FakeEllipticCurve.Iso (tw.repT ℓ (galT ℓ σ • P')).1
        (tw.rep ((galT ℓ σ • P').restrictAlong (𝕋.φ (ℓ, 0)) (𝕋.integral (ℓ, 0)))) := tw.restrict_zero ℓ (galT ℓ σ • P')
    have hiso1 := CerednikDrinfeld.QM.FakeEllipticCurve.iso_of_isPullback_of_isPullback
      (σ : AlgebraicClosure ℚ →+* AlgebraicClosure ℚ) _ u'.1 E (PLPhiGal.isPullback_congr_left hPBu r0) hPB
    exact place_of_iso _ _ (ALGlue.iso_trans (ALGlue.iso_symm r0')
      (ALGlue.iso_trans (ALGlue.iso_symm (PLPhiGal.isoT_fst hisoT)) (ALGlue.iso_trans hiso1 hEiso)))
  ·
    obtain ⟨E, ⟨h, hh, hm, ha, hl⟩, hEiso⟩ := tw.gal_rep σ (P'.restrictAlong (𝕋.φ (ℓ, 1)) (𝕋.integral (ℓ, 1)))
    have hlv' := fun {T : Scheme} (t' : T ⟶ Spec (CommRingCat.of (AlgebraicClosure ℚ))) (Q : SchemeHomOver t' u'.1.f) =>
      CerednikDrinfeld.QM.FakeEllipticCurve.factorsThrough_lev_of_exists_comp_eq_of_isPullback
        (σ : AlgebraicClosure ℚ →+* AlgebraicClosure ℚ) (tw.repT ℓ P').1 u'.1 g hg h1 hlv t' Q
    have hl' := fun {T : Scheme} (t' : T ⟶ Spec (CommRingCat.of (AlgebraicClosure ℚ))) (Q : SchemeHomOver t' E.f) =>
      CerednikDrinfeld.QM.FakeEllipticCurve.factorsThrough_lev_of_exists_comp_eq_of_isPullback
        (σ : AlgebraicClosure ℚ →+* AlgebraicClosure ℚ) _ E h hh hm hl t' Q
    obtain ⟨Kbar, hKpts, hisog⟩ := CerednikDrinfeld.QM.FakeEllipticCurve.exists_extraLevel_isLevelIsogeny_of_isPullback
      (σ : AlgebraicClosure ℚ →+* AlgebraicClosure ℚ) (ℓ.1 : ℕ) (tw.repT ℓ P') _ (tw.restrict_one ℓ P')
      u'.1 E g hg h1 h2 hlv hlv' h hh hm ha hl hl'
    have hagree : ∀ {T : Scheme} (t' : T ⟶ Spec (CommRingCat.of (AlgebraicClosure ℚ))) (Q : SchemeHomOver t' u'.1.f),
        FactorsThrough u'.2.levK Q ↔ FactorsThrough Kbar.levK Q := by
      intro T t' Q
      constructor
      · intro hQ; exact (hKpts t' Q).mpr (hlvK t' Q hQ)
      · intro hQ
        exact ALTBaseChange.factorsThrough_levK_of_exists_comp_eq (σ : AlgebraicClosure ℚ →+* AlgebraicClosure ℚ)
          (tw.repT ℓ P') u' g hg hlvK t' Q ((hKpts t' Q).mp hQ)
    have isoT2 : FakeEllipticCurve.WithExtraLevel.Iso (tw.repT ℓ (galT ℓ σ • P')) ⟨u'.1, Kbar⟩ :=
      PLPhiGal.isoT_trans (PLPhiGal.isoT_symm hisoT) (PLPhiGal.isoT_of_levK_iff u'.1 u'.2 Kbar hagree)
    have hiso1 := CerednikDrinfeld.QM.FakeEllipticCurve.iso_of_isLevelIsogeny_of_iso_of_isOrder (k := AlgebraicClosure ℚ) (ℓ.1 : ℕ)
      ℓ.1.2.pos hΛ.isOrder (tw.repT ℓ (galT ℓ σ • P')) ⟨u'.1, Kbar⟩ _ E isoT2 (tw.restrict_one ℓ (galT ℓ σ • P')) hisog
    exact place_of_iso _ _ (ALGlue.iso_trans hiso1 hEiso)

p2m_export "Ws23TL.L7" "main"
end Ws23TL.L7
p2m_reactivate "P2MW.S_CerednikDrinfeld_QM_ModuliTowerWitness_tower_laws_of_two_mul_dvd.Ws23TL.L3.ALGlue P2MW.S_CerednikDrinfeld_QM_ModuliTowerWitness_tower_laws_of_two_mul_dvd.Ws23TL P2MW.S_CerednikDrinfeld_QM_ModuliTowerWitness_tower_laws_of_two_mul_dvd.Ws23TL.L3 P2MW.S_CerednikDrinfeld_QM_ModuliTowerWitness_tower_laws_of_two_mul_dvd.Ws23TL.L7.ALGlue P2MW.S_CerednikDrinfeld_QM_ModuliTowerWitness_tower_laws_of_two_mul_dvd.Ws23TL.L7"
p2m_reactivate "P2MW.S_CerednikDrinfeld_QM_ModuliTowerWitness_tower_laws_of_two_mul_dvd.Ws23TL.L3.ALGlue P2MW.S_CerednikDrinfeld_QM_ModuliTowerWitness_tower_laws_of_two_mul_dvd.Ws23TL P2MW.S_CerednikDrinfeld_QM_ModuliTowerWitness_tower_laws_of_two_mul_dvd.Ws23TL.L3 P2MW.S_CerednikDrinfeld_QM_ModuliTowerWitness_tower_laws_of_two_mul_dvd.Ws23TL.L7.ALGlue"

namespace Ws23TL
namespace L8

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry NeronModelInfra GoodReductionJacobian IsDedekindDomain AlgebraicCurve QuaternionAlgebra CerednikDrinfeld CerednikDrinfeld.QM
open scoped Quaternion TensorProduct NumberField

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian
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
p2m_reactivate "P2MW.S_CerednikDrinfeld_QM_ModuliTowerWitness_tower_laws_of_two_mul_dvd.Ws23TL.L3.ALGlue P2MW.S_CerednikDrinfeld_QM_ModuliTowerWitness_tower_laws_of_two_mul_dvd.Ws23TL P2MW.S_CerednikDrinfeld_QM_ModuliTowerWitness_tower_laws_of_two_mul_dvd.Ws23TL.L3 P2MW.S_CerednikDrinfeld_QM_ModuliTowerWitness_tower_laws_of_two_mul_dvd.Ws23TL.L7.ALGlue P2MW.S_CerednikDrinfeld_QM_ModuliTowerWitness_tower_laws_of_two_mul_dvd.Ws23TL.L7"

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
p2m_reactivate "P2MW.S_CerednikDrinfeld_QM_ModuliTowerWitness_tower_laws_of_two_mul_dvd.Ws23TL.L3.ALGlue P2MW.S_CerednikDrinfeld_QM_ModuliTowerWitness_tower_laws_of_two_mul_dvd.Ws23TL P2MW.S_CerednikDrinfeld_QM_ModuliTowerWitness_tower_laws_of_two_mul_dvd.Ws23TL.L3 P2MW.S_CerednikDrinfeld_QM_ModuliTowerWitness_tower_laws_of_two_mul_dvd.Ws23TL.L7.ALGlue P2MW.S_CerednikDrinfeld_QM_ModuliTowerWitness_tower_laws_of_two_mul_dvd.Ws23TL.L7 P2MW.S_CerednikDrinfeld_QM_ModuliTowerWitness_tower_laws_of_two_mul_dvd.Ws23TL.L8.ALGlue"

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian
open CerednikDrinfeld CerednikDrinfeld.QM CerednikDrinfeld.QM.FakeEllipticCurve QuaternionAlgebra
open scoped Quaternion

theorem BaseAL.iso_of_alq_of_alq
    {N q q' : ℕ} [NeZero N] [Fact q.Prime] [Fact q'.Prime] (hqN : ¬ q ∣ N) (hq'N : ¬ q' ∣ N) (hqq' : q' ≠ q)
    {a b : ℚ} (hB : IsIndefiniteRamifiedExactlyAt a b q q')
    (Λ : Submodule ℤ ℍ[ℚ, a, b]) (hΛ : IsMaximalOrder Λ)
    (r : ℕ) (hr : r = q ∨ r = q')
    (u u' u'' : QM.FakeEllipticCurve Λ N (AlgebraicClosure ℚ))
    (h' : QM.FakeEllipticCurve.IsAtkinLehnerQuotient r u u')
    (h'' : QM.FakeEllipticCurve.IsAtkinLehnerQuotient r u u'') :
    QM.FakeEllipticCurve.Iso u' u'' := by
  classical
  obtain ⟨φ', hφ', ψ', hψ', mφ', mψ', aφ', aψ', c', k', l'⟩ := h'
  obtain ⟨φ'', hφ'', ψ'', hψ'', mφ'', mψ'', aφ'', aψ'', c'', k'', l''⟩ := h''
  have hO : IsOrder Λ := hΛ.isOrder
  have hrprime : r.Prime := by rcases hr with rfl | rfl <;> exact Fact.out
  have hrN : ¬ r ∣ N := by rcases hr with rfl | rfl <;> assumption
  have hcopN : Nat.Coprime r N := (Nat.Prime.coprime_iff_not_dvd hrprime).2 hrN
  have hrΛ : ((r : ℚ) : ℍ[ℚ, a, b]) ∈ Λ := by
    have : ((r : ℚ) : ℍ[ℚ, a, b]) = (r : ℤ) • (1 : ℍ[ℚ, a, b]) := by
      rw [zsmul_eq_mul, mul_one]; norm_cast
    rw [this]; exact Λ.smul_mem _ hO.one_mem

  have nsm : ∀ (E E' : FakeEllipticCurve Λ N (AlgebraicClosure ℚ)) (φ : E.A ⟶ E'.A) (hφ : φ ≫ E'.f = E.f)
      (ψ : E'.A ⟶ E.A) (hψ : ψ ≫ E.f = E'.f) (hc : φ ≫ ψ = E.act ⟨((r : ℚ) : ℍ[ℚ, a, b]), hrΛ⟩)
      {T : Scheme} (t : T ⟶ Spec (CommRingCat.of (AlgebraicClosure ℚ))) (P : SchemeHomOver t E.f),
      mapPt ψ hψ (mapPt φ hφ P) = nsmulPt E.L t r P := by
    intro E E' φ hφ ψ hψ hc T t P
    rw [← pushPt_act_natCast_eq_nsmulPt E hO.one_mem r hrΛ t P]
    apply Subtype.ext
    simp only [mapPt_coe, pushPt, Category.assoc, hc]
  have hψφ' := fun {T : Scheme} (t : T ⟶ Spec (CommRingCat.of (AlgebraicClosure ℚ))) (P : SchemeHomOver t u.f) => nsm u u' φ' hφ' ψ' hψ' (c' hrΛ).1 t P
  have hφψ' := fun {T : Scheme} (t : T ⟶ Spec (CommRingCat.of (AlgebraicClosure ℚ))) (P : SchemeHomOver t u'.f) => nsm u' u ψ' hψ' φ' hφ' (c' hrΛ).2 t P
  have hψφ'' := fun {T : Scheme} (t : T ⟶ Spec (CommRingCat.of (AlgebraicClosure ℚ))) (P : SchemeHomOver t u.f) => nsm u u'' φ'' hφ'' ψ'' hψ'' (c'' hrΛ).1 t P
  have hφψ'' := fun {T : Scheme} (t : T ⟶ Spec (CommRingCat.of (AlgebraicClosure ℚ))) (P : SchemeHomOver t u''.f) => nsm u'' u ψ'' hψ'' φ'' hφ'' (c'' hrΛ).2 t P
  have hker1 : ∀ {T : Scheme} (t : T ⟶ Spec (CommRingCat.of (AlgebraicClosure ℚ))) (P : SchemeHomOver t u.f),
      mapPt φ' hφ' P = u'.L.one t → mapPt φ'' hφ'' P = u''.L.one t :=
    fun t P h => (k'' t P).2 ((k' t P).1 h)
  have hker2 : ∀ {T : Scheme} (t : T ⟶ Spec (CommRingCat.of (AlgebraicClosure ℚ))) (P : SchemeHomOver t u.f),
      mapPt φ'' hφ'' P = u''.L.one t → mapPt φ' hφ' P = u'.L.one t :=
    fun t P h => (k' t P).2 ((k'' t P).1 h)
  obtain ⟨χ, hχ, hφχ, -, χmul, χact, hisoχ⟩ :=
    CerednikDrinfeld.QM.FakeEllipticCurve.exists_unique_comp_eq_of_forall_mapPt_eq_one (AlgebraicClosure ℚ) u u' u''
      φ' hφ' mφ' aφ' ψ' hψ' r hrprime.pos hψφ' hφψ' φ'' hφ'' mφ'' aφ'' ψ'' hψ'' r hrprime.pos hψφ'' hφψ'' hker1
  haveI : IsIso χ := hisoχ hker2
  have LO' := fun {T : Scheme} (t : T ⟶ Spec (CommRingCat.of (AlgebraicClosure ℚ))) (Q : SchemeHomOver t u'.f) =>
    CerednikDrinfeld.QM.FakeEllipticCurve.factorsThrough_lev_iff_exists_mapPt_eq_of_coprime
      u u' φ' hφ' mφ' ψ' hψ' r hcopN hψφ' l' t Q
  have LO'' := fun {T : Scheme} (t : T ⟶ Spec (CommRingCat.of (AlgebraicClosure ℚ))) (Q : SchemeHomOver t u''.f) =>
    CerednikDrinfeld.QM.FakeEllipticCurve.factorsThrough_lev_iff_exists_mapPt_eq_of_coprime
      u u'' φ'' hφ'' mφ'' ψ'' hψ'' r hcopN hψφ'' l'' t Q
  have tχ : ∀ {T : Scheme} {t : T ⟶ Spec (CommRingCat.of (AlgebraicClosure ℚ))} (P : SchemeHomOver t u.f),
      mapPt χ hχ (mapPt φ' hφ' P) = mapPt φ'' hφ'' P :=
    fun P => Subtype.ext (by simp only [mapPt_coe, Category.assoc, hφχ])
  have χinj : ∀ {T : Scheme} {t : T ⟶ Spec (CommRingCat.of (AlgebraicClosure ℚ))} (Q Q' : SchemeHomOver t u'.f),
      mapPt χ hχ Q = mapPt χ hχ Q' → Q = Q' := by
    intro T t Q Q' h
    apply Subtype.ext
    rw [← cancel_mono χ]
    exact congrArg Subtype.val h
  refine ⟨asIso χ, hχ, ?_, χact, ?_⟩
  · intro T t P Q; exact χmul hχ t P Q
  · intro T t Q
    constructor
    · intro hQ
      obtain ⟨P, hP, rfl⟩ := (LO' t Q).1 hQ
      show FactorsThrough u''.lev (mapPt χ hχ (mapPt φ' hφ' P))
      rw [tχ]; exact l'' t P hP
    · intro hQ
      obtain ⟨P, hP, hPe⟩ := (LO'' t (mapPt χ hχ Q)).1 hQ
      have hPQ : mapPt φ' hφ' P = Q := χinj _ _ (by rw [tχ, hPe])
      rw [← hPQ]; exact l' t P hP

namespace PLPhiW
open CerednikDrinfeld.QM.FakeEllipticCurve

variable {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} {N : ℕ}

theorem alq_fst {S : Type u} [CommRing S] {ℓ r : ℕ} {u u' : WithExtraLevel Λ N ℓ S}
    (h : WithExtraLevel.IsAtkinLehnerQuotient r u u') : IsAtkinLehnerQuotient r u.1 u'.1 := by
  obtain ⟨φ, hφ, ψ, hψ, h1, h2, h3, h4, h5, h6, h7, -⟩ := h
  exact ⟨φ, hφ, ψ, hψ, h1, h2, h3, h4, h5, h6, h7⟩

end PLPhiW
p2m_reactivate "P2MW.S_CerednikDrinfeld_QM_ModuliTowerWitness_tower_laws_of_two_mul_dvd.Ws23TL.L3.ALGlue P2MW.S_CerednikDrinfeld_QM_ModuliTowerWitness_tower_laws_of_two_mul_dvd.Ws23TL P2MW.S_CerednikDrinfeld_QM_ModuliTowerWitness_tower_laws_of_two_mul_dvd.Ws23TL.L3 P2MW.S_CerednikDrinfeld_QM_ModuliTowerWitness_tower_laws_of_two_mul_dvd.Ws23TL.L7.ALGlue P2MW.S_CerednikDrinfeld_QM_ModuliTowerWitness_tower_laws_of_two_mul_dvd.Ws23TL.L7 P2MW.S_CerednikDrinfeld_QM_ModuliTowerWitness_tower_laws_of_two_mul_dvd.Ws23TL.L8.ALGlue"

private theorem _root_.Ws23TL.L8.main
    {N q q' : ℕ} [NeZero N] [Fact q.Prime] [Fact q'.Prime] (hqN : ¬ q ∣ N) (hq'N : ¬ q' ∣ N) (hqq' : q' ≠ q)
    (D : ℕ) [NeZero D] (hD : 2 * N * q * q' ∣ D)
    {a b : ℚ} (hB : IsIndefiniteRamifiedExactlyAt a b q q')
    (Λ : Submodule ℤ ℍ[ℚ, a, b]) (hΛ : IsMaximalOrder Λ)

    (X : Scheme.{0}) [hXint : IsIntegral X]
    (πX : X ⟶ Spec (CommRingCat.of (Localization.Away ((D : ℕ) : ℤ))))
    (pt : ∀ (S : Type) [CommRing S]
      (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of (Localization.Away ((D : ℕ) : ℤ)))),
      FakeEllipticCurve Λ N S → SchemeHomOver s πX)
    (hsmooth : Smooth πX) (hproper : IsProper πX)
    (pt_iso : ∀ (S : Type) [CommRing S] (s : Spec (CommRingCat.of S) ⟶ _) (E E' : FakeEllipticCurve Λ N S),
      FakeEllipticCurve.Iso E E' → pt S s E = pt S s E')
    (pt_pullback : ∀ (S S' : Type) [CommRing S] [CommRing S'] (φ : S →+* S')
      (s : Spec (CommRingCat.of S) ⟶ _) (s' : Spec (CommRingCat.of S') ⟶ _),
      Spec.map (CommRingCat.ofHom φ) ≫ s = s' → ∀ (E : FakeEllipticCurve Λ N S) (E' : FakeEllipticCurve Λ N S'),
      FakeEllipticCurve.IsPullback φ E E' → (pt S' s' E').1 = Spec.map (CommRingCat.ofHom φ) ≫ (pt S s E).1)
    (pt_surjective : ∀ (k : Type) [Field k] [IsAlgClosed k] (s : Spec (CommRingCat.of k) ⟶ _) (P : SchemeHomOver s πX),
      ∃ E : FakeEllipticCurve Λ N k, pt k s E = P)
    (pt_injective : ∀ (k : Type) [Field k] [IsAlgClosed k] (s : Spec (CommRingCat.of k) ⟶ _)
      (E E' : FakeEllipticCurve Λ N k), pt k s E = pt k s E' → FakeEllipticCurve.Iso E E')
    (hsmooth1 : SmoothOfRelativeDimension 1 πX)
    (hgeom : ∀ (k : Type) [Field k] [IsAlgClosed k]
      (s : Spec (CommRingCat.of k) ⟶ Spec (CommRingCat.of (Localization.Away ((D : ℕ) : ℤ)))),
      IsIntegral (CategoryTheory.Limits.pullback πX s))
    (sbar : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ Spec (CommRingCat.of (Localization.Away ((D : ℕ) : ℤ))))
    (sbar_over : sbar ≫ Spec.map (CommRingCat.ofHom (algebraMap ℤ (Localization.Away ((D : ℕ) : ℤ)))) =
      Spec.map (CommRingCat.ofHom (algebraMap ℤ (AlgebraicClosure ℚ))))

    (Fbar : Type) [Field Fbar] [Algebra (AlgebraicClosure ℚ) Fbar]
    [IsCurveOver (AlgebraicClosure ℚ) Fbar] [Algebra.EssFiniteType (AlgebraicClosure ℚ) Fbar]
    (gal : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) →* SemilinearAut (AlgebraicClosure ℚ) Fbar)
    (𝔐 : AlgebraicCurve.CurveModel (AlgebraicClosure ℚ) Fbar)
    (e𝔐 : 𝔐.C ⟶ CategoryTheory.Limits.pullback πX sbar) (he𝔐 : IsIso e𝔐)
    (he𝔐_snd : e𝔐 ≫ CategoryTheory.Limits.pullback.snd πX sbar = 𝔐.toBase)

    (𝕋 : HeckeTower.TowerData q q' Fbar)
    (galT : ∀ ℓ : HeckeTower.AwayPrime q q', (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) →* SemilinearAut (AlgebraicClosure ℚ) (𝕋.F ℓ))
    (W : Fin 2 → SemilinearAut (AlgebraicClosure ℚ) Fbar) (WT : ∀ ℓ : HeckeTower.AwayPrime q q', Fin 2 → SemilinearAut (AlgebraicClosure ℚ) (𝕋.F ℓ))
    (tw : ModuliTowerWitnessD Λ N q q' D Fbar X πX sbar pt 𝔐 e𝔐 gal 𝕋 galT W WT) :
    ∀ (α : HeckeTower.Arr q q') (i : Fin 2) (P' : Place (AlgebraicClosure ℚ) (𝕋.F α.1)),
      (WT α.1 i • P').restrictAlong (𝕋.φ α) (𝕋.integral α) = W i • P'.restrictAlong (𝕋.φ α) (𝕋.integral α) := by
  classical
  have place_of_iso : ∀ P Q : Place (AlgebraicClosure ℚ) Fbar, FakeEllipticCurve.Iso (tw.rep P) (tw.rep Q) → P = Q := by
    intro P Q hPQ
    apply AlgebraicCurve.CurveModel.place_eq_of_pointEquivPlace_symm_comp_eq 𝔐 πX sbar e𝔐 he𝔐 he𝔐_snd
    rw [← tw.pt_rep P, ← tw.pt_rep Q, pt_iso _ sbar _ _ hPQ]

  have al_unique : ∀ (r : ℕ), (r = q ∨ r = q') → ∀ (E E₁ E₂ : FakeEllipticCurve Λ N (AlgebraicClosure ℚ)),
      E.IsAtkinLehnerQuotient r E₁ → E.IsAtkinLehnerQuotient r E₂ → FakeEllipticCurve.Iso E₁ E₂ :=
    fun r hr E E₁ E₂ h₁ h₂ => BaseAL.iso_of_alq_of_alq hqN hq'N hqq' hB Λ hΛ r hr E E₁ E₂ h₁ h₂
  rintro ⟨ℓ, j⟩ i P'

  have hrep : ∃ r : ℕ, (r = q ∨ r = q') ∧
      (∀ Q : Place (AlgebraicClosure ℚ) Fbar, (tw.rep Q).IsAtkinLehnerQuotient r (tw.rep (W i • Q))) ∧
      (∀ Q' : Place (AlgebraicClosure ℚ) (𝕋.F ℓ),
        FakeEllipticCurve.WithExtraLevel.IsAtkinLehnerQuotient r (tw.repT ℓ Q') (tw.repT ℓ (WT ℓ i • Q'))) := by
    fin_cases i
    · exact ⟨q, Or.inl rfl, tw.W_zero_rep, tw.WT_zero_rep ℓ⟩
    · exact ⟨q', Or.inr rfl, tw.W_one_rep, tw.WT_one_rep ℓ⟩
  obtain ⟨r, hr, hW, hWT⟩ := hrep
  fin_cases j
  ·
    have r0 : FakeEllipticCurve.Iso (tw.repT ℓ P').1
        (tw.rep (P'.restrictAlong (𝕋.φ (ℓ, 0)) (𝕋.integral (ℓ, 0)))) := tw.restrict_zero ℓ P'
    have r0' : FakeEllipticCurve.Iso (tw.repT ℓ (WT ℓ i • P')).1
        (tw.rep ((WT ℓ i • P').restrictAlong (𝕋.φ (ℓ, 0)) (𝕋.integral (ℓ, 0)))) := tw.restrict_zero ℓ (WT ℓ i • P')
    have hcg := ALGlue.isAtkinLehnerQuotient_congr r (PLPhiW.alq_fst (hWT P')) r0 r0'
    exact place_of_iso _ _ (al_unique r hr _ _ _ hcg (hW _))
  ·
    have hd := CerednikDrinfeld.QM.FakeEllipticCurve.isAtkinLehnerQuotient_of_isLevelIsogeny_of_isLevelIsogeny
      hqN hq'N hqq' hB Λ hΛ (ℓ.1 : ℕ) ℓ.1.2 ℓ.2.1 ℓ.2.2 r hr (tw.repT ℓ P') (tw.repT ℓ (WT ℓ i • P')) _ _
      (tw.restrict_one ℓ P') (hWT P') (tw.restrict_one ℓ (WT ℓ i • P'))
    exact place_of_iso _ _ (al_unique r hr _ _ _ hd (hW _))

p2m_export "Ws23TL.L8" "main"
end Ws23TL.L8
p2m_reactivate "P2MW.S_CerednikDrinfeld_QM_ModuliTowerWitness_tower_laws_of_two_mul_dvd.Ws23TL.L3.ALGlue P2MW.S_CerednikDrinfeld_QM_ModuliTowerWitness_tower_laws_of_two_mul_dvd.Ws23TL P2MW.S_CerednikDrinfeld_QM_ModuliTowerWitness_tower_laws_of_two_mul_dvd.Ws23TL.L3 P2MW.S_CerednikDrinfeld_QM_ModuliTowerWitness_tower_laws_of_two_mul_dvd.Ws23TL.L7.ALGlue P2MW.S_CerednikDrinfeld_QM_ModuliTowerWitness_tower_laws_of_two_mul_dvd.Ws23TL.L7 P2MW.S_CerednikDrinfeld_QM_ModuliTowerWitness_tower_laws_of_two_mul_dvd.Ws23TL.L8.ALGlue P2MW.S_CerednikDrinfeld_QM_ModuliTowerWitness_tower_laws_of_two_mul_dvd.Ws23TL.L8"
p2m_reactivate "P2MW.S_CerednikDrinfeld_QM_ModuliTowerWitness_tower_laws_of_two_mul_dvd.Ws23TL.L3.ALGlue P2MW.S_CerednikDrinfeld_QM_ModuliTowerWitness_tower_laws_of_two_mul_dvd.Ws23TL P2MW.S_CerednikDrinfeld_QM_ModuliTowerWitness_tower_laws_of_two_mul_dvd.Ws23TL.L3 P2MW.S_CerednikDrinfeld_QM_ModuliTowerWitness_tower_laws_of_two_mul_dvd.Ws23TL.L7.ALGlue P2MW.S_CerednikDrinfeld_QM_ModuliTowerWitness_tower_laws_of_two_mul_dvd.Ws23TL.L7 P2MW.S_CerednikDrinfeld_QM_ModuliTowerWitness_tower_laws_of_two_mul_dvd.Ws23TL.L8.ALGlue"

open CategoryTheory AlgebraicGeometry NeronModelInfra GoodReductionJacobian IsDedekindDomain AlgebraicCurve QuaternionAlgebra CerednikDrinfeld CerednikDrinfeld.QM
open scoped Quaternion TensorProduct NumberField

namespace TowerLawsSkel

theorem rigid' (F₀ : Type) [Field F₀] [Algebra (AlgebraicClosure ℚ) F₀] [IsCurveOver (AlgebraicClosure ℚ) F₀]
    [Algebra.EssFiniteType (AlgebraicClosure ℚ) F₀]
    (W W' : SemilinearAut (AlgebraicClosure ℚ) F₀)
    (hb : SemilinearAut.baseAut W = SemilinearAut.baseAut W')
    (h : ∀ P : Place (AlgebraicClosure ℚ) F₀, W • P = W' • P) : W = W' := by
  have key := AlgebraicCurve.SemilinearAut.eq_of_forall_smul_place_eq F₀ (W'⁻¹ * W) 1 ?_ ?_ ?_
  · exact (by simpa [inv_mul_eq_one] using key : W' = W).symm
  · intro a
    show (SemilinearAut.baseAut W'⁻¹ * SemilinearAut.baseAut W) a = a
    rw [hb]
    show (SemilinearAut.baseAut W')⁻¹ (SemilinearAut.baseAut W' a) = a
    exact (SemilinearAut.baseAut W').symm_apply_apply a
  · intro a; rfl
  · intro P; rw [mul_smul, h, ← mul_smul, inv_mul_cancel, one_smul]

end TowerLawsSkel
p2m_reactivate "P2MW.S_CerednikDrinfeld_QM_ModuliTowerWitness_tower_laws_of_two_mul_dvd.Ws23TL.L3.ALGlue P2MW.S_CerednikDrinfeld_QM_ModuliTowerWitness_tower_laws_of_two_mul_dvd.Ws23TL P2MW.S_CerednikDrinfeld_QM_ModuliTowerWitness_tower_laws_of_two_mul_dvd.Ws23TL.L3 P2MW.S_CerednikDrinfeld_QM_ModuliTowerWitness_tower_laws_of_two_mul_dvd.Ws23TL.L7.ALGlue P2MW.S_CerednikDrinfeld_QM_ModuliTowerWitness_tower_laws_of_two_mul_dvd.Ws23TL.L7 P2MW.S_CerednikDrinfeld_QM_ModuliTowerWitness_tower_laws_of_two_mul_dvd.Ws23TL.L8.ALGlue P2MW.S_CerednikDrinfeld_QM_ModuliTowerWitness_tower_laws_of_two_mul_dvd.Ws23TL.L8"

namespace TowerLawsSkel

open AlgebraicCurve

theorem intertwine {Fb F1 : Type} [Field Fb] [Field F1]
    [Algebra (AlgebraicClosure ℚ) Fb] [Algebra (AlgebraicClosure ℚ) F1]
    [IsCurveOver (AlgebraicClosure ℚ) Fb] [Algebra.EssFiniteType (AlgebraicClosure ℚ) Fb]
    [IsCurveOver (AlgebraicClosure ℚ) F1] [Algebra.EssFiniteType (AlgebraicClosure ℚ) F1]
    (φ : Fb →ₐ[AlgebraicClosure ℚ] F1) (hφ : φ.toRingHom.IsIntegral)
    (g : SemilinearAut (AlgebraicClosure ℚ) Fb) (g' : SemilinearAut (AlgebraicClosure ℚ) F1)
    (hbase : SemilinearAut.baseAut g = SemilinearAut.baseAut g')
    (hpl : ∀ P' : Place (AlgebraicClosure ℚ) F1, (g' • P').restrictAlong φ hφ = g • P'.restrictAlong φ hφ) :
    ∀ x : Fb, g' • φ x = φ (g • x) := by
  classical

  let ψ : Fb →ₐ[AlgebraicClosure ℚ] F1 :=
    { toFun := fun x => g'⁻¹ • φ (g • x)
      map_one' := by simp
      map_mul' := fun x y => by simp [smul_mul']
      map_zero' := by simp
      map_add' := fun x y => by simp [smul_add]
      commutes' := fun a => by
        rw [SemilinearAut.smul_algebraMap, AlgHom.commutes, SemilinearAut.smul_algebraMap, hbase]
        congr 1
        show (SemilinearAut.baseAut g'⁻¹) (SemilinearAut.baseAut g' a) = a
        exact (SemilinearAut.baseAut g').symm_apply_apply a }
  have hψ_apply : ∀ x, ψ x = g'⁻¹ • φ (g • x) := fun _ => rfl

  have hψ : ψ.toRingHom.IsIntegral := by
    have h1 : ψ.toRingHom = ((SemilinearAut.toRingAut g'⁻¹).toRingHom.comp φ.toRingHom).comp
        (SemilinearAut.toRingAut g).toRingHom := RingHom.ext fun x => rfl
    rw [h1]
    refine RingHom.IsIntegral.trans _ _ (RingHom.isIntegral_of_surjective _ (SemilinearAut.toRingAut g).surjective)
      (RingHom.IsIntegral.trans _ _ hφ (RingHom.isIntegral_of_surjective _ (SemilinearAut.toRingAut g'⁻¹).surjective))

  have hres : ∀ w : Place (AlgebraicClosure ℚ) F1, w.restrictAlong ψ hψ = w.restrictAlong φ hφ := by
    intro w
    apply Place.ext
    ext x
    show ψ x ∈ w.toValuationSubring ↔ φ x ∈ w.toValuationSubring
    rw [hψ_apply]
    have e1 : g'⁻¹ • φ (g • x) ∈ w.toValuationSubring ↔ φ (g • x) ∈ (g' • w).toValuationSubring := by
      rw [SemilinearAut.smul_toValuationSubring, ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem]
    have e2 : φ (g • x) ∈ (g' • w).toValuationSubring ↔ g • x ∈ ((g' • w).restrictAlong φ hφ).toValuationSubring := Iff.rfl
    have e3 : x ∈ (w.restrictAlong φ hφ).toValuationSubring ↔ φ x ∈ w.toValuationSubring := Iff.rfl
    rw [e1, e2, hpl, SemilinearAut.smul_toValuationSubring, ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem,
      inv_smul_smul, ← e3]
  have heq := AlgebraicCurve.algHom_eq_of_forall_restrictAlong_eq_of_charZero (AlgebraicClosure ℚ) Fb F1 ψ φ hψ hφ hres
  intro x
  have := congrArg (fun (χ : Fb →ₐ[AlgebraicClosure ℚ] F1) => χ x) heq
  rw [hψ_apply] at this

  rw [← this, smul_inv_smul]

end TowerLawsSkel
p2m_reactivate "P2MW.S_CerednikDrinfeld_QM_ModuliTowerWitness_tower_laws_of_two_mul_dvd.Ws23TL.L3.ALGlue P2MW.S_CerednikDrinfeld_QM_ModuliTowerWitness_tower_laws_of_two_mul_dvd.Ws23TL P2MW.S_CerednikDrinfeld_QM_ModuliTowerWitness_tower_laws_of_two_mul_dvd.Ws23TL.L3 P2MW.S_CerednikDrinfeld_QM_ModuliTowerWitness_tower_laws_of_two_mul_dvd.Ws23TL.L7.ALGlue P2MW.S_CerednikDrinfeld_QM_ModuliTowerWitness_tower_laws_of_two_mul_dvd.Ws23TL.L7 P2MW.S_CerednikDrinfeld_QM_ModuliTowerWitness_tower_laws_of_two_mul_dvd.Ws23TL.L8.ALGlue P2MW.S_CerednikDrinfeld_QM_ModuliTowerWitness_tower_laws_of_two_mul_dvd.Ws23TL.L8"

theorem solution
    {N q q' : ℕ} [NeZero N] [Fact q.Prime] [Fact q'.Prime] (hqN : ¬ q ∣ N) (hq'N : ¬ q' ∣ N) (hqq' : q' ≠ q)
    (D : ℕ) [NeZero D] (hD : 2 * N * q * q' ∣ D)
    {a b : ℚ} (hB : IsIndefiniteRamifiedExactlyAt a b q q')
    (Λ : Submodule ℤ ℍ[ℚ, a, b]) (hΛ : IsMaximalOrder Λ)

    (X : Scheme.{0}) [hXint : IsIntegral X]
    (πX : X ⟶ Spec (CommRingCat.of (Localization.Away ((D : ℕ) : ℤ))))
    (pt : ∀ (S : Type) [CommRing S]
      (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of (Localization.Away ((D : ℕ) : ℤ)))),
      FakeEllipticCurve Λ N S → SchemeHomOver s πX)
    (hsmooth : Smooth πX) (hproper : IsProper πX)
    (pt_iso : ∀ (S : Type) [CommRing S] (s : Spec (CommRingCat.of S) ⟶ _) (E E' : FakeEllipticCurve Λ N S),
      FakeEllipticCurve.Iso E E' → pt S s E = pt S s E')
    (pt_pullback : ∀ (S S' : Type) [CommRing S] [CommRing S'] (φ : S →+* S')
      (s : Spec (CommRingCat.of S) ⟶ _) (s' : Spec (CommRingCat.of S') ⟶ _),
      Spec.map (CommRingCat.ofHom φ) ≫ s = s' → ∀ (E : FakeEllipticCurve Λ N S) (E' : FakeEllipticCurve Λ N S'),
      FakeEllipticCurve.IsPullback φ E E' → (pt S' s' E').1 = Spec.map (CommRingCat.ofHom φ) ≫ (pt S s E).1)
    (pt_surjective : ∀ (k : Type) [Field k] [IsAlgClosed k] (s : Spec (CommRingCat.of k) ⟶ _) (P : SchemeHomOver s πX),
      ∃ E : FakeEllipticCurve Λ N k, pt k s E = P)
    (pt_injective : ∀ (k : Type) [Field k] [IsAlgClosed k] (s : Spec (CommRingCat.of k) ⟶ _)
      (E E' : FakeEllipticCurve Λ N k), pt k s E = pt k s E' → FakeEllipticCurve.Iso E E')
    (hsmooth1 : SmoothOfRelativeDimension 1 πX)
    (hgeom : ∀ (k : Type) [Field k] [IsAlgClosed k]
      (s : Spec (CommRingCat.of k) ⟶ Spec (CommRingCat.of (Localization.Away ((D : ℕ) : ℤ)))),
      IsIntegral (CategoryTheory.Limits.pullback πX s))
    (sbar : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ Spec (CommRingCat.of (Localization.Away ((D : ℕ) : ℤ))))
    (sbar_over : sbar ≫ Spec.map (CommRingCat.ofHom (algebraMap ℤ (Localization.Away ((D : ℕ) : ℤ)))) =
      Spec.map (CommRingCat.ofHom (algebraMap ℤ (AlgebraicClosure ℚ))))

    (Fbar : Type) [Field Fbar] [Algebra (AlgebraicClosure ℚ) Fbar]
    [IsCurveOver (AlgebraicClosure ℚ) Fbar] [Algebra.EssFiniteType (AlgebraicClosure ℚ) Fbar]
    (gal : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) →* SemilinearAut (AlgebraicClosure ℚ) Fbar)
    (𝔐 : AlgebraicCurve.CurveModel (AlgebraicClosure ℚ) Fbar)
    (e𝔐 : 𝔐.C ⟶ CategoryTheory.Limits.pullback πX sbar) (he𝔐 : IsIso e𝔐)
    (he𝔐_snd : e𝔐 ≫ CategoryTheory.Limits.pullback.snd πX sbar = 𝔐.toBase)

    (𝕋 : HeckeTower.TowerData q q' Fbar)
    (galT : ∀ ℓ : HeckeTower.AwayPrime q q', (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) →* SemilinearAut (AlgebraicClosure ℚ) (𝕋.F ℓ))
    (W : Fin 2 → SemilinearAut (AlgebraicClosure ℚ) Fbar) (WT : ∀ ℓ : HeckeTower.AwayPrime q q', Fin 2 → SemilinearAut (AlgebraicClosure ℚ) (𝕋.F ℓ))
    (tw : ModuliTowerWitnessD Λ N q q' D Fbar X πX sbar pt 𝔐 e𝔐 gal 𝕋 galT W WT) :
    (∀ (α : HeckeTower.Arr q q') (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (x : Fbar),
      galT α.1 σ • 𝕋.φ α x = 𝕋.φ α (gal σ • x)) ∧
    (∀ i, W i * W i = 1) ∧ W 0 * W 1 = W 1 * W 0 ∧ (∀ i σ, W i * gal σ = gal σ * W i) ∧
    (∀ ℓ i, WT ℓ i * WT ℓ i = 1) ∧ (∀ ℓ, WT ℓ 0 * WT ℓ 1 = WT ℓ 1 * WT ℓ 0) ∧ (∀ ℓ i σ, WT ℓ i * galT ℓ σ = galT ℓ σ * WT ℓ i) ∧
    (∀ (α : HeckeTower.Arr q q') i (x : Fbar), WT α.1 i • 𝕋.φ α x = 𝕋.φ α (W i • x)) := by
  classical

  have PL_W_sq : ∀ (i : Fin 2) (P : Place (AlgebraicClosure ℚ) Fbar), W i • (W i • P) = P := by
    exact Ws23TL.L1.main hqN hq'N hqq' D hD hB Λ hΛ X πX pt hsmooth hproper pt_iso pt_pullback pt_surjective pt_injective hsmooth1 hgeom sbar sbar_over Fbar gal 𝔐 e𝔐 he𝔐 he𝔐_snd 𝕋 galT W WT tw
  have PL_W_comm : ∀ P : Place (AlgebraicClosure ℚ) Fbar, W 0 • (W 1 • P) = W 1 • (W 0 • P) := by
    exact Ws23TL.L2.main hqN hq'N hqq' D hD hB Λ hΛ X πX pt hsmooth hproper pt_iso pt_pullback pt_surjective pt_injective hsmooth1 hgeom sbar sbar_over Fbar gal 𝔐 e𝔐 he𝔐 he𝔐_snd 𝕋 galT W WT tw
  have PL_W_gal : ∀ (i : Fin 2) (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (P : Place (AlgebraicClosure ℚ) Fbar),
      W i • (gal σ • P) = gal σ • (W i • P) := by
    exact Ws23TL.L3.main hqN hq'N hqq' D hD hB Λ hΛ X πX pt hsmooth hproper pt_iso pt_pullback pt_surjective pt_injective hsmooth1 hgeom sbar sbar_over Fbar gal 𝔐 e𝔐 he𝔐 he𝔐_snd 𝕋 galT W WT tw
  have PL_WT_sq : ∀ (ℓ : HeckeTower.AwayPrime q q') (i : Fin 2) (P : Place (AlgebraicClosure ℚ) (𝕋.F ℓ)),
      WT ℓ i • (WT ℓ i • P) = P := by
    exact Ws23TL.L4.main hqN hq'N hqq' D hD hB Λ hΛ X πX pt hsmooth hproper pt_iso pt_pullback pt_surjective pt_injective hsmooth1 hgeom sbar sbar_over Fbar gal 𝔐 e𝔐 he𝔐 he𝔐_snd 𝕋 galT W WT tw
  have PL_WT_comm : ∀ (ℓ : HeckeTower.AwayPrime q q') (P : Place (AlgebraicClosure ℚ) (𝕋.F ℓ)),
      WT ℓ 0 • (WT ℓ 1 • P) = WT ℓ 1 • (WT ℓ 0 • P) := by
    exact Ws23TL.L5.main hqN hq'N hqq' D hD hB Λ hΛ X πX pt hsmooth hproper pt_iso pt_pullback pt_surjective pt_injective hsmooth1 hgeom sbar sbar_over Fbar gal 𝔐 e𝔐 he𝔐 he𝔐_snd 𝕋 galT W WT tw
  have PL_WT_gal : ∀ (ℓ : HeckeTower.AwayPrime q q') (i : Fin 2) (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)
      (P : Place (AlgebraicClosure ℚ) (𝕋.F ℓ)), WT ℓ i • (galT ℓ σ • P) = galT ℓ σ • (WT ℓ i • P) := by
    exact Ws23TL.L6.main hqN hq'N hqq' D hD hB Λ hΛ X πX pt hsmooth hproper pt_iso pt_pullback pt_surjective pt_injective hsmooth1 hgeom sbar sbar_over Fbar gal 𝔐 e𝔐 he𝔐 he𝔐_snd 𝕋 galT W WT tw

  have hWb : ∀ i, SemilinearAut.baseAut (W i) = 1 := fun i => RingEquiv.ext (tw.W_base i)
  have hWTb : ∀ ℓ i, SemilinearAut.baseAut (WT ℓ i) = 1 := fun ℓ i => RingEquiv.ext (tw.WT_base ℓ i)
  have hgb : ∀ σ, SemilinearAut.baseAut (gal σ) = (σ : AlgebraicClosure ℚ ≃+* AlgebraicClosure ℚ) := tw.gal_base
  have hgTb : ∀ ℓ σ, SemilinearAut.baseAut (galT ℓ σ) = (σ : AlgebraicClosure ℚ ≃+* AlgebraicClosure ℚ) := tw.galT_base
  have hbmul : ∀ {F₀ : Type} [Field F₀] [Algebra (AlgebraicClosure ℚ) F₀] (g h : SemilinearAut (AlgebraicClosure ℚ) F₀),
      SemilinearAut.baseAut (g * h) = SemilinearAut.baseAut g * SemilinearAut.baseAut h := fun g h => rfl
  refine ⟨?law1, ?law2, ?law3, ?law4, ?law5, ?law6, ?law7, ?law8⟩
  case law1 =>
    intro α σ x
    have PL_phi_gal : ∀ P' : Place (AlgebraicClosure ℚ) (𝕋.F α.1),
        (galT α.1 σ • P').restrictAlong (𝕋.φ α) (𝕋.integral α) = gal σ • P'.restrictAlong (𝕋.φ α) (𝕋.integral α) := by
      exact Ws23TL.L7.main hqN hq'N hqq' D hD hB Λ hΛ X πX pt hsmooth hproper pt_iso pt_pullback pt_surjective pt_injective hsmooth1 hgeom sbar sbar_over Fbar gal 𝔐 e𝔐 he𝔐 he𝔐_snd 𝕋 galT W WT tw α σ
    exact TowerLawsSkel.intertwine (𝕋.φ α) (𝕋.integral α) (gal σ) (galT α.1 σ) (by rw [hgb, hgTb]) PL_phi_gal x
  case law8 =>
    intro α i x
    have PL_phi_W : ∀ P' : Place (AlgebraicClosure ℚ) (𝕋.F α.1),
        (WT α.1 i • P').restrictAlong (𝕋.φ α) (𝕋.integral α) = W i • P'.restrictAlong (𝕋.φ α) (𝕋.integral α) := by
      exact Ws23TL.L8.main hqN hq'N hqq' D hD hB Λ hΛ X πX pt hsmooth hproper pt_iso pt_pullback pt_surjective pt_injective hsmooth1 hgeom sbar sbar_over Fbar gal 𝔐 e𝔐 he𝔐 he𝔐_snd 𝕋 galT W WT tw α i
    exact TowerLawsSkel.intertwine (𝕋.φ α) (𝕋.integral α) (W i) (WT α.1 i) (by rw [hWb, hWTb]) PL_phi_W x
  case law2 =>
    intro i
    apply TowerLawsSkel.rigid' Fbar
    · rw [hbmul, hWb]; rfl
    · intro P; rw [mul_smul, PL_W_sq, one_smul]
  case law3 =>
    apply TowerLawsSkel.rigid' Fbar
    · rw [hbmul, hbmul, hWb, hWb]
    · intro P; rw [mul_smul, mul_smul, PL_W_comm]
  case law4 =>
    intro i σ
    apply TowerLawsSkel.rigid' Fbar
    · rw [hbmul, hbmul, hWb, hgb, one_mul, mul_one]
    · intro P; rw [mul_smul, mul_smul, PL_W_gal]
  case law5 =>
    intro ℓ i
    apply TowerLawsSkel.rigid' (𝕋.F ℓ)
    · rw [hbmul, hWTb]; rfl
    · intro P; rw [mul_smul, PL_WT_sq, one_smul]
  case law6 =>
    intro ℓ
    apply TowerLawsSkel.rigid' (𝕋.F ℓ)
    · rw [hbmul, hbmul, hWTb, hWTb]
    · intro P; rw [mul_smul, mul_smul, PL_WT_comm]
  case law7 =>
    intro ℓ i σ
    apply TowerLawsSkel.rigid' (𝕋.F ℓ)
    · rw [hbmul, hbmul, hWTb, hgTb, one_mul, mul_one]
    · intro P; rw [mul_smul, mul_smul, PL_WT_gal]

end S_CerednikDrinfeld_QM_ModuliTowerWitness_tower_laws_of_two_mul_dvd
end P2MW
export P2MW.S_CerednikDrinfeld_QM_ModuliTowerWitness_tower_laws_of_two_mul_dvd (solution)
