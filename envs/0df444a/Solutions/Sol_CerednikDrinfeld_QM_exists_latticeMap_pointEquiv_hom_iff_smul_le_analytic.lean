-- Prove2me | solution 1 for CerednikDrinfeld.QM.exists_latticeMap_pointEquiv_hom_iff_smul_le_analytic
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.141142+00:00
-- url     : https://prove2.me/submissions/2eef6d07-533d-51e2-8af9-54a24535fa09

import Definitions.Def_CerednikDrinfeld_QMModuli
import Definitions.Def_CerednikDrinfeld_QMModuliProps
import Definitions.Def_AlgebraicCurve_CurveModel
import Definitions.Def_CerednikDrinfeld_ShimuraCurve
import Definitions.Def_CerednikDrinfeld_ClassSetGraph
import Definitions.Def_QuaternionAlgebra_QMPeriodLattice
import Theorems.Thm_GoodReductionJacobian_AbelianSchemePropertyBundle_exists_submodule_pointEquiv_quotient_differentiableOn_appLE
import Theorems.Thm_AlgebraicGeometry_exists_finset_forall_pointEquiv_eq_coe_mem_ball_of_differentiableOn_appLE_of_isSeparated
import Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_existsUnique_linearMap_forall_pointEquiv_mapPt_eq_of_differentiableOn_appLE
import Theorems.Thm_QuaternionAlgebra_IsOrder_exists_linearEquiv_apply_eq_mulVec_map_of_finrank_eq_two
import Theorems.Thm_GoodReductionJacobian_AbelianSchemePropertyBundle_exists_hom_mapPt_eq_pointEquiv_symm_quotientMap_of_le_comap
import Theorems.Thm_QuaternionAlgebra_IsOrder_exists_eq_smul_of_forall_mulVec_comm
import Theorems.Thm_AlgebraicGeometry_ext_of_forall_comp_eq_of_isAlgClosed
import Theorems.Thm_AlgebraicGeometry_isIntegral_of_smooth_of_preconnectedSpace
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_QM_exists_latticeMap_pointEquiv_hom_iff_smul_le_analytic
p2m_attr_erase "instance" "PresheafOfModules.ExteriorPower.instModulePresheafAb TwoChartCech.Sections.M0_moduleA TwoChartCech.Sections.M1_module TwoChartCech.Cover.A01_algebra TwoChartCech.Cover.A0_algebra TwoChartCech.Cover.A1_commRing TwoChartCech.Cover.A1_algebra TwoChartCech.Sections.M01_module TwoChartCech.Sections.M0_addCommGroup TwoChartCech.Sections.M0_tower TwoChartCech.Sections.M01_addCommGroup TwoChartCech.Cover.A0_commRing TwoChartCech.Sections.M1_tower TwoChartCech.Sections.M01_moduleA TwoChartCech.Sections.M0_module TwoChartCech.Sections.M1_moduleA TwoChartCech.Sections.M1_addCommGroup TwoChartCech.Cover.A01_commRing TwoChartCech.Sections.M01_tower CoherentBaseChange.TwoTermComplex.C0_module CoherentBaseChange.TwoTermComplex.C0_addCommGroup CoherentBaseChange.TwoTermComplex.C1_module CoherentBaseChange.TwoTermComplex.C1_addCommGroup CoherentBaseChange.TwoTermComplex.C0_free CoherentBaseChange.TwoTermComplex.C1_finite CoherentBaseChange.TwoTermComplex.C0_finite CoherentBaseChange.TwoTermComplex.C1_free AlgebraicCurve.CurveModel.locallyOfFiniteType_gluedToBase AlgebraicCurve.CurveModel.isFractionRing_overlap AlgebraicCurve.CurveModel.isLocallyNoetherian_glued AlgebraicCurve.CurveModel.jacobsonSpace_glued AlgebraicCurve.CurveModel.isOpenImmersion_ι₀ AlgebraicCurve.CurveModel.isIntegral_glued AlgebraicCurve.CurveModel.quasiSeparated_gluedToBase AlgebraicCurve.CurveModel.compactSpace_glued AlgebraicCurve.CurveModel.isIntegral_adjoin_chartRing AlgebraicCurve.CurveModel.isFractionRing_overlap_functionField AlgebraicCurve.CurveModel.isProper_gluedToBase AlgebraicCurve.CurveModel.isOpenImmersion_ιU AlgebraicCurve.CurveModel.isOpenImmersion_f₀"
p2m_attr_erase "instance" "AlgebraicCurve.CurveModel.isOpenImmersion_fInf AlgebraicCurve.CurveModel.isOpenImmersion_ιInf AlgebraicCurve.CurveModel.algebra_overlap_functionField AlgebraicCurve.CurveModel.quasiCompact_gluedToBase AlgebraicCurve.CurveModel.algebraAdjoin AlgebraicCurve.CurveModel.isDedekindDomain_chartRing AlgebraicCurve.CurveModel.isIntegralClosure AlgebraicCurve.CurveModel.finite_chartRing AlgebraicCurve.CurveModel.centre_isPrime AlgebraicCurve.CurveModel.isFractionRing_chartRing AlgebraicCurve.CurveModel.finiteType_chartRing AlgebraicCurve.CurveModel.isNoetherianRing_chartRing AlgebraicCurve.CurveModel.isScalarTower_base_adjoin AlgebraicCurve.CurveModel.isScalarTower_adjoin AlgebraicCurve.CurveModel.chartRing_finitePresentation AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation AlgebraicGeometry.OModulePresheaf.isScalarTower AlgebraicGeometry.Scheme.OrderedAffineCover.instLinearOrder AlgebraicGeometry.OModulePresheaf.module AlgebraicGeometry.Scheme.OrderedAffineCover.instFintype AlgebraicGeometry.Scheme.OrderedAffineCover.instFintypeIdx AlgebraicGeometry.OModulePresheaf.addCommGroup AlgebraicGeometry.Scheme.OrderedAffineCover.instDecidableEqIdx AlgebraicGeometry.OModulePresheaf.moduleSections AlgebraicGeometry.OModulePresheaf.instSubsingletonObjZero AlgebraicGeometry.OModulePresheaf.Leray.relAltC_scalarTower AlgebraicGeometry.OModulePresheaf.Leray.ker_relAltd_modΓ AlgebraicGeometry.OModulePresheaf.Leray.relAltC_modΓ AlgebraicGeometry.OModulePresheaf.Leray.biC_abGrp AlgebraicGeometry.OModulePresheaf.Leray.relAltH_modΓ AlgebraicGeometry.OModulePresheaf.Leray.ker_relAltd_smul AlgebraicGeometry.OModulePresheaf.Leray.relAltH_scalarTower AlgebraicGeometry.OModulePresheaf.Leray.relAltH_smul AlgebraicGeometry.OModulePresheaf.Leray.biC_module AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instDecidableEqIdx AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instFintype AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instLinearOrder AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instFintypeIdx DoubleComplex.instModuleE₂I"
p2m_attr_erase "instance" "DoubleComplex.Bounded.modR DoubleComplex.instModuleE₂II DoubleComplex.instAddCommGroupE₂II DoubleComplex.Bounded.abGrp DoubleComplex.instAddCommGroupE₂I AlgebraicGeometry.ChowDatum.hι_closed AlgebraicGeometry.ChowDatumProj.hιN_closed AlgebraicGeometry.ChowDatumProj.hp_proper AlgebraicGeometry.ChowDatum.hp_isoU AlgebraicGeometry.ChowDatum.hp_proper AlgebraicGeometry.ProjSpace.algebraAway AlgebraicGeometry.ProjSpace.instIsProperProdOverπ AlgebraicGeometry.ChowDatumProj.hp_isoU AlgebraicGeometry.ProjSpace.isProper_π AlgebraicGeometry.ProjSpace.finiteType_mvPolynomial ProjSpaceCech.GradedModule.H.module ProjSpaceCech.GradedModule.H.addCommGroup ProjSpaceCech.GradedModule.sec.instAdd ProjSpaceCech.GradedModule.sec.instNeg ProjSpaceCech.GradedModule.acg ProjSpaceCech.GradedModule.Frac.setoid ProjSpaceCech.GradedModule.modR ProjSpaceCech.GradedModule.sec.instModule ProjSpaceCech.GradedModule.sec.instAddCommGroup ProjSpaceCech.GradedModule.sec.instZero ProjSpaceCech.GradedModule.Presentation.fJ ProjSpaceCech.GradedModule.sec.instSMul ProjSpaceCech.Twist.H.module ProjSpaceCech.Idx.instFintype ProjSpaceCech.Twist.H.addCommGroup ProjSpaceCech.Idx.instDecidableEq ProjSpaceCech.Twist.Mon.instDecidableEq ProjSpaceCech.Twist.cochain.instAddCommGroup ProjSpaceCech.Twist.cochain.instModule AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.instFundamentalIdentityOfSumRamificationInertia"
p2m_attr_erase "instance" "AlgebraicCurve.Place.instIsScalarTowerResidueFieldRestrictPushforward AlgebraicCurve.Place.instAlgebraResidueFieldRestrictPushforward AlgebraicCurve.Place.instIsLocalHomRestrictInclusion AlgebraicGeometry.SmoothOfRelativeDimension.fiberToSpecResidueField AlgebraicGeometry.SmoothOfRelativeDimension.pullback_snd AlgebraicGeometry.SmoothOfRelativeDimension.pullback_fst AlgebraicGeometry.SmoothOfRelativeDimension.smooth_one AlgebraicGeometry.SmoothProperCurve.isIntegral_pullback_Spec_field AlgebraicGeometry.IsProper.fiberToSpecResidueField AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions ModularCurve.Gamma0Pair.isElliptic AlgebraicCurve.instHasLocalResidue_of_hasCanonicalLocalResidueK AlgebraicCurve.instHasCanonicalLocalResidueK_of_hasCanonicalLocalResidueKStar AlgebraicCurve.Place.kw_ffgc_finiteDimensional_adicCompletion instAlgebraSubtypeMemValuationSubring_definitions AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersIntegersCompletion ModularCurve.KwF4gRRTate.instAlgebraKAdicCompletionIntegers AlgebraicCurve.Place.kw_ffgc_continuousSMul_adicCompletionComap AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersCompletionCompletion IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions AlgebraicCurve.instHasCanonicalLocalResidueK AlgebraicCurve.Place.instAlgebra_restrictResidueField AlgebraicCurve.Place.instIsScalarTower_restrictResidueField AlgebraicCurve.instHasLocalResidue AlgebraicCurve.HasSeparableResidue.of_perfectField_of_isCurveOver AlgebraicCurve.HasSeparableResidue.of_perfectField AlgebraicCurve.Place.instIsLocalHom_restrictSubringHom AlgebraicCurve.instHasCanonicalLocalResidueKStar ModularCurve.KwNo6Pin.isLocalRing_completion"
p2m_attr_erase "simp" "AlgebraicGeometry.Scheme.Hom.kaehlerPresheaf_obj PresheafOfModules.exteriorPower_map_ιMulti PresheafOfModules.ExteriorPower.appₗ_apply AlgebraicGeometry.Scheme.Modules.exteriorPower_obj AlgebraicGeometry.Scheme.TwoAffineOpenCover.mk.injEq AlgebraicGeometry.Scheme.TwoAffineOpenCover.mk.sizeOf_spec AlgebraicGeometry.Scheme.TwoAffineOpenCover.pullback_U1 AlgebraicGeometry.Scheme.TwoAffineOpenCover.pullback_U0 TwoChartCech.Sections.mk.injEq TwoChartCech.Cover.mk.injEq TwoChartCech.GrothendieckComplex.mk.injEq TwoChartCech.Sections.mk.sizeOf_spec TwoChartCech.Cover.mk.sizeOf_spec TwoChartCech.Cover.lineBundle_r0_apply TwoChartCech.GrothendieckComplex.mk.sizeOf_spec TwoChartCech.Cover.lineBundle_r1_apply CoherentBaseChange.TwoTermComplex.mk.sizeOf_spec CoherentBaseChange.TwoTermComplex.mk.injEq RegularLocalRingQuotientAscent.dualNumberFst_apply AlgebraicCurve.CurveModel.coe_gInf AlgebraicCurve.CurveModel.coe_tInvChart AlgebraicCurve.CurveModel.ιInf_gluedToBase_assoc AlgebraicCurve.CurveModel.ιInf_gluedToBase AlgebraicCurve.CurveModel.primeOfι₀_asIdeal AlgebraicCurve.CurveModel.coe_tChart AlgebraicCurve.CurveModel.ι₀_gluedToBase_assoc AlgebraicCurve.CurveModel.primeOfιInf_asIdeal AlgebraicCurve.CurveModel.ι₀_gluedToBase AlgebraicCurve.CurveModel.coe_tma AlgebraicCurve.CurveModel.coe_primeEquivChartPlaces AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicGeometry.Scheme.OrderedAffineCover.mk.injEq AlgebraicGeometry.OModulePresheaf.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCover.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.mk.injEq"
p2m_attr_erase "simp" "AlgebraicGeometry.OModulePresheaf.prod_obj AlgebraicGeometry.OModulePresheaf.restrOpen_obj AlgebraicGeometry.OModulePresheaf.DevissageStep.mk.injEq AlgebraicGeometry.OModulePresheaf.pushforward_obj AlgebraicGeometry.OModulePresheaf.im_obj AlgebraicGeometry.OModulePresheaf.pow_obj AlgebraicGeometry.OModulePresheaf.fstHom_app AlgebraicGeometry.OModulePresheaf.ker_obj AlgebraicGeometry.OModulePresheaf.coker_obj AlgebraicGeometry.OModulePresheaf.DevissageStep.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCover.preimage_U AlgebraicGeometry.OModulePresheaf.sndHom_app AlgebraicGeometry.OModulePresheaf.Hom.mk.injEq AlgebraicGeometry.OModulePresheaf.Hom.id_app AlgebraicGeometry.OModulePresheaf.AffHom.appSections_apply AlgebraicGeometry.OModulePresheaf.AffHom.comp_app AlgebraicGeometry.OModulePresheaf.AffSES.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.AffHom.kerMap_coe AlgebraicGeometry.OModulePresheaf.AffHom.id_app AlgebraicGeometry.OModulePresheaf.Hom.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.Hom.toAffHom_app AlgebraicGeometry.OModulePresheaf.SES.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.AffHom.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.Hom.comp_app AlgebraicGeometry.OModulePresheaf.SES.mk.injEq AlgebraicGeometry.OModulePresheaf.AffHom.mk.injEq AlgebraicGeometry.OModulePresheaf.Hom.appSections_apply AlgebraicGeometry.OModulePresheaf.AffSES.mk.injEq AlgebraicGeometry.OModulePresheaf.Leray.restrictToPreimage_U AlgebraicGeometry.Scheme.OrderedAffineCover.toCoverOf_U AlgebraicGeometry.Scheme.OrderedAffineCoverOf.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCoverOf.mk.injEq AlgebraicGeometry.Scheme.OrderedAffineCover.restrict_U DoubleComplex.Bounded.mk.injEq DoubleComplex.Bounded.mk.sizeOf_spec DoubleComplex.Convergence.mk.injEq DoubleComplex.Convergence.mk.sizeOf_spec DoubleComplex.SubQuot.mk.sizeOf_spec DoubleComplex.SubQuot.mk.injEq AlgebraicGeometry.ChowDatumProj.mk.sizeOf_spec"
p2m_attr_erase "simp" "AlgebraicGeometry.ChowDatum.mk.sizeOf_spec AlgebraicGeometry.ChowDatumProj.mk.injEq AlgebraicGeometry.ChowDatum.mk.injEq ProjSpaceCech.GradedModule.mk.injEq ProjSpaceCech.GradedModule.mk.sizeOf_spec ProjSpaceCech.GradedModule.Frac.mk.sizeOf_spec ProjSpaceCech.GradedModule.Presentation.mk.injEq ProjSpaceCech.GradedModule.Frac.mk.injEq ProjSpaceCech.GradedModule.Presentation.mk.sizeOf_spec ProjSpaceCech.GradedModule.Hom.shift_toLinearMap ProjSpaceCech.GradedModule.Hom.mk.sizeOf_spec ProjSpaceCech.GradedModule.Hom.mk.injEq AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.Divisor.mapRestrict_single AlgebraicCurve.Divisor.pushforward_single AlgebraicCurve.Place.coe_restrictInclusion AlgebraicCurve.Place.mem_fiber AlgebraicCurve.Place.restrict_toValuationSubring AlgebraicCurve.Divisor.degree_pushforward AlgebraicCurve.Place.restrictResidueMap_residue AlgebraicCurve.Pic0.coe_pushforwardDegZeroHom AlgebraicCurve.Pic0.coe_pullbackDegZeroHom AlgebraicGeometry.SmoothProperCurve.sectionBaseChange_coe_snd AlgebraicGeometry.SmoothProperCurve.sectionBaseChange_coe_fst AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk"
p2m_attr_erase "simp" "ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Divisor.degree_pushforwardAlong AlgebraicCurve.Pic0.coe_degZeroCorrespondence AlgebraicCurve.Place.mem_fiberAlong AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.jqNModC_one ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none AlgebraicCurve.mulAdele_apply AlgebraicCurve.residuePairing_apply_coe AlgebraicCurve.mem_adeleBdd AlgebraicCurve.weilSmul_one AlgebraicCurve.diagonalHom_apply AlgebraicCurve.weilSmul_apply AlgebraicCurve.adeleSpaceMul_coe AlgebraicCurve.mulAdele_one AlgebraicCurve.Place.differentialCoeff_zero AlgebraicCurve.Place.differentialCoeff_dCoord AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.injEq AlgebraicCurve.TranscendenceTower.mk.injEq AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec AlgebraicCurve.PoleDivisorPackage.mk.injEq GoodReductionJacobian.RelativeGroupLaw.nsmul_zero"
p2m_attr_erase "simp" "GoodReductionJacobian.RelativeGroupLaw.mem_torsionSubset GoodReductionJacobian.RelativeGroupLaw.nsmul_succ ModularCurve.coe_nodeEquivOfPlaces_apply ModularCurve.widthOfPlaces_mk ModularCurve.smulNodePairEmb_apply ModularCurve.card_nodePairsOfPlaces ModularCurve.smulNodePair_snd ModularCurve.smulNodePair_fst ModularCurve.coe_nodeEquivOfPlaces_symm_apply ModularCurve.coe_jGeomGen ModularCurve.coe_jNGeomGen ModularCurve.coe_uniformizerMod ModularCurve.qSeriesBar_jModElt ModularCurve.qInftyPlaceMod_toValuationSubring ModularCurve.qInftyPlaceBar_toValuationSubring ModularCurve.qSeriesBar_zero ModularCurve.qSeriesBar_add ModularCurve.cuspInftyFull_toValuationSubring ModularCurve.qInftyPlaceRat_toValuationSubring ModularCurve.qSeriesBar_mul ModularCurve.qSeriesBar_div ModularCurve.qSeriesBar_eq_zero_iff ModularCurve.coe_uniformizerBar ModularCurve.qSeriesBar_pow ModularCurve.cuspInfty_toValuationSubring ModularCurve.qSeriesBar_one ModularCurve.qSeriesBar_inv ModularCurve.qSeriesBar_sub ModularCurve.qSeriesBar_neg ModularCurve.charLGeomModuliDictionary_single ModularCurve.specializeModuli_single ModularCurve.specializePlace_def ModularCurve.gamma0PairMap_gen ModularCurve.moduliPointMapRingHom_mk ModularCurve.Gamma0Pair.mk.injEq ModularCurve.ModuliPoint.j_mk ModularCurve.Gamma0Pair.mk.sizeOf_spec ModularCurve.gamma0PairMap_toCurve WeierstrassCurve.Affine.vcY_vcYInv WeierstrassCurve.Affine.vcXInv_vcX"
p2m_attr_erase "simp" "WeierstrassCurve.Affine.Point.vcFun_zero WeierstrassCurve.Affine.vcX_vcXInv WeierstrassCurve.Affine.vcYInv_vcY WeierstrassCurve.Affine.Point.vcInvFun_zero WeierstrassCurve.ratPointHom_apply WeierstrassCurve.ratPointMap_zero AlgebraicCurve.coe_cechH0Equiv_apply AlgebraicCurve.cechH1ToH1_mk AlgebraicCurve.lSpaceOn_univ AlgebraicCurve.lSpaceOn_empty AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.sizeOf_spec AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.injEq AlgebraicCurve.adeleSingle_coe AlgebraicCurve.kaehlerResidueTermKFam_apply AlgebraicCurve.Place.LocalResidueData.mk.injEq AlgebraicCurve.Place.LocalResidueData.mk.sizeOf_spec AlgebraicCurve.Place.kw_ffgc_adicCompletionComapIntegers_coe AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.sizeOf_spec AlgebraicCurve.Place.mem_simplePoleSubmodule AlgebraicCurve.Place.coe_uniformizerSubring ModularCurve.Lg37.Lg37CompletionSection.mk.injEq AlgebraicCurve.Place.CoefficientFieldSection.mk.injEq AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.injEq ModularCurve.Lg37.Lg37CompletionSection.mk.sizeOf_spec AlgebraicCurve.Place.CoefficientFieldSection.mk.sizeOf_spec AlgebraicCurve.Place.poleSubmodule_one AlgebraicCurve.Place.mem_poleSubmodule GoodReductionJacobian.prodInr_comp_prodFst GoodReductionJacobian.RelativeGroupLaw.prod_inv GoodReductionJacobian.prodInl_comp_prodSnd GoodReductionJacobian.prodInr_comp_prodSnd GoodReductionJacobian.prodInl_comp_prodFst GoodReductionJacobian.prodFstPt_prodPairPt GoodReductionJacobian.prodFst_coe GoodReductionJacobian.prodSndPt_prodPairPt GoodReductionJacobian.RelativeGroupLaw.prod_one GoodReductionJacobian.prodPairPt_coe GoodReductionJacobian.prodPairPt_prodFstPt_prodSndPt GoodReductionJacobian.prodFstPt_coe GoodReductionJacobian.RelativeGroupLaw.prod_mul"
p2m_attr_erase "simp" "GoodReductionJacobian.prodSndPt_coe GoodReductionJacobian.prodSnd_coe NeronModelInfra.NeronModelPropertyBundle.endExtensionEquiv_symm_restrict NeronModelInfra.schemeHomOverComp_id_left NeronModelInfra.schemeHomOverComp_id_right NeronModelInfra.schemeHomOverId_coe NeronModelInfra.NeronModelPropertyBundle.endExtensionEquiv_apply NeronModelInfra.NeronModelPropertyBundle.restrict_endExtensionEquiv_symm NeronModelInfra.schemeHomOverComp_coe GoodReductionJacobian.relativeGroupLawOfGrpObj_inv GoodReductionJacobian.relativeGroupLawOfGrpObj_mul GoodReductionJacobian.overHomEquivSchemeHomOver_apply_coe GoodReductionJacobian.relativeGroupLawOfGrpObj_one GoodReductionJacobian.overHomEquivSchemeHomOver_symm_apply_left"

set_option autoImplicit false

noncomputable section

p2m_open "CategoryTheory AlgebraicGeometry NeronModelInfra GoodReductionJacobian IsDedekindDomain AlgebraicCurve~H1 QuaternionAlgebra CerednikDrinfeld CerednikDrinfeld.QM"
open scoped Quaternion TensorProduct NumberField MatrixGroups Topology Pointwise

namespace K8Assembly

section MapPt
variable {R : Type} [CommRing R]

theorem mapPt_congr' {A A' : Scheme.{0}} {f : A ⟶ Spec (CommRingCat.of R)} {f' : A' ⟶ Spec (CommRingCat.of R)}
    {φ ψ : A ⟶ A'} (h : φ = ψ) (hφ : φ ≫ f' = f) (hψ : ψ ≫ f' = f)
    {T : Scheme.{0}} {t : T ⟶ Spec (CommRingCat.of R)} (P : SchemeHomOver t f) :
    mapPt φ hφ P = mapPt ψ hψ P := by subst h; rfl

theorem mapPt_of_eq_id {A : Scheme.{0}} {f : A ⟶ Spec (CommRingCat.of R)}
    {φ : A ⟶ A} (hφ : φ ≫ f = f) (h : φ = 𝟙 A)
    {T : Scheme.{0}} {t : T ⟶ Spec (CommRingCat.of R)} (P : SchemeHomOver t f) :
    mapPt φ hφ P = P := by subst h; exact Subtype.ext (Category.comp_id _)

theorem mapPt_of_eq_comp {A A' A'' : Scheme.{0}} {f : A ⟶ Spec (CommRingCat.of R)} {f' : A' ⟶ Spec (CommRingCat.of R)}
    {f'' : A'' ⟶ Spec (CommRingCat.of R)}
    {χ : A ⟶ A''} {φ : A ⟶ A'} {ψ : A' ⟶ A''} (hχ : χ ≫ f'' = f) (h : χ = φ ≫ ψ) (hφ : φ ≫ f' = f) (hψ : ψ ≫ f'' = f')
    {T : Scheme.{0}} {t : T ⟶ Spec (CommRingCat.of R)} (P : SchemeHomOver t f) :
    mapPt χ hχ P = mapPt ψ hψ (mapPt φ hφ P) := by subst h; exact Subtype.ext (Category.assoc _ _ _).symm
end MapPt

theorem appLE_congr_pt {X Y : Scheme.{0}} {p q : X ⟶ Y} (hpq : p = q) (U : Y.Opens)
    (h : ⊤ ≤ p ⁻¹ᵁ U) (h' : ⊤ ≤ q ⁻¹ᵁ U) : p.appLE U ⊤ h = q.appLE U ⊤ h' := by subst hpq; rfl

section Transport
variable {g : ℕ}

def lattMap (Pm : (Fin g → ℂ) ≃ₗ[ℂ] (Fin g → ℂ)) (Λ₀ : Submodule ℤ (Fin g → ℂ)) : Submodule ℤ (Fin g → ℂ) :=
  Λ₀.map (Pm : (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ)).toAddMonoidHom.toIntLinearMap

theorem mem_lattMap (Pm : (Fin g → ℂ) ≃ₗ[ℂ] (Fin g → ℂ)) (Λ₀ : Submodule ℤ (Fin g → ℂ)) (v : Fin g → ℂ) :
    v ∈ lattMap Pm Λ₀ ↔ Pm.symm v ∈ Λ₀ := by
  simp only [lattMap, Submodule.mem_map]
  constructor
  · rintro ⟨w, hw, rfl⟩
    simpa using hw
  · intro h
    exact ⟨Pm.symm v, h, by simp⟩

theorem le_comap_lattMap (Pm : (Fin g → ℂ) ≃ₗ[ℂ] (Fin g → ℂ)) (Λ₀ : Submodule ℤ (Fin g → ℂ)) :
    Λ₀.toAddSubgroup ≤ (lattMap Pm Λ₀).toAddSubgroup.comap (Pm : (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ)).toAddMonoidHom := by
  intro v hv
  simp only [AddSubgroup.mem_comap, Submodule.mem_toAddSubgroup, LinearMap.toAddMonoidHom_coe,
    LinearEquiv.coe_coe, mem_lattMap, LinearEquiv.symm_apply_apply]
  exact hv

theorem le_comap_lattMap_symm (Pm : (Fin g → ℂ) ≃ₗ[ℂ] (Fin g → ℂ)) (Λ₀ : Submodule ℤ (Fin g → ℂ)) :
    (lattMap Pm Λ₀).toAddSubgroup ≤
      Λ₀.toAddSubgroup.comap (Pm.symm : (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ)).toAddMonoidHom := by
  intro v hv
  simp only [AddSubgroup.mem_comap, Submodule.mem_toAddSubgroup, LinearMap.toAddMonoidHom_coe,
    LinearEquiv.coe_coe]
  exact (mem_lattMap Pm Λ₀ v).1 hv

def qIso (Pm : (Fin g → ℂ) ≃ₗ[ℂ] (Fin g → ℂ)) (Λ₀ : Submodule ℤ (Fin g → ℂ)) :
    ((Fin g → ℂ) ⧸ Λ₀.toAddSubgroup) ≃+ ((Fin g → ℂ) ⧸ (lattMap Pm Λ₀).toAddSubgroup) where
  toFun := QuotientAddGroup.map _ _ _ (le_comap_lattMap Pm Λ₀)
  invFun := QuotientAddGroup.map _ _ _ (le_comap_lattMap_symm Pm Λ₀)
  left_inv x := by
    obtain ⟨z, rfl⟩ := QuotientAddGroup.mk_surjective x
    simp
  right_inv x := by
    obtain ⟨z, rfl⟩ := QuotientAddGroup.mk_surjective x
    simp
  map_add' x y := map_add _ x y

@[scoped simp] theorem qIso_mk (Pm : (Fin g → ℂ) ≃ₗ[ℂ] (Fin g → ℂ)) (Λ₀ : Submodule ℤ (Fin g → ℂ)) (v : Fin g → ℂ) :
    qIso Pm Λ₀ (v : (Fin g → ℂ) ⧸ Λ₀.toAddSubgroup) = ((Pm v : Fin g → ℂ) : (Fin g → ℂ) ⧸ (lattMap Pm Λ₀).toAddSubgroup) :=
  rfl

@[scoped simp] theorem qIso_symm_mk (Pm : (Fin g → ℂ) ≃ₗ[ℂ] (Fin g → ℂ)) (Λ₀ : Submodule ℤ (Fin g → ℂ)) (v : Fin g → ℂ) :
    (qIso Pm Λ₀).symm (v : (Fin g → ℂ) ⧸ (lattMap Pm Λ₀).toAddSubgroup) =
      ((Pm.symm v : Fin g → ℂ) : (Fin g → ℂ) ⧸ Λ₀.toAddSubgroup) :=
  rfl

variable {G : Scheme.{0}} {f : G ⟶ Spec (CommRingCat.of ℂ)}

def transE (Λ₀ : Submodule ℤ (Fin g → ℂ))
    (e₀ : SchemeHomOver (𝟙 (Spec (CommRingCat.of ℂ))) f ≃ ((Fin g → ℂ) ⧸ Λ₀.toAddSubgroup))
    (Pm : (Fin g → ℂ) ≃ₗ[ℂ] (Fin g → ℂ)) :
    SchemeHomOver (𝟙 (Spec (CommRingCat.of ℂ))) f ≃ ((Fin g → ℂ) ⧸ (lattMap Pm Λ₀).toAddSubgroup) :=
  e₀.trans (qIso Pm Λ₀).toEquiv

theorem transE_apply (Λ₀ : Submodule ℤ (Fin g → ℂ))
    (e₀ : SchemeHomOver (𝟙 (Spec (CommRingCat.of ℂ))) f ≃ ((Fin g → ℂ) ⧸ Λ₀.toAddSubgroup))
    (Pm : (Fin g → ℂ) ≃ₗ[ℂ] (Fin g → ℂ)) (P : SchemeHomOver (𝟙 (Spec (CommRingCat.of ℂ))) f) :
    transE Λ₀ e₀ Pm P = qIso Pm Λ₀ (e₀ P) := rfl

theorem transE_symm_mk (Λ₀ : Submodule ℤ (Fin g → ℂ))
    (e₀ : SchemeHomOver (𝟙 (Spec (CommRingCat.of ℂ))) f ≃ ((Fin g → ℂ) ⧸ Λ₀.toAddSubgroup))
    (Pm : (Fin g → ℂ) ≃ₗ[ℂ] (Fin g → ℂ)) (v : Fin g → ℂ) :
    (transE Λ₀ e₀ Pm).symm (v : (Fin g → ℂ) ⧸ (lattMap Pm Λ₀).toAddSubgroup) =
      e₀.symm ((Pm.symm v : Fin g → ℂ) : (Fin g → ℂ) ⧸ Λ₀.toAddSubgroup) := by
  rfl

theorem transE_eq_iff (Λ₀ : Submodule ℤ (Fin g → ℂ))
    (e₀ : SchemeHomOver (𝟙 (Spec (CommRingCat.of ℂ))) f ≃ ((Fin g → ℂ) ⧸ Λ₀.toAddSubgroup))
    (Pm : (Fin g → ℂ) ≃ₗ[ℂ] (Fin g → ℂ)) (P : SchemeHomOver (𝟙 (Spec (CommRingCat.of ℂ))) f) (v : Fin g → ℂ) :
    transE Λ₀ e₀ Pm P = (v : (Fin g → ℂ) ⧸ (lattMap Pm Λ₀).toAddSubgroup) ↔
      e₀ P = ((Pm.symm v : Fin g → ℂ) : (Fin g → ℂ) ⧸ Λ₀.toAddSubgroup) := by
  rw [Equiv.apply_eq_iff_eq_symm_apply, transE_symm_mk, ← Equiv.apply_eq_iff_eq_symm_apply]

end Transport

section Clauses
variable {g : ℕ} {G : Scheme.{0}} {f : G ⟶ Spec (CommRingCat.of ℂ)}

theorem clauseE1 (L : RelativeGroupLaw ℂ f) (Λ₀ : Submodule ℤ (Fin g → ℂ))
    (e₀ : SchemeHomOver (𝟙 (Spec (CommRingCat.of ℂ))) f ≃ ((Fin g → ℂ) ⧸ Λ₀.toAddSubgroup))
    (Pm : (Fin g → ℂ) ≃ₗ[ℂ] (Fin g → ℂ))
    (he : ∀ P Q : SchemeHomOver (𝟙 (Spec (CommRingCat.of ℂ))) f,
      e₀ (L.mul (𝟙 (Spec (CommRingCat.of ℂ))) P Q) = e₀ P + e₀ Q)
    (P Q : SchemeHomOver (𝟙 (Spec (CommRingCat.of ℂ))) f) :
    transE Λ₀ e₀ Pm (L.mul (𝟙 (Spec (CommRingCat.of ℂ))) P Q) = transE Λ₀ e₀ Pm P + transE Λ₀ e₀ Pm Q := by
  simp only [transE_apply, he, map_add]

theorem clauseL1full (Λ₀ : Submodule ℤ (Fin 2 → ℂ)) (Pm : (Fin 2 → ℂ) ≃ₗ[ℂ] (Fin 2 → ℂ))
    (hL1 : ∃ b₀ : Module.Basis (Fin (2 * 2)) ℝ (Fin 2 → ℂ), Λ₀ = Submodule.span ℤ (Set.range b₀)) :
    ∃ b₀ : Module.Basis (Fin 4) ℝ (Fin 2 → ℂ), lattMap Pm Λ₀ = Submodule.span ℤ (Set.range b₀) := by
  obtain ⟨b₀, hb⟩ := hL1
  refine ⟨b₀.map (Pm.restrictScalars ℝ), ?_⟩
  rw [hb, lattMap, Submodule.map_span]
  congr 1
  ext v
  simp only [Set.mem_image, Set.mem_range]
  constructor
  · rintro ⟨w, ⟨i, rfl⟩, rfl⟩
    exact ⟨i, by simp⟩
  · rintro ⟨i, rfl⟩
    exact ⟨b₀ i, ⟨i, rfl⟩, by simp⟩

theorem clauseAN (Λ₀ : Submodule ℤ (Fin g → ℂ))
    (e₀ : SchemeHomOver (𝟙 (Spec (CommRingCat.of ℂ))) f ≃ ((Fin g → ℂ) ⧸ Λ₀.toAddSubgroup))
    (Pm : (Fin g → ℂ) ≃ₗ[ℂ] (Fin g → ℂ))
    (hAN : ∀ (U : G.Opens) (φ : Γ(G, U)),
      IsOpen {v : Fin g → ℂ | ⊤ ≤ (e₀.symm (v : (Fin g → ℂ) ⧸ Λ₀.toAddSubgroup)).1 ⁻¹ᵁ U} ∧
      ∃ F : (Fin g → ℂ) → ℂ,
        DifferentiableOn ℂ F {v : Fin g → ℂ | ⊤ ≤ (e₀.symm (v : (Fin g → ℂ) ⧸ Λ₀.toAddSubgroup)).1 ⁻¹ᵁ U} ∧
        ∀ (v : Fin g → ℂ) (h : ⊤ ≤ (e₀.symm (v : (Fin g → ℂ) ⧸ Λ₀.toAddSubgroup)).1 ⁻¹ᵁ U),
          F v = (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom ((((e₀.symm (v : (Fin g → ℂ) ⧸ Λ₀.toAddSubgroup)).1.appLE U ⊤ h) φ)))
    (U : G.Opens) (φ : Γ(G, U)) :
    IsOpen {v : Fin g → ℂ | ⊤ ≤ ((transE Λ₀ e₀ Pm).symm (v : (Fin g → ℂ) ⧸ (lattMap Pm Λ₀).toAddSubgroup)).1 ⁻¹ᵁ U} ∧
      ∃ F : (Fin g → ℂ) → ℂ,
        DifferentiableOn ℂ F {v : Fin g → ℂ | ⊤ ≤ ((transE Λ₀ e₀ Pm).symm (v : (Fin g → ℂ) ⧸ (lattMap Pm Λ₀).toAddSubgroup)).1 ⁻¹ᵁ U} ∧
        ∀ (v : Fin g → ℂ) (h : ⊤ ≤ ((transE Λ₀ e₀ Pm).symm (v : (Fin g → ℂ) ⧸ (lattMap Pm Λ₀).toAddSubgroup)).1 ⁻¹ᵁ U),
          F v = (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom
            (((((transE Λ₀ e₀ Pm).symm (v : (Fin g → ℂ) ⧸ (lattMap Pm Λ₀).toAddSubgroup)).1.appLE U ⊤ h) φ)) := by
  obtain ⟨hopen, F, hF, hFv⟩ := hAN U φ
  have hset : {v : Fin g → ℂ | ⊤ ≤ ((transE Λ₀ e₀ Pm).symm (v : (Fin g → ℂ) ⧸ (lattMap Pm Λ₀).toAddSubgroup)).1 ⁻¹ᵁ U} =
      (Pm.symm : (Fin g → ℂ) → (Fin g → ℂ)) ⁻¹'
        {v : Fin g → ℂ | ⊤ ≤ (e₀.symm (v : (Fin g → ℂ) ⧸ Λ₀.toAddSubgroup)).1 ⁻¹ᵁ U} := by
    ext v
    simp only [Set.mem_setOf_eq, Set.mem_preimage, transE_symm_mk]
  have hcont : Continuous (Pm.symm : (Fin g → ℂ) → (Fin g → ℂ)) := by
    simpa using Pm.symm.toContinuousLinearEquiv.continuous
  have hdiff : Differentiable ℂ (Pm.symm : (Fin g → ℂ) → (Fin g → ℂ)) := by
    simpa using (Pm.symm.toContinuousLinearEquiv : (Fin g → ℂ) →L[ℂ] (Fin g → ℂ)).differentiable
  refine ⟨?_, F ∘ Pm.symm, ?_, ?_⟩
  · rw [hset]; exact hopen.preimage hcont
  · rw [hset]; exact hF.comp hdiff.differentiableOn (Set.mapsTo_preimage _ _)
  · intro v h
    have h' : ⊤ ≤ (e₀.symm ((Pm.symm v : Fin g → ℂ) : (Fin g → ℂ) ⧸ Λ₀.toAddSubgroup)).1 ⁻¹ᵁ U := by
      rw [← transE_symm_mk]; exact h
    show F (Pm.symm v) = _
    rw [hFv (Pm.symm v) h', appLE_congr_pt (congrArg Subtype.val (transE_symm_mk Λ₀ e₀ Pm v)) U h h']

theorem clauseCOV {G : Scheme.{0}} {f : G ⟶ Spec (CommRingCat.of ℂ)} (Λ₀ : Submodule ℤ (Fin 2 → ℂ))
    (e₀ : SchemeHomOver (𝟙 (Spec (CommRingCat.of ℂ))) f ≃ ((Fin 2 → ℂ) ⧸ Λ₀.toAddSubgroup))
    (Pm : (Fin 2 → ℂ) ≃ₗ[ℂ] (Fin 2 → ℂ))
    (hCOV : ∀ v₀ : Fin 2 → ℂ,
      ∃ (U : G.Opens) (t : Fin 2 → Γ(G, U)) (ε : ℝ) (D : (Fin 2 → ℂ) ≃L[ℂ] (Fin 2 → ℂ))
        (F : (Fin 2 → ℂ) → (Fin 2 → ℂ)),
        0 < ε ∧
        (∀ v ∈ Metric.ball v₀ ε, ⊤ ≤ (e₀.symm (v : (Fin 2 → ℂ) ⧸ Λ₀.toAddSubgroup)).1 ⁻¹ᵁ U) ∧
        (∀ (v : Fin 2 → ℂ) (h : ⊤ ≤ (e₀.symm (v : (Fin 2 → ℂ) ⧸ Λ₀.toAddSubgroup)).1 ⁻¹ᵁ U), v ∈ Metric.ball v₀ ε →
          F v = fun i : Fin 2 => (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom ((((e₀.symm (v : (Fin 2 → ℂ) ⧸ Λ₀.toAddSubgroup)).1.appLE U ⊤ h) (t i)))) ∧
        HasFDerivAt F (D : (Fin 2 → ℂ) →L[ℂ] (Fin 2 → ℂ)) v₀)
    (v₀ : Fin 2 → ℂ) :
    ∃ (U : G.Opens) (f₁ f₂ : Γ(G, U)) (ε : ℝ) (D : (Fin 2 → ℂ) ≃L[ℂ] (Fin 2 → ℂ))
      (F : (Fin 2 → ℂ) → (Fin 2 → ℂ)),
      0 < ε ∧
      (∀ v ∈ Metric.ball v₀ ε, ⊤ ≤ ((transE Λ₀ e₀ Pm).symm (v : (Fin 2 → ℂ) ⧸ (lattMap Pm Λ₀).toAddSubgroup)).1 ⁻¹ᵁ U) ∧
      (∀ (v : Fin 2 → ℂ) (h : ⊤ ≤ ((transE Λ₀ e₀ Pm).symm (v : (Fin 2 → ℂ) ⧸ (lattMap Pm Λ₀).toAddSubgroup)).1 ⁻¹ᵁ U),
        v ∈ Metric.ball v₀ ε →
        F v = ![(Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom
                  ((((transE Λ₀ e₀ Pm).symm (v : (Fin 2 → ℂ) ⧸ (lattMap Pm Λ₀).toAddSubgroup)).1.appLE U ⊤ h) f₁),
                (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom
                  ((((transE Λ₀ e₀ Pm).symm (v : (Fin 2 → ℂ) ⧸ (lattMap Pm Λ₀).toAddSubgroup)).1.appLE U ⊤ h) f₂)]) ∧
      HasFDerivAt F (D : (Fin 2 → ℂ) →L[ℂ] (Fin 2 → ℂ)) v₀ := by
  obtain ⟨U, t, ε, D, F, hε, hball, hFv, hD⟩ := hCOV (Pm.symm v₀)
  set A : (Fin 2 → ℂ) ≃L[ℂ] (Fin 2 → ℂ) := Pm.symm.toContinuousLinearEquiv with hAdef
  have hA : ∀ v, A v = Pm.symm v := fun v => by simp [hAdef]
  have hcont : Continuous (Pm.symm : (Fin 2 → ℂ) → (Fin 2 → ℂ)) := by
    simpa using Pm.symm.toContinuousLinearEquiv.continuous
  have hpre : IsOpen ((Pm.symm : (Fin 2 → ℂ) → (Fin 2 → ℂ)) ⁻¹' Metric.ball (Pm.symm v₀) ε) :=
    Metric.isOpen_ball.preimage hcont
  obtain ⟨ε', hε', hsub⟩ := Metric.isOpen_iff.mp hpre v₀ (Metric.mem_ball_self hε)
  refine ⟨U, t 0, t 1, ε', A.trans D, F ∘ Pm.symm, hε', ?_, ?_, ?_⟩
  · intro v hv
    rw [transE_symm_mk]
    exact hball (Pm.symm v) (hsub hv)
  · intro v h hv
    have h' : ⊤ ≤ (e₀.symm ((Pm.symm v : Fin 2 → ℂ) : (Fin 2 → ℂ) ⧸ Λ₀.toAddSubgroup)).1 ⁻¹ᵁ U := by
      rw [← transE_symm_mk]; exact h
    show F (Pm.symm v) = _
    rw [hFv (Pm.symm v) h' (hsub hv),
      appLE_congr_pt (congrArg Subtype.val (transE_symm_mk Λ₀ e₀ Pm v)) U h h']
    funext i
    fin_cases i <;> simp
  · have h1 : HasFDerivAt F (D : (Fin 2 → ℂ) →L[ℂ] (Fin 2 → ℂ)) (A v₀) := by rw [hA]; exact hD
    have h2 := h1.comp v₀ A.hasFDerivAt
    have hfun : (F ∘ (A : (Fin 2 → ℂ) → (Fin 2 → ℂ))) = F ∘ (Pm.symm : (Fin 2 → ℂ) → (Fin 2 → ℂ)) :=
      funext fun v => by simp [hA]
    have hder : ((D : (Fin 2 → ℂ) →L[ℂ] (Fin 2 → ℂ)).comp (A : (Fin 2 → ℂ) →L[ℂ] (Fin 2 → ℂ))) =
        ((A.trans D : (Fin 2 → ℂ) ≃L[ℂ] (Fin 2 → ℂ)) : (Fin 2 → ℂ) →L[ℂ] (Fin 2 → ℂ)) := by
      ext v; simp
    rw [hfun, hder] at h2
    exact h2

end Clauses

section FEC
variable {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} {N : ℕ}

def LinPred {G G' : Scheme.{0}} {f : G ⟶ Spec (CommRingCat.of ℂ)} {f' : G' ⟶ Spec (CommRingCat.of ℂ)} {g g' : ℕ}
    (Λ₀ : Submodule ℤ (Fin g → ℂ)) (Λ₀' : Submodule ℤ (Fin g' → ℂ))
    (e₀ : SchemeHomOver (𝟙 (Spec (CommRingCat.of ℂ))) f ≃ ((Fin g → ℂ) ⧸ Λ₀.toAddSubgroup))
    (e₀' : SchemeHomOver (𝟙 (Spec (CommRingCat.of ℂ))) f' ≃ ((Fin g' → ℂ) ⧸ Λ₀'.toAddSubgroup))
    (u : G ⟶ G') (hu : u ≫ f' = f) (T : (Fin g → ℂ) →ₗ[ℂ] (Fin g' → ℂ)) : Prop :=
  (∀ v ∈ Λ₀, T v ∈ Λ₀') ∧
    ∀ (P : SchemeHomOver (𝟙 (Spec (CommRingCat.of ℂ))) f) (v : Fin g → ℂ),
      e₀ P = (v : (Fin g → ℂ) ⧸ Λ₀.toAddSubgroup) →
      e₀' (mapPt u hu P) = ((T v : Fin g' → ℂ) : (Fin g' → ℂ) ⧸ Λ₀'.toAddSubgroup)

theorem rho_laws (E : FakeEllipticCurve Λ N ℂ) (Λ₀ : Submodule ℤ (Fin 2 → ℂ))
    (e₀ : SchemeHomOver (𝟙 (Spec (CommRingCat.of ℂ))) E.f ≃ ((Fin 2 → ℂ) ⧸ Λ₀.toAddSubgroup))
    (he : ∀ P Q : SchemeHomOver (𝟙 (Spec (CommRingCat.of ℂ))) E.f,
      e₀ (E.L.mul (𝟙 (Spec (CommRingCat.of ℂ))) P Q) = e₀ P + e₀ Q)
    (ρ : ↥Λ → ((Fin 2 → ℂ) →ₗ[ℂ] (Fin 2 → ℂ)))
    (hρ : ∀ x : ↥Λ, LinPred Λ₀ Λ₀ e₀ e₀ (E.act x) (E.act_over x) (ρ x))
    (hρu : ∀ (x : ↥Λ) (T : (Fin 2 → ℂ) →ₗ[ℂ] (Fin 2 → ℂ)),
      LinPred Λ₀ Λ₀ e₀ e₀ (E.act x) (E.act_over x) T → T = ρ x) :
    (∀ h : (1 : ℍ[ℚ, a, b]) ∈ Λ, ρ ⟨1, h⟩ = LinearMap.id) ∧
    (∀ (x y : ↥Λ) (h : (x : ℍ[ℚ, a, b]) * (y : ℍ[ℚ, a, b]) ∈ Λ),
      ρ ⟨(x : ℍ[ℚ, a, b]) * (y : ℍ[ℚ, a, b]), h⟩ = (ρ x).comp (ρ y)) ∧
    (∀ x y : ↥Λ, ρ (x + y) = ρ x + ρ y) := by
  refine ⟨fun h => ?_, fun x y h => ?_, fun x y => ?_⟩
  · symm
    refine hρu ⟨1, h⟩ LinearMap.id ⟨fun v hv => hv, fun P v hP => ?_⟩
    rw [mapPt_of_eq_id (E.act_over ⟨1, h⟩) (E.act_one h)]
    simpa using hP
  · symm
    refine hρu ⟨(x : ℍ[ℚ, a, b]) * (y : ℍ[ℚ, a, b]), h⟩ ((ρ x).comp (ρ y))
      ⟨fun v hv => (hρ x).1 _ ((hρ y).1 v hv), fun P v hP => ?_⟩
    rw [mapPt_of_eq_comp (E.act_over _) (E.act_mul x y h) (E.act_over y) (E.act_over x)]
    exact (hρ x).2 _ _ ((hρ y).2 P v hP)
  · symm
    refine hρu (x + y) (ρ x + ρ y)
      ⟨fun v hv => Λ₀.add_mem ((hρ x).1 v hv) ((hρ y).1 v hv), fun P v hP => ?_⟩
    have hadd : mapPt (E.act (x + y)) (E.act_over (x + y)) P =
        E.L.mul (𝟙 (Spec (CommRingCat.of ℂ))) (mapPt (E.act x) (E.act_over x) P)
          (mapPt (E.act y) (E.act_over y) P) :=
      E.act_add x y _ P
    rw [hadd, he, (hρ x).2 P v hP, (hρ y).2 P v hP, LinearMap.add_apply, QuotientAddGroup.mk_add]

theorem rho_conj (ι : ℍ[ℚ, a, b] →ₐ[ℚ] Matrix (Fin 2) (Fin 2) ℝ)
    (ρ : ↥Λ → ((Fin 2 → ℂ) →ₗ[ℂ] (Fin 2 → ℂ))) (Pm : (Fin 2 → ℂ) ≃ₗ[ℂ] (Fin 2 → ℂ))
    (hPm : ∀ (x : ↥Λ) (v : Fin 2 → ℂ),
      Pm (ρ x v) = ((ι (x : ℍ[ℚ, a, b])).map (algebraMap ℝ ℂ)).mulVec (Pm v))
    (x : ↥Λ) (v : Fin 2 → ℂ) :
    Pm.symm (((ι (x : ℍ[ℚ, a, b])).map (algebraMap ℝ ℂ)).mulVec v) = ρ x (Pm.symm v) := by
  apply Pm.injective
  rw [LinearEquiv.apply_symm_apply, hPm, LinearEquiv.apply_symm_apply]

theorem isReduced_FEC (E : FakeEllipticCurve Λ N ℂ) : IsReduced E.A := by
  haveI : Smooth E.f := E.bundle.smooth
  let s : ↥(Spec (CommRingCat.of ℂ)) := default
  have huniv : (E.f.base : ↥E.A → ↥(Spec (CommRingCat.of ℂ))) ⁻¹' {s} = Set.univ := by
    ext x
    simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_univ, iff_true]
    exact Subsingleton.elim _ _
  have hconn : _root_.IsConnected (Set.univ : Set ↥E.A) := huniv ▸ E.bundle.connectedFibres s
  haveI : ConnectedSpace ↥E.A := connectedSpace_iff_univ.mpr hconn
  haveI : Nonempty ↥E.A := Set.nonempty_iff_univ_nonempty.mpr hconn.nonempty
  haveI : IsIntegral E.A := AlgebraicGeometry.isIntegral_of_smooth_of_preconnectedSpace E.f
  infer_instance

theorem clauseL1stab (E : FakeEllipticCurve Λ N ℂ) (ι : ℍ[ℚ, a, b] →ₐ[ℚ] Matrix (Fin 2) (Fin 2) ℝ)
    (Λ₀ : Submodule ℤ (Fin 2 → ℂ))
    (e₀ : SchemeHomOver (𝟙 (Spec (CommRingCat.of ℂ))) E.f ≃ ((Fin 2 → ℂ) ⧸ Λ₀.toAddSubgroup))
    (ρ : ↥Λ → ((Fin 2 → ℂ) →ₗ[ℂ] (Fin 2 → ℂ)))
    (hρ : ∀ x : ↥Λ, LinPred Λ₀ Λ₀ e₀ e₀ (E.act x) (E.act_over x) (ρ x))
    (Pm : (Fin 2 → ℂ) ≃ₗ[ℂ] (Fin 2 → ℂ))
    (hPm : ∀ (x : ↥Λ) (v : Fin 2 → ℂ),
      Pm (ρ x v) = ((ι (x : ℍ[ℚ, a, b])).map (algebraMap ℝ ℂ)).mulVec (Pm v)) :
    ∀ x ∈ Λ, ∀ v ∈ lattMap Pm Λ₀, ((ι x).map (algebraMap ℝ ℂ)).mulVec v ∈ lattMap Pm Λ₀ := by
  intro x hx v hv
  rw [mem_lattMap] at hv ⊢
  have H := (hρ ⟨x, hx⟩).1 _ hv
  rw [← rho_conj ι ρ Pm hPm ⟨x, hx⟩ v] at H
  exact H

theorem clauseE2 (E : FakeEllipticCurve Λ N ℂ) (ι : ℍ[ℚ, a, b] →ₐ[ℚ] Matrix (Fin 2) (Fin 2) ℝ)
    (Λ₀ : Submodule ℤ (Fin 2 → ℂ))
    (e₀ : SchemeHomOver (𝟙 (Spec (CommRingCat.of ℂ))) E.f ≃ ((Fin 2 → ℂ) ⧸ Λ₀.toAddSubgroup))
    (ρ : ↥Λ → ((Fin 2 → ℂ) →ₗ[ℂ] (Fin 2 → ℂ)))
    (hρ : ∀ x : ↥Λ, LinPred Λ₀ Λ₀ e₀ e₀ (E.act x) (E.act_over x) (ρ x))
    (Pm : (Fin 2 → ℂ) ≃ₗ[ℂ] (Fin 2 → ℂ))
    (hPm : ∀ (x : ↥Λ) (v : Fin 2 → ℂ),
      Pm (ρ x v) = ((ι (x : ℍ[ℚ, a, b])).map (algebraMap ℝ ℂ)).mulVec (Pm v))
    (x : ↥Λ) (P : SchemeHomOver (𝟙 (Spec (CommRingCat.of ℂ))) E.f) (v : Fin 2 → ℂ)
    (hP : transE Λ₀ e₀ Pm P = (v : (Fin 2 → ℂ) ⧸ (lattMap Pm Λ₀).toAddSubgroup)) :
    transE Λ₀ e₀ Pm (pushPt (E.act x) (E.act_over x) P) =
      ((((ι (x : ℍ[ℚ, a, b])).map (algebraMap ℝ ℂ)).mulVec v : Fin 2 → ℂ) :
        (Fin 2 → ℂ) ⧸ (lattMap Pm Λ₀).toAddSubgroup) := by
  rw [transE_eq_iff] at hP ⊢
  rw [rho_conj ι ρ Pm hPm x v]
  exact (hρ x).2 P _ hP

variable {q q' : ℕ} [Fact q.Prime] [Fact q'.Prime]

theorem clauseH1 (hB : IsIndefiniteRamifiedExactlyAt a b q q') (hΛ : IsOrder Λ)
    (ι : ℍ[ℚ, a, b] →ₐ[ℚ] Matrix (Fin 2) (Fin 2) ℝ) (hι : Function.Injective ι)
    (E E' : FakeEllipticCurve Λ N ℂ)
    (Λ₀ Λ₀' : Submodule ℤ (Fin 2 → ℂ))
    (e₀ : SchemeHomOver (𝟙 (Spec (CommRingCat.of ℂ))) E.f ≃ ((Fin 2 → ℂ) ⧸ Λ₀.toAddSubgroup))
    (e₀' : SchemeHomOver (𝟙 (Spec (CommRingCat.of ℂ))) E'.f ≃ ((Fin 2 → ℂ) ⧸ Λ₀'.toAddSubgroup))
    (ρ ρ' : ↥Λ → ((Fin 2 → ℂ) →ₗ[ℂ] (Fin 2 → ℂ)))
    (hρ : ∀ x : ↥Λ, LinPred Λ₀ Λ₀ e₀ e₀ (E.act x) (E.act_over x) (ρ x))
    (hρ' : ∀ x : ↥Λ, LinPred Λ₀' Λ₀' e₀' e₀' (E'.act x) (E'.act_over x) (ρ' x))
    (Pm Pm' : (Fin 2 → ℂ) ≃ₗ[ℂ] (Fin 2 → ℂ))
    (hPm : ∀ (x : ↥Λ) (v : Fin 2 → ℂ),
      Pm (ρ x v) = ((ι (x : ℍ[ℚ, a, b])).map (algebraMap ℝ ℂ)).mulVec (Pm v))
    (hPm' : ∀ (x : ↥Λ) (v : Fin 2 → ℂ),
      Pm' (ρ' x v) = ((ι (x : ℍ[ℚ, a, b])).map (algebraMap ℝ ℂ)).mulVec (Pm' v))
    (hactE : ∀ (x : ↥Λ) (P Q : SchemeHomOver (𝟙 (Spec (CommRingCat.of ℂ))) E.f),
      mapPt (E.act x) (E.act_over x) (E.L.mul (𝟙 (Spec (CommRingCat.of ℂ))) P Q) =
        E.L.mul (𝟙 (Spec (CommRingCat.of ℂ))) (mapPt (E.act x) (E.act_over x) P) (mapPt (E.act x) (E.act_over x) Q))
    (K4bEE' : ∀ (u : E.A ⟶ E'.A) (hu : u ≫ E'.f = E.f),
      (∀ P Q : SchemeHomOver (𝟙 (Spec (CommRingCat.of ℂ))) E.f,
        mapPt u hu (E.L.mul (𝟙 (Spec (CommRingCat.of ℂ))) P Q) =
          E'.L.mul (𝟙 (Spec (CommRingCat.of ℂ))) (mapPt u hu P) (mapPt u hu Q)) →
      ∃! T : (Fin 2 → ℂ) →ₗ[ℂ] (Fin 2 → ℂ), LinPred Λ₀ Λ₀' e₀ e₀' u hu T)
    (φ : E.A ⟶ E'.A) (hφ : φ ≫ E'.f = E.f)
    (hhom : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of ℂ)) (P Q : SchemeHomOver t E.f),
      mapPt φ hφ (E.L.mul t P Q) = E'.L.mul t (mapPt φ hφ P) (mapPt φ hφ Q))
    (hlin : ∀ x : ↥Λ, E.act x ≫ φ = φ ≫ E'.act x) :
    ∃ c : ℂ, (∀ v ∈ lattMap Pm Λ₀, c • v ∈ lattMap Pm' Λ₀') ∧
      ∀ (P : SchemeHomOver (𝟙 (Spec (CommRingCat.of ℂ))) E.f) (v : Fin 2 → ℂ),
        transE Λ₀ e₀ Pm P = (v : (Fin 2 → ℂ) ⧸ (lattMap Pm Λ₀).toAddSubgroup) →
        transE Λ₀' e₀' Pm' (mapPt φ hφ P) = ((c • v : Fin 2 → ℂ) : (Fin 2 → ℂ) ⧸ (lattMap Pm' Λ₀').toAddSubgroup) := by
  obtain ⟨Tφ, ⟨hTl, hTp⟩, -⟩ := K4bEE' φ hφ (fun P Q => hhom _ P Q)

  have hcomm : ∀ x : ↥Λ, Tφ.comp (ρ x) = (ρ' x).comp Tφ := by
    intro x
    have hu : (E.act x ≫ φ) ≫ E'.f = E.f := by rw [Category.assoc, hφ, E.act_over]
    have hu' : (φ ≫ E'.act x) ≫ E'.f = E.f := by rw [Category.assoc, E'.act_over, hφ]
    have hhom' : ∀ P Q : SchemeHomOver (𝟙 (Spec (CommRingCat.of ℂ))) E.f,
        mapPt (E.act x ≫ φ) hu (E.L.mul (𝟙 (Spec (CommRingCat.of ℂ))) P Q) =
          E'.L.mul (𝟙 (Spec (CommRingCat.of ℂ))) (mapPt (E.act x ≫ φ) hu P) (mapPt (E.act x ≫ φ) hu Q) := by
      intro P Q
      rw [mapPt_of_eq_comp hu rfl (E.act_over x) hφ, mapPt_of_eq_comp hu rfl (E.act_over x) hφ,
        mapPt_of_eq_comp hu rfl (E.act_over x) hφ, hactE, hhom]
    obtain ⟨T, -, hTu⟩ := K4bEE' (E.act x ≫ φ) hu hhom'
    have h1 : Tφ.comp (ρ x) = T := hTu _ ⟨fun v hv => hTl _ ((hρ x).1 v hv), fun P v hP => by
      rw [mapPt_of_eq_comp hu rfl (E.act_over x) hφ]
      exact hTp _ _ ((hρ x).2 P v hP)⟩
    have h2 : (ρ' x).comp Tφ = T := hTu _ ⟨fun v hv => (hρ' x).1 _ (hTl v hv), fun P v hP => by
      rw [mapPt_congr' (hlin x) hu hu', mapPt_of_eq_comp hu' rfl hφ (E'.act_over x)]
      exact (hρ' x).2 _ _ (hTp P v hP)⟩
    rw [h1, h2]

  set S : (Fin 2 → ℂ) →ₗ[ℂ] (Fin 2 → ℂ) :=
    (Pm' : (Fin 2 → ℂ) →ₗ[ℂ] (Fin 2 → ℂ)).comp (Tφ.comp (Pm.symm : (Fin 2 → ℂ) →ₗ[ℂ] (Fin 2 → ℂ))) with hSdef
  have hSapp : ∀ v, S v = Pm' (Tφ (Pm.symm v)) := fun v => by simp [hSdef]
  have hS : ∀ x ∈ Λ, ∀ v : Fin 2 → ℂ,
      S (((ι x).map (algebraMap ℝ ℂ)).mulVec v) = ((ι x).map (algebraMap ℝ ℂ)).mulVec (S v) := by
    intro x hx v
    have hc := LinearMap.congr_fun (hcomm ⟨x, hx⟩) (Pm.symm v)
    simp only [LinearMap.comp_apply] at hc
    have chain : Pm' (Tφ (Pm.symm (((ι ((⟨x, hx⟩ : ↥Λ) : ℍ[ℚ, a, b])).map (algebraMap ℝ ℂ)).mulVec v))) =
        ((ι ((⟨x, hx⟩ : ↥Λ) : ℍ[ℚ, a, b])).map (algebraMap ℝ ℂ)).mulVec (Pm' (Tφ (Pm.symm v))) := by
      rw [rho_conj ι ρ Pm hPm ⟨x, hx⟩ v, hc, hPm']
    rw [hSapp, hSapp]
    exact chain
  obtain ⟨c, hc⟩ := QuaternionAlgebra.IsOrder.exists_eq_smul_of_forall_mulVec_comm hB Λ hΛ ι hι S hS
  refine ⟨c, ?_, ?_⟩
  · intro v hv
    rw [mem_lattMap] at hv
    rw [← hc v, mem_lattMap, hSapp, LinearEquiv.symm_apply_apply]
    exact hTl _ hv
  · intro P v hP
    rw [transE_eq_iff] at hP ⊢
    rw [← hc v, hSapp, LinearEquiv.symm_apply_apply]
    exact hTp P _ hP

theorem clauseH2 (ι : ℍ[ℚ, a, b] →ₐ[ℚ] Matrix (Fin 2) (Fin 2) ℝ)
    (E E' : FakeEllipticCurve Λ N ℂ)
    (Λ₀ Λ₀' : Submodule ℤ (Fin 2 → ℂ))
    (e₀ : SchemeHomOver (𝟙 (Spec (CommRingCat.of ℂ))) E.f ≃ ((Fin 2 → ℂ) ⧸ Λ₀.toAddSubgroup))
    (e₀' : SchemeHomOver (𝟙 (Spec (CommRingCat.of ℂ))) E'.f ≃ ((Fin 2 → ℂ) ⧸ Λ₀'.toAddSubgroup))
    (ρ ρ' : ↥Λ → ((Fin 2 → ℂ) →ₗ[ℂ] (Fin 2 → ℂ)))
    (hρ : ∀ x : ↥Λ, LinPred Λ₀ Λ₀ e₀ e₀ (E.act x) (E.act_over x) (ρ x))
    (hρ' : ∀ x : ↥Λ, LinPred Λ₀' Λ₀' e₀' e₀' (E'.act x) (E'.act_over x) (ρ' x))
    (Pm Pm' : (Fin 2 → ℂ) ≃ₗ[ℂ] (Fin 2 → ℂ))
    (hPm : ∀ (x : ↥Λ) (v : Fin 2 → ℂ),
      Pm (ρ x v) = ((ι (x : ℍ[ℚ, a, b])).map (algebraMap ℝ ℂ)).mulVec (Pm v))
    (hPm' : ∀ (x : ↥Λ) (v : Fin 2 → ℂ),
      Pm' (ρ' x v) = ((ι (x : ℍ[ℚ, a, b])).map (algebraMap ℝ ℂ)).mulVec (Pm' v))
    (K6EE' : ∀ (T : (Fin 2 → ℂ) →ₗ[ℂ] (Fin 2 → ℂ)) (hT : Λ₀.toAddSubgroup ≤ Λ₀'.toAddSubgroup.comap T.toAddMonoidHom),
      ∃ (u : E.A ⟶ E'.A) (hu : u ≫ E'.f = E.f),
        (∀ {S : Scheme.{0}} (s : S ⟶ Spec (CommRingCat.of ℂ)) (P Q : SchemeHomOver s E.f),
          mapPt u hu (E.L.mul s P Q) = E'.L.mul s (mapPt u hu P) (mapPt u hu Q)) ∧
        (∀ P : SchemeHomOver (𝟙 (Spec (CommRingCat.of ℂ))) E.f,
          mapPt u hu P = (fun P => e₀'.symm ((QuotientAddGroup.map Λ₀.toAddSubgroup Λ₀'.toAddSubgroup T.toAddMonoidHom hT) (e₀ P))) P))
    (c : ℂ) (hc : ∀ v ∈ lattMap Pm Λ₀, c • v ∈ lattMap Pm' Λ₀') :
    ∃ (φ : E.A ⟶ E'.A) (hφ : φ ≫ E'.f = E.f),
      (∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of ℂ)) (P Q : SchemeHomOver t E.f),
        mapPt φ hφ (E.L.mul t P Q) = E'.L.mul t (mapPt φ hφ P) (mapPt φ hφ Q)) ∧
      (∀ x : ↥Λ, E.act x ≫ φ = φ ≫ E'.act x) ∧
      ∀ (P : SchemeHomOver (𝟙 (Spec (CommRingCat.of ℂ))) E.f) (v : Fin 2 → ℂ),
        transE Λ₀ e₀ Pm P = (v : (Fin 2 → ℂ) ⧸ (lattMap Pm Λ₀).toAddSubgroup) →
        transE Λ₀' e₀' Pm' (mapPt φ hφ P) = ((c • v : Fin 2 → ℂ) : (Fin 2 → ℂ) ⧸ (lattMap Pm' Λ₀').toAddSubgroup) := by

  set T : (Fin 2 → ℂ) →ₗ[ℂ] (Fin 2 → ℂ) :=
    (Pm'.symm : (Fin 2 → ℂ) →ₗ[ℂ] (Fin 2 → ℂ)).comp
      ((c • (LinearMap.id : (Fin 2 → ℂ) →ₗ[ℂ] (Fin 2 → ℂ))).comp (Pm : (Fin 2 → ℂ) →ₗ[ℂ] (Fin 2 → ℂ))) with hTdef
  have hTapp : ∀ w, T w = Pm'.symm (c • Pm w) := fun w => by simp [hTdef]
  have hT : Λ₀.toAddSubgroup ≤ Λ₀'.toAddSubgroup.comap T.toAddMonoidHom := by
    intro w hw
    have h1 : Pm w ∈ lattMap Pm Λ₀ := by
      rw [mem_lattMap, LinearEquiv.symm_apply_apply]; exact hw
    have h2 := hc _ h1
    rw [mem_lattMap] at h2
    simp only [AddSubgroup.mem_comap, Submodule.mem_toAddSubgroup, LinearMap.toAddMonoidHom_coe, hTapp]
    exact h2
  obtain ⟨φ, hφ, hhomS, hpt⟩ := K6EE' T hT

  have hptT : ∀ (P : SchemeHomOver (𝟙 (Spec (CommRingCat.of ℂ))) E.f) (w : Fin 2 → ℂ),
      e₀ P = (w : (Fin 2 → ℂ) ⧸ Λ₀.toAddSubgroup) →
      e₀' (mapPt φ hφ P) = ((T w : Fin 2 → ℂ) : (Fin 2 → ℂ) ⧸ Λ₀'.toAddSubgroup) := by
    intro P w hP
    rw [hpt P]
    simp only [hP, QuotientAddGroup.map_mk, Equiv.apply_symm_apply, LinearMap.toAddMonoidHom_coe]
  refine ⟨φ, hφ, hhomS, ?_, ?_⟩
  ·
    intro x
    haveI : IsProper E'.f := E'.bundle.proper
    haveI : IsProper E.f := E.bundle.proper
    haveI : IsReduced E.A := isReduced_FEC E
    have hu : (E.act x ≫ φ) ≫ E'.f = E.f := by rw [Category.assoc, hφ, E.act_over]
    have hu' : (φ ≫ E'.act x) ≫ E'.f = E.f := by rw [Category.assoc, E'.act_over, hφ]
    refine AlgebraicGeometry.ext_of_forall_comp_eq_of_isAlgClosed E.f E'.f hu hu' fun pt hpt0 => ?_
    let P : SchemeHomOver (𝟙 (Spec (CommRingCat.of ℂ))) E.f := ⟨pt, hpt0⟩
    obtain ⟨w, hw⟩ := QuotientAddGroup.mk_surjective (e₀ P)
    have lhs : e₀' (mapPt (E.act x ≫ φ) hu P) =
        ((T (ρ x w) : Fin 2 → ℂ) : (Fin 2 → ℂ) ⧸ Λ₀'.toAddSubgroup) := by
      rw [mapPt_of_eq_comp hu rfl (E.act_over x) hφ]
      exact hptT _ _ ((hρ x).2 P w hw.symm)
    have rhs : e₀' (mapPt (φ ≫ E'.act x) hu' P) =
        ((ρ' x (T w) : Fin 2 → ℂ) : (Fin 2 → ℂ) ⧸ Λ₀'.toAddSubgroup) := by
      rw [mapPt_of_eq_comp hu' rfl hφ (E'.act_over x)]
      exact (hρ' x).2 _ _ (hptT P w hw.symm)
    have hTρ : T (ρ x w) = ρ' x (T w) := by
      apply Pm'.injective
      rw [hTapp, hTapp, LinearEquiv.apply_symm_apply, hPm', LinearEquiv.apply_symm_apply, hPm,
        Matrix.mulVec_smul]
    have key : mapPt (E.act x ≫ φ) hu P = mapPt (φ ≫ E'.act x) hu' P :=
      e₀'.injective (by rw [lhs, rhs, hTρ])
    exact congrArg Subtype.val key
  · intro P v hP
    rw [transE_eq_iff] at hP ⊢
    rw [hptT P _ hP, hTapp, LinearEquiv.apply_symm_apply]

theorem clauseH3 (E E' : FakeEllipticCurve Λ N ℂ) (φ ψ : E.A ⟶ E'.A) (hφ : φ ≫ E'.f = E.f) (hψ : ψ ≫ E'.f = E.f)
    (h : ∀ P : SchemeHomOver (𝟙 (Spec (CommRingCat.of ℂ))) E.f, mapPt φ hφ P = mapPt ψ hψ P) : φ = ψ := by
  haveI : IsProper E'.f := E'.bundle.proper
  haveI : IsProper E.f := E.bundle.proper
  haveI : IsReduced E.A := isReduced_FEC E
  exact AlgebraicGeometry.ext_of_forall_comp_eq_of_isAlgClosed E.f E'.f hφ hψ
    fun x hx => congrArg Subtype.val (h ⟨x, hx⟩)

end FEC

end K8Assembly
p2m_reactivate "P2MW.S_CerednikDrinfeld_QM_exists_latticeMap_pointEquiv_hom_iff_smul_le_analytic.K8Assembly"

open K8Assembly

theorem solution
    {q q' : ℕ} [Fact q.Prime] [Fact q'.Prime] {a b : ℚ} (hB : IsIndefiniteRamifiedExactlyAt a b q q')
    (Λ : Submodule ℤ ℍ[ℚ, a, b]) (hΛ : IsMaximalOrder Λ)
    (ι : ℍ[ℚ, a, b] →ₐ[ℚ] Matrix (Fin 2) (Fin 2) ℝ) (hι : Function.Injective ι) (hqq' : q' ≠ q)
    {N : ℕ} [NeZero N] (hqN : ¬ q ∣ N) (hq'N : ¬ q' ∣ N) :
    ∃ (latt : FakeEllipticCurve Λ N ℂ → Submodule ℤ (Fin 2 → ℂ))
      (e : ∀ E : FakeEllipticCurve Λ N ℂ,
        SchemeHomOver (𝟙 (Spec (CommRingCat.of ℂ))) E.f ≃ ((Fin 2 → ℂ) ⧸ (latt E).toAddSubgroup)),

      (∀ E : FakeEllipticCurve Λ N ℂ,
        (∃ b₀ : Module.Basis (Fin 4) ℝ (Fin 2 → ℂ), latt E = Submodule.span ℤ (Set.range b₀)) ∧
        (∀ x ∈ Λ, ∀ v ∈ latt E, ((ι x).map (algebraMap ℝ ℂ)).mulVec v ∈ latt E)) ∧

      (∀ (E : FakeEllipticCurve Λ N ℂ) (P Q : SchemeHomOver (𝟙 (Spec (CommRingCat.of ℂ))) E.f),
        e E (E.L.mul (𝟙 (Spec (CommRingCat.of ℂ))) P Q) = e E P + e E Q) ∧

      (∀ (E : FakeEllipticCurve Λ N ℂ) (x : ↥Λ) (P : SchemeHomOver (𝟙 (Spec (CommRingCat.of ℂ))) E.f) (v : Fin 2 → ℂ),
        e E P = (v : (Fin 2 → ℂ) ⧸ (latt E).toAddSubgroup) →
        e E (pushPt (E.act x) (E.act_over x) P) =
          ((((ι (x : ℍ[ℚ, a, b])).map (algebraMap ℝ ℂ)).mulVec v : Fin 2 → ℂ) : (Fin 2 → ℂ) ⧸ (latt E).toAddSubgroup)) ∧

      (∀ (E E' : FakeEllipticCurve Λ N ℂ) (φ : E.A ⟶ E'.A) (hφ : φ ≫ E'.f = E.f),
        (∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of ℂ)) (P Q : SchemeHomOver t E.f),
          mapPt φ hφ (E.L.mul t P Q) = E'.L.mul t (mapPt φ hφ P) (mapPt φ hφ Q)) →
        (∀ x : ↥Λ, E.act x ≫ φ = φ ≫ E'.act x) →
        ∃ c : ℂ, (∀ v ∈ latt E, c • v ∈ latt E') ∧
          ∀ (P : SchemeHomOver (𝟙 (Spec (CommRingCat.of ℂ))) E.f) (v : Fin 2 → ℂ),
            e E P = (v : (Fin 2 → ℂ) ⧸ (latt E).toAddSubgroup) →
            e E' (mapPt φ hφ P) = ((c • v : Fin 2 → ℂ) : (Fin 2 → ℂ) ⧸ (latt E').toAddSubgroup)) ∧

      (∀ (E E' : FakeEllipticCurve Λ N ℂ) (c : ℂ), (∀ v ∈ latt E, c • v ∈ latt E') →
        ∃ (φ : E.A ⟶ E'.A) (hφ : φ ≫ E'.f = E.f),
          (∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of ℂ)) (P Q : SchemeHomOver t E.f),
            mapPt φ hφ (E.L.mul t P Q) = E'.L.mul t (mapPt φ hφ P) (mapPt φ hφ Q)) ∧
          (∀ x : ↥Λ, E.act x ≫ φ = φ ≫ E'.act x) ∧
          ∀ (P : SchemeHomOver (𝟙 (Spec (CommRingCat.of ℂ))) E.f) (v : Fin 2 → ℂ),
            e E P = (v : (Fin 2 → ℂ) ⧸ (latt E).toAddSubgroup) →
            e E' (mapPt φ hφ P) = ((c • v : Fin 2 → ℂ) : (Fin 2 → ℂ) ⧸ (latt E').toAddSubgroup)) ∧

      (∀ (E E' : FakeEllipticCurve Λ N ℂ) (φ ψ : E.A ⟶ E'.A) (hφ : φ ≫ E'.f = E.f) (hψ : ψ ≫ E'.f = E.f),
        (∀ P : SchemeHomOver (𝟙 (Spec (CommRingCat.of ℂ))) E.f, mapPt φ hφ P = mapPt ψ hψ P) → φ = ψ) ∧

      (∀ (E : FakeEllipticCurve Λ N ℂ) (U : E.A.Opens) (f : Γ(E.A, U)),
        IsOpen {v : Fin 2 → ℂ | ⊤ ≤ ((e E).symm (v : (Fin 2 → ℂ) ⧸ (latt E).toAddSubgroup)).1 ⁻¹ᵁ U} ∧
        ∃ F : (Fin 2 → ℂ) → ℂ,
          DifferentiableOn ℂ F {v : Fin 2 → ℂ | ⊤ ≤ ((e E).symm (v : (Fin 2 → ℂ) ⧸ (latt E).toAddSubgroup)).1 ⁻¹ᵁ U} ∧
          ∀ (v : Fin 2 → ℂ) (h : ⊤ ≤ ((e E).symm (v : (Fin 2 → ℂ) ⧸ (latt E).toAddSubgroup)).1 ⁻¹ᵁ U),
            F v = (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom
              ((((e E).symm (v : (Fin 2 → ℂ) ⧸ (latt E).toAddSubgroup)).1.appLE U ⊤ h) f)) ∧

      (∀ (E : FakeEllipticCurve Λ N ℂ) (v₀ : Fin 2 → ℂ),
        ∃ (U : E.A.Opens) (f₁ f₂ : Γ(E.A, U)) (ε : ℝ) (D : (Fin 2 → ℂ) ≃L[ℂ] (Fin 2 → ℂ))
          (F : (Fin 2 → ℂ) → (Fin 2 → ℂ)),
          0 < ε ∧
          (∀ v ∈ Metric.ball v₀ ε, ⊤ ≤ ((e E).symm (v : (Fin 2 → ℂ) ⧸ (latt E).toAddSubgroup)).1 ⁻¹ᵁ U) ∧
          (∀ (v : Fin 2 → ℂ) (h : ⊤ ≤ ((e E).symm (v : (Fin 2 → ℂ) ⧸ (latt E).toAddSubgroup)).1 ⁻¹ᵁ U),
            v ∈ Metric.ball v₀ ε →
            F v = ![(Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom
                      ((((e E).symm (v : (Fin 2 → ℂ) ⧸ (latt E).toAddSubgroup)).1.appLE U ⊤ h) f₁),
                    (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom
                      ((((e E).symm (v : (Fin 2 → ℂ) ⧸ (latt E).toAddSubgroup)).1.appLE U ⊤ h) f₂)]) ∧
          HasFDerivAt F (D : (Fin 2 → ℂ) →L[ℂ] (Fin 2 → ℂ)) v₀) := by
  classical

  choose latt₀ e₀ hL1₀ hE1₀ hAN₀ hCOV₀ using
    fun E : FakeEllipticCurve Λ N ℂ =>
      GoodReductionJacobian.AbelianSchemePropertyBundle.exists_submodule_pointEquiv_quotient_differentiableOn_appLE
        E.L E.comm E.bundle E.dim_fibre

  have hSURJ₀ := fun E : FakeEllipticCurve Λ N ℂ =>
    haveI : IsProper E.f := E.bundle.proper
    AlgebraicGeometry.exists_finset_forall_pointEquiv_eq_coe_mem_ball_of_differentiableOn_appLE_of_isSeparated
      (latt₀ E) (e₀ E) (hL1₀ E) (hAN₀ E)

  have hact : ∀ (E : FakeEllipticCurve Λ N ℂ) (x : ↥Λ) (P Q : SchemeHomOver (𝟙 (Spec (CommRingCat.of ℂ))) E.f),
      mapPt (E.act x) (E.act_over x) (E.L.mul (𝟙 (Spec (CommRingCat.of ℂ))) P Q) =
        E.L.mul (𝟙 (Spec (CommRingCat.of ℂ))) (mapPt (E.act x) (E.act_over x) P)
          (mapPt (E.act x) (E.act_over x) Q) :=
    fun E x P Q => E.act_hom x _ P Q

  have K4b : ∀ (E E' : FakeEllipticCurve Λ N ℂ) (u : E.A ⟶ E'.A) (hu : u ≫ E'.f = E.f),
      (∀ P Q : SchemeHomOver (𝟙 (Spec (CommRingCat.of ℂ))) E.f,
        mapPt u hu (E.L.mul (𝟙 (Spec (CommRingCat.of ℂ))) P Q) =
          E'.L.mul (𝟙 (Spec (CommRingCat.of ℂ))) (mapPt u hu P) (mapPt u hu Q)) →
      ∃! T : (Fin 2 → ℂ) →ₗ[ℂ] (Fin 2 → ℂ), LinPred (latt₀ E) (latt₀ E') (e₀ E) (e₀ E') u hu T :=
    fun E E' u hu hhom =>
      GoodReductionJacobian.RelativeGroupLaw.existsUnique_linearMap_forall_pointEquiv_mapPt_eq_of_differentiableOn_appLE
        E.L E'.L (latt₀ E) (latt₀ E') (e₀ E) (e₀ E') (hL1₀ E') (hE1₀ E) (hE1₀ E') (hAN₀ E) (hAN₀ E')
        (hCOV₀ E') (hSURJ₀ E') u hu hhom
  choose ρ hρ hρu using
    fun (E : FakeEllipticCurve Λ N ℂ) (x : ↥Λ) => K4b E E (E.act x) (E.act_over x) (hact E x)
  have hρlaws := fun E : FakeEllipticCurve Λ N ℂ =>
    rho_laws E (latt₀ E) (e₀ E) (hE1₀ E) (ρ E) (hρ E) (hρu E)

  choose Pm hPm using fun E : FakeEllipticCurve Λ N ℂ =>
    QuaternionAlgebra.IsOrder.exists_linearEquiv_apply_eq_mulVec_map_of_finrank_eq_two hB Λ hΛ.isOrder ι hι
      (Fin 2 → ℂ) (Module.finrank_fin_fun ℂ) (ρ E) (hρlaws E).1 (hρlaws E).2.1 (hρlaws E).2.2
  refine ⟨fun E => lattMap (Pm E) (latt₀ E), fun E => transE (latt₀ E) (e₀ E) (Pm E),
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  ·
    exact fun E => ⟨clauseL1full (latt₀ E) (Pm E) (hL1₀ E),
      clauseL1stab E ι (latt₀ E) (e₀ E) (ρ E) (hρ E) (Pm E) (hPm E)⟩
  ·
    exact fun E P Q => clauseE1 E.L (latt₀ E) (e₀ E) (Pm E) (hE1₀ E) P Q
  ·
    exact fun E x P v hP => clauseE2 E ι (latt₀ E) (e₀ E) (ρ E) (hρ E) (Pm E) (hPm E) x P v hP
  ·
    exact fun E E' φ hφ hhom hlin =>
      clauseH1 hB hΛ.isOrder ι hι E E' (latt₀ E) (latt₀ E') (e₀ E) (e₀ E') (ρ E) (ρ E')
        (hρ E) (hρ E') (Pm E) (Pm E') (hPm E) (hPm E') (hact E) (K4b E E') φ hφ
        (fun t P Q => hhom t P Q) hlin
  ·
    exact fun E E' c hc =>
      clauseH2 ι E E' (latt₀ E) (latt₀ E') (e₀ E) (e₀ E') (ρ E) (ρ E') (hρ E) (hρ E')
        (Pm E) (Pm E') (hPm E) (hPm E')
        (fun T hT =>
          GoodReductionJacobian.AbelianSchemePropertyBundle.exists_hom_mapPt_eq_pointEquiv_symm_quotientMap_of_le_comap
            E.L E'.L E.bundle E'.bundle E.dim_fibre E'.dim_fibre (latt₀ E) (latt₀ E') (e₀ E) (e₀ E')
            (hL1₀ E) (hL1₀ E') (hE1₀ E) (hE1₀ E') (hAN₀ E) (hAN₀ E') (hCOV₀ E) (hCOV₀ E') T hT)
        c hc
  ·
    exact fun E E' φ ψ hφ hψ h => clauseH3 E E' φ ψ hφ hψ h
  ·
    exact fun E U f => clauseAN (latt₀ E) (e₀ E) (Pm E) (hAN₀ E) U f
  ·
    exact fun E v₀ => clauseCOV (latt₀ E) (e₀ E) (Pm E) (hCOV₀ E) v₀

end
end S_CerednikDrinfeld_QM_exists_latticeMap_pointEquiv_hom_iff_smul_le_analytic
end P2MW
export P2MW.S_CerednikDrinfeld_QM_exists_latticeMap_pointEquiv_hom_iff_smul_le_analytic (solution)
