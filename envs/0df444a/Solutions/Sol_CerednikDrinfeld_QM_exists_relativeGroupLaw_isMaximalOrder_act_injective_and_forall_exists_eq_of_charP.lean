-- Prove2me | solution 1 for CerednikDrinfeld.QM.exists_relativeGroupLaw_isMaximalOrder_act_injective_and_forall_exists_eq_of_charP
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.141142+00:00
-- url     : https://prove2.me/submissions/452e845c-3ba3-50b0-aaaa-fb82a468bf08

import Mathlib
import Definitions.Def_CerednikDrinfeld_QMModuli
import Definitions.Def_QuaternionAlgebra_EichlerOrder
import Definitions.Def_WeierstrassCurve_ProjModel
import Definitions.Def_WeierstrassCurve_ProjModel_GroupLawVocabulary
import Definitions.Def_WeierstrassCurve_PointChart
import Definitions.Def_WeierstrassCurve_RationalEnd
import Definitions.Def_AlgebraicGeometry_NeronModelEndomorphismExtension
import Theorems.Thm_QuaternionAlgebra_exists_isDefiniteRamifiedExactlyAt_isEichlerOrder
import Theorems.Thm_WeierstrassCurve_exists_supersingular_rationalEndSubring_range_eq_of_isMaximalOrder
import Theorems.Thm_WeierstrassProjModel_exists_relativeGroupLaw_isPointsEval_of_isElliptic_of_isDomain
import Theorems.Thm_WeierstrassProjModel_mul_comm_of_isPointsEval
import Theorems.Thm_WeierstrassProjModel_RelativeGroupLaw_exists_isCommutative_one_eq_zeroSect_of_isCommutative
import Theorems.Thm_WeierstrassProjModel_exists_isPointsEval_apply_eq_some_of_eq_comp_zChartInclusion
import Theorems.Thm_WeierstrassProjModel_exists_action_rationalEndSubring_of_isAlgClosed
import Theorems.Thm_WeierstrassProjModel_projModelStrCR_smooth
import Theorems.Thm_WeierstrassProjModel_projModelStrCR_isProper
import Theorems.Thm_WeierstrassProjModel_projModelStrCR_smoothOfRelativeDimension_one
import Theorems.Thm_WeierstrassProjModel_kw_hgi_geometricallyIntegral_of_baseChangeIso
import Theorems.Thm_WeierstrassProjModel_projModel_pullback_iso_baseChange
import Theorems.Thm_WeierstrassProjModel_exists_zChartAway_equiv_coordinateRing
import Theorems.Thm_AlgebraicGeometry_SchemeHomOver_ext_of_forall_point_of_isReduced_of_locallyOfFiniteType
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_QM_exists_relativeGroupLaw_isMaximalOrder_act_injective_and_forall_exists_eq_of_charP
p2m_attr_erase "instance" "IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions AlgebraicCurve.instFundamentalIdentityOfSumRamificationInertia AlgebraicCurve.Place.instIsScalarTowerResidueFieldRestrictPushforward AlgebraicCurve.Place.instAlgebraResidueFieldRestrictPushforward AlgebraicCurve.Place.instIsLocalHomRestrictInclusion AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation ModularCurve.SpecializationWitnessData.addCommGroup ModularCurve.CommutingHeckeFamily.commRing_adjoin ModularCurve.Gamma0Pair.isElliptic WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly TateModule.instModule TateModule.instSMul GaloisRepAdic.instAddCommGroup GaloisRepAdic.instFree GaloisRepAdic.instFinite GaloisRepAdic.instModule ResidualGaloisRep.instModule ResidualGaloisRep.instModuleFinite ResidualGaloisRep.instAddCommGroup WeierstrassCurve.Affine.Point.instFinite WeierstrassCurve.Affine.CoordinateRing.moduleFinite WeierstrassCurve.Affine.instDecidableEqFunctionField WeierstrassCurve.Affine.CoordinateRing.isIntegral AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt WeierstrassCurve.Affine.instIsScalarTowerPolynomialRatFuncFunctionField_definitions WeierstrassCurve.Affine.instAlgebraRatFuncFunctionField_definitions WeierstrassCurve.Affine.instIsScalarTowerRatFuncFunctionField_definitions"
p2m_attr_erase "instance" "ModularCurve.ModuliTestDatum.isElliptic_reduced ModularCurve.ModuliTestDatum.isElliptic_curve ModularCurve.ModuliTestDatum.isElliptic_generic ModularCurve.PhiGen.instNeZeroPhiGenCosetA ModularCurve.ElevenA1.instDecidableEquation ModularCurve.ElevenA1.instDecidableNonsingular ModularCurve.instIsElliptic_tateBase ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid WeierstrassCurve.VeluQuotientJGates.instIsElliptic27a4 CyclotomicUniv.instCharZeroR₀ CyclotomicUniv.instIsDomain CyclotomicUniv.instIsDomainR₀ CyclotomicUniv.instCharZero AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions ModularCurve.instSMulAlgEquivRatPic0SubtypeLaurentSeriesMemIntermediateFieldLaurentBaseChange ModularCurve.instDistribMulActionAlgEquivRatPic0SubtypeLaurentSeriesMemIntermediateFieldLaurentBaseChange instTopologicallyFGOfFiniteType AlgebraicCurve.CurveModel.isProper AlgebraicCurve.CurveModel.isIntegral AlgebraicCurve.CurveModel.smooth AlgebraicCurve.CurveModel.locallyOfFiniteType_gluedToBase AlgebraicCurve.CurveModel.isFractionRing_overlap AlgebraicCurve.CurveModel.isLocallyNoetherian_glued AlgebraicCurve.CurveModel.jacobsonSpace_glued AlgebraicCurve.CurveModel.isOpenImmersion_ι₀ AlgebraicCurve.CurveModel.isIntegral_glued AlgebraicCurve.CurveModel.quasiSeparated_gluedToBase AlgebraicCurve.CurveModel.compactSpace_glued AlgebraicCurve.CurveModel.isIntegral_adjoin_chartRing AlgebraicCurve.CurveModel.isFractionRing_overlap_functionField AlgebraicCurve.CurveModel.isProper_gluedToBase AlgebraicCurve.CurveModel.isOpenImmersion_ιU AlgebraicCurve.CurveModel.isOpenImmersion_f₀ AlgebraicCurve.CurveModel.isOpenImmersion_fInf AlgebraicCurve.CurveModel.isOpenImmersion_ιInf AlgebraicCurve.CurveModel.algebra_overlap_functionField AlgebraicCurve.CurveModel.quasiCompact_gluedToBase AlgebraicCurve.CurveModel.algebraAdjoin AlgebraicCurve.CurveModel.isDedekindDomain_chartRing"
p2m_attr_erase "instance" "AlgebraicCurve.CurveModel.isIntegralClosure AlgebraicCurve.CurveModel.finite_chartRing AlgebraicCurve.CurveModel.centre_isPrime AlgebraicCurve.CurveModel.isFractionRing_chartRing AlgebraicCurve.CurveModel.finiteType_chartRing AlgebraicCurve.CurveModel.isNoetherianRing_chartRing AlgebraicCurve.CurveModel.isScalarTower_base_adjoin AlgebraicCurve.CurveModel.isScalarTower_adjoin AlgebraicCurve.CurveModel.chartRing_finitePresentation"
p2m_attr_erase "simp" "QuaternionAlgebra.baseChangeRight_tmul QuaternionAlgebra.mapOfAlgebraMapEq_apply QuaternionAlgebra.baseChange_tmul QuaternionAlgebra.ClassSet.map_mk ModularCurve.coe_levelAlphaC ModularCurve.SSLevelDatum.mk.sizeOf_spec ModularCurve.SSLevelDatum.mk.injEq ModularCurve.coe_levelBetaC ModularCurve.coe_heckeBetaC AlgebraicCurve.Divisor.coe_degZeroEnd ModularCurve.coe_heckeAlphaC AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Divisor.mapRestrict_single AlgebraicCurve.Divisor.pushforward_single AlgebraicCurve.Place.coe_restrictInclusion AlgebraicCurve.Place.mem_fiber AlgebraicCurve.Place.restrict_toValuationSubring AlgebraicCurve.Divisor.degree_pushforward AlgebraicCurve.Place.restrictResidueMap_residue AlgebraicCurve.Pic0.coe_pushforwardDegZeroHom AlgebraicCurve.Pic0.coe_pullbackDegZeroHom AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply"
p2m_attr_erase "simp" "AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.Divisor.degree_pushforwardAlong AlgebraicCurve.Pic0.coe_degZeroCorrespondence AlgebraicCurve.Place.mem_fiberAlong AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.CommutingHeckeFamily.mk.injEq ModularCurve.SpecializationWitnessData.mk.sizeOf_spec ModularCurve.SpecializationWitnessData.mk.injEq ModularCurve.CommutingHeckeFamily.mk.sizeOf_spec ModularCurve.coe_nodeEquivOfPlaces_apply ModularCurve.widthOfPlaces_mk ModularCurve.smulNodePairEmb_apply ModularCurve.card_nodePairsOfPlaces ModularCurve.smulNodePair_snd ModularCurve.smulNodePair_fst ModularCurve.coe_nodeEquivOfPlaces_symm_apply ModularCurve.coe_jGeomGen ModularCurve.coe_jNGeomGen ModularCurve.coe_uniformizerMod ModularCurve.qSeriesBar_jModElt ModularCurve.qInftyPlaceMod_toValuationSubring ModularCurve.qInftyPlaceBar_toValuationSubring ModularCurve.qSeriesBar_zero ModularCurve.qSeriesBar_add ModularCurve.cuspInftyFull_toValuationSubring ModularCurve.qInftyPlaceRat_toValuationSubring ModularCurve.qSeriesBar_mul ModularCurve.qSeriesBar_div ModularCurve.qSeriesBar_eq_zero_iff ModularCurve.coe_uniformizerBar ModularCurve.qSeriesBar_pow ModularCurve.cuspInfty_toValuationSubring"
p2m_attr_erase "simp" "ModularCurve.qSeriesBar_one ModularCurve.qSeriesBar_inv ModularCurve.qSeriesBar_sub ModularCurve.qSeriesBar_neg ModularCurve.charLGeomModuliDictionary_single ModularCurve.specializeModuli_single ModularCurve.specializePlace_def AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one ModularCurve.gamma0PairMap_gen ModularCurve.moduliPointMapRingHom_mk ModularCurve.Gamma0Pair.mk.injEq ModularCurve.ModuliPoint.j_mk ModularCurve.Gamma0Pair.mk.sizeOf_spec ModularCurve.gamma0PairMap_toCurve WeierstrassCurve.Affine.vcY_vcYInv WeierstrassCurve.Affine.vcXInv_vcX WeierstrassCurve.Affine.Point.vcFun_zero WeierstrassCurve.Affine.vcX_vcXInv WeierstrassCurve.Affine.vcYInv_vcY WeierstrassCurve.Affine.Point.vcInvFun_zero WeierstrassCurve.ratPointHom_apply WeierstrassCurve.ratPointMap_zero compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one"
p2m_attr_erase "simp" "WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two TateModule.smul_apply TateModule.coe_mulP TateModule.proj_apply TateModule.coe_add TateModule.coe_sub WeierstrassCurve.tateModuleRepOfBasis_V TateModule.coe_zero TateModule.rep_apply WeierstrassCurve.tateModuleRep_V WeierstrassCurve.tateModuleRepOfBasis_ρ_apply GaloisRep.padicIntToRingLevel_apply TateModule.coe_neg WeierstrassCurve.tateModuleRep_ρ_apply GaloisRepAdic.mk.injEq GaloisRepAdic.mk.sizeOf_spec GaloisRepAdic.Equiv.mk.sizeOf_spec GaloisRepAdic.Equiv.mk.injEq ResidualGaloisRep.mk.sizeOf_spec ResidualGaloisRep.mk.injEq ResidualGaloisRep.Equiv.mk.sizeOf_spec ResidualGaloisRep.Equiv.mk.injEq WeierstrassCurve.Universal.halveX_zero WeierstrassCurve.Universal.specialize_X_one WeierstrassCurve.Universal.coeff_halve"
p2m_attr_erase "simp" "WeierstrassCurve.Universal.specialize_X_two WeierstrassCurve.Universal.halveCoeff_zero WeierstrassCurve.Universal.specialize_X_four WeierstrassCurve.Universal.coeff_halveX WeierstrassCurve.Universal.specialize_X_three WeierstrassCurve.Universal.specialize_X_zero FrobeniusEndo.linePencil_apply WeierstrassCurve.Affine.mem_fibSet WeierstrassCurve.Affine.pointHom_mk_C_C WeierstrassCurve.Affine.Point.yc_some WeierstrassCurve.Affine.Point.xc_some WeierstrassCurve.Affine.pointPull_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_X WeierstrassCurve.Affine.pointHom_mk_Y WeierstrassCurve.Affine.placeOf_asIdeal AddMonoid.End.DualEndData.symm_trace AddMonoid.End.dualEndData_intCast_norm AddMonoid.End.DualEndData.ofCharPoly_norm AddMonoid.End.DualEndData.mk.sizeOf_spec AddMonoid.End.DualEndData.mk.injEq AddMonoid.End.DualEndData.ofCharPoly_dual AddMonoid.End.dualEndData_intCast_dual AddMonoid.End.DualEndData.intLinComb_norm AddMonoid.End.DualEndData.ofCharPoly_trace AddMonoid.End.DualEndData.intLinComb_dual AddMonoid.End.DualEndData.symm_dual AddMonoid.End.DualEndData.intLinComb_trace AddMonoid.End.dualEndData_intCast_trace AddMonoid.End.DualEndData.symm_norm WeierstrassCurve.veluWSum_empty WeierstrassCurve.veluQuotient_a₁ WeierstrassCurve.veluQuotient_a₃ WeierstrassCurve.veluQuotient_empty WeierstrassCurve.veluTSum_empty WeierstrassCurve.veluQuotient_a₂ WeierstrassCurve.veluX_empty WeierstrassCurve.veluY_empty WeierstrassCurve.Affine.Point.coordsOrZero_some WeierstrassCurve.Affine.Point.coordsOrZero_zero WeierstrassCurve.Affine.IsogenyEndDatum.mk.injEq"
p2m_attr_erase "simp" "WeierstrassCurve.Affine.IsogenyHomDatum.mk.sizeOf_spec WeierstrassCurve.Affine.IsogenyHomDatum.mk.injEq WeierstrassCurve.Affine.IsogenyEndDatum.mk.sizeOf_spec AlgebraicCurve.Pic0.coe_pushforwardAlongDegZero WeierstrassCurve.Affine.pointMapOfPushforward_apply WeierstrassCurve.Affine.pointClass_zero WeierstrassCurve.Affine.pic0ToPoint_pointClass WeierstrassCurve.Affine.deg_placeOfPoint WeierstrassCurve.Affine.coe_pointDivisor WeierstrassCurve.Affine.pointEquivPlace_symm_placeOfPoint WeierstrassCurve.Affine.pointEquivPlace_apply WeierstrassCurve.Affine.genusOnePic0Equiv_symm_apply WeierstrassCurve.Affine.pointDivisor_zero WeierstrassCurve.Affine.pic0ToPoint_mk WeierstrassCurve.Affine.divisorSum_single WeierstrassCurve.Affine.genusOnePic0Equiv_apply AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal WeierstrassCurve.vcInvEmbedding_apply WeierstrassCurve.map_veluU WeierstrassCurve.map_veluT WeierstrassCurve.map_veluW WeierstrassCurve.map_veluGy WeierstrassCurve.map_veluGx WeierstrassCurve.map_veluWSum_singleton WeierstrassCurve.map_veluTSum_singleton WeierstrassCurve.veluPointMap3_zero WeierstrassCurve.Affine.ratFuncToFunctionField_algebraMap WeierstrassCurve.frobPoint_zero WeierstrassCurve.frobCardHom_apply AddMonoid.End.dualEndDataOfSurjective_trace AddMonoid.End.dualEndDataOfSurjective_norm WeierstrassCurve.pointAddEquivOfEq_refl WeierstrassCurve.veluPointMap2_zero WeierstrassCurve.veluQuotient2_a₂ WeierstrassCurve.veluQuotient2_a₃ WeierstrassCurve.veluQuotient2_a₁"
p2m_attr_erase "simp" "ModularCurve.qExpandAlgHomC_apply WeierstrassCurve.veluQuotientOfSums_a₂ WeierstrassCurve.veluQuotientOfSums_a₁ WeierstrassCurve.veluQuotientOfSums_a₃ ModularCurve.ComapPlace.place_toValuationSubring ModularCurve.ModuliTestDatum.restrictLevel_emb ModularCurve.ModuliTestDatum.restrictLevel_res ModularCurve.ModuliTestDatum.mk.injEq ModularCurve.ModuliTestDatum.restrictLevel_W ModularCurve.ModuliTestDatum.place_toValuationSubring ModularCurve.ModuliTestDatum.restrictLevel_curve ModularCurve.ModuliTestDatum.resEquiv_apply ModularCurve.ModuliTestDatum.restrictLevel_gen ModularCurve.ModuliTestDatum.mk.sizeOf_spec ModularCurve.coe_jqNFull ModularCurve.Gamma0Pair.map_toCurve WeierstrassCurve.mapPoint_eq_ratPointMap ModularCurve.Gamma0Pair.map_gen ModularCurve.Gamma0Pair.map_eq_gamma0PairMap ModularCurve.ModuliPoint.map_eq_moduliPointMapRingHom ModularCurve.ModuliPoint.map_mk WeierstrassCurve.mapPointHom_apply WeierstrassCurve.mapPoint_zero WeierstrassCurve.reducePoint_zero WeierstrassCurve.Affine.Point.galoisRep_apply WeierstrassCurve.twoVeluCurve_a₁ WeierstrassCurve.twoVeluCurve_a₂ WeierstrassCurve.twoVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₂ WeierstrassCurve.xVeluCurve_a₁ ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X"
p2m_attr_erase "simp" "ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ WeierstrassCurve.Affine.Point.netCol_one WeierstrassCurve.Affine.Point.xOrZero_zero WeierstrassCurve.Affine.Point.netPairing_zero_right WeierstrassCurve.Affine.Point.netW20_some WeierstrassCurve.Affine.Point.netCol_zero WeierstrassCurve.Affine.Point.netPairing_zero_left WeierstrassCurve.Affine.Point.xOrZero_some WeierstrassCurve.Affine.Point.netW20_zero TateCurve.cauchyMulInt_zero TateCurve.cauchyMulInt3_zero TateCurve.tent_one TateCurve.Gz_zero TateCurve.cauchyMulInt_one TateCurve.tent_zero TateCurve.Fz_zero TateCurve.xCoeffFull_succ TateCurve.a₆Coeff_zero TateCurve.a₄Coeff_succ TateCurve.a₄Coeff_zero TateCurve.cauchyMul_zero TateCurve.a₆Coeff_succ TateCurve.yCoeffFull_succ TateCurve.xCoeffFull_zero TateCurve.yCoeffFull_zero TateCurve.yfun_zero TateCurve.xfun_zero TateCurve.yTerm_zero TateCurve.xTerm_zero TateCurve.curve_a₂ TateCurve.b_one TateCurve.curve_a₁ TateCurve.term_zero TateCurve.curve_a₆ TateCurve.curve_a₄ TateCurve.curve_a₃ FLT.DivisorConvolution.sigma_zero_right FLT.DivisorConvolution.sigma_one_right FLT.DivisorConvolution.sigmaConv_one"
p2m_attr_erase "simp" "FLT.DivisorConvolution.sigmaConv_zero FormalCoordinates.mk.injEq WeierstrassCurve.formalParam_zero WeierstrassCurve.SmoothLocusReductionData.reduceHom₀_apply WeierstrassCurve.formalParam_some FormalCoordinates.mk.sizeOf_spec WeierstrassCurve.SmoothLocusReductionData.mk.injEq WeierstrassCurve.reducePointSmooth_zero WeierstrassCurve.SmoothLocusReductionData.mk.sizeOf_spec WeierstrassCurve.mem_zeroComponentSubgroup_iff ModularCurve.tateUnivCurve_a₂ ModularCurve.tateUnivCurve_a₃ ModularCurve.tateUnivCurve_a₆ ModularCurve.nonToricPoint_fst ModularCurve.toricPoint_snd ModularCurve.tateUnivCurve_a₁ ModularCurve.nonToricPoint_snd ModularCurve.tateUnivCurve_a₄ ModularCurve.toricPoint_fst ModularCurve.ProjectiveLine.map_mk PeriodPair.weierstrassCurve_a₆ PeriodPair.weierstrassCurve_a₃ PeriodPair.weierstrassCurve_a₁ PeriodPair.ofTau_ω₂ PeriodPair.scale_ω₂ PeriodPair.ofTau_ω₁ PeriodPair.toPoint_zero PeriodPair.toPoint_of_mem PeriodPair.weierstrassCurve_a₂ PeriodPair.ofTau_lattice PeriodPair.scale_ω₁ PeriodPair.weierstrassCurve_a₄ CyclotomicUniv.lift₀_ζ₀ CyclotomicUniv.lift_algebraMap CyclotomicUniv.val_ζUnit CyclotomicUniv.lift_ζ ModularCurve.cuspData_yP ModularCurve.qTwistAlgHom_apply ModularCurve.cuspData_yQ ModularCurve.cuspData_xP"
p2m_attr_erase "simp" "ModularCurve.cuspData_xQ ModularCurve.val_cyclZeta ModularCurve.cuspShift_one ModularCurve.cuspShift_zero TateCurve.tateTorsionPoint_zero_zero AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none WeierstrassCurve.kernelPolynomial_singleton WeierstrassCurve.kernelPolynomial_empty WeierstrassCurve.kohelW_one Polynomial.rootESymm_zero_right WeierstrassCurve.kohelQuotient_a₂ WeierstrassCurve.kohelQuotient_a₃ WeierstrassCurve.kohelT_one WeierstrassCurve.kohelQuotient_one WeierstrassCurve.kohelQuotient_a₁ Polynomial.rootESymm_one WeierstrassCurve.legendreVariableChange_s WeierstrassCurve.legendreVariableChange_t WeierstrassCurve.legendreVariableChange_r WeierstrassCurve.legendreVariableChange_u WeierstrassCurve.deuringVariableChange_s WeierstrassCurve.deuringVariableChange_t WeierstrassCurve.deuringCurve_a₄ WeierstrassCurve.deuringCurve_a₂ WeierstrassCurve.deuringCurve_a₆ WeierstrassCurve.deuringCurve_a₁ WeierstrassCurve.deuringVariableChange_u WeierstrassCurve.deuringCurve_a₃ WeierstrassCurve.deuringVariableChange_r ModularCurve.coe_towerInclBar ModularCurve.coe_towerSubstBar ModularCurve.coe_heckeBetaBarRingHom ModularCurve.coe_heckeBetaBar ModularCurve.coe_heckeAlphaBar ModularCurve.baseAut_arithmeticGalois ModularCurve.JZero.torsionGaloisRep_apply"
p2m_attr_erase "simp" "ModularCurve.coe_arithmeticRingAut_apply ModularCurve.toRingAut_arithmeticGalois WeierstrassProjModel.kw_lrThird_substHom_X WeierstrassCurve.DrinfeldGlobal.LevelTransport.mk.injEq WeierstrassCurve.DrinfeldGlobal.LevelTransport.mk.sizeOf_spec GoodReductionJacobian.RelativeGroupLaw.nsmul_zero GoodReductionJacobian.RelativeGroupLaw.mem_torsionSubset GoodReductionJacobian.RelativeGroupLaw.nsmul_succ GoodReductionJacobian.RelativeGroupLaw.baseChangePointToBase_ofBase GoodReductionJacobian.RelativeGroupLaw.baseChangePointToBase_coe GoodReductionJacobian.RelativeGroupLaw.baseChangePointOfBase_coe GoodReductionJacobian.RelativeGroupLaw.baseChange_inv GoodReductionJacobian.RelativeGroupLaw.baseChangePointOfBase_toBase GoodReductionJacobian.RelativeGroupLaw.baseChange_mul GoodReductionJacobian.RelativeGroupLaw.baseChange_one NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_fst NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_snd NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_fst NeronSpecialFibreInfra.neronEndRestrictEquiv_apply NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_fst_assoc NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_snd NeronSpecialFibreInfra.neronEndExtension_genericFibreRestrict NeronSpecialFibreInfra.specClosedFibreInclusion_eq NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_fst_assoc NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_snd_assoc NeronSpecialFibreInfra.genericFibreRestrict_neronEndExtension NeronSpecialFibreInfra.homOverId_coe NeronSpecialFibreInfra.homOverComp_coe NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_snd_assoc GoodReductionJacobian.RelativeGroupLaw.fibre_inv GoodReductionJacobian.RelativeGroupLaw.fibrePointToBase_coe GoodReductionJacobian.RelativeGroupLaw.fibrePointOfBase_toBase GoodReductionJacobian.RelativeGroupLaw.fibre_mul GoodReductionJacobian.RelativeGroupLaw.fibrePointToBase_ofBase GoodReductionJacobian.RelativeGroupLaw.fibre_one GoodReductionJacobian.RelativeGroupLaw.fibrePointOfBase_coe RegularLocalRingQuotientAscent.dualNumberFst_apply AlgebraicGeometry.schemeFibreEndo_snd AlgebraicGeometry.schemeFibreEndo_fst AlgebraicCurve.CurveModel.mk.injEq"
p2m_attr_erase "simp" "AlgebraicCurve.CurveModel.mk.sizeOf_spec AlgebraicCurve.CurveModel.coe_gInf AlgebraicCurve.CurveModel.coe_tInvChart AlgebraicCurve.CurveModel.ιInf_gluedToBase_assoc AlgebraicCurve.CurveModel.ιInf_gluedToBase AlgebraicCurve.CurveModel.primeOfι₀_asIdeal AlgebraicCurve.CurveModel.coe_tChart AlgebraicCurve.CurveModel.ι₀_gluedToBase_assoc AlgebraicCurve.CurveModel.primeOfιInf_asIdeal AlgebraicCurve.CurveModel.ι₀_gluedToBase AlgebraicCurve.CurveModel.coe_tma AlgebraicCurve.CurveModel.coe_primeEquivChartPlaces"

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.longFile 0
set_option maxHeartbeats 6400000
set_option synthInstance.maxHeartbeats 1600000

p2m_open "CategoryTheory AlgebraicGeometry Polynomial AlgebraicGeometry.Polynomial"
open scoped Polynomial.Bivariate

noncomputable section

namespace DeuringEqSol

open NeronModelInfra (SchemeHomOver)

section Setup

variable {k : Type} [Field k] [IsAlgClosed k] [DecidableEq k]
variable (X : WeierstrassCurve k) [X.IsElliptic]

abbrev E : Scheme.{0} := WeierstrassProjModel.projModelCR X.toProjective

abbrev π : E X ⟶ Spec (CommRingCat.of k) := WeierstrassProjModel.projModelStrCR X.toProjective

abbrev t₀ (k : Type) [Field k] : Spec (CommRingCat.of k) ⟶ Spec (CommRingCat.of k) :=
  Spec.map (CommRingCat.ofHom (algebraMap k k))

theorem t₀_eq (k : Type) [Field k] : t₀ k = 𝟙 _ := by
  simp only [t₀, Algebra.algebraMap_self, CommRingCat.ofHom_id, Spec.map_id]

scoped instance isProper_π : IsProper (π X) := WeierstrassProjModel.projModelStrCR_isProper X.toProjective

scoped instance smooth_π : Smooth (π X) := WeierstrassProjModel.projModelStrCR_smooth X.toProjective

scoped instance geometricallyIntegral_π : GeometricallyIntegral (π X) :=
  WeierstrassProjModel.kw_hgi_geometricallyIntegral_of_baseChangeIso X
    (WeierstrassProjModel.projModel_pullback_iso_baseChange X.toProjective)

scoped instance subsingleton_specField : Subsingleton (Spec (CommRingCat.of k) : Scheme.{0}) :=
  inferInstanceAs (Subsingleton (PrimeSpectrum k))

scoped instance isIntegral_E : IsIntegral (E X) :=
  GeometricallyIntegral.isIntegral_of_subsingleton (π X)

scoped instance connectedSpace_E : ConnectedSpace (E X) := inferInstance

scoped instance isReduced_E : IsReduced (E X) := inferInstance

def toGRJ (G : WeierstrassProjModel.RelativeGroupLaw k (π X)) :
    GoodReductionJacobian.RelativeGroupLaw k (π X) where
  mul := G.mul
  one := G.one
  inv := G.inv
  mul_assoc := G.mul_assoc
  one_mul := G.one_mul
  mul_one := G.mul_one
  inv_mul_cancel := G.inv_mul_cancel
  mul_natural := fun t t' ψ hψ x y => G.mul_natural t t' ψ hψ x y

theorem bundle (G : WeierstrassProjModel.RelativeGroupLaw k (π X)) :
    GoodReductionJacobian.AbelianSchemePropertyBundle k (π X) where
  smooth := inferInstance
  proper := inferInstance
  connectedFibres s := by
    have : (π X).base ⁻¹' {s} = Set.univ := by
      ext x
      simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_univ, iff_true]
      exact Subsingleton.elim _ _
    rw [this]
    exact isConnected_univ
  hasGroupLaw := ⟨toGRJ X G⟩

end Setup

section Algebra

variable {k : Type} [Field k]

theorem mk_eq_zero_of_infinite (W : WeierstrassCurve.Affine k) (g : k[X][Y])
    (h : {x : k | ∃ y : k, W.Equation x y ∧ g.evalEval x y = 0}.Infinite) :
    WeierstrassCurve.Affine.CoordinateRing.mk W g = 0 := by
  classical
  haveI : Module.Free k[X] W.CoordinateRing :=
    Module.Free.of_basis (WeierstrassCurve.Affine.CoordinateRing.basis W)
  haveI : Module.Finite k[X] W.CoordinateRing :=
    Module.Finite.of_basis (WeierstrassCurve.Affine.CoordinateRing.basis W)
  by_contra hne
  obtain ⟨p, q, hpq⟩ := WeierstrassCurve.Affine.CoordinateRing.exists_smul_basis_eq
    (WeierstrassCurve.Affine.CoordinateRing.mk W g)
  set N : k[X] := Algebra.norm k[X] (WeierstrassCurve.Affine.CoordinateRing.mk W g) with hN_def
  have hN : N ≠ 0 := Algebra.norm_ne_zero_iff.2 hne
  have hNa : (algebraMap k[X] W.CoordinateRing N) =
      WeierstrassCurve.Affine.CoordinateRing.mk W g *
        WeierstrassCurve.Affine.CoordinateRing.mk W (C p + C q * (-(Y : k[X][Y]) - C (C W.a₁ * X + C W.a₃))) := by
    have h1 := WeierstrassCurve.Affine.CoordinateRing.coe_norm_smul_basis (W' := W) p q
    rw [hpq] at h1
    rw [hN_def]
    refine h1.trans ?_
    rw [map_mul]
    congr 1
    rw [← hpq, map_add, map_mul, AdjoinRoot.mk_C, AdjoinRoot.mk_C, Algebra.smul_def, Algebra.smul_def, mul_one]
    rfl
  have hroot : {x : k | ∃ y : k, W.Equation x y ∧ g.evalEval x y = 0} ⊆ {x | N.IsRoot x} := by
    rintro x ⟨y, hxy, hg⟩
    have hW : W.polynomial.evalEval x y = 0 := hxy
    let φ : W.CoordinateRing →+* k := AdjoinRoot.evalEval hW
    have hφg : φ (WeierstrassCurve.Affine.CoordinateRing.mk W g) = 0 := by
      show AdjoinRoot.evalEval hW (AdjoinRoot.mk W.polynomial g) = 0
      rw [AdjoinRoot.evalEval_mk]; exact hg
    have hφN : φ (algebraMap k[X] W.CoordinateRing N) = N.eval x := by
      show AdjoinRoot.lift (evalRingHom x) y _ (AdjoinRoot.of W.polynomial N) = _
      rw [AdjoinRoot.lift_of]; rfl
    show N.IsRoot x
    rw [IsRoot.def, ← hφN, hNa, map_mul, hφg, zero_mul]
  exact h (Set.Finite.subset (Polynomial.finite_setOf_isRoot hN) hroot)

theorem point_some_ext {W : WeierstrassCurve.Affine k} {x x' y y' : k} (hx : x = x') (hy : y = y')
    {h : W.Nonsingular x y} {h' : W.Nonsingular x' y'} :
    WeierstrassCurve.Affine.Point.some x y h = WeierstrassCurve.Affine.Point.some x' y' h' := by
  subst hx; subst hy; rfl

end Algebra

section Restrict

attribute [local instance] MvPolynomial.gradedAlgebra

open WeierstrassCurve.DrinfeldGlobal HomogeneousIdealQuotientGrading

variable {k : Type} [Field k] [IsAlgClosed k] [DecidableEq k]

theorem restrict (X : WeierstrassCurve k) [X.IsElliptic]
    (ev : SchemeHomOver (t₀ k) (π X) ≃ (X.toProjective.baseChange k).toAffine.Point)
    (hev_chart : ∀ (P : SchemeHomOver (t₀ k) (π X)) (χ : ZChartRing X.toProjective →+* k),
      P.1 = Spec.map (CommRingCat.ofHom χ) ≫ zChartι X.toProjective →
      ∃ hxy : (X.toProjective.baseChange k).toAffine.Nonsingular (χ (xOverZ X.toProjective)) (χ (yOverZ X.toProjective)),
        ev P = WeierstrassCurve.Affine.Point.some _ _ hxy)
    (φ : SchemeHomOver (π X) (π X)) :
    (∀ (P : SchemeHomOver (t₀ k) (π X)) (x y : k) (h : (X.toProjective.baseChange k).toAffine.Nonsingular x y),
        ev P = .some x y h → ev (NeronModelInfra.schemeHomOverComp P φ) = 0) ∨
    ∃ (nX dX nY dY : k[X][Y]) (B : Set k), B.Finite ∧
      ∀ (P : SchemeHomOver (t₀ k) (π X)) (x y : k) (h : (X.toProjective.baseChange k).toAffine.Nonsingular x y),
        ev P = .some x y h → x ∉ B →
        dX.evalEval x y ≠ 0 ∧ dY.evalEval x y ≠ 0 ∧
          ∃ h', ev (NeronModelInfra.schemeHomOverComp P φ) =
            .some (nX.evalEval x y / dX.evalEval x y) (nY.evalEval x y / dY.evalEval x y) h' := by
  classical

  have hbc : X.toProjective.baseChange k = X := by
    change X.map (algebraMap k k) = X
    rw [Algebra.algebraMap_self, WeierstrassCurve.map_id]
  have hns : ∀ x y : k, (X.toProjective.baseChange k).toAffine.Nonsingular x y ↔ X.toAffine.Nonsingular x y := by
    intro x y; rw [hbc]

  set W : WeierstrassCurve.Affine k := X.toAffine with hW
  haveI : W.IsElliptic := by rw [hW]; infer_instance
  let A : Type := W.CoordinateRing
  let mkA : k[X][Y] →+* A := WeierstrassCurve.Affine.CoordinateRing.mk W
  have mkA_surj : Function.Surjective mkA := AdjoinRoot.mk_surjective

  obtain ⟨fZ, hfZ_bij, hfZ_alg, hfZ_gen⟩ := WeierstrassProjModel.exists_zChartAway_equiv_coordinateRing X.toProjective
  let fA : ZChartRing X.toProjective →+* A := fZ
  let 𝒜 := WeierstrassProjModel.projModelGradingCR X.toProjective
  let ιk : k →+* ZChartRing X.toProjective :=
    (HomogeneousLocalization.fromZeroRingHom 𝒜 (Submonoid.powers (coord X.toProjective 2))).comp (algebraMap k (𝒜 0))
  have hfA_ιk : ∀ a : k, fA (ιk a) = mkA (C (C a)) := by
    intro a
    have h := RingHom.congr_fun hfZ_alg a
    refine h.trans ?_
    show algebraMap k A a = mkA (C (C a))
    rw [IsScalarTower.algebraMap_apply k k[X] A, Polynomial.algebraMap_eq, AdjoinRoot.algebraMap_eq]
    exact (AdjoinRoot.mk_C (f := W.polynomial) (C a)).symm
  have chart_over : zChartι X.toProjective ≫ π X = Spec.map (CommRingCat.ofHom ιk) := by
    show Proj.awayι 𝒜 (coord X.toProjective 2) (coord_mem X.toProjective 2) one_pos ≫
      (Proj.toSpecZero 𝒜 ≫ Spec.map (CommRingCat.ofHom (algebraMap k (𝒜 0)))) = _
    rw [← Category.assoc, AlgebraicGeometry.Proj.awayι_toSpecZero, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
  have hfx : fA (xOverZ X.toProjective) = mkA (C Polynomial.X) := by
    have h := hfZ_gen 1 (MvPolynomial.X 0)
      (by simpa using (MvPolynomial.mem_homogeneousSubmodule _ _).mpr (MvPolynomial.isHomogeneous_X k 0))
    rw [MvPolynomial.aeval_X] at h
    exact h
  have hfy : fA (yOverZ X.toProjective) = mkA (Y : k[X][Y]) := by
    have h := hfZ_gen 1 (MvPolynomial.X 1)
      (by simpa using (MvPolynomial.mem_homogeneousSubmodule _ _).mpr (MvPolynomial.isHomogeneous_X k 1))
    rw [MvPolynomial.aeval_X] at h
    exact h

  let eZA : ZChartRing X.toProjective ≃+* A := RingEquiv.ofBijective fA hfZ_bij
  let eA : Spec (CommRingCat.of A) ⟶ Spec (CommRingCat.of (ZChartRing X.toProjective)) :=
    Spec.map eZA.toCommRingCatIso.hom
  have heA : eA = Spec.map (CommRingCat.ofHom fA) := rfl

  have hPfac : ∀ (P : SchemeHomOver (t₀ k) (π X)) (x y : k) (hxy : W.Nonsingular x y)
      (hxy' : (X.toProjective.baseChange k).toAffine.Nonsingular x y),
      ev P = WeierstrassCurve.Affine.Point.some x y hxy' →
      P.1 = Spec.map (CommRingCat.ofHom (AdjoinRoot.evalEval (p := W.polynomial) hxy.1)) ≫ eA ≫
        zChartι X.toProjective := by
    intro P x y hxy hxy' hevP
    let χA : A →+* k := AdjoinRoot.evalEval (p := W.polynomial) hxy.1
    have hχA : ∀ p, χA (mkA p) = p.evalEval x y := fun p => AdjoinRoot.evalEval_mk hxy.1 p
    have hover : (Spec.map (CommRingCat.ofHom (χA.comp fA)) ≫ zChartι X.toProjective) ≫ π X = t₀ k := by
      rw [Category.assoc, chart_over, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
      have : (χA.comp fA).comp ιk = algebraMap k k := by
        ext a
        rw [RingHom.comp_apply, RingHom.comp_apply, hfA_ιk, hχA, evalEval_CC, Algebra.algebraMap_self,
          RingHom.id_apply]
      rw [this]
    obtain ⟨hxy'', hevQ⟩ := hev_chart ⟨_, hover⟩ (χA.comp fA) rfl
    have hQP : ev ⟨_, hover⟩ = ev P := by
      rw [hevQ, hevP]
      apply point_some_ext
      · rw [RingHom.comp_apply, hfx, hχA, evalEval_C, eval_X]
      · rw [RingHom.comp_apply, hfy, hχA, evalEval_X]
    have hPQ := ev.injective hQP
    rw [← hPQ]
    show Spec.map (CommRingCat.ofHom (χA.comp fA)) ≫ zChartι X.toProjective = _
    rw [heA, CommRingCat.ofHom_comp, Spec.map_comp, Category.assoc]

  let c : Spec (CommRingCat.of A) ⟶ E X := eA ≫ zChartι X.toProjective ≫ φ.1
  let V : Set (Spec (CommRingCat.of A)) := c ⁻¹' Set.range (zChartι X.toProjective)
  have hVopen : IsOpen V :=
    (IsOpenImmersion.isOpen_range (zChartι X.toProjective)).preimage c.continuous

  obtain ⟨pt⟩ : Nonempty (Spec (CommRingCat.of k) : Scheme.{0}) := inferInstance
  by_cases hV : ∃ p, p ∈ V
  swap
  ·
    left
    intro P x y hxy' hevP
    have hxy : W.Nonsingular x y := (hns x y).1 hxy'
    have hP := hPfac P x y hxy hxy' hevP
    rcases hevφ : ev (NeronModelInfra.schemeHomOverComp P φ) with _ | @⟨x', y', hxy₂'⟩
    · rfl
    · exfalso
      apply hV
      have hxy₂ : W.Nonsingular x' y' := (hns x' y').1 hxy₂'
      have hP₂ := hPfac (NeronModelInfra.schemeHomOverComp P φ) x' y' hxy₂ hxy₂' hevφ
      set χ₂ : A →+* k := AdjoinRoot.evalEval (p := W.polynomial) hxy₂.1 with hχ₂
      refine ⟨Spec.map (CommRingCat.ofHom (AdjoinRoot.evalEval (p := W.polynomial) hxy.1)) pt, ?_⟩
      show c _ ∈ Set.range (zChartι X.toProjective)
      have h1 : c (Spec.map (CommRingCat.ofHom (AdjoinRoot.evalEval (p := W.polynomial) hxy.1)) pt) =
          (P.1 ≫ φ.1) pt := by
        rw [hP]
        simp only [c, Scheme.Hom.comp_apply]
      rw [h1]
      have h2 : P.1 ≫ φ.1 = (NeronModelInfra.schemeHomOverComp P φ).1 := rfl
      rw [h2, hP₂]
      refine ⟨eA (Spec.map (CommRingCat.ofHom χ₂) pt), ?_⟩
      simp only [Scheme.Hom.comp_apply]
  ·
    right
    obtain ⟨p, hp⟩ := hV
    obtain ⟨_, ⟨s, rfl⟩, hps, hsV⟩ :=
      (PrimeSpectrum.isTopologicalBasis_basic_opens (R := A)).exists_subset_of_mem_open hp hVopen
    have hps' : p ∈ PrimeSpectrum.basicOpen s := hps
    have hsV' : (PrimeSpectrum.basicOpen s : Set (PrimeSpectrum A)) ⊆ V := hsV
    have hs0 : s ≠ 0 := by
      intro h0
      rw [h0] at hps'
      exact (PrimeSpectrum.mem_basicOpen _ _).1 hps' (Ideal.zero_mem _)

    let L : Type := Localization.Away s
    let ℓ : A →+* L := algebraMap A L
    let u : Spec (CommRingCat.of L) ⟶ E X := Spec.map (CommRingCat.ofHom ℓ) ≫ eA ≫ zChartι X.toProjective
    let g : Spec (CommRingCat.of L) ⟶ E X := u ≫ φ.1
    have hrange : Set.range g ⊆ Set.range (zChartι X.toProjective) := by
      rintro _ ⟨z, rfl⟩
      have hz : Spec.map (CommRingCat.ofHom ℓ) z ∈ V := by
        apply hsV'
        show PrimeSpectrum.comap ℓ z ∈ (PrimeSpectrum.basicOpen s : Set (PrimeSpectrum A))
        rw [← PrimeSpectrum.localization_away_comap_range L s]
        exact ⟨z, rfl⟩
      have : g z = c (Spec.map (CommRingCat.ofHom ℓ) z) := by
        simp only [g, u, c, Scheme.Hom.comp_apply]
      rw [this]
      exact hz
    let g' : Spec (CommRingCat.of L) ⟶ Spec (CommRingCat.of (ZChartRing X.toProjective)) :=
      IsOpenImmersion.lift (zChartι X.toProjective) g hrange
    have hg' : g' ≫ zChartι X.toProjective = g := IsOpenImmersion.lift_fac _ _ hrange
    let ψZ : CommRingCat.of (ZChartRing X.toProjective) ⟶ CommRingCat.of L := Spec.preimage g'
    have hψZ : Spec.map ψZ = g' := Spec.map_preimage g'
    let ψ : ZChartRing X.toProjective →+* L := ψZ.hom

    obtain ⟨⟨aX, ⟨_, n, rfl⟩⟩, haX⟩ := IsLocalization.surj (Submonoid.powers s) (ψ (xOverZ X.toProjective))
    obtain ⟨⟨aY, ⟨_, m, rfl⟩⟩, haY⟩ := IsLocalization.surj (Submonoid.powers s) (ψ (yOverZ X.toProjective))
    simp only at haX haY
    obtain ⟨pX, hpX⟩ := mkA_surj aX
    obtain ⟨pY, hpY⟩ := mkA_surj aY
    obtain ⟨pS, hpS⟩ := mkA_surj s

    let B : Set k := {x | ∃ y, W.Equation x y ∧ pS.evalEval x y = 0}
    have hB : B.Finite := by
      by_contra hinf
      apply hs0
      rw [← hpS]
      exact mk_eq_zero_of_infinite W pS hinf
    refine ⟨pX, pS ^ n, pY, pS ^ m, B, hB, ?_⟩
    intro P x y hxy' hevP hxB
    have hxy : W.Nonsingular x y := (hns x y).1 hxy'
    have hpSxy : pS.evalEval x y ≠ 0 := fun h0 => hxB ⟨y, hxy.1, h0⟩
    have hdX : (pS ^ n).evalEval x y ≠ 0 := by rw [evalEval_pow]; exact pow_ne_zero _ hpSxy
    have hdY : (pS ^ m).evalEval x y ≠ 0 := by rw [evalEval_pow]; exact pow_ne_zero _ hpSxy
    refine ⟨hdX, hdY, ?_⟩

    let χA : A →+* k := AdjoinRoot.evalEval (p := W.polynomial) hxy.1
    have hχA : ∀ p, χA (mkA p) = p.evalEval x y := fun p => AdjoinRoot.evalEval_mk hxy.1 p
    have hχs : IsUnit (χA s) := by
      rw [← hpS, hχA]; exact isUnit_iff_ne_zero.2 hpSxy
    let χL : L →+* k := IsLocalization.Away.lift s hχs
    have hχL : ∀ a : A, χL (ℓ a) = χA a := fun a => IsLocalization.Away.lift_eq s hχs a
    have hχLcomp : χL.comp ℓ = χA := IsLocalization.Away.lift_comp s hχs
    have hχAs : χA s = pS.evalEval x y := by rw [← hpS, hχA]

    have hP := hPfac P x y hxy hxy' hevP
    have hPu : P.1 = Spec.map (CommRingCat.ofHom χL) ≫ u := by
      rw [hP]
      show _ = Spec.map (CommRingCat.ofHom χL) ≫ Spec.map (CommRingCat.ofHom ℓ) ≫ eA ≫ zChartι X.toProjective
      rw [← Category.assoc (Spec.map (CommRingCat.ofHom χL)), ← Spec.map_comp, ← CommRingCat.ofHom_comp, hχLcomp]

    have hPφ : (NeronModelInfra.schemeHomOverComp P φ).1 =
        Spec.map (CommRingCat.ofHom (χL.comp ψ)) ≫ zChartι X.toProjective := by
      show P.1 ≫ φ.1 = _
      rw [hPu, Category.assoc]
      change Spec.map (CommRingCat.ofHom χL) ≫ g = _
      rw [← hg', ← hψZ, ← Category.assoc, ← Spec.map_comp]
      rfl
    obtain ⟨hns2, hev2⟩ := hev_chart (NeronModelInfra.schemeHomOverComp P φ) (χL.comp ψ) hPφ

    have hvx : χL (ψ (xOverZ X.toProjective)) = pX.evalEval x y / (pS ^ n).evalEval x y := by
      have h1 := congrArg χL haX
      rw [map_mul, hχL, hχL, ← hpX, hχA, map_pow, hχAs, ← evalEval_pow] at h1
      exact eq_div_of_mul_eq hdX h1
    have hvy : χL (ψ (yOverZ X.toProjective)) = pY.evalEval x y / (pS ^ m).evalEval x y := by
      have h1 := congrArg χL haY
      rw [map_mul, hχL, hχL, ← hpY, hχA, map_pow, hχAs, ← evalEval_pow] at h1
      exact eq_div_of_mul_eq hdY h1
    refine ⟨?_, ?_⟩
    · have h := hns2
      rw [RingHom.comp_apply, RingHom.comp_apply, hvx, hvy] at h
      exact h
    · rw [hev2]
      exact point_some_ext (by rw [RingHom.comp_apply, hvx]) (by rw [RingHom.comp_apply, hvy])

end Restrict

section Main

open WeierstrassCurve.DrinfeldGlobal

variable {k : Type} [Field k] [IsAlgClosed k] [DecidableEq k]
variable {X : WeierstrassCurve k} [X.IsElliptic]
variable (ev : SchemeHomOver (t₀ k) (π X) ≃ (X.toProjective.baseChange k).toAffine.Point)

theorem eq_of_forall_ev_eq (φ ψ : SchemeHomOver (π X) (π X))
    (h : ∀ P : SchemeHomOver (t₀ k) (π X),
      ev (NeronModelInfra.schemeHomOverComp P φ) = ev (NeronModelInfra.schemeHomOverComp P ψ)) :
    φ = ψ := by
  refine AlgebraicGeometry.SchemeHomOver.ext_of_forall_point_of_isReduced_of_locallyOfFiniteType k φ ψ ?_
  intro x
  have := h ⟨x.1, x.2.trans (t₀_eq k).symm⟩
  exact congrArg Subtype.val (ev.injective this)

end Main

end DeuringEqSol
p2m_reactivate "P2MW.S_CerednikDrinfeld_QM_exists_relativeGroupLaw_isMaximalOrder_act_injective_and_forall_exists_eq_of_charP.DeuringEqSol"

end
p2m_reactivate "P2MW.S_CerednikDrinfeld_QM_exists_relativeGroupLaw_isMaximalOrder_act_injective_and_forall_exists_eq_of_charP.DeuringEqSol"

p2m_open "P2MW.S_CerednikDrinfeld_QM_exists_relativeGroupLaw_isMaximalOrder_act_injective_and_forall_exists_eq_of_charP.DeuringEqSol NeronModelInfra GoodReductionJacobian QuaternionAlgebra~baseChange CerednikDrinfeld CerednikDrinfeld.QM"
open scoped Quaternion

theorem solution
    (q : ℕ) [Fact q.Prime]
    (k : Type) [Field k] [IsAlgClosed k] [CharP k q] [Algebra (ZMod q) k] [Algebra.IsAlgebraic (ZMod q) k] :
    ∃ (A : Scheme.{0}) (f : A ⟶ Spec (CommRingCat.of k)) (L : RelativeGroupLaw k f),
      L.IsCommutative ∧ AbelianSchemePropertyBundle k f ∧ SmoothOfRelativeDimension 1 f ∧
      ∃ (c d : ℚ) (_ : IsDefiniteRamifiedExactlyAt c d q)
        (O : Submodule ℤ ℍ[ℚ, c, d]) (_ : IsMaximalOrder O)
        (ε : ↥O → (A ⟶ A)) (hε : ∀ x : ↥O, ε x ≫ f = f),
        (∀ (x : ↥O) {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of k)) (P Q : SchemeHomOver t f),
          pushPt (ε x) (hε x) (L.mul t P Q) = L.mul t (pushPt (ε x) (hε x) P) (pushPt (ε x) (hε x) Q)) ∧
        (∀ h : (1 : ℍ[ℚ, c, d]) ∈ O, ε ⟨1, h⟩ = 𝟙 A) ∧
        (∀ (x y : ↥O) (h : (x : ℍ[ℚ, c, d]) * (y : ℍ[ℚ, c, d]) ∈ O),
          ε ⟨(x : ℍ[ℚ, c, d]) * (y : ℍ[ℚ, c, d]), h⟩ = ε y ≫ ε x) ∧
        (∀ (x y : ↥O) {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of k)) (P : SchemeHomOver t f),
          pushPt (ε (x + y)) (hε (x + y)) P = L.mul t (pushPt (ε x) (hε x) P) (pushPt (ε y) (hε y) P)) ∧

        Function.Injective ε ∧
        (∀ (φ : A ⟶ A) (hφ : φ ≫ f = f),
          (∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of k)) (P Q : SchemeHomOver t f),
            mapPt φ hφ (L.mul t P Q) = L.mul t (mapPt φ hφ P) (mapPt φ hφ Q)) → ∃ x : ↥O, φ = ε x) := by
  classical
  have hq : q.Prime := Fact.out

  obtain ⟨c, d, hdef, Λ, Λ₁, Λ₂, hΛ₁, -, -, -⟩ :=
    QuaternionAlgebra.exists_isDefiniteRamifiedExactlyAt_isEichlerOrder q hq 1 one_ne_zero
      (fun h => hq.one_lt.ne' (Nat.dvd_one.mp h))

  obtain ⟨X₀, hell, -, θ, hθinj, hθrange⟩ :=
    WeierstrassCurve.exists_supersingular_rationalEndSubring_range_eq_of_isMaximalOrder
      (κ := k) q c d hdef Λ₁ hΛ₁

  obtain ⟨hbc, G₁, ev₁, hev₁⟩ :=
    WeierstrassProjModel.exists_relativeGroupLaw_isPointsEval_of_isElliptic_of_isDomain (R := k) X₀.toProjective
  obtain ⟨G, hGcomm, hGone⟩ :=
    WeierstrassProjModel.RelativeGroupLaw.exists_isCommutative_one_eq_zeroSect_of_isCommutative
      X₀.toProjective G₁ (fun t x y => WeierstrassProjModel.mul_comm_of_isPointsEval k X₀ G₁ ev₁ hev₁ t x y)
  have hG1 : (G.one (𝟙 _)).1 = (WeierstrassProjModel.kwZeroSect k X₀).1 := by
    rw [hGone (𝟙 _), Category.id_comp]
  obtain ⟨ev, hIs, -, hchart⟩ :=
    WeierstrassProjModel.exists_isPointsEval_apply_eq_some_of_eq_comp_zChartInclusion X₀ X₀.isUnit_Δ G hG1

  obtain ⟨Φ, hΦev, hΦhom, hΦone, hΦmul, hΦadd⟩ :=
    WeierstrassProjModel.exists_action_rationalEndSubring_of_isAlgClosed X₀ G (ev k)
      (fun P Q => hIs.1 k P Q) (fun P χ h => hchart k P χ h)

  have hmem : ∀ x : ↥Λ₁, ∃ α : ↥(WeierstrassCurve.rationalEndSubring k X₀), θ α = (x : ℍ[ℚ, c, d]) := by
    intro x
    have hx : (x : ℍ[ℚ, c, d]) ∈ Set.range θ := by rw [hθrange]; exact x.2
    exact hx
  choose ι hι using hmem
  have hι_one : ∀ h : (1 : ℍ[ℚ, c, d]) ∈ Λ₁, ι ⟨1, h⟩ = 1 := by
    intro h
    apply hθinj
    rw [hι, map_one]
  have hι_mul : ∀ (x y : ↥Λ₁) (h : (x : ℍ[ℚ, c, d]) * (y : ℍ[ℚ, c, d]) ∈ Λ₁),
      ι ⟨(x : ℍ[ℚ, c, d]) * (y : ℍ[ℚ, c, d]), h⟩ = ι x * ι y := by
    intro x y h
    apply hθinj
    rw [hι, map_mul, hι, hι]
  have hι_add : ∀ x y : ↥Λ₁, ι (x + y) = ι x + ι y := by
    intro x y
    apply hθinj
    rw [hι, map_add, hι, hι, Submodule.coe_add]
  have hι_inj : ∀ x y : ↥Λ₁, ι x = ι y → x = y := by
    intro x y h
    apply Subtype.ext
    rw [← hι x, ← hι y, h]
  have hpush : ∀ (α : ↥(WeierstrassCurve.rationalEndSubring k X₀)) {T : Scheme.{0}}
      (t : T ⟶ Spec (CommRingCat.of k)) (P : SchemeHomOver t (π X₀)),
      pushPt (Φ α).1 (Φ α).2 P = NeronModelInfra.schemeHomOverComp P (Φ α) := fun α {T} t P => rfl
  refine ⟨E X₀, π X₀, toGRJ X₀ G, fun t x y => hGcomm t x y, bundle X₀ G,
    WeierstrassProjModel.projModelStrCR_smoothOfRelativeDimension_one X₀.toProjective,
    c, d, hdef, Λ₁, hΛ₁, fun x => (Φ (ι x)).1, fun x => (Φ (ι x)).2, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro x T t P Q
    dsimp only
    rw [hpush, hpush, hpush]
    exact hΦhom (ι x) t P Q
  · intro h
    show (Φ (ι ⟨1, h⟩)).1 = 𝟙 _
    rw [hι_one h, hΦone]
    rfl
  · intro x y h
    show (Φ (ι ⟨(x : ℍ[ℚ, c, d]) * (y : ℍ[ℚ, c, d]), h⟩)).1 = (Φ (ι y)).1 ≫ (Φ (ι x)).1
    rw [hι_mul x y h, hΦmul]
    rfl
  · intro x y T t P
    dsimp only
    rw [hpush, hpush, hpush, hι_add, hΦadd]
    rfl
  ·
    intro x y hxy
    apply hι_inj
    have hΦeq : Φ (ι x) = Φ (ι y) := Subtype.ext hxy
    apply Subtype.ext
    apply AddMonoidHom.ext
    intro Q
    obtain ⟨P, rfl⟩ := (ev k).surjective Q
    have h1 := hΦev (ι x) P
    have h2 := hΦev (ι y) P
    rw [hΦeq] at h1
    exact h1.symm.trans h2
  ·
    intro φ hφ hhom
    let φ' : SchemeHomOver (π X₀) (π X₀) := ⟨φ, hφ⟩

    have hadd : ∀ Q Q' : (X₀.toProjective.baseChange k).toAffine.Point,
        ev k (NeronModelInfra.schemeHomOverComp ((ev k).symm (Q + Q')) φ') =
          ev k (NeronModelInfra.schemeHomOverComp ((ev k).symm Q) φ') +
            ev k (NeronModelInfra.schemeHomOverComp ((ev k).symm Q') φ') := by
      intro Q Q'
      have h1 : (ev k).symm (Q + Q') = G.mul _ ((ev k).symm Q) ((ev k).symm Q') := by
        apply (ev k).injective
        rw [hIs.1 k, Equiv.apply_symm_apply, Equiv.apply_symm_apply, Equiv.apply_symm_apply]
      rw [h1]
      have h2 := hhom (t₀ k) ((ev k).symm Q) ((ev k).symm Q')
      have h3 : NeronModelInfra.schemeHomOverComp (G.mul _ ((ev k).symm Q) ((ev k).symm Q')) φ' =
          G.mul _ (NeronModelInfra.schemeHomOverComp ((ev k).symm Q) φ')
            (NeronModelInfra.schemeHomOverComp ((ev k).symm Q') φ') := h2
      rw [h3, hIs.1 k]
    let α : (X₀.baseChange k).toAffine.Point →+ (X₀.baseChange k).toAffine.Point :=
      AddMonoidHom.mk' (fun Q => ev k (NeronModelInfra.schemeHomOverComp ((ev k).symm Q) φ')) hadd
    have hαQ : ∀ Q, α Q = ev k (NeronModelInfra.schemeHomOverComp ((ev k).symm Q) φ') := fun Q => rfl
    have hαP : ∀ P : SchemeHomOver (t₀ k) (π X₀),
        ev k (NeronModelInfra.schemeHomOverComp P φ') = α (ev k P) := by
      intro P
      rw [hαQ, Equiv.symm_apply_apply]

    have hev' : ∀ (p : k[X][Y]) (x y : k), WeierstrassCurve.evalEvalBC k p x y = p.evalEval x y := by
      intro p x y
      simp only [WeierstrassCurve.evalEvalBC, Algebra.algebraMap_self, Polynomial.mapRingHom_id, Polynomial.map_id]
    have hαmem : α ∈ WeierstrassCurve.rationalHomSet k X₀ X₀ := by
      rcases restrict X₀ (ev k) (fun P χ h => hchart k P χ h) φ' with hA | ⟨nX, dX, nY, dY, B, hB, hrep⟩
      · left
        ext Q
        rcases Q with _ | @⟨x, y, hxy⟩
        · exact (map_zero α).trans (map_zero (0 : _ →+ (X₀.baseChange k).toAffine.Point)).symm
        · rw [hαQ, AddMonoidHom.zero_apply]
          exact hA _ x y hxy (Equiv.apply_symm_apply _ _)
      · right
        refine ⟨nX, dX, nY, dY, B, hB, fun x y hxy hxB => ?_⟩
        obtain ⟨hdX, hdY, h', heq⟩ := hrep ((ev k).symm (.some x y hxy)) x y hxy (Equiv.apply_symm_apply _ _) hxB
        refine ⟨by rw [hev']; exact hdX, by rw [hev']; exact hdY, ?_⟩
        have h'' : (X₀.baseChange k).toAffine.Nonsingular
            (WeierstrassCurve.evalEvalBC k nX x y / WeierstrassCurve.evalEvalBC k dX x y)
            (WeierstrassCurve.evalEvalBC k nY x y / WeierstrassCurve.evalEvalBC k dY x y) := by
          rw [hev', hev', hev', hev']; exact h'
        refine ⟨h'', ?_⟩
        rw [hαQ, heq]
        exact point_some_ext (by rw [hev', hev']) (by rw [hev', hev'])
    have hαsub : (α : AddMonoid.End (X₀.baseChange k).toAffine.Point) ∈
        WeierstrassCurve.rationalEndSubring k X₀ := Subring.subset_closure hαmem
    set a : ↥(WeierstrassCurve.rationalEndSubring k X₀) := ⟨α, hαsub⟩ with ha
    have hθa : θ a ∈ (Λ₁ : Set ℍ[ℚ, c, d]) := by rw [← hθrange]; exact ⟨a, rfl⟩
    let x : ↥Λ₁ := ⟨θ a, hθa⟩
    have hιx : ι x = a := hθinj (by rw [hι x])
    refine ⟨x, ?_⟩
    show φ = (Φ (ι x)).1
    rw [hιx]
    have hφa : φ' = Φ a := by
      apply eq_of_forall_ev_eq (ev k)
      intro P
      rw [hαP, hΦev a P]
      rfl
    exact congrArg Subtype.val hφa

end S_CerednikDrinfeld_QM_exists_relativeGroupLaw_isMaximalOrder_act_injective_and_forall_exists_eq_of_charP
end P2MW
export P2MW.S_CerednikDrinfeld_QM_exists_relativeGroupLaw_isMaximalOrder_act_injective_and_forall_exists_eq_of_charP (solution)
