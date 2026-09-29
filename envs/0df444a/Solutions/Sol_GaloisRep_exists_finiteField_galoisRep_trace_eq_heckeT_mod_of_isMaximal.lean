-- Prove2me | solution 1 for GaloisRep.exists_finiteField_galoisRep_trace_eq_heckeT_mod_of_isMaximal
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.331093+00:00
-- url     : https://prove2.me/submissions/aafa476a-27e9-555a-a4af-612eb11928be

import Mathlib
import Definitions.Def_CuspForm_HeckeAlgebra
import Definitions.Def_GaloisRep_Residual
import Definitions.Def_FLTPrelim_Ramification
import Definitions.Def_EllipticCurve_FrobeniusTrace
import Theorems.Thm_GaloisRep_exists_finiteField_galoisRep_trace_eq_heckeT_mod_of_isMaximal_two
import Theorems.Thm_GaloisRep_exists_galoisRep_trace_eq_eigenchar_and_det_eq_pow_of_three_le
import Theorems.Thm_DeligneSerre_exists_eigencharacter_of_annihilator_le
import Theorems.Thm_CuspForm_moduleFinite_heckeAlgebra
import Theorems.Thm_CuspForm_finiteDimensional_Gamma0
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_GaloisRep_exists_finiteField_galoisRep_trace_eq_heckeT_mod_of_isMaximal
p2m_attr_erase "instance" "GaloisRepAdic.instAddCommGroup GaloisRepAdic.instFree GaloisRepAdic.instFinite GaloisRepAdic.instModule ModularCurve.instSMulAlgEquivRatPic0SubtypeLaurentSeriesMemIntermediateFieldLaurentBaseChange ModularCurve.instDistribMulActionAlgEquivRatPic0SubtypeLaurentSeriesMemIntermediateFieldLaurentBaseChange AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupDivisor AlgebraicCurve.Pic0.instModuleZModTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instDistribMulActionTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instSMulTorsion AlgebraicCurve.SemilinearAut.instMulActionSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instSMulCommClassZModTorsion AlgebraicCurve.SemilinearAut.instMulSemiringActionSubtypeProdRingAutMemSubgroup AlgebraicCurve.Place.instIsScalarTowerSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Divisor.instDistribMulActionAlgEquiv AlgebraicCurve.Place.instSMulAlgEquiv AlgebraicCurve.Place.instIsPrincipalIdealRingSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Place.instIsDiscreteValuationRingSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Pic0.instDistribMulActionAlgEquiv AlgebraicCurve.Place.instAlgebraSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Place.instMulActionAlgEquiv AlgebraicCurve.Pic0.instSMulAlgEquiv TateModule.instModule TateModule.instSMul AlgebraicCurve.instFundamentalIdentityOfSumRamificationInertia AlgebraicCurve.Place.instIsScalarTowerResidueFieldRestrictPushforward AlgebraicCurve.Place.instAlgebraResidueFieldRestrictPushforward AlgebraicCurve.Place.instIsLocalHomRestrictInclusion AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue"
p2m_attr_erase "instance" "AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation ModularCurve.PhiGen.instNeZeroPhiGenCosetA ModularCurve.instIsDomainTensorProduct AlgebraicClosure.Rat.isGalois ModularCurve.CuspSpace.instNonempty ModularCurve.CuspSpace.instSubsingletonOfOne ModularCurve.CuspSpace.instFinite ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid ModularCurve.instAlgebraIntermediateFieldLaurent ModularCurve.instIsScalarTowerKaehlerIntermediateFieldLaurent ModularCurve.instIsScalarTowerIntermediateFieldLaurent ModularCurve.instModuleKaehlerIntermediateFieldLaurent ModularCurve.Gamma0Pair.isElliptic ModularCurve.TatePoint.instIsElliptic_nearCurve ModularCurve.instIsElliptic_tateLaurent WeierstrassCurve.Affine.instIsScalarTowerPolynomialRatFuncFunctionField_definitions WeierstrassCurve.Affine.instAlgebraRatFuncFunctionField_definitions WeierstrassCurve.Affine.instIsScalarTowerRatFuncFunctionField_definitions WeierstrassCurve.Affine.CoordinateRing.moduleFinite WeierstrassCurve.Affine.instDecidableEqFunctionField WeierstrassCurve.Affine.CoordinateRing.isIntegral WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly ModularCurve.B3.instIsElliptic_goodModel AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions ModularCurve.instAlgebraJLineBar ModularCurve.instModuleJLineBar AlgebraicCurve.instHasLocalResidue_of_hasCanonicalLocalResidueK AlgebraicCurve.instHasCanonicalLocalResidueK_of_hasCanonicalLocalResidueKStar AlgebraicCurve.Place.kw_ffgc_finiteDimensional_adicCompletion instAlgebraSubtypeMemValuationSubring_definitions AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersIntegersCompletion ModularCurve.KwF4gRRTate.instAlgebraKAdicCompletionIntegers AlgebraicCurve.Place.kw_ffgc_continuousSMul_adicCompletionComap AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersCompletionCompletion IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions"
p2m_attr_erase "instance" "IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions AlgebraicCurve.instHasCanonicalLocalResidueK AlgebraicCurve.Place.instAlgebra_restrictResidueField AlgebraicCurve.Place.instIsScalarTower_restrictResidueField AlgebraicCurve.instHasLocalResidue AlgebraicCurve.HasSeparableResidue.of_perfectField_of_isCurveOver AlgebraicCurve.HasSeparableResidue.of_perfectField AlgebraicCurve.Place.instIsLocalHom_restrictSubringHom AlgebraicCurve.instHasCanonicalLocalResidueKStar ModularCurve.KwNo6Pin.isLocalRing_completion ModularCurve.instIsScalarTowerJAdjoin HeckeEis.instFiniteIndexHeckeUpper ModularCurve.Period.parabolicHoms_int_moduleFinite ModularCurve.Period.instGroupFG_SL2Z ModularCurve.Period.instIsNoetherian_addHom_int ModularCurve.Period.instGroupFG_Gamma0 FLT.Gamma0FundamentalSet.instContinuousConstSMulSpecialLinearGroupFinOfNatNatIntUpperHalfPlane_definitions FLT.HyperbolicMeasure.instSMulInvariantMeasureSpecialLinearGroupFinOfNatNatIntUpperHalfPlaneVolume_definitions FLT.HyperbolicMeasure.instIsOpenPosMeasureUpperHalfPlaneVolume_definitions FLT.L2ProductionInstance.isFiniteMeasure_gamma0 FLT.L2ProductionInstance.countable_SL2Z FLT.L2ProductionInstance.countable_quotient FLT.L2ProductionInstance.nontrivial_gamma0L2 HeckeEis.instModuleCoeffH1par HeckeEis.instAddCommGroupCoeffH1par AlgebraicCurve.CellDissection.fintypeV AlgebraicCurve.CellDissection.fintypeC AlgebraicCurve.CellDissection.fintypeE AlgebraicCurve.CellDissection.decEqV AlgebraicCurve.CellDissection.decEqC AlgebraicCurve.CellDissection.decEqE ValuationSubring.instIsAlgClosedResidueField WeierstrassCurve.VeluQuotientJGates.instIsElliptic27a4 ModularCurve.ElevenA1.instDecidableEquation ModularCurve.ElevenA1.instDecidableNonsingular HeckeEis.instFiniteProjLineCusps"
p2m_attr_erase "instance" "HeckeEis.instAddCommGroupCoeffH1 HeckeEis.instModuleCoeffH1 CohCarrier.iotaDeg_range_finiteIndex CohCarrier.Gamma0Upper_finiteIndex CohCarrier.HeckeData.V_isScalarTower CohCarrier.HeckeData.opSubalgebra_isMulCommutative CohCarrier.HeckeData.mTheta_isPrime CohCarrier.GammaHLower_finiteIndex ModularCurve.numberField_of_finiteDimensional"
p2m_attr_erase "simp" "PowerSeries.coeff_heckeV PowerSeries.coeff_heckeU GaloisRepAdic.mk.injEq GaloisRepAdic.mk.sizeOf_spec GaloisRepAdic.Equiv.mk.sizeOf_spec GaloisRepAdic.Equiv.mk.injEq ResidualGaloisRep.Equiv.mk.sizeOf_spec ResidualGaloisRep.Equiv.mk.injEq ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd ModularCurve.baseAut_arithmeticGalois ModularCurve.JZero.torsionGaloisRep_apply ModularCurve.coe_arithmeticRingAut_apply ModularCurve.toRingAut_arithmeticGalois ModularCurve.qExpand_coeff_mul ModularCurve.qExpandₐ_apply ModularCurve.jqN_one ModularCurve.qExpand_single ModularCurve.dedekindPsi_one ModularCurve.ModularPolynomialData.mk.sizeOf_spec ModularCurve.evalAtJ_X ModularCurve.ModularPolynomialData.mk.injEq ModularCurve.constantCoeff_jNum ModularCurve.constantCoeff_eisenstein4 ModularCurve.qExpand_C ModularCurve.coeff_jq_neg_one ModularCurve.constantCoeff_jNumQ ModularCurve.coeffEmb_coeff ModularCurve.coeffMap_coeff ModularCurve.coeffMap_id ModularCurve.coeffMap_single AlgebraicCurve.SemilinearAut.toRingAut_inv AlgebraicCurve.SemilinearAut.smul_def AlgebraicCurve.SemilinearAut.smul_single AlgebraicCurve.SemilinearAut.smul_toValuationSubring AlgebraicCurve.SemilinearAut.baseAut_inv AlgebraicCurve.SemilinearAut.baseAut_ofAlgAut AlgebraicCurve.SemilinearAut.toRingAut_ofAlgAut"
p2m_attr_erase "simp" "AlgebraicCurve.SemilinearAut.torsionRep_apply AlgebraicCurve.SemilinearAut.toRingAut_one AlgebraicCurve.SemilinearAut.deg_smul AlgebraicCurve.SemilinearAut.degree_smul AlgebraicCurve.SemilinearAut.coe_degZeroSMulHom AlgebraicCurve.SemilinearAut.baseAut_mul AlgebraicCurve.SemilinearAut.coe_smulValuationSubringEquiv_apply AlgebraicCurve.SemilinearAut.baseAut_one AlgebraicCurve.SemilinearAut.ofAlgAut_smul AlgebraicCurve.SemilinearAut.coe_torsion_smul AlgebraicCurve.SemilinearAut.toRingAut_mul AlgebraicCurve.Place.mk.injEq AlgebraicCurve.Divisor.degree_single AlgebraicCurve.Divisor.smul_single AlgebraicCurve.Place.smul_toValuationSubring AlgebraicCurve.Place.heightOneSpectrum_asIdeal AlgebraicCurve.Place.coe_algebraMap AlgebraicCurve.Place.ord_one AlgebraicCurve.Place.coe_smulRingEquiv_apply AlgebraicCurve.Pic0.coe_degZeroSMulHom AlgebraicCurve.Place.deg_smul AlgebraicCurve.Pic0.mk_zero AlgebraicCurve.Place.mk.sizeOf_spec AlgebraicCurve.Divisor.degree_smul AlgebraicCurve.Pic0.mk_add AlgebraicCurve.Place.ord_zero AlgebraicCurve.Place.ofHeightOneSpectrum_toValuationSubring TateModule.smul_apply TateModule.coe_mulP TateModule.proj_apply TateModule.coe_add TateModule.coe_sub WeierstrassCurve.tateModuleRepOfBasis_V TateModule.coe_zero TateModule.rep_apply WeierstrassCurve.tateModuleRep_V WeierstrassCurve.tateModuleRepOfBasis_ρ_apply GaloisRep.padicIntToRingLevel_apply TateModule.coe_neg WeierstrassCurve.tateModuleRep_ρ_apply"
p2m_attr_erase "simp" "ModularCurve.coe_heckeBetaBarRingHom ModularCurve.coe_heckeBetaBar ModularCurve.coe_heckeAlphaBar AlgebraicCurve.Divisor.degree_pushforwardAlong AlgebraicCurve.Pic0.coe_degZeroCorrespondence AlgebraicCurve.Place.mem_fiberAlong AlgebraicCurve.Divisor.mapRestrict_single AlgebraicCurve.Divisor.pushforward_single AlgebraicCurve.Place.coe_restrictInclusion AlgebraicCurve.Place.mem_fiber AlgebraicCurve.Place.restrict_toValuationSubring AlgebraicCurve.Divisor.degree_pushforward AlgebraicCurve.Place.restrictResidueMap_residue AlgebraicCurve.Pic0.coe_pushforwardDegZeroHom AlgebraicCurve.Pic0.coe_pullbackDegZeroHom ModularCurve.coe_towerInclBar ModularCurve.coe_towerSubstBar AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring"
p2m_attr_erase "simp" "AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.jqNModC_one ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularCurve.coe_baseChangeEquiv_apply ModularCurve.baseChangeHom_tmul ModularCurve.qInftyPlaceBar_toValuationSubring ModularCurve.qSeriesBar_zero ModularCurve.qSeriesBar_add ModularCurve.cuspInftyFull_toValuationSubring ModularCurve.qInftyPlaceRat_toValuationSubring ModularCurve.qSeriesBar_mul ModularCurve.qSeriesBar_div ModularCurve.qSeriesBar_eq_zero_iff ModularCurve.coe_uniformizerBar ModularCurve.qSeriesBar_pow ModularCurve.cuspInfty_toValuationSubring ModularCurve.qSeriesBar_one ModularCurve.qSeriesBar_inv ModularCurve.qSeriesBar_sub"
p2m_attr_erase "simp" "ModularCurve.qSeriesBar_neg ModularCurve.coe_cuspidalDivisor₀ ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ ModularCurve.dualHeckeRep_apply_apply ModularCurve.coe_segmentPath ModularCurve.cuspHeckeAeval_heckeGen ModularCurve.coe_periodLatticeRestrict_apply ModularCurve.Period.IsEquivariantPrimitive.periodHom_apply ModularCurve.Period.IsEquivariantPrimitive.period_one ModularCurve.cuspCount_one ModularCurve.CuspSpace.cuspDenomAux_infty ModularCurve.CuspSpace.cuspDenomAux_coe ModularCurve.CuspSpace.cuspDenom_mk_zero ModularCurve.CuspSpace.cuspDenom_mk_infty ModularCurve.mapGL_apply_coe ModularCurve.ratPoint_one_zero ModularCurve.ratPoint_zero_right ModularCurve.CuspSpace.fromCoset_mk ModularCurve.CuspSpace.cuspDenom_mk ModularCurve.ratPoint_zero_one ModularCurve.ProjectiveLine.map_mk ModularCurve.qEulerFun_coeff ModularCurve.diffQExp_D ModularCurve.qEulerOn_apply ModularCurve.qEuler_coeff AlgebraicCurve.Place.differentialCoeff_zero AlgebraicCurve.Place.differentialCoeff_dCoord ModularCurve.gamma0PairMap_gen ModularCurve.moduliPointMapRingHom_mk ModularCurve.Gamma0Pair.mk.injEq ModularCurve.ModuliPoint.j_mk ModularCurve.Gamma0Pair.mk.sizeOf_spec ModularCurve.gamma0PairMap_toCurve"
p2m_attr_erase "simp" "WeierstrassCurve.Affine.vcY_vcYInv WeierstrassCurve.Affine.vcXInv_vcX WeierstrassCurve.Affine.Point.vcFun_zero WeierstrassCurve.Affine.vcX_vcXInv WeierstrassCurve.Affine.vcYInv_vcY WeierstrassCurve.Affine.Point.vcInvFun_zero WeierstrassCurve.ratPointHom_apply WeierstrassCurve.ratPointMap_zero ModularCurve.tateLaurent_a₆ ModularCurve.tatePowerSeries_a₄ ModularCurve.tatePowerSeries_a₆ ModularCurve.tateLaurent_a₄ ModularCurve.tatePowerSeries_a₁ ModularCurve.tatePowerSeries_a₂ ModularCurve.tatePowerSeries_a₃ WeierstrassCurve.veluX_empty WeierstrassCurve.veluWSum_empty WeierstrassCurve.veluQuotient_a₁ WeierstrassCurve.veluQuotient_a₃ WeierstrassCurve.veluQuotient_empty WeierstrassCurve.veluTSum_empty WeierstrassCurve.veluQuotient_a₂ WeierstrassCurve.Affine.Point.coordsOrZero_some WeierstrassCurve.Affine.Point.coordsOrZero_zero WeierstrassCurve.veluY_empty WeierstrassCurve.Affine.IsogenyEndDatum.mk.injEq WeierstrassCurve.Affine.IsogenyHomDatum.mk.sizeOf_spec WeierstrassCurve.Affine.IsogenyHomDatum.mk.injEq WeierstrassCurve.Affine.IsogenyEndDatum.mk.sizeOf_spec AlgebraicCurve.Pic0.coe_pushforwardAlongDegZero WeierstrassCurve.Affine.pointMapOfPushforward_apply WeierstrassCurve.Affine.pointClass_zero WeierstrassCurve.Affine.pic0ToPoint_pointClass WeierstrassCurve.Affine.deg_placeOfPoint WeierstrassCurve.Affine.coe_pointDivisor WeierstrassCurve.Affine.pointEquivPlace_symm_placeOfPoint WeierstrassCurve.Affine.pointEquivPlace_apply WeierstrassCurve.Affine.genusOnePic0Equiv_symm_apply WeierstrassCurve.Affine.pointDivisor_zero WeierstrassCurve.Affine.pic0ToPoint_mk"
p2m_attr_erase "simp" "WeierstrassCurve.Affine.divisorSum_single WeierstrassCurve.Affine.genusOnePic0Equiv_apply PeriodPair.weierstrassCurve_a₆ PeriodPair.weierstrassCurve_a₃ PeriodPair.weierstrassCurve_a₁ PeriodPair.ofTau_ω₂ PeriodPair.scale_ω₂ PeriodPair.ofTau_ω₁ PeriodPair.toPoint_zero PeriodPair.toPoint_of_mem PeriodPair.weierstrassCurve_a₂ PeriodPair.ofTau_lattice PeriodPair.scale_ω₁ PeriodPair.weierstrassCurve_a₄ WeierstrassCurve.Affine.ratFuncToFunctionField_algebraMap AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one WeierstrassCurve.Affine.pointHom_mk_C_C WeierstrassCurve.Affine.Point.yc_some WeierstrassCurve.Affine.Point.xc_some WeierstrassCurve.Affine.pointPull_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_X WeierstrassCurve.Affine.pointHom_mk_Y WeierstrassCurve.Affine.placeOf_asIdeal compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg"
p2m_attr_erase "simp" "WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two AddMonoid.End.DualEndData.symm_trace AddMonoid.End.dualEndData_intCast_norm AddMonoid.End.DualEndData.ofCharPoly_norm AddMonoid.End.DualEndData.mk.sizeOf_spec AddMonoid.End.DualEndData.mk.injEq AddMonoid.End.DualEndData.ofCharPoly_dual AddMonoid.End.dualEndData_intCast_dual AddMonoid.End.DualEndData.intLinComb_norm AddMonoid.End.DualEndData.ofCharPoly_trace AddMonoid.End.DualEndData.intLinComb_dual AddMonoid.End.DualEndData.symm_dual AddMonoid.End.DualEndData.intLinComb_trace AddMonoid.End.dualEndData_intCast_trace AddMonoid.End.DualEndData.symm_norm WeierstrassCurve.veluQuotientOfSums_a₂ WeierstrassCurve.veluQuotientOfSums_a₁ WeierstrassCurve.veluQuotientOfSums_a₃ WeierstrassCurve.veluQuotient2_a₂ WeierstrassCurve.veluQuotient2_a₃ WeierstrassCurve.veluQuotient2_a₁ ModularCurve.B3.cycOfCongr_apply_coe ModularCurve.B3.cycOfTorsionBy_symm_apply_coe ModularCurve.B3.redPoint_zero"
p2m_attr_erase "simp" "ModularCurve.B3.pointAddEquivOfEq_rfl ModularCurve.B3.vcAddEquiv_apply ModularCurve.B3.scaleAddEquiv_apply ModularCurve.B3.cycOfTorsionBy_apply_coe ModularCurve.B3.val_inv_sU ModularCurve.B3.val_sU ModularCurve.B3.resO_apply HahnSeries.coeff_hahnTwist ModularCurve.HahnSpecialise.coe_specialiseCycSub CycSubOf.coe_map ModularCurve.HahnSpecialise.algebraMap_Qbar_apply ModularCurve.HahnSpecialise.resH_apply ModularCurve.HahnSpecialise.liftModel_map_subtype ModularCurve.HahnSpecialise.specialise_zero WeierstrassCurve.reducePoint_zero WeierstrassCurve.Affine.Point.galoisRep_apply HahnSeries.ramScale_apply AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none WeierstrassCurve.veluPointMap2_zero AlgebraicCurve.mulAdele_apply AlgebraicCurve.residuePairing_apply_coe AlgebraicCurve.mem_adeleBdd AlgebraicCurve.weilSmul_one AlgebraicCurve.diagonalHom_apply AlgebraicCurve.weilSmul_apply AlgebraicCurve.adeleSpaceMul_coe AlgebraicCurve.mulAdele_one AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.sizeOf_spec AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.injEq AlgebraicCurve.adeleSingle_coe AlgebraicCurve.kaehlerResidueTermKFam_apply AlgebraicCurve.Place.LocalResidueData.mk.injEq AlgebraicCurve.Place.LocalResidueData.mk.sizeOf_spec AlgebraicCurve.Place.kw_ffgc_adicCompletionComapIntegers_coe AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.sizeOf_spec AlgebraicCurve.Place.mem_simplePoleSubmodule"
p2m_attr_erase "simp" "AlgebraicCurve.Place.coe_uniformizerSubring ModularCurve.Lg37.Lg37CompletionSection.mk.injEq AlgebraicCurve.Place.CoefficientFieldSection.mk.injEq AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.injEq ModularCurve.Lg37.Lg37CompletionSection.mk.sizeOf_spec AlgebraicCurve.Place.CoefficientFieldSection.mk.sizeOf_spec AlgebraicCurve.Place.poleSubmodule_one AlgebraicCurve.Place.mem_poleSubmodule ModularCurve.Period.jConjMat_apply_zero_one ModularCurve.Period.jConjSL_coe ModularCurve.Period.jConjMat_apply_one_zero ModularCurve.Period.jConjMat_apply_one_one ModularCurve.Period.jConjGamma0_coe ModularCurve.Period.charInvolution_apply ModularCurve.Period.jConjMat_apply_zero_zero HeckeEis.heckeConjMat_apply_one_one HeckeEis.coe_heckeConjSL HeckeEis.mem_heckeUpperSL HeckeEis.resHom_apply HeckeEis.heckeConjMat_apply_zero_one HeckeEis.coe_transferAux HeckeEis.coe_heckeConj HeckeEis.alphaMat_apply_one_one HeckeEis.heckeConjMat_apply_one_zero HeckeEis.alphaMat_apply_zero_one HeckeEis.pullbackHom_apply HeckeEis.alphaMat_apply_one_zero HeckeEis.alphaMat_apply_zero_zero HeckeEis.heckeConjMat_apply_zero_zero AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.injEq AlgebraicCurve.TranscendenceTower.mk.injEq AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec AlgebraicCurve.PoleDivisorPackage.mk.injEq ModularCurve.ComplexPlaceDictionary.mk.injEq ModularCurve.ComplexPlaceDictionary.mk.sizeOf_spec FLT.TruncatedDomainPartition.unipotentDiagonalSum_zero HeckeEis.coeffCoboundaryMap_apply AlgebraicCurve.DivisorialWeilPairingData.toChar_apply"
p2m_attr_erase "simp" "AlgebraicCurve.WeilDatum.coe_classRight AlgebraicCurve.WeilDatum.coe_degZeroRight AlgebraicCurve.DivisorialWeilPairingData.mk.sizeOf_spec AlgebraicCurve.WeilDatum.coe_classLeft AlgebraicCurve.WeilDatum.coe_degZeroLeft AlgebraicCurve.DivisorialWeilPairingData.mk.injEq AlgebraicCurve.DivisorialWeilPairingData.toHom_apply_apply AlgebraicCurve.WeilDatum.mk.sizeOf_spec AlgebraicCurve.WeilDatum.mk.injEq AlgebraicCurve.WeilPairingData.evalAddChar_zero AlgebraicCurve.PrincipalPolarization.mk.injEq AlgebraicCurve.WeilPairingData.evalAddChar_apply AlgebraicCurve.H1Gm.degree_ofPic0 AlgebraicCurve.WeilPairingData.mk.sizeOf_spec AlgebraicCurve.HomPic0Gm.map_one AlgebraicCurve.PrincipalPolarization.mk.sizeOf_spec AlgebraicCurve.WeilPairingData.autodualityEquiv_apply AlgebraicCurve.WeilPairingData.eval_zero_right AlgebraicCurve.H1Gm.ofPic0_mk AlgebraicCurve.WeilPairingData.eval_neg_left AlgebraicCurve.HomPic0Gm.map_apply AlgebraicCurve.H1Gm.degree_mk AlgebraicCurve.HomPic0Gm.map_id AlgebraicCurve.WeilPairingData.mk.injEq AlgebraicCurve.WeilPairingData.congr_eval AlgebraicCurve.WeilPairingData.eval_neg_right AlgebraicCurve.WeilPairingData.eval_zero_left AlgebraicCurve.ConstantReduction.toRegularProlongation_residue AlgebraicCurve.RegularProlongation.mk.sizeOf_spec AlgebraicCurve.ConstantReduction.toRegularProlongation_integers AlgebraicCurve.RegularProlongation.mk.injEq AlgebraicCurve.ConstantReduction.mk.injEq AlgebraicCurve.ConstantReduction.mk.sizeOf_spec AlgebraicCurve.ConstantReduction.divMap_apply AlgebraicCurve.ConstantReduction.coe_degZeroMap ModularCurve.tateMap_apply AlgebraicCurve.abelJacobiDiv_single AlgebraicCurve.AnalyticCoord.mk.injEq AlgebraicCurve.Cell.mk.sizeOf_spec AlgebraicCurve.RadialRegion.mk.sizeOf_spec"
p2m_attr_erase "simp" "AlgebraicCurve.RadialRegion.mk.injEq AlgebraicCurve.CellDissection.mk.sizeOf_spec AlgebraicCurve.Cell.mk.injEq AlgebraicCurve.CellDissection.mk.injEq AlgebraicCurve.AnalyticCoord.mk.sizeOf_spec ModularCurve.reductionDivAlong_apply ModularCurve.coe_reductionDegZeroAlong ModularCurve.qExpandAlgHomC_apply ModularCurve.coe_frobeniusModL ModularCurve.coe_frobeniusDegZeroPullbackModL ModularCurve.coe_frobeniusDegZeroPushforwardModL ValuationSubring.reduceAt_coe ValuationSubring.reduceAt_one ValuationSubring.reduceAt_natCast ValuationSubring.reduceAt_intCast ValuationSubring.reduceAt_zero ModularCurve.coe_uniformizerMod ModularCurve.qSeriesBar_jModElt ModularCurve.qInftyPlaceMod_toValuationSubring WeierstrassCurve.twoVeluCurve_a₁ WeierstrassCurve.twoVeluCurve_a₂ WeierstrassCurve.twoVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₂ WeierstrassCurve.xVeluCurve_a₁ WeierstrassCurve.map_veluU WeierstrassCurve.map_veluT WeierstrassCurve.map_veluW WeierstrassCurve.map_veluGy WeierstrassCurve.map_veluGx WeierstrassCurve.map_veluWSum_singleton WeierstrassCurve.map_veluTSum_singleton WeierstrassCurve.veluPointMap3_zero WeierstrassCurve.vcInvEmbedding_apply WeierstrassCurve.Affine.Point.netCol_one WeierstrassCurve.Affine.Point.xOrZero_zero WeierstrassCurve.Affine.Point.netPairing_zero_right WeierstrassCurve.Affine.Point.netW20_some WeierstrassCurve.Affine.Point.netCol_zero WeierstrassCurve.Affine.Point.netPairing_zero_left"
p2m_attr_erase "simp" "WeierstrassCurve.Affine.Point.xOrZero_some WeierstrassCurve.Affine.Point.netW20_zero TateCurve.cauchyMulInt_zero TateCurve.cauchyMulInt3_zero TateCurve.tent_one TateCurve.Gz_zero TateCurve.cauchyMulInt_one TateCurve.tent_zero TateCurve.Fz_zero TateCurve.xCoeffFull_succ TateCurve.a₆Coeff_zero TateCurve.a₄Coeff_succ TateCurve.a₄Coeff_zero TateCurve.cauchyMul_zero TateCurve.a₆Coeff_succ TateCurve.yCoeffFull_succ TateCurve.xCoeffFull_zero TateCurve.yCoeffFull_zero TateCurve.yfun_zero TateCurve.xfun_zero TateCurve.yTerm_zero TateCurve.xTerm_zero TateCurve.curve_a₂ TateCurve.b_one TateCurve.curve_a₁ TateCurve.term_zero TateCurve.curve_a₆ TateCurve.curve_a₄ TateCurve.curve_a₃ FLT.DivisorConvolution.sigma_zero_right FLT.DivisorConvolution.sigma_one_right FLT.DivisorConvolution.sigmaConv_one FLT.DivisorConvolution.sigmaConv_zero FormalCoordinates.mk.injEq WeierstrassCurve.formalParam_zero WeierstrassCurve.SmoothLocusReductionData.reduceHom₀_apply WeierstrassCurve.formalParam_some FormalCoordinates.mk.sizeOf_spec WeierstrassCurve.SmoothLocusReductionData.mk.injEq WeierstrassCurve.reducePointSmooth_zero"
p2m_attr_erase "simp" "WeierstrassCurve.SmoothLocusReductionData.mk.sizeOf_spec WeierstrassCurve.mem_zeroComponentSubgroup_iff HeckeEis.binaryFormEval_mk HeckeEis.binaryFormAlphaAdj_apply_coe HeckeEis.binaryFormRepSL_apply_coe ModularCurve.ProjectiveLine.vecMulRow_snd HeckeEis.projLineRepSL_apply HeckeEis.projLineAct_one HeckeEis.projLineRep_apply HeckeEis.projLineAlphaAdj_apply ModularCurve.ProjectiveLine.vecMulRow_fst ModularCurve.ProjectiveLine.vecMul_mk HeckeEis.binaryFormRep_apply_coe HeckeEis.coe_linePow HeckeEis.gamma0NebenRep_apply CohCarrier.conjUpperMat_apply_11 CohCarrier.conjUpperMat_apply_10 CohCarrier.mem_Gamma0Upper CohCarrier.val_gamma0Units CohCarrier.Gen.dia.sizeOf_spec CohCarrier.Gen.U.injEq CohCarrier.Gen.T.sizeOf_spec CohCarrier.Gen.U.sizeOf_spec CohCarrier.Gen.T.injEq CohCarrier.Gen.dia.injEq CohCarrier.HeckeData.mk.sizeOf_spec CohCarrier.HeckeData.opAlgHom_X CohCarrier.HeckeData.toMLₒ_apply CohCarrier.HeckeData.mk.injEq CohCarrier.uMat_apply_10 CohCarrier.rightQuotEquivOfDvd_apply CohCarrier.uMat_apply_11 CohCarrier.uMat_apply_01 CohCarrier.uMat_apply_00 CohCarrier.coe_uElt ModularCurve.symPoly_zero"

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option synthInstance.maxHeartbeats 800000

open CuspForm Polynomial
open scoped MatrixGroups

namespace DeligneModM

abbrev Γℚ : Type := AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ

abbrev Zbar : Type := integralClosure ℤ ℂ

section LowWeight

theorem cuspForm_eq_zero_of_odd (N : ℕ) (k : ℤ) (hk : Odd k)
    (f : CuspForm (CongruenceSubgroup.Gamma0 N) k) : f = 0 := by
  apply DFunLike.ext
  intro z
  have hmem : (-1 : SL(2, ℤ)) ∈ CongruenceSubgroup.Gamma0 N := by
    simp [CongruenceSubgroup.Gamma0_mem]
  have hf := SlashInvariantForm.slash_action_eqn_SL'' f hmem z
  have h1 : ((-1 : SL(2, ℤ)) : GL (Fin 2) ℝ) = -1 := by
    ext i j; fin_cases i <;> fin_cases j <;> simp
  have hz : (-1 : SL(2, ℤ)) • z = z := by
    rw [show (-1 : SL(2, ℤ)) = -(1 : SL(2, ℤ)) from rfl, ModularGroup.SL_neg_smul, one_smul]
  rw [hz, UpperHalfPlane.denom, h1] at hf
  simp at hf
  rw [hk.neg_one_zpow] at hf
  have h2 : (2 : ℂ) * f z = 0 := by linear_combination hf
  simpa using h2

theorem cuspForm_eq_zero_of_nonpos (N : ℕ) [NeZero N] (k : ℤ) (hk : k ≤ 0)
    (f : CuspForm (CongruenceSubgroup.Gamma0 N) k) : f = 0 := by
  rcases hk.lt_or_eq with hlt | rfl
  · have h := ModularForm.isZero_of_neg_weight hlt
      (f : ModularForm (CongruenceSubgroup.Gamma0 N) k)
    apply DFunLike.ext
    intro z
    have := congrArg (fun g : ModularForm (CongruenceSubgroup.Gamma0 N) k => g z) h
    simpa using this
  · obtain ⟨c, hc⟩ :=
      ModularForm.eq_const_of_weight_zero (f : ModularForm (CongruenceSubgroup.Gamma0 N) 0)
    have hzero : UpperHalfPlane.IsZeroAtImInfty (f : UpperHalfPlane → ℂ) :=
      CuspFormClass.zero_at_infty f
    have hfc : (f : UpperHalfPlane → ℂ) = Function.const UpperHalfPlane c := by
      ext z; have := congrFun hc z; simpa using this
    have hc0 : c = 0 := by
      rw [hfc] at hzero
      have h' : Filter.Tendsto (fun _ : UpperHalfPlane => c) UpperHalfPlane.atImInfty (nhds 0) :=
        hzero
      exact tendsto_nhds_unique tendsto_const_nhds h'
    apply DFunLike.ext
    intro z
    have := congrFun hfc z
    simpa [hc0] using this

theorem not_isMaximal_of_subsingleton (N : ℕ) [NeZero N] (k : ℤ) (S : Set ℕ)
    [Subsingleton (CuspForm (CongruenceSubgroup.Gamma0 N) k)]
    (𝔪 : Ideal (heckeAlgebra N k S)) : ¬ 𝔪.IsMaximal := by
  intro h𝔪
  have h1 : (1 : heckeAlgebra N k S) = 0 := Subtype.ext (Subsingleton.elim _ _)
  apply h𝔪.ne_top
  rw [Ideal.eq_top_iff_one, h1]
  exact 𝔪.zero_mem

theorem two_eq_or_three_le_of_isMaximal (N : ℕ) [NeZero N] (k : ℤ) (S : Set ℕ)
    (𝔪 : Ideal (heckeAlgebra N k S)) (h𝔪 : 𝔪.IsMaximal) : k = 2 ∨ 3 ≤ k := by
  by_cases h2 : k = 2
  · exact Or.inl h2
  by_cases h3 : 3 ≤ k
  · exact Or.inr h3
  exfalso
  have hk : k ≤ 0 ∨ Odd k := by
    rcases le_or_gt k 0 with h | h
    · exact Or.inl h
    · right
      have hk12 : k = 1 := by omega
      exact hk12 ▸ odd_one
  haveI : Subsingleton (CuspForm (CongruenceSubgroup.Gamma0 N) k) := by
    refine ⟨fun f g => ?_⟩
    rcases hk with h | h
    · rw [cuspForm_eq_zero_of_nonpos N k h f, cuspForm_eq_zero_of_nonpos N k h g]
    · rw [cuspForm_eq_zero_of_odd N k h f, cuspForm_eq_zero_of_odd N k h g]
  exact not_isMaximal_of_subsingleton N k S 𝔪 h𝔪

end LowWeight

section CutDown

variable {G : Type*} [Group G] {K : Type*} [Field K] {F : Type*} [Field F] [Algebra F K]
  (E : IntermediateField F K) (M : G →* Matrix (Fin 2) (Fin 2) K)
  (hM : ∀ g i j, M g i j ∈ E)

def cutFun (g : G) : Matrix (Fin 2) (Fin 2) E := Matrix.of fun i j => ⟨M g i j, hM g i j⟩

theorem map_cutFun (g : G) : (cutFun E M hM g).map (algebraMap E K) = M g := by
  ext i j; rfl

theorem mapMatrix_injective :
    Function.Injective ((algebraMap E K).mapMatrix : Matrix (Fin 2) (Fin 2) E →+* _) :=
  fun A B h => Matrix.map_injective (algebraMap E K).injective h

def cut : G →* Matrix (Fin 2) (Fin 2) E where
  toFun := cutFun E M hM
  map_one' := by
    apply mapMatrix_injective E
    rw [RingHom.mapMatrix_apply, map_cutFun, map_one, map_one]
  map_mul' g h := by
    apply mapMatrix_injective E
    rw [RingHom.mapMatrix_apply, map_cutFun, map_mul, map_mul, RingHom.mapMatrix_apply,
      RingHom.mapMatrix_apply, map_cutFun, map_cutFun]

theorem map_cut (g : G) : (cut E M hM g).map (algebraMap E K) = M g := map_cutFun E M hM g

theorem cut_eq_one_of {g : G} (hg : M g = 1) : cut E M hM g = 1 := by
  apply mapMatrix_injective E
  rw [RingHom.mapMatrix_apply, map_cut, hg, map_one]

end CutDown

section FiniteImage

variable {X : Type*} [Monoid X] (M : Γℚ →* X)

theorem finite_range_of_factorsThroughFiniteLevel
    (L' : IntermediateField ℚ (AlgebraicClosure ℚ)) [FiniteDimensional ℚ L']
    (hker : ∀ σ : Γℚ, (∀ x ∈ L', σ x = x) → M σ = 1) : (Set.range M).Finite := by
  classical
  let res : Γℚ → (L' →ₐ[ℚ] AlgebraicClosure ℚ) :=
    fun σ => (σ : AlgebraicClosure ℚ →ₐ[ℚ] AlgebraicClosure ℚ).comp L'.val
  have hres : ∀ σ τ : Γℚ, res σ = res τ → M σ = M τ := by
    intro σ τ h
    have hfix : ∀ x ∈ L', (τ⁻¹ * σ) x = x := by
      intro x hx
      have hx' : σ x = τ x := by
        have := congrArg (fun f : L' →ₐ[ℚ] AlgebraicClosure ℚ => f ⟨x, hx⟩) h
        simp [res] at this
        exact this
      rw [AlgEquiv.mul_apply, hx', AlgEquiv.aut_inv, AlgEquiv.symm_apply_apply]
    have h1 : M (τ⁻¹ * σ) = 1 := hker _ hfix
    calc M σ = M (τ * (τ⁻¹ * σ)) := by rw [mul_inv_cancel_left]
      _ = M τ := by rw [map_mul, h1, mul_one]
  let g : (L' →ₐ[ℚ] AlgebraicClosure ℚ) → X :=
    fun y => if h : ∃ σ, res σ = y then M h.choose else 1
  refine (Set.finite_range g).subset ?_
  rintro _ ⟨σ, rfl⟩
  refine ⟨res σ, ?_⟩
  have h : ∃ σ', res σ' = res σ := ⟨σ, rfl⟩
  simp only [g, dif_pos h]
  exact hres _ _ h.choose_spec

end FiniteImage

section Descent

variable (p : ℕ) [Fact p.Prime] {κ : Type} [Field κ] [Algebra (ZMod p) κ]
  {T : Type} [CommRing T]

theorem descend (halg : ∀ x : κ, IsIntegral (ZMod p) x)
    (𝔪 : Ideal T) [Finite (T ⧸ 𝔪)] (j₀ : T ⧸ 𝔪 →+* κ)
    (ρκ : Γℚ →* GL (Fin 2) κ) (hfin : GaloisFactorsThroughFiniteLevel ρκ) :
    ∃ (L : IntermediateField (ZMod p) κ) (_ : Finite L) (jL : T ⧸ 𝔪 →+* L)
      (ρL : Γℚ →* GL (Fin 2) L),
      GaloisFactorsThroughFiniteLevel ρL ∧
      (∀ x, algebraMap L κ (jL x) = j₀ x) ∧
      (∀ σ, (ρκ σ).val = (ρL σ).val.map (algebraMap L κ)) ∧
      (∀ σ, ρκ σ = 1 → ρL σ = 1) := by
  classical
  let M : Γℚ →* Matrix (Fin 2) (Fin 2) κ := (Units.coeHom _).comp ρκ
  have hM : ∀ σ, M σ = (ρκ σ).val := fun σ => rfl
  obtain ⟨L', hL'fd, hker⟩ := hfin
  haveI := hL'fd
  have hkerM : ∀ σ : Γℚ, (∀ x ∈ L', σ x = x) → M σ = 1 := by
    intro σ hσ; rw [hM, hker σ hσ, Units.val_one]
  have hfinM : (Set.range M).Finite := finite_range_of_factorsThroughFiniteLevel M L' hkerM
  let E₁ : Set κ :=
    (fun q : Matrix (Fin 2) (Fin 2) κ × (Fin 2 × Fin 2) => q.1 q.2.1 q.2.2) ''
      (Set.range M ×ˢ Set.univ)
  let E : Set κ := E₁ ∪ Set.range j₀
  have hE : E.Finite :=
    ((hfinM.prod Set.finite_univ).image _).union (Set.finite_range j₀)
  haveI : Finite E := hE.to_subtype
  let K' : IntermediateField (ZMod p) κ := IntermediateField.adjoin (ZMod p) E
  haveI : FiniteDimensional (ZMod p) K' :=
    IntermediateField.finiteDimensional_adjoin fun x _ => halg x
  haveI : Finite K' := Module.finite_of_finite (ZMod p)
  have hME : ∀ σ i j, M σ i j ∈ K' := fun σ i j =>
    IntermediateField.subset_adjoin _ _ (Or.inl ⟨⟨M σ, (i, j)⟩, ⟨⟨σ, rfl⟩, Set.mem_univ _⟩, rfl⟩)
  have hjE : ∀ x, j₀ x ∈ K' := fun x => IntermediateField.subset_adjoin _ _ (Or.inr ⟨x, rfl⟩)
  let ρL : Γℚ →* GL (Fin 2) K' := (cut K' M hME).toHomUnits
  have hρL : ∀ σ, (ρL σ).val = cut K' M hME σ := fun σ => rfl
  let jL : T ⧸ 𝔪 →+* K' := j₀.codRestrict K' hjE
  refine ⟨K', inferInstance, jL, ρL, ?_, fun x => rfl, ?_, ?_⟩
  · refine ⟨L', hL'fd, fun σ hσ => Units.ext ?_⟩
    rw [hρL, Units.val_one]
    exact cut_eq_one_of K' M hME (hkerM σ hσ)
  · intro σ
    rw [hρL, map_cut, hM]
  · intro σ hσ
    apply Units.ext
    rw [hρL, Units.val_one]
    exact cut_eq_one_of K' M hME (by rw [hM, hσ, Units.val_one])

end Descent

section Residue

theorem isIntegral_zmod_of_quotient (p : ℕ) {k₀ : Type} [Field k₀] [CharP k₀ p]
    [Algebra (ZMod p) k₀] (φ : Zbar →+* k₀) (hφ : Function.Surjective φ) (x : k₀) :
    IsIntegral (ZMod p) x := by
  obtain ⟨a, rfl⟩ := hφ x
  obtain ⟨f, hfm, hf⟩ := integralClosure.isIntegral a
  refine ⟨f.map (algebraMap ℤ (ZMod p)), hfm.map _, ?_⟩
  rw [eval₂_map, RingHom.ext_int ((algebraMap (ZMod p) k₀).comp (algebraMap ℤ (ZMod p)))
    (φ.comp (algebraMap ℤ Zbar)), ← hom_eval₂, hf, map_zero]

theorem finite_quotient_of_natCast_mem {T : Type*} [CommRing T] [Module.Finite ℤ T]
    {p : ℕ} (hp : p ≠ 0) (𝔪 : Ideal T) (hp𝔪 : ((p : ℕ) : T) ∈ 𝔪) : Finite (T ⧸ 𝔪) := by
  have hsurj : Function.Surjective
      ((Ideal.Quotient.mk 𝔪 : T →+* T ⧸ 𝔪).toIntAlgHom.toLinearMap) :=
    Ideal.Quotient.mk_surjective
  haveI : Module.Finite ℤ (T ⧸ 𝔪) := Module.Finite.of_surjective _ hsurj
  refine Module.finite_of_fg_torsion (T ⧸ 𝔪) ?_
  have hp0 : ((p : ℕ) : T ⧸ 𝔪) = 0 := by
    rw [← map_natCast (Ideal.Quotient.mk 𝔪), Ideal.Quotient.eq_zero_iff_mem]; exact hp𝔪
  intro x
  refine ⟨⟨(p : ℤ), mem_nonZeroDivisors_of_ne_zero (by exact_mod_cast hp)⟩, ?_⟩
  change (p : ℤ) • x = 0
  rw [zsmul_eq_mul, Int.cast_natCast, hp0, zero_mul]

end Residue

section HigherWeight

variable (p : ℕ) [Fact p.Prime] (N : ℕ) [NeZero N] (S : Set ℕ)

set_option maxHeartbeats 4000000 in

theorem main_of_three_le (k : ℤ) (hk3 : 3 ≤ k) (kn : ℕ) (hkn : (kn : ℤ) = k)
    (𝔪 : Ideal (heckeAlgebra N k S)) (h𝔪 : 𝔪.IsMaximal)
    (hp𝔪 : ((p : ℕ) : heckeAlgebra N k S) ∈ 𝔪) :
    ∃ (L : Type) (_ : Field L) (_ : Finite L) (j : heckeAlgebra N k S ⧸ 𝔪 →+* L)
      (ρ : Γℚ →* GL (Fin 2) L),
      GaloisFactorsThroughFiniteLevel ρ ∧
      (∀ (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓN : ¬ ℓ ∣ N) (hℓS : ℓ ∉ S), ℓ ≠ p →
        ∀ A : ValuationSubring (AlgebraicClosure ℚ), A.LiesOverPrime ℓ →
          ∀ σ : Γℚ, A.IsFrobeniusAt σ ℓ →
            Matrix.trace (ρ σ).val = j (Ideal.Quotient.mk 𝔪 (heckeAlgebra.T hℓ hℓN hℓS))) ∧
      (∀ ℓ : ℕ, ℓ.Prime → ¬ ℓ ∣ N → ℓ ≠ p →
        ∀ A : ValuationSubring (AlgebraicClosure ℚ), A.LiesOverPrime ℓ →
          ∀ σ : Γℚ, A.IsFrobeniusAt σ ℓ →
            Matrix.det (ρ σ).val = (ℓ : L) ^ (kn - 1)) ∧
      (∀ ℓ : ℕ, ℓ.Prime → ¬ ℓ ∣ N → ℓ ≠ p →
        ∀ A : ValuationSubring (AlgebraicClosure ℚ), A.LiesOverPrime ℓ →
          ∀ σ ∈ A.inertiaSubgroupIn ℚ, ρ σ = 1) := by
  classical
  have hp : p.Prime := Fact.out

  haveI : Module.Finite ℤ (heckeAlgebra N k S) := CuspForm.moduleFinite_heckeAlgebra N k S
  haveI : FiniteDimensional ℂ (CuspForm (CongruenceSubgroup.Gamma0 N) k) :=
    CuspForm.finiteDimensional_Gamma0 N k
  haveI : SMulCommClass (heckeAlgebra N k S) ℂ (CuspForm (CongruenceSubgroup.Gamma0 N) k) :=
    ⟨fun t c v => (t : Module.End ℂ (CuspForm (CongruenceSubgroup.Gamma0 N) k)).map_smul c v⟩
  haveI := h𝔪
  have hsupp : Module.annihilator (heckeAlgebra N k S) (CuspForm (CongruenceSubgroup.Gamma0 N) k)
      ≤ 𝔪 := by
    intro t ht
    rw [Module.mem_annihilator] at ht
    have : t = 0 := by
      apply Subtype.ext
      exact LinearMap.ext fun v => ht v
    rw [this]; exact 𝔪.zero_mem
  obtain ⟨χ, 𝔐, h𝔐, hcomap, f, hf0, hf⟩ :=
    DeligneSerre.exists_eigencharacter_of_annihilator_le
      (V := CuspForm (CongruenceSubgroup.Gamma0 N) k) (T := heckeAlgebra N k S) 𝔪 hsupp
  have hχ : ∀ t : heckeAlgebra N k S,
      (t : Module.End ℂ (CuspForm (CongruenceSubgroup.Gamma0 N) k)) f =
        ((χ t : Zbar) : ℂ) • f := fun t => hf t

  letI : Field (Zbar ⧸ 𝔐) := Ideal.Quotient.field 𝔐
  let φ : Zbar →+* Zbar ⧸ 𝔐 := Ideal.Quotient.mk 𝔐
  have hmem : ∀ t : heckeAlgebra N k S, χ t ∈ 𝔐 ↔ t ∈ 𝔪 := by
    intro t; rw [← hcomap, Ideal.mem_comap]
  have hp𝔐 : ((p : ℕ) : Zbar) ∈ 𝔐 := by
    have := (hmem _).2 hp𝔪
    rwa [map_natCast] at this
  have hp0 : ((p : ℕ) : Zbar ⧸ 𝔐) = 0 := by
    rw [← map_natCast φ, Ideal.Quotient.eq_zero_iff_mem]; exact hp𝔐
  haveI : CharP (Zbar ⧸ 𝔐) p := (CharP.charP_iff_prime_eq_zero hp).mpr hp0
  letI : Algebra (ZMod p) (Zbar ⧸ 𝔐) := ZMod.algebra _ p

  obtain ⟨ρκ, hfinκ, htrκ, hdetκ, hunrκ⟩ :=
    GaloisRep.exists_galoisRep_trace_eq_eigenchar_and_det_eq_pow_of_three_le
      p N S k hk3 kn hkn f hf0 χ hχ φ

  haveI : Finite (heckeAlgebra N k S ⧸ 𝔪) := finite_quotient_of_natCast_mem hp.ne_zero 𝔪 hp𝔪
  let j₀ : heckeAlgebra N k S ⧸ 𝔪 →+* Zbar ⧸ 𝔐 :=
    Ideal.Quotient.lift 𝔪 (φ.comp χ) fun t ht =>
      Ideal.Quotient.eq_zero_iff_mem.mpr ((hmem t).2 ht)
  have hj₀ : ∀ t, j₀ (Ideal.Quotient.mk 𝔪 t) = φ (χ t) := fun t => Ideal.Quotient.lift_mk _ _ _
  obtain ⟨L, _instL, jL, ρL, hfinL, hjL, hcut, hone⟩ :=
    descend p (isIntegral_zmod_of_quotient p φ Ideal.Quotient.mk_surjective) 𝔪 j₀ ρκ hfinκ
  have hinj : Function.Injective (algebraMap L (Zbar ⧸ 𝔐)) := (algebraMap L (Zbar ⧸ 𝔐)).injective
  refine ⟨L, inferInstance, inferInstance, jL, ρL, hfinL, ?_, ?_, ?_⟩
  · intro ℓ hℓ hℓN hℓS hℓp A hA σ hσ
    apply hinj
    rw [AddMonoidHom.map_trace (algebraMap L (Zbar ⧸ 𝔐) : L →+* _), ← RingHom.mapMatrix_apply,
      RingHom.mapMatrix_apply, ← hcut, htrκ ℓ hℓ hℓN hℓS hℓp A hA σ hσ, hjL, hj₀]
  · intro ℓ hℓ hℓN hℓp A hA σ hσ
    apply hinj
    rw [RingHom.map_det, RingHom.mapMatrix_apply, ← hcut, hdetκ ℓ hℓ hℓN hℓp A hA σ hσ,
      map_pow, map_natCast]
  · intro ℓ hℓ hℓN hℓp A hA σ hσ
    exact hone σ (hunrκ ℓ hℓ hℓN hℓp A hA σ hσ)

end HigherWeight

end DeligneModM

theorem solution
    (p : ℕ) [Fact p.Prime] (N : ℕ) [NeZero N] (hpN : ¬ p ∣ N)
    (S : Set ℕ) (hSfin : S.Finite)
    (k : ℤ) (kn : ℕ) (hkn : (kn : ℤ) = k)
    (𝔪 : Ideal (heckeAlgebra N k S)) (h𝔪 : 𝔪.IsMaximal)
    (hp𝔪 : ((p : ℕ) : heckeAlgebra N k S) ∈ 𝔪) :
    ∃ (L : Type) (_ : Field L) (_ : Finite L) (j : heckeAlgebra N k S ⧸ 𝔪 →+* L)
      (ρ : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) →* GL (Fin 2) L),
      GaloisFactorsThroughFiniteLevel ρ ∧
      (∀ (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓN : ¬ ℓ ∣ N) (hℓS : ℓ ∉ S), ℓ ≠ p →
        ∀ A : ValuationSubring (AlgebraicClosure ℚ), A.LiesOverPrime ℓ →
          ∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, A.IsFrobeniusAt σ ℓ →
            Matrix.trace (ρ σ).val =
              j (Ideal.Quotient.mk 𝔪 (heckeAlgebra.T hℓ hℓN hℓS))) ∧
      (∀ ℓ : ℕ, ℓ.Prime → ¬ ℓ ∣ N → ℓ ∉ S → ℓ ≠ p →
        ∀ A : ValuationSubring (AlgebraicClosure ℚ), A.LiesOverPrime ℓ →
          ∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, A.IsFrobeniusAt σ ℓ →
            Matrix.det (ρ σ).val = (ℓ : L) ^ (kn - 1)) := by
  rcases DeligneModM.two_eq_or_three_le_of_isMaximal N k S 𝔪 h𝔪 with h2 | h3
  ·
    subst h2
    have hkn2 : kn = 2 := by exact_mod_cast hkn
    subst hkn2
    obtain ⟨L, iF, iFin, j, ρ, hfin, htr, hdet, -⟩ :=
      GaloisRep.exists_finiteField_galoisRep_trace_eq_heckeT_mod_of_isMaximal_two p N S 𝔪 h𝔪 hp𝔪
    refine ⟨L, iF, iFin, j, ρ, hfin, htr, ?_⟩
    intro ℓ hℓ hℓN hℓS hℓp A hA σ hσ
    rw [hdet ℓ hℓ hℓN hℓp A hA σ hσ, pow_one]
  ·
    obtain ⟨L, iF, iFin, j, ρ, hfin, htr, hdet, -⟩ :=
      DeligneModM.main_of_three_le p N S k h3 kn hkn 𝔪 h𝔪 hp𝔪
    exact ⟨L, iF, iFin, j, ρ, hfin, htr,
      fun ℓ hℓ hℓN hℓS hℓp A hA σ hσ => hdet ℓ hℓ hℓN hℓp A hA σ hσ⟩

end S_GaloisRep_exists_finiteField_galoisRep_trace_eq_heckeT_mod_of_isMaximal
end P2MW
export P2MW.S_GaloisRep_exists_finiteField_galoisRep_trace_eq_heckeT_mod_of_isMaximal (solution)
