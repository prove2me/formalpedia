-- Prove2me | solution 1 for GaloisRep.exists_finiteField_galoisRep_trace_eq_heckeT_mod_of_isMaximal_two
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.331093+00:00
-- url     : https://prove2.me/submissions/20fd6603-ffb3-56c9-bf34-b7e21f40f1e1

import Mathlib
import Definitions.Def_CuspForm_HeckeAlgebra
import Definitions.Def_GaloisRep_Residual
import Definitions.Def_FLTPrelim_Modularity
import Theorems.Thm_CuspForm_exists_isNormalizedEigenform_of_isMaximal_heckeAlgebra
import Theorems.Thm_CuspForm_IsNormalizedEigenform_exists_residualGaloisRep_isAttachedTo
import Theorems.Thm_CuspForm_IsNormalizedEigenform_exists_ringHom_heckeAlgebra
import Theorems.Thm_CuspForm_moduleFinite_heckeAlgebra_two
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_GaloisRep_exists_finiteField_galoisRep_trace_eq_heckeT_mod_of_isMaximal_two
p2m_attr_erase "instance" "GaloisRepAdic.instAddCommGroup GaloisRepAdic.instFree GaloisRepAdic.instFinite GaloisRepAdic.instModule ModularCurve.instSMulAlgEquivRatPic0SubtypeLaurentSeriesMemIntermediateFieldLaurentBaseChange ModularCurve.instDistribMulActionAlgEquivRatPic0SubtypeLaurentSeriesMemIntermediateFieldLaurentBaseChange AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupDivisor AlgebraicCurve.Pic0.instModuleZModTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instDistribMulActionTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instSMulTorsion AlgebraicCurve.SemilinearAut.instMulActionSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instSMulCommClassZModTorsion AlgebraicCurve.SemilinearAut.instMulSemiringActionSubtypeProdRingAutMemSubgroup AlgebraicCurve.Place.instIsScalarTowerSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Divisor.instDistribMulActionAlgEquiv AlgebraicCurve.Place.instSMulAlgEquiv AlgebraicCurve.Place.instIsPrincipalIdealRingSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Place.instIsDiscreteValuationRingSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Pic0.instDistribMulActionAlgEquiv AlgebraicCurve.Place.instAlgebraSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Place.instMulActionAlgEquiv AlgebraicCurve.Pic0.instSMulAlgEquiv TateModule.instModule TateModule.instSMul AlgebraicCurve.instFundamentalIdentityOfSumRamificationInertia AlgebraicCurve.Place.instIsScalarTowerResidueFieldRestrictPushforward AlgebraicCurve.Place.instAlgebraResidueFieldRestrictPushforward AlgebraicCurve.Place.instIsLocalHomRestrictInclusion AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue"
p2m_attr_erase "instance" "AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation ModularCurve.PhiGen.instNeZeroPhiGenCosetA ModularCurve.instIsDomainTensorProduct AlgebraicClosure.Rat.isGalois ModularCurve.CuspSpace.instNonempty ModularCurve.CuspSpace.instSubsingletonOfOne ModularCurve.CuspSpace.instFinite ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid ModularCurve.instAlgebraIntermediateFieldLaurent ModularCurve.instIsScalarTowerKaehlerIntermediateFieldLaurent ModularCurve.instIsScalarTowerIntermediateFieldLaurent ModularCurve.instModuleKaehlerIntermediateFieldLaurent ModularCurve.Gamma0Pair.isElliptic ModularCurve.TatePoint.instIsElliptic_nearCurve ModularCurve.instIsElliptic_tateLaurent WeierstrassCurve.Affine.instIsScalarTowerPolynomialRatFuncFunctionField_definitions WeierstrassCurve.Affine.instAlgebraRatFuncFunctionField_definitions WeierstrassCurve.Affine.instIsScalarTowerRatFuncFunctionField_definitions WeierstrassCurve.Affine.CoordinateRing.moduleFinite WeierstrassCurve.Affine.instDecidableEqFunctionField WeierstrassCurve.Affine.CoordinateRing.isIntegral WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly ModularCurve.B3.instIsElliptic_goodModel AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions ModularCurve.instAlgebraJLineBar ModularCurve.instModuleJLineBar AlgebraicCurve.instHasLocalResidue_of_hasCanonicalLocalResidueK AlgebraicCurve.instHasCanonicalLocalResidueK_of_hasCanonicalLocalResidueKStar AlgebraicCurve.Place.kw_ffgc_finiteDimensional_adicCompletion instAlgebraSubtypeMemValuationSubring_definitions AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersIntegersCompletion ModularCurve.KwF4gRRTate.instAlgebraKAdicCompletionIntegers AlgebraicCurve.Place.kw_ffgc_continuousSMul_adicCompletionComap AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersCompletionCompletion IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions"
p2m_attr_erase "instance" "IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions AlgebraicCurve.instHasCanonicalLocalResidueK AlgebraicCurve.Place.instAlgebra_restrictResidueField AlgebraicCurve.Place.instIsScalarTower_restrictResidueField AlgebraicCurve.instHasLocalResidue AlgebraicCurve.HasSeparableResidue.of_perfectField_of_isCurveOver AlgebraicCurve.HasSeparableResidue.of_perfectField AlgebraicCurve.Place.instIsLocalHom_restrictSubringHom AlgebraicCurve.instHasCanonicalLocalResidueKStar ModularCurve.KwNo6Pin.isLocalRing_completion ModularCurve.instIsScalarTowerJAdjoin HeckeEis.instFiniteIndexHeckeUpper ModularCurve.Period.parabolicHoms_int_moduleFinite ModularCurve.Period.instGroupFG_SL2Z ModularCurve.Period.instIsNoetherian_addHom_int ModularCurve.Period.instGroupFG_Gamma0 FLT.Gamma0FundamentalSet.instContinuousConstSMulSpecialLinearGroupFinOfNatNatIntUpperHalfPlane_definitions FLT.HyperbolicMeasure.instSMulInvariantMeasureSpecialLinearGroupFinOfNatNatIntUpperHalfPlaneVolume_definitions FLT.HyperbolicMeasure.instIsOpenPosMeasureUpperHalfPlaneVolume_definitions FLT.L2ProductionInstance.isFiniteMeasure_gamma0 FLT.L2ProductionInstance.countable_SL2Z FLT.L2ProductionInstance.countable_quotient FLT.L2ProductionInstance.nontrivial_gamma0L2 HeckeEis.instModuleCoeffH1par HeckeEis.instAddCommGroupCoeffH1par AlgebraicCurve.CellDissection.fintypeV AlgebraicCurve.CellDissection.fintypeC AlgebraicCurve.CellDissection.fintypeE AlgebraicCurve.CellDissection.decEqV AlgebraicCurve.CellDissection.decEqC AlgebraicCurve.CellDissection.decEqE ValuationSubring.instIsAlgClosedResidueField WeierstrassCurve.VeluQuotientJGates.instIsElliptic27a4 ModularCurve.ElevenA1.instDecidableEquation ModularCurve.ElevenA1.instDecidableNonsingular"
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
p2m_attr_erase "simp" "WeierstrassCurve.SmoothLocusReductionData.mk.sizeOf_spec WeierstrassCurve.mem_zeroComponentSubgroup_iff"

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

open CuspForm Polynomial

namespace DeligneModMTwo

abbrev Γℚ : Type := AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ

section Charpoly

variable {K : Type*} [CommRing K]

theorem trace_eq_of_charpoly_eq (M : Matrix (Fin 2) (Fin 2) K) (u v : K)
    (h : M.charpoly = X ^ 2 - C u * X + C v) : M.trace = u := by
  rw [Matrix.trace_eq_neg_charpoly_coeff, h, Fintype.card_fin]
  simp [coeff_C, coeff_X_pow]

theorem det_eq_of_charpoly_eq (M : Matrix (Fin 2) (Fin 2) K) (u v : K)
    (h : M.charpoly = X ^ 2 - C u * X + C v) : M.det = v := by
  rw [Matrix.det_eq_sign_charpoly_coeff, h, Fintype.card_fin]
  simp [coeff_C, coeff_X_pow]

end Charpoly

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

theorem algebraMap_trace_cut (g : G) : algebraMap E K (cut E M hM g).trace = (M g).trace := by
  rw [AddMonoidHom.map_trace (algebraMap E K : E →+* K), map_cut]

theorem algebraMap_det_cut (g : G) : algebraMap E K (cut E M hM g).det = (M g).det := by
  rw [RingHom.map_det, RingHom.mapMatrix_apply, map_cut]

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

section Package

variable (p : ℕ) [Fact p.Prime] {k₀ : Type} [Field k₀] [Algebra (ZMod p) k₀]
  {T : Type} [CommRing T]

theorem package (halg : ∀ x : k₀, IsIntegral (ZMod p) x)
    (𝔪 : Ideal T) [Finite (T ⧸ 𝔪)] (j₀ : T ⧸ 𝔪 →+* k₀)
    (N : ℕ) (S : Set ℕ) (tgen : ∀ ℓ : ℕ, ℓ.Prime → ¬ ℓ ∣ N → ℓ ∉ S → T)
    (ρb : ResidualGaloisRep k₀)
    (hchar : ∀ (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓN : ¬ ℓ ∣ N), ℓ ≠ p →
      ∀ A : ValuationSubring (AlgebraicClosure ℚ), A.LiesOverPrime ℓ →
        ∀ σ : Γℚ, A.IsFrobeniusAt σ ℓ →
          ∃ c : k₀, (ρb.ρ σ).charpoly = X ^ 2 - C c * X + C (ℓ : k₀) ∧
            ∀ hℓS : ℓ ∉ S, c = j₀ (Ideal.Quotient.mk 𝔪 (tgen ℓ hℓ hℓN hℓS)))
    (hunr : ∀ ℓ : ℕ, ℓ.Prime → ¬ ℓ ∣ N → ℓ ≠ p → ρb.IsUnramifiedAt ℓ) :
    ∃ (L : Type) (_ : Field L) (_ : Finite L) (j : T ⧸ 𝔪 →+* L)
      (ρ : Γℚ →* GL (Fin 2) L),
      GaloisFactorsThroughFiniteLevel ρ ∧
      (∀ (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓN : ¬ ℓ ∣ N) (hℓS : ℓ ∉ S), ℓ ≠ p →
        ∀ A : ValuationSubring (AlgebraicClosure ℚ), A.LiesOverPrime ℓ →
          ∀ σ : Γℚ, A.IsFrobeniusAt σ ℓ →
            Matrix.trace (ρ σ).val =
              j (Ideal.Quotient.mk 𝔪 (tgen ℓ hℓ hℓN hℓS))) ∧
      (∀ ℓ : ℕ, ℓ.Prime → ¬ ℓ ∣ N → ℓ ≠ p →
        ∀ A : ValuationSubring (AlgebraicClosure ℚ), A.LiesOverPrime ℓ →
          ∀ σ : Γℚ, A.IsFrobeniusAt σ ℓ → Matrix.det (ρ σ).val = (ℓ : L)) ∧
      (∀ ℓ : ℕ, ℓ.Prime → ¬ ℓ ∣ N → ℓ ≠ p →
        ∀ A : ValuationSubring (AlgebraicClosure ℚ), A.LiesOverPrime ℓ →
          ∀ σ ∈ A.inertiaSubgroupIn ℚ, ρ σ = 1) := by
  classical
  haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩

  let b : Module.Basis (Fin 2) k₀ ρb.V := Module.finBasisOfFinrankEq _ _ ρb.finrank_eq
  let M : Γℚ →* Matrix (Fin 2) (Fin 2) k₀ :=
    { toFun := fun σ => LinearMap.toMatrix b b (ρb.ρ σ)
      map_one' := by rw [map_one, LinearMap.toMatrix_one]
      map_mul' := fun σ τ => by rw [map_mul, LinearMap.toMatrix_mul] }
  have hM : ∀ σ, M σ = LinearMap.toMatrix b b (ρb.ρ σ) := fun σ => rfl

  obtain ⟨L', hL'fd, hker⟩ := ρb.factorsThroughFiniteLevel
  haveI := hL'fd
  have hkerM : ∀ σ : Γℚ, (∀ x ∈ L', σ x = x) → M σ = 1 := by
    intro σ hσ; rw [hM, hker σ hσ, LinearMap.toMatrix_one]
  have hfinM : (Set.range M).Finite := finite_range_of_factorsThroughFiniteLevel M L' hkerM

  let E₁ : Set k₀ :=
    (fun q : Matrix (Fin 2) (Fin 2) k₀ × (Fin 2 × Fin 2) => q.1 q.2.1 q.2.2) ''
      (Set.range M ×ˢ Set.univ)
  let E : Set k₀ := E₁ ∪ Set.range j₀
  have hE : E.Finite :=
    ((hfinM.prod Set.finite_univ).image _).union (Set.finite_range j₀)
  haveI : Finite E := hE.to_subtype
  let K' : IntermediateField (ZMod p) k₀ := IntermediateField.adjoin (ZMod p) E
  haveI : FiniteDimensional (ZMod p) K' :=
    IntermediateField.finiteDimensional_adjoin fun x _ => halg x
  haveI : Finite K' := Module.finite_of_finite (ZMod p)
  have hME : ∀ σ i j, M σ i j ∈ K' := fun σ i j =>
    IntermediateField.subset_adjoin _ _ (Or.inl ⟨⟨M σ, (i, j)⟩, ⟨⟨σ, rfl⟩, Set.mem_univ _⟩, rfl⟩)
  have hjE : ∀ x, j₀ x ∈ K' := fun x => IntermediateField.subset_adjoin _ _ (Or.inr ⟨x, rfl⟩)

  let ρL : Γℚ →* GL (Fin 2) K' := (cut K' M hME).toHomUnits
  have hρL : ∀ σ, (ρL σ).val = cut K' M hME σ := fun σ => rfl
  let jL : T ⧸ 𝔪 →+* K' := j₀.codRestrict K' hjE
  have hjL : ∀ x, algebraMap K' k₀ (jL x) = j₀ x := fun x => rfl
  refine ⟨K', inferInstance, inferInstance, jL, ρL, ?_, ?_, ?_, ?_⟩
  ·
    refine ⟨L', hL'fd, fun σ hσ => Units.ext ?_⟩
    rw [hρL, Units.val_one]
    exact cut_eq_one_of K' M hME (hkerM σ hσ)
  ·
    intro ℓ hℓ hℓN hℓS hℓp A hA σ hσ
    obtain ⟨c, hc, hcj⟩ := hchar ℓ hℓ hℓN hℓp A hA σ hσ
    have hcharM : (M σ).charpoly = X ^ 2 - C c * X + C (ℓ : k₀) := by
      rw [hM, LinearMap.charpoly_toMatrix, hc]
    apply (algebraMap K' k₀).injective
    rw [hρL, algebraMap_trace_cut, trace_eq_of_charpoly_eq _ _ _ hcharM, hjL, hcj hℓS]
  ·
    intro ℓ hℓ hℓN hℓp A hA σ hσ
    obtain ⟨c, hc, -⟩ := hchar ℓ hℓ hℓN hℓp A hA σ hσ
    have hcharM : (M σ).charpoly = X ^ 2 - C c * X + C (ℓ : k₀) := by
      rw [hM, LinearMap.charpoly_toMatrix, hc]
    apply (algebraMap K' k₀).injective
    rw [hρL, algebraMap_det_cut, det_eq_of_charpoly_eq _ _ _ hcharM, map_natCast]
  ·
    intro ℓ hℓ hℓN hℓp A hA σ hσ
    have h1 : ρb.ρ σ = 1 := hunr ℓ hℓ hℓN hℓp A hA σ hσ
    apply Units.ext
    rw [hρL, Units.val_one]
    apply cut_eq_one_of K' M hME
    rw [hM, h1, LinearMap.toMatrix_one]

end Package

section Residue

abbrev Zbar : Type := integralClosure ℤ ℂ

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

section Eigen

variable {N : ℕ} [NeZero N] {S : Set ℕ}

theorem ne_zero_of_isNormalizedEigenform {g : CuspForm (CongruenceSubgroup.Gamma0 N) 2}
    (hg : g.IsNormalizedEigenform) : g ≠ 0 := by
  intro h
  have h1 := hg.qCoeff_one
  have hcoe : (⇑g : UpperHalfPlane → ℂ) = 0 := by rw [h]; rfl
  rw [hcoe, ModularFormClass.qCoeff, UpperHalfPlane.qExpansion_zero, map_zero] at h1
  exact zero_ne_one h1

theorem smul_eigen_unique {g : CuspForm (CongruenceSubgroup.Gamma0 N) 2} (hg0 : g ≠ 0)
    {c d : ℂ} (h : c • g = d • g) : c = d := by
  have h' : (c - d) • g = 0 := by rw [sub_smul, h, sub_self]
  rcases smul_eq_zero.mp h' with h'' | h''
  · exact sub_eq_zero.mp h''
  · exact absurd h'' hg0

theorem exists_eigenchar (𝔪 : Ideal (heckeAlgebra N 2 S)) (h𝔪 : 𝔪.IsMaximal) :
    ∃ (g : CuspForm (CongruenceSubgroup.Gamma0 N) 2) (𝔐 : Ideal Zbar)
      (θ : heckeAlgebra N 2 S →+* Zbar),
      g.IsNormalizedEigenform ∧ 𝔐.IsMaximal ∧
      (∀ t : heckeAlgebra N 2 S, t ∈ 𝔪 → θ t ∈ 𝔐) ∧
      (∀ (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓN : ¬ ℓ ∣ N) (hℓS : ℓ ∉ S),
        (θ (heckeAlgebra.T hℓ hℓN hℓS) : ℂ) = ModularFormClass.qCoeff g ℓ) := by
  obtain ⟨g, 𝔐, hg, h𝔐, H⟩ :=
    CuspForm.exists_isNormalizedEigenform_of_isMaximal_heckeAlgebra N S 𝔪 h𝔪
  obtain ⟨χ, hχ, hχT, -⟩ := hg.exists_ringHom_heckeAlgebra S
  have hg0 := ne_zero_of_isNormalizedEigenform hg

  have hχa : ∀ (t : heckeAlgebra N 2 S) (a : Zbar),
      (t : Module.End ℂ (CuspForm (CongruenceSubgroup.Gamma0 N) 2)) g = (a : ℂ) • g →
        χ t = (a : ℂ) := by
    intro t a ha
    exact smul_eigen_unique hg0 ((hχ t).symm.trans ha)
  have hmem : ∀ t : heckeAlgebra N 2 S, χ t ∈ integralClosure ℤ ℂ := by
    intro t
    obtain ⟨a, ha, -⟩ := H t
    rw [hχa t a ha]; exact a.2
  refine ⟨g, 𝔐, χ.codRestrict (integralClosure ℤ ℂ) hmem, hg, h𝔐, ?_, ?_⟩
  · intro t ht
    obtain ⟨a, ha, ha𝔐⟩ := H t
    have : χ.codRestrict (integralClosure ℤ ℂ) hmem t = a := Subtype.ext (hχa t a ha)
    rw [this]; exact ha𝔐 ht
  · intro ℓ hℓ hℓN hℓS
    exact hχT ℓ hℓ hℓN hℓS

end Eigen

section Main

variable (p : ℕ) [Fact p.Prime] (N : ℕ) [NeZero N] (S : Set ℕ)

theorem main (𝔪 : Ideal (heckeAlgebra N 2 S)) (h𝔪 : 𝔪.IsMaximal)
    (hp𝔪 : ((p : ℕ) : heckeAlgebra N 2 S) ∈ 𝔪) :
    ∃ (L : Type) (_ : Field L) (_ : Finite L) (j : heckeAlgebra N 2 S ⧸ 𝔪 →+* L)
      (ρ : Γℚ →* GL (Fin 2) L),
      GaloisFactorsThroughFiniteLevel ρ ∧
      (∀ (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓN : ¬ ℓ ∣ N) (hℓS : ℓ ∉ S), ℓ ≠ p →
        ∀ A : ValuationSubring (AlgebraicClosure ℚ), A.LiesOverPrime ℓ →
          ∀ σ : Γℚ, A.IsFrobeniusAt σ ℓ →
            Matrix.trace (ρ σ).val =
              j (Ideal.Quotient.mk 𝔪 (heckeAlgebra.T hℓ hℓN hℓS))) ∧
      (∀ ℓ : ℕ, ℓ.Prime → ¬ ℓ ∣ N → ℓ ≠ p →
        ∀ A : ValuationSubring (AlgebraicClosure ℚ), A.LiesOverPrime ℓ →
          ∀ σ : Γℚ, A.IsFrobeniusAt σ ℓ → Matrix.det (ρ σ).val = (ℓ : L)) ∧
      (∀ ℓ : ℕ, ℓ.Prime → ¬ ℓ ∣ N → ℓ ≠ p →
        ∀ A : ValuationSubring (AlgebraicClosure ℚ), A.LiesOverPrime ℓ →
          ∀ σ ∈ A.inertiaSubgroupIn ℚ, ρ σ = 1) := by
  classical
  have hp : p.Prime := Fact.out

  obtain ⟨g, 𝔐, θ, hg, h𝔐, hθ𝔪, hθT⟩ := exists_eigenchar 𝔪 h𝔪

  letI : Field (Zbar ⧸ 𝔐) := Ideal.Quotient.field 𝔐
  let φ : Zbar →+* Zbar ⧸ 𝔐 := Ideal.Quotient.mk 𝔐
  have hp𝔐 : ((p : ℕ) : Zbar) ∈ 𝔐 := by
    have := hθ𝔪 _ hp𝔪
    rwa [map_natCast] at this
  have hp0 : ((p : ℕ) : Zbar ⧸ 𝔐) = 0 := by
    rw [← map_natCast φ, Ideal.Quotient.eq_zero_iff_mem]; exact hp𝔐
  haveI : CharP (Zbar ⧸ 𝔐) p := (CharP.charP_iff_prime_eq_zero hp).mpr hp0
  letI : Algebra (ZMod p) (Zbar ⧸ 𝔐) := ZMod.algebra _ p

  obtain ⟨ρb, hatt, hunr⟩ := hg.exists_residualGaloisRep_isAttachedTo hp φ

  haveI : Module.Finite ℤ (heckeAlgebra N 2 S) := CuspForm.moduleFinite_heckeAlgebra_two N S
  haveI : Finite (heckeAlgebra N 2 S ⧸ 𝔪) := finite_quotient_of_natCast_mem hp.ne_zero 𝔪 hp𝔪

  let j₀ : heckeAlgebra N 2 S ⧸ 𝔪 →+* Zbar ⧸ 𝔐 :=
    Ideal.Quotient.lift 𝔪 (φ.comp θ) fun t ht =>
      (Ideal.Quotient.eq_zero_iff_mem.mpr (hθ𝔪 t ht))
  have hj₀ : ∀ t, j₀ (Ideal.Quotient.mk 𝔪 t) = φ (θ t) := fun t => Ideal.Quotient.lift_mk _ _ _

  refine package p (isIntegral_zmod_of_quotient p φ Ideal.Quotient.mk_surjective) 𝔪 j₀ N S
    (fun ℓ hℓ hℓN hℓS => heckeAlgebra.T hℓ hℓN hℓS) ρb ?_ ?_
  · intro ℓ hℓ hℓN hℓp A hA σ hσ
    have hℓ0 : (ℓ : Zbar ⧸ 𝔐) ≠ 0 :=
      CharP.cast_ne_zero_of_ne_of_prime (Zbar ⧸ 𝔐) (p := p) hℓ (Ne.symm hℓp)
    obtain ⟨a, ha, hchar⟩ := hatt ℓ hℓ hℓN hℓ0 A hA σ hσ
    refine ⟨φ a, hchar, fun hℓS => ?_⟩
    rw [hj₀]
    congr 1
    apply Subtype.ext
    rw [hθT ℓ hℓ hℓN hℓS, ha]
  · intro ℓ hℓ hℓN hℓp
    refine hunr ℓ hℓ fun h => ?_
    rcases (Nat.Prime.dvd_mul hℓ).mp h with h | h
    · exact hℓN h
    · exact hℓp ((Nat.prime_dvd_prime_iff_eq hℓ hp).mp h)

end Main

end DeligneModMTwo

theorem solution
    (p : ℕ) [Fact p.Prime] (N : ℕ) [NeZero N] (S : Set ℕ)
    (𝔪 : Ideal (heckeAlgebra N 2 S)) (h𝔪 : 𝔪.IsMaximal)
    (hp𝔪 : ((p : ℕ) : heckeAlgebra N 2 S) ∈ 𝔪) :
    ∃ (L : Type) (_ : Field L) (_ : Finite L) (j : heckeAlgebra N 2 S ⧸ 𝔪 →+* L)
      (ρ : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) →* GL (Fin 2) L),
      GaloisFactorsThroughFiniteLevel ρ ∧
      (∀ (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓN : ¬ ℓ ∣ N) (hℓS : ℓ ∉ S), ℓ ≠ p →
        ∀ A : ValuationSubring (AlgebraicClosure ℚ), A.LiesOverPrime ℓ →
          ∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, A.IsFrobeniusAt σ ℓ →
            Matrix.trace (ρ σ).val =
              j (Ideal.Quotient.mk 𝔪 (heckeAlgebra.T hℓ hℓN hℓS))) ∧
      (∀ ℓ : ℕ, ℓ.Prime → ¬ ℓ ∣ N → ℓ ≠ p →
        ∀ A : ValuationSubring (AlgebraicClosure ℚ), A.LiesOverPrime ℓ →
          ∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, A.IsFrobeniusAt σ ℓ →
            Matrix.det (ρ σ).val = (ℓ : L)) ∧
      (∀ ℓ : ℕ, ℓ.Prime → ¬ ℓ ∣ N → ℓ ≠ p →
        ∀ A : ValuationSubring (AlgebraicClosure ℚ), A.LiesOverPrime ℓ →
          ∀ σ ∈ A.inertiaSubgroupIn ℚ, ρ σ = 1) :=
  DeligneModMTwo.main p N S 𝔪 h𝔪 hp𝔪

end S_GaloisRep_exists_finiteField_galoisRep_trace_eq_heckeT_mod_of_isMaximal_two
end P2MW
export P2MW.S_GaloisRep_exists_finiteField_galoisRep_trace_eq_heckeT_mod_of_isMaximal_two (solution)
