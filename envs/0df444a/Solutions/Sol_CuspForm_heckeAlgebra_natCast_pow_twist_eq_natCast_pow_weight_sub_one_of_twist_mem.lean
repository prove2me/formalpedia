-- Prove2me | solution 1 for CuspForm.heckeAlgebra.natCast_pow_twist_eq_natCast_pow_weight_sub_one_of_twist_mem
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.805612+00:00
-- url     : https://prove2.me/submissions/107222d2-3074-5961-b7ff-34a7d3d2d53c

import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
import Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Basic
import Mathlib.Tactic.Linarith
import Definitions.Def_FLTPrelim_ModularRep
import Definitions.Def_FLTPrelim_Modularity
import Definitions.Def_FLTPrelim_Ramification
import Definitions.Def_CuspForm_HeckeAlgebra
import Definitions.Def_GaloisRep_Residual
import Definitions.Def_GaloisRep_TameCharacter
import Definitions.Def_EllipticCurve_FrobeniusTrace
import Mathlib.Algebra.Group.Subgroup.Basic
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Algebra.Order.Ring.Int
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.GroupTheory.FiniteAbelian.Basic
import Mathlib.RingTheory.Ideal.GoingUp
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
import Definitions.Def_ValuationSubring_ReduceAt
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Definitions.Def_GaloisRep_DeligneOrdinaryShape
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.LinearAlgebra.Charpoly.BaseChange
import Mathlib.LinearAlgebra.Trace
import Mathlib.LinearAlgebra.Determinant
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.LinearAlgebra.Span.Basic
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.RingTheory.Polynomial.Cyclotomic.Roots
import Mathlib.RingTheory.Ideal.Span
import Mathlib.FieldTheory.Galois.Basic
import Definitions.Def_FieldTheory_RatAlgClosureGalois
import Mathlib.FieldTheory.Normal.Closure
import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.Algebra.CharP.Basic
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Theorems.Thm_WeierstrassCurve_card_torsionBy_eq_sq_of_isAlgClosed
import Theorems.Thm_WeierstrassCurve_galoisRepModuleEnd_factorsThroughFiniteLevel
import Theorems.Thm_WeierstrassCurve_galoisTrace_frobenius_eq_apOfModel
import Theorems.Thm_WeierstrassCurve_det_galoisRep_frobenius_eq_prime
import Theorems.Thm_ValuationSubring_exists_liesOverPrime_isFrobeniusAt_ratAlgClosure
import Theorems.Thm_GaloisRep_exists_galoisFactorsThroughFiniteLevel_trace_eq_theta_heckeT_and_det_eq_pow
import Theorems.Thm_FrobeniusDensity_exists_isFrobeniusAt_conj_mem_of_le_ker
import Theorems.Thm_MonoidHom_det_eq_of_trace_eq_of_exists_isFrobeniusAt_conj
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CuspForm_heckeAlgebra_natCast_pow_twist_eq_natCast_pow_weight_sub_one_of_twist_mem
p2m_attr_erase "instance" "WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly HeckeEis.instFiniteProjLineCusps ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid HeckeEis.instModuleCoeffH1par HeckeEis.instAddCommGroupCoeffH1par HeckeEis.instFiniteIndexHeckeUpper FLT.Gamma0FundamentalSet.instContinuousConstSMulSpecialLinearGroupFinOfNatNatIntUpperHalfPlane_definitions FLT.HyperbolicMeasure.instSMulInvariantMeasureSpecialLinearGroupFinOfNatNatIntUpperHalfPlaneVolume_definitions FLT.HyperbolicMeasure.instIsOpenPosMeasureUpperHalfPlaneVolume_definitions ModularCurve.CuspSpace.instNonempty ModularCurve.CuspSpace.instSubsingletonOfOne ModularCurve.CuspSpace.instFinite ModularCurve.PhiGen.instNeZeroPhiGenCosetA AlgebraicCurve.instFundamentalIdentityOfSumRamificationInertia AlgebraicCurve.Place.instIsScalarTowerResidueFieldRestrictPushforward AlgebraicCurve.Place.instAlgebraResidueFieldRestrictPushforward AlgebraicCurve.Place.instIsLocalHomRestrictInclusion AlgebraicCurve.Place.instIsScalarTowerSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Divisor.instDistribMulActionAlgEquiv AlgebraicCurve.Place.instSMulAlgEquiv AlgebraicCurve.Place.instIsPrincipalIdealRingSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Place.instIsDiscreteValuationRingSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Pic0.instDistribMulActionAlgEquiv AlgebraicCurve.Place.instAlgebraSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Place.instMulActionAlgEquiv AlgebraicCurve.Pic0.instSMulAlgEquiv AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupDivisor AlgebraicCurve.Pic0.instModuleZModTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instDistribMulActionTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instSMulTorsion AlgebraicCurve.SemilinearAut.instMulActionSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instSMulCommClassZModTorsion AlgebraicCurve.SemilinearAut.instMulSemiringActionSubtypeProdRingAutMemSubgroup"
p2m_attr_erase "instance" "ModularCurve.instSMulAlgEquivRatPic0SubtypeLaurentSeriesMemIntermediateFieldLaurentBaseChange ModularCurve.instDistribMulActionAlgEquivRatPic0SubtypeLaurentSeriesMemIntermediateFieldLaurentBaseChange ModularCurve.instIsDomainTensorProduct AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue ModularCurve.Gamma0Pair.isElliptic AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions WeierstrassCurve.Affine.instIsScalarTowerPolynomialRatFuncFunctionField_definitions WeierstrassCurve.Affine.instAlgebraRatFuncFunctionField_definitions WeierstrassCurve.Affine.instIsScalarTowerRatFuncFunctionField_definitions WeierstrassCurve.Affine.CoordinateRing.moduleFinite WeierstrassCurve.Affine.instDecidableEqFunctionField WeierstrassCurve.Affine.CoordinateRing.isIntegral ModularCurve.instAlgebraJLineBar ModularCurve.instModuleJLineBar ModularCurve.instIsScalarTowerJAdjoin ModularCurve.TatePoint.instIsElliptic_nearCurve ModularCurve.instIsElliptic_tateLaurent ModularCurve.B3.instIsElliptic_goodModel ModularCurve.numberField_of_finiteDimensional AlgebraicCurve.instHasLocalResidue_of_hasCanonicalLocalResidueK AlgebraicCurve.instHasCanonicalLocalResidueK_of_hasCanonicalLocalResidueKStar AlgebraicCurve.Place.kw_ffgc_finiteDimensional_adicCompletion instAlgebraSubtypeMemValuationSubring_definitions AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersIntegersCompletion ModularCurve.KwF4gRRTate.instAlgebraKAdicCompletionIntegers AlgebraicCurve.Place.kw_ffgc_continuousSMul_adicCompletionComap AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersCompletionCompletion IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal"
p2m_attr_erase "instance" "IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions AlgebraicCurve.instHasCanonicalLocalResidueK AlgebraicCurve.Place.instAlgebra_restrictResidueField AlgebraicCurve.Place.instIsScalarTower_restrictResidueField AlgebraicCurve.instHasLocalResidue AlgebraicCurve.HasSeparableResidue.of_perfectField_of_isCurveOver AlgebraicCurve.HasSeparableResidue.of_perfectField AlgebraicCurve.Place.instIsLocalHom_restrictSubringHom AlgebraicCurve.instHasCanonicalLocalResidueKStar ModularCurve.KwNo6Pin.isLocalRing_completion ModularCurve.instAlgebraIntermediateFieldLaurent ModularCurve.instIsScalarTowerKaehlerIntermediateFieldLaurent ModularCurve.instIsScalarTowerIntermediateFieldLaurent ModularCurve.instModuleKaehlerIntermediateFieldLaurent GaloisRepAdic.instAddCommGroup GaloisRepAdic.instFree GaloisRepAdic.instFinite GaloisRepAdic.instModule TateModule.instModule TateModule.instSMul ModularCurve.Period.parabolicHoms_int_moduleFinite ModularCurve.Period.instGroupFG_SL2Z ModularCurve.Period.instIsNoetherian_addHom_int ModularCurve.Period.instGroupFG_Gamma0 FLT.L2ProductionInstance.isFiniteMeasure_gamma0 FLT.L2ProductionInstance.countable_SL2Z FLT.L2ProductionInstance.countable_quotient FLT.L2ProductionInstance.nontrivial_gamma0L2 AlgebraicCurve.CellDissection.fintypeV AlgebraicCurve.CellDissection.fintypeC AlgebraicCurve.CellDissection.fintypeE AlgebraicCurve.CellDissection.decEqV AlgebraicCurve.CellDissection.decEqC AlgebraicCurve.CellDissection.decEqE WeierstrassCurve.VeluQuotientJGates.instIsElliptic27a4 ModularCurve.ElevenA1.instDecidableEquation ModularCurve.ElevenA1.instDecidableNonsingular HeckeEis.instAddCommGroupCoeffH1"
p2m_attr_erase "instance" "HeckeEis.instModuleCoeffH1 CohCarrier.iotaDeg_range_finiteIndex CohCarrier.Gamma0Upper_finiteIndex CohCarrier.HeckeData.V_isScalarTower CohCarrier.HeckeData.opSubalgebra_isMulCommutative CohCarrier.HeckeData.mTheta_isPrime CohCarrier.GammaHLower_finiteIndex FrobeniusDensity.isMaximal_ratPrimeIdeal FrobeniusDensity.liesOver_ratBelow Deep.NTSupply.instNormalRayClassSubgroup NumberField.NormResidueChar.fintype_G NumberField.NormResidueChar.finite_G"
p2m_attr_erase "simp" "compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two FrobeniusEndo.linePencil_apply WeierstrassCurve.Universal.halveX_zero WeierstrassCurve.Universal.specialize_X_one WeierstrassCurve.Universal.coeff_halve WeierstrassCurve.Universal.specialize_X_two WeierstrassCurve.Universal.halveCoeff_zero WeierstrassCurve.Universal.specialize_X_four"
p2m_attr_erase "simp" "WeierstrassCurve.Universal.coeff_halveX WeierstrassCurve.Universal.specialize_X_three WeierstrassCurve.Universal.specialize_X_zero HeckeEis.binaryFormEval_mk HeckeEis.binaryFormAlphaAdj_apply_coe HeckeEis.binaryFormRepSL_apply_coe ModularCurve.ProjectiveLine.vecMulRow_snd HeckeEis.projLineRepSL_apply HeckeEis.projLineAct_one HeckeEis.projLineRep_apply HeckeEis.projLineAlphaAdj_apply ModularCurve.ProjectiveLine.vecMulRow_fst ModularCurve.ProjectiveLine.vecMul_mk ModularCurve.ProjectiveLine.map_mk HeckeEis.coeffCoboundaryMap_apply HeckeEis.heckeConjMat_apply_one_one HeckeEis.coe_heckeConjSL HeckeEis.mem_heckeUpperSL HeckeEis.resHom_apply HeckeEis.heckeConjMat_apply_zero_one HeckeEis.coe_transferAux HeckeEis.coe_heckeConj HeckeEis.alphaMat_apply_one_one HeckeEis.heckeConjMat_apply_one_zero HeckeEis.alphaMat_apply_zero_one HeckeEis.pullbackHom_apply HeckeEis.alphaMat_apply_one_zero HeckeEis.alphaMat_apply_zero_zero HeckeEis.heckeConjMat_apply_zero_zero HeckeEis.coe_linePow ModularCurve.cuspCount_one ModularCurve.qExpand_coeff_mul ModularCurve.qExpandₐ_apply ModularCurve.jqN_one ModularCurve.qExpand_single ModularCurve.dedekindPsi_one ModularCurve.ModularPolynomialData.mk.sizeOf_spec ModularCurve.evalAtJ_X ModularCurve.ModularPolynomialData.mk.injEq ModularCurve.constantCoeff_jNum"
p2m_attr_erase "simp" "ModularCurve.constantCoeff_eisenstein4 ModularCurve.qExpand_C ModularCurve.coeff_jq_neg_one ModularCurve.constantCoeff_jNumQ ModularCurve.CuspSpace.cuspDenomAux_infty ModularCurve.CuspSpace.cuspDenomAux_coe ModularCurve.CuspSpace.cuspDenom_mk_zero ModularCurve.CuspSpace.cuspDenom_mk_infty ModularCurve.mapGL_apply_coe ModularCurve.ratPoint_one_zero ModularCurve.ratPoint_zero_right ModularCurve.CuspSpace.fromCoset_mk ModularCurve.CuspSpace.cuspDenom_mk ModularCurve.ratPoint_zero_one ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularCurve.coeffEmb_coeff ModularCurve.coeffMap_coeff ModularCurve.coeffMap_id ModularCurve.coeffMap_single ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd ModularCurve.coe_heckeBetaBarRingHom ModularCurve.coe_heckeBetaBar ModularCurve.coe_heckeAlphaBar AlgebraicCurve.Divisor.degree_pushforwardAlong AlgebraicCurve.Pic0.coe_degZeroCorrespondence AlgebraicCurve.Place.mem_fiberAlong AlgebraicCurve.Divisor.mapRestrict_single"
p2m_attr_erase "simp" "AlgebraicCurve.Divisor.pushforward_single AlgebraicCurve.Place.coe_restrictInclusion AlgebraicCurve.Place.mem_fiber AlgebraicCurve.Place.restrict_toValuationSubring AlgebraicCurve.Divisor.degree_pushforward AlgebraicCurve.Place.restrictResidueMap_residue AlgebraicCurve.Pic0.coe_pushforwardDegZeroHom AlgebraicCurve.Pic0.coe_pullbackDegZeroHom AlgebraicCurve.Place.mk.injEq AlgebraicCurve.Divisor.degree_single AlgebraicCurve.Divisor.smul_single AlgebraicCurve.Place.smul_toValuationSubring AlgebraicCurve.Place.heightOneSpectrum_asIdeal AlgebraicCurve.Place.coe_algebraMap AlgebraicCurve.Place.ord_one AlgebraicCurve.Place.coe_smulRingEquiv_apply AlgebraicCurve.Pic0.coe_degZeroSMulHom AlgebraicCurve.Place.deg_smul AlgebraicCurve.Pic0.mk_zero AlgebraicCurve.Place.mk.sizeOf_spec AlgebraicCurve.Divisor.degree_smul AlgebraicCurve.Pic0.mk_add AlgebraicCurve.Place.ord_zero AlgebraicCurve.Place.ofHeightOneSpectrum_toValuationSubring AlgebraicCurve.SemilinearAut.toRingAut_inv AlgebraicCurve.SemilinearAut.smul_def AlgebraicCurve.SemilinearAut.smul_single AlgebraicCurve.SemilinearAut.smul_toValuationSubring AlgebraicCurve.SemilinearAut.baseAut_inv AlgebraicCurve.SemilinearAut.baseAut_ofAlgAut AlgebraicCurve.SemilinearAut.toRingAut_ofAlgAut AlgebraicCurve.SemilinearAut.torsionRep_apply AlgebraicCurve.SemilinearAut.toRingAut_one AlgebraicCurve.SemilinearAut.deg_smul AlgebraicCurve.SemilinearAut.degree_smul AlgebraicCurve.SemilinearAut.coe_degZeroSMulHom AlgebraicCurve.SemilinearAut.baseAut_mul AlgebraicCurve.SemilinearAut.coe_smulValuationSubringEquiv_apply AlgebraicCurve.SemilinearAut.baseAut_one AlgebraicCurve.SemilinearAut.ofAlgAut_smul"
p2m_attr_erase "simp" "AlgebraicCurve.SemilinearAut.coe_torsion_smul AlgebraicCurve.SemilinearAut.toRingAut_mul ModularCurve.baseAut_arithmeticGalois ModularCurve.JZero.torsionGaloisRep_apply ModularCurve.coe_arithmeticRingAut_apply ModularCurve.toRingAut_arithmeticGalois ModularCurve.coe_cuspidalDivisor₀ ModularCurve.qInftyPlaceBar_toValuationSubring ModularCurve.qSeriesBar_zero ModularCurve.qSeriesBar_add ModularCurve.cuspInftyFull_toValuationSubring ModularCurve.qInftyPlaceRat_toValuationSubring ModularCurve.qSeriesBar_mul ModularCurve.qSeriesBar_div ModularCurve.qSeriesBar_eq_zero_iff ModularCurve.coe_uniformizerBar ModularCurve.qSeriesBar_pow ModularCurve.cuspInfty_toValuationSubring ModularCurve.qSeriesBar_one ModularCurve.qSeriesBar_inv ModularCurve.qSeriesBar_sub ModularCurve.qSeriesBar_neg ModularCurve.coe_baseChangeEquiv_apply ModularCurve.baseChangeHom_tmul AlgebraicCurve.mulAdele_apply AlgebraicCurve.residuePairing_apply_coe AlgebraicCurve.mem_adeleBdd AlgebraicCurve.weilSmul_one AlgebraicCurve.diagonalHom_apply AlgebraicCurve.weilSmul_apply AlgebraicCurve.adeleSpaceMul_coe AlgebraicCurve.mulAdele_one AlgebraicCurve.Place.differentialCoeff_zero AlgebraicCurve.Place.differentialCoeff_dCoord ModularCurve.gamma0PairMap_gen ModularCurve.moduliPointMapRingHom_mk ModularCurve.Gamma0Pair.mk.injEq ModularCurve.ModuliPoint.j_mk ModularCurve.Gamma0Pair.mk.sizeOf_spec ModularCurve.gamma0PairMap_toCurve"
p2m_attr_erase "simp" "WeierstrassCurve.Affine.vcY_vcYInv WeierstrassCurve.Affine.vcXInv_vcX WeierstrassCurve.Affine.Point.vcFun_zero WeierstrassCurve.Affine.vcX_vcXInv WeierstrassCurve.Affine.vcYInv_vcY WeierstrassCurve.Affine.Point.vcInvFun_zero WeierstrassCurve.ratPointHom_apply WeierstrassCurve.ratPointMap_zero AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint ModularCurve.jqNModC_one AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X"
p2m_attr_erase "simp" "ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one ModularCurve.coe_towerInclBar ModularCurve.coe_towerSubstBar HahnSeries.ramScale_apply WeierstrassCurve.veluWSum_empty WeierstrassCurve.veluQuotient_a₁ WeierstrassCurve.veluQuotient_a₃ WeierstrassCurve.veluQuotient_empty WeierstrassCurve.veluTSum_empty WeierstrassCurve.veluQuotient_a₂ WeierstrassCurve.Affine.Point.coordsOrZero_some WeierstrassCurve.Affine.Point.coordsOrZero_zero WeierstrassCurve.veluQuotient2_a₂ WeierstrassCurve.veluQuotient2_a₃ WeierstrassCurve.veluQuotient2_a₁ WeierstrassCurve.veluPointMap2_zero WeierstrassCurve.Affine.IsogenyEndDatum.mk.injEq WeierstrassCurve.Affine.IsogenyHomDatum.mk.sizeOf_spec WeierstrassCurve.Affine.IsogenyHomDatum.mk.injEq WeierstrassCurve.Affine.IsogenyEndDatum.mk.sizeOf_spec AlgebraicCurve.Pic0.coe_pushforwardAlongDegZero WeierstrassCurve.Affine.pointMapOfPushforward_apply"
p2m_attr_erase "simp" "WeierstrassCurve.Affine.pointClass_zero WeierstrassCurve.Affine.pic0ToPoint_pointClass WeierstrassCurve.Affine.deg_placeOfPoint WeierstrassCurve.Affine.coe_pointDivisor WeierstrassCurve.Affine.pointEquivPlace_symm_placeOfPoint WeierstrassCurve.Affine.pointEquivPlace_apply WeierstrassCurve.Affine.genusOnePic0Equiv_symm_apply WeierstrassCurve.Affine.pointDivisor_zero WeierstrassCurve.Affine.pic0ToPoint_mk WeierstrassCurve.Affine.divisorSum_single WeierstrassCurve.Affine.genusOnePic0Equiv_apply PeriodPair.weierstrassCurve_a₆ PeriodPair.weierstrassCurve_a₃ PeriodPair.weierstrassCurve_a₁ PeriodPair.ofTau_ω₂ PeriodPair.scale_ω₂ PeriodPair.ofTau_ω₁ PeriodPair.toPoint_zero PeriodPair.toPoint_of_mem PeriodPair.weierstrassCurve_a₂ PeriodPair.ofTau_lattice PeriodPair.scale_ω₁ PeriodPair.weierstrassCurve_a₄ WeierstrassCurve.Affine.ratFuncToFunctionField_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_C WeierstrassCurve.Affine.Point.yc_some WeierstrassCurve.Affine.Point.xc_some WeierstrassCurve.Affine.pointPull_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_X WeierstrassCurve.Affine.pointHom_mk_Y WeierstrassCurve.Affine.placeOf_asIdeal WeierstrassCurve.veluY_empty WeierstrassCurve.veluX_empty AddMonoid.End.DualEndData.symm_trace AddMonoid.End.dualEndData_intCast_norm AddMonoid.End.DualEndData.ofCharPoly_norm AddMonoid.End.DualEndData.mk.sizeOf_spec AddMonoid.End.DualEndData.mk.injEq AddMonoid.End.DualEndData.ofCharPoly_dual AddMonoid.End.dualEndData_intCast_dual"
p2m_attr_erase "simp" "AddMonoid.End.DualEndData.intLinComb_norm AddMonoid.End.DualEndData.ofCharPoly_trace AddMonoid.End.DualEndData.intLinComb_dual AddMonoid.End.DualEndData.symm_dual AddMonoid.End.DualEndData.intLinComb_trace AddMonoid.End.dualEndData_intCast_trace AddMonoid.End.DualEndData.symm_norm ModularCurve.tateLaurent_a₆ ModularCurve.tatePowerSeries_a₄ ModularCurve.tatePowerSeries_a₆ ModularCurve.tateLaurent_a₄ ModularCurve.tatePowerSeries_a₁ ModularCurve.tatePowerSeries_a₂ ModularCurve.tatePowerSeries_a₃ WeierstrassCurve.veluQuotientOfSums_a₂ WeierstrassCurve.veluQuotientOfSums_a₁ WeierstrassCurve.veluQuotientOfSums_a₃ ModularCurve.B3.cycOfCongr_apply_coe ModularCurve.B3.cycOfTorsionBy_symm_apply_coe ModularCurve.B3.redPoint_zero ModularCurve.B3.pointAddEquivOfEq_rfl ModularCurve.B3.vcAddEquiv_apply ModularCurve.B3.scaleAddEquiv_apply ModularCurve.B3.cycOfTorsionBy_apply_coe ModularCurve.B3.val_inv_sU ModularCurve.B3.val_sU ModularCurve.B3.resO_apply HahnSeries.coeff_hahnTwist ModularCurve.HahnSpecialise.coe_specialiseCycSub CycSubOf.coe_map ModularCurve.HahnSpecialise.algebraMap_Qbar_apply ModularCurve.HahnSpecialise.resH_apply ModularCurve.HahnSpecialise.liftModel_map_subtype ModularCurve.HahnSpecialise.specialise_zero ModularCurve.symPoly_zero AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.sizeOf_spec AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.injEq AlgebraicCurve.adeleSingle_coe AlgebraicCurve.kaehlerResidueTermKFam_apply AlgebraicCurve.Place.LocalResidueData.mk.injEq"
p2m_attr_erase "simp" "AlgebraicCurve.Place.LocalResidueData.mk.sizeOf_spec AlgebraicCurve.Place.kw_ffgc_adicCompletionComapIntegers_coe AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.sizeOf_spec AlgebraicCurve.Place.mem_simplePoleSubmodule AlgebraicCurve.Place.coe_uniformizerSubring ModularCurve.Lg37.Lg37CompletionSection.mk.injEq AlgebraicCurve.Place.CoefficientFieldSection.mk.injEq AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.injEq ModularCurve.Lg37.Lg37CompletionSection.mk.sizeOf_spec AlgebraicCurve.Place.CoefficientFieldSection.mk.sizeOf_spec AlgebraicCurve.Place.poleSubmodule_one AlgebraicCurve.Place.mem_poleSubmodule AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.injEq AlgebraicCurve.TranscendenceTower.mk.injEq AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec AlgebraicCurve.PoleDivisorPackage.mk.injEq ModularCurve.Period.IsEquivariantPrimitive.periodHom_apply ModularCurve.Period.IsEquivariantPrimitive.period_one ModularCurve.qEulerFun_coeff ModularCurve.diffQExp_D ModularCurve.qEulerOn_apply ModularCurve.qEuler_coeff PowerSeries.coeff_heckeV PowerSeries.coeff_heckeU GaloisRepAdic.mk.injEq GaloisRepAdic.mk.sizeOf_spec GaloisRepAdic.Equiv.mk.sizeOf_spec GaloisRepAdic.Equiv.mk.injEq ResidualGaloisRep.Equiv.mk.sizeOf_spec ResidualGaloisRep.Equiv.mk.injEq TateModule.smul_apply TateModule.coe_mulP TateModule.proj_apply TateModule.coe_add TateModule.coe_sub WeierstrassCurve.tateModuleRepOfBasis_V TateModule.coe_zero TateModule.rep_apply"
p2m_attr_erase "simp" "WeierstrassCurve.tateModuleRep_V WeierstrassCurve.tateModuleRepOfBasis_ρ_apply GaloisRep.padicIntToRingLevel_apply TateModule.coe_neg WeierstrassCurve.tateModuleRep_ρ_apply ModularCurve.dualHeckeRep_apply_apply ModularCurve.coe_segmentPath ModularCurve.cuspHeckeAeval_heckeGen ModularCurve.coe_periodLatticeRestrict_apply ModularCurve.Period.jConjMat_apply_zero_one ModularCurve.Period.jConjSL_coe ModularCurve.Period.jConjMat_apply_one_zero ModularCurve.Period.jConjMat_apply_one_one ModularCurve.Period.jConjGamma0_coe ModularCurve.Period.charInvolution_apply ModularCurve.Period.jConjMat_apply_zero_zero ModularCurve.ComplexPlaceDictionary.mk.injEq ModularCurve.ComplexPlaceDictionary.mk.sizeOf_spec FLT.TruncatedDomainPartition.unipotentDiagonalSum_zero AlgebraicCurve.DivisorialWeilPairingData.toChar_apply AlgebraicCurve.WeilDatum.coe_classRight AlgebraicCurve.WeilDatum.coe_degZeroRight AlgebraicCurve.DivisorialWeilPairingData.mk.sizeOf_spec AlgebraicCurve.WeilDatum.coe_classLeft AlgebraicCurve.WeilDatum.coe_degZeroLeft AlgebraicCurve.DivisorialWeilPairingData.mk.injEq AlgebraicCurve.DivisorialWeilPairingData.toHom_apply_apply AlgebraicCurve.WeilDatum.mk.sizeOf_spec AlgebraicCurve.WeilDatum.mk.injEq AlgebraicCurve.WeilPairingData.evalAddChar_zero AlgebraicCurve.PrincipalPolarization.mk.injEq AlgebraicCurve.WeilPairingData.evalAddChar_apply AlgebraicCurve.H1Gm.degree_ofPic0 AlgebraicCurve.WeilPairingData.mk.sizeOf_spec AlgebraicCurve.HomPic0Gm.map_one AlgebraicCurve.PrincipalPolarization.mk.sizeOf_spec AlgebraicCurve.WeilPairingData.autodualityEquiv_apply AlgebraicCurve.WeilPairingData.eval_zero_right AlgebraicCurve.H1Gm.ofPic0_mk AlgebraicCurve.WeilPairingData.eval_neg_left"
p2m_attr_erase "simp" "AlgebraicCurve.HomPic0Gm.map_apply AlgebraicCurve.H1Gm.degree_mk AlgebraicCurve.HomPic0Gm.map_id AlgebraicCurve.WeilPairingData.mk.injEq AlgebraicCurve.WeilPairingData.congr_eval AlgebraicCurve.WeilPairingData.eval_neg_right AlgebraicCurve.WeilPairingData.eval_zero_left AlgebraicCurve.ConstantReduction.toRegularProlongation_residue AlgebraicCurve.RegularProlongation.mk.sizeOf_spec AlgebraicCurve.ConstantReduction.toRegularProlongation_integers AlgebraicCurve.RegularProlongation.mk.injEq AlgebraicCurve.ConstantReduction.mk.injEq AlgebraicCurve.ConstantReduction.mk.sizeOf_spec AlgebraicCurve.ConstantReduction.divMap_apply AlgebraicCurve.ConstantReduction.coe_degZeroMap ModularCurve.tateMap_apply AlgebraicCurve.abelJacobiDiv_single AlgebraicCurve.AnalyticCoord.mk.injEq AlgebraicCurve.Cell.mk.sizeOf_spec AlgebraicCurve.RadialRegion.mk.sizeOf_spec AlgebraicCurve.RadialRegion.mk.injEq AlgebraicCurve.CellDissection.mk.sizeOf_spec AlgebraicCurve.Cell.mk.injEq AlgebraicCurve.CellDissection.mk.injEq AlgebraicCurve.AnalyticCoord.mk.sizeOf_spec ModularCurve.reductionDivAlong_apply ModularCurve.coe_reductionDegZeroAlong ModularCurve.qExpandAlgHomC_apply ModularCurve.coe_frobeniusModL ModularCurve.coe_frobeniusDegZeroPullbackModL ModularCurve.coe_frobeniusDegZeroPushforwardModL ModularCurve.coe_uniformizerMod ModularCurve.qSeriesBar_jModElt ModularCurve.qInftyPlaceMod_toValuationSubring WeierstrassCurve.twoVeluCurve_a₁ WeierstrassCurve.twoVeluCurve_a₂ WeierstrassCurve.twoVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₂ WeierstrassCurve.xVeluCurve_a₁"
p2m_attr_erase "simp" "WeierstrassCurve.map_veluU WeierstrassCurve.map_veluT WeierstrassCurve.map_veluW WeierstrassCurve.map_veluGy WeierstrassCurve.map_veluGx WeierstrassCurve.map_veluWSum_singleton WeierstrassCurve.map_veluTSum_singleton WeierstrassCurve.veluPointMap3_zero WeierstrassCurve.vcInvEmbedding_apply WeierstrassCurve.Affine.Point.netCol_one WeierstrassCurve.Affine.Point.xOrZero_zero WeierstrassCurve.Affine.Point.netPairing_zero_right WeierstrassCurve.Affine.Point.netW20_some WeierstrassCurve.Affine.Point.netCol_zero WeierstrassCurve.Affine.Point.netPairing_zero_left WeierstrassCurve.Affine.Point.xOrZero_some WeierstrassCurve.Affine.Point.netW20_zero TateCurve.cauchyMulInt_zero TateCurve.cauchyMulInt3_zero TateCurve.tent_one TateCurve.Gz_zero TateCurve.cauchyMulInt_one TateCurve.tent_zero TateCurve.Fz_zero TateCurve.xCoeffFull_succ TateCurve.a₆Coeff_zero TateCurve.a₄Coeff_succ TateCurve.a₄Coeff_zero TateCurve.cauchyMul_zero TateCurve.a₆Coeff_succ TateCurve.yCoeffFull_succ TateCurve.xCoeffFull_zero TateCurve.yCoeffFull_zero TateCurve.yfun_zero TateCurve.xfun_zero TateCurve.yTerm_zero TateCurve.xTerm_zero TateCurve.curve_a₂ TateCurve.b_one TateCurve.curve_a₁"
p2m_attr_erase "simp" "TateCurve.term_zero TateCurve.curve_a₆ TateCurve.curve_a₄ TateCurve.curve_a₃ FLT.DivisorConvolution.sigma_zero_right FLT.DivisorConvolution.sigma_one_right FLT.DivisorConvolution.sigmaConv_one FLT.DivisorConvolution.sigmaConv_zero FormalCoordinates.mk.injEq WeierstrassCurve.formalParam_zero WeierstrassCurve.SmoothLocusReductionData.reduceHom₀_apply WeierstrassCurve.formalParam_some FormalCoordinates.mk.sizeOf_spec WeierstrassCurve.SmoothLocusReductionData.mk.injEq WeierstrassCurve.reducePointSmooth_zero WeierstrassCurve.SmoothLocusReductionData.mk.sizeOf_spec WeierstrassCurve.mem_zeroComponentSubgroup_iff HeckeEis.binaryFormRep_apply_coe HeckeEis.gamma0NebenRep_apply CohCarrier.conjUpperMat_apply_11 CohCarrier.conjUpperMat_apply_10 CohCarrier.mem_Gamma0Upper CohCarrier.val_gamma0Units CohCarrier.Gen.dia.sizeOf_spec CohCarrier.Gen.U.injEq CohCarrier.Gen.T.sizeOf_spec CohCarrier.Gen.U.sizeOf_spec CohCarrier.Gen.T.injEq CohCarrier.Gen.dia.injEq CohCarrier.HeckeData.mk.sizeOf_spec CohCarrier.HeckeData.opAlgHom_X CohCarrier.HeckeData.toMLₒ_apply CohCarrier.HeckeData.mk.injEq CohCarrier.uMat_apply_10 CohCarrier.rightQuotEquivOfDvd_apply CohCarrier.uMat_apply_11 CohCarrier.uMat_apply_01 CohCarrier.uMat_apply_00 CohCarrier.coe_uElt TaylorWiles.Seed.mk.injEq"
p2m_attr_erase "simp" "TaylorWiles.Seed.mk.sizeOf_spec"

set_option autoImplicit false

noncomputable section

namespace WLightCong

section Twist

open Matrix

variable {G : Type*} [Group G] {F : Type*} [Field F]

private def scalarUnit (c : Fˣ) : GeneralLinearGroup (Fin 2) F :=
  Units.map (scalar (Fin 2) : F →+* Matrix (Fin 2) (Fin 2) F).toMonoidHom c

private theorem scalarUnit_val (c : Fˣ) : (scalarUnit c).val = scalar (Fin 2) (c : F) := rfl

private theorem scalarUnit_mul (c d : Fˣ) : scalarUnit (c * d) = scalarUnit c * scalarUnit d :=
  map_mul _ c d

private theorem scalarUnit_comm (c : Fˣ) (M : GeneralLinearGroup (Fin 2) F) :
    scalarUnit c * M = M * scalarUnit c := by
  apply Units.ext
  simp only [Units.val_mul, scalarUnit_val]
  exact (scalar_commute (c : F) (fun r => Commute.all _ r) M.val).eq

private def detTwist (ρ : G →* GeneralLinearGroup (Fin 2) F) (i : ℕ) : G →* GeneralLinearGroup (Fin 2) F :=
  MonoidHom.mk' (fun σ => scalarUnit (GeneralLinearGroup.det (ρ σ) ^ i) * ρ σ) (by
    intro σ τ
    simp only [map_mul, mul_pow, scalarUnit_mul]
    calc scalarUnit (GeneralLinearGroup.det (ρ σ) ^ i) * scalarUnit (GeneralLinearGroup.det (ρ τ) ^ i)
          * (ρ σ * ρ τ)
        = scalarUnit (GeneralLinearGroup.det (ρ σ) ^ i)
            * ((scalarUnit (GeneralLinearGroup.det (ρ τ) ^ i) * ρ σ) * ρ τ) := by
          simp only [mul_assoc]
      _ = scalarUnit (GeneralLinearGroup.det (ρ σ) ^ i)
            * ((ρ σ * scalarUnit (GeneralLinearGroup.det (ρ τ) ^ i)) * ρ τ) := by
          rw [scalarUnit_comm (GeneralLinearGroup.det (ρ τ) ^ i) (ρ σ)]
      _ = scalarUnit (GeneralLinearGroup.det (ρ σ) ^ i) * ρ σ
            * (scalarUnit (GeneralLinearGroup.det (ρ τ) ^ i) * ρ τ) := by
          simp only [mul_assoc])

private theorem detTwist_apply (ρ : G →* GeneralLinearGroup (Fin 2) F) (i : ℕ) (σ : G) :
    detTwist ρ i σ = scalarUnit (GeneralLinearGroup.det (ρ σ) ^ i) * ρ σ := rfl

private theorem detTwist_apply_val (ρ : G →* GeneralLinearGroup (Fin 2) F) (i : ℕ) (σ : G) :
    (detTwist ρ i σ).val = ((ρ σ).val.det ^ i) • (ρ σ).val := by
  rw [detTwist_apply, Units.val_mul, scalarUnit_val, scalar_apply, ← smul_eq_diagonal_mul,
    Units.val_pow_eq_pow_val, GeneralLinearGroup.val_det_apply]

private theorem trace_detTwist (ρ : G →* GeneralLinearGroup (Fin 2) F) (i : ℕ) (σ : G) :
    (detTwist ρ i σ).val.trace = (ρ σ).val.det ^ i * (ρ σ).val.trace := by
  rw [detTwist_apply_val, trace_smul, smul_eq_mul]

private theorem det_detTwist (ρ : G →* GeneralLinearGroup (Fin 2) F) (i : ℕ) (σ : G) :
    (detTwist ρ i σ).val.det = (ρ σ).val.det ^ (2 * i + 1) := by
  rw [detTwist_apply_val, det_smul, Fintype.card_fin, ← pow_mul, pow_succ, mul_comm 2 i]

private theorem detTwist_apply_eq_one (ρ : G →* GeneralLinearGroup (Fin 2) F) (i : ℕ) {σ : G}
    (h : ρ σ = 1) : detTwist ρ i σ = 1 := by
  rw [detTwist_apply, h, map_one, one_pow]
  simp [scalarUnit]

private theorem detTwist_mulVec (ρ : G →* GeneralLinearGroup (Fin 2) F) (i : ℕ) (σ : G) (v : Fin 2 → F) :
    (detTwist ρ i σ).val.mulVec v = (ρ σ).val.det ^ i • (ρ σ).val.mulVec v := by
  rw [detTwist_apply_val, smul_mulVec]

private theorem detTwist_mulVec_eq_of_mulVec_eq (ρ : G →* GeneralLinearGroup (Fin 2) F) (i : ℕ) (σ : G)
    (v : Fin 2 → F) (c : F) (h : (ρ σ).val.mulVec v = c • v) :
    (detTwist ρ i σ).val.mulVec v = ((ρ σ).val.det ^ i * c) • v := by
  rw [detTwist_mulVec, h, smul_smul]

private theorem detTwist_mulVec_mem_span_iff (ρ : G →* GeneralLinearGroup (Fin 2) F) (i : ℕ) (σ : G)
    (v : Fin 2 → F) :
    (detTwist ρ i σ).val.mulVec v ∈ F ∙ v ↔ (ρ σ).val.mulVec v ∈ F ∙ v := by
  rw [detTwist_mulVec]
  constructor
  · intro h
    have hd : (ρ σ).val.det ≠ 0 := by
      rw [← GeneralLinearGroup.val_det_apply]
      exact Units.ne_zero _
    have hu : ((ρ σ).val.det ^ i) ≠ 0 := pow_ne_zero i hd
    have := Submodule.smul_mem _ (((ρ σ).val.det ^ i)⁻¹) h
    rwa [smul_smul, inv_mul_cancel₀ hu, one_smul] at this
  · intro h
    exact Submodule.smul_mem _ _ h

private theorem factorsThroughFiniteLevel_detTwist {F : Type} [Field F]
    (ρ : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) →* GeneralLinearGroup (Fin 2) F) (j : ℕ)
    (h : GaloisFactorsThroughFiniteLevel ρ) : GaloisFactorsThroughFiniteLevel (detTwist ρ j) := by
  obtain ⟨L, hL, h1⟩ := h
  exact ⟨L, hL, fun σ hσ => detTwist_apply_eq_one ρ j (h1 σ hσ)⟩

end Twist

section Model

open Matrix
open scoped TensorProduct

private theorem exists_matrix_model {F : Type} [Field F] (R : ResidualGaloisRep F) :
    ∃ (b : Module.Basis (Fin 2) F R.V)
      (ρ : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) →* GeneralLinearGroup (Fin 2) F),
      (∀ σ, (ρ σ).val = LinearMap.toMatrix b b (R.ρ σ)) ∧ GaloisFactorsThroughFiniteLevel ρ := by
  let b : Module.Basis (Fin 2) F R.V := Module.finBasisOfFinrankEq F R.V R.finrank_eq
  let e : Module.End F R.V ≃* Matrix (Fin 2) (Fin 2) F := (LinearMap.toMatrixAlgEquiv b).toMulEquiv
  let ρ : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) →* GeneralLinearGroup (Fin 2) F :=
    (Units.map e.toMonoidHom).comp R.ρ.toHomUnits
  have hval : ∀ σ, (ρ σ).val = LinearMap.toMatrix b b (R.ρ σ) := fun σ => rfl
  refine ⟨b, ρ, hval, ?_⟩
  obtain ⟨L, hL, h1⟩ := R.factorsThroughFiniteLevel
  refine ⟨L, hL, fun σ hσ => Units.ext ?_⟩
  rw [hval, h1 σ hσ, Units.val_one, LinearMap.toMatrix_one b]

private theorem trace_toMatrix_eq {F : Type} [Field F] (R : ResidualGaloisRep F)
    (b : Module.Basis (Fin 2) F R.V) (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) :
    (LinearMap.toMatrix b b (R.ρ σ)).trace = LinearMap.trace F R.V (R.ρ σ) :=
  (LinearMap.trace_eq_matrix_trace F b (R.ρ σ)).symm

private theorem det_toMatrix_eq {F : Type} [Field F] (R : ResidualGaloisRep F)
    (b : Module.Basis (Fin 2) F R.V) (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) :
    (LinearMap.toMatrix b b (R.ρ σ)).det = LinearMap.det (R.ρ σ) :=
  LinearMap.det_toMatrix b (R.ρ σ)

private theorem trace_baseChangeAlong {k F : Type} [Field k] [Field F] (φ : k →+* F)
    (R : ResidualGaloisRep k) (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) :
    LinearMap.trace F (R.baseChangeAlong φ).V ((R.baseChangeAlong φ).ρ σ) =
      φ (LinearMap.trace k R.V (R.ρ σ)) := by
  letI : Algebra k F := φ.toAlgebra
  change LinearMap.trace F (F ⊗[k] R.V) ((R.ρ σ).baseChange F) = φ (LinearMap.trace k R.V (R.ρ σ))
  rw [LinearMap.trace_baseChange]
  rfl

private theorem det_baseChangeAlong {k F : Type} [Field k] [Field F] (φ : k →+* F)
    (R : ResidualGaloisRep k) (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) :
    LinearMap.det ((R.baseChangeAlong φ).ρ σ) = φ (LinearMap.det (R.ρ σ)) := by
  letI : Algebra k F := φ.toAlgebra
  change LinearMap.det ((R.ρ σ).baseChange F) = φ (LinearMap.det (R.ρ σ))
  rw [LinearMap.det_baseChange]
  rfl

end Model

section CurveSide

open WeierstrassCurve WeierstrassCurve.Affine
open scoped WeierstrassCurve.Affine
open Matrix

private theorem isElliptic_map_of_Δ_ne_zero (W : WeierstrassCurve ℤ) (hΔ : W.Δ ≠ 0) :
    (W.map (Int.castRingHom ℚ)).IsElliptic := by
  refine ⟨?_⟩
  rw [WeierstrassCurve.map_Δ, isUnit_iff_ne_zero]
  simpa using hΔ

private theorem exists_card_and_level (p : ℕ) [hp : Fact p.Prime] (W : WeierstrassCurve ℤ) (hΔ : W.Δ ≠ 0) :
    ∃ (_ : Nat.card (Submodule.torsionBy ℤ
          ((W.map (Int.castRingHom ℚ))⁄(AlgebraicClosure ℚ)).Point p) = p ^ 2),
      GaloisFactorsThroughFiniteLevel
        (Point.galoisRepModuleEnd (K := AlgebraicClosure ℚ) ℚ (W.map (Int.castRingHom ℚ)) p) := by
  classical
  haveI : (W.map (Int.castRingHom ℚ)).IsElliptic := isElliptic_map_of_Δ_ne_zero W hΔ
  haveI : ((W.map (Int.castRingHom ℚ))⁄(AlgebraicClosure ℚ)).IsElliptic :=
    inferInstanceAs ((W.map (Int.castRingHom ℚ)).map (algebraMap ℚ (AlgebraicClosure ℚ))).IsElliptic
  refine ⟨WeierstrassCurve.card_torsionBy_eq_sq_of_isAlgClosed
      ((W.map (Int.castRingHom ℚ)).baseChange (AlgebraicClosure ℚ))
      (Nat.cast_ne_zero.mpr hp.out.ne_zero) two_ne_zero, ?_⟩
  exact WeierstrassCurve.galoisRepModuleEnd_factorsThroughFiniteLevel (W.map (Int.castRingHom ℚ)) p

private theorem exists_curve_matrix_rep (p : ℕ) [hp : Fact p.Prime] (W : WeierstrassCurve ℤ) (hΔ : W.Δ ≠ 0)
    (K : Type) [Field K] [CharP K p] :
    ∃ ρ : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) →* GeneralLinearGroup (Fin 2) K,
      GaloisFactorsThroughFiniteLevel ρ ∧
      ∀ ℓ : ℕ, ℓ.Prime → ℓ ≠ p → W.IsGoodPrimeFor ℓ →
        ∀ A : ValuationSubring (AlgebraicClosure ℚ), A.LiesOverPrime ℓ →
          ∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, A.IsFrobeniusAt σ ℓ →
            (ρ σ).val.trace = ((W.apOfModel ℓ : ℤ) : K) ∧ (ρ σ).val.det = (ℓ : K) := by
  obtain ⟨hcard, hker⟩ := exists_card_and_level p W hΔ
  set R := ((W.map (Int.castRingHom ℚ)).residualGaloisRepOf p hcard hker).baseChangeAlong
    (ZMod.castHom (dvd_refl p) K) with hR
  obtain ⟨b, ρ, hρ, hlevel⟩ := exists_matrix_model R
  refine ⟨ρ, hlevel, fun ℓ hℓ hℓp hgood A hA σ hσ => ⟨?_, ?_⟩⟩
  · rw [hρ, trace_toMatrix_eq, hR, trace_baseChangeAlong]
    change ZMod.castHom (dvd_refl p) K
      (Point.galoisTrace (K := AlgebraicClosure ℚ) ℚ (W.map (Int.castRingHom ℚ)) p σ) = _
    rw [WeierstrassCurve.galoisTrace_frobenius_eq_apOfModel W p ℓ hp.out hℓ hℓp hgood A hA σ hσ,
      map_intCast]
  · rw [hρ, det_toMatrix_eq, hR, det_baseChangeAlong]
    change ZMod.castHom (dvd_refl p) K
      (LinearMap.det (Point.galoisRepModuleEnd (K := AlgebraicClosure ℚ) ℚ (W.map (Int.castRingHom ℚ)) p σ)) = _
    rw [WeierstrassCurve.det_galoisRep_frobenius_eq_prime W p ℓ hp.out hℓ hℓp hgood A hA σ hσ,
      map_natCast]

end CurveSide

section Glue

open Matrix

private theorem exists_common_level {K : Type} [Field K]
    (ρ₁ ρ₂ : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) →* GeneralLinearGroup (Fin 2) K)
    (h₁ : GaloisFactorsThroughFiniteLevel ρ₁) (h₂ : GaloisFactorsThroughFiniteLevel ρ₂) (S : Finset ℕ)
    (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) :
    ∃ (ℓ : ℕ) (A : ValuationSubring (AlgebraicClosure ℚ)) (τ g : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ),
      ℓ.Prime ∧ ℓ ∉ S ∧ A.LiesOverPrime ℓ ∧ A.IsFrobeniusAt τ ℓ ∧
        g * τ * g⁻¹ * σ⁻¹ ∈
          ((Units.coeHom (Matrix (Fin 2) (Fin 2) K)).comp ρ₁).ker ⊓
            ((Units.coeHom (Matrix (Fin 2) (Fin 2) K)).comp ρ₂).ker := by
  obtain ⟨L₁, hL₁, hρ₁⟩ := h₁
  obtain ⟨L₂, hL₂, hρ₂⟩ := h₂
  haveI : FiniteDimensional ℚ (↥(L₁ ⊔ L₂)) := IntermediateField.finiteDimensional_sup L₁ L₂
  set M : IntermediateField ℚ (AlgebraicClosure ℚ) :=
    IntermediateField.normalClosure ℚ (↥(L₁ ⊔ L₂)) (AlgebraicClosure ℚ) with hMdef
  haveI hfdM : FiniteDimensional ℚ M := by
    rw [hMdef]; exact normalClosure.is_finiteDimensional ℚ (↥(L₁ ⊔ L₂)) (AlgebraicClosure ℚ)
  haveI hnM : Normal ℚ M := by
    rw [hMdef]; exact normalClosure.normal ℚ (↥(L₁ ⊔ L₂)) (AlgebraicClosure ℚ)
  haveI hfd : @FiniteDimensional ℚ M _ _ (DivisionRing.toRatAlgebra).toModule := by convert hfdM
  haveI hn : @Normal ℚ M _ _ DivisionRing.toRatAlgebra := by convert hnM
  haveI hnf : NumberField M := ⟨⟩
  haveI hg : @IsGalois ℚ _ M _ DivisionRing.toRatAlgebra := { }
  have hle : L₁ ⊔ L₂ ≤ M := by rw [hMdef]; exact IntermediateField.le_normalClosure (L₁ ⊔ L₂)
  refine FrobeniusDensity.exists_isFrobeniusAt_conj_mem_of_le_ker M ?_ S σ
  intro γ hγ
  rw [MonoidHom.mem_ker] at hγ
  have hfix : ∀ x ∈ M, γ x = x := by
    intro x hx
    have h2 := congrArg (fun e : (M ≃ₐ[ℚ] M) => ((e ⟨x, hx⟩ : M) : AlgebraicClosure ℚ)) hγ
    simp only [AlgEquiv.one_apply] at h2
    refine Eq.trans ?_ h2
    convert (AlgEquiv.restrictNormalHom_apply M γ ⟨x, hx⟩).symm
    rfl
  refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
  · rw [MonoidHom.mem_ker, MonoidHom.comp_apply,
      hρ₁ γ (fun x hx => hfix x (hle (le_sup_left (a := L₁) (b := L₂) hx)))]
    rfl
  · rw [MonoidHom.mem_ker, MonoidHom.comp_apply,
      hρ₂ γ (fun x hx => hfix x (hle (le_sup_right (a := L₁) (b := L₂) hx)))]
    rfl

private theorem natCast_pow_eq_of_charP {K F : Type} [Field K] [Field F] (p : ℕ) [Fact p.Prime]
    [CharP K p] [CharP F p] (ℓ a b : ℕ) (h : (ℓ : K) ^ a = (ℓ : K) ^ b) : (ℓ : F) ^ a = (ℓ : F) ^ b := by
  have h' : ((ℓ ^ a : ℕ) : K) = ((ℓ ^ b : ℕ) : K) := by push_cast; exact h
  have hmod := (CharP.natCast_eq_natCast K p).mp h'
  have h'' : ((ℓ ^ a : ℕ) : F) = ((ℓ ^ b : ℕ) : F) := (CharP.natCast_eq_natCast F p).mpr hmod
  push_cast at h''
  exact h''

end Glue

private theorem congruence_of_field (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2) (W : WeierstrassCurve ℤ) (hΔ : W.Δ ≠ 0)
    (N' : ℕ) [NeZero N'] (hpN' : ¬ p ∣ N') (S₀ : Set ℕ) (hS₀fin : S₀.Finite) (hS₀p : p ∈ S₀)
    (k' : ℤ) (i : ℕ) (kn : ℕ) (hkn : (kn : ℤ) = k')
    (K : Type) [Field K] [CharP K p] (θ : CuspForm.heckeAlgebra N' k' S₀ →+* K)
    (hθocc : ∀ (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓS : ℓ ∉ S₀) (hℓN : ¬ ℓ ∣ N'), W.IsGoodPrimeFor ℓ →
      θ (CuspForm.heckeAlgebra.T hℓ hℓN hℓS) = ((ℓ ^ i * W.apOfModel ℓ : ℤ) : K)) :
    ∀ ℓ : ℕ, ℓ.Prime → ℓ ∉ S₀ → ¬ ℓ ∣ N' → W.IsGoodPrimeFor ℓ →
      (ℓ : K) ^ (1 + 2 * i) = (ℓ : K) ^ (kn - 1) := by
  classical

  obtain ⟨ρ₁, hlev₁, htr₁, hdet₁⟩ :=
    GaloisRep.exists_galoisFactorsThroughFiniteLevel_trace_eq_theta_heckeT_and_det_eq_pow
      p N' hpN' S₀ hS₀fin k' kn hkn K θ

  obtain ⟨ρW, hlevW, hW⟩ := exists_curve_matrix_rep p W hΔ K
  let ρ₂ := detTwist ρW i
  have hlev₂ : GaloisFactorsThroughFiniteLevel ρ₂ := factorsThroughFiniteLevel_detTwist ρW i hlevW

  let S : Finset ℕ := hS₀fin.toFinset ∪ N'.primeFactors ∪ W.Δ.natAbs.primeFactors

  have htr : ∀ ℓ : ℕ, ℓ.Prime → ℓ ∉ S →
      ∀ A : ValuationSubring (AlgebraicClosure ℚ), A.LiesOverPrime ℓ →
        ∀ τ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, A.IsFrobeniusAt τ ℓ →
          ((Units.coeHom (Matrix (Fin 2) (Fin 2) K)).comp ρ₁ τ).trace =
            ((Units.coeHom (Matrix (Fin 2) (Fin 2) K)).comp ρ₂ τ).trace := by
    intro ℓ hℓ hℓS' A hA τ hτ
    simp only [S, Finset.mem_union, not_or, Set.Finite.mem_toFinset, Nat.mem_primeFactors] at hℓS'
    obtain ⟨⟨hℓS₀, hℓN'⟩, hℓΔ⟩ := hℓS'
    have hℓN : ¬ ℓ ∣ N' := fun h => hℓN' ⟨hℓ, h, NeZero.ne N'⟩
    have hgood : W.IsGoodPrimeFor ℓ := fun h =>
      hℓΔ ⟨hℓ, Int.ofNat_dvd_left.mp h, Int.natAbs_ne_zero.mpr hΔ⟩
    have hℓp : ℓ ≠ p := fun h => hℓS₀ (h ▸ hS₀p)

    have hθ := hθocc ℓ hℓ hℓS₀ hℓN hgood
    obtain ⟨hWtr, hWdet⟩ := hW ℓ hℓ hℓp hgood A hA τ hτ
    simp only [MonoidHom.comp_apply, Units.coeHom_apply]
    rw [htr₁ ℓ hℓ hℓN hℓS₀ hℓp A hA τ hτ, hθ, trace_detTwist, hWdet, hWtr]
    push_cast
    ring

  have hdet : ∀ τ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ,
      ((Units.coeHom (Matrix (Fin 2) (Fin 2) K)).comp ρ₁ τ).det =
        ((Units.coeHom (Matrix (Fin 2) (Fin 2) K)).comp ρ₂ τ).det :=
    MonoidHom.det_eq_of_trace_eq_of_exists_isFrobeniusAt_conj p hp2 K _ _ S
      (exists_common_level ρ₁ ρ₂ hlev₁ hlev₂ S) htr

  intro ℓ hℓ hℓS hℓN hgood
  have hℓp : ℓ ≠ p := fun h => hℓS (h ▸ hS₀p)
  obtain ⟨A, τ, hA, hτ⟩ := ValuationSubring.exists_liesOverPrime_isFrobeniusAt_ratAlgClosure ⟨ℓ, hℓ⟩
  have h₁ : ((ρ₁ τ).val).det = (ℓ : K) ^ (kn - 1) := hdet₁ ℓ hℓ hℓN hℓS hℓp A hA τ hτ
  have h₂ : ((ρ₂ τ).val).det = (ℓ : K) ^ (2 * i + 1) := by
    rw [det_detTwist, (hW ℓ hℓ hℓp hgood A hA τ hτ).2]
  have hK : (ℓ : K) ^ (1 + 2 * i) = (ℓ : K) ^ (kn - 1) := by
    have h := hdet τ
    simp only [MonoidHom.comp_apply, Units.coeHom_apply] at h
    rw [h₁, h₂] at h
    rw [Nat.add_comm]
    exact h.symm
  exact hK

end WLightCong

open WLightCong in

theorem solution
    (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2) (W : WeierstrassCurve ℤ)
    (hΔ : W.Δ ≠ 0)
    (N' : ℕ) [NeZero N'] (hpN' : ¬ p ∣ N')
    (S₀ : Set ℕ) (hS₀fin : S₀.Finite) (hS₀p : p ∈ S₀)
    (k' : ℤ) (i : ℕ)
    (𝔪' : Ideal (CuspForm.heckeAlgebra N' k' S₀)) (h𝔪' : 𝔪'.IsMaximal)
    (hp𝔪' : (p : CuspForm.heckeAlgebra N' k' S₀) ∈ 𝔪')
    (hocc : ∀ (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓS : ℓ ∉ S₀) (hℓN : ¬ ℓ ∣ N'),
      W.IsGoodPrimeFor ℓ →
        CuspForm.heckeAlgebra.T hℓ hℓN hℓS -
          ((ℓ ^ i * W.apOfModel ℓ : ℤ) : CuspForm.heckeAlgebra N' k' S₀) ∈ 𝔪')
    (F : Type) [Field F] [CharP F p]
    (kn : ℕ) (hkn : (kn : ℤ) = k') :
    ∀ ℓ : ℕ, ℓ.Prime → ℓ ∉ S₀ → ¬ ℓ ∣ N' → W.IsGoodPrimeFor ℓ →
      (ℓ : F) ^ (1 + 2 * i) = (ℓ : F) ^ (kn - 1) := by
  classical
  haveI : 𝔪'.IsMaximal := h𝔪'
  letI : Field (CuspForm.heckeAlgebra N' k' S₀ ⧸ 𝔪') := Ideal.Quotient.field 𝔪'
  haveI hKp : CharP (CuspForm.heckeAlgebra N' k' S₀ ⧸ 𝔪') p :=
    (CharP.charP_iff_prime_eq_zero (Fact.out : p.Prime)).mpr
      ((Ideal.Quotient.eq_zero_iff_mem (I := 𝔪') (a := (p : CuspForm.heckeAlgebra N' k' S₀))).mpr hp𝔪')
  have hθocc : ∀ (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓS : ℓ ∉ S₀) (hℓN : ¬ ℓ ∣ N'), W.IsGoodPrimeFor ℓ →
      Ideal.Quotient.mk 𝔪' (CuspForm.heckeAlgebra.T hℓ hℓN hℓS) =
        ((ℓ ^ i * W.apOfModel ℓ : ℤ) : CuspForm.heckeAlgebra N' k' S₀ ⧸ 𝔪') := by
    intro ℓ hℓ hℓS hℓN hgood
    rw [← map_intCast (Ideal.Quotient.mk 𝔪'), Ideal.Quotient.eq]
    exact hocc ℓ hℓ hℓS hℓN hgood
  intro ℓ hℓ hℓS hℓN hgood
  exact natCast_pow_eq_of_charP p ℓ _ _
    (congruence_of_field p hp2 W hΔ N' hpN' S₀ hS₀fin hS₀p k' i kn hkn _ (Ideal.Quotient.mk 𝔪') hθocc
      ℓ hℓ hℓS hℓN hgood)

end

end S_CuspForm_heckeAlgebra_natCast_pow_twist_eq_natCast_pow_weight_sub_one_of_twist_mem
end P2MW
export P2MW.S_CuspForm_heckeAlgebra_natCast_pow_twist_eq_natCast_pow_weight_sub_one_of_twist_mem (solution)
