-- Prove2me | solution 1 for CuspForm.heckeAlgebra.exists_ringHom_apply_T_eq_of_insert_of_residue_eq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.805612+00:00
-- url     : https://prove2.me/submissions/c4012efb-045e-509c-94d1-5baf09a505dc

import Theorems.Thm_CuspForm_exists_mem_heckeAlgebra_insert_heckeTLin_eq_add_smul_of_ne
import Theorems.Thm_CuspForm_hasIntegralStructure_two
import Theorems.Thm_CuspForm_moduleFinite_heckeAlgebra_two
import Definitions.Def_CuspForm_HeckeAlgebra
import Mathlib.RingTheory.DiscreteValuationRing.Basic
import Mathlib.RingTheory.AdicCompletion.Basic
import Mathlib.RingTheory.LocalRing.ResidueField.Basic
import Mathlib.RingTheory.Finiteness.Nakayama
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CuspForm_heckeAlgebra_exists_ringHom_apply_T_eq_of_insert_of_residue_eq
p2m_attr_erase "instance" "ModularCurve.instSMulAlgEquivRatPic0SubtypeLaurentSeriesMemIntermediateFieldLaurentBaseChange ModularCurve.instDistribMulActionAlgEquivRatPic0SubtypeLaurentSeriesMemIntermediateFieldLaurentBaseChange AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupDivisor AlgebraicCurve.Pic0.instModuleZModTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instDistribMulActionTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instSMulTorsion AlgebraicCurve.SemilinearAut.instMulActionSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instSMulCommClassZModTorsion AlgebraicCurve.SemilinearAut.instMulSemiringActionSubtypeProdRingAutMemSubgroup AlgebraicCurve.Place.instIsScalarTowerSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Divisor.instDistribMulActionAlgEquiv AlgebraicCurve.Place.instSMulAlgEquiv AlgebraicCurve.Place.instIsPrincipalIdealRingSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Place.instIsDiscreteValuationRingSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Pic0.instDistribMulActionAlgEquiv AlgebraicCurve.Place.instAlgebraSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Place.instMulActionAlgEquiv AlgebraicCurve.Pic0.instSMulAlgEquiv instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy TateModule.instModule TateModule.instSMul GaloisRepAdic.instAddCommGroup GaloisRepAdic.instFree GaloisRepAdic.instFinite GaloisRepAdic.instModule ResidualGaloisRep.instModule ResidualGaloisRep.instModuleFinite ResidualGaloisRep.instAddCommGroup AlgebraicCurve.instFundamentalIdentityOfSumRamificationInertia AlgebraicCurve.Place.instIsScalarTowerResidueFieldRestrictPushforward AlgebraicCurve.Place.instAlgebraResidueFieldRestrictPushforward"
p2m_attr_erase "instance" "AlgebraicCurve.Place.instIsLocalHomRestrictInclusion ValuationSubring.instIsAlgClosedResidueField AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue ModularCurve.PhiGen.instNeZeroPhiGenCosetA AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions ModularCurve.instIsDomainTensorProduct AlgebraicClosure.Rat.isGalois ModularCurve.instAlgebraJLineBar ModularCurve.instModuleJLineBar AlgebraicCurve.instHasLocalResidue_of_hasCanonicalLocalResidueK AlgebraicCurve.instHasCanonicalLocalResidueK_of_hasCanonicalLocalResidueKStar AlgebraicCurve.Place.kw_ffgc_finiteDimensional_adicCompletion instAlgebraSubtypeMemValuationSubring_definitions AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersIntegersCompletion ModularCurve.KwF4gRRTate.instAlgebraKAdicCompletionIntegers AlgebraicCurve.Place.kw_ffgc_continuousSMul_adicCompletionComap AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersCompletionCompletion IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions AlgebraicCurve.instHasCanonicalLocalResidueK AlgebraicCurve.Place.instAlgebra_restrictResidueField AlgebraicCurve.Place.instIsScalarTower_restrictResidueField AlgebraicCurve.instHasLocalResidue AlgebraicCurve.HasSeparableResidue.of_perfectField_of_isCurveOver AlgebraicCurve.HasSeparableResidue.of_perfectField AlgebraicCurve.Place.instIsLocalHom_restrictSubringHom"
p2m_attr_erase "instance" "AlgebraicCurve.instHasCanonicalLocalResidueKStar ModularCurve.KwNo6Pin.isLocalRing_completion ModularCurve.Gamma0Pair.isElliptic WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly WeierstrassCurve.Affine.instIsScalarTowerPolynomialRatFuncFunctionField_definitions WeierstrassCurve.Affine.instAlgebraRatFuncFunctionField_definitions WeierstrassCurve.Affine.instIsScalarTowerRatFuncFunctionField_definitions WeierstrassCurve.Affine.CoordinateRing.moduleFinite WeierstrassCurve.Affine.instDecidableEqFunctionField WeierstrassCurve.Affine.CoordinateRing.isIntegral ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid ModularCurve.TatePoint.instIsElliptic_nearCurve ModularCurve.instIsElliptic_tateLaurent ModularCurve.B3.instIsElliptic_goodModel ModularCurve.instIsScalarTowerJAdjoin WeierstrassCurve.VeluQuotientJGates.instIsElliptic27a4 ModularCurve.ElevenA1.instDecidableEquation ModularCurve.ElevenA1.instDecidableNonsingular ModularCurve.CuspSpace.instNonempty ModularCurve.CuspSpace.instSubsingletonOfOne ModularCurve.CuspSpace.instFinite ModularCurve.instAlgebraIntermediateFieldLaurent ModularCurve.instIsScalarTowerKaehlerIntermediateFieldLaurent ModularCurve.instIsScalarTowerIntermediateFieldLaurent ModularCurve.instModuleKaehlerIntermediateFieldLaurent FLT.Gamma0FundamentalSet.instContinuousConstSMulSpecialLinearGroupFinOfNatNatIntUpperHalfPlane_definitions FLT.HyperbolicMeasure.instSMulInvariantMeasureSpecialLinearGroupFinOfNatNatIntUpperHalfPlaneVolume_definitions FLT.HyperbolicMeasure.instIsOpenPosMeasureUpperHalfPlaneVolume_definitions FLT.L2ProductionInstance.isFiniteMeasure_gamma0 FLT.L2ProductionInstance.countable_SL2Z FLT.L2ProductionInstance.countable_quotient FLT.L2ProductionInstance.nontrivial_gamma0L2 HeckeEis.instModuleCoeffH1par HeckeEis.instAddCommGroupCoeffH1par HeckeEis.instFiniteIndexHeckeUpper FrobeniusDensity.isMaximal_ratPrimeIdeal"
p2m_attr_erase "instance" "FrobeniusDensity.liesOver_ratBelow ModularCurve.Period.parabolicHoms_int_moduleFinite ModularCurve.Period.instGroupFG_SL2Z ModularCurve.Period.instIsNoetherian_addHom_int ModularCurve.Period.instGroupFG_Gamma0"
p2m_attr_erase "simp" "ModularCurve.baseAut_arithmeticGalois ModularCurve.JZero.torsionGaloisRep_apply ModularCurve.coe_arithmeticRingAut_apply ModularCurve.toRingAut_arithmeticGalois ModularCurve.qExpand_coeff_mul ModularCurve.qExpandₐ_apply ModularCurve.jqN_one ModularCurve.qExpand_single ModularCurve.dedekindPsi_one ModularCurve.ModularPolynomialData.mk.sizeOf_spec ModularCurve.evalAtJ_X ModularCurve.ModularPolynomialData.mk.injEq ModularCurve.constantCoeff_jNum ModularCurve.constantCoeff_eisenstein4 ModularCurve.qExpand_C ModularCurve.coeff_jq_neg_one ModularCurve.constantCoeff_jNumQ ModularCurve.coeffEmb_coeff ModularCurve.coeffMap_coeff ModularCurve.coeffMap_id ModularCurve.coeffMap_single AlgebraicCurve.SemilinearAut.toRingAut_inv AlgebraicCurve.SemilinearAut.smul_def AlgebraicCurve.SemilinearAut.smul_single AlgebraicCurve.SemilinearAut.smul_toValuationSubring AlgebraicCurve.SemilinearAut.baseAut_inv AlgebraicCurve.SemilinearAut.baseAut_ofAlgAut AlgebraicCurve.SemilinearAut.toRingAut_ofAlgAut AlgebraicCurve.SemilinearAut.torsionRep_apply AlgebraicCurve.SemilinearAut.toRingAut_one AlgebraicCurve.SemilinearAut.deg_smul AlgebraicCurve.SemilinearAut.degree_smul AlgebraicCurve.SemilinearAut.coe_degZeroSMulHom AlgebraicCurve.SemilinearAut.baseAut_mul AlgebraicCurve.SemilinearAut.coe_smulValuationSubringEquiv_apply AlgebraicCurve.SemilinearAut.baseAut_one AlgebraicCurve.SemilinearAut.ofAlgAut_smul AlgebraicCurve.SemilinearAut.coe_torsion_smul AlgebraicCurve.SemilinearAut.toRingAut_mul AlgebraicCurve.Place.mk.injEq"
p2m_attr_erase "simp" "AlgebraicCurve.Divisor.degree_single AlgebraicCurve.Divisor.smul_single AlgebraicCurve.Place.smul_toValuationSubring AlgebraicCurve.Place.heightOneSpectrum_asIdeal AlgebraicCurve.Place.coe_algebraMap AlgebraicCurve.Place.ord_one AlgebraicCurve.Place.coe_smulRingEquiv_apply AlgebraicCurve.Pic0.coe_degZeroSMulHom AlgebraicCurve.Place.deg_smul AlgebraicCurve.Pic0.mk_zero AlgebraicCurve.Place.mk.sizeOf_spec AlgebraicCurve.Divisor.degree_smul AlgebraicCurve.Pic0.mk_add AlgebraicCurve.Place.ord_zero AlgebraicCurve.Place.ofHeightOneSpectrum_toValuationSubring ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd FreyPackage.mk.sizeOf_spec FreyPackage.mk.injEq WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply TateModule.smul_apply TateModule.coe_mulP TateModule.proj_apply TateModule.coe_add TateModule.coe_sub WeierstrassCurve.tateModuleRepOfBasis_V TateModule.coe_zero TateModule.rep_apply WeierstrassCurve.tateModuleRep_V WeierstrassCurve.tateModuleRepOfBasis_ρ_apply GaloisRep.padicIntToRingLevel_apply TateModule.coe_neg WeierstrassCurve.tateModuleRep_ρ_apply GaloisRepAdic.mk.injEq GaloisRepAdic.mk.sizeOf_spec GaloisRepAdic.Equiv.mk.sizeOf_spec GaloisRepAdic.Equiv.mk.injEq ResidualGaloisRep.mk.sizeOf_spec"
p2m_attr_erase "simp" "ResidualGaloisRep.mk.injEq ResidualGaloisRep.Equiv.mk.sizeOf_spec ResidualGaloisRep.Equiv.mk.injEq ModularCurve.coe_heckeBetaBarRingHom ModularCurve.coe_heckeBetaBar ModularCurve.coe_heckeAlphaBar AlgebraicCurve.Divisor.degree_pushforwardAlong AlgebraicCurve.Pic0.coe_degZeroCorrespondence AlgebraicCurve.Place.mem_fiberAlong AlgebraicCurve.Divisor.mapRestrict_single AlgebraicCurve.Divisor.pushforward_single AlgebraicCurve.Place.coe_restrictInclusion AlgebraicCurve.Place.mem_fiber AlgebraicCurve.Place.restrict_toValuationSubring AlgebraicCurve.Divisor.degree_pushforward AlgebraicCurve.Place.restrictResidueMap_residue AlgebraicCurve.Pic0.coe_pushforwardDegZeroHom AlgebraicCurve.Pic0.coe_pullbackDegZeroHom ModularCurve.dualHeckeRep_apply_apply ModularCurve.coe_segmentPath ModularCurve.cuspHeckeAeval_heckeGen ModularCurve.coe_periodLatticeRestrict_apply ModularCurve.reductionDivAlong_apply ModularCurve.coe_reductionDegZeroAlong ModularCurve.qExpandAlgHomC_apply ModularCurve.jqNModC_one ModularCurve.coe_frobeniusModL ModularCurve.coe_frobeniusDegZeroPullbackModL ModularCurve.coe_frobeniusDegZeroPushforwardModL WeierstrassCurve.reducePoint_zero WeierstrassCurve.Affine.Point.galoisRep_apply ValuationSubring.reduceAt_coe ValuationSubring.reduceAt_one ValuationSubring.reduceAt_natCast ValuationSubring.reduceAt_intCast ValuationSubring.reduceAt_zero AlgebraicCurve.ConstantReduction.mk.injEq AlgebraicCurve.ConstantReduction.mk.sizeOf_spec AlgebraicCurve.ConstantReduction.divMap_apply AlgebraicCurve.ConstantReduction.coe_degZeroMap"
p2m_attr_erase "simp" "ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.reduceModBivar_C_X"
p2m_attr_erase "simp" "ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.coe_towerInclBar ModularCurve.coe_towerSubstBar AlgebraicCurve.ConstantReduction.toRegularProlongation_residue AlgebraicCurve.RegularProlongation.mk.sizeOf_spec AlgebraicCurve.ConstantReduction.toRegularProlongation_integers AlgebraicCurve.RegularProlongation.mk.injEq AlgebraicCurve.mulAdele_apply AlgebraicCurve.residuePairing_apply_coe AlgebraicCurve.mem_adeleBdd AlgebraicCurve.weilSmul_one AlgebraicCurve.diagonalHom_apply AlgebraicCurve.weilSmul_apply AlgebraicCurve.adeleSpaceMul_coe AlgebraicCurve.mulAdele_one AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.injEq AlgebraicCurve.TranscendenceTower.mk.injEq AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec AlgebraicCurve.PoleDivisorPackage.mk.injEq AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.Place.differentialCoeff_zero AlgebraicCurve.Place.differentialCoeff_dCoord AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none ModularCurve.cuspCount_one ModularCurve.coe_uniformizerMod ModularCurve.qSeriesBar_jModElt ModularCurve.qInftyPlaceMod_toValuationSubring ModularCurve.qInftyPlaceBar_toValuationSubring"
p2m_attr_erase "simp" "ModularCurve.qSeriesBar_zero ModularCurve.qSeriesBar_add ModularCurve.cuspInftyFull_toValuationSubring ModularCurve.qInftyPlaceRat_toValuationSubring ModularCurve.qSeriesBar_mul ModularCurve.qSeriesBar_div ModularCurve.qSeriesBar_eq_zero_iff ModularCurve.coe_uniformizerBar ModularCurve.qSeriesBar_pow ModularCurve.cuspInfty_toValuationSubring ModularCurve.qSeriesBar_one ModularCurve.qSeriesBar_inv ModularCurve.qSeriesBar_sub ModularCurve.qSeriesBar_neg ModularCurve.coe_cuspidalDivisor₀ ModularCurve.coe_baseChangeEquiv_apply ModularCurve.baseChangeHom_tmul ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.sizeOf_spec AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.injEq AlgebraicCurve.adeleSingle_coe AlgebraicCurve.kaehlerResidueTermKFam_apply AlgebraicCurve.Place.LocalResidueData.mk.injEq AlgebraicCurve.Place.LocalResidueData.mk.sizeOf_spec AlgebraicCurve.Place.kw_ffgc_adicCompletionComapIntegers_coe AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.sizeOf_spec AlgebraicCurve.Place.mem_simplePoleSubmodule AlgebraicCurve.Place.coe_uniformizerSubring ModularCurve.Lg37.Lg37CompletionSection.mk.injEq AlgebraicCurve.Place.CoefficientFieldSection.mk.injEq AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.injEq ModularCurve.Lg37.Lg37CompletionSection.mk.sizeOf_spec AlgebraicCurve.Place.CoefficientFieldSection.mk.sizeOf_spec"
p2m_attr_erase "simp" "AlgebraicCurve.Place.poleSubmodule_one AlgebraicCurve.Place.mem_poleSubmodule HahnSeries.ramScale_apply ModularCurve.gamma0PairMap_gen ModularCurve.moduliPointMapRingHom_mk ModularCurve.Gamma0Pair.mk.injEq ModularCurve.ModuliPoint.j_mk ModularCurve.Gamma0Pair.mk.sizeOf_spec ModularCurve.gamma0PairMap_toCurve WeierstrassCurve.Affine.vcY_vcYInv WeierstrassCurve.Affine.vcXInv_vcX WeierstrassCurve.Affine.Point.vcFun_zero WeierstrassCurve.Affine.vcX_vcXInv WeierstrassCurve.Affine.vcYInv_vcY WeierstrassCurve.Affine.Point.vcInvFun_zero WeierstrassCurve.ratPointHom_apply WeierstrassCurve.ratPointMap_zero compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two"
p2m_attr_erase "simp" "WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two WeierstrassCurve.veluWSum_empty WeierstrassCurve.veluQuotient_a₁ WeierstrassCurve.veluQuotient_a₃ WeierstrassCurve.veluQuotient_empty WeierstrassCurve.veluTSum_empty WeierstrassCurve.veluQuotient_a₂ WeierstrassCurve.Affine.Point.coordsOrZero_some WeierstrassCurve.Affine.Point.coordsOrZero_zero WeierstrassCurve.veluQuotient2_a₂ WeierstrassCurve.veluQuotient2_a₃ WeierstrassCurve.veluQuotient2_a₁ WeierstrassCurve.veluPointMap2_zero WeierstrassCurve.Affine.IsogenyEndDatum.mk.injEq WeierstrassCurve.Affine.IsogenyHomDatum.mk.sizeOf_spec WeierstrassCurve.Affine.IsogenyHomDatum.mk.injEq WeierstrassCurve.Affine.IsogenyEndDatum.mk.sizeOf_spec AlgebraicCurve.Pic0.coe_pushforwardAlongDegZero WeierstrassCurve.Affine.pointMapOfPushforward_apply WeierstrassCurve.Affine.pointClass_zero WeierstrassCurve.Affine.pic0ToPoint_pointClass WeierstrassCurve.Affine.deg_placeOfPoint WeierstrassCurve.Affine.coe_pointDivisor WeierstrassCurve.Affine.pointEquivPlace_symm_placeOfPoint WeierstrassCurve.Affine.pointEquivPlace_apply WeierstrassCurve.Affine.genusOnePic0Equiv_symm_apply WeierstrassCurve.Affine.pointDivisor_zero WeierstrassCurve.Affine.pic0ToPoint_mk WeierstrassCurve.Affine.divisorSum_single WeierstrassCurve.Affine.genusOnePic0Equiv_apply PeriodPair.weierstrassCurve_a₆"
p2m_attr_erase "simp" "PeriodPair.weierstrassCurve_a₃ PeriodPair.weierstrassCurve_a₁ PeriodPair.ofTau_ω₂ PeriodPair.scale_ω₂ PeriodPair.ofTau_ω₁ PeriodPair.toPoint_zero PeriodPair.toPoint_of_mem PeriodPair.weierstrassCurve_a₂ PeriodPair.ofTau_lattice PeriodPair.scale_ω₁ PeriodPair.weierstrassCurve_a₄ WeierstrassCurve.Affine.ratFuncToFunctionField_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_C WeierstrassCurve.Affine.Point.yc_some WeierstrassCurve.Affine.Point.xc_some WeierstrassCurve.Affine.pointPull_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_X WeierstrassCurve.Affine.pointHom_mk_Y WeierstrassCurve.Affine.placeOf_asIdeal WeierstrassCurve.veluY_empty WeierstrassCurve.veluX_empty AddMonoid.End.DualEndData.symm_trace AddMonoid.End.dualEndData_intCast_norm AddMonoid.End.DualEndData.ofCharPoly_norm AddMonoid.End.DualEndData.mk.sizeOf_spec AddMonoid.End.DualEndData.mk.injEq AddMonoid.End.DualEndData.ofCharPoly_dual AddMonoid.End.dualEndData_intCast_dual AddMonoid.End.DualEndData.intLinComb_norm AddMonoid.End.DualEndData.ofCharPoly_trace AddMonoid.End.DualEndData.intLinComb_dual AddMonoid.End.DualEndData.symm_dual AddMonoid.End.DualEndData.intLinComb_trace AddMonoid.End.dualEndData_intCast_trace AddMonoid.End.DualEndData.symm_norm ModularCurve.ProjectiveLine.map_mk ModularCurve.tateLaurent_a₆ ModularCurve.tatePowerSeries_a₄ ModularCurve.tatePowerSeries_a₆ ModularCurve.tateLaurent_a₄"
p2m_attr_erase "simp" "ModularCurve.tatePowerSeries_a₁ ModularCurve.tatePowerSeries_a₂ ModularCurve.tatePowerSeries_a₃ WeierstrassCurve.veluQuotientOfSums_a₂ WeierstrassCurve.veluQuotientOfSums_a₁ WeierstrassCurve.veluQuotientOfSums_a₃ ModularCurve.B3.cycOfCongr_apply_coe ModularCurve.B3.cycOfTorsionBy_symm_apply_coe ModularCurve.B3.redPoint_zero ModularCurve.B3.pointAddEquivOfEq_rfl ModularCurve.B3.vcAddEquiv_apply ModularCurve.B3.scaleAddEquiv_apply ModularCurve.B3.cycOfTorsionBy_apply_coe ModularCurve.B3.val_inv_sU ModularCurve.B3.val_sU ModularCurve.B3.resO_apply HahnSeries.coeff_hahnTwist ModularCurve.HahnSpecialise.coe_specialiseCycSub CycSubOf.coe_map ModularCurve.HahnSpecialise.algebraMap_Qbar_apply ModularCurve.HahnSpecialise.resH_apply ModularCurve.HahnSpecialise.liftModel_map_subtype ModularCurve.HahnSpecialise.specialise_zero WeierstrassCurve.twoVeluCurve_a₁ WeierstrassCurve.twoVeluCurve_a₂ WeierstrassCurve.twoVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₂ WeierstrassCurve.xVeluCurve_a₁ WeierstrassCurve.map_veluU WeierstrassCurve.map_veluT WeierstrassCurve.map_veluW WeierstrassCurve.map_veluGy WeierstrassCurve.map_veluGx WeierstrassCurve.map_veluWSum_singleton WeierstrassCurve.map_veluTSum_singleton WeierstrassCurve.veluPointMap3_zero WeierstrassCurve.vcInvEmbedding_apply WeierstrassCurve.Affine.Point.netCol_one WeierstrassCurve.Affine.Point.xOrZero_zero"
p2m_attr_erase "simp" "WeierstrassCurve.Affine.Point.netPairing_zero_right WeierstrassCurve.Affine.Point.netW20_some WeierstrassCurve.Affine.Point.netCol_zero WeierstrassCurve.Affine.Point.netPairing_zero_left WeierstrassCurve.Affine.Point.xOrZero_some WeierstrassCurve.Affine.Point.netW20_zero TateCurve.cauchyMulInt_zero TateCurve.cauchyMulInt3_zero TateCurve.tent_one TateCurve.Gz_zero TateCurve.cauchyMulInt_one TateCurve.tent_zero TateCurve.Fz_zero TateCurve.xCoeffFull_succ TateCurve.a₆Coeff_zero TateCurve.a₄Coeff_succ TateCurve.a₄Coeff_zero TateCurve.cauchyMul_zero TateCurve.a₆Coeff_succ TateCurve.yCoeffFull_succ TateCurve.xCoeffFull_zero TateCurve.yCoeffFull_zero TateCurve.yfun_zero TateCurve.xfun_zero TateCurve.yTerm_zero TateCurve.xTerm_zero TateCurve.curve_a₂ TateCurve.b_one TateCurve.curve_a₁ TateCurve.term_zero TateCurve.curve_a₆ TateCurve.curve_a₄ TateCurve.curve_a₃ FLT.DivisorConvolution.sigma_zero_right FLT.DivisorConvolution.sigma_one_right FLT.DivisorConvolution.sigmaConv_one FLT.DivisorConvolution.sigmaConv_zero FormalCoordinates.mk.injEq WeierstrassCurve.formalParam_zero WeierstrassCurve.SmoothLocusReductionData.reduceHom₀_apply"
p2m_attr_erase "simp" "WeierstrassCurve.formalParam_some FormalCoordinates.mk.sizeOf_spec WeierstrassCurve.SmoothLocusReductionData.mk.injEq WeierstrassCurve.reducePointSmooth_zero WeierstrassCurve.SmoothLocusReductionData.mk.sizeOf_spec WeierstrassCurve.mem_zeroComponentSubgroup_iff ModularCurve.ComplexPlaceDictionary.mk.injEq ModularCurve.ComplexPlaceDictionary.mk.sizeOf_spec ModularCurve.Period.IsEquivariantPrimitive.periodHom_apply ModularCurve.Period.IsEquivariantPrimitive.period_one ModularCurve.CuspSpace.cuspDenomAux_infty ModularCurve.CuspSpace.cuspDenomAux_coe ModularCurve.CuspSpace.cuspDenom_mk_zero ModularCurve.CuspSpace.cuspDenom_mk_infty ModularCurve.mapGL_apply_coe ModularCurve.ratPoint_one_zero ModularCurve.ratPoint_zero_right ModularCurve.CuspSpace.fromCoset_mk ModularCurve.CuspSpace.cuspDenom_mk ModularCurve.ratPoint_zero_one ModularCurve.qEulerFun_coeff ModularCurve.diffQExp_D ModularCurve.qEulerOn_apply ModularCurve.qEuler_coeff FLT.TruncatedDomainPartition.unipotentDiagonalSum_zero HeckeEis.coeffCoboundaryMap_apply HeckeEis.heckeConjMat_apply_one_one HeckeEis.coe_heckeConjSL HeckeEis.mem_heckeUpperSL HeckeEis.resHom_apply HeckeEis.heckeConjMat_apply_zero_one HeckeEis.coe_transferAux HeckeEis.coe_heckeConj HeckeEis.alphaMat_apply_one_one HeckeEis.heckeConjMat_apply_one_zero HeckeEis.alphaMat_apply_zero_one HeckeEis.pullbackHom_apply HeckeEis.alphaMat_apply_one_zero HeckeEis.alphaMat_apply_zero_zero HeckeEis.heckeConjMat_apply_zero_zero"
p2m_attr_erase "simp" "TaylorWiles.Seed.mk.injEq TaylorWiles.Seed.mk.sizeOf_spec ModularCurve.Period.jConjMat_apply_zero_one ModularCurve.Period.jConjSL_coe ModularCurve.Period.jConjMat_apply_one_zero ModularCurve.Period.jConjMat_apply_one_one ModularCurve.Period.jConjGamma0_coe ModularCurve.Period.charInvolution_apply ModularCurve.Period.jConjMat_apply_zero_zero PowerSeries.coeff_heckeV PowerSeries.coeff_heckeU"

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 6400000

noncomputable section

open IsLocalRing CuspForm

namespace RedTr

theorem heckeAlgebra_induction (N' : ℕ) [NeZero N'] (S : Set ℕ)
    (hN'S : ∀ q : ℕ, q.Prime → q ∣ N' → q ∈ S)
    {R : Type} [Ring R] (F : heckeAlgebra N' 2 S →+* R) (B : Subring R)
    (hT : ∀ (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓN' : ¬ ℓ ∣ N') (hℓS : ℓ ∉ S),
      F (heckeAlgebra.T hℓ hℓN' hℓS) ∈ B)
    (t : heckeAlgebra N' 2 S) : F t ∈ B := by
  classical
  obtain ⟨t, ht⟩ := t
  refine Algebra.adjoin_induction (p := fun t ht => F ⟨t, ht⟩ ∈ B) ?_ ?_ ?_ ?_ ht
  · rintro x (⟨ℓ, hℓ, hℓN', hℓS, rfl⟩ | ⟨q, hqN', hq, hqS, rfl⟩)
    · exact hT ℓ hℓ hℓN' hℓS
    · exact absurd (hN'S q hq hqN') hqS
  · intro r
    have e : (⟨algebraMap ℤ _ r, algebraMap_mem _ r⟩ : heckeAlgebra N' 2 S) =
        (r : heckeAlgebra N' 2 S) := Subtype.ext (by simp)
    rw [e, map_intCast F r]
    exact intCast_mem _ r
  · intro x y hx hy hpx hpy
    have e : (⟨x + y, add_mem hx hy⟩ : heckeAlgebra N' 2 S) = ⟨x, hx⟩ + ⟨y, hy⟩ := rfl
    rw [e, RingHom.map_add]
    exact add_mem hpx hpy
  · intro x y hx hy hpx hpy
    have e : (⟨x * y, mul_mem hx hy⟩ : heckeAlgebra N' 2 S) = ⟨x, hx⟩ * ⟨y, hy⟩ := rfl
    rw [e, RingHom.map_mul]
    exact mul_mem hpx hpy

section Nakayama

variable (N : ℕ) [NeZero N] (S : Finset ℕ) (r p : ℕ)

abbrev E : Type := Module.End ℂ (CuspForm (CongruenceSubgroup.Gamma0 N) 2)

theorem le_of_insert : heckeAlgebra N 2 (↑(insert r S) : Set ℕ) ≤ heckeAlgebra N 2 (↑S : Set ℕ) :=
  heckeAlgebra_mono (by rw [Finset.coe_insert]; exact Set.subset_insert _ _)

def subA' : Submodule ℤ ↥(heckeAlgebra N 2 (↑S : Set ℕ)) where
  carrier := {v | (v : E N) ∈ heckeAlgebra N 2 (↑(insert r S) : Set ℕ)}
  add_mem' {a b} ha hb := by
    show ((a + b : heckeAlgebra N 2 (↑S : Set ℕ)) : E N) ∈ heckeAlgebra N 2 (↑(insert r S) : Set ℕ)
    exact add_mem ha hb
  zero_mem' := by
    show ((0 : heckeAlgebra N 2 (↑S : Set ℕ)) : E N) ∈ heckeAlgebra N 2 (↑(insert r S) : Set ℕ)
    exact zero_mem _
  smul_mem' c {x} hx := by
    show ((c • x : heckeAlgebra N 2 (↑S : Set ℕ)) : E N) ∈ heckeAlgebra N 2 (↑(insert r S) : Set ℕ)
    rw [Subalgebra.coe_smul]
    exact zsmul_mem hx c

theorem mem_subA' (v : heckeAlgebra N 2 (↑S : Set ℕ)) :
    v ∈ subA' N S r ↔ (v : E N) ∈ heckeAlgebra N 2 (↑(insert r S) : Set ℕ) := Iff.rfl

theorem exists_decomp (hp : p.Prime) (hr : r.Prime) (hrp : r ≠ p) (hrN : ¬ r ∣ N)
    (hrS : r ∉ (↑S : Set ℕ)) (hNS : ∀ q : ℕ, q.Prime → q ∣ N → q ∈ S)
    (x : E N) (hx : x ∈ heckeAlgebra N 2 (↑S : Set ℕ)) :
    ∃ y ∈ heckeAlgebra N 2 (↑(insert r S) : Set ℕ), ∃ z ∈ heckeAlgebra N 2 (↑S : Set ℕ),
      x = y + (p : ℤ) • z := by
  classical

  obtain ⟨t', ht', t'', ht'', hT⟩ :=
    CuspForm.exists_mem_heckeAlgebra_insert_heckeTLin_eq_add_smul_of_ne N
      (CuspForm.hasIntegralStructure_two N) p r hp hr hrp hrN (↑S : Set ℕ) S.finite_toSet hrS
  rw [← Finset.coe_insert] at ht'

  let B : Subring (E N) :=
    { carrier := {x | ∃ y ∈ heckeAlgebra N 2 (↑(insert r S) : Set ℕ),
        ∃ z ∈ heckeAlgebra N 2 (↑S : Set ℕ), x = y + (p : ℤ) • z}
      mul_mem' := by
        rintro _ _ ⟨y, hy, z, hz, rfl⟩ ⟨y', hy', z', hz', rfl⟩
        refine ⟨y * y', mul_mem hy hy', y * z' + z * y' + (p : ℤ) • (z * z'), ?_, ?_⟩
        · have hyA : y ∈ heckeAlgebra N 2 (↑S : Set ℕ) := le_of_insert N S r hy
          have hy'A : y' ∈ heckeAlgebra N 2 (↑S : Set ℕ) := le_of_insert N S r hy'
          exact add_mem (add_mem (mul_mem hyA hz') (mul_mem hz hy'A)) (zsmul_mem (mul_mem hz hz') _)
        · simp only [mul_add, add_mul, smul_add, mul_smul_comm, smul_mul_assoc, smul_smul]
          abel
      one_mem' := ⟨1, one_mem _, 0, zero_mem _, by simp⟩
      add_mem' := by
        rintro _ _ ⟨y, hy, z, hz, rfl⟩ ⟨y', hy', z', hz', rfl⟩
        exact ⟨y + y', add_mem hy hy', z + z', add_mem hz hz', by simp only [smul_add]; abel⟩
      zero_mem' := ⟨0, zero_mem _, 0, zero_mem _, by simp⟩
      neg_mem' := by
        rintro _ ⟨y, hy, z, hz, rfl⟩
        exact ⟨-y, neg_mem hy, -z, neg_mem hz, by simp only [smul_neg, neg_add]⟩ }

  suffices h : x ∈ B from h
  refine Algebra.adjoin_induction (p := fun t _ => t ∈ B) ?_ ?_ ?_ ?_ hx
  · rintro _ (⟨ℓ, hℓ, hℓN, hℓS, rfl⟩ | ⟨q, hqN, hq, hqS, rfl⟩)
    · by_cases hℓr : ℓ = r
      · subst hℓr
        exact ⟨t', ht', t'', ht'', hT⟩
      · refine ⟨heckeTLin 2 hℓ hℓN, ?_, 0, zero_mem _, by simp⟩
        refine heckeTLin_mem_heckeAlgebra hℓ hℓN ?_
        intro hmem
        rcases Finset.mem_insert.mp (Finset.mem_coe.mp hmem) with h | h
        · exact hℓr h
        · exact hℓS (Finset.mem_coe.mpr h)
    · exact absurd (Finset.mem_coe.mpr (hNS q hq hqN)) hqS
  · intro n
    exact ⟨algebraMap ℤ (E N) n, algebraMap_mem _ n, 0, zero_mem _, by simp⟩
  · intro _ _ _ _ ha hb
    exact B.add_mem ha hb
  · intro _ _ _ _ ha hb
    exact B.mul_mem ha hb

theorem exists_int_smul_mem (hp : p.Prime) (hr : r.Prime) (hrp : r ≠ p) (hrN : ¬ r ∣ N)
    (hrS : r ∉ (↑S : Set ℕ)) (hNS : ∀ q : ℕ, q.Prime → q ∣ N → q ∈ S) :
    ∃ a : ℤ, a - 1 ∈ Ideal.span {(p : ℤ)} ∧
      ∀ v : heckeAlgebra N 2 (↑S : Set ℕ),
        (a • (v : E N)) ∈ heckeAlgebra N 2 (↑(insert r S) : Set ℕ) := by
  classical
  haveI : Module.Finite ℤ (heckeAlgebra N 2 (↑S : Set ℕ)) := CuspForm.moduleFinite_heckeAlgebra_two N _
  set W := subA' N S r with hWdef
  haveI hQfin : Module.Finite ℤ (↥(heckeAlgebra N 2 (↑S : Set ℕ)) ⧸ W) :=
    Module.Finite.of_surjective (W.mkQ.restrictScalars ℤ) W.mkQ_surjective
  have hfg : (⊤ : Submodule ℤ (↥(heckeAlgebra N 2 (↑S : Set ℕ)) ⧸ W)).FG := Module.finite_def.mp hQfin
  have hle : (⊤ : Submodule ℤ (↥(heckeAlgebra N 2 (↑S : Set ℕ)) ⧸ W)) ≤
      Ideal.span {(p : ℤ)} • (⊤ : Submodule ℤ (↥(heckeAlgebra N 2 (↑S : Set ℕ)) ⧸ W)) := by
    rintro q -
    obtain ⟨v, rfl⟩ := Submodule.Quotient.mk_surjective W q
    obtain ⟨y, hy, z, hz, hv⟩ := exists_decomp N S r p hp hr hrp hrN hrS hNS (v : E N) v.2
    have hv' : v = ⟨y, le_of_insert N S r hy⟩ + (p : ℤ) • (⟨z, hz⟩ : heckeAlgebra N 2 (↑S : Set ℕ)) :=
      Subtype.ext (by rw [hv]; rfl)
    have hyW : (⟨y, le_of_insert N S r hy⟩ : heckeAlgebra N 2 (↑S : Set ℕ)) ∈ W := hy
    rw [hv', Submodule.Quotient.mk_add, (Submodule.Quotient.mk_eq_zero W).mpr hyW, zero_add,
      Submodule.Quotient.mk_smul]
    exact Submodule.smul_mem_smul (Ideal.mem_span_singleton_self _) Submodule.mem_top
  obtain ⟨a, ha1, ha⟩ :=
    Submodule.exists_sub_one_mem_and_smul_eq_zero_of_fg_of_le_smul (Ideal.span {(p : ℤ)}) ⊤ hfg hle
  refine ⟨a, ha1, fun v => ?_⟩
  have h := ha (Submodule.Quotient.mk v) Submodule.mem_top
  have h' : (Submodule.Quotient.mk (a • v) : ↥(heckeAlgebra N 2 (↑S : Set ℕ)) ⧸ W) = 0 := by
    rw [Submodule.Quotient.mk_smul]; exact h
  rw [Submodule.Quotient.mk_eq_zero, hWdef, mem_subA', Subalgebra.coe_smul] at h'
  exact h'

end Nakayama

section Extension

variable {N : ℕ} [NeZero N] {S : Finset ℕ} {r : ℕ} {𝒪 : Type} [CommRing 𝒪]

def chiExt (χ₀ : heckeAlgebra N 2 (↑(insert r S) : Set ℕ) →+* 𝒪) (a : ℤ)
    (ha : ∀ v : heckeAlgebra N 2 (↑S : Set ℕ),
      (a • (v : E N)) ∈ heckeAlgebra N 2 (↑(insert r S) : Set ℕ))
    (u : 𝒪ˣ) (hu : (u : 𝒪) = (a : 𝒪)) :
    heckeAlgebra N 2 (↑S : Set ℕ) →+* 𝒪 where
  toFun v := (u⁻¹ : 𝒪ˣ) • χ₀ ⟨a • (v : E N), ha v⟩
  map_one' := by
    have e : (⟨a • ((1 : heckeAlgebra N 2 (↑S : Set ℕ)) : E N), ha 1⟩ :
        heckeAlgebra N 2 (↑(insert r S) : Set ℕ)) = a • (1 : heckeAlgebra N 2 (↑(insert r S) : Set ℕ)) :=
      Subtype.ext (by rw [Subalgebra.coe_smul]; rfl)
    rw [e, map_zsmul, map_one, zsmul_eq_mul (1 : 𝒪) a, mul_one, ← hu, Units.smul_def, smul_eq_mul,
      Units.inv_mul]
  map_mul' v w := by
    have e : (⟨a • (v : E N), ha v⟩ * ⟨a • (w : E N), ha w⟩ :
        heckeAlgebra N 2 (↑(insert r S) : Set ℕ)) =
        a • ⟨a • ((v * w : heckeAlgebra N 2 (↑S : Set ℕ)) : E N), ha (v * w)⟩ := by
      apply Subtype.ext
      rw [Subalgebra.coe_mul, Subalgebra.coe_smul]
      show (a • (v : E N)) * (a • (w : E N)) = a • (a • ((v : E N) * (w : E N)))
      rw [smul_mul_assoc, mul_smul_comm]
    rw [Units.smul_def, Units.smul_def, Units.smul_def, smul_eq_mul, smul_eq_mul, smul_eq_mul,
      mul_mul_mul_comm, ← map_mul, e, map_zsmul,
      zsmul_eq_mul (χ₀ ⟨a • ((v * w : heckeAlgebra N 2 (↑S : Set ℕ)) : E N), ha (v * w)⟩) a, ← hu,
      ← mul_assoc, mul_assoc (↑u⁻¹ : 𝒪) (↑u⁻¹ : 𝒪) (u : 𝒪), Units.inv_mul, mul_one]
  map_zero' := by
    have e : (⟨a • ((0 : heckeAlgebra N 2 (↑S : Set ℕ)) : E N), ha 0⟩ :
        heckeAlgebra N 2 (↑(insert r S) : Set ℕ)) = 0 :=
      Subtype.ext (by show a • ((0 : heckeAlgebra N 2 (↑S : Set ℕ)) : E N) = 0; simp)
    rw [e, map_zero, smul_zero]
  map_add' v w := by
    have e : (⟨a • ((v + w : heckeAlgebra N 2 (↑S : Set ℕ)) : E N), ha (v + w)⟩ :
        heckeAlgebra N 2 (↑(insert r S) : Set ℕ)) = ⟨a • (v : E N), ha v⟩ + ⟨a • (w : E N), ha w⟩ :=
      Subtype.ext (by
        show a • ((v + w : heckeAlgebra N 2 (↑S : Set ℕ)) : E N) = a • (v : E N) + a • (w : E N)
        rw [Subalgebra.coe_add, smul_add])
    rw [e, map_add, smul_add]

theorem chiExt_apply (χ₀ : heckeAlgebra N 2 (↑(insert r S) : Set ℕ) →+* 𝒪) (a : ℤ)
    (ha : ∀ v : heckeAlgebra N 2 (↑S : Set ℕ),
      (a • (v : E N)) ∈ heckeAlgebra N 2 (↑(insert r S) : Set ℕ))
    (u : 𝒪ˣ) (hu : (u : 𝒪) = (a : 𝒪)) (v : heckeAlgebra N 2 (↑S : Set ℕ)) :
    chiExt χ₀ a ha u hu v = (u⁻¹ : 𝒪ˣ) • χ₀ ⟨a • (v : E N), ha v⟩ := rfl

theorem chiExt_of_mem (χ₀ : heckeAlgebra N 2 (↑(insert r S) : Set ℕ) →+* 𝒪) (a : ℤ)
    (ha : ∀ v : heckeAlgebra N 2 (↑S : Set ℕ),
      (a • (v : E N)) ∈ heckeAlgebra N 2 (↑(insert r S) : Set ℕ))
    (u : 𝒪ˣ) (hu : (u : 𝒪) = (a : 𝒪)) (v : heckeAlgebra N 2 (↑S : Set ℕ))
    (hv : (v : E N) ∈ heckeAlgebra N 2 (↑(insert r S) : Set ℕ)) :
    chiExt χ₀ a ha u hu v = χ₀ ⟨(v : E N), hv⟩ := by
  have e : (⟨a • (v : E N), ha v⟩ : heckeAlgebra N 2 (↑(insert r S) : Set ℕ)) =
      a • (⟨(v : E N), hv⟩ : heckeAlgebra N 2 (↑(insert r S) : Set ℕ)) :=
    Subtype.ext (by rw [Subalgebra.coe_smul])
  rw [chiExt_apply, e, map_zsmul, zsmul_eq_mul (χ₀ ⟨(v : E N), hv⟩) a, ← hu, Units.smul_def,
    smul_eq_mul, ← mul_assoc, Units.inv_mul, one_mul]

end Extension

theorem residueField_map_self {R : Type} [CommRing R] [IsLocalRing R] (y : ResidueField R) :
    ResidueField.map (algebraMap R R) y = y := by
  obtain ⟨x, rfl⟩ := residue_surjective y
  rw [ResidueField.map_residue]
  rfl

end RedTr

end

open RedTr IsLocalRing CuspForm in
theorem solution
    {𝒪 : Type} [CommRing 𝒪] [IsDomain 𝒪] [IsDiscreteValuationRing 𝒪]
    [IsAdicComplete (maximalIdeal 𝒪) 𝒪] [Finite (ResidueField 𝒪)] [CharZero 𝒪]
    (p : ℕ) [Fact p.Prime] (hp𝒪 : (p : 𝒪) ∈ maximalIdeal 𝒪)
    (N : ℕ) [NeZero N] (S : Finset ℕ) (hpS : p ∈ S) (hNS : ∀ q : ℕ, q.Prime → q ∣ N → q ∈ S)
    (r : ℕ) (hr : r.Prime) (hrS : r ∉ (↑S : Set ℕ)) (hrN : ¬ r ∣ N)
    (θ : CuspForm.heckeAlgebra N 2 (↑S : Set ℕ) →+* ResidueField 𝒪)
    (χ₀ : CuspForm.heckeAlgebra N 2 (↑(insert r S) : Set ℕ) →+* 𝒪)
    (hχ₀ : ∀ (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓN : ¬ ℓ ∣ N) (hℓS : ℓ ∉ (↑S : Set ℕ))
        (hℓS' : ℓ ∉ (↑(insert r S) : Set ℕ)),
      residue 𝒪 (χ₀ (CuspForm.heckeAlgebra.T hℓ hℓN hℓS')) =
        θ (CuspForm.heckeAlgebra.T hℓ hℓN hℓS)) :
    ∃ (𝒪' : Type) (_ : CommRing 𝒪') (_ : IsDomain 𝒪') (_ : IsDiscreteValuationRing 𝒪')
      (_ : IsAdicComplete (maximalIdeal 𝒪') 𝒪') (_ : Finite (ResidueField 𝒪'))
      (_ : CharZero 𝒪') (_ : Algebra 𝒪 𝒪') (_ : Module.Finite 𝒪 𝒪')
      (_ : IsLocalHom (algebraMap 𝒪 𝒪')),
    Function.Injective (algebraMap 𝒪 𝒪') ∧
    ∃ χ : CuspForm.heckeAlgebra N 2 (↑S : Set ℕ) →+* 𝒪',
      (∀ (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓN : ¬ ℓ ∣ N) (hℓS : ℓ ∉ (↑S : Set ℕ))
          (hℓS' : ℓ ∉ (↑(insert r S) : Set ℕ)),
        χ (CuspForm.heckeAlgebra.T hℓ hℓN hℓS) =
          algebraMap 𝒪 𝒪' (χ₀ (CuspForm.heckeAlgebra.T hℓ hℓN hℓS'))) ∧
      ∀ t : CuspForm.heckeAlgebra N 2 (↑S : Set ℕ),
        residue 𝒪' (χ t) = ResidueField.map (algebraMap 𝒪 𝒪') (θ t) := by
  classical
  have hp : p.Prime := Fact.out
  have hrp : r ≠ p := fun h => hrS (Finset.mem_coe.mpr (h ▸ hpS))

  obtain ⟨a, ha1, ha⟩ := exists_int_smul_mem N S r p hp hr hrp hrN hrS hNS

  have hres_a : residue 𝒪 (a : 𝒪) = 1 := by
    obtain ⟨k, hk⟩ := Ideal.mem_span_singleton.mp ha1
    have ha' : (a : 𝒪) = 1 + (p : 𝒪) * (k : 𝒪) := by
      have : a = 1 + (p : ℤ) * k := by linarith
      rw [this]; push_cast; ring
    rw [ha', map_add, map_one, map_mul, (residue_eq_zero_iff _).mpr hp𝒪, zero_mul, add_zero]
  have hunit : IsUnit (a : 𝒪) :=
    (residue_ne_zero_iff_isUnit _).mp (by rw [hres_a]; exact one_ne_zero)
  set u : 𝒪ˣ := hunit.unit with hudef
  have hu : (u : 𝒪) = (a : 𝒪) := hunit.unit_spec

  set χ : heckeAlgebra N 2 (↑S : Set ℕ) →+* 𝒪 := chiExt χ₀ a ha u hu with hχdef

  have hNS' : ∀ q : ℕ, q.Prime → q ∣ N → q ∈ (↑(insert r S) : Set ℕ) := fun q hq h =>
    Finset.mem_coe.mpr (Finset.mem_insert_of_mem (hNS q hq h))
  set incl : heckeAlgebra N 2 (↑(insert r S) : Set ℕ) →ₐ[ℤ] heckeAlgebra N 2 (↑S : Set ℕ) :=
    Subalgebra.inclusion (le_of_insert N S r) with hincl
  have hagree : ∀ t : heckeAlgebra N 2 (↑(insert r S) : Set ℕ),
      residue 𝒪 (χ₀ t) = θ (incl t) := by
    intro t
    have h := heckeAlgebra_induction N (↑(insert r S) : Set ℕ) hNS' (RingHom.id _)
      (RingHom.eqLocus ((residue 𝒪).comp χ₀) (θ.comp (incl : _ →+* _))) ?_ t
    · exact h
    intro ℓ hℓ hℓN hℓS'
    have hℓS : ℓ ∉ (↑S : Set ℕ) := fun h =>
      hℓS' (Finset.mem_coe.mpr (Finset.mem_insert_of_mem (Finset.mem_coe.mp h)))
    show residue 𝒪 (χ₀ (heckeAlgebra.T hℓ hℓN hℓS')) = θ (incl (heckeAlgebra.T hℓ hℓN hℓS'))
    rw [hχ₀ ℓ hℓ hℓN hℓS hℓS']
    rfl

  have hres : ∀ t : heckeAlgebra N 2 (↑S : Set ℕ), residue 𝒪 (χ t) = θ t := by
    intro t
    rw [hχdef, chiExt_apply, Units.smul_def, smul_eq_mul, map_mul, hagree]
    have e : incl ⟨a • (t : E N), ha t⟩ = a • t :=
      Subtype.ext (by rw [Subalgebra.coe_smul]; rfl)
    rw [e, map_zsmul, zsmul_eq_mul (θ t) a, ← mul_assoc, ← map_intCast (residue 𝒪), ← map_mul, ← hu,
      Units.inv_mul, map_one, one_mul]
  refine ⟨𝒪, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance,
    Algebra.id 𝒪, inferInstance, ⟨fun x hx => by simpa using hx⟩, fun x y h => by simpa using h, χ,
    ?_, ?_⟩
  · intro ℓ hℓ hℓN hℓS hℓS'
    rw [Algebra.algebraMap_self, RingHom.id_apply, hχdef,
      chiExt_of_mem χ₀ a ha u hu _ (heckeTLin_mem_heckeAlgebra hℓ hℓN hℓS')]
    rfl
  · intro t
    rw [residueField_map_self, hres]

end S_CuspForm_heckeAlgebra_exists_ringHom_apply_T_eq_of_insert_of_residue_eq
end P2MW
export P2MW.S_CuspForm_heckeAlgebra_exists_ringHom_apply_T_eq_of_insert_of_residue_eq (solution)
