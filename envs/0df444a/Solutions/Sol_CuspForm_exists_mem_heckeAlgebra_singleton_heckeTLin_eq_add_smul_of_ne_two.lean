-- Prove2me | solution 1 for CuspForm.exists_mem_heckeAlgebra_singleton_heckeTLin_eq_add_smul_of_ne_two
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.491319+00:00
-- url     : https://prove2.me/submissions/3bd35d0f-f495-5ac6-9e36-81bf47023d9b

import Definitions.Def_CuspForm_HeckeAlgebra
import Definitions.Def_CuspForm_IntegralStructure
import Definitions.Def_CuspForm_ModPForms
import Theorems.Thm_ModPForms_eq_zero_of_thetaPS_eq_zero_of_mem_modPCusp_two
import Theorems.Thm_ModularFormClass_qCoeff_heckeT
import Theorems.Thm_ModularFormClass_qCoeff_heckeU
import Theorems.Thm_ModularFormClass_eq_of_forall_qCoeff_eq
import Theorems.Thm_CuspForm_qCoeff_zero
import Theorems.Thm_CuspForm_mem_intLattice_of_mem_heckeAlgebra
import Theorems.Thm_CuspForm_intLattice_fg
import Theorems.Thm_CuspForm_HasIntegralStructure_moduleFinite_heckeAlgebra
import Theorems.Thm_CuspForm_HasIntegralStructure_eq_zero_of_forall_mem_intLattice
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CuspForm_exists_mem_heckeAlgebra_singleton_heckeTLin_eq_add_smul_of_ne_two
p2m_attr_erase "instance" "AlgebraicCurve.Place.instIsScalarTowerSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Divisor.instDistribMulActionAlgEquiv AlgebraicCurve.Place.instSMulAlgEquiv AlgebraicCurve.Place.instIsPrincipalIdealRingSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Place.instIsDiscreteValuationRingSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Pic0.instDistribMulActionAlgEquiv AlgebraicCurve.Place.instAlgebraSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Place.instMulActionAlgEquiv AlgebraicCurve.Pic0.instSMulAlgEquiv AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue AlgebraicCurve.instFundamentalIdentityOfSumRamificationInertia AlgebraicCurve.Place.instIsScalarTowerResidueFieldRestrictPushforward AlgebraicCurve.Place.instAlgebraResidueFieldRestrictPushforward AlgebraicCurve.Place.instIsLocalHomRestrictInclusion AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupDivisor AlgebraicCurve.Pic0.instModuleZModTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instDistribMulActionTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instSMulTorsion AlgebraicCurve.SemilinearAut.instMulActionSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instSMulCommClassZModTorsion AlgebraicCurve.SemilinearAut.instMulSemiringActionSubtypeProdRingAutMemSubgroup instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy ModularCurve.Gamma0Pair.isElliptic ModularCurve.instSMulAlgEquivRatPic0SubtypeLaurentSeriesMemIntermediateFieldLaurentBaseChange ModularCurve.instDistribMulActionAlgEquivRatPic0SubtypeLaurentSeriesMemIntermediateFieldLaurentBaseChange GaloisRep.ratLocalizedAt.span_isPrime"
p2m_attr_erase "instance" "GaloisRep.instAlgebraRatLocalizedAtZMod GaloisRepAdic.instAddCommGroup GaloisRepAdic.instFree GaloisRepAdic.instFinite GaloisRepAdic.instModule ResidualGaloisRep.instModule ResidualGaloisRep.instModuleFinite ResidualGaloisRep.instAddCommGroup ModularCurve.instIsElliptic_tateLaurent ModularCurve.PhiGen.instNeZeroPhiGenCosetA ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid ModularCurve.instIsDomainTensorProduct AlgebraicClosure.Rat.isGalois AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions ModularCurve.instAlgebraJLineBar ModularCurve.instModuleJLineBar AlgebraicCurve.instHasLocalResidue_of_hasCanonicalLocalResidueK AlgebraicCurve.instHasCanonicalLocalResidueK_of_hasCanonicalLocalResidueKStar AlgebraicCurve.Place.kw_ffgc_finiteDimensional_adicCompletion instAlgebraSubtypeMemValuationSubring_definitions AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersIntegersCompletion ModularCurve.KwF4gRRTate.instAlgebraKAdicCompletionIntegers AlgebraicCurve.Place.kw_ffgc_continuousSMul_adicCompletionComap AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersCompletionCompletion IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions AlgebraicCurve.instHasCanonicalLocalResidueK AlgebraicCurve.Place.instAlgebra_restrictResidueField AlgebraicCurve.Place.instIsScalarTower_restrictResidueField AlgebraicCurve.instHasLocalResidue"
p2m_attr_erase "instance" "AlgebraicCurve.HasSeparableResidue.of_perfectField_of_isCurveOver AlgebraicCurve.HasSeparableResidue.of_perfectField AlgebraicCurve.Place.instIsLocalHom_restrictSubringHom AlgebraicCurve.instHasCanonicalLocalResidueKStar ModularCurve.KwNo6Pin.isLocalRing_completion WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly WeierstrassCurve.Affine.instIsScalarTowerPolynomialRatFuncFunctionField_definitions WeierstrassCurve.Affine.instAlgebraRatFuncFunctionField_definitions WeierstrassCurve.Affine.instIsScalarTowerRatFuncFunctionField_definitions WeierstrassCurve.Affine.CoordinateRing.moduleFinite WeierstrassCurve.Affine.instDecidableEqFunctionField WeierstrassCurve.Affine.CoordinateRing.isIntegral ModularCurve.TatePoint.instIsElliptic_nearCurve ModularCurve.B3.instIsElliptic_goodModel ModularCurve.instIsScalarTowerJAdjoin WeierstrassCurve.VeluQuotientJGates.instIsElliptic27a4 ModularCurve.ElevenA1.instDecidableEquation ModularCurve.ElevenA1.instDecidableNonsingular ModularCurve.instIsElliptic_tateBase"
p2m_attr_erase "simp" "ModularCurve.coe_nodeEquivOfPlaces_apply ModularCurve.widthOfPlaces_mk ModularCurve.smulNodePairEmb_apply ModularCurve.card_nodePairsOfPlaces ModularCurve.smulNodePair_snd ModularCurve.smulNodePair_fst ModularCurve.coe_nodeEquivOfPlaces_symm_apply ModularCurve.coe_jGeomGen ModularCurve.coe_jNGeomGen ModularCurve.coe_uniformizerMod ModularCurve.qSeriesBar_jModElt ModularCurve.qInftyPlaceMod_toValuationSubring ModularCurve.qInftyPlaceBar_toValuationSubring ModularCurve.qSeriesBar_zero ModularCurve.qSeriesBar_add ModularCurve.cuspInftyFull_toValuationSubring ModularCurve.qInftyPlaceRat_toValuationSubring ModularCurve.qSeriesBar_mul ModularCurve.qSeriesBar_div ModularCurve.qSeriesBar_eq_zero_iff ModularCurve.coe_uniformizerBar ModularCurve.qSeriesBar_pow ModularCurve.cuspInfty_toValuationSubring ModularCurve.qSeriesBar_one ModularCurve.qSeriesBar_inv ModularCurve.qSeriesBar_sub ModularCurve.qSeriesBar_neg ModularCurve.qExpand_coeff_mul ModularCurve.qExpandₐ_apply ModularCurve.jqN_one ModularCurve.qExpand_single ModularCurve.dedekindPsi_one ModularCurve.ModularPolynomialData.mk.sizeOf_spec ModularCurve.evalAtJ_X ModularCurve.ModularPolynomialData.mk.injEq ModularCurve.constantCoeff_jNum ModularCurve.constantCoeff_eisenstein4 ModularCurve.qExpand_C ModularCurve.coeff_jq_neg_one ModularCurve.constantCoeff_jNumQ"
p2m_attr_erase "simp" "AlgebraicCurve.Place.mk.injEq AlgebraicCurve.Divisor.degree_single AlgebraicCurve.Divisor.smul_single AlgebraicCurve.Place.smul_toValuationSubring AlgebraicCurve.Place.heightOneSpectrum_asIdeal AlgebraicCurve.Place.coe_algebraMap AlgebraicCurve.Place.ord_one AlgebraicCurve.Place.coe_smulRingEquiv_apply AlgebraicCurve.Pic0.coe_degZeroSMulHom AlgebraicCurve.Place.deg_smul AlgebraicCurve.Pic0.mk_zero AlgebraicCurve.Place.mk.sizeOf_spec AlgebraicCurve.Divisor.degree_smul AlgebraicCurve.Pic0.mk_add AlgebraicCurve.Place.ord_zero AlgebraicCurve.Place.ofHeightOneSpectrum_toValuationSubring ModularCurve.jqNModC_one AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Divisor.mapRestrict_single AlgebraicCurve.Divisor.pushforward_single AlgebraicCurve.Place.coe_restrictInclusion AlgebraicCurve.Place.mem_fiber AlgebraicCurve.Place.restrict_toValuationSubring AlgebraicCurve.Divisor.degree_pushforward AlgebraicCurve.Place.restrictResidueMap_residue AlgebraicCurve.Pic0.coe_pushforwardDegZeroHom"
p2m_attr_erase "simp" "AlgebraicCurve.Pic0.coe_pullbackDegZeroHom AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.Divisor.degree_pushforwardAlong AlgebraicCurve.Pic0.coe_degZeroCorrespondence AlgebraicCurve.Place.mem_fiberAlong AlgebraicCurve.SemilinearAut.toRingAut_inv AlgebraicCurve.SemilinearAut.smul_def AlgebraicCurve.SemilinearAut.smul_single AlgebraicCurve.SemilinearAut.smul_toValuationSubring AlgebraicCurve.SemilinearAut.baseAut_inv AlgebraicCurve.SemilinearAut.baseAut_ofAlgAut AlgebraicCurve.SemilinearAut.toRingAut_ofAlgAut AlgebraicCurve.SemilinearAut.torsionRep_apply AlgebraicCurve.SemilinearAut.toRingAut_one AlgebraicCurve.SemilinearAut.deg_smul AlgebraicCurve.SemilinearAut.degree_smul AlgebraicCurve.SemilinearAut.coe_degZeroSMulHom AlgebraicCurve.SemilinearAut.baseAut_mul AlgebraicCurve.SemilinearAut.coe_smulValuationSubringEquiv_apply AlgebraicCurve.SemilinearAut.baseAut_one AlgebraicCurve.SemilinearAut.ofAlgAut_smul AlgebraicCurve.SemilinearAut.coe_torsion_smul AlgebraicCurve.SemilinearAut.toRingAut_mul AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd"
p2m_attr_erase "simp" "ModularCurve.eisensteinSystem_of_not_dvd FreyPackage.mk.sizeOf_spec FreyPackage.mk.injEq WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply ModularCurve.charLGeomModuliDictionary_single ModularCurve.specializeModuli_single ModularCurve.specializePlace_def AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one ModularCurve.gamma0PairMap_gen ModularCurve.moduliPointMapRingHom_mk ModularCurve.Gamma0Pair.mk.injEq ModularCurve.ModuliPoint.j_mk ModularCurve.Gamma0Pair.mk.sizeOf_spec ModularCurve.gamma0PairMap_toCurve WeierstrassCurve.Affine.vcY_vcYInv WeierstrassCurve.Affine.vcXInv_vcX WeierstrassCurve.Affine.Point.vcFun_zero WeierstrassCurve.Affine.vcX_vcXInv WeierstrassCurve.Affine.vcYInv_vcY WeierstrassCurve.Affine.Point.vcInvFun_zero WeierstrassCurve.ratPointHom_apply WeierstrassCurve.ratPointMap_zero ModularCurve.coeffEmb_coeff ModularCurve.coeffMap_coeff ModularCurve.coeffMap_id ModularCurve.coeffMap_single ModularCurve.qExpandAlgHomC_apply ModularCurve.reductionDivAlong_apply ModularCurve.coe_reductionDegZeroAlong ModularCurve.baseAut_arithmeticGalois ModularCurve.JZero.torsionGaloisRep_apply ModularCurve.coe_arithmeticRingAut_apply ModularCurve.toRingAut_arithmeticGalois GaloisRepAdic.mk.injEq GaloisRepAdic.mk.sizeOf_spec GaloisRepAdic.Equiv.mk.sizeOf_spec GaloisRepAdic.Equiv.mk.injEq ResidualGaloisRep.mk.sizeOf_spec ResidualGaloisRep.mk.injEq"
p2m_attr_erase "simp" "ResidualGaloisRep.Equiv.mk.sizeOf_spec ResidualGaloisRep.Equiv.mk.injEq ModularCurve.tateLaurent_a₆ ModularCurve.tatePowerSeries_a₄ ModularCurve.tatePowerSeries_a₆ ModularCurve.tateLaurent_a₄ ModularCurve.tatePowerSeries_a₁ ModularCurve.tatePowerSeries_a₂ ModularCurve.tatePowerSeries_a₃ ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularCurve.coe_towerInclBar ModularCurve.coe_towerSubstBar ModularCurve.coe_heckeBetaBarRingHom ModularCurve.coe_heckeBetaBar ModularCurve.coe_heckeAlphaBar ModularCurve.ProjectiveLine.map_mk ModularCurve.coe_baseChangeEquiv_apply ModularCurve.baseChangeHom_tmul ModularCurve.coe_cuspidalDivisor₀ AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply"
p2m_attr_erase "simp" "AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.mulAdele_apply AlgebraicCurve.residuePairing_apply_coe AlgebraicCurve.mem_adeleBdd AlgebraicCurve.weilSmul_one AlgebraicCurve.diagonalHom_apply AlgebraicCurve.weilSmul_apply AlgebraicCurve.adeleSpaceMul_coe AlgebraicCurve.mulAdele_one AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.injEq AlgebraicCurve.TranscendenceTower.mk.injEq AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec AlgebraicCurve.PoleDivisorPackage.mk.injEq AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none ModularCurve.coe_frobeniusModL ModularCurve.coe_frobeniusDegZeroPullbackModL ModularCurve.coe_frobeniusDegZeroPushforwardModL AlgebraicCurve.ConstantReduction.toRegularProlongation_residue AlgebraicCurve.RegularProlongation.mk.sizeOf_spec AlgebraicCurve.ConstantReduction.toRegularProlongation_integers AlgebraicCurve.RegularProlongation.mk.injEq AlgebraicCurve.ConstantReduction.mk.injEq AlgebraicCurve.ConstantReduction.mk.sizeOf_spec AlgebraicCurve.ConstantReduction.divMap_apply AlgebraicCurve.ConstantReduction.coe_degZeroMap AlgebraicCurve.Place.differentialCoeff_zero AlgebraicCurve.Place.differentialCoeff_dCoord ModularCurve.cuspCount_one AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.sizeOf_spec AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.injEq AlgebraicCurve.adeleSingle_coe AlgebraicCurve.kaehlerResidueTermKFam_apply AlgebraicCurve.Place.LocalResidueData.mk.injEq"
p2m_attr_erase "simp" "AlgebraicCurve.Place.LocalResidueData.mk.sizeOf_spec AlgebraicCurve.Place.kw_ffgc_adicCompletionComapIntegers_coe AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.sizeOf_spec AlgebraicCurve.Place.mem_simplePoleSubmodule AlgebraicCurve.Place.coe_uniformizerSubring ModularCurve.Lg37.Lg37CompletionSection.mk.injEq AlgebraicCurve.Place.CoefficientFieldSection.mk.injEq AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.injEq ModularCurve.Lg37.Lg37CompletionSection.mk.sizeOf_spec AlgebraicCurve.Place.CoefficientFieldSection.mk.sizeOf_spec AlgebraicCurve.Place.poleSubmodule_one AlgebraicCurve.Place.mem_poleSubmodule HahnSeries.ramScale_apply WeierstrassCurve.reducePoint_zero WeierstrassCurve.Affine.Point.galoisRep_apply compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec"
p2m_attr_erase "simp" "WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two WeierstrassCurve.veluWSum_empty WeierstrassCurve.veluQuotient_a₁ WeierstrassCurve.veluQuotient_a₃ WeierstrassCurve.veluQuotient_empty WeierstrassCurve.veluTSum_empty WeierstrassCurve.veluQuotient_a₂ WeierstrassCurve.Affine.Point.coordsOrZero_some WeierstrassCurve.Affine.Point.coordsOrZero_zero WeierstrassCurve.veluQuotient2_a₂ WeierstrassCurve.veluQuotient2_a₃ WeierstrassCurve.veluQuotient2_a₁ WeierstrassCurve.veluPointMap2_zero WeierstrassCurve.Affine.IsogenyEndDatum.mk.injEq WeierstrassCurve.Affine.IsogenyHomDatum.mk.sizeOf_spec WeierstrassCurve.Affine.IsogenyHomDatum.mk.injEq WeierstrassCurve.Affine.IsogenyEndDatum.mk.sizeOf_spec AlgebraicCurve.Pic0.coe_pushforwardAlongDegZero WeierstrassCurve.Affine.pointMapOfPushforward_apply WeierstrassCurve.Affine.pointClass_zero WeierstrassCurve.Affine.pic0ToPoint_pointClass WeierstrassCurve.Affine.deg_placeOfPoint WeierstrassCurve.Affine.coe_pointDivisor WeierstrassCurve.Affine.pointEquivPlace_symm_placeOfPoint WeierstrassCurve.Affine.pointEquivPlace_apply WeierstrassCurve.Affine.genusOnePic0Equiv_symm_apply WeierstrassCurve.Affine.pointDivisor_zero WeierstrassCurve.Affine.pic0ToPoint_mk WeierstrassCurve.Affine.divisorSum_single WeierstrassCurve.Affine.genusOnePic0Equiv_apply PeriodPair.weierstrassCurve_a₆ PeriodPair.weierstrassCurve_a₃ PeriodPair.weierstrassCurve_a₁"
p2m_attr_erase "simp" "PeriodPair.ofTau_ω₂ PeriodPair.scale_ω₂ PeriodPair.ofTau_ω₁ PeriodPair.toPoint_zero PeriodPair.toPoint_of_mem PeriodPair.weierstrassCurve_a₂ PeriodPair.ofTau_lattice PeriodPair.scale_ω₁ PeriodPair.weierstrassCurve_a₄ WeierstrassCurve.Affine.ratFuncToFunctionField_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_C WeierstrassCurve.Affine.Point.yc_some WeierstrassCurve.Affine.Point.xc_some WeierstrassCurve.Affine.pointPull_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_X WeierstrassCurve.Affine.pointHom_mk_Y WeierstrassCurve.Affine.placeOf_asIdeal WeierstrassCurve.veluY_empty WeierstrassCurve.veluX_empty AddMonoid.End.DualEndData.symm_trace AddMonoid.End.dualEndData_intCast_norm AddMonoid.End.DualEndData.ofCharPoly_norm AddMonoid.End.DualEndData.mk.sizeOf_spec AddMonoid.End.DualEndData.mk.injEq AddMonoid.End.DualEndData.ofCharPoly_dual AddMonoid.End.dualEndData_intCast_dual AddMonoid.End.DualEndData.intLinComb_norm AddMonoid.End.DualEndData.ofCharPoly_trace AddMonoid.End.DualEndData.intLinComb_dual AddMonoid.End.DualEndData.symm_dual AddMonoid.End.DualEndData.intLinComb_trace AddMonoid.End.dualEndData_intCast_trace AddMonoid.End.DualEndData.symm_norm WeierstrassCurve.veluQuotientOfSums_a₂ WeierstrassCurve.veluQuotientOfSums_a₁ WeierstrassCurve.veluQuotientOfSums_a₃ ModularCurve.B3.cycOfCongr_apply_coe ModularCurve.B3.cycOfTorsionBy_symm_apply_coe ModularCurve.B3.redPoint_zero ModularCurve.B3.pointAddEquivOfEq_rfl"
p2m_attr_erase "simp" "ModularCurve.B3.vcAddEquiv_apply ModularCurve.B3.scaleAddEquiv_apply ModularCurve.B3.cycOfTorsionBy_apply_coe ModularCurve.B3.val_inv_sU ModularCurve.B3.val_sU ModularCurve.B3.resO_apply HahnSeries.coeff_hahnTwist ModularCurve.HahnSpecialise.coe_specialiseCycSub CycSubOf.coe_map ModularCurve.HahnSpecialise.algebraMap_Qbar_apply ModularCurve.HahnSpecialise.resH_apply ModularCurve.HahnSpecialise.liftModel_map_subtype ModularCurve.HahnSpecialise.specialise_zero WeierstrassCurve.twoVeluCurve_a₁ WeierstrassCurve.twoVeluCurve_a₂ WeierstrassCurve.twoVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₂ WeierstrassCurve.xVeluCurve_a₁ WeierstrassCurve.map_veluU WeierstrassCurve.map_veluT WeierstrassCurve.map_veluW WeierstrassCurve.map_veluGy WeierstrassCurve.map_veluGx WeierstrassCurve.map_veluWSum_singleton WeierstrassCurve.map_veluTSum_singleton WeierstrassCurve.veluPointMap3_zero WeierstrassCurve.vcInvEmbedding_apply WeierstrassCurve.Affine.Point.netCol_one WeierstrassCurve.Affine.Point.xOrZero_zero WeierstrassCurve.Affine.Point.netPairing_zero_right WeierstrassCurve.Affine.Point.netW20_some WeierstrassCurve.Affine.Point.netCol_zero WeierstrassCurve.Affine.Point.netPairing_zero_left WeierstrassCurve.Affine.Point.xOrZero_some WeierstrassCurve.Affine.Point.netW20_zero TateCurve.cauchyMulInt_zero TateCurve.cauchyMulInt3_zero TateCurve.tent_one TateCurve.Gz_zero"
p2m_attr_erase "simp" "TateCurve.cauchyMulInt_one TateCurve.tent_zero TateCurve.Fz_zero TateCurve.xCoeffFull_succ TateCurve.a₆Coeff_zero TateCurve.a₄Coeff_succ TateCurve.a₄Coeff_zero TateCurve.cauchyMul_zero TateCurve.a₆Coeff_succ TateCurve.yCoeffFull_succ TateCurve.xCoeffFull_zero TateCurve.yCoeffFull_zero TateCurve.yfun_zero TateCurve.xfun_zero TateCurve.yTerm_zero TateCurve.xTerm_zero TateCurve.curve_a₂ TateCurve.b_one TateCurve.curve_a₁ TateCurve.term_zero TateCurve.curve_a₆ TateCurve.curve_a₄ TateCurve.curve_a₃ FLT.DivisorConvolution.sigma_zero_right FLT.DivisorConvolution.sigma_one_right FLT.DivisorConvolution.sigmaConv_one FLT.DivisorConvolution.sigmaConv_zero FormalCoordinates.mk.injEq WeierstrassCurve.formalParam_zero WeierstrassCurve.SmoothLocusReductionData.reduceHom₀_apply WeierstrassCurve.formalParam_some FormalCoordinates.mk.sizeOf_spec WeierstrassCurve.SmoothLocusReductionData.mk.injEq WeierstrassCurve.reducePointSmooth_zero WeierstrassCurve.SmoothLocusReductionData.mk.sizeOf_spec WeierstrassCurve.mem_zeroComponentSubgroup_iff ModularCurve.tateUnivCurve_a₂ ModularCurve.tateUnivCurve_a₃ ModularCurve.tateUnivCurve_a₆ ModularCurve.nonToricPoint_fst"
p2m_attr_erase "simp" "ModularCurve.toricPoint_snd ModularCurve.tateUnivCurve_a₁ ModularCurve.nonToricPoint_snd ModularCurve.tateUnivCurve_a₄ ModularCurve.toricPoint_fst"

set_option autoImplicit false

noncomputable section

open scoped MatrixGroups

namespace RW2

open CuspForm ModularFormClass

variable {N : ℕ} [NeZero N]

local notation "𝕍" N => CuspForm (CongruenceSubgroup.Gamma0 N) 2
local notation "𝔼" N => Module.End ℂ (CuspForm (CongruenceSubgroup.Gamma0 N) 2)

theorem hΓ (M : ℕ) : (1 : ℝ) ∈ ((CongruenceSubgroup.Gamma0 M : Subgroup SL(2, ℤ)) :
    Subgroup (GL (Fin 2) ℝ)).strictPeriods := by simp

def qCoeffLin (M n : ℕ) : CuspForm (CongruenceSubgroup.Gamma0 M) 2 →ₗ[ℂ] ℂ where
  toFun G := qCoeff G n
  map_add' f g := by
    show qCoeff (⇑(f + g)) n = _
    unfold ModularFormClass.qCoeff
    rw [CuspForm.coe_add, ModularForm.qExpansion_add one_pos (hΓ M) f g, map_add]
  map_smul' c f := by
    show qCoeff (⇑(c • f)) n = _
    unfold ModularFormClass.qCoeff
    rw [CuspForm.IsGLPos.coe_smul, ModularForm.qExpansion_smul one_pos (hΓ M), _root_.map_smul]
    rfl

theorem qCoeffLin_apply (M n : ℕ) (G : CuspForm (CongruenceSubgroup.Gamma0 M) 2) :
    qCoeffLin M n G = qCoeff G n := rfl

theorem qCoeff_add' (f g : 𝕍 N) (n : ℕ) : qCoeff (⇑(f + g)) n = qCoeff f n + qCoeff g n := by
  rw [← qCoeffLin_apply, map_add, qCoeffLin_apply, qCoeffLin_apply]

theorem qCoeff_smul' (c : ℂ) (f : 𝕍 N) (n : ℕ) : qCoeff (⇑(c • f)) n = c * qCoeff f n := by
  rw [← qCoeffLin_apply, map_smul, qCoeffLin_apply, smul_eq_mul]

theorem qCoeff_zsmul' (c : ℤ) (f : 𝕍 N) (n : ℕ) : qCoeff (⇑(c • f)) n = (c : ℂ) * qCoeff f n := by
  rw [← Int.cast_smul_eq_zsmul ℂ c f, qCoeff_smul']

theorem qCoeff_sub' (f g : 𝕍 N) (n : ℕ) : qCoeff (⇑(f - g)) n = qCoeff f n - qCoeff g n := by
  rw [← qCoeffLin_apply, map_sub, qCoeffLin_apply, qCoeffLin_apply]

theorem qCoeff_zero' (n : ℕ) : qCoeff (⇑(0 : 𝕍 N)) n = 0 := by
  rw [← qCoeffLin_apply, map_zero]

theorem eq_zero_of_forall_qCoeff (f : 𝕍 N) (h : ∀ n, qCoeff f n = 0) : f = 0 :=
  ModularFormClass.eq_of_forall_qCoeff_eq (hΓ N) fun n => (h n).trans (qCoeff_zero' n).symm

theorem qCoeff_T {ℓ : ℕ} (hℓ : ℓ.Prime) (hℓN : ¬ ℓ ∣ N) (f : 𝕍 N) (n : ℕ) :
    qCoeff (⇑(heckeTLin 2 hℓ hℓN f)) n =
      qCoeff f (n * ℓ) + if ℓ ∣ n then (ℓ : ℂ) * qCoeff f (n / ℓ) else 0 := by
  rw [CuspForm.coe_heckeTLin_apply, ModularFormClass.qCoeff_heckeT f (hΓ N) hℓ.ne_zero n,
    ModularForm.coeffHeckeT_apply]
  have e2 : ((2 : ℤ) - 1) = 1 := by norm_num
  rw [e2, zpow_one]

theorem qCoeff_U {q : ℕ} (hq : q ≠ 0) (hqN : q ∣ N) (f : 𝕍 N) (n : ℕ) :
    qCoeff (⇑(heckeULin 2 hqN f)) n = qCoeff f (n * q) := by
  rw [CuspForm.coe_heckeULin_apply]
  exact ModularFormClass.qCoeff_heckeU f (hΓ N) hq n

theorem qCoeff_mem_of_forall_qCoeff_one_mem (X : Set ℕ) (D : AddSubgroup ℂ) (n : ℕ) :
    n ≠ 0 → (∀ ℓ : ℕ, ℓ.Prime → ℓ ∣ n → ℓ ∉ X) →
      ∀ f : 𝕍 N, (∀ t ∈ heckeAlgebra N 2 X, qCoeff (⇑(t f)) 1 ∈ D) → qCoeff f n ∈ D := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro hn hX f hf
  by_cases h1 : n = 1
  · subst h1
    have h := hf 1 (one_mem _)
    rwa [Module.End.one_apply] at h
  obtain ⟨ℓ, hℓ, hℓn⟩ := Nat.exists_prime_and_dvd h1
  obtain ⟨m, rfl⟩ := hℓn
  have hm0 : m ≠ 0 := fun h => hn (by rw [h, mul_zero])
  have hmlt : m < ℓ * m := lt_mul_left (Nat.pos_of_ne_zero hm0) hℓ.one_lt
  have hℓX : ℓ ∉ X := hX ℓ hℓ (dvd_mul_right ℓ m)
  have hXm : ∀ ℓ' : ℕ, ℓ'.Prime → ℓ' ∣ m → ℓ' ∉ X := fun ℓ' h1' h2' =>
    hX ℓ' h1' (Dvd.dvd.mul_left h2' ℓ)
  by_cases hℓN : ℓ ∣ N
  ·
    have hU : (heckeULin 2 hℓN : 𝔼 N) ∈ heckeAlgebra N 2 X := heckeULin_mem_heckeAlgebra hℓ hℓN hℓX
    have hf' : ∀ t ∈ heckeAlgebra N 2 X, qCoeff (⇑(t (heckeULin 2 hℓN f))) 1 ∈ D := by
      intro t ht
      have h := hf (t * heckeULin 2 hℓN) (mul_mem ht hU)
      rwa [Module.End.mul_apply] at h
    have h := ih m hmlt hm0 hXm (heckeULin 2 hℓN f) hf'
    rwa [qCoeff_U hℓ.ne_zero, mul_comm] at h
  ·
    have hT : (heckeTLin 2 hℓ hℓN : 𝔼 N) ∈ heckeAlgebra N 2 X := heckeTLin_mem_heckeAlgebra hℓ hℓN hℓX
    have hf' : ∀ t ∈ heckeAlgebra N 2 X, qCoeff (⇑(t (heckeTLin 2 hℓ hℓN f))) 1 ∈ D := by
      intro t ht
      have h := hf (t * heckeTLin 2 hℓ hℓN) (mul_mem ht hT)
      rwa [Module.End.mul_apply] at h
    have h := ih m hmlt hm0 hXm (heckeTLin 2 hℓ hℓN f) hf'
    rw [qCoeff_T hℓ hℓN, mul_comm] at h

    have hcorr : (if ℓ ∣ m then (ℓ : ℂ) * qCoeff f (m / ℓ) else 0) ∈ D := by
      split_ifs with hℓm
      · obtain ⟨m', rfl⟩ := hℓm
        have hm'0 : m' ≠ 0 := fun h => hm0 (by rw [h, mul_zero])
        have hm'lt : m' < ℓ * (ℓ * m') :=
          lt_of_lt_of_le (lt_mul_left (Nat.pos_of_ne_zero hm'0) hℓ.one_lt) hmlt.le
        have hXm' : ∀ ℓ' : ℕ, ℓ'.Prime → ℓ' ∣ m' → ℓ' ∉ X := fun ℓ' h1' h2' =>
          hXm ℓ' h1' (Dvd.dvd.mul_left h2' ℓ)
        have h' := ih m' hm'lt hm'0 hXm' f hf
        rw [Nat.mul_div_cancel_left m' hℓ.pos]
        have e : (ℓ : ℂ) * qCoeff f m' = ℓ • qCoeff f m' := by rw [nsmul_eq_mul]
        rw [e]
        exact D.nsmul_mem h' ℓ
      · exact D.zero_mem
    have e : qCoeff (⇑f) (ℓ * m) =
        (qCoeff (⇑f) (ℓ * m) + if ℓ ∣ m then (ℓ : ℂ) * qCoeff f (m / ℓ) else 0) -
          (if ℓ ∣ m then (ℓ : ℂ) * qCoeff f (m / ℓ) else 0) := by ring
    rw [e]
    exact D.sub_mem h hcorr

theorem exists_int_qCoeff_of_mem_intLattice {f : 𝕍 N} (hf : f ∈ intLattice N 2) (n : ℕ) :
    ∃ m : ℤ, qCoeff f n = (m : ℂ) := by
  induction hf using Submodule.span_induction with
  | mem g hg => exact hg n
  | zero => exact ⟨0, by rw [qCoeff_zero', Int.cast_zero]⟩
  | add g h _ _ ihg ihh =>
    obtain ⟨a, ha⟩ := ihg
    obtain ⟨b, hb⟩ := ihh
    exact ⟨a + b, by rw [qCoeff_add', ha, hb, Int.cast_add]⟩
  | smul c g _ ih =>
    obtain ⟨a, ha⟩ := ih
    exact ⟨c * a, by rw [qCoeff_zsmul', ha, Int.cast_mul]⟩

def zcoeff (n : ℕ) (f : ↥(intLattice N 2)) : ℤ :=
  (exists_int_qCoeff_of_mem_intLattice f.2 n).choose

theorem zcoeff_spec (n : ℕ) (f : ↥(intLattice N 2)) :
    ((zcoeff n f : ℤ) : ℂ) = qCoeff (⇑(f : 𝕍 N)) n :=
  (exists_int_qCoeff_of_mem_intLattice f.2 n).choose_spec.symm

def zcoeffLin (n : ℕ) : ↥(intLattice N 2) →ₗ[ℤ] ℤ where
  toFun := zcoeff n
  map_add' f g := by
    apply Int.cast_injective (α := ℂ)
    rw [Int.cast_add, zcoeff_spec, zcoeff_spec, zcoeff_spec, Submodule.coe_add, qCoeff_add']
  map_smul' c f := by
    apply Int.cast_injective (α := ℂ)
    rw [RingHom.id_apply, smul_eq_mul, Int.cast_mul, zcoeff_spec, zcoeff_spec, Submodule.coe_smul,
      qCoeff_zsmul']

theorem zcoeffLin_apply (n : ℕ) (f : ↥(intLattice N 2)) : zcoeffLin n f = zcoeff n f := rfl

theorem mem_intLattice_of_forall_int {f : 𝕍 N} (h : ∀ n, ∃ m : ℤ, qCoeff f n = (m : ℂ)) :
    f ∈ intLattice N 2 :=
  Submodule.subset_span h

abbrev T (N : ℕ) [NeZero N] : Subalgebra ℤ (𝔼 N) := heckeAlgebra N 2 (∅ : Set ℕ)

def act (t : ↥(T N)) (f : ↥(intLattice N 2)) : ↥(intLattice N 2) :=
  ⟨(t : 𝔼 N) (f : 𝕍 N), CuspForm.mem_intLattice_of_mem_heckeAlgebra one_le_two t.2 f.2⟩

@[scoped simp] theorem coe_act (t : ↥(T N)) (f : ↥(intLattice N 2)) :
    ((act t f : ↥(intLattice N 2)) : 𝕍 N) = (t : 𝔼 N) (f : 𝕍 N) := rfl

def Φ : ↥(intLattice N 2) →ₗ[ℤ] Module.Dual ℤ ↥(T N) where
  toFun f :=
    { toFun := fun t => zcoeff 1 (act t f)
      map_add' := fun s t => by
        apply Int.cast_injective (α := ℂ)
        rw [Int.cast_add, zcoeff_spec, zcoeff_spec, zcoeff_spec, coe_act, coe_act, coe_act,
          Subalgebra.coe_add, LinearMap.add_apply, qCoeff_add']
      map_smul' := fun c t => by
        apply Int.cast_injective (α := ℂ)
        rw [RingHom.id_apply, smul_eq_mul, Int.cast_mul, zcoeff_spec, zcoeff_spec, coe_act, coe_act,
          Subalgebra.coe_smul, LinearMap.smul_apply, qCoeff_zsmul'] }
  map_add' f g := by
    ext t
    apply Int.cast_injective (α := ℂ)
    simp only [LinearMap.coe_mk, AddHom.coe_mk, LinearMap.add_apply]
    rw [Int.cast_add, zcoeff_spec, zcoeff_spec, zcoeff_spec, coe_act, coe_act, coe_act,
      Submodule.coe_add, map_add, qCoeff_add']
  map_smul' c f := by
    ext t
    apply Int.cast_injective (α := ℂ)
    simp only [LinearMap.coe_mk, AddHom.coe_mk, LinearMap.smul_apply, RingHom.id_apply, smul_eq_mul]
    rw [Int.cast_mul, zcoeff_spec, zcoeff_spec, coe_act, coe_act, Submodule.coe_smul, map_zsmul,
      qCoeff_zsmul']

theorem Φ_apply_coe (f : ↥(intLattice N 2)) (t : ↥(T N)) :
    ((Φ f t : ℤ) : ℂ) = qCoeff (⇑((t : 𝔼 N) (f : 𝕍 N))) 1 := by
  show ((zcoeff 1 (act t f) : ℤ) : ℂ) = _
  rw [zcoeff_spec, coe_act]

def intSubgroup : AddSubgroup ℂ := (Int.castAddHom ℂ).range

theorem mem_intSubgroup_iff (z : ℂ) : z ∈ intSubgroup ↔ ∃ m : ℤ, z = (m : ℂ) := by
  simp only [intSubgroup, AddMonoidHom.mem_range, Int.coe_castAddHom, eq_comm]

theorem Φ_injective : Function.Injective (Φ (N := N)) := by
  refine (injective_iff_map_eq_zero _).mpr fun f hf => ?_
  apply Subtype.ext
  refine eq_zero_of_forall_qCoeff (f : 𝕍 N) fun n => ?_
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · exact CuspForm.qCoeff_zero (f : 𝕍 N)
  have h := qCoeff_mem_of_forall_qCoeff_one_mem (N := N) (∅ : Set ℕ) (⊥ : AddSubgroup ℂ) n hn.ne'
    (fun _ _ _ h => h) (f : 𝕍 N) (fun t ht => by
      have e := Φ_apply_coe f ⟨t, ht⟩
      rw [hf, LinearMap.zero_apply, Int.cast_zero] at e
      rw [AddSubgroup.mem_bot]
      exact e.symm)
  exact (AddSubgroup.mem_bot).mp h

theorem eq_zero_of_forall_Φ_eq_zero (hint : HasIntegralStructure N 2) (t : ↥(T N))
    (h : ∀ f : ↥(intLattice N 2), Φ f t = 0) : t = 0 := by
  apply Subtype.ext
  refine CuspForm.HasIntegralStructure.eq_zero_of_forall_mem_intLattice hint (t : 𝔼 N) fun g hg => ?_
  refine eq_zero_of_forall_qCoeff _ fun n => ?_
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · exact CuspForm.qCoeff_zero _
  have h' := qCoeff_mem_of_forall_qCoeff_one_mem (N := N) (∅ : Set ℕ) (⊥ : AddSubgroup ℂ) n hn.ne'
    (fun _ _ _ h => h) ((t : 𝔼 N) g) (fun s hs => by
      have e := Φ_apply_coe (act ⟨s, hs⟩ ⟨g, hg⟩) t
      rw [h, Int.cast_zero, coe_act] at e
      rw [AddSubgroup.mem_bot]
      have hc : (⟨s, hs⟩ * t : ↥(T N)) = t * ⟨s, hs⟩ := mul_comm _ _
      have hc' := congrArg (fun u : ↥(T N) => (u : 𝔼 N) g) hc
      simp only [Subalgebra.coe_mul, Module.End.mul_apply] at hc'
      rw [hc']
      exact e.symm)
  exact (AddSubgroup.mem_bot).mp h'

theorem moduleFinite_L : Module.Finite ℤ ↥(intLattice N 2) :=
  Module.Finite.iff_fg.mpr (intLattice_fg N 2)

theorem moduleFree_L : Module.Free ℤ ↥(intLattice N 2) := by
  haveI := moduleFinite_L (N := N)
  haveI : IsAddTorsionFree (CuspForm (CongruenceSubgroup.Gamma0 N) 2) := .of_isTorsionFree ℂ _
  exact Module.free_of_finite_type_torsion_free'

theorem moduleFree_T (hint : HasIntegralStructure N 2) : Module.Free ℤ ↥(T N) := by
  haveI := CuspForm.HasIntegralStructure.moduleFinite_heckeAlgebra hint one_le_two (∅ : Set ℕ)
  exact Module.free_of_finite_type_torsion_free'

set_option maxHeartbeats 8000000 in
set_option synthInstance.maxHeartbeats 1600000 in

theorem exists_smul_mem_range_Φ (hint : HasIntegralStructure N 2) (ψ : Module.Dual ℤ ↥(T N)) :
    ∃ m : ℤ, m ≠ 0 ∧ m • ψ ∈ LinearMap.range (Φ (N := N)) := by
  haveI := moduleFinite_L (N := N)
  haveI := moduleFree_L (N := N)
  haveI := CuspForm.HasIntegralStructure.moduleFinite_heckeAlgebra hint one_le_two (∅ : Set ℕ)
  haveI := moduleFree_T hint
  haveI : Module.Finite ℤ (Module.Dual ℤ ↥(T N)) := inferInstance
  haveI : Module.Finite ℤ (Module.Dual ℤ ↥(intLattice N 2)) := inferInstance
  haveI : Module.Finite ℤ (Module.Dual ℤ ↥(T N) ⧸ LinearMap.range (Φ (N := N))) :=
    Module.Finite.of_surjective (LinearMap.range (Φ (N := N))).mkQ (Submodule.mkQ_surjective _)

  have hΨ : Function.Injective (Φ (N := N)).flip := by
    refine (injective_iff_map_eq_zero _).mpr fun t ht =>
      eq_zero_of_forall_Φ_eq_zero hint t fun f => ?_
    have h := LinearMap.congr_fun ht f
    rwa [LinearMap.flip_apply, LinearMap.zero_apply] at h

  have h1 : Module.finrank ℤ ↥(intLattice N 2) ≤ Module.finrank ℤ (Module.Dual ℤ ↥(T N)) :=
    LinearMap.finrank_le_finrank_of_injective Φ_injective
  have h2 : Module.finrank ℤ (Module.Dual ℤ ↥(T N)) = Module.finrank ℤ ↥(T N) :=
    Module.finrank_linearMap_self ℤ ℤ ↥(T N)
  have h3 : Module.finrank ℤ ↥(T N) ≤ Module.finrank ℤ (Module.Dual ℤ ↥(intLattice N 2)) :=
    LinearMap.finrank_le_finrank_of_injective hΨ
  have h4 : Module.finrank ℤ (Module.Dual ℤ ↥(intLattice N 2)) =
      Module.finrank ℤ ↥(intLattice N 2) :=
    Module.finrank_linearMap_self ℤ ℤ ↥(intLattice N 2)
  have hL : Module.finrank ℤ ↥(intLattice N 2) = Module.finrank ℤ (Module.Dual ℤ ↥(T N)) :=
    le_antisymm h1 (h2 ▸ h3.trans h4.le)
  have hrange : Module.finrank ℤ ↥(LinearMap.range (Φ (N := N))) =
      Module.finrank ℤ (Module.Dual ℤ ↥(T N)) := by
    rw [LinearMap.finrank_range_of_inj Φ_injective]
    exact hL

  have hq : Module.finrank ℤ (Module.Dual ℤ ↥(T N) ⧸ LinearMap.range (Φ (N := N))) = 0 := by
    have h := Submodule.finrank_quotient_add_finrank (LinearMap.range (Φ (N := N)))
    rw [hrange] at h
    have h' : Module.finrank ℤ (Module.Dual ℤ ↥(T N) ⧸ LinearMap.range (Φ (N := N))) +
        Module.finrank ℤ (Module.Dual ℤ ↥(T N)) = 0 + Module.finrank ℤ (Module.Dual ℤ ↥(T N)) := by
      rw [zero_add]; exact h
    exact Nat.add_right_cancel h'
  have htors : Module.IsTorsion ℤ (Module.Dual ℤ ↥(T N) ⧸ LinearMap.range (Φ (N := N))) :=
    Module.finrank_eq_zero_iff_isTorsion.mp hq
  obtain ⟨⟨m, hm⟩, hmψ⟩ := @htors (Submodule.Quotient.mk ψ)
  refine ⟨m, nonZeroDivisors.ne_zero hm, ?_⟩
  rw [Submonoid.mk_smul] at hmψ
  change Submodule.Quotient.mk (m • ψ) = 0 at hmψ
  exact (Submodule.Quotient.mk_eq_zero _).mp hmψ

theorem Φ_surjective (hint : HasIntegralStructure N 2) : Function.Surjective (Φ (N := N)) := by
  intro ψ
  obtain ⟨m, hm, f, hf⟩ := exists_smul_mem_range_Φ hint ψ

  set g : 𝕍 N := (m : ℂ)⁻¹ • (f : 𝕍 N) with hg
  have hmC : (m : ℂ) ≠ 0 := Int.cast_ne_zero.mpr hm
  have hg1 : ∀ t : ↥(T N), qCoeff (⇑((t : 𝔼 N) g)) 1 = (ψ t : ℂ) := by
    intro t
    have e := Φ_apply_coe f t
    rw [hf, LinearMap.smul_apply, smul_eq_mul, Int.cast_mul] at e
    rw [hg, map_smul, qCoeff_smul', ← e, ← mul_assoc, inv_mul_cancel₀ hmC, one_mul]
  have hgint : ∀ n, ∃ k : ℤ, qCoeff g n = (k : ℂ) := by
    intro n
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · exact ⟨0, by rw [CuspForm.qCoeff_zero, Int.cast_zero]⟩
    have h := qCoeff_mem_of_forall_qCoeff_one_mem (N := N) (∅ : Set ℕ) intSubgroup n hn.ne'
      (fun _ _ _ h => h) g (fun t ht => (mem_intSubgroup_iff _).mpr ⟨ψ ⟨t, ht⟩, hg1 ⟨t, ht⟩⟩)
    exact (mem_intSubgroup_iff _).mp h
  refine ⟨⟨g, mem_intLattice_of_forall_int hgint⟩, ?_⟩
  ext t
  apply Int.cast_injective (α := ℂ)
  rw [Φ_apply_coe]
  exact hg1 t

theorem mem_zmultiples_natCast_iff (p : ℕ) (m : ℤ) :
    ((m : ℤ) : ℂ) ∈ AddSubgroup.zmultiples ((p : ℕ) : ℂ) ↔ (p : ℤ) ∣ m := by
  rw [AddSubgroup.mem_zmultiples_iff]
  constructor
  · rintro ⟨k, hk⟩
    refine ⟨k, ?_⟩
    apply Int.cast_injective (α := ℂ)
    rw [← hk, Int.cast_mul, Int.cast_natCast, zsmul_eq_mul, mul_comm]
  · rintro ⟨k, rfl⟩
    exact ⟨k, by rw [Int.cast_mul, Int.cast_natCast, zsmul_eq_mul, mul_comm]⟩

theorem exists_addMonoidHom_zmod_apply_ne_zero (p : ℕ) [Fact p.Prime] (Q : Type) [AddCommGroup Q]
    [Module (ZMod p) Q] (x : Q) (hx : x ≠ 0) : ∃ χ : Q →+ ZMod p, χ x ≠ 0 := by
  obtain ⟨f, hf⟩ := Module.Projective.exists_dual_ne_zero (ZMod p) hx
  exact ⟨f.toAddMonoidHom, hf⟩

end RW2
p2m_reactivate "P2MW.S_CuspForm_exists_mem_heckeAlgebra_singleton_heckeTLin_eq_add_smul_of_ne_two.RW2"

open RW2 CuspForm ModularFormClass in
theorem solution
    (N : ℕ) [NeZero N] (hint : CuspForm.HasIntegralStructure N 2)
    (p : ℕ) (hp : p.Prime) (hp2 : p ≠ 2) (hpN : ¬ p ∣ N) :
    ∃ t' ∈ CuspForm.heckeAlgebra N 2 ({p} : Set ℕ),
      ∃ t'' ∈ CuspForm.heckeAlgebra N 2 (∅ : Set ℕ),
        (CuspForm.heckeTLin 2 hp hpN :
            Module.End ℂ (CuspForm (CongruenceSubgroup.Gamma0 N) 2)) = t' + (p : ℤ) • t'' := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  haveI := CuspForm.HasIntegralStructure.moduleFinite_heckeAlgebra hint one_le_two (∅ : Set ℕ)
  haveI := moduleFree_T (N := N) hint
  by_contra hnot

  let A : Subalgebra ℤ (Module.End ℂ (CuspForm (CongruenceSubgroup.Gamma0 N) 2)) := RW2.T N
  let M : Submodule ℤ ↥A :=
    { carrier := {a | ∃ b ∈ heckeAlgebra N 2 ({p} : Set ℕ), ∃ a' ∈ heckeAlgebra N 2 (∅ : Set ℕ),
        (a : Module.End ℂ (CuspForm (CongruenceSubgroup.Gamma0 N) 2)) = b + (p : ℤ) • a'}
      add_mem' := by
        rintro x y ⟨b₁, hb₁, a₁, ha₁, hx⟩ ⟨b₂, hb₂, a₂, ha₂, hy⟩
        refine ⟨b₁ + b₂, add_mem hb₁ hb₂, a₁ + a₂, add_mem ha₁ ha₂, ?_⟩
        rw [Subalgebra.coe_add, hx, hy, smul_add]; abel
      zero_mem' := ⟨0, zero_mem _, 0, zero_mem _, by simp⟩
      smul_mem' := by
        rintro c x ⟨b, hb, a, ha, hx⟩
        refine ⟨c • b, Subalgebra.smul_mem _ hb c, c • a, Subalgebra.smul_mem _ ha c, ?_⟩
        rw [Subalgebra.coe_smul, hx, smul_add, smul_comm] }
  have hMmem : ∀ a : ↥A, a ∈ M ↔ ∃ b ∈ heckeAlgebra N 2 ({p} : Set ℕ),
      ∃ a' ∈ heckeAlgebra N 2 (∅ : Set ℕ),
        (a : Module.End ℂ (CuspForm (CongruenceSubgroup.Gamma0 N) 2)) = b + (p : ℤ) • a' :=
    fun a => Iff.rfl

  let Tp : ↥A := ⟨heckeTLin 2 hp hpN, heckeTLin_mem_heckeAlgebra hp hpN (Set.notMem_empty p)⟩
  have hTpM : Tp ∉ M := fun h => by
    obtain ⟨b, hb, a', ha', e⟩ := (hMmem Tp).mp h
    exact hnot ⟨b, hb, a', ha', e⟩

  have hpM : ∀ a : ↥A, (p : ℤ) • a ∈ M := fun a =>
    (hMmem _).mpr ⟨0, zero_mem _, a, a.2, by rw [Subalgebra.coe_smul, zero_add]⟩
  have hBM : ∀ (b) (hb : b ∈ heckeAlgebra N 2 ({p} : Set ℕ)),
      (⟨b, heckeAlgebra_mono (Set.empty_subset _) hb⟩ : ↥A) ∈ M := fun b hb =>
    (hMmem _).mpr ⟨b, hb, 0, zero_mem _, by simp⟩

  have hQp : ∀ x : ↥A ⧸ M, p • x = 0 := by
    intro x
    induction x using Submodule.Quotient.induction_on with
    | _ a =>
      change Submodule.Quotient.mk (p • a) = 0
      rw [Submodule.Quotient.mk_eq_zero, ← natCast_zsmul]
      exact hpM a
  have hx : Submodule.Quotient.mk (p := M) Tp ≠ 0 := fun h =>
    hTpM ((Submodule.Quotient.mk_eq_zero M).mp h)
  obtain ⟨χ, hχ⟩ := @RW2.exists_addMonoidHom_zmod_apply_ne_zero p ⟨hp⟩ (↥A ⧸ M) _
    (AddCommGroup.zmodModule hQp) _ hx

  let ψbar : ↥A →+ ZMod p := χ.comp (Submodule.mkQ M).toAddMonoidHom
  have hψbar_apply : ∀ a : ↥A, ψbar a = χ (Submodule.Quotient.mk a) := fun a => rfl
  have hψbarM : ∀ a ∈ M, ψbar a = 0 := fun a ha => by
    rw [hψbar_apply, (Submodule.Quotient.mk_eq_zero M).mpr ha, map_zero]
  have hψbarTp : ψbar Tp ≠ 0 := hχ

  let e := Module.Free.chooseBasis ℤ ↥A
  let ψ : Module.Dual ℤ ↥A := e.constr ℤ fun i => ((ψbar (e i)).val : ℤ)
  have hψ : ∀ a : ↥A, ((ψ a : ℤ) : ZMod p) = ψbar a := by

    let L₁ : ↥A →ₗ[ℤ] ZMod p := (Int.castAddHom (ZMod p)).toIntLinearMap.comp ψ
    let L₂ : ↥A →ₗ[ℤ] ZMod p := ψbar.toIntLinearMap
    have hL : L₁ = L₂ := by
      refine e.ext fun i => ?_
      show ((ψ (e i) : ℤ) : ZMod p) = ψbar (e i)
      rw [show ψ (e i) = ((ψbar (e i)).val : ℤ) from e.constr_basis ℤ _ i]
      rw [Int.cast_natCast, ZMod.natCast_zmod_val]
    intro a
    exact LinearMap.congr_fun hL a

  obtain ⟨f, hf⟩ := Φ_surjective (N := N) hint ψ

  have hDp : ∀ b ∈ heckeAlgebra N 2 ({p} : Set ℕ),
      qCoeff (⇑(b (f : CuspForm (CongruenceSubgroup.Gamma0 N) 2))) 1 ∈
        AddSubgroup.zmultiples ((p : ℕ) : ℂ) := by
    intro b hb
    have e1 := Φ_apply_coe f ⟨b, heckeAlgebra_mono (Set.empty_subset _) hb⟩
    rw [hf] at e1
    rw [← e1, mem_zmultiples_natCast_iff p, ← ZMod.intCast_zmod_eq_zero_iff_dvd, hψ]
    exact hψbarM _ (hBM b hb)

  have hcoef : ∀ n : ℕ, n ≠ 0 → ¬ p ∣ n → (p : ℤ) ∣ zcoeff n f := by
    intro n hn hpn
    have h := qCoeff_mem_of_forall_qCoeff_one_mem (N := N) ({p} : Set ℕ)
      (AddSubgroup.zmultiples ((p : ℕ) : ℂ)) n hn
      (fun ℓ hℓ hℓn hℓp => hpn (by rw [Set.mem_singleton_iff.mp hℓp] at hℓn; exact hℓn))
      (f : CuspForm (CongruenceSubgroup.Gamma0 N) 2) hDp
    rw [← zcoeff_spec] at h
    exact (mem_zmultiples_natCast_iff p _).mp h

  let φ : PowerSeries (ZMod p) := PowerSeries.mk fun n => ((zcoeff n f : ℤ) : ZMod p)
  have hφmem : φ ∈ ModPForms.modPCusp N 2 (ZMod p) :=
    Submodule.subset_span ⟨(f : CuspForm (CongruenceSubgroup.Gamma0 N) 2), fun n => zcoeff n f,
      fun n => (zcoeff_spec n f).symm, rfl⟩
  have hθ : ModPForms.thetaPS φ = 0 := by
    refine PowerSeries.ext fun n => ?_
    rw [ModPForms.thetaPS, PowerSeries.coeff_mk, map_zero, PowerSeries.coeff_mk]
    by_cases hn : n = 0
    · rw [hn, Nat.cast_zero, zero_mul]
    by_cases hpn : p ∣ n
    · rw [(ZMod.natCast_eq_zero_iff n p).mpr hpn, zero_mul]
    · rw [(ZMod.intCast_zmod_eq_zero_iff_dvd _ p).mpr (hcoef n hn hpn), mul_zero]
  have hφ0 : φ = 0 :=
    ModPForms.eq_zero_of_thetaPS_eq_zero_of_mem_modPCusp_two p hp hp2 N hpN (ZMod p) φ hφmem hθ

  have hap : (p : ℤ) ∣ zcoeff p f := by
    have h := congrArg (PowerSeries.coeff p) hφ0
    rw [PowerSeries.coeff_mk, map_zero] at h
    exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).mp h
  have hψTp : ψ Tp = zcoeff p f := by
    apply Int.cast_injective (α := ℂ)
    rw [← hf, Φ_apply_coe, zcoeff_spec]
    show qCoeff (⇑(heckeTLin 2 hp hpN (f : CuspForm (CongruenceSubgroup.Gamma0 N) 2))) 1 = _
    rw [qCoeff_T hp hpN, one_mul, if_neg (fun h => hp.one_lt.ne' (Nat.dvd_one.mp h)), add_zero]
  apply hψbarTp
  rw [← hψ, hψTp]
  exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).mpr hap

end
end S_CuspForm_exists_mem_heckeAlgebra_singleton_heckeTLin_eq_add_smul_of_ne_two
end P2MW
export P2MW.S_CuspForm_exists_mem_heckeAlgebra_singleton_heckeTLin_eq_add_smul_of_ne_two (solution)
