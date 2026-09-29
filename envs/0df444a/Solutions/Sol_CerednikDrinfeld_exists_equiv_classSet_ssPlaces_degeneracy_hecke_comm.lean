-- Prove2me | solution 1 for CerednikDrinfeld.exists_equiv_classSet_ssPlaces_degeneracy_hecke_comm
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.491319+00:00
-- url     : https://prove2.me/submissions/a6b2ed94-e987-55eb-8227-8e2386ef7f26

import Definitions.Def_ModularCurve_SSDegeneracyHecke
import Definitions.Def_CerednikDrinfeld_ClassSetGraph
import Definitions.Def_QuaternionAlgebra_EichlerOrder
import Definitions.Def_WeierstrassCurve_RationalEnd
import Definitions.Def_WeierstrassCurve_KernelIdeal
import Definitions.Def_ModularCurve_ModuliPlace
import Theorems.Thm_CerednikDrinfeld_exists_classSet_equiv_ssPlaces_forall_toValuationSubring_eq_comap_moduliPlace_ker
import Theorems.Thm_QuaternionAlgebra_exists_conjByFiniteIdele_eq_mem_finiteAdeleBox_smul_inv_mem_of_relIndex_eq
import Theorems.Thm_QuaternionAlgebra_exists_eq_mul_mem_primeHeckeSet_mem_normalizer_meetOrder_eq_of_isEichlerOrder_meetOrder
import Theorems.Thm_CerednikDrinfeld_restrictAlong_levelAlphaC_eq_of_forall_toValuationSubring_eq_comap_moduliPlace_of_prime
import Theorems.Thm_QuaternionAlgebra_smul_inv_mul_mem_finiteAdeleBox_of_mem_primeHeckeSet_of_inv_mul_mul_mem
import Theorems.Thm_CerednikDrinfeld_ssHeckeMatrixC_apply_eq_classSetHeckeMatrix_primeHeckeSet_of_forall_toValuationSubring_eq_comap_moduliPlace
import Theorems.Thm_WeierstrassCurve_exists_supersingular_rationalEndSubring_range_eq_of_isMaximalOrder
import Theorems.Thm_ModularCurve_ssPlaces_finite
import Theorems.Thm_ValuationSubring_isAlgClosed_residueField
import Theorems.Thm_ValuationSubring_algebra_isAlgebraic_zmod_residueField_of_isAlgebraic_rat
import Theorems.Thm_QuaternionAlgebra_IsEichlerOrder_not_dvd_of_isDefiniteRamifiedExactlyAt
import Theorems.Thm_QuaternionAlgebra_IsOrder_finiteAdeleBox_inf_conjByFiniteIdele_eq_and_finiteIdeleStabilizer_le
import Theorems.Thm_QuaternionAlgebra_IsEichlerOrder_exists_isMaximalOrder_eq_inf_relIndex_eq_of_squarefree
import Theorems.Thm_CerednikDrinfeld_uHeckeSet_eq_levelHeckeUSet_meetOrder_of_mem_primeHeckeSet
import Theorems.Thm_CerednikDrinfeld_ssHeckeMatrixC_apply_eq_classSetHeckeMatrix_levelHeckeUSet_of_dvd_of_forall_toValuationSubring_eq_comap_moduliPlace_of_five_le
import Theorems.Thm_CerednikDrinfeld_ssFrobMatrixC_apply_eq_classSetHeckeMatrix_primeHeckeSet_of_forall_toValuationSubring_eq_comap_moduliPlace
import Theorems.Thm_CerednikDrinfeld_autOnPlaces_eq_of_isAtkinLehnerLevelAut_of_forall_toValuationSubring_eq_comap_moduliPlace
import Theorems.Thm_CerednikDrinfeld_toPNat_placeWidth_eq_classWeight_of_forall_toValuationSubring_eq_comap_moduliPlace
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_exists_equiv_classSet_ssPlaces_degeneracy_hecke_comm
p2m_attr_erase "instance" "WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt WeierstrassCurve.Affine.instIsScalarTowerPolynomialRatFuncFunctionField_definitions WeierstrassCurve.Affine.instAlgebraRatFuncFunctionField_definitions WeierstrassCurve.Affine.instIsScalarTowerRatFuncFunctionField_definitions WeierstrassCurve.Affine.CoordinateRing.moduleFinite WeierstrassCurve.Affine.instDecidableEqFunctionField WeierstrassCurve.Affine.CoordinateRing.isIntegral IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions ModularCurve.ElevenA1.instDecidableEquation ModularCurve.ElevenA1.instDecidableNonsingular ModularCurve.instIsElliptic_tateBase ModularCurve.instIsElliptic_tateLaurent ModularCurve.PhiGen.instNeZeroPhiGenCosetA ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid WeierstrassCurve.VeluQuotientJGates.instIsElliptic27a4 CyclotomicUniv.instCharZeroR₀ CyclotomicUniv.instIsDomain CyclotomicUniv.instIsDomainR₀ CyclotomicUniv.instCharZero ModularCurve.KatzGamma0Form.instModule ModularCurve.KatzGamma0Form.instZero ModularCurve.KatzLevelPForm.instSMul ModularCurve.KatzGamma0Form.instAdd ModularCurve.KatzLevelPForm.instAddCommGroup ModularCurve.KatzGamma0Form.instNeg ModularCurve.KatzGamma0Form.instAddCommGroup"
p2m_attr_erase "instance" "ModularCurve.KatzLevelPForm.instAdd ModularCurve.KatzLevelPForm.instSub ModularCurve.KatzLevelPForm.instNeg ModularCurve.KatzGamma0Form.instSMul ModularCurve.KatzGamma0Form.instSub ModularCurve.KatzLevelPForm.instZero ModularCurve.KatzLevelPForm.instModule KatzModularForm.instAddCommGroup KatzModularForm.instSub KatzModularForm.instZero KatzModularForm.instModule KatzModularForm.instAdd KatzModularForm.instNeg KatzModularForm.instSMul TateModule.instModule TateModule.instSMul GaloisRepAdic.instAddCommGroup GaloisRepAdic.instFree GaloisRepAdic.instFinite GaloisRepAdic.instModule ResidualGaloisRep.instModule ResidualGaloisRep.instModuleFinite ResidualGaloisRep.instAddCommGroup WeierstrassCurve.Affine.Point.instFinite AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions ModularCurve.instSMulAlgEquivRatPic0SubtypeLaurentSeriesMemIntermediateFieldLaurentBaseChange ModularCurve.instDistribMulActionAlgEquivRatPic0SubtypeLaurentSeriesMemIntermediateFieldLaurentBaseChange GaloisRep.ratLocalizedAt.span_isPrime GaloisRep.instAlgebraRatLocalizedAtZMod ModularCurve.instIsDomainTensorProduct AlgebraicClosure.Rat.isGalois ModularCurve.instAlgebraJLineBar ModularCurve.instModuleJLineBar AlgebraicCurve.instHasLocalResidue_of_hasCanonicalLocalResidueK AlgebraicCurve.instHasCanonicalLocalResidueK_of_hasCanonicalLocalResidueKStar AlgebraicCurve.Place.kw_ffgc_finiteDimensional_adicCompletion instAlgebraSubtypeMemValuationSubring_definitions AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersIntegersCompletion ModularCurve.KwF4gRRTate.instAlgebraKAdicCompletionIntegers AlgebraicCurve.Place.kw_ffgc_continuousSMul_adicCompletionComap"
p2m_attr_erase "instance" "AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersCompletionCompletion AlgebraicCurve.instHasCanonicalLocalResidueK AlgebraicCurve.Place.instAlgebra_restrictResidueField AlgebraicCurve.Place.instIsScalarTower_restrictResidueField AlgebraicCurve.instHasLocalResidue AlgebraicCurve.HasSeparableResidue.of_perfectField_of_isCurveOver AlgebraicCurve.HasSeparableResidue.of_perfectField AlgebraicCurve.Place.instIsLocalHom_restrictSubringHom AlgebraicCurve.instHasCanonicalLocalResidueKStar ModularCurve.KwNo6Pin.isLocalRing_completion ModularCurve.TatePoint.instIsElliptic_nearCurve ModularCurve.B3.instIsElliptic_goodModel ModularCurve.instIsScalarTowerJAdjoin WeierstrassCurve.Affine.instIsDiscreteValuationRingSubtypeFunctionFieldMemValuationSubringValuationSubringWithZeroMultiplicativeIntValuationInfty WeierstrassCurve.Affine.valuationInfty_isNontrivial WeierstrassCurve.veluQuotient2_isShortNF WeierstrassCurve.instIsShortNFMk"
p2m_attr_erase "simp" "compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two AddMonoid.End.DualEndData.symm_trace AddMonoid.End.dualEndData_intCast_norm AddMonoid.End.DualEndData.ofCharPoly_norm AddMonoid.End.DualEndData.mk.sizeOf_spec AddMonoid.End.DualEndData.mk.injEq AddMonoid.End.DualEndData.ofCharPoly_dual AddMonoid.End.dualEndData_intCast_dual"
p2m_attr_erase "simp" "AddMonoid.End.DualEndData.intLinComb_norm AddMonoid.End.DualEndData.ofCharPoly_trace AddMonoid.End.DualEndData.intLinComb_dual AddMonoid.End.DualEndData.symm_dual AddMonoid.End.DualEndData.intLinComb_trace AddMonoid.End.dualEndData_intCast_trace AddMonoid.End.DualEndData.symm_norm AddMonoid.End.dualEndDataOfSurjective_trace AddMonoid.End.dualEndDataOfSurjective_norm WeierstrassCurve.Universal.halveX_zero WeierstrassCurve.Universal.specialize_X_one WeierstrassCurve.Universal.coeff_halve WeierstrassCurve.Universal.specialize_X_two WeierstrassCurve.Universal.halveCoeff_zero WeierstrassCurve.Universal.specialize_X_four WeierstrassCurve.Universal.coeff_halveX WeierstrassCurve.Universal.specialize_X_three WeierstrassCurve.Universal.specialize_X_zero WeierstrassCurve.veluX_empty WeierstrassCurve.veluY_empty WeierstrassCurve.vcInvEmbedding_apply WeierstrassCurve.map_veluU WeierstrassCurve.map_veluT WeierstrassCurve.map_veluW WeierstrassCurve.map_veluGy WeierstrassCurve.map_veluGx WeierstrassCurve.map_veluWSum_singleton WeierstrassCurve.map_veluTSum_singleton WeierstrassCurve.veluPointMap3_zero WeierstrassCurve.Affine.IsogenyEndDatum.mk.injEq WeierstrassCurve.Affine.IsogenyHomDatum.mk.sizeOf_spec WeierstrassCurve.Affine.IsogenyHomDatum.mk.injEq WeierstrassCurve.Affine.IsogenyEndDatum.mk.sizeOf_spec AlgebraicCurve.Pic0.coe_pushforwardAlongDegZero WeierstrassCurve.Affine.pointMapOfPushforward_apply WeierstrassCurve.Affine.pointClass_zero WeierstrassCurve.Affine.pic0ToPoint_pointClass WeierstrassCurve.Affine.deg_placeOfPoint WeierstrassCurve.Affine.coe_pointDivisor WeierstrassCurve.Affine.pointEquivPlace_symm_placeOfPoint"
p2m_attr_erase "simp" "WeierstrassCurve.Affine.pointEquivPlace_apply WeierstrassCurve.Affine.genusOnePic0Equiv_symm_apply WeierstrassCurve.Affine.pointDivisor_zero WeierstrassCurve.Affine.pic0ToPoint_mk WeierstrassCurve.Affine.divisorSum_single WeierstrassCurve.Affine.genusOnePic0Equiv_apply AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal WeierstrassCurve.Affine.ratFuncToFunctionField_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_C WeierstrassCurve.Affine.Point.yc_some WeierstrassCurve.Affine.Point.xc_some WeierstrassCurve.Affine.pointPull_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_X WeierstrassCurve.Affine.pointHom_mk_Y WeierstrassCurve.Affine.placeOf_asIdeal WeierstrassCurve.pointAddEquivOfEq_refl QuaternionAlgebra.baseChangeRight_tmul QuaternionAlgebra.mapOfAlgebraMapEq_apply QuaternionAlgebra.baseChange_tmul LocalGL2.swapUnit_val WeierstrassCurve.Affine.Point.netCol_one WeierstrassCurve.Affine.Point.xOrZero_zero WeierstrassCurve.Affine.Point.netPairing_zero_right WeierstrassCurve.Affine.Point.netW20_some WeierstrassCurve.Affine.Point.netCol_zero WeierstrassCurve.Affine.Point.netPairing_zero_left WeierstrassCurve.Affine.Point.xOrZero_some WeierstrassCurve.Affine.Point.netW20_zero TateCurve.cauchyMulInt_zero TateCurve.cauchyMulInt3_zero TateCurve.tent_one TateCurve.Gz_zero TateCurve.cauchyMulInt_one TateCurve.tent_zero TateCurve.Fz_zero TateCurve.xCoeffFull_succ"
p2m_attr_erase "simp" "TateCurve.a₆Coeff_zero TateCurve.a₄Coeff_succ TateCurve.a₄Coeff_zero TateCurve.cauchyMul_zero TateCurve.a₆Coeff_succ TateCurve.yCoeffFull_succ TateCurve.xCoeffFull_zero TateCurve.yCoeffFull_zero TateCurve.yfun_zero TateCurve.xfun_zero TateCurve.yTerm_zero TateCurve.xTerm_zero TateCurve.curve_a₂ TateCurve.b_one TateCurve.curve_a₁ TateCurve.term_zero TateCurve.curve_a₆ TateCurve.curve_a₄ TateCurve.curve_a₃ FLT.DivisorConvolution.sigma_zero_right FLT.DivisorConvolution.sigma_one_right FLT.DivisorConvolution.sigmaConv_one FLT.DivisorConvolution.sigmaConv_zero FormalCoordinates.mk.injEq WeierstrassCurve.formalParam_zero WeierstrassCurve.SmoothLocusReductionData.reduceHom₀_apply WeierstrassCurve.formalParam_some FormalCoordinates.mk.sizeOf_spec WeierstrassCurve.SmoothLocusReductionData.mk.injEq WeierstrassCurve.reducePointSmooth_zero WeierstrassCurve.SmoothLocusReductionData.mk.sizeOf_spec WeierstrassCurve.mem_zeroComponentSubgroup_iff ModularCurve.tateUnivCurve_a₂ ModularCurve.tateUnivCurve_a₃ ModularCurve.tateUnivCurve_a₆ ModularCurve.nonToricPoint_fst ModularCurve.toricPoint_snd ModularCurve.tateUnivCurve_a₁ ModularCurve.nonToricPoint_snd ModularCurve.tateUnivCurve_a₄"
p2m_attr_erase "simp" "ModularCurve.toricPoint_fst ModularCurve.tateLaurent_a₆ ModularCurve.tatePowerSeries_a₄ ModularCurve.tatePowerSeries_a₆ ModularCurve.tateLaurent_a₄ ModularCurve.tatePowerSeries_a₁ ModularCurve.tatePowerSeries_a₂ ModularCurve.tatePowerSeries_a₃ ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL ModularCurve.ProjectiveLine.map_mk PeriodPair.weierstrassCurve_a₆ PeriodPair.weierstrassCurve_a₃ PeriodPair.weierstrassCurve_a₁ PeriodPair.ofTau_ω₂ PeriodPair.scale_ω₂ PeriodPair.ofTau_ω₁ PeriodPair.toPoint_zero PeriodPair.toPoint_of_mem PeriodPair.weierstrassCurve_a₂ PeriodPair.ofTau_lattice PeriodPair.scale_ω₁"
p2m_attr_erase "simp" "PeriodPair.weierstrassCurve_a₄ CyclotomicUniv.lift₀_ζ₀ CyclotomicUniv.lift_algebraMap CyclotomicUniv.val_ζUnit CyclotomicUniv.lift_ζ ModularCurve.cuspData_yP ModularCurve.qTwistAlgHom_apply ModularCurve.cuspData_yQ ModularCurve.cuspData_xP ModularCurve.cuspData_xQ ModularCurve.val_cyclZeta ModularCurve.cuspShift_one ModularCurve.cuspShift_zero ModularCurve.LevelPData.mk.sizeOf_spec ModularCurve.KatzLevelPForm.neg_toFun ModularCurve.LevelP.coe_swapW ModularCurve.KatzLevelPForm.swap_swap KatzModularForm.pullbackLevelP_toFun ModularCurve.LevelPData.swap_xQ KatzModularForm.pullbackLevelP_zero ModularCurve.LevelPData.map_yP ModularCurve.KatzLevelPForm.swap_neg ModularCurve.KatzGamma0Form.toKatzLevelPForm_sub ModularCurve.KatzLevelPForm.swap_add KatzModularForm.swap_pullbackLevelP ModularCurve.KatzGamma0Form.toKatzLevelPForm_add ModularCurve.KatzLevelPForm.swap_smul ModularCurve.LevelPData.map_yQ ModularCurve.KatzLevelPForm.mk.injEq ModularCurve.KatzLevelPForm.zero_toFun KatzModularForm.pullbackLevelP_smul ModularCurve.LevelPData.swap_xP ModularCurve.KatzGamma0Form.toKatzLevelPForm_mul ModularCurve.KatzGamma0Form.toKatzLevelPForm_neg ModularCurve.LevelPData.variableChange_xQ KatzModularForm.pullbackGamma0_toKatzLevelPForm ModularCurve.KatzLevelPForm.mk.sizeOf_spec ModularCurve.KatzLevelPForm.swap_zero ModularCurve.LevelP.coe_unipotentU ModularCurve.KatzLevelPForm.mul_toFun"
p2m_attr_erase "simp" "ModularCurve.LevelPData.variableChange_yP ModularCurve.LevelPData.mk.injEq ModularCurve.KatzLevelPForm.sub_toFun ModularCurve.LevelPData.variableChange_xP ModularCurve.KatzLevelPForm.smul_toFun ModularCurve.LevelPData.swap_yP ModularCurve.LevelPData.map_xP ModularCurve.LevelPData.swap_swap ModularCurve.LevelPData.swap_yQ ModularCurve.KatzGamma0Form.toKatzLevelPForm_zero ModularCurve.KatzGamma0Form.mk.injEq ModularCurve.KatzLevelPForm.swap_toFun KatzModularForm.pullbackLevelP_add ModularCurve.KatzGamma0Form.mk.sizeOf_spec ModularCurve.LevelPData.variableChange_yQ ModularCurve.KatzLevelPForm.swap_sub ModularCurve.KatzGamma0Form.toKatzLevelPForm_smul ModularCurve.LevelPData.map_xQ ModularCurve.KatzLevelPForm.add_toFun KatzModularForm.c₆_toFun KatzModularForm.neg_toFun KatzModularForm.mul_toFun KatzModularForm.qExpansion_neg KatzModularForm.discr_toFun KatzModularForm.qExpansion_sub KatzModularForm.qExpansion_add KatzModularForm.qExpansion_mul KatzModularForm.zero_toFun KatzModularForm.mk.injEq KatzModularForm.qExpansion_smul KatzModularForm.smul_toFun KatzModularForm.add_toFun KatzModularForm.sub_toFun KatzModularForm.c₄_toFun KatzModularForm.qExpansion_zero KatzModularForm.mk.sizeOf_spec TateCurve.tateTorsionPoint_zero_zero TateModule.smul_apply TateModule.coe_mulP TateModule.proj_apply"
p2m_attr_erase "simp" "TateModule.coe_add TateModule.coe_sub WeierstrassCurve.tateModuleRepOfBasis_V TateModule.coe_zero TateModule.rep_apply WeierstrassCurve.tateModuleRep_V WeierstrassCurve.tateModuleRepOfBasis_ρ_apply GaloisRep.padicIntToRingLevel_apply TateModule.coe_neg WeierstrassCurve.tateModuleRep_ρ_apply GaloisRepAdic.mk.injEq GaloisRepAdic.mk.sizeOf_spec GaloisRepAdic.Equiv.mk.sizeOf_spec GaloisRepAdic.Equiv.mk.injEq ResidualGaloisRep.mk.sizeOf_spec ResidualGaloisRep.mk.injEq ResidualGaloisRep.Equiv.mk.sizeOf_spec ResidualGaloisRep.Equiv.mk.injEq FrobeniusEndo.linePencil_apply WeierstrassCurve.Affine.mem_fibSet WeierstrassCurve.frobPoint_zero WeierstrassCurve.frobCardHom_apply WeierstrassCurve.kernelPolynomial_singleton WeierstrassCurve.kernelPolynomial_empty WeierstrassCurve.kohelW_one Polynomial.rootESymm_zero_right WeierstrassCurve.kohelQuotient_a₂ WeierstrassCurve.kohelQuotient_a₃ WeierstrassCurve.kohelT_one WeierstrassCurve.kohelQuotient_one WeierstrassCurve.kohelQuotient_a₁ Polynomial.rootESymm_one WeierstrassCurve.veluQuotientOfSums_a₂ WeierstrassCurve.veluQuotientOfSums_a₁ WeierstrassCurve.veluQuotientOfSums_a₃ WeierstrassCurve.legendreVariableChange_s WeierstrassCurve.legendreVariableChange_t WeierstrassCurve.legendreVariableChange_r WeierstrassCurve.legendreVariableChange_u WeierstrassCurve.deuringVariableChange_s"
p2m_attr_erase "simp" "WeierstrassCurve.deuringVariableChange_t WeierstrassCurve.deuringCurve_a₄ WeierstrassCurve.deuringCurve_a₂ WeierstrassCurve.deuringCurve_a₆ WeierstrassCurve.deuringCurve_a₁ WeierstrassCurve.deuringVariableChange_u WeierstrassCurve.deuringCurve_a₃ WeierstrassCurve.deuringVariableChange_r AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none ModularCurve.coe_towerInclBar ModularCurve.coe_towerSubstBar ModularCurve.coe_heckeBetaBarRingHom ModularCurve.coe_heckeBetaBar ModularCurve.coe_heckeAlphaBar ModularCurve.baseAut_arithmeticGalois ModularCurve.JZero.torsionGaloisRep_apply ModularCurve.coe_arithmeticRingAut_apply ModularCurve.toRingAut_arithmeticGalois ModularCurve.coe_frobeniusModL ModularCurve.coe_frobeniusDegZeroPullbackModL ModularCurve.coe_frobeniusDegZeroPushforwardModL ModularCurve.cuspCount_one HahnSeries.ramScale_apply AlgebraicCurve.mulAdele_apply AlgebraicCurve.residuePairing_apply_coe AlgebraicCurve.mem_adeleBdd AlgebraicCurve.weilSmul_one AlgebraicCurve.diagonalHom_apply AlgebraicCurve.weilSmul_apply AlgebraicCurve.adeleSpaceMul_coe AlgebraicCurve.mulAdele_one AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.injEq AlgebraicCurve.TranscendenceTower.mk.injEq AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec"
p2m_attr_erase "simp" "AlgebraicCurve.PoleDivisorPackage.mk.injEq PowerSeries.coeff_heckeV PowerSeries.coeff_heckeU LaurentSeries.coeff_heckeV LaurentSeries.coeff_heckeU FreyPackage.ModMCarrier.coe_rescaleLin_apply ModularForm.AtkinLehnerDatum.mk.injEq ModularForm.AtkinLehnerDatum.alGL_coe ModularForm.AtkinLehnerDatum.mk.sizeOf_spec ModularForm.AtkinLehnerDatum.sqUnitSL_coe ModularForm.AtkinLehnerDatum.det_sqUnit ModularForm.AtkinLehnerDatum.det_mat ModularCurve.reductionDivAlong_apply ModularCurve.coe_reductionDegZeroAlong ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ ModularCurve.coe_baseChangeEquiv_apply ModularCurve.baseChangeHom_tmul ModularCurve.coe_cuspidalDivisor₀ AlgebraicCurve.ConstantReduction.toRegularProlongation_residue AlgebraicCurve.RegularProlongation.mk.sizeOf_spec AlgebraicCurve.ConstantReduction.toRegularProlongation_integers AlgebraicCurve.RegularProlongation.mk.injEq AlgebraicCurve.ConstantReduction.mk.injEq AlgebraicCurve.ConstantReduction.mk.sizeOf_spec AlgebraicCurve.ConstantReduction.divMap_apply AlgebraicCurve.ConstantReduction.coe_degZeroMap AlgebraicCurve.Place.differentialCoeff_zero AlgebraicCurve.Place.differentialCoeff_dCoord AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.sizeOf_spec AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.injEq AlgebraicCurve.adeleSingle_coe AlgebraicCurve.kaehlerResidueTermKFam_apply AlgebraicCurve.Place.LocalResidueData.mk.injEq"
p2m_attr_erase "simp" "AlgebraicCurve.Place.LocalResidueData.mk.sizeOf_spec AlgebraicCurve.Place.kw_ffgc_adicCompletionComapIntegers_coe AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.sizeOf_spec AlgebraicCurve.Place.mem_simplePoleSubmodule AlgebraicCurve.Place.coe_uniformizerSubring ModularCurve.Lg37.Lg37CompletionSection.mk.injEq AlgebraicCurve.Place.CoefficientFieldSection.mk.injEq AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.injEq ModularCurve.Lg37.Lg37CompletionSection.mk.sizeOf_spec AlgebraicCurve.Place.CoefficientFieldSection.mk.sizeOf_spec AlgebraicCurve.Place.poleSubmodule_one AlgebraicCurve.Place.mem_poleSubmodule ModularCurve.B3.cycOfCongr_apply_coe ModularCurve.B3.cycOfTorsionBy_symm_apply_coe ModularCurve.B3.redPoint_zero ModularCurve.B3.pointAddEquivOfEq_rfl ModularCurve.B3.vcAddEquiv_apply ModularCurve.B3.scaleAddEquiv_apply ModularCurve.B3.cycOfTorsionBy_apply_coe ModularCurve.B3.val_inv_sU ModularCurve.B3.val_sU ModularCurve.B3.resO_apply HahnSeries.coeff_hahnTwist ModularCurve.HahnSpecialise.coe_specialiseCycSub CycSubOf.coe_map ModularCurve.HahnSpecialise.algebraMap_Qbar_apply ModularCurve.HahnSpecialise.resH_apply ModularCurve.HahnSpecialise.liftModel_map_subtype ModularCurve.HahnSpecialise.specialise_zero ModularCurve.toRingAut_coeffSemilinearAut ModularCurve.baseAut_arithFrobC_apply ModularCurve.coe_coeffRingAut_apply ModularCurve.baseAut_coeffSemilinearAut"

set_option autoImplicit false
open scoped TensorProduct Quaternion NumberField Pointwise
open QuaternionAlgebra CerednikDrinfeld ModularCurve AlgebraicCurve

namespace DeuringEichlerTransport

variable {a b : ℚ}

private theorem mulVecLin_comp_symm_of_forall_apply_equiv {ι σ : Type*} [Fintype ι] [Fintype σ] [DecidableEq ι] [DecidableEq σ]
    (M' : Matrix σ σ ℤ) (M : Matrix ι ι ℤ) (e : ι ≃ σ) (h : ∀ i j, M' (e i) (e j) = M i j) (x : ι → ℤ) :
    M'.mulVecLin (x ∘ e.symm) = (M.mulVecLin x) ∘ e.symm := by
  funext W
  obtain ⟨i, rfl⟩ := e.surjective W
  simp only [Matrix.mulVecLin_apply, Function.comp_apply, Equiv.symm_apply_apply, Matrix.mulVec, dotProduct]
  rw [← Equiv.sum_comp e]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [h, Equiv.symm_apply_apply]

private theorem classSetEdgeHecke_eq_of_not_dvd (N q : ℕ) (Λ R : Submodule ℤ ℍ[ℚ, a, b])
    (n : (ℍ[ℚ, a, b] ⊗[ℚ] IsDedekindDomain.FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) (ℓ : Nat.Primes) (hq : (ℓ : ℕ) ≠ q) (hN : ¬ (ℓ : ℕ) ∣ N) :
    classSetEdgeHecke N q Λ R n ℓ = classSetHeckeMatrix _ (primeHeckeSet (meetOrder R n) ℓ) := by
  unfold classSetEdgeHecke
  rw [if_neg hq, if_neg hN]

private theorem classSetEdgeHecke_eq_of_dvd (N q : ℕ) (Λ R : Submodule ℤ ℍ[ℚ, a, b])
    (n : (ℍ[ℚ, a, b] ⊗[ℚ] IsDedekindDomain.FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) (ℓ : Nat.Primes) (hq : (ℓ : ℕ) ≠ q) (hN : (ℓ : ℕ) ∣ N) :
    classSetEdgeHecke N q Λ R n ℓ = classSetHeckeMatrix _ (levelHeckeUSet Λ (meetOrder R n) ℓ) := by
  unfold classSetEdgeHecke
  rw [if_neg hq, if_pos hN]

private theorem classSetEdgeHecke_eq_of_eq (N q : ℕ) (Λ R : Submodule ℤ ℍ[ℚ, a, b])
    (n : (ℍ[ℚ, a, b] ⊗[ℚ] IsDedekindDomain.FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) (ℓ : Nat.Primes) (hq : (ℓ : ℕ) = q) :
    classSetEdgeHecke N q Λ R n ℓ = classSetHeckeMatrix _ (uHeckeSet R n q) := by
  unfold classSetEdgeHecke
  rw [if_pos hq]

end DeuringEichlerTransport

set_option synthInstance.maxHeartbeats 1600000 in
set_option maxHeartbeats 6400000 in
theorem solution
    (M s q' : ℕ) [NeZero M] [Fact q'.Prime] [Fact s.Prime]
    (hq5 : 5 ≤ q') (hM : Squarefree M) (hsq' : s ≠ q') (hsM : ¬ s ∣ M)
    {a b : ℚ} (hdef : IsDefiniteRamifiedExactlyAt (a := a) (b := b) q')
    (Λ R : Submodule ℤ ℍ[ℚ, a, b]) (hΛ : IsMaximalOrder Λ) (hR : IsEichlerOrder R M) (hRΛ : R ≤ Λ)
    (n : (ℍ[ℚ, a, b] ⊗[ℚ] IsDedekindDomain.FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) (hn : n ∈ primeHeckeSet R s)
    (hS : IsEichlerOrder (meetOrder R n) (M * s))
    (hnorm : Submodule.conjByFiniteIdele (meetOrder R n) n = meetOrder R n)
    (hsq : ∀ x : ClassSet (Submodule.finiteIdeleStabilizer (meetOrder R n)),
      classSetShift _ n (classSetShift _ n x) = x)
    (A : ValuationSubring (AlgebraicClosure ℚ))
    [CharP (IsLocalRing.ResidueField ↥A) q'] [DecidableEq (IsLocalRing.ResidueField ↥A)]
    (X : SSLevelDatum q' (IsLocalRing.ResidueField ↥A) M s)
    [Fintype (ClassSet (Submodule.finiteIdeleStabilizer (meetOrder R n)))]
    [Fintype ↥(ssPlaces q' (M * s) (IsLocalRing.ResidueField ↥A))] :
    ∃ (eE : ClassSet (Submodule.finiteIdeleStabilizer (meetOrder R n)) ≃
          ↥(ssPlaces q' (M * s) (IsLocalRing.ResidueField ↥A)))
      (eV : ClassSet (Submodule.finiteIdeleStabilizer R) ≃ ↥(ssPlaces q' M (IsLocalRing.ResidueField ↥A))),
      (∀ e, X.degeneracyData.a (eE e) = eV ((classSetDegeneracyData R n).a e)) ∧
      (∀ e, X.degeneracyData.w (eE e) = (classSetDegeneracyData R n).w e) ∧
      (∀ (ℓ : Nat.Primes) (x : ClassSet (Submodule.finiteIdeleStabilizer (meetOrder R n)) → ℤ),
          (X.edgeHecke ℓ).mulVecLin (x ∘ eE.symm) = ((classSetEdgeHecke M s Λ R n ℓ).mulVecLin x) ∘ eE.symm) ∧
      (∀ e, eE (classSetShift _ n e) = X.atkinLehnerPerm (eE e)) := by
  classical
  haveI : IsAlgClosed (IsLocalRing.ResidueField ↥A) := ValuationSubring.isAlgClosed_residueField A
  letI : Algebra (ZMod q') (IsLocalRing.ResidueField ↥A) := ZMod.algebra _ q'
  haveI : Algebra.IsAlgebraic ℚ (AlgebraicClosure ℚ) := AlgebraicClosure.isAlgebraic ℚ
  haveI : Algebra.IsAlgebraic (ZMod q') (IsLocalRing.ResidueField ↥A) :=
    ValuationSubring.algebra_isAlgebraic_zmod_residueField_of_isAlgebraic_rat (AlgebraicClosure ℚ) A q'
  have hq'p : q'.Prime := Fact.out
  have hsp : s.Prime := Fact.out
  haveI : NeZero s := ⟨hsp.ne_zero⟩
  have hq'M : ¬ q' ∣ M := QuaternionAlgebra.IsEichlerOrder.not_dvd_of_isDefiniteRamifiedExactlyAt hq'p hdef hR
  have hRo : IsOrder R := hR.isOrder
  have hq'Ms : ¬ q' ∣ M * s := by
    intro h
    rcases (Nat.Prime.dvd_mul hq'p).mp h with h1 | h2
    · exact hq'M h1
    · exact hsq' ((Nat.prime_dvd_prime_iff_eq hq'p hsp).mp h2).symm

  have hle : Submodule.finiteIdeleStabilizer (meetOrder R n) ≤ Submodule.finiteIdeleStabilizer R :=
    (QuaternionAlgebra.IsOrder.finiteAdeleBox_inf_conjByFiniteIdele_eq_and_finiteIdeleStabilizer_le R hRo n).2.2.1
  haveI : Fintype (ClassSet (Submodule.finiteIdeleStabilizer R)) :=
    @Fintype.ofFinite _ (Finite.of_surjective _ (ClassSet.map_surjective hle))
  haveI : Fintype ↥(ssPlaces q' M (IsLocalRing.ResidueField ↥A)) :=
    @Fintype.ofFinite _ (ModularCurve.ssPlaces_finite q' M (IsLocalRing.ResidueField ↥A)).to_subtype

  obtain ⟨Λ₂, hΛ₂, hRdef, hRM⟩ := QuaternionAlgebra.IsEichlerOrder.exists_isMaximalOrder_eq_inf_relIndex_eq_of_squarefree hdef hM Λ R hΛ hR hRΛ
  subst hRdef
  obtain ⟨m, hm, hm₁, hmN⟩ :=
    QuaternionAlgebra.exists_conjByFiniteIdele_eq_mem_finiteAdeleBox_smul_inv_mem_of_relIndex_eq q' hdef Λ Λ₂ hΛ hΛ₂ M hq'M hRM
  subst hm

  obtain ⟨X₁, hX₁, hss₁, θ₁, hθ₁, hθ₁Λ⟩ :=
    WeierstrassCurve.exists_supersingular_rationalEndSubring_range_eq_of_isMaximalOrder q' a b hdef Λ hΛ
      (κ := IsLocalRing.ResidueField ↥A)
  haveI := hX₁

  obtain ⟨n₀, z, hnz, hn₀, hz, hmm', hm'₁, hm'N, hm', hS', hSNq⟩ :=
    QuaternionAlgebra.exists_eq_mul_mem_primeHeckeSet_mem_normalizer_meetOrder_eq_of_isEichlerOrder_meetOrder q' hdef Λ hΛ M hq'M
      m hm₁ hmN hΛ₂ (Λ ⊓ Submodule.conjByFiniteIdele Λ m) rfl hRM s (Ne.symm hsq') hsM n hS

  haveI hMs : NeZero (M * s) := ⟨Nat.mul_ne_zero (NeZero.ne M) (NeZero.ne s)⟩
  obtain ⟨eV, heV⟩ :=
    CerednikDrinfeld.exists_classSet_equiv_ssPlaces_forall_toValuationSubring_eq_comap_moduliPlace_ker q' X₁ hss₁ a b hdef Λ hΛ θ₁ hθ₁ hθ₁Λ
      M hq'M m hm₁ hmN hΛ₂ (Λ ⊓ Submodule.conjByFiniteIdele Λ m) rfl hRM
  obtain ⟨eE, heE⟩ :=
    CerednikDrinfeld.exists_classSet_equiv_ssPlaces_forall_toValuationSubring_eq_comap_moduliPlace_ker q' X₁ hss₁ a b hdef Λ hΛ θ₁ hθ₁ hθ₁Λ
      (M * s) hq'Ms (n₀ * m) hm'₁ hm'N hm' (meetOrder (Λ ⊓ Submodule.conjByFiniteIdele Λ m) n) hS' hSNq
  refine ⟨eE, eV, ?_, ?_, ?_, ?_⟩
  ·
    intro e
    have h1 : (classSetDegeneracyData (Λ ⊓ Submodule.conjByFiniteIdele Λ m) n).a e =
        ClassSet.mk (Submodule.finiteIdeleStabilizer (Λ ⊓ Submodule.conjByFiniteIdele Λ m)) e.out := rfl
    have he : ClassSet.mk (Submodule.finiteIdeleStabilizer (meetOrder (Λ ⊓ Submodule.conjByFiniteIdele Λ m) n)) e.out = e :=
      Quotient.out_eq' e
    rw [h1]
    apply Subtype.ext
    have h2 : (X.degeneracyData.a (eE e)).1 =
        Place.restrictAlong (levelAlphaC (IsLocalRing.ResidueField ↥A) M s X.mem_M) X.fstIntegral (eE e).1 := rfl
    rw [h2]
    conv_lhs => rw [← he]
    have hqm'm := QuaternionAlgebra.smul_inv_mul_mem_finiteAdeleBox_of_mem_primeHeckeSet_of_inv_mul_mul_mem q' hdef Λ hΛ M m hm₁ hmN s hsM n₀ hn₀ hmm'
    exact CerednikDrinfeld.restrictAlong_levelAlphaC_eq_of_forall_toValuationSubring_eq_comap_moduliPlace_of_prime q' X₁ hss₁ a b hdef Λ hΛ θ₁ hθ₁ hθ₁Λ
      M hq'M m hm₁ hmN hΛ₂ (Λ ⊓ Submodule.conjByFiniteIdele Λ m) rfl hRM s hsM hq'Ms (n₀ * m) hm'₁ hm'N hm'
      (meetOrder (Λ ⊓ Submodule.conjByFiniteIdele Λ m) n) hS' hSNq hmm' hqm'm eV heV eE heE X.mem_M X.fstIntegral e.out
  ·
    intro e
    show Nat.toPNat' (placeWidth (M * s) (eE e).1) = classWeight _ (meetOrder (Λ ⊓ Submodule.conjByFiniteIdele Λ m) n) e
    exact CerednikDrinfeld.toPNat_placeWidth_eq_classWeight_of_forall_toValuationSubring_eq_comap_moduliPlace q' X₁ hss₁ a b hdef Λ hΛ θ₁ hθ₁ hθ₁Λ M hq'M m hm₁ hmN hΛ₂ (Λ ⊓ Submodule.conjByFiniteIdele Λ m) rfl hRM
      s (Ne.symm hsq') hsM hq'Ms n₀ hn₀ hm'₁ hm'N hm' (meetOrder (Λ ⊓ Submodule.conjByFiniteIdele Λ m) n) hS' hSNq eE heE hq5 e
  ·
    intro ℓ x
    have hℓp : (ℓ : ℕ).Prime := ℓ.2
    haveI : NeZero (ℓ : ℕ) := ⟨hℓp.pos.ne'⟩
    by_cases hℓq' : (ℓ : ℕ) = q'
    ·
      have h1 : X.edgeHecke ℓ = ssFrobMatrixC q' (IsLocalRing.ResidueField ↥A) (M * s) X.frobData X.kronecker := by
        simp only [SSLevelDatum.edgeHecke, ssHeckeFamilyC, hℓq', ↓reduceIte]
      have hℓs : (ℓ : ℕ) ≠ s := by rw [hℓq']; exact Ne.symm hsq'
      have hℓM : ¬ (ℓ : ℕ) ∣ M := by rw [hℓq']; exact hq'M
      rw [h1, DeuringEichlerTransport.classSetEdgeHecke_eq_of_not_dvd M s Λ _ n ℓ hℓs hℓM, hℓq']
      exact DeuringEichlerTransport.mulVecLin_comp_symm_of_forall_apply_equiv _ _ eE (fun i j =>
        CerednikDrinfeld.ssFrobMatrixC_apply_eq_classSetHeckeMatrix_primeHeckeSet_of_forall_toValuationSubring_eq_comap_moduliPlace q' X₁ hss₁ a b hdef Λ hΛ θ₁ hθ₁ hθ₁Λ (M * s) hq'Ms (n₀ * m) hm'₁ hm'N hm'
          (meetOrder (Λ ⊓ Submodule.conjByFiniteIdele Λ m) n) hS' hSNq eE heE X.frobData X.kronecker i j) x
    · have h1 : X.edgeHecke ℓ = ssHeckeMatrixC q' (IsLocalRing.ResidueField ↥A) (M * s) ℓ
          (X.legsIntegral (M * s) ℓ).1 (X.legsIntegral (M * s) ℓ).2 := by
        simp only [SSLevelDatum.edgeHecke, ssHeckeFamilyC, hℓq', ↓reduceIte]
      rw [h1]
      by_cases hℓs : (ℓ : ℕ) = s
      ·
        have hR' : IsEichlerOrder (Λ ⊓ Submodule.conjByFiniteIdele Λ m) M := ⟨Λ, _, hΛ, hΛ₂, rfl, hRM⟩
        have hdvd : (ℓ : ℕ) ∣ M * s := hℓs ▸ dvd_mul_left s M
        rw [DeuringEichlerTransport.classSetEdgeHecke_eq_of_eq M s Λ _ n ℓ hℓs,
          CerednikDrinfeld.uHeckeSet_eq_levelHeckeUSet_meetOrder_of_mem_primeHeckeSet hdef Λ (Λ ⊓ Submodule.conjByFiniteIdele Λ m) hΛ hR' inf_le_left hsq' hsM n hn,
          show levelHeckeUSet Λ (meetOrder (Λ ⊓ Submodule.conjByFiniteIdele Λ m) n) s =
            levelHeckeUSet Λ (meetOrder (Λ ⊓ Submodule.conjByFiniteIdele Λ m) n) (ℓ : ℕ) from by rw [hℓs]]
        exact DeuringEichlerTransport.mulVecLin_comp_symm_of_forall_apply_equiv _ _ eE (fun i j =>
          CerednikDrinfeld.ssHeckeMatrixC_apply_eq_classSetHeckeMatrix_levelHeckeUSet_of_dvd_of_forall_toValuationSubring_eq_comap_moduliPlace_of_five_le q' hq5 X₁ hss₁ a b hdef Λ hΛ θ₁ hθ₁ hθ₁Λ (M * s) hq'Ms (n₀ * m) hm'₁ hm'N hm'
            (meetOrder (Λ ⊓ Submodule.conjByFiniteIdele Λ m) n) hS' hSNq eE heE ℓ hℓp hℓq' hdvd
            (X.legsIntegral (M * s) ℓ).1 (X.legsIntegral (M * s) ℓ).2 i j) x
      · by_cases hℓM : (ℓ : ℕ) ∣ M
        ·
          have hdvd : (ℓ : ℕ) ∣ M * s := dvd_mul_of_dvd_left hℓM s
          rw [DeuringEichlerTransport.classSetEdgeHecke_eq_of_dvd M s Λ _ n ℓ hℓs hℓM]
          exact DeuringEichlerTransport.mulVecLin_comp_symm_of_forall_apply_equiv _ _ eE (fun i j =>
            CerednikDrinfeld.ssHeckeMatrixC_apply_eq_classSetHeckeMatrix_levelHeckeUSet_of_dvd_of_forall_toValuationSubring_eq_comap_moduliPlace_of_five_le q' hq5 X₁ hss₁ a b hdef Λ hΛ θ₁ hθ₁ hθ₁Λ (M * s) hq'Ms (n₀ * m) hm'₁ hm'N hm'
              (meetOrder (Λ ⊓ Submodule.conjByFiniteIdele Λ m) n) hS' hSNq eE heE ℓ hℓp hℓq' hdvd
              (X.legsIntegral (M * s) ℓ).1 (X.legsIntegral (M * s) ℓ).2 i j) x
        ·
          have hℓMs : ¬ (ℓ : ℕ) ∣ M * s := by
            intro h
            rcases (Nat.Prime.dvd_mul hℓp).mp h with h1 | h2
            · exact hℓM h1
            · exact hℓs ((Nat.prime_dvd_prime_iff_eq hℓp hsp).mp h2)
          rw [DeuringEichlerTransport.classSetEdgeHecke_eq_of_not_dvd M s Λ _ n ℓ hℓs hℓM]
          exact DeuringEichlerTransport.mulVecLin_comp_symm_of_forall_apply_equiv _ _ eE (fun i j =>
            CerednikDrinfeld.ssHeckeMatrixC_apply_eq_classSetHeckeMatrix_primeHeckeSet_of_forall_toValuationSubring_eq_comap_moduliPlace q' X₁ hss₁
              a b hdef Λ hΛ θ₁ hθ₁ hθ₁Λ (M * s) hq'Ms (n₀ * m) hm'₁ hm'N hm' (meetOrder (Λ ⊓ Submodule.conjByFiniteIdele Λ m) n) hS' hSNq
              eE heE ℓ hℓp hℓq' hℓMs (X.legsIntegral (M * s) ℓ).1 (X.legsIntegral (M * s) ℓ).2 i j) x
  ·
    intro e
    have he : ClassSet.mk (Submodule.finiteIdeleStabilizer (meetOrder (Λ ⊓ Submodule.conjByFiniteIdele Λ m) n)) e.out = e :=
      Quotient.out_eq' e
    apply Subtype.ext
    show (eE (ClassSet.mk _ (e.out * n))).1 = autOnPlaces (IsLocalRing.ResidueField ↥A) M s X.atkinLehnerAut (eE e).1
    conv_rhs => rw [← he]
    exact CerednikDrinfeld.autOnPlaces_eq_of_isAtkinLehnerLevelAut_of_forall_toValuationSubring_eq_comap_moduliPlace q' X₁ hss₁ a b hdef Λ hΛ θ₁ hθ₁ hθ₁Λ M hq'M m hm₁ hmN hΛ₂ (Λ ⊓ Submodule.conjByFiniteIdele Λ m) rfl hRM
      s hsM hq'Ms (n₀ * m) hm'₁ hm'N hm' (meetOrder (Λ ⊓ Submodule.conjByFiniteIdele Λ m) n) hS' hSNq eE heE
      n hn rfl hnorm X.mem_M X.mem_s X.atkinLehnerAut X.isAtkinLehner e.out

end S_CerednikDrinfeld_exists_equiv_classSet_ssPlaces_degeneracy_hecke_comm
end P2MW
export P2MW.S_CerednikDrinfeld_exists_equiv_classSet_ssPlaces_degeneracy_hecke_comm (solution)
