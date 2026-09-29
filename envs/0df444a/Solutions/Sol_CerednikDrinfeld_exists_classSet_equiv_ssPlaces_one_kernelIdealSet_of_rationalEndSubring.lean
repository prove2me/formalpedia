-- Prove2me | solution 1 for CerednikDrinfeld.exists_classSet_equiv_ssPlaces_one_kernelIdealSet_of_rationalEndSubring
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.491319+00:00
-- url     : https://prove2.me/submissions/29f9620d-7017-5adb-99bd-785d1de33f28

import Mathlib
import Definitions.Def_QuaternionAlgebra_EichlerOrder
import Definitions.Def_WeierstrassCurve_RationalEnd
import Definitions.Def_WeierstrassCurve_KernelIdeal
import Definitions.Def_CerednikDrinfeld_ClassSetGraph
import Definitions.Def_ModularCurve_SSDegeneracyHecke
import Theorems.Thm_WeierstrassCurve_exists_image_kernelIdealSet_eq_star_smul_ofFiniteIdele_and_range_eq_conjByFiniteIdele
import Theorems.Thm_CerednikDrinfeld_classSet_mk_eq_iff_nonempty_variableChange_of_kernelIdealSet
import Theorems.Thm_CerednikDrinfeld_exists_kernelIdealSet_eq_star_smul_ofFiniteIdele
import Theorems.Thm_ModularCurve_ssHeckeMatrixC_one_apply_eq_natCard_subgroup_dualPair
import Theorems.Thm_QuaternionAlgebra_IsOrder_heckeKernel_primeHeckeSet_mk_mk_eq_natCard
import Theorems.Thm_CerednikDrinfeld_natCard_subideal_primeHeckeSet_eq_natCard_subgroup_dualPair_of_kernelIdealSet
import Theorems.Thm_WeierstrassCurve_exists_ne_zero_mem_rationalHomSet_of_forall_nsmul_char_eq_zero
import Theorems.Thm_WeierstrassCurve_surjective_of_mem_rationalHomSet
import Theorems.Thm_WeierstrassCurve_exists_addEquiv_point_variableChange
import Theorems.Thm_ModularCurve_mem_ssPlaces_one_iff_exists_charLGeomPlaceOfPoint_eq
import Theorems.Thm_ModularCurve_eq_charLGeomPlaceOfPoint_of_ord_pos
import Theorems.Thm_Submodule_ofFiniteIdele_eq_ofFiniteIdele_iff
import Theorems.Thm_Submodule_ofFiniteIdele_diagonal_mul
import Theorems.Thm_Submodule_conjByFiniteIdele_mul_eq_of_mem_finiteIdeleStabilizer
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_exists_classSet_equiv_ssPlaces_one_kernelIdealSet_of_rationalEndSubring
p2m_attr_erase "instance" "WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly TateModule.instModule TateModule.instSMul GaloisRepAdic.instAddCommGroup GaloisRepAdic.instFree GaloisRepAdic.instFinite GaloisRepAdic.instModule ResidualGaloisRep.instModule ResidualGaloisRep.instModuleFinite ResidualGaloisRep.instAddCommGroup WeierstrassCurve.Affine.Point.instFinite WeierstrassCurve.Affine.CoordinateRing.moduleFinite WeierstrassCurve.Affine.instDecidableEqFunctionField WeierstrassCurve.Affine.CoordinateRing.isIntegral AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt WeierstrassCurve.Affine.instIsScalarTowerPolynomialRatFuncFunctionField_definitions WeierstrassCurve.Affine.instAlgebraRatFuncFunctionField_definitions WeierstrassCurve.Affine.instIsScalarTowerRatFuncFunctionField_definitions ModularCurve.ModuliTestDatum.isElliptic_reduced ModularCurve.ModuliTestDatum.isElliptic_curve ModularCurve.ModuliTestDatum.isElliptic_generic ModularCurve.PhiGen.instNeZeroPhiGenCosetA ModularCurve.ElevenA1.instDecidableEquation ModularCurve.ElevenA1.instDecidableNonsingular ModularCurve.instIsElliptic_tateBase ModularCurve.instIsElliptic_tateLaurent ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid WeierstrassCurve.VeluQuotientJGates.instIsElliptic27a4 CyclotomicUniv.instCharZeroR₀ CyclotomicUniv.instIsDomain CyclotomicUniv.instIsDomainR₀ CyclotomicUniv.instCharZero"
p2m_attr_erase "instance" "ModularCurve.KatzGamma0Form.instModule ModularCurve.KatzGamma0Form.instZero ModularCurve.KatzLevelPForm.instSMul ModularCurve.KatzGamma0Form.instAdd ModularCurve.KatzLevelPForm.instAddCommGroup ModularCurve.KatzGamma0Form.instNeg ModularCurve.KatzGamma0Form.instAddCommGroup ModularCurve.KatzLevelPForm.instAdd ModularCurve.KatzLevelPForm.instSub ModularCurve.KatzLevelPForm.instNeg ModularCurve.KatzGamma0Form.instSMul ModularCurve.KatzGamma0Form.instSub ModularCurve.KatzLevelPForm.instZero ModularCurve.KatzLevelPForm.instModule KatzModularForm.instAddCommGroup KatzModularForm.instSub KatzModularForm.instZero KatzModularForm.instModule KatzModularForm.instAdd KatzModularForm.instNeg KatzModularForm.instSMul AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions"
p2m_attr_erase "simp" "AddMonoid.End.DualEndData.symm_trace AddMonoid.End.dualEndData_intCast_norm AddMonoid.End.DualEndData.ofCharPoly_norm AddMonoid.End.DualEndData.mk.sizeOf_spec AddMonoid.End.DualEndData.mk.injEq AddMonoid.End.DualEndData.ofCharPoly_dual AddMonoid.End.dualEndData_intCast_dual AddMonoid.End.DualEndData.intLinComb_norm AddMonoid.End.DualEndData.ofCharPoly_trace AddMonoid.End.DualEndData.intLinComb_dual AddMonoid.End.DualEndData.symm_dual AddMonoid.End.DualEndData.intLinComb_trace AddMonoid.End.dualEndData_intCast_trace AddMonoid.End.DualEndData.symm_norm AddMonoid.End.dualEndDataOfSurjective_trace AddMonoid.End.dualEndDataOfSurjective_norm compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆"
p2m_attr_erase "simp" "Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two WeierstrassCurve.Universal.halveX_zero WeierstrassCurve.Universal.specialize_X_one WeierstrassCurve.Universal.coeff_halve WeierstrassCurve.Universal.specialize_X_two WeierstrassCurve.Universal.halveCoeff_zero WeierstrassCurve.Universal.specialize_X_four WeierstrassCurve.Universal.coeff_halveX WeierstrassCurve.Universal.specialize_X_three WeierstrassCurve.Universal.specialize_X_zero TateModule.smul_apply TateModule.coe_mulP TateModule.proj_apply TateModule.coe_add TateModule.coe_sub WeierstrassCurve.tateModuleRepOfBasis_V TateModule.coe_zero TateModule.rep_apply WeierstrassCurve.tateModuleRep_V WeierstrassCurve.tateModuleRepOfBasis_ρ_apply GaloisRep.padicIntToRingLevel_apply TateModule.coe_neg WeierstrassCurve.tateModuleRep_ρ_apply GaloisRepAdic.mk.injEq GaloisRepAdic.mk.sizeOf_spec GaloisRepAdic.Equiv.mk.sizeOf_spec GaloisRepAdic.Equiv.mk.injEq ResidualGaloisRep.mk.sizeOf_spec ResidualGaloisRep.mk.injEq ResidualGaloisRep.Equiv.mk.sizeOf_spec ResidualGaloisRep.Equiv.mk.injEq FrobeniusEndo.linePencil_apply"
p2m_attr_erase "simp" "WeierstrassCurve.Affine.mem_fibSet WeierstrassCurve.Affine.pointHom_mk_C_C WeierstrassCurve.Affine.Point.yc_some WeierstrassCurve.Affine.Point.xc_some WeierstrassCurve.Affine.pointPull_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_X WeierstrassCurve.Affine.pointHom_mk_Y WeierstrassCurve.Affine.placeOf_asIdeal WeierstrassCurve.veluWSum_empty WeierstrassCurve.veluQuotient_a₁ WeierstrassCurve.veluQuotient_a₃ WeierstrassCurve.veluQuotient_empty WeierstrassCurve.veluTSum_empty WeierstrassCurve.veluQuotient_a₂ WeierstrassCurve.veluX_empty WeierstrassCurve.veluY_empty WeierstrassCurve.Affine.Point.coordsOrZero_some WeierstrassCurve.Affine.Point.coordsOrZero_zero WeierstrassCurve.Affine.IsogenyEndDatum.mk.injEq WeierstrassCurve.Affine.IsogenyHomDatum.mk.sizeOf_spec WeierstrassCurve.Affine.IsogenyHomDatum.mk.injEq WeierstrassCurve.Affine.IsogenyEndDatum.mk.sizeOf_spec AlgebraicCurve.Pic0.coe_pushforwardAlongDegZero WeierstrassCurve.Affine.pointMapOfPushforward_apply WeierstrassCurve.Affine.pointClass_zero WeierstrassCurve.Affine.pic0ToPoint_pointClass WeierstrassCurve.Affine.deg_placeOfPoint WeierstrassCurve.Affine.coe_pointDivisor WeierstrassCurve.Affine.pointEquivPlace_symm_placeOfPoint WeierstrassCurve.Affine.pointEquivPlace_apply WeierstrassCurve.Affine.genusOnePic0Equiv_symm_apply WeierstrassCurve.Affine.pointDivisor_zero WeierstrassCurve.Affine.pic0ToPoint_mk WeierstrassCurve.Affine.divisorSum_single WeierstrassCurve.Affine.genusOnePic0Equiv_apply AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal"
p2m_attr_erase "simp" "WeierstrassCurve.vcInvEmbedding_apply WeierstrassCurve.map_veluU WeierstrassCurve.map_veluT WeierstrassCurve.map_veluW WeierstrassCurve.map_veluGy WeierstrassCurve.map_veluGx WeierstrassCurve.map_veluWSum_singleton WeierstrassCurve.map_veluTSum_singleton WeierstrassCurve.veluPointMap3_zero WeierstrassCurve.Affine.ratFuncToFunctionField_algebraMap WeierstrassCurve.frobPoint_zero WeierstrassCurve.frobCardHom_apply QuaternionAlgebra.baseChangeRight_tmul QuaternionAlgebra.mapOfAlgebraMapEq_apply QuaternionAlgebra.baseChange_tmul WeierstrassCurve.pointAddEquivOfEq_refl WeierstrassCurve.veluPointMap2_zero WeierstrassCurve.veluQuotient2_a₂ WeierstrassCurve.veluQuotient2_a₃ WeierstrassCurve.veluQuotient2_a₁ ModularCurve.qExpandAlgHomC_apply ModularCurve.coeffEmb_coeff ModularCurve.coeffMap_coeff ModularCurve.coeffMap_id ModularCurve.coeffMap_single WeierstrassCurve.veluQuotientOfSums_a₂ WeierstrassCurve.veluQuotientOfSums_a₁ WeierstrassCurve.veluQuotientOfSums_a₃ ModularCurve.ComapPlace.place_toValuationSubring ModularCurve.ModuliTestDatum.restrictLevel_emb ModularCurve.ModuliTestDatum.restrictLevel_res ModularCurve.ModuliTestDatum.mk.injEq ModularCurve.ModuliTestDatum.restrictLevel_W ModularCurve.ModuliTestDatum.place_toValuationSubring ModularCurve.ModuliTestDatum.restrictLevel_curve ModularCurve.ModuliTestDatum.resEquiv_apply ModularCurve.ModuliTestDatum.restrictLevel_gen ModularCurve.ModuliTestDatum.mk.sizeOf_spec ModularCurve.coe_jqNFull ModularCurve.Gamma0Pair.map_toCurve"
p2m_attr_erase "simp" "WeierstrassCurve.mapPoint_eq_ratPointMap ModularCurve.Gamma0Pair.map_gen ModularCurve.Gamma0Pair.map_eq_gamma0PairMap ModularCurve.ModuliPoint.map_eq_moduliPointMapRingHom ModularCurve.ModuliPoint.map_mk WeierstrassCurve.mapPointHom_apply WeierstrassCurve.mapPoint_zero WeierstrassCurve.reducePoint_zero WeierstrassCurve.Affine.Point.galoisRep_apply WeierstrassCurve.twoVeluCurve_a₁ WeierstrassCurve.twoVeluCurve_a₂ WeierstrassCurve.twoVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₂ WeierstrassCurve.xVeluCurve_a₁ ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL WeierstrassCurve.Affine.Point.netCol_one WeierstrassCurve.Affine.Point.xOrZero_zero WeierstrassCurve.Affine.Point.netPairing_zero_right WeierstrassCurve.Affine.Point.netW20_some WeierstrassCurve.Affine.Point.netCol_zero"
p2m_attr_erase "simp" "WeierstrassCurve.Affine.Point.netPairing_zero_left WeierstrassCurve.Affine.Point.xOrZero_some WeierstrassCurve.Affine.Point.netW20_zero TateCurve.cauchyMulInt_zero TateCurve.cauchyMulInt3_zero TateCurve.tent_one TateCurve.Gz_zero TateCurve.cauchyMulInt_one TateCurve.tent_zero TateCurve.Fz_zero TateCurve.xCoeffFull_succ TateCurve.a₆Coeff_zero TateCurve.a₄Coeff_succ TateCurve.a₄Coeff_zero TateCurve.cauchyMul_zero TateCurve.a₆Coeff_succ TateCurve.yCoeffFull_succ TateCurve.xCoeffFull_zero TateCurve.yCoeffFull_zero TateCurve.yfun_zero TateCurve.xfun_zero TateCurve.yTerm_zero TateCurve.xTerm_zero TateCurve.curve_a₂ TateCurve.b_one TateCurve.curve_a₁ TateCurve.term_zero TateCurve.curve_a₆ TateCurve.curve_a₄ TateCurve.curve_a₃ FLT.DivisorConvolution.sigma_zero_right FLT.DivisorConvolution.sigma_one_right FLT.DivisorConvolution.sigmaConv_one FLT.DivisorConvolution.sigmaConv_zero FormalCoordinates.mk.injEq WeierstrassCurve.formalParam_zero WeierstrassCurve.SmoothLocusReductionData.reduceHom₀_apply WeierstrassCurve.formalParam_some FormalCoordinates.mk.sizeOf_spec WeierstrassCurve.SmoothLocusReductionData.mk.injEq"
p2m_attr_erase "simp" "WeierstrassCurve.reducePointSmooth_zero WeierstrassCurve.SmoothLocusReductionData.mk.sizeOf_spec WeierstrassCurve.mem_zeroComponentSubgroup_iff ModularCurve.tateUnivCurve_a₂ ModularCurve.tateUnivCurve_a₃ ModularCurve.tateUnivCurve_a₆ ModularCurve.nonToricPoint_fst ModularCurve.toricPoint_snd ModularCurve.tateUnivCurve_a₁ ModularCurve.nonToricPoint_snd ModularCurve.tateUnivCurve_a₄ ModularCurve.toricPoint_fst ModularCurve.tateLaurent_a₆ ModularCurve.tatePowerSeries_a₄ ModularCurve.tatePowerSeries_a₆ ModularCurve.tateLaurent_a₄ ModularCurve.tatePowerSeries_a₁ ModularCurve.tatePowerSeries_a₂ ModularCurve.tatePowerSeries_a₃ ModularCurve.ProjectiveLine.map_mk PeriodPair.weierstrassCurve_a₆ PeriodPair.weierstrassCurve_a₃ PeriodPair.weierstrassCurve_a₁ PeriodPair.ofTau_ω₂ PeriodPair.scale_ω₂ PeriodPair.ofTau_ω₁ PeriodPair.toPoint_zero PeriodPair.toPoint_of_mem PeriodPair.weierstrassCurve_a₂ PeriodPair.ofTau_lattice PeriodPair.scale_ω₁ PeriodPair.weierstrassCurve_a₄ CyclotomicUniv.lift₀_ζ₀ CyclotomicUniv.lift_algebraMap CyclotomicUniv.val_ζUnit CyclotomicUniv.lift_ζ ModularCurve.cuspData_yP ModularCurve.qTwistAlgHom_apply ModularCurve.cuspData_yQ ModularCurve.cuspData_xP"
p2m_attr_erase "simp" "ModularCurve.cuspData_xQ ModularCurve.val_cyclZeta ModularCurve.cuspShift_one ModularCurve.cuspShift_zero ModularCurve.LevelPData.mk.sizeOf_spec ModularCurve.KatzLevelPForm.neg_toFun ModularCurve.LevelP.coe_swapW ModularCurve.KatzLevelPForm.swap_swap KatzModularForm.pullbackLevelP_toFun ModularCurve.LevelPData.swap_xQ KatzModularForm.pullbackLevelP_zero ModularCurve.LevelPData.map_yP ModularCurve.KatzLevelPForm.swap_neg ModularCurve.KatzGamma0Form.toKatzLevelPForm_sub ModularCurve.KatzLevelPForm.swap_add KatzModularForm.swap_pullbackLevelP ModularCurve.KatzGamma0Form.toKatzLevelPForm_add ModularCurve.KatzLevelPForm.swap_smul ModularCurve.LevelPData.map_yQ ModularCurve.KatzLevelPForm.mk.injEq ModularCurve.KatzLevelPForm.zero_toFun KatzModularForm.pullbackLevelP_smul ModularCurve.LevelPData.swap_xP ModularCurve.KatzGamma0Form.toKatzLevelPForm_mul ModularCurve.KatzGamma0Form.toKatzLevelPForm_neg ModularCurve.LevelPData.variableChange_xQ KatzModularForm.pullbackGamma0_toKatzLevelPForm ModularCurve.KatzLevelPForm.mk.sizeOf_spec ModularCurve.KatzLevelPForm.swap_zero ModularCurve.LevelP.coe_unipotentU ModularCurve.KatzLevelPForm.mul_toFun ModularCurve.LevelPData.variableChange_yP ModularCurve.LevelPData.mk.injEq ModularCurve.KatzLevelPForm.sub_toFun ModularCurve.LevelPData.variableChange_xP ModularCurve.KatzLevelPForm.smul_toFun ModularCurve.LevelPData.swap_yP ModularCurve.LevelPData.map_xP ModularCurve.LevelPData.swap_swap ModularCurve.LevelPData.swap_yQ"
p2m_attr_erase "simp" "ModularCurve.KatzGamma0Form.toKatzLevelPForm_zero ModularCurve.KatzGamma0Form.mk.injEq ModularCurve.KatzLevelPForm.swap_toFun KatzModularForm.pullbackLevelP_add ModularCurve.KatzGamma0Form.mk.sizeOf_spec ModularCurve.LevelPData.variableChange_yQ ModularCurve.KatzLevelPForm.swap_sub ModularCurve.KatzGamma0Form.toKatzLevelPForm_smul ModularCurve.LevelPData.map_xQ ModularCurve.KatzLevelPForm.add_toFun KatzModularForm.c₆_toFun KatzModularForm.neg_toFun KatzModularForm.mul_toFun KatzModularForm.qExpansion_neg KatzModularForm.discr_toFun KatzModularForm.qExpansion_sub KatzModularForm.qExpansion_add KatzModularForm.qExpansion_mul KatzModularForm.zero_toFun KatzModularForm.mk.injEq KatzModularForm.qExpansion_smul KatzModularForm.smul_toFun KatzModularForm.add_toFun KatzModularForm.sub_toFun KatzModularForm.c₄_toFun KatzModularForm.qExpansion_zero KatzModularForm.mk.sizeOf_spec TateCurve.tateTorsionPoint_zero_zero AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none WeierstrassCurve.kernelPolynomial_singleton WeierstrassCurve.kernelPolynomial_empty WeierstrassCurve.kohelW_one Polynomial.rootESymm_zero_right WeierstrassCurve.kohelQuotient_a₂ WeierstrassCurve.kohelQuotient_a₃ WeierstrassCurve.kohelT_one"
p2m_attr_erase "simp" "WeierstrassCurve.kohelQuotient_one WeierstrassCurve.kohelQuotient_a₁ Polynomial.rootESymm_one WeierstrassCurve.legendreVariableChange_s WeierstrassCurve.legendreVariableChange_t WeierstrassCurve.legendreVariableChange_r WeierstrassCurve.legendreVariableChange_u WeierstrassCurve.deuringVariableChange_s WeierstrassCurve.deuringVariableChange_t WeierstrassCurve.deuringCurve_a₄ WeierstrassCurve.deuringCurve_a₂ WeierstrassCurve.deuringCurve_a₆ WeierstrassCurve.deuringCurve_a₁ WeierstrassCurve.deuringVariableChange_u WeierstrassCurve.deuringCurve_a₃ WeierstrassCurve.deuringVariableChange_r"

set_option autoImplicit false

open scoped Quaternion TensorProduct NumberField Pointwise
p2m_open "QuaternionAlgebra~baseChange CerednikDrinfeld P2MW.S_CerednikDrinfeld_exists_classSet_equiv_ssPlaces_one_kernelIdealSet_of_rationalEndSubring.CerednikDrinfeld ModularCurve IsDedekindDomain"

namespace CerednikDrinfeld
p2m_export "CerednikDrinfeld" "classSetHeckeMatrix classSet_mk_eq_iff_nonempty_variableChange_of_kernelIdealSet exists_kernelIdealSet_eq_star_smul_ofFiniteIdele natCard_subideal_primeHeckeSet_eq_natCard_subgroup_dualPair_of_kernelIdealSet"
namespace LevelOneDeuringAssembly
p2m_open "CerednikDrinfeld"

section Torsion

open WeierstrassCurve Polynomial

variable {F : Type*} [Field F] {k : Type*} [Field k] [Algebra F k] [DecidableEq k]

def Good (W : WeierstrassCurve F) (B : Set k) (P : (W.baseChange k).toAffine.Point) : Prop :=
  ∃ (x y : k) (h : (W.baseChange k).toAffine.Nonsingular x y), P = .some x y h ∧ x ∉ B

omit [DecidableEq k] in
theorem finite_setOf_equation (W : WeierstrassCurve F) (x : k) :
    {y : k | (W.baseChange k).toAffine.Equation x y}.Finite := by
  have hne : ((W.baseChange k).toAffine.polynomial.map (evalRingHom x)) ≠ 0 :=
    (WeierstrassCurve.Affine.monic_polynomial.map _).ne_zero
  refine (Polynomial.finite_setOf_isRoot hne).subset ?_
  intro y hy
  simp only [Set.mem_setOf_eq, IsRoot.def, map_evalRingHom_eval]
  exact hy

omit [DecidableEq k] in
theorem finite_not_good (W : WeierstrassCurve F) {B : Set k} (hB : B.Finite) :
    {P : (W.baseChange k).toAffine.Point | ¬ Good W B P}.Finite := by
  have hfin : (insert (0 : (W.baseChange k).toAffine.Point)
      (⋃ x ∈ B, ⋃ y ∈ {y : k | (W.baseChange k).toAffine.Equation x y},
        {P : (W.baseChange k).toAffine.Point |
          ∃ h : (W.baseChange k).toAffine.Nonsingular x y, P = .some x y h})).Finite := by
    refine Set.Finite.insert _ (Set.Finite.biUnion hB fun x _ => ?_)
    refine Set.Finite.biUnion (finite_setOf_equation (k := k) W x) fun y _ => ?_
    refine Set.Subsingleton.finite ?_
    rintro P ⟨h1, rfl⟩ Q ⟨h2, rfl⟩
    rfl
  refine hfin.subset ?_
  intro P hP
  simp only [Set.mem_setOf_eq, Good, not_exists, not_and, not_not] at hP
  rcases P with _ | ⟨x, y, h⟩
  · exact Set.mem_insert _ _
  · refine Set.mem_insert_of_mem _ ?_
    simp only [Set.mem_iUnion, Set.mem_setOf_eq]
    exact ⟨x, hP x y h rfl, y, h.left, h, rfl⟩

theorem finite_ker {W₁ W₂ : WeierstrassCurve F}
    {α : (W₁.baseChange k).toAffine.Point →+ (W₂.baseChange k).toAffine.Point}
    (hα : IsRationallyRepresented k W₁ W₂ α) : {P | α P = 0}.Finite := by
  obtain ⟨nX, dX, nY, dY, B, hB, hrep⟩ := hα
  refine (finite_not_good W₁ hB).subset ?_
  rintro P (hP : α P = 0) ⟨x, y, h, rfl, hx⟩
  obtain ⟨-, -, h', hP'⟩ := hrep x y h hx
  rw [hP'] at hP
  exact absurd hP (by rintro ⟨⟩)

theorem noTorsion_of_hom [IsAlgClosed k] {W₁ W₂ : WeierstrassCurve F} [W₁.IsElliptic] [W₂.IsElliptic]
    {χ : (W₁.baseChange k).toAffine.Point →+ (W₂.baseChange k).toAffine.Point}
    (hχ : χ ∈ rationalHomSet k W₁ W₂) (hχ0 : χ ≠ 0) (p : ℕ)
    (h₁ : ∀ P : (W₁.baseChange k).toAffine.Point, p • P = 0 → P = 0) :
    ∀ P : (W₂.baseChange k).toAffine.Point, p • P = 0 → P = 0 := by
  intro P hP
  have hsurj := WeierstrassCurve.surjective_of_mem_rationalHomSet k hχ hχ0
  obtain ⟨Q, rfl⟩ := hsurj P
  set K : Set (W₁.baseChange k).toAffine.Point := {R | χ R = 0} with hK
  have hKfin : K.Finite := finite_ker (hχ.resolve_left hχ0)
  set S : Set (W₁.baseChange k).toAffine.Point := {R | χ (p • R) = 0} with hS
  have hinj : Set.InjOn (fun R : (W₁.baseChange k).toAffine.Point => p • R) Set.univ := by
    intro R _ R' _ hRR'
    have h0 : p • (R - R') = 0 := by
      simp only [smul_sub, sub_eq_zero]; exact hRR'
    exact sub_eq_zero.mp (h₁ _ h0)
  have hKS : K ⊆ S := by
    intro R hR
    simp only [hS, Set.mem_setOf_eq, map_nsmul]
    rw [show χ R = 0 from hR, smul_zero]
  have hmaps : ∀ R ∈ S, (fun R : (W₁.baseChange k).toAffine.Point => p • R) R ∈ K := fun R hR => hR
  have hle : S.ncard ≤ K.ncard :=
    Set.ncard_le_ncard_of_injOn (fun R => p • R) hmaps (hinj.mono (Set.subset_univ _)) hKfin
  have hSfin : S.Finite := by
    have : S = (fun R : (W₁.baseChange k).toAffine.Point => p • R) ⁻¹' K := rfl
    rw [this]
    exact hKfin.preimage (hinj.mono (Set.subset_univ _))
  have hKeq : K = S := Set.eq_of_subset_of_ncard_le hKS hle hSfin
  have hQS : Q ∈ S := by
    simp only [hS, Set.mem_setOf_eq, map_nsmul]
    exact hP
  rw [← hKeq] at hQS
  exact hQS

end Torsion

section Quaternion

variable {a b : ℚ}

def unitConj (e : (ℍ[ℚ, a, b])ˣ) : ℍ[ℚ, a, b] →+* ℍ[ℚ, a, b] where
  toFun y := (e : ℍ[ℚ, a, b]) * y * ((e⁻¹ : (ℍ[ℚ, a, b])ˣ) : ℍ[ℚ, a, b])
  map_one' := by simp
  map_mul' y z := by simp only [mul_assoc, Units.inv_mul_cancel_left]
  map_zero' := by simp
  map_add' y z := by simp only [mul_add, add_mul]

theorem unitConj_apply (e : (ℍ[ℚ, a, b])ˣ) (y : ℍ[ℚ, a, b]) :
    unitConj e y = (e : ℍ[ℚ, a, b]) * y * ((e⁻¹ : (ℍ[ℚ, a, b])ˣ) : ℍ[ℚ, a, b]) := rfl

theorem unitConj_inv_apply_unitConj (e : (ℍ[ℚ, a, b])ˣ) (y : ℍ[ℚ, a, b]) :
    unitConj e⁻¹ (unitConj e y) = y := by
  simp only [unitConj_apply, inv_inv, ← mul_assoc, Units.inv_mul, one_mul, Units.inv_mul_cancel_right]

theorem unitConj_apply_unitConj_inv (e : (ℍ[ℚ, a, b])ˣ) (y : ℍ[ℚ, a, b]) :
    unitConj e (unitConj e⁻¹ y) = y := by
  simpa only [inv_inv] using unitConj_inv_apply_unitConj e⁻¹ y

theorem unitConj_injective (e : (ℍ[ℚ, a, b])ˣ) : Function.Injective (unitConj e) :=
  Function.LeftInverse.injective (unitConj_inv_apply_unitConj e)

end Quaternion

section Adelic

variable {a b : ℚ} (Λ : Submodule ℤ ℍ[ℚ, a, b])

theorem ofFiniteIdele_mul_of_mem (hΛ : IsOrder Λ)
    (x u : (ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) (hu : u ∈ Submodule.finiteIdeleStabilizer Λ) :
    Submodule.ofFiniteIdele Λ (x * u) = Submodule.ofFiniteIdele Λ x :=
  ((Submodule.ofFiniteIdele_eq_ofFiniteIdele_iff Λ hΛ.fg hΛ.spanTop x (x * u)).mpr
    (by rwa [inv_mul_cancel_left])).symm

theorem exists_ofFiniteIdele_eq_smul_of_mk_eq_mk (hΛ : IsOrder Λ)
    {x x' : (ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ}
    (h : ClassSet.mk (Submodule.finiteIdeleStabilizer Λ) x = ClassSet.mk (Submodule.finiteIdeleStabilizer Λ) x') :
    ∃ δ : (ℍ[ℚ, a, b])ˣ, Submodule.ofFiniteIdele Λ x' = δ • Submodule.ofFiniteIdele Λ x := by
  obtain ⟨g, hg, u, hu, rfl⟩ := (DoubleCoset.eq _ _ _ _).mp h
  obtain ⟨δ, rfl⟩ := MonoidHom.mem_range.mp hg
  exact ⟨δ, by rw [ofFiniteIdele_mul_of_mem Λ hΛ _ u hu, Submodule.ofFiniteIdele_diagonal_mul]⟩

theorem exists_mem_stabilizer_of_ofFiniteIdele_eq_smul (hΛ : IsOrder Λ)
    {x x' : (ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ} (δ : (ℍ[ℚ, a, b])ˣ)
    (h : Submodule.ofFiniteIdele Λ x' = δ • Submodule.ofFiniteIdele Λ x) :
    ∃ u ∈ Submodule.finiteIdeleStabilizer Λ, x' = Submodule.finiteIdeleDiagonal ℍ[ℚ, a, b] δ * x * u := by
  rw [← Submodule.ofFiniteIdele_diagonal_mul] at h
  have hu := (Submodule.ofFiniteIdele_eq_ofFiniteIdele_iff Λ hΛ.fg hΛ.spanTop
    (Submodule.finiteIdeleDiagonal ℍ[ℚ, a, b] δ * x) x').mp h.symm
  exact ⟨_, hu, by rw [mul_inv_cancel_left]⟩

theorem mk_eq_mk_of_ofFiniteIdele_eq_smul (hΛ : IsOrder Λ)
    {x x' : (ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ} (δ : (ℍ[ℚ, a, b])ˣ)
    (h : Submodule.ofFiniteIdele Λ x' = δ • Submodule.ofFiniteIdele Λ x) :
    ClassSet.mk (Submodule.finiteIdeleStabilizer Λ) x' = ClassSet.mk (Submodule.finiteIdeleStabilizer Λ) x := by
  obtain ⟨u, hu, rfl⟩ := exists_mem_stabilizer_of_ofFiniteIdele_eq_smul Λ hΛ δ h
  exact ((DoubleCoset.eq _ _ _ _).mpr ⟨_, MonoidHom.mem_range.mpr ⟨δ, rfl⟩, u, hu, rfl⟩).symm

theorem mem_conjByFiniteIdele_diagonal_mul_iff (δ : (ℍ[ℚ, a, b])ˣ)
    (g : (ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) (z : ℍ[ℚ, a, b]) :
    z ∈ Submodule.conjByFiniteIdele Λ (Submodule.finiteIdeleDiagonal ℍ[ℚ, a, b] δ * g) ↔
      ((δ⁻¹ : (ℍ[ℚ, a, b])ˣ) : ℍ[ℚ, a, b]) * z * δ ∈ Submodule.conjByFiniteIdele Λ g := by

  set e : ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ := (δ : ℍ[ℚ, a, b]) ⊗ₜ[ℚ] 1 with he
  set e' : ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ := ((δ⁻¹ : (ℍ[ℚ, a, b])ˣ) : ℍ[ℚ, a, b]) ⊗ₜ[ℚ] 1
    with he'
  have hee' : e * e' = 1 := by
    rw [he, he', Algebra.TensorProduct.tmul_mul_tmul, Units.mul_inv, mul_one]; rfl
  have he'e : e' * e = 1 := by
    rw [he, he', Algebra.TensorProduct.tmul_mul_tmul, Units.inv_mul, mul_one]; rfl
  have hval : ((Submodule.finiteIdeleDiagonal ℍ[ℚ, a, b] δ * g :
      (ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) : ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ) = e * g := by
    rw [Units.val_mul, Submodule.val_finiteIdeleDiagonal_apply]
  have hinv : (((Submodule.finiteIdeleDiagonal ℍ[ℚ, a, b] δ * g)⁻¹ :
      (ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) : ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ) =
        (g⁻¹ : (ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) * e' := by
    rw [mul_inv_rev, Units.val_mul, ← map_inv, Submodule.val_finiteIdeleDiagonal_apply]
  simp only [Submodule.mem_conjByFiniteIdele_iff, AddSubgroup.mem_map, AddMonoidHom.coe_comp,
    Function.comp_apply, AddMonoidHom.coe_mulLeft, AddMonoidHom.coe_mulRight, hval, hinv]
  constructor
  · rintro ⟨y, hy, hyz⟩
    refine ⟨y, hy, ?_⟩

    have : (g : ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ) * y * (g⁻¹ : (ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ)
        = e' * (z ⊗ₜ[ℚ] (1 : FiniteAdeleRing (𝓞 ℚ) ℚ)) * e := by
      rw [← hyz]
      simp only [← mul_assoc, he'e, one_mul]
      simp only [mul_assoc, he'e, mul_one]
    rw [this, he, he', Algebra.TensorProduct.tmul_mul_tmul, Algebra.TensorProduct.tmul_mul_tmul, mul_one, mul_one]
  · rintro ⟨y, hy, hyz⟩
    refine ⟨y, hy, ?_⟩
    have h3 : e * (g : ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ) * y *
        ((g⁻¹ : (ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) * e') =
          e * ((g : ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ) * y *
            (g⁻¹ : (ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ)) * e' := by
      simp only [mul_assoc]
    rw [h3, hyz, he, he', Algebra.TensorProduct.tmul_mul_tmul, Algebra.TensorProduct.tmul_mul_tmul, mul_one,
      mul_one]
    simp only [mul_assoc, Units.mul_inv, mul_one, Units.mul_inv_cancel_left]

end Adelic

section Places

open AlgebraicCurve

variable {κ : Type} [Field κ] [DecidableEq κ] (q' : ℕ)

noncomputable def jOf (w : ↥(ssPlaces q' 1 κ)) : κ := (w.1).evalAt (jGeomGen κ 1)

theorem eq_charLGeomPlaceOfPoint_jOf (w : ↥(ssPlaces q' 1 κ)) : (w.1) = charLGeomPlaceOfPoint κ (jOf q' w) :=
  ModularCurve.eq_charLGeomPlaceOfPoint_of_ord_pos (IsSupersingularPlace.isCentreOf_evalAt w.2).1

theorem jOf_mem_ssJSet (w : ↥(ssPlaces q' 1 κ)) : jOf q' w ∈ ssJSet q' κ := w.2.2.2

theorem jOf_injective : Function.Injective (jOf (κ := κ) q') := by
  intro w w' h
  apply Subtype.ext
  rw [eq_charLGeomPlaceOfPoint_jOf q' w, eq_charLGeomPlaceOfPoint_jOf q' w', h]

theorem charLGeomPlaceOfPoint_mem_ssPlaces {c : κ} (hc : c ∈ ssJSet q' κ) :
    charLGeomPlaceOfPoint κ c ∈ ssPlaces q' 1 κ :=
  (ModularCurve.mem_ssPlaces_one_iff_exists_charLGeomPlaceOfPoint_eq q' κ _).mpr ⟨c, hc, rfl⟩

theorem jOf_mk_charLGeomPlaceOfPoint {c : κ} (hc : c ∈ ssJSet q' κ) :
    jOf q' ⟨charLGeomPlaceOfPoint κ c, charLGeomPlaceOfPoint_mem_ssPlaces q' hc⟩ = c :=
  (charLGeomPlaceOfPoint_injective κ
    (eq_charLGeomPlaceOfPoint_jOf q' ⟨charLGeomPlaceOfPoint κ c, charLGeomPlaceOfPoint_mem_ssPlaces q' hc⟩)).symm

theorem mem_ssJSet_of_noTorsion [IsSepClosed κ] (W : WeierstrassCurve κ) [W.IsElliptic]
    (hW : ∀ P : W.toAffine.Point, q' • P = 0 → P = 0) : W.j ∈ ssJSet q' κ := by
  intro W' _ hj P hP
  obtain ⟨γ, hγ⟩ := WeierstrassCurve.exists_variableChange_of_j_eq W W' hj.symm
  subst hγ
  obtain ⟨e, -⟩ := WeierstrassCurve.exists_addEquiv_point_variableChange W γ
  have h := hW (e.symm P) (by rw [← map_nsmul, hP, map_zero])
  simpa using congrArg e h

theorem j_eq_of_variableChange_smul_eq {F : Type*} [Field F] {W W' : WeierstrassCurve F} [W.IsElliptic] [W'.IsElliptic]
    (γ : WeierstrassCurve.VariableChange F) (h : γ • W = W') : W.j = W'.j := by
  subst h
  exact (WeierstrassCurve.variableChange_j W γ).symm

end Places

end CerednikDrinfeld.LevelOneDeuringAssembly

open CerednikDrinfeld.LevelOneDeuringAssembly AlgebraicCurve in
theorem solution
    {κ : Type} [Field κ] [IsAlgClosed κ] [DecidableEq κ]
    (q' : ℕ) [Fact q'.Prime] [CharP κ q'] [Algebra (ZMod q') κ] [Algebra.IsAlgebraic (ZMod q') κ]
    (X₀ : WeierstrassCurve κ) [X₀.IsElliptic] (hss : ∀ P : X₀.toAffine.Point, q' • P = 0 → P = 0)
    (a b : ℚ) (hdef : IsDefiniteRamifiedExactlyAt a b q')
    (Λ : Submodule ℤ ℍ[ℚ, a, b]) (hΛ : IsMaximalOrder Λ)
    (θ : ↥(WeierstrassCurve.rationalEndSubring κ X₀) →+* ℍ[ℚ, a, b])
    (hθ : Function.Injective θ) (hθΛ : Set.range θ = (Λ : Set ℍ[ℚ, a, b]))
    [Fintype (ClassSet (Submodule.finiteIdeleStabilizer Λ))] [Fintype ↥(ssPlaces q' 1 κ)] :
    ∃ Φ₁ : ClassSet (Submodule.finiteIdeleStabilizer Λ) ≃ ↥(ssPlaces q' 1 κ),
      (∀ (x : (ℍ[ℚ, a, b] ⊗[ℚ] IsDedekindDomain.FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) (W : WeierstrassCurve κ) [W.IsElliptic],
          W.j = ((Φ₁ (ClassSet.mk _ x)).1).evalAt (jGeomGen κ 1) →
          (∃ χ ∈ WeierstrassCurve.rationalHomSet κ X₀ W, χ ≠ 0 ∧
            ∃ d : (ℍ[ℚ, a, b])ˣ,
              θ '' (WeierstrassCurve.kernelIdealSet κ X₀ W χ) = star '' ((d • Submodule.ofFiniteIdele Λ x : Submodule ℤ ℍ[ℚ, a, b]) : Set ℍ[ℚ, a, b])) ∧
          (∃ θW : ↥(WeierstrassCurve.rationalEndSubring κ W) →+* ℍ[ℚ, a, b],
              Function.Injective θW ∧ Set.range θW = (Submodule.conjByFiniteIdele Λ x : Set ℍ[ℚ, a, b]))) ∧
      (∀ (ℓ : ℕ) [NeZero ℓ], ℓ.Prime → ℓ ≠ q' →
        ∀ (hα : (heckeAlphaC κ 1 ℓ).toRingHom.IsIntegral) (hβ : (heckeBetaC κ 1 ℓ).toRingHom.IsIntegral)
          (i j : ClassSet (Submodule.finiteIdeleStabilizer Λ)),
          ssHeckeMatrixC q' κ 1 ℓ hα hβ (Φ₁ i) (Φ₁ j) =
            classSetHeckeMatrix (Submodule.finiteIdeleStabilizer Λ) (primeHeckeSet Λ ℓ) i j) := by
  classical
  have hord : IsOrder Λ := hΛ.1

  have hss' : ∀ P : (X₀.baseChange κ).toAffine.Point, q' • P = 0 → P = 0 := fun P hP => hss P hP

  have h0 : ∀ w : ↥(ssPlaces q' 1 κ),
      ∃ χ ∈ WeierstrassCurve.rationalHomSet κ X₀ (WeierstrassCurve.ofJ (jOf q' w)), χ ≠ 0 := fun w =>
    WeierstrassCurve.exists_ne_zero_mem_rationalHomSet_of_forall_nsmul_char_eq_zero q' X₀
      (WeierstrassCurve.ofJ (jOf q' w)) hss
      ((jOf_mem_ssJSet q' w) (WeierstrassCurve.ofJ (jOf q' w)) (WeierstrassCurve.ofJ_j _))
  choose χ hχ hχ0 using h0

  have h1 : ∀ w : ↥(ssPlaces q' 1 κ), ∃ (d : (ℍ[ℚ, a, b])ˣ) (x : (ℍ[ℚ, a, b] ⊗[ℚ] IsDedekindDomain.FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ),
      θ '' (WeierstrassCurve.kernelIdealSet κ X₀ (WeierstrassCurve.ofJ (jOf q' w)) (χ w)) =
        star '' ((d • Submodule.ofFiniteIdele Λ x : Submodule ℤ ℍ[ℚ, a, b]) : Set ℍ[ℚ, a, b]) := fun w => by
    obtain ⟨d, x, hx, -⟩ :=
      WeierstrassCurve.exists_image_kernelIdealSet_eq_star_smul_ofFiniteIdele_and_range_eq_conjByFiniteIdele q' X₀ hss
        a b hdef Λ hΛ θ hθ hθΛ (WeierstrassCurve.ofJ (jOf q' w)) (χ w) (hχ w) (hχ0 w)
    exact ⟨d, x, hx⟩
  choose dw xw hxw using h1

  let Ψ : ↥(ssPlaces q' 1 κ) → ClassSet (Submodule.finiteIdeleStabilizer Λ) := fun w =>
    ClassSet.mk (Submodule.finiteIdeleStabilizer Λ) (xw w)

  have hinj : Function.Injective Ψ := by
    intro w w' hww'
    obtain ⟨γ, hγ⟩ :=
      (CerednikDrinfeld.classSet_mk_eq_iff_nonempty_variableChange_of_kernelIdealSet q' X₀ hss a b hdef Λ hΛ θ hθ hθΛ
        (xw w) (xw w') (WeierstrassCurve.ofJ (jOf q' w)) (χ w) (hχ w) (hχ0 w) (dw w) (hxw w)
        (WeierstrassCurve.ofJ (jOf q' w')) (χ w') (hχ w') (hχ0 w') (dw w') (hxw w')).mp hww'
    have hj := j_eq_of_variableChange_smul_eq γ hγ
    rw [WeierstrassCurve.ofJ_j, WeierstrassCurve.ofJ_j] at hj
    exact jOf_injective q' hj

  have hsurj : Function.Surjective Ψ := by
    intro q
    obtain ⟨x, rfl⟩ := ClassSet.mk_surjective q
    obtain ⟨W, hW, χ₃, hχ₃, hχ₃0, d, hK3⟩ :=
      CerednikDrinfeld.exists_kernelIdealSet_eq_star_smul_ofFiniteIdele q' X₀ hss a b hdef Λ hΛ θ hθ hθΛ x
    haveI := hW
    have hWtors : ∀ P : W.toAffine.Point, q' • P = 0 → P = 0 :=
      fun P hP => noTorsion_of_hom hχ₃ hχ₃0 q' hss' P hP
    have hjmem : W.j ∈ ssJSet q' κ := mem_ssJSet_of_noTorsion q' W hWtors
    let w : ↥(ssPlaces q' 1 κ) := ⟨charLGeomPlaceOfPoint κ W.j, charLGeomPlaceOfPoint_mem_ssPlaces q' hjmem⟩
    have hjw : jOf q' w = W.j := jOf_mk_charLGeomPlaceOfPoint q' hjmem
    refine ⟨w, ?_⟩
    have hjj : (WeierstrassCurve.ofJ (jOf q' w)).j = W.j := by rw [WeierstrassCurve.ofJ_j, hjw]
    obtain ⟨γ, hγ⟩ := WeierstrassCurve.exists_variableChange_of_j_eq _ _ hjj
    exact (CerednikDrinfeld.classSet_mk_eq_iff_nonempty_variableChange_of_kernelIdealSet q' X₀ hss a b hdef Λ hΛ θ hθ
      hθΛ (xw w) x (WeierstrassCurve.ofJ (jOf q' w)) (χ w) (hχ w) (hχ0 w) (dw w) (hxw w) W χ₃ hχ₃ hχ₃0 d hK3).mpr
      ⟨γ, hγ⟩

  let E : ↥(ssPlaces q' 1 κ) ≃ ClassSet (Submodule.finiteIdeleStabilizer Λ) := Equiv.ofBijective Ψ ⟨hinj, hsurj⟩
  have hE : ∀ w, E w = ClassSet.mk (Submodule.finiteIdeleStabilizer Λ) (xw w) := fun w => rfl
  refine ⟨E.symm, ?_, ?_⟩
  ·
    intro x W _ hjW
    set w : ↥(ssPlaces q' 1 κ) := E.symm (ClassSet.mk (Submodule.finiteIdeleStabilizer Λ) x) with hw
    have hΨw : ClassSet.mk (Submodule.finiteIdeleStabilizer Λ) (xw w) =
        ClassSet.mk (Submodule.finiteIdeleStabilizer Λ) x := by
      rw [← hE, hw, Equiv.apply_symm_apply]
    change W.j = jOf q' w at hjW

    have hWtors : ∀ P : W.toAffine.Point, q' • P = 0 → P = 0 := (jOf_mem_ssJSet q' w) W hjW
    obtain ⟨χW, hχW, hχW0⟩ :=
      WeierstrassCurve.exists_ne_zero_mem_rationalHomSet_of_forall_nsmul_char_eq_zero q' X₀ W hss hWtors

    obtain ⟨d', x', hx', θW, hθWi, hθWr⟩ :=
      WeierstrassCurve.exists_image_kernelIdealSet_eq_star_smul_ofFiniteIdele_and_range_eq_conjByFiniteIdele q' X₀ hss
        a b hdef Λ hΛ θ hθ hθΛ W χW hχW hχW0

    have hjj : (WeierstrassCurve.ofJ (jOf q' w)).j = W.j := by rw [WeierstrassCurve.ofJ_j, hjW]
    obtain ⟨γ, hγ⟩ := WeierstrassCurve.exists_variableChange_of_j_eq _ _ hjj
    have hxx' : ClassSet.mk (Submodule.finiteIdeleStabilizer Λ) x = ClassSet.mk (Submodule.finiteIdeleStabilizer Λ) x' :=
      hΨw.symm.trans
        ((CerednikDrinfeld.classSet_mk_eq_iff_nonempty_variableChange_of_kernelIdealSet q' X₀ hss a b hdef Λ hΛ θ hθ
          hθΛ (xw w) x' (WeierstrassCurve.ofJ (jOf q' w)) (χ w) (hχ w) (hχ0 w) (dw w) (hxw w) W χW hχW hχW0 d' hx').mpr
          ⟨γ, hγ⟩)
    obtain ⟨δ, hδ⟩ := exists_ofFiniteIdele_eq_smul_of_mk_eq_mk Λ hord hxx'
    refine ⟨⟨χW, hχW, hχW0, d' * δ, by rw [hx', hδ, smul_smul]⟩, ?_⟩

    obtain ⟨u, hu, hx'eq⟩ := exists_mem_stabilizer_of_ofFiniteIdele_eq_smul Λ hord δ hδ
    have hconj : Submodule.conjByFiniteIdele Λ x' =
        Submodule.conjByFiniteIdele Λ (Submodule.finiteIdeleDiagonal ℍ[ℚ, a, b] δ * x) := by
      rw [hx'eq]
      exact Submodule.conjByFiniteIdele_mul_eq_of_mem_finiteIdeleStabilizer Λ hord.one_mem
        (fun y z hy hz => hord.mul_mem hy hz) _ u hu
    refine ⟨(unitConj δ⁻¹).comp θW, (unitConj_injective δ⁻¹).comp hθWi, ?_⟩
    ext z
    simp only [Set.mem_range, RingHom.coe_comp, Function.comp_apply, SetLike.mem_coe]
    constructor
    · rintro ⟨y, rfl⟩
      have hy : θW y ∈ Submodule.conjByFiniteIdele Λ x' := by
        rw [← SetLike.mem_coe, ← hθWr]; exact ⟨y, rfl⟩
      rw [hconj, mem_conjByFiniteIdele_diagonal_mul_iff] at hy
      rw [unitConj_apply, inv_inv]
      exact hy
    · intro hz
      have hz' : unitConj δ z ∈ Submodule.conjByFiniteIdele Λ x' := by
        rw [hconj, mem_conjByFiniteIdele_diagonal_mul_iff, unitConj_apply]
        simpa only [mul_assoc, Units.inv_mul, mul_one, Units.inv_mul_cancel_left] using hz
      rw [← SetLike.mem_coe, ← hθWr] at hz'
      obtain ⟨y, hy⟩ := hz'
      exact ⟨y, by rw [hy, unitConj_inv_apply_unitConj]⟩
  ·

    intro ℓ _ hℓ hne hα hβ i j
    obtain ⟨wi, rfl⟩ := E.surjective i
    obtain ⟨wj, rfl⟩ := E.surjective j
    simp only [Equiv.symm_apply_apply]
    rw [hE, hE,
      ModularCurve.ssHeckeMatrixC_one_apply_eq_natCard_subgroup_dualPair q' ℓ hℓ hne hα hβ wj wi
        (WeierstrassCurve.ofJ (jOf q' wj)) (WeierstrassCurve.ofJ (jOf q' wi)) (WeierstrassCurve.ofJ_j _)
        (WeierstrassCurve.ofJ_j _),
      classSetHeckeMatrix, Matrix.of_apply,
      QuaternionAlgebra.IsOrder.heckeKernel_primeHeckeSet_mk_mk_eq_natCard hord ℓ (xw wj) (xw wi),
      CerednikDrinfeld.natCard_subideal_primeHeckeSet_eq_natCard_subgroup_dualPair_of_kernelIdealSet q' X₀ hss a b hdef
        Λ hΛ θ hθ hθΛ (xw wj) (xw wi) (WeierstrassCurve.ofJ (jOf q' wj)) (χ wj) (hχ wj) (hχ0 wj) (dw wj) (hxw wj)
        (WeierstrassCurve.ofJ (jOf q' wi)) (χ wi) (hχ wi) (hχ0 wi) (dw wi) (hxw wi) ℓ hℓ hne]

end S_CerednikDrinfeld_exists_classSet_equiv_ssPlaces_one_kernelIdealSet_of_rationalEndSubring
end P2MW
export P2MW.S_CerednikDrinfeld_exists_classSet_equiv_ssPlaces_one_kernelIdealSet_of_rationalEndSubring (solution)
