-- Prove2me | solution 1 for CerednikDrinfeld.exists_equiv_ofFiniteIdele_mul_isAddCyclic_forall_ker_eq_of_kernelIdealSet_comp_eq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.491319+00:00
-- url     : https://prove2.me/submissions/1ec6b0e5-a1e4-53bb-a557-dde3cb535895

import Mathlib
import Definitions.Def_QuaternionAlgebra_EichlerOrder
import Definitions.Def_WeierstrassCurve_RationalEnd
import Definitions.Def_WeierstrassCurve_KernelIdeal
import Definitions.Def_CerednikDrinfeld_ClassSetGraph
import Definitions.Def_DualIsogenyAPI
import Theorems.Thm_CerednikDrinfeld_exists_mem_finiteAdeleBox_image_kernelIdealSet_comp_eq_star_smul_ofFiniteIdele_mul_of_dualPair
import Theorems.Thm_CerednikDrinfeld_natCard_ker_sq_eq_relIndex_ofFiniteIdele_mul_of_image_kernelIdealSet_comp_eq
import Theorems.Thm_CerednikDrinfeld_isAddCyclic_ker_iff_forall_inv_smul_not_mem_finiteAdeleBox_of_image_kernelIdealSet_comp_eq
import Theorems.Thm_QuaternionAlgebra_exists_ofFiniteIdele_mul_eq_ofFiniteIdele_mul_mul_iff_relIndex_eq_sq_and_forall_not_le_zsmul
import Theorems.Thm_CerednikDrinfeld_exists_dualPair_image_kernelIdealSet_comp_eq_star_smul_ofFiniteIdele_mul_of_mem_finiteAdeleBox
import Theorems.Thm_CerednikDrinfeld_isAddCyclic_ker_of_forall_inv_smul_not_mem_finiteAdeleBox_of_image_kernelIdealSet_comp_eq
import Theorems.Thm_WeierstrassCurve_exists_quotient_dualPair_kernelIdealSet_comp_eq
import Theorems.Thm_QuaternionAlgebra_forall_inv_smul_not_mem_finiteAdeleBox_of_mem_of_smul_inv_mem_of_relIndex_inf_conjByFiniteIdele_eq
import Theorems.Thm_QuaternionAlgebra_IsOrder_ofFiniteIdele_mul_le_zsmul_ofFiniteIdele_iff_inv_smul_mem_finiteAdeleBox
import Theorems.Thm_Submodule_ofFiniteIdele_eq_ofFiniteIdele_iff
import Theorems.Thm_WeierstrassCurve_exists_addOrderOf_eq_prime_of_isAlgClosed
import Theorems.Thm_WeierstrassCurve_surjective_of_mem_rationalHomSet
import Theorems.Thm_WeierstrassCurve_comp_mem_rationalHomSet
import Theorems.Thm_WeierstrassCurve_exists_isDualPair_of_mem_rationalHomSet
import Theorems.Thm_WeierstrassCurve_exists_mem_rationalHomSet_apply_ne_zero_of_prime_nsmul_eq_zero
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_exists_equiv_ofFiniteIdele_mul_isAddCyclic_forall_ker_eq_of_kernelIdealSet_comp_eq
p2m_attr_erase "instance" "instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly AlgebraicCurve.instFundamentalIdentityOfSumRamificationInertia AlgebraicCurve.Place.instIsScalarTowerResidueFieldRestrictPushforward AlgebraicCurve.Place.instAlgebraResidueFieldRestrictPushforward AlgebraicCurve.Place.instIsLocalHomRestrictInclusion AlgebraicCurve.Place.instIsScalarTowerSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Divisor.instDistribMulActionAlgEquiv AlgebraicCurve.Place.instSMulAlgEquiv AlgebraicCurve.Place.instIsPrincipalIdealRingSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Place.instIsDiscreteValuationRingSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Pic0.instDistribMulActionAlgEquiv AlgebraicCurve.Place.instAlgebraSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Place.instMulActionAlgEquiv AlgebraicCurve.Pic0.instSMulAlgEquiv AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupDivisor AlgebraicCurve.Pic0.instModuleZModTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instDistribMulActionTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instSMulTorsion AlgebraicCurve.SemilinearAut.instMulActionSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instSMulCommClassZModTorsion AlgebraicCurve.SemilinearAut.instMulSemiringActionSubtypeProdRingAutMemSubgroup AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation"
p2m_attr_erase "instance" "AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy WeierstrassCurve.Affine.instIsScalarTowerPolynomialRatFuncFunctionField_definitions WeierstrassCurve.Affine.instAlgebraRatFuncFunctionField_definitions WeierstrassCurve.Affine.instIsScalarTowerRatFuncFunctionField_definitions WeierstrassCurve.Affine.CoordinateRing.moduleFinite WeierstrassCurve.Affine.instDecidableEqFunctionField WeierstrassCurve.Affine.CoordinateRing.isIntegral ModularCurve.SpecializationWitnessData.addCommGroup ModularCurve.CommutingHeckeFamily.commRing_adjoin ModularCurve.Gamma0Pair.isElliptic IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions"
p2m_attr_erase "simp" "AddMonoid.End.dualEndDataOfSurjective_trace AddMonoid.End.dualEndDataOfSurjective_norm compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two WeierstrassCurve.Universal.halveX_zero WeierstrassCurve.Universal.specialize_X_one WeierstrassCurve.Universal.coeff_halve WeierstrassCurve.Universal.specialize_X_two WeierstrassCurve.Universal.halveCoeff_zero"
p2m_attr_erase "simp" "WeierstrassCurve.Universal.specialize_X_four WeierstrassCurve.Universal.coeff_halveX WeierstrassCurve.Universal.specialize_X_three WeierstrassCurve.Universal.specialize_X_zero QuaternionAlgebra.baseChangeRight_tmul QuaternionAlgebra.mapOfAlgebraMapEq_apply QuaternionAlgebra.baseChange_tmul WeierstrassCurve.Affine.Point.netCol_one WeierstrassCurve.Affine.Point.xOrZero_zero WeierstrassCurve.Affine.Point.netPairing_zero_right WeierstrassCurve.Affine.Point.netW20_some WeierstrassCurve.Affine.Point.netCol_zero WeierstrassCurve.Affine.Point.netPairing_zero_left WeierstrassCurve.Affine.Point.xOrZero_some WeierstrassCurve.Affine.Point.netW20_zero TateCurve.cauchyMulInt_zero TateCurve.cauchyMulInt3_zero TateCurve.tent_one TateCurve.Gz_zero TateCurve.cauchyMulInt_one TateCurve.tent_zero TateCurve.Fz_zero TateCurve.xCoeffFull_succ TateCurve.a₆Coeff_zero TateCurve.a₄Coeff_succ TateCurve.a₄Coeff_zero TateCurve.cauchyMul_zero TateCurve.a₆Coeff_succ TateCurve.yCoeffFull_succ TateCurve.xCoeffFull_zero TateCurve.yCoeffFull_zero TateCurve.yfun_zero TateCurve.xfun_zero TateCurve.yTerm_zero TateCurve.xTerm_zero TateCurve.curve_a₂ TateCurve.b_one TateCurve.curve_a₁ TateCurve.term_zero TateCurve.curve_a₆"
p2m_attr_erase "simp" "TateCurve.curve_a₄ TateCurve.curve_a₃ FLT.DivisorConvolution.sigma_zero_right FLT.DivisorConvolution.sigma_one_right FLT.DivisorConvolution.sigmaConv_one FLT.DivisorConvolution.sigmaConv_zero WeierstrassCurve.veluWSum_empty WeierstrassCurve.veluQuotient_a₁ WeierstrassCurve.veluQuotient_a₃ WeierstrassCurve.veluQuotient_empty WeierstrassCurve.veluTSum_empty WeierstrassCurve.veluQuotient_a₂ WeierstrassCurve.veluX_empty WeierstrassCurve.veluY_empty WeierstrassCurve.Affine.Point.coordsOrZero_some WeierstrassCurve.Affine.Point.coordsOrZero_zero WeierstrassCurve.Affine.IsogenyEndDatum.mk.injEq WeierstrassCurve.Affine.IsogenyHomDatum.mk.sizeOf_spec WeierstrassCurve.Affine.IsogenyHomDatum.mk.injEq WeierstrassCurve.Affine.IsogenyEndDatum.mk.sizeOf_spec AlgebraicCurve.Pic0.coe_pushforwardAlongDegZero WeierstrassCurve.Affine.pointMapOfPushforward_apply AlgebraicCurve.Divisor.degree_pushforwardAlong AlgebraicCurve.Pic0.coe_degZeroCorrespondence AlgebraicCurve.Place.mem_fiberAlong AlgebraicCurve.Divisor.mapRestrict_single AlgebraicCurve.Divisor.pushforward_single AlgebraicCurve.Place.coe_restrictInclusion AlgebraicCurve.Place.mem_fiber AlgebraicCurve.Place.restrict_toValuationSubring AlgebraicCurve.Divisor.degree_pushforward AlgebraicCurve.Place.restrictResidueMap_residue AlgebraicCurve.Pic0.coe_pushforwardDegZeroHom AlgebraicCurve.Pic0.coe_pullbackDegZeroHom AlgebraicCurve.Place.mk.injEq AlgebraicCurve.Divisor.degree_single AlgebraicCurve.Divisor.smul_single AlgebraicCurve.Place.smul_toValuationSubring AlgebraicCurve.Place.heightOneSpectrum_asIdeal AlgebraicCurve.Place.coe_algebraMap"
p2m_attr_erase "simp" "AlgebraicCurve.Place.ord_one AlgebraicCurve.Place.coe_smulRingEquiv_apply AlgebraicCurve.Pic0.coe_degZeroSMulHom AlgebraicCurve.Place.deg_smul AlgebraicCurve.Pic0.mk_zero AlgebraicCurve.Place.mk.sizeOf_spec AlgebraicCurve.Divisor.degree_smul AlgebraicCurve.Pic0.mk_add AlgebraicCurve.Place.ord_zero AlgebraicCurve.Place.ofHeightOneSpectrum_toValuationSubring AlgebraicCurve.SemilinearAut.toRingAut_inv AlgebraicCurve.SemilinearAut.smul_def AlgebraicCurve.SemilinearAut.smul_single AlgebraicCurve.SemilinearAut.smul_toValuationSubring AlgebraicCurve.SemilinearAut.baseAut_inv AlgebraicCurve.SemilinearAut.baseAut_ofAlgAut AlgebraicCurve.SemilinearAut.toRingAut_ofAlgAut AlgebraicCurve.SemilinearAut.torsionRep_apply AlgebraicCurve.SemilinearAut.toRingAut_one AlgebraicCurve.SemilinearAut.deg_smul AlgebraicCurve.SemilinearAut.degree_smul AlgebraicCurve.SemilinearAut.coe_degZeroSMulHom AlgebraicCurve.SemilinearAut.baseAut_mul AlgebraicCurve.SemilinearAut.coe_smulValuationSubringEquiv_apply AlgebraicCurve.SemilinearAut.baseAut_one AlgebraicCurve.SemilinearAut.ofAlgAut_smul AlgebraicCurve.SemilinearAut.coe_torsion_smul AlgebraicCurve.SemilinearAut.toRingAut_mul WeierstrassCurve.Affine.pointClass_zero WeierstrassCurve.Affine.pic0ToPoint_pointClass WeierstrassCurve.Affine.deg_placeOfPoint WeierstrassCurve.Affine.coe_pointDivisor WeierstrassCurve.Affine.pointEquivPlace_symm_placeOfPoint WeierstrassCurve.Affine.pointEquivPlace_apply WeierstrassCurve.Affine.genusOnePic0Equiv_symm_apply WeierstrassCurve.Affine.pointDivisor_zero WeierstrassCurve.Affine.pic0ToPoint_mk WeierstrassCurve.Affine.divisorSum_single WeierstrassCurve.Affine.genusOnePic0Equiv_apply AlgebraicCurve.Place.placeOfPrime_toValuationSubring"
p2m_attr_erase "simp" "AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.jqNModC_one ModularCurve.qExpand_coeff_mul ModularCurve.qExpandₐ_apply ModularCurve.jqN_one ModularCurve.qExpand_single ModularCurve.dedekindPsi_one ModularCurve.ModularPolynomialData.mk.sizeOf_spec ModularCurve.evalAtJ_X ModularCurve.ModularPolynomialData.mk.injEq ModularCurve.constantCoeff_jNum ModularCurve.constantCoeff_eisenstein4 ModularCurve.qExpand_C ModularCurve.coeff_jq_neg_one"
p2m_attr_erase "simp" "ModularCurve.constantCoeff_jNumQ ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd FreyPackage.mk.sizeOf_spec FreyPackage.mk.injEq WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply WeierstrassCurve.vcInvEmbedding_apply WeierstrassCurve.Affine.vcY_vcYInv WeierstrassCurve.Affine.vcXInv_vcX WeierstrassCurve.Affine.Point.vcFun_zero WeierstrassCurve.Affine.vcX_vcXInv WeierstrassCurve.Affine.vcYInv_vcY WeierstrassCurve.Affine.Point.vcInvFun_zero WeierstrassCurve.map_veluU WeierstrassCurve.map_veluT WeierstrassCurve.map_veluW WeierstrassCurve.map_veluGy WeierstrassCurve.map_veluGx WeierstrassCurve.map_veluWSum_singleton WeierstrassCurve.map_veluTSum_singleton WeierstrassCurve.veluPointMap3_zero WeierstrassCurve.Affine.ratFuncToFunctionField_algebraMap AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one WeierstrassCurve.Affine.pointHom_mk_C_C WeierstrassCurve.Affine.Point.yc_some WeierstrassCurve.Affine.Point.xc_some WeierstrassCurve.Affine.pointPull_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_X WeierstrassCurve.Affine.pointHom_mk_Y WeierstrassCurve.Affine.placeOf_asIdeal"
p2m_attr_erase "simp" "ModularCurve.coe_levelAlphaC ModularCurve.SSLevelDatum.mk.sizeOf_spec ModularCurve.SSLevelDatum.mk.injEq ModularCurve.coe_levelBetaC ModularCurve.coe_heckeBetaC AlgebraicCurve.Divisor.coe_degZeroEnd ModularCurve.coe_heckeAlphaC ModularCurve.CommutingHeckeFamily.mk.injEq ModularCurve.SpecializationWitnessData.mk.sizeOf_spec ModularCurve.SpecializationWitnessData.mk.injEq ModularCurve.CommutingHeckeFamily.mk.sizeOf_spec ModularCurve.coe_nodeEquivOfPlaces_apply ModularCurve.widthOfPlaces_mk ModularCurve.smulNodePairEmb_apply ModularCurve.card_nodePairsOfPlaces ModularCurve.smulNodePair_snd ModularCurve.smulNodePair_fst ModularCurve.coe_nodeEquivOfPlaces_symm_apply ModularCurve.coe_jGeomGen ModularCurve.coe_jNGeomGen ModularCurve.coe_uniformizerMod ModularCurve.qSeriesBar_jModElt ModularCurve.qInftyPlaceMod_toValuationSubring ModularCurve.qInftyPlaceBar_toValuationSubring ModularCurve.qSeriesBar_zero ModularCurve.qSeriesBar_add ModularCurve.cuspInftyFull_toValuationSubring ModularCurve.qInftyPlaceRat_toValuationSubring ModularCurve.qSeriesBar_mul ModularCurve.qSeriesBar_div ModularCurve.qSeriesBar_eq_zero_iff ModularCurve.coe_uniformizerBar ModularCurve.qSeriesBar_pow ModularCurve.cuspInfty_toValuationSubring ModularCurve.qSeriesBar_one ModularCurve.qSeriesBar_inv ModularCurve.qSeriesBar_sub ModularCurve.qSeriesBar_neg ModularCurve.charLGeomModuliDictionary_single ModularCurve.specializeModuli_single"
p2m_attr_erase "simp" "ModularCurve.specializePlace_def ModularCurve.gamma0PairMap_gen ModularCurve.moduliPointMapRingHom_mk ModularCurve.Gamma0Pair.mk.injEq ModularCurve.ModuliPoint.j_mk ModularCurve.Gamma0Pair.mk.sizeOf_spec ModularCurve.gamma0PairMap_toCurve WeierstrassCurve.ratPointHom_apply WeierstrassCurve.ratPointMap_zero LocalGL2.swapUnit_val WeierstrassCurve.veluPointMap2_zero WeierstrassCurve.veluQuotient2_a₂ WeierstrassCurve.veluQuotient2_a₃ WeierstrassCurve.veluQuotient2_a₁ WeierstrassCurve.pointAddEquivOfEq_refl"

set_option autoImplicit false

open scoped Quaternion TensorProduct NumberField Pointwise
p2m_open "QuaternionAlgebra~baseChange CerednikDrinfeld"

namespace C1bReduce

open WeierstrassCurve

section Group

variable {A B : Type*} [AddCommGroup A] [AddCommGroup B]

theorem exists_prime_nsmul_ne_zero {Q : B} (hfin : IsOfFinAddOrder Q) (hQ0 : Q ≠ 0) :
    ∃ (ℓ m : ℕ), ℓ.Prime ∧ m • Q ≠ 0 ∧ ℓ • (m • Q) = 0 := by
  set n := addOrderOf Q with hn
  have hn0 : 0 < n := hfin.addOrderOf_pos
  have hn1 : n ≠ 1 := fun h => hQ0 (AddMonoid.addOrderOf_eq_one_iff.mp h)
  obtain ⟨ℓ, hℓ, hℓn⟩ := Nat.exists_prime_and_dvd hn1
  obtain ⟨m, hm⟩ := hℓn
  have hm0 : m ≠ 0 := by rintro rfl; rw [mul_zero] at hm; omega
  have hmn : m < n := by
    rw [hm]
    have := hℓ.two_le
    nlinarith [Nat.pos_of_ne_zero hm0]
  refine ⟨ℓ, m, hℓ, nsmul_ne_zero_of_lt_addOrderOf hm0 hmn, ?_⟩
  rw [smul_smul, ← hm]
  exact addOrderOf_nsmul_eq_zero Q

theorem forall_nsmul_eq_zero_of_dual {φ : A →+ B} {σ : B →+ A} {n : ℤ} (hn : n ≠ 0)
    (hd : ∀ P : A, σ (φ P) = n • P) (hφ : Function.Surjective φ) {p : ℕ} (hp : p.Prime)
    (hA : ∀ P : A, p • P = 0 → P = 0) : ∀ Q : B, p • Q = 0 → Q = 0 := by
  intro Q hQ
  by_contra hQ0
  obtain ⟨P, rfl⟩ := hφ Q

  have hfinP : IsOfFinAddOrder P := by
    have h1 : IsOfFinAddOrder (p • P) := by
      rw [isOfFinAddOrder_iff_zsmul_eq_zero]
      refine ⟨n, hn, ?_⟩
      rw [← hd, map_nsmul, hQ, map_zero]
    exact h1.of_nsmul hp.ne_zero
  haveI : Fact p.Prime := ⟨hp⟩
  have hordQ : addOrderOf (φ P) = p := addOrderOf_eq_prime hQ hQ0
  have hdvd : p ∣ addOrderOf P := hordQ ▸ addOrderOf_map_dvd φ P
  have hoP : addOrderOf P ≠ 0 := hfinP.addOrderOf_pos.ne'
  have hord : addOrderOf ((addOrderOf P / p) • P) = p := addOrderOf_nsmul_addOrderOf_sub hoP hdvd
  have hne : (addOrderOf P / p) • P ≠ 0 := by
    intro h
    have h1 : addOrderOf ((addOrderOf P / p) • P) = 1 := AddMonoid.addOrderOf_eq_one_iff.mpr h
    rw [hord] at h1
    exact hp.one_lt.ne' h1
  refine hne (hA _ ?_)
  have h2 := addOrderOf_nsmul_eq_zero ((addOrderOf P / p) • P)
  rwa [hord] at h2

end Group

section Kernel

variable {κ : Type} [Field κ] [IsAlgClosed κ] [DecidableEq κ]

abbrev Pt (W : WeierstrassCurve κ) := (W.baseChange κ).toAffine.Point

theorem apply_eq_zero_iff_forall_kernelIdealSet
    (q' : ℕ) [Fact q'.Prime] [CharP κ q']
    (X₁ : WeierstrassCurve κ) [X₁.IsElliptic] (hss : ∀ P : Pt X₁, q' • P = 0 → P = 0)
    (a b : ℚ) (Λ₁ : Submodule ℤ ℍ[ℚ, a, b]) (hΛ₁ : IsOrder Λ₁)
    (θ₁ : ↥(WeierstrassCurve.rationalEndSubring κ X₁) →+* ℍ[ℚ, a, b])
    (hθ₁ : Function.Injective θ₁) (hθ₁Λ : Set.range θ₁ = (Λ₁ : Set ℍ[ℚ, a, b]))
    (W' : WeierstrassCurve κ) [W'.IsElliptic] (φ : Pt X₁ →+ Pt W')
    (hφ : φ ∈ WeierstrassCurve.rationalHomSet κ X₁ W') (P : Pt X₁) :
    φ P = 0 ↔ ∀ s ∈ WeierstrassCurve.kernelIdealSet κ X₁ W' φ, (s : AddMonoid.End (Pt X₁)) P = 0 := by
  constructor
  · rintro hP s ⟨ρ, -, hs⟩
    rw [hs]
    show ρ (φ P) = 0
    rw [hP, map_zero]
  · intro hall

    have hkill : ∀ ρ ∈ WeierstrassCurve.rationalHomSet κ W' X₁, ρ (φ P) = 0 := by
      intro ρ hρ
      have hmemR : ρ.comp φ ∈ WeierstrassCurve.rationalEndSubring κ X₁ :=
        Subring.subset_closure (WeierstrassCurve.comp_mem_rationalHomSet κ X₁ W' X₁ hφ hρ)
      have hmemK : (⟨ρ.comp φ, hmemR⟩ : ↥(WeierstrassCurve.rationalEndSubring κ X₁)) ∈
          WeierstrassCurve.kernelIdealSet κ X₁ W' φ := ⟨ρ, hρ, rfl⟩
      exact hall _ hmemK
    by_cases hφ0 : φ = 0
    · rw [hφ0, AddMonoidHom.zero_apply]
    by_contra hQ0

    obtain ⟨σ, hσ, n, hn, hdual⟩ :=
      WeierstrassCurve.exists_isDualPair_of_mem_rationalHomSet κ X₁ W' hφ hφ0

    have hfinQ : IsOfFinAddOrder (φ P) := by
      rw [isOfFinAddOrder_iff_zsmul_eq_zero]
      refine ⟨n, hn.ne', ?_⟩
      rw [← hdual.comp_right (φ P), hkill σ hσ, map_zero]

    obtain ⟨ℓ, m, hℓ, hQ₁0, hℓQ₁⟩ := exists_prime_nsmul_ne_zero hfinQ hQ0

    have hW' : ∀ Q : Pt W', q' • Q = 0 → Q = 0 :=
      forall_nsmul_eq_zero_of_dual hn.ne' hdual.comp_left
        (WeierstrassCurve.surjective_of_mem_rationalHomSet κ hφ hφ0) (Fact.out : q'.Prime) hss
    have hℓq : ℓ ≠ q' := by
      rintro rfl
      exact hQ₁0 (hW' _ hℓQ₁)

    obtain ⟨ρ, hρ, hρQ⟩ :=
      WeierstrassCurve.exists_mem_rationalHomSet_apply_ne_zero_of_prime_nsmul_eq_zero q' X₁ a b Λ₁ hΛ₁ θ₁ hθ₁ hθ₁Λ
        W' φ hφ hφ0 ℓ hℓ hℓq (m • φ P) hℓQ₁ hQ₁0
    exact hρQ (by rw [map_nsmul, hkill ρ hρ, smul_zero])

theorem apply_eq_zero_iff_of_kernelIdealSet_eq
    (q' : ℕ) [Fact q'.Prime] [CharP κ q']
    (X₁ : WeierstrassCurve κ) [X₁.IsElliptic] (hss : ∀ P : Pt X₁, q' • P = 0 → P = 0)
    (a b : ℚ) (Λ₁ : Submodule ℤ ℍ[ℚ, a, b]) (hΛ₁ : IsOrder Λ₁)
    (θ₁ : ↥(WeierstrassCurve.rationalEndSubring κ X₁) →+* ℍ[ℚ, a, b])
    (hθ₁ : Function.Injective θ₁) (hθ₁Λ : Set.range θ₁ = (Λ₁ : Set ℍ[ℚ, a, b]))
    (W₁ : WeierstrassCurve κ) [W₁.IsElliptic] (φ₁ : Pt X₁ →+ Pt W₁)
    (hφ₁ : φ₁ ∈ WeierstrassCurve.rationalHomSet κ X₁ W₁)
    (W₂ : WeierstrassCurve κ) [W₂.IsElliptic] (φ₂ : Pt X₁ →+ Pt W₂)
    (hφ₂ : φ₂ ∈ WeierstrassCurve.rationalHomSet κ X₁ W₂)
    (hK : WeierstrassCurve.kernelIdealSet κ X₁ W₁ φ₁ = WeierstrassCurve.kernelIdealSet κ X₁ W₂ φ₂)
    (P : Pt X₁) : φ₁ P = 0 ↔ φ₂ P = 0 := by
  rw [apply_eq_zero_iff_forall_kernelIdealSet q' X₁ hss a b Λ₁ hΛ₁ θ₁ hθ₁ hθ₁Λ W₁ φ₁ hφ₁ P,
    apply_eq_zero_iff_forall_kernelIdealSet q' X₁ hss a b Λ₁ hΛ₁ θ₁ hθ₁ hθ₁Λ W₂ φ₂ hφ₂ P, hK]

end Kernel

section Frame

variable {κ : Type} [Field κ] [IsAlgClosed κ] [DecidableEq κ]

theorem ker_eq_ker_of_image_kernelIdealSet_comp_eq
    (q' : ℕ) [Fact q'.Prime] [CharP κ q']
    (X₁ : WeierstrassCurve κ) [X₁.IsElliptic] (hss : ∀ P : Pt X₁, q' • P = 0 → P = 0)
    (a b : ℚ) (Λ₁ : Submodule ℤ ℍ[ℚ, a, b]) (hΛ₁ : IsOrder Λ₁)
    (θ₁ : ↥(WeierstrassCurve.rationalEndSubring κ X₁) →+* ℍ[ℚ, a, b])
    (hθ₁ : Function.Injective θ₁) (hθ₁Λ : Set.range θ₁ = (Λ₁ : Set ℍ[ℚ, a, b]))
    (W : WeierstrassCurve κ) [W.IsElliptic] (χ : Pt X₁ →+ Pt W)
    (hχ : χ ∈ WeierstrassCurve.rationalHomSet κ X₁ W) (hχ0 : χ ≠ 0)
    (W₁ : WeierstrassCurve κ) [W₁.IsElliptic] (ψ₁ : Pt W →+ Pt W₁)
    (hψ₁ : ψ₁ ∈ WeierstrassCurve.rationalHomSet κ W W₁)
    (W₂ : WeierstrassCurve κ) [W₂.IsElliptic] (ψ₂ : Pt W →+ Pt W₂)
    (hψ₂ : ψ₂ ∈ WeierstrassCurve.rationalHomSet κ W W₂)
    (hK12 : θ₁ '' WeierstrassCurve.kernelIdealSet κ X₁ W₁ (ψ₁.comp χ) =
      θ₁ '' WeierstrassCurve.kernelIdealSet κ X₁ W₂ (ψ₂.comp χ)) :
    ψ₁.ker = ψ₂.ker := by
  have hφ₁ : ψ₁.comp χ ∈ WeierstrassCurve.rationalHomSet κ X₁ W₁ :=
    WeierstrassCurve.comp_mem_rationalHomSet κ X₁ W W₁ hχ hψ₁
  have hφ₂ : ψ₂.comp χ ∈ WeierstrassCurve.rationalHomSet κ X₁ W₂ :=
    WeierstrassCurve.comp_mem_rationalHomSet κ X₁ W W₂ hχ hψ₂
  have hKI : WeierstrassCurve.kernelIdealSet κ X₁ W₁ (ψ₁.comp χ) =
      WeierstrassCurve.kernelIdealSet κ X₁ W₂ (ψ₂.comp χ) :=
    hθ₁.image_injective hK12
  have hker : ∀ P : Pt X₁, ψ₁ (χ P) = 0 ↔ ψ₂ (χ P) = 0 := fun P =>
    apply_eq_zero_iff_of_kernelIdealSet_eq q' X₁ hss a b Λ₁ hΛ₁ θ₁ hθ₁ hθ₁Λ
      W₁ (ψ₁.comp χ) hφ₁ W₂ (ψ₂.comp χ) hφ₂ hKI P
  have hsurj : Function.Surjective χ := WeierstrassCurve.surjective_of_mem_rationalHomSet κ hχ hχ0
  ext T
  obtain ⟨P, rfl⟩ := hsurj T
  simp only [AddMonoidHom.mem_ker]
  exact hker P

omit [IsAlgClosed κ] in

theorem kernelIdealSet_comp_subset_of_eq_comp
    (X₁ W V W₁ : WeierstrassCurve κ)
    (χ : Pt X₁ →+ Pt W) (φ : Pt W →+ Pt V) (ψ : Pt W →+ Pt W₁) (β : Pt V →+ Pt W₁)
    (hβ : β ∈ WeierstrassCurve.rationalHomSet κ V W₁) (hfac : ψ = β.comp φ) :
    WeierstrassCurve.kernelIdealSet κ X₁ W₁ (ψ.comp χ) ⊆ WeierstrassCurve.kernelIdealSet κ X₁ V (φ.comp χ) := by
  rintro e ⟨ρ, hρ, he⟩
  exact ⟨ρ.comp β, WeierstrassCurve.comp_mem_rationalHomSet κ V W₁ X₁ hβ hρ, by rw [he, hfac]; rfl⟩

theorem ne_zero_of_comp_eq_nsmul_id (q' : ℕ) [Fact q'.Prime] [CharP κ q']
    (W : WeierstrassCurve κ) [W.IsElliptic] {B : Type*} [AddCommGroup B]
    (φ : W.toAffine.Point →+ B) (φ' : B →+ W.toAffine.Point) (N : ℕ) [NeZero N] (hq'N : ¬ q' ∣ N)
    (h : φ'.comp φ = N • AddMonoidHom.id _) : φ ≠ 0 := by
  rintro rfl
  obtain ⟨ℓ, hℓle, hℓp⟩ := Nat.exists_infinite_primes (N * q' + 1)
  have hq' : q'.Prime := Fact.out
  have hN : 0 < N := Nat.pos_of_ne_zero (NeZero.ne N)
  have hq'1 : 1 ≤ q' := hq'.one_lt.le
  have hℓN : N < ℓ := by nlinarith
  have hℓq : ℓ ≠ q' := by
    intro hℓq; subst hℓq; nlinarith
  have hℓκ : (ℓ : κ) ≠ 0 := by
    rw [Ne, CharP.cast_eq_zero_iff κ q' ℓ]
    intro hdvd
    exact hℓq ((Nat.prime_dvd_prime_iff_eq hq' hℓp).mp hdvd).symm
  obtain ⟨T, hT⟩ := WeierstrassCurve.exists_addOrderOf_eq_prime_of_isAlgClosed W ℓ hℓp hℓκ
  have hNT : N • T = 0 := by
    have h1 := DFunLike.congr_fun h T
    simp only [AddMonoidHom.comp_apply, AddMonoidHom.zero_apply, map_zero] at h1
    simpa using h1.symm
  have hdvd : ℓ ∣ N := hT ▸ (addOrderOf_dvd_iff_nsmul_eq_zero.mpr hNT)
  exact absurd (Nat.le_of_dvd hN hdvd) (not_le.mpr hℓN)

end Frame

theorem le_of_star_image_smul_subset {a b : ℚ} (d : (ℍ[ℚ, a, b])ˣ) {S T : Submodule ℤ ℍ[ℚ, a, b]}
    (h : star '' ((d • S : Submodule ℤ ℍ[ℚ, a, b]) : Set ℍ[ℚ, a, b]) ⊆
      star '' ((d • T : Submodule ℤ ℍ[ℚ, a, b]) : Set ℍ[ℚ, a, b])) : S ≤ T := by
  intro z hz
  have h1 : star ((d • z : ℍ[ℚ, a, b])) ∈ star '' ((d • T : Submodule ℤ ℍ[ℚ, a, b]) : Set ℍ[ℚ, a, b]) :=
    h ⟨d • z, Submodule.smul_mem_pointwise_smul z d S hz, rfl⟩
  obtain ⟨w, hw, hww⟩ := h1
  have hw' : w = d • z := star_injective hww
  rw [hw'] at hw
  obtain ⟨t, ht, hdt⟩ := (Submodule.mem_smul_pointwise_iff_exists _ _ _).mp hw
  have htz : t = z := smul_left_cancel d hdt
  exact htz ▸ ht

theorem le_of_le_of_relIndex_eq {M : Type*} [AddCommGroup M] {J J' I : AddSubgroup M}
    (hJJ' : J ≤ J') (hJ'I : J' ≤ I) (n : ℕ) (hn : n ≠ 0)
    (hJ : J.relIndex I = n) (hJ' : J'.relIndex I = n) : J' ≤ J := by
  have h := AddSubgroup.relIndex_mul_relIndex J J' I hJJ' hJ'I
  rw [hJ, hJ'] at h
  have h1 : J.relIndex J' = 1 := by
    have h2 : J.relIndex J' * n = 1 * n := by rw [one_mul]; exact h
    exact Nat.eq_of_mul_eq_mul_right (Nat.pos_of_ne_zero hn) h2
  exact AddSubgroup.relIndex_eq_one.mp h1

section Realised

variable {κ : Type} [Field κ] [DecidableEq κ] {a b : ℚ}

def Realised (X₁ W : WeierstrassCurve κ) (θ₁ : ↥(WeierstrassCurve.rationalEndSubring κ X₁) →+* ℍ[ℚ, a, b])
    (χ : Pt X₁ →+ Pt W) (d : (ℍ[ℚ, a, b])ˣ) (J : Submodule ℤ ℍ[ℚ, a, b]) (C : AddSubgroup (Pt W)) : Prop :=
  ∃ (W' : WeierstrassCurve κ) (_ : W'.IsElliptic) (ψ : Pt W →+ Pt W'),
    ψ ∈ WeierstrassCurve.rationalHomSet κ W W' ∧
    θ₁ '' WeierstrassCurve.kernelIdealSet κ X₁ W' (ψ.comp χ) =
      star '' ((d • J : Submodule ℤ ℍ[ℚ, a, b]) : Set ℍ[ℚ, a, b]) ∧
    ψ.ker = C

def RealisedUP (X₁ W : WeierstrassCurve κ) (θ₁ : ↥(WeierstrassCurve.rationalEndSubring κ X₁) →+* ℍ[ℚ, a, b])
    (χ : Pt X₁ →+ Pt W) (d : (ℍ[ℚ, a, b])ˣ) (J : Submodule ℤ ℍ[ℚ, a, b]) (C : AddSubgroup (Pt W)) : Prop :=
  ∃ (V : WeierstrassCurve κ) (_ : V.IsElliptic) (φ : Pt W →+ Pt V),
    φ ∈ WeierstrassCurve.rationalHomSet κ W V ∧ φ.ker = C ∧
    (∀ (W₃ : WeierstrassCurve κ) [W₃.IsElliptic] (α : Pt W →+ Pt W₃),
        α ∈ WeierstrassCurve.rationalHomSet κ W W₃ → (∀ P ∈ C, α P = 0) →
          ∃ β ∈ WeierstrassCurve.rationalHomSet κ V W₃, α = β.comp φ) ∧
    θ₁ '' WeierstrassCurve.kernelIdealSet κ X₁ V (φ.comp χ) =
      star '' ((d • J : Submodule ℤ ℍ[ℚ, a, b]) : Set ℍ[ℚ, a, b])

theorem RealisedUP.toRealised {X₁ W : WeierstrassCurve κ}
    {θ₁ : ↥(WeierstrassCurve.rationalEndSubring κ X₁) →+* ℍ[ℚ, a, b]}
    {χ : Pt X₁ →+ Pt W} {d : (ℍ[ℚ, a, b])ˣ} {J : Submodule ℤ ℍ[ℚ, a, b]} {C : AddSubgroup (Pt W)}
    (h : RealisedUP X₁ W θ₁ χ d J C) : Realised X₁ W θ₁ χ d J C := by
  obtain ⟨V, hV, φ, hφ, hker, -, hK⟩ := h
  exact ⟨V, hV, φ, hφ, hK, hker⟩

end Realised

end C1bReduce

open C1bReduce in
theorem solution
    {κ : Type} [Field κ] [IsAlgClosed κ] [DecidableEq κ]
    (q' : ℕ) [Fact q'.Prime] [CharP κ q'] [Algebra (ZMod q') κ] [Algebra.IsAlgebraic (ZMod q') κ]
    (X₁ : WeierstrassCurve κ) [X₁.IsElliptic] (hss : ∀ P : X₁.toAffine.Point, q' • P = 0 → P = 0)
    (a b : ℚ) (hdef : IsDefiniteRamifiedExactlyAt a b q')
    (Λ₁ : Submodule ℤ ℍ[ℚ, a, b]) (hΛ₁ : IsMaximalOrder Λ₁)
    (θ₁ : ↥(WeierstrassCurve.rationalEndSubring κ X₁) →+* ℍ[ℚ, a, b])
    (hθ₁ : Function.Injective θ₁) (hθ₁Λ : Set.range θ₁ = (Λ₁ : Set ℍ[ℚ, a, b]))
    (N : ℕ) [NeZero N] (hq'N : ¬ q' ∣ N)
    (m : (ℍ[ℚ, a, b] ⊗[ℚ] IsDedekindDomain.FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ)
    (hm₁ : ((m : (ℍ[ℚ, a, b] ⊗[ℚ] IsDedekindDomain.FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) : (ℍ[ℚ, a, b] ⊗[ℚ] IsDedekindDomain.FiniteAdeleRing (𝓞 ℚ) ℚ)) ∈ Submodule.finiteAdeleBox Λ₁)
    (hmN : ((N : ℕ) : ℚ) • ((m⁻¹ : (ℍ[ℚ, a, b] ⊗[ℚ] IsDedekindDomain.FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) : (ℍ[ℚ, a, b] ⊗[ℚ] IsDedekindDomain.FiniteAdeleRing (𝓞 ℚ) ℚ)) ∈ Submodule.finiteAdeleBox Λ₁)
    (hm : IsMaximalOrder (Submodule.conjByFiniteIdele Λ₁ m))
    (R : Submodule ℤ ℍ[ℚ, a, b]) (hR : R = Λ₁ ⊓ Submodule.conjByFiniteIdele Λ₁ m)
    (hRN : R.toAddSubgroup.relIndex Λ₁.toAddSubgroup = N)
    (x : (ℍ[ℚ, a, b] ⊗[ℚ] IsDedekindDomain.FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ)
    (W : WeierstrassCurve κ) [W.IsElliptic] (χ : X₁.toAffine.Point →+ W.toAffine.Point)
    (hχ : χ ∈ WeierstrassCurve.rationalHomSet κ X₁ W) (hχ0 : χ ≠ 0) (d : (ℍ[ℚ, a, b])ˣ)
    (hK : θ₁ '' WeierstrassCurve.kernelIdealSet κ X₁ W χ =
      star '' ((d • Submodule.ofFiniteIdele Λ₁ x : Submodule ℤ ℍ[ℚ, a, b]) : Set ℍ[ℚ, a, b])) :
    ∃ κx : {J : Submodule ℤ ℍ[ℚ, a, b] //
            ∃ u ∈ Submodule.finiteIdeleStabilizer Λ₁, J = Submodule.ofFiniteIdele Λ₁ (x * u * m)} ≃
        {C : AddSubgroup W.toAffine.Point // IsAddCyclic C ∧ Nat.card C = N},
      ∀ (J : {J : Submodule ℤ ℍ[ℚ, a, b] //
            ∃ u ∈ Submodule.finiteIdeleStabilizer Λ₁, J = Submodule.ofFiniteIdele Λ₁ (x * u * m)})
          (W' : WeierstrassCurve κ) [W'.IsElliptic] (ψ : W.toAffine.Point →+ W'.toAffine.Point),
          ψ ∈ WeierstrassCurve.rationalHomSet κ W W' →
        ∀ (ψ' : W'.toAffine.Point →+ W.toAffine.Point), ψ' ∈ WeierstrassCurve.rationalHomSet κ W' W →
          ψ'.comp ψ = (N : ℕ) • AddMonoidHom.id _ → ψ.comp ψ' = (N : ℕ) • AddMonoidHom.id _ →
          θ₁ '' WeierstrassCurve.kernelIdealSet κ X₁ W' (ψ.comp χ) =
            star '' ((d • (J : Submodule ℤ ℍ[ℚ, a, b]) : Submodule ℤ ℍ[ℚ, a, b]) : Set ℍ[ℚ, a, b]) →
          ψ.ker = ((κx J).1 : AddSubgroup W.toAffine.Point) := by
  classical
  subst hR
  have hO : IsOrder Λ₁ := hΛ₁.isOrder
  have hsurjχ : Function.Surjective χ := WeierstrassCurve.surjective_of_mem_rationalHomSet κ hχ hχ0

  obtain ⟨σχ, hσχ, nχ, hnχ, hdualχ⟩ := WeierstrassCurve.exists_isDualPair_of_mem_rationalHomSet κ X₁ W hχ hχ0
  have hssW : ∀ P : W.toAffine.Point, q' • P = 0 → P = 0 :=
    C1bReduce.forall_nsmul_eq_zero_of_dual hnχ.ne' hdualχ.comp_left hsurjχ (Fact.out : q'.Prime) hss

  have hxu : ∀ u ∈ Submodule.finiteIdeleStabilizer Λ₁,
      Submodule.ofFiniteIdele Λ₁ (x * u) = Submodule.ofFiniteIdele Λ₁ x := fun u hu =>
    ((Submodule.ofFiniteIdele_eq_ofFiniteIdele_iff Λ₁ hO.fg hO.spanTop x (x * u)).mpr
      (by rwa [inv_mul_cancel_left])).symm

  have hle_of_mem : ∀ (y g : (ℍ[ℚ, a, b] ⊗[ℚ] IsDedekindDomain.FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ), (g : (ℍ[ℚ, a, b] ⊗[ℚ] IsDedekindDomain.FiniteAdeleRing (𝓞 ℚ) ℚ)) ∈ Submodule.finiteAdeleBox Λ₁ →
      Submodule.ofFiniteIdele Λ₁ (y * g) ≤ Submodule.ofFiniteIdele Λ₁ y := by
    intro y g hg
    have h1 := (QuaternionAlgebra.IsOrder.ofFiniteIdele_mul_le_zsmul_ofFiniteIdele_iff_inv_smul_mem_finiteAdeleBox
      hO y g 1).mpr (by simpa using hg)
    simpa using h1

  have hT : ∀ u ∈ Submodule.finiteIdeleStabilizer Λ₁,
      Submodule.ofFiniteIdele Λ₁ (x * u * m) ≤ Submodule.ofFiniteIdele Λ₁ x ∧
      (Submodule.ofFiniteIdele Λ₁ (x * u * m)).toAddSubgroup.relIndex
          (Submodule.ofFiniteIdele Λ₁ (x * u)).toAddSubgroup = N ^ 2 ∧
      (Submodule.ofFiniteIdele Λ₁ (x * u * m)).toAddSubgroup.relIndex
          (Submodule.ofFiniteIdele Λ₁ x).toAddSubgroup = N ^ 2 := by
    intro u hu
    have hQ := (QuaternionAlgebra.exists_ofFiniteIdele_mul_eq_ofFiniteIdele_mul_mul_iff_relIndex_eq_sq_and_forall_not_le_zsmul
      Λ₁ hΛ₁ N m hm₁ hmN hRN (x * u) m hm₁).mp ⟨1, one_mem _, by rw [mul_one]⟩
    refine ⟨?_, hQ.1, ?_⟩
    · have h1 := hle_of_mem (x * u) m hm₁
      rwa [hxu u hu] at h1
    · have h2 := hQ.1
      rwa [hxu u hu] at h2

  have R1 : ∀ J : {J : Submodule ℤ ℍ[ℚ, a, b] //
            ∃ u ∈ Submodule.finiteIdeleStabilizer Λ₁, J = Submodule.ofFiniteIdele Λ₁ (x * u * m)},
      ∃ C : {C : AddSubgroup W.toAffine.Point // IsAddCyclic C ∧ Nat.card C = N},
        Realised X₁ W θ₁ χ d J.1 C.1 := by
    rintro ⟨J, u, hu, rfl⟩
    have hKu : θ₁ '' WeierstrassCurve.kernelIdealSet κ X₁ W χ =
        star '' ((d • Submodule.ofFiniteIdele Λ₁ (x * u) : Submodule ℤ ℍ[ℚ, a, b]) : Set ℍ[ℚ, a, b]) := by
      rw [hxu u hu]; exact hK
    obtain ⟨-, hidx', -⟩ := hT u hu
    have hq'idx : ¬ q' ∣ (Submodule.ofFiniteIdele Λ₁ (x * u * m)).toAddSubgroup.relIndex
        (Submodule.ofFiniteIdele Λ₁ (x * u)).toAddSubgroup := by
      rw [hidx']; exact fun h => hq'N ((Fact.out : q'.Prime).dvd_of_dvd_pow h)
    obtain ⟨W', hW', ψ, hψ, ψ', hψ', hKψ, hψ'ψ, hψψ'⟩ :=
      CerednikDrinfeld.exists_dualPair_image_kernelIdealSet_comp_eq_star_smul_ofFiniteIdele_mul_of_mem_finiteAdeleBox
        q' X₁ hss a b hdef Λ₁ hΛ₁ θ₁ hθ₁ hθ₁Λ (x * u) W χ hχ hχ0 d hKu m hm₁ hq'idx
    haveI : W'.IsElliptic := hW'
    have hcard2 :=
      CerednikDrinfeld.natCard_ker_sq_eq_relIndex_ofFiniteIdele_mul_of_image_kernelIdealSet_comp_eq
        q' X₁ hss a b hdef Λ₁ hΛ₁ θ₁ hθ₁ hθ₁Λ (x * u) W χ hχ hχ0 d hKu m hm₁ W' ψ hψ ψ' hψ' ⟨hψ'ψ, hψψ'⟩ hKψ
    rw [hidx'] at hcard2
    have hcard : Nat.card ψ.ker = N := Nat.pow_left_injective two_ne_zero hcard2
    have hprim :=
      QuaternionAlgebra.forall_inv_smul_not_mem_finiteAdeleBox_of_mem_of_smul_inv_mem_of_relIndex_inf_conjByFiniteIdele_eq
        Λ₁ hΛ₁ N m hm₁ hmN hRN
    have hcyc : IsAddCyclic ψ.ker :=
      CerednikDrinfeld.isAddCyclic_ker_of_forall_inv_smul_not_mem_finiteAdeleBox_of_image_kernelIdealSet_comp_eq
        q' X₁ hss a b hdef Λ₁ hΛ₁ θ₁ hθ₁ hθ₁Λ (x * u) W χ hχ hχ0 d hKu m hm₁ W' ψ hψ ψ' hψ' ⟨hψ'ψ, hψψ'⟩ hKψ hprim
    exact ⟨⟨ψ.ker, hcyc, hcard⟩, W', hW', ψ, hψ, hKψ, rfl⟩

  have R2 : ∀ C : {C : AddSubgroup W.toAffine.Point // IsAddCyclic C ∧ Nat.card C = N},
      ∃ J : {J : Submodule ℤ ℍ[ℚ, a, b] //
            ∃ u ∈ Submodule.finiteIdeleStabilizer Λ₁, J = Submodule.ofFiniteIdele Λ₁ (x * u * m)},
        RealisedUP X₁ W θ₁ χ d J.1 C.1 ∧ J.1 ≤ Submodule.ofFiniteIdele Λ₁ x ∧
        J.1.toAddSubgroup.relIndex (Submodule.ofFiniteIdele Λ₁ x).toAddSubgroup = N ^ 2 := by
    rintro ⟨C, hCcyc, hCcard⟩
    haveI : Finite C := Nat.finite_of_card_ne_zero (by rw [hCcard]; exact NeZero.ne N)
    have hCfin : (C : Set W.toAffine.Point).Finite := Set.toFinite _
    obtain ⟨V, hV, φ, hφ, φ', hφ', hker, hup, hφ'φ, hφφ', -⟩ :=
      WeierstrassCurve.exists_quotient_dualPair_kernelIdealSet_comp_eq q' X₁ W hssW χ C hCfin
    haveI : V.IsElliptic := hV
    have hcardkerC : Nat.card φ.ker = Nat.card C := by rw [hker]; rfl
    have hcardker : Nat.card φ.ker = N := hcardkerC.trans hCcard
    have hφ'φN : φ'.comp φ = N • AddMonoidHom.id _ :=
      hφ'φ.trans (congrArg (· • AddMonoidHom.id _) hCcard)
    have hφ0 : φ ≠ 0 := ne_zero_of_comp_eq_nsmul_id q' W φ φ' N hq'N hφ'φN
    have hψd : φ'.comp φ = Nat.card φ.ker • AddMonoidHom.id _ ∧
        φ.comp φ' = Nat.card φ.ker • AddMonoidHom.id _ :=
      ⟨hφ'φ.trans (congrArg (· • AddMonoidHom.id _) hcardkerC.symm),
       hφφ'.trans (congrArg (· • AddMonoidHom.id _) hcardkerC.symm)⟩
    have hcycker : IsAddCyclic φ.ker := by rw [hker]; exact hCcyc
    obtain ⟨g, hg, hKg, hidx⟩ :=
      CerednikDrinfeld.exists_mem_finiteAdeleBox_image_kernelIdealSet_comp_eq_star_smul_ofFiniteIdele_mul_of_dualPair
        q' X₁ hss a b hdef Λ₁ hΛ₁ θ₁ hθ₁ hθ₁Λ x W χ hχ hχ0 d hK V φ hφ hφ0 φ' hφ' hψd
    have hidxN : (Submodule.ofFiniteIdele Λ₁ (x * g)).toAddSubgroup.relIndex
        (Submodule.ofFiniteIdele Λ₁ x).toAddSubgroup = N ^ 2 :=
      hidx.symm.trans (congrArg (· ^ 2) hcardker)
    have hprim : ∀ ℓ : ℕ, ℓ.Prime → ((ℓ : ℚ)⁻¹ • ((g : (ℍ[ℚ, a, b] ⊗[ℚ] IsDedekindDomain.FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) : (ℍ[ℚ, a, b] ⊗[ℚ] IsDedekindDomain.FiniteAdeleRing (𝓞 ℚ) ℚ))) ∉ Submodule.finiteAdeleBox Λ₁ :=
      (CerednikDrinfeld.isAddCyclic_ker_iff_forall_inv_smul_not_mem_finiteAdeleBox_of_image_kernelIdealSet_comp_eq
        q' X₁ hss a b hdef Λ₁ hΛ₁ θ₁ hθ₁ hθ₁Λ x W χ hχ hχ0 d hK g hg V φ hφ φ' hφ' hψd hKg).mp
        hcycker
    have hlat : ∀ p : ℕ, p.Prime →
        ¬ (Submodule.ofFiniteIdele Λ₁ (x * g) ≤ ((p : ℕ) : ℤ) • Submodule.ofFiniteIdele Λ₁ x) := by
      intro p hp hle
      haveI : NeZero p := ⟨hp.ne_zero⟩
      exact hprim p hp
        ((QuaternionAlgebra.IsOrder.ofFiniteIdele_mul_le_zsmul_ofFiniteIdele_iff_inv_smul_mem_finiteAdeleBox
          hO x g p).mp hle)
    obtain ⟨u, hu, hJu⟩ :=
      (QuaternionAlgebra.exists_ofFiniteIdele_mul_eq_ofFiniteIdele_mul_mul_iff_relIndex_eq_sq_and_forall_not_le_zsmul
        Λ₁ hΛ₁ N m hm₁ hmN hRN x g hg).mpr ⟨hidxN, hlat⟩
    exact ⟨⟨Submodule.ofFiniteIdele Λ₁ (x * g), u, hu, hJu⟩, ⟨V, hV, φ, hφ, hker, hup, hKg⟩,
      hle_of_mem x g hg, hidxN⟩

  have R3 : ∀ (J : Submodule ℤ ℍ[ℚ, a, b]) (C₁ C₂ : AddSubgroup W.toAffine.Point),
      Realised X₁ W θ₁ χ d J C₁ → Realised X₁ W θ₁ χ d J C₂ → C₁ = C₂ := by
    rintro J C₁ C₂ ⟨W₁, hW₁, ψ₁, hψ₁, hK₁, rfl⟩ ⟨W₂, hW₂, ψ₂, hψ₂, hK₂, rfl⟩
    haveI : W₁.IsElliptic := hW₁
    haveI : W₂.IsElliptic := hW₂
    exact ker_eq_ker_of_image_kernelIdealSet_comp_eq q' X₁ hss a b Λ₁ hO θ₁ hθ₁ hθ₁Λ W χ hχ hχ0
      W₁ ψ₁ hψ₁ W₂ ψ₂ hψ₂ (hK₁.trans hK₂.symm)

  have R4 : ∀ (u : (ℍ[ℚ, a, b] ⊗[ℚ] IsDedekindDomain.FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ), u ∈ Submodule.finiteIdeleStabilizer Λ₁ →
      ∀ (J' : Submodule ℤ ℍ[ℚ, a, b]) (C : AddSubgroup W.toAffine.Point),
        Realised X₁ W θ₁ χ d (Submodule.ofFiniteIdele Λ₁ (x * u * m)) C →
        RealisedUP X₁ W θ₁ χ d J' C → J' ≤ Submodule.ofFiniteIdele Λ₁ x →
        J'.toAddSubgroup.relIndex (Submodule.ofFiniteIdele Λ₁ x).toAddSubgroup = N ^ 2 →
        Submodule.ofFiniteIdele Λ₁ (x * u * m) = J' := by
    rintro u hu J' C ⟨W₁, hW₁, ψ₁, hψ₁, hK₁, rfl⟩ ⟨V, hV, φ, hφ, hker, hup, hK'⟩ hJ'I hJ'idx
    haveI : W₁.IsElliptic := hW₁
    haveI : V.IsElliptic := hV
    obtain ⟨β, hβ, hfac⟩ := hup W₁ ψ₁ hψ₁ (fun P hP => (AddMonoidHom.mem_ker).mp hP)
    have hsub := Set.image_mono (f := θ₁) (kernelIdealSet_comp_subset_of_eq_comp X₁ W V W₁ χ φ ψ₁ β hβ hfac)
    rw [hK₁, hK'] at hsub
    have hJJ' : Submodule.ofFiniteIdele Λ₁ (x * u * m) ≤ J' := le_of_star_image_smul_subset d hsub
    obtain ⟨-, -, hJidx⟩ := hT u hu
    exact le_antisymm hJJ' ((Submodule.toAddSubgroup_le (p := _) (p' := _)).mp
      (le_of_le_of_relIndex_eq (Submodule.toAddSubgroup_mono hJJ') (Submodule.toAddSubgroup_mono hJ'I)
        (N ^ 2) (pow_ne_zero 2 (NeZero.ne N)) hJidx hJ'idx))
  choose F hF using R1
  choose G hG using R2
  refine ⟨{ toFun := F, invFun := G, left_inv := ?_, right_inv := ?_ }, ?_⟩
  · rintro ⟨J, u, hu, rfl⟩
    apply Subtype.ext
    obtain ⟨hUP, hGI, hGidx⟩ := hG (F ⟨_, u, hu, rfl⟩)
    exact (R4 u hu _ _ (hF ⟨_, u, hu, rfl⟩) hUP hGI hGidx).symm
  · intro C
    apply Subtype.ext
    obtain ⟨hUP, -, -⟩ := hG C
    exact R3 _ _ _ (hF (G C)) hUP.toRealised
  · intro J W' _ ψ hψ ψ' hψ' _ _ hKJ
    exact R3 _ _ _ ⟨W', ‹W'.IsElliptic›, ψ, hψ, hKJ, rfl⟩ (hF J)

end S_CerednikDrinfeld_exists_equiv_ofFiniteIdele_mul_isAddCyclic_forall_ker_eq_of_kernelIdealSet_comp_eq
end P2MW
export P2MW.S_CerednikDrinfeld_exists_equiv_ofFiniteIdele_mul_isAddCyclic_forall_ker_eq_of_kernelIdealSet_comp_eq (solution)
