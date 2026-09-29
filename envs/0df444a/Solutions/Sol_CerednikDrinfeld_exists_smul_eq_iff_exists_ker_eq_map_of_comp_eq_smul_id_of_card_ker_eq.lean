-- Prove2me | solution 1 for CerednikDrinfeld.exists_smul_eq_iff_exists_ker_eq_map_of_comp_eq_smul_id_of_card_ker_eq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.491319+00:00
-- url     : https://prove2.me/submissions/15893232-5e00-525e-b282-b68a43ea4a72

import Mathlib
import Definitions.Def_QuaternionAlgebra_EichlerOrder
import Definitions.Def_WeierstrassCurve_RationalEnd
import Definitions.Def_WeierstrassCurve_KernelIdeal
import Definitions.Def_CerednikDrinfeld_ClassSetGraph
import Theorems.Thm_CerednikDrinfeld_exists_mem_rationalHomSet_comp_eq_id_forall_mem_ker_of_image_kernelIdealSet_eq_image_mul
import Theorems.Thm_CerednikDrinfeld_exists_units_image_kernelIdealSet_pair_eq_image_mul_of_comp_eq_id_forall_mem_ker
import Theorems.Thm_QuaternionAlgebra_star_image_smul_eq_mulRight_image_star_image_smul_iff
import Theorems.Thm_WeierstrassCurve_exists_addOrderOf_eq_prime_of_isAlgClosed
import Theorems.Thm_Submodule_ofFiniteIdele_eq_ofFiniteIdele_iff
import Theorems.Thm_Submodule_ofFiniteIdele_diagonal_mul
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_exists_smul_eq_iff_exists_ker_eq_map_of_comp_eq_smul_id_of_card_ker_eq
p2m_attr_erase "instance" "WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue AlgebraicCurve.Place.instIsScalarTowerSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Divisor.instDistribMulActionAlgEquiv AlgebraicCurve.Place.instSMulAlgEquiv AlgebraicCurve.Place.instIsPrincipalIdealRingSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Place.instIsDiscreteValuationRingSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Pic0.instDistribMulActionAlgEquiv AlgebraicCurve.Place.instAlgebraSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Place.instMulActionAlgEquiv AlgebraicCurve.Pic0.instSMulAlgEquiv AlgebraicCurve.instFundamentalIdentityOfSumRamificationInertia AlgebraicCurve.Place.instIsScalarTowerResidueFieldRestrictPushforward AlgebraicCurve.Place.instAlgebraResidueFieldRestrictPushforward AlgebraicCurve.Place.instIsLocalHomRestrictInclusion AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupDivisor AlgebraicCurve.Pic0.instModuleZModTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instDistribMulActionTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instSMulTorsion AlgebraicCurve.SemilinearAut.instMulActionSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instSMulCommClassZModTorsion AlgebraicCurve.SemilinearAut.instMulSemiringActionSubtypeProdRingAutMemSubgroup WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy"
p2m_attr_erase "instance" "ModularCurve.SpecializationWitnessData.addCommGroup ModularCurve.CommutingHeckeFamily.commRing_adjoin ModularCurve.Gamma0Pair.isElliptic AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt WeierstrassCurve.Affine.instIsScalarTowerPolynomialRatFuncFunctionField_definitions WeierstrassCurve.Affine.instAlgebraRatFuncFunctionField_definitions WeierstrassCurve.Affine.instIsScalarTowerRatFuncFunctionField_definitions WeierstrassCurve.Affine.CoordinateRing.moduleFinite WeierstrassCurve.Affine.instDecidableEqFunctionField WeierstrassCurve.Affine.CoordinateRing.isIntegral IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions"
p2m_attr_erase "simp" "compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two ModularCurve.coe_levelAlphaC ModularCurve.SSLevelDatum.mk.sizeOf_spec ModularCurve.SSLevelDatum.mk.injEq ModularCurve.coe_levelBetaC ModularCurve.coe_heckeBetaC AlgebraicCurve.Divisor.coe_degZeroEnd ModularCurve.coe_heckeAlphaC"
p2m_attr_erase "simp" "AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Place.mk.injEq AlgebraicCurve.Divisor.degree_single AlgebraicCurve.Divisor.smul_single AlgebraicCurve.Place.smul_toValuationSubring AlgebraicCurve.Place.heightOneSpectrum_asIdeal AlgebraicCurve.Place.coe_algebraMap AlgebraicCurve.Place.ord_one AlgebraicCurve.Place.coe_smulRingEquiv_apply AlgebraicCurve.Pic0.coe_degZeroSMulHom AlgebraicCurve.Place.deg_smul AlgebraicCurve.Pic0.mk_zero AlgebraicCurve.Place.mk.sizeOf_spec AlgebraicCurve.Divisor.degree_smul AlgebraicCurve.Pic0.mk_add AlgebraicCurve.Place.ord_zero AlgebraicCurve.Place.ofHeightOneSpectrum_toValuationSubring AlgebraicCurve.Divisor.mapRestrict_single AlgebraicCurve.Divisor.pushforward_single AlgebraicCurve.Place.coe_restrictInclusion AlgebraicCurve.Place.mem_fiber AlgebraicCurve.Place.restrict_toValuationSubring AlgebraicCurve.Divisor.degree_pushforward AlgebraicCurve.Place.restrictResidueMap_residue AlgebraicCurve.Pic0.coe_pushforwardDegZeroHom AlgebraicCurve.Pic0.coe_pullbackDegZeroHom"
p2m_attr_erase "simp" "AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.Divisor.degree_pushforwardAlong AlgebraicCurve.Pic0.coe_degZeroCorrespondence AlgebraicCurve.Place.mem_fiberAlong AlgebraicCurve.SemilinearAut.toRingAut_inv AlgebraicCurve.SemilinearAut.smul_def AlgebraicCurve.SemilinearAut.smul_single AlgebraicCurve.SemilinearAut.smul_toValuationSubring AlgebraicCurve.SemilinearAut.baseAut_inv AlgebraicCurve.SemilinearAut.baseAut_ofAlgAut AlgebraicCurve.SemilinearAut.toRingAut_ofAlgAut AlgebraicCurve.SemilinearAut.torsionRep_apply AlgebraicCurve.SemilinearAut.toRingAut_one AlgebraicCurve.SemilinearAut.deg_smul AlgebraicCurve.SemilinearAut.degree_smul AlgebraicCurve.SemilinearAut.coe_degZeroSMulHom AlgebraicCurve.SemilinearAut.baseAut_mul AlgebraicCurve.SemilinearAut.coe_smulValuationSubringEquiv_apply AlgebraicCurve.SemilinearAut.baseAut_one AlgebraicCurve.SemilinearAut.ofAlgAut_smul AlgebraicCurve.SemilinearAut.coe_torsion_smul AlgebraicCurve.SemilinearAut.toRingAut_mul AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.jqNModC_one ModularCurve.qExpand_coeff_mul ModularCurve.qExpandₐ_apply ModularCurve.jqN_one ModularCurve.qExpand_single ModularCurve.dedekindPsi_one ModularCurve.ModularPolynomialData.mk.sizeOf_spec ModularCurve.evalAtJ_X ModularCurve.ModularPolynomialData.mk.injEq ModularCurve.constantCoeff_jNum ModularCurve.constantCoeff_eisenstein4"
p2m_attr_erase "simp" "ModularCurve.qExpand_C ModularCurve.coeff_jq_neg_one ModularCurve.constantCoeff_jNumQ ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd FreyPackage.mk.sizeOf_spec FreyPackage.mk.injEq WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply ModularCurve.CommutingHeckeFamily.mk.injEq ModularCurve.SpecializationWitnessData.mk.sizeOf_spec ModularCurve.SpecializationWitnessData.mk.injEq ModularCurve.CommutingHeckeFamily.mk.sizeOf_spec ModularCurve.coe_nodeEquivOfPlaces_apply ModularCurve.widthOfPlaces_mk ModularCurve.smulNodePairEmb_apply ModularCurve.card_nodePairsOfPlaces ModularCurve.smulNodePair_snd ModularCurve.smulNodePair_fst ModularCurve.coe_nodeEquivOfPlaces_symm_apply ModularCurve.coe_jGeomGen ModularCurve.coe_jNGeomGen ModularCurve.coe_uniformizerMod ModularCurve.qSeriesBar_jModElt ModularCurve.qInftyPlaceMod_toValuationSubring ModularCurve.qInftyPlaceBar_toValuationSubring ModularCurve.qSeriesBar_zero ModularCurve.qSeriesBar_add ModularCurve.cuspInftyFull_toValuationSubring ModularCurve.qInftyPlaceRat_toValuationSubring ModularCurve.qSeriesBar_mul ModularCurve.qSeriesBar_div"
p2m_attr_erase "simp" "ModularCurve.qSeriesBar_eq_zero_iff ModularCurve.coe_uniformizerBar ModularCurve.qSeriesBar_pow ModularCurve.cuspInfty_toValuationSubring ModularCurve.qSeriesBar_one ModularCurve.qSeriesBar_inv ModularCurve.qSeriesBar_sub ModularCurve.qSeriesBar_neg ModularCurve.charLGeomModuliDictionary_single ModularCurve.specializeModuli_single ModularCurve.specializePlace_def AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one ModularCurve.gamma0PairMap_gen ModularCurve.moduliPointMapRingHom_mk ModularCurve.Gamma0Pair.mk.injEq ModularCurve.ModuliPoint.j_mk ModularCurve.Gamma0Pair.mk.sizeOf_spec ModularCurve.gamma0PairMap_toCurve WeierstrassCurve.Affine.vcY_vcYInv WeierstrassCurve.Affine.vcXInv_vcX WeierstrassCurve.Affine.Point.vcFun_zero WeierstrassCurve.Affine.vcX_vcXInv WeierstrassCurve.Affine.vcYInv_vcY WeierstrassCurve.Affine.Point.vcInvFun_zero WeierstrassCurve.ratPointHom_apply WeierstrassCurve.ratPointMap_zero AddMonoid.End.DualEndData.symm_trace AddMonoid.End.dualEndData_intCast_norm AddMonoid.End.DualEndData.ofCharPoly_norm AddMonoid.End.DualEndData.mk.sizeOf_spec AddMonoid.End.DualEndData.mk.injEq AddMonoid.End.DualEndData.ofCharPoly_dual AddMonoid.End.dualEndData_intCast_dual AddMonoid.End.DualEndData.intLinComb_norm AddMonoid.End.DualEndData.ofCharPoly_trace AddMonoid.End.DualEndData.intLinComb_dual AddMonoid.End.DualEndData.symm_dual AddMonoid.End.DualEndData.intLinComb_trace AddMonoid.End.dualEndData_intCast_trace"
p2m_attr_erase "simp" "AddMonoid.End.DualEndData.symm_norm AddMonoid.End.dualEndDataOfSurjective_trace AddMonoid.End.dualEndDataOfSurjective_norm WeierstrassCurve.Universal.halveX_zero WeierstrassCurve.Universal.specialize_X_one WeierstrassCurve.Universal.coeff_halve WeierstrassCurve.Universal.specialize_X_two WeierstrassCurve.Universal.halveCoeff_zero WeierstrassCurve.Universal.specialize_X_four WeierstrassCurve.Universal.coeff_halveX WeierstrassCurve.Universal.specialize_X_three WeierstrassCurve.Universal.specialize_X_zero WeierstrassCurve.pointAddEquivOfEq_refl WeierstrassCurve.veluWSum_empty WeierstrassCurve.veluQuotient_a₁ WeierstrassCurve.veluQuotient_a₃ WeierstrassCurve.veluQuotient_empty WeierstrassCurve.veluTSum_empty WeierstrassCurve.veluQuotient_a₂ WeierstrassCurve.veluX_empty WeierstrassCurve.veluY_empty WeierstrassCurve.Affine.Point.coordsOrZero_some WeierstrassCurve.Affine.Point.coordsOrZero_zero WeierstrassCurve.Affine.IsogenyEndDatum.mk.injEq WeierstrassCurve.Affine.IsogenyHomDatum.mk.sizeOf_spec WeierstrassCurve.Affine.IsogenyHomDatum.mk.injEq WeierstrassCurve.Affine.IsogenyEndDatum.mk.sizeOf_spec AlgebraicCurve.Pic0.coe_pushforwardAlongDegZero WeierstrassCurve.Affine.pointMapOfPushforward_apply WeierstrassCurve.Affine.pointClass_zero WeierstrassCurve.Affine.pic0ToPoint_pointClass WeierstrassCurve.Affine.deg_placeOfPoint WeierstrassCurve.Affine.coe_pointDivisor WeierstrassCurve.Affine.pointEquivPlace_symm_placeOfPoint WeierstrassCurve.Affine.pointEquivPlace_apply WeierstrassCurve.Affine.genusOnePic0Equiv_symm_apply WeierstrassCurve.Affine.pointDivisor_zero WeierstrassCurve.Affine.pic0ToPoint_mk WeierstrassCurve.Affine.divisorSum_single WeierstrassCurve.Affine.genusOnePic0Equiv_apply"
p2m_attr_erase "simp" "AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal WeierstrassCurve.vcInvEmbedding_apply WeierstrassCurve.map_veluU WeierstrassCurve.map_veluT WeierstrassCurve.map_veluW WeierstrassCurve.map_veluGy WeierstrassCurve.map_veluGx WeierstrassCurve.map_veluWSum_singleton WeierstrassCurve.map_veluTSum_singleton WeierstrassCurve.veluPointMap3_zero WeierstrassCurve.Affine.ratFuncToFunctionField_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_C WeierstrassCurve.Affine.Point.yc_some WeierstrassCurve.Affine.Point.xc_some WeierstrassCurve.Affine.pointPull_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_X WeierstrassCurve.Affine.pointHom_mk_Y WeierstrassCurve.Affine.placeOf_asIdeal WeierstrassCurve.veluPointMap2_zero WeierstrassCurve.veluQuotient2_a₂ WeierstrassCurve.veluQuotient2_a₃ WeierstrassCurve.veluQuotient2_a₁ QuaternionAlgebra.baseChangeRight_tmul QuaternionAlgebra.mapOfAlgebraMapEq_apply QuaternionAlgebra.baseChange_tmul"

set_option autoImplicit false

open scoped Quaternion TensorProduct NumberField Pointwise
open QuaternionAlgebra CerednikDrinfeld IsDedekindDomain

namespace IsoUnit

variable {κ : Type} [Field κ] [IsAlgClosed κ] [DecidableEq κ]

theorem ne_zero_of_comp_eq_nsmul_id (q' : ℕ) [Fact q'.Prime] [CharP κ q']
    {W W₁ : WeierstrassCurve κ} [W.IsElliptic]
    {ψ : W.toAffine.Point →+ W₁.toAffine.Point} {ψd : W₁.toAffine.Point →+ W.toAffine.Point}
    {N : ℕ} (hN0 : N ≠ 0) (h : ψd.comp ψ = N • AddMonoidHom.id _) : ψ ≠ 0 := by
  intro h0
  obtain ⟨r, hrle, hr⟩ := Nat.exists_infinite_primes (max N q' + 1)
  have hrN : N < r := lt_of_lt_of_le (Nat.lt_succ_of_le (le_max_left _ _)) hrle
  have hrq : q' < r := lt_of_lt_of_le (Nat.lt_succ_of_le (le_max_right _ _)) hrle
  have hrκ : (r : κ) ≠ 0 := by
    intro hz
    have := (CharP.cast_eq_zero_iff κ q' r).mp hz
    exact (ne_of_gt hrq) ((Nat.prime_dvd_prime_iff_eq Fact.out hr).mp this).symm
  obtain ⟨T, hT⟩ := WeierstrassCurve.exists_addOrderOf_eq_prime_of_isAlgClosed W r hr hrκ
  have hNT : N • T = 0 := by
    have := DFunLike.congr_fun h T
    rw [AddMonoidHom.comp_apply, h0, AddMonoidHom.zero_apply, map_zero, AddMonoidHom.nsmul_apply,
      AddMonoidHom.id_apply] at this
    exact this.symm
  have hdvd : r ∣ N := by rw [← hT]; exact addOrderOf_dvd_of_nsmul_eq_zero hNT
  exact absurd (Nat.le_of_dvd (Nat.pos_of_ne_zero hN0) hdvd) (not_le.mpr hrN)

variable {a b : ℚ}

theorem image_mulRight_inv {A B : Set ℍ[ℚ, a, b]} (c : (ℍ[ℚ, a, b])ˣ)
    (h : B = (· * (c : ℍ[ℚ, a, b])) '' A) : A = (· * ((c⁻¹ : (ℍ[ℚ, a, b])ˣ) : ℍ[ℚ, a, b])) '' B := by
  rw [h, Set.image_image]
  ext z
  simp only [Set.mem_image, Units.mul_inv_cancel_right, exists_eq_right]

end IsoUnit

open IsoUnit in
theorem solution
    {κ : Type} [Field κ] [IsAlgClosed κ] [DecidableEq κ]
    (q' : ℕ) [Fact q'.Prime] [CharP κ q'] [Algebra (ZMod q') κ] [Algebra.IsAlgebraic (ZMod q') κ]
    (X₁ : WeierstrassCurve κ) [X₁.IsElliptic] (hss : ∀ P : X₁.toAffine.Point, q' • P = 0 → P = 0)
    (a b : ℚ) (hdef : IsDefiniteRamifiedExactlyAt a b q')
    (Λ₁ : Submodule ℤ ℍ[ℚ, a, b]) (hΛ₁ : IsMaximalOrder Λ₁)
    (θ₁ : ↥(WeierstrassCurve.rationalEndSubring κ X₁) →+* ℍ[ℚ, a, b])
    (hθ₁ : Function.Injective θ₁) (hθ₁Λ : Set.range θ₁ = (Λ₁ : Set ℍ[ℚ, a, b]))
    (x : (ℍ[ℚ, a, b] ⊗[ℚ] IsDedekindDomain.FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ)
    (W₁ : WeierstrassCurve κ) [W₁.IsElliptic] (χ₁ : X₁.toAffine.Point →+ W₁.toAffine.Point)
    (hχ₁ : χ₁ ∈ WeierstrassCurve.rationalHomSet κ X₁ W₁) (hχ₁0 : χ₁ ≠ 0) (d₁ : (ℍ[ℚ, a, b])ˣ)
    (hK₁ : θ₁ '' WeierstrassCurve.kernelIdealSet κ X₁ W₁ χ₁ =
      star '' ((d₁ • Submodule.ofFiniteIdele Λ₁ x : Submodule ℤ ℍ[ℚ, a, b]) : Set ℍ[ℚ, a, b]))
    (J₁ : Submodule ℤ ℍ[ℚ, a, b])
    (W₁' : WeierstrassCurve κ) [W₁'.IsElliptic] (ψ₁ : W₁.toAffine.Point →+ W₁'.toAffine.Point)
    (hψ₁ : ψ₁ ∈ WeierstrassCurve.rationalHomSet κ W₁ W₁')
    (ψ₁' : W₁'.toAffine.Point →+ W₁.toAffine.Point) (hψ₁' : ψ₁' ∈ WeierstrassCurve.rationalHomSet κ W₁' W₁)
    (N₁ : ℕ) (hN₁ : ¬ q' ∣ N₁)
    (hψ₁d : ψ₁'.comp ψ₁ = (N₁ : ℕ) • AddMonoidHom.id _ ∧ ψ₁.comp ψ₁' = (N₁ : ℕ) • AddMonoidHom.id _)
    (hψ₁N : Nat.card ψ₁.ker = N₁)
    (hJ₁ : θ₁ '' WeierstrassCurve.kernelIdealSet κ X₁ W₁' (ψ₁.comp χ₁) =
      star '' ((d₁ • J₁ : Submodule ℤ ℍ[ℚ, a, b]) : Set ℍ[ℚ, a, b]))
    (W₂ : WeierstrassCurve κ) [W₂.IsElliptic] (χ₂ : X₁.toAffine.Point →+ W₂.toAffine.Point)
    (hχ₂ : χ₂ ∈ WeierstrassCurve.rationalHomSet κ X₁ W₂) (hχ₂0 : χ₂ ≠ 0) (d₂ : (ℍ[ℚ, a, b])ˣ)
    (hK₂ : θ₁ '' WeierstrassCurve.kernelIdealSet κ X₁ W₂ χ₂ =
      star '' ((d₂ • Submodule.ofFiniteIdele Λ₁ x : Submodule ℤ ℍ[ℚ, a, b]) : Set ℍ[ℚ, a, b]))
    (J₂ : Submodule ℤ ℍ[ℚ, a, b])
    (W₂' : WeierstrassCurve κ) [W₂'.IsElliptic] (ψ₂ : W₂.toAffine.Point →+ W₂'.toAffine.Point)
    (hψ₂ : ψ₂ ∈ WeierstrassCurve.rationalHomSet κ W₂ W₂')
    (ψ₂' : W₂'.toAffine.Point →+ W₂.toAffine.Point) (hψ₂' : ψ₂' ∈ WeierstrassCurve.rationalHomSet κ W₂' W₂)
    (N₂ : ℕ) (hN₂ : ¬ q' ∣ N₂)
    (hψ₂d : ψ₂'.comp ψ₂ = (N₂ : ℕ) • AddMonoidHom.id _ ∧ ψ₂.comp ψ₂' = (N₂ : ℕ) • AddMonoidHom.id _)
    (hψ₂N : Nat.card ψ₂.ker = N₂)
    (hJ₂ : θ₁ '' WeierstrassCurve.kernelIdealSet κ X₁ W₂' (ψ₂.comp χ₂) =
      star '' ((d₂ • J₂ : Submodule ℤ ℍ[ℚ, a, b]) : Set ℍ[ℚ, a, b])) :
    (∃ δ : (ℍ[ℚ, a, b])ˣ,
        x⁻¹ * Submodule.finiteIdeleDiagonal ℍ[ℚ, a, b] δ * x ∈ Submodule.finiteIdeleStabilizer Λ₁ ∧ J₂ = δ • J₁) ↔
      ∃ ι ∈ WeierstrassCurve.rationalHomSet κ W₁ W₂, ∃ ι' ∈ WeierstrassCurve.rationalHomSet κ W₂ W₁,
        ι'.comp ι = AddMonoidHom.id _ ∧ ι.comp ι' = AddMonoidHom.id _ ∧ ψ₂.ker = ψ₁.ker.map ι := by
  classical
  have ha : a < 0 := hdef.neg_left
  have hb : b < 0 := hdef.neg_right
  have hN₁0 : N₁ ≠ 0 := fun h => hN₁ (h ▸ dvd_zero q')
  have hN₂0 : N₂ ≠ 0 := fun h => hN₂ (h ▸ dvd_zero q')
  have hN₁κ : (N₁ : κ) ≠ 0 := fun h => hN₁ ((CharP.cast_eq_zero_iff κ q' N₁).mp h)
  have hN₂κ : (N₂ : κ) ≠ 0 := fun h => hN₂ ((CharP.cast_eq_zero_iff κ q' N₂).mp h)
  have hfin₁ : Finite ↥(ψ₁.ker) := Nat.finite_of_card_ne_zero (by rw [hψ₁N]; exact hN₁0)
  have hfin₂ : Finite ↥(ψ₂.ker) := Nat.finite_of_card_ne_zero (by rw [hψ₂N]; exact hN₂0)
  have hψ₁0 : ψ₁ ≠ 0 := ne_zero_of_comp_eq_nsmul_id q' hN₁0 hψ₁d.1
  have hψ₂0 : ψ₂ ≠ 0 := ne_zero_of_comp_eq_nsmul_id q' hN₂0 hψ₂d.1

  have hstab : ∀ δ : (ℍ[ℚ, a, b])ˣ,
      x⁻¹ * Submodule.finiteIdeleDiagonal ℍ[ℚ, a, b] δ * x ∈ Submodule.finiteIdeleStabilizer Λ₁ ↔
        δ • Submodule.ofFiniteIdele Λ₁ x = Submodule.ofFiniteIdele Λ₁ x := by
    intro δ
    rw [← Submodule.ofFiniteIdele_diagonal_mul, eq_comm,
      Submodule.ofFiniteIdele_eq_ofFiniteIdele_iff Λ₁ hΛ₁.isOrder.fg hΛ₁.isOrder.spanTop, mul_assoc]
  constructor
  · rintro ⟨δ, hδ, hJ⟩
    have hI : δ • Submodule.ofFiniteIdele Λ₁ x = Submodule.ofFiniteIdele Λ₁ x := (hstab δ).mp hδ
    set c : (ℍ[ℚ, a, b])ˣ := star (d₂ * δ * d₁⁻¹) with hcdef
    have hcδ : d₂⁻¹ * star c * d₁ = δ := by rw [hcdef, star_star]; group
    have hc1 : θ₁ '' WeierstrassCurve.kernelIdealSet κ X₁ W₂ χ₂ =
        (· * (c : ℍ[ℚ, a, b])) '' (θ₁ '' WeierstrassCurve.kernelIdealSet κ X₁ W₁ χ₁) := by
      rw [hK₁, hK₂]
      exact (QuaternionAlgebra.star_image_smul_eq_mulRight_image_star_image_smul_iff _ _ d₁ d₂ c).mpr
        (by rw [hcδ, hI])
    have hc2 : θ₁ '' WeierstrassCurve.kernelIdealSet κ X₁ W₂' (ψ₂.comp χ₂) =
        (· * (c : ℍ[ℚ, a, b])) '' (θ₁ '' WeierstrassCurve.kernelIdealSet κ X₁ W₁' (ψ₁.comp χ₁)) := by
      rw [hJ₁, hJ₂]
      exact (QuaternionAlgebra.star_image_smul_eq_mulRight_image_star_image_smul_iff _ _ d₁ d₂ c).mpr
        (by rw [hcδ]; exact hJ)
    obtain ⟨φ, hφ, φ', hφ', hi1, hi2, -, hlev⟩ :=
      CerednikDrinfeld.exists_mem_rationalHomSet_comp_eq_id_forall_mem_ker_of_image_kernelIdealSet_eq_image_mul
        q' X₁ hss a b Λ₁ hΛ₁.isOrder θ₁ hθ₁ hθ₁Λ W₁ W₂ χ₁ hχ₁ hχ₁0 χ₂ hχ₂ hχ₂0 (c : ℍ[ℚ, a, b]) c.ne_zero hc1
        W₁' W₂' ψ₁ hψ₁ hψ₁0 ψ₂ hψ₂ hψ₂0 hc2
    obtain ⟨φ₂, hφ₂, φ₂', hφ₂', hj1, hj2, -, hlev₂⟩ :=
      CerednikDrinfeld.exists_mem_rationalHomSet_comp_eq_id_forall_mem_ker_of_image_kernelIdealSet_eq_image_mul
        q' X₁ hss a b Λ₁ hΛ₁.isOrder θ₁ hθ₁ hθ₁Λ W₂ W₁ χ₂ hχ₂ hχ₂0 χ₁ hχ₁ hχ₁0
        ((c⁻¹ : (ℍ[ℚ, a, b])ˣ) : ℍ[ℚ, a, b]) (c⁻¹).ne_zero (image_mulRight_inv c hc1)
        W₂' W₁' ψ₂ hψ₂ hψ₂0 ψ₁ hψ₁ hψ₁0 (image_mulRight_inv c hc2)
    have hφinj : Function.Injective φ := by
      intro P Q h
      have := congrArg φ' h
      rwa [show φ' (φ P) = P from DFunLike.congr_fun hi1 P, show φ' (φ Q) = Q from DFunLike.congr_fun hi1 Q] at this
    have hφ₂inj : Function.Injective φ₂ := by
      intro P Q h
      have := congrArg φ₂' h
      rwa [show φ₂' (φ₂ P) = P from DFunLike.congr_fun hj1 P, show φ₂' (φ₂ Q) = Q from DFunLike.congr_fun hj1 Q] at this
    refine ⟨φ, hφ, φ', hφ', hi1, hi2, ?_⟩
    have hle : ψ₁.ker.map φ ≤ ψ₂.ker := AddSubgroup.map_le_iff_le_comap.mpr (fun T hT => hlev T hT)
    have hle₂ : ψ₂.ker.map φ₂ ≤ ψ₁.ker := AddSubgroup.map_le_iff_le_comap.mpr (fun T hT => hlev₂ T hT)
    have hcard1 : Nat.card (ψ₁.ker.map φ) = Nat.card ψ₁.ker :=
      (Nat.card_congr (ψ₁.ker.equivMapOfInjective φ hφinj).toEquiv).symm
    have hcard2 : Nat.card ψ₂.ker ≤ Nat.card ψ₁.ker := by
      rw [Nat.card_congr (ψ₂.ker.equivMapOfInjective φ₂ hφ₂inj).toEquiv]
      exact @AddSubgroup.card_le_of_le _ _ _ _ hfin₁ hle₂
    exact (@AddSubgroup.eq_of_le_of_card_ge _ _ _ _ hfin₂ hle (hcard2.trans hcard1.symm.le)).symm
  · rintro ⟨ι, hι, ι', hι', hi1, hi2, hker⟩
    have hιinj : Function.Injective ι := by
      intro P Q h
      have := congrArg ι' h
      rwa [show ι' (ι P) = P from DFunLike.congr_fun hi1 P, show ι' (ι Q) = Q from DFunLike.congr_fun hi1 Q] at this
    have hN : N₂ = N₁ := by
      rw [← hψ₁N, ← hψ₂N, hker]
      exact (Nat.card_congr (ψ₁.ker.equivMapOfInjective ι hιinj).toEquiv).symm
    subst hN
    have hlev : ∀ T ∈ ψ₁.ker, ι T ∈ ψ₂.ker := fun T hT => by
      rw [hker]; exact AddSubgroup.mem_map_of_mem ι hT
    obtain ⟨c, hc1, hc2⟩ :=
      CerednikDrinfeld.exists_units_image_kernelIdealSet_pair_eq_image_mul_of_comp_eq_id_forall_mem_ker
        q' X₁ hss a b ha hb θ₁ hθ₁ W₁ W₂ W₁' W₂' χ₁ hχ₁ hχ₁0 χ₂ hχ₂ hχ₂0 N₂ hN₂0 hN₂κ
        ψ₁ hψ₁ ψ₁' hψ₁' hψ₁d.1 hψ₁d.2 hψ₁N ψ₂ hψ₂ ψ₂' hψ₂' hψ₂d.1 hψ₂d.2 hψ₂N ι hι ι' hι' hi1 hi2 hlev
    refine ⟨d₂⁻¹ * star c * d₁, (hstab _).mpr ?_, ?_⟩
    · symm
      exact (QuaternionAlgebra.star_image_smul_eq_mulRight_image_star_image_smul_iff _ _ d₁ d₂ c).mp
        (by rw [← hK₁, ← hK₂]; exact hc1)
    · exact (QuaternionAlgebra.star_image_smul_eq_mulRight_image_star_image_smul_iff _ _ d₁ d₂ c).mp
        (by rw [← hJ₁, ← hJ₂]; exact hc2)

end S_CerednikDrinfeld_exists_smul_eq_iff_exists_ker_eq_map_of_comp_eq_smul_id_of_card_ker_eq
end P2MW
export P2MW.S_CerednikDrinfeld_exists_smul_eq_iff_exists_ker_eq_map_of_comp_eq_smul_id_of_card_ker_eq (solution)
