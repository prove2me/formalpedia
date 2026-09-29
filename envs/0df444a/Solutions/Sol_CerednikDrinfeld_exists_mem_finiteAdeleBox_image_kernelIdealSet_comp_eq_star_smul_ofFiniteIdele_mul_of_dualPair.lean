-- Prove2me | solution 1 for CerednikDrinfeld.exists_mem_finiteAdeleBox_image_kernelIdealSet_comp_eq_star_smul_ofFiniteIdele_mul_of_dualPair
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.491319+00:00
-- url     : https://prove2.me/submissions/6a615290-c675-567d-ae67-a4ff7c13948a

import Mathlib
import Definitions.Def_QuaternionAlgebra_EichlerOrder
import Definitions.Def_WeierstrassCurve_RationalEnd
import Definitions.Def_WeierstrassCurve_KernelIdeal
import Definitions.Def_CerednikDrinfeld_ClassSetGraph
import Theorems.Thm_WeierstrassCurve_comp_mem_rationalHomSet
import Theorems.Thm_WeierstrassCurve_add_mem_rationalHomSet
import Theorems.Thm_WeierstrassCurve_neg_mem_rationalHomSet
import Theorems.Thm_WeierstrassCurve_surjective_of_mem_rationalHomSet
import Theorems.Thm_WeierstrassCurve_exists_isDualPair_of_mem_rationalHomSet
import Theorems.Thm_QuaternionAlgebra_IsOrder_exists_intCast_eq_nrd_and_exists_intCast_eq_trd
import Theorems.Thm_QuaternionAlgebra_IsMaximalOrder_exists_eq_ofFiniteIdele_of_forall_mul_mem
import Theorems.Thm_Submodule_finiteAdeleBox_ofFiniteIdele
import Theorems.Thm_CerednikDrinfeld_natCard_ker_sq_eq_relIndex_ofFiniteIdele_mul_of_image_kernelIdealSet_comp_eq
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_exists_mem_finiteAdeleBox_image_kernelIdealSet_comp_eq_star_smul_ofFiniteIdele_mul_of_dualPair
p2m_attr_erase "instance" "instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly AlgebraicCurve.instFundamentalIdentityOfSumRamificationInertia AlgebraicCurve.Place.instIsScalarTowerResidueFieldRestrictPushforward AlgebraicCurve.Place.instAlgebraResidueFieldRestrictPushforward AlgebraicCurve.Place.instIsLocalHomRestrictInclusion AlgebraicCurve.Place.instIsScalarTowerSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Divisor.instDistribMulActionAlgEquiv AlgebraicCurve.Place.instSMulAlgEquiv AlgebraicCurve.Place.instIsPrincipalIdealRingSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Place.instIsDiscreteValuationRingSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Pic0.instDistribMulActionAlgEquiv AlgebraicCurve.Place.instAlgebraSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Place.instMulActionAlgEquiv AlgebraicCurve.Pic0.instSMulAlgEquiv AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupDivisor AlgebraicCurve.Pic0.instModuleZModTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instDistribMulActionTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instSMulTorsion AlgebraicCurve.SemilinearAut.instMulActionSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instSMulCommClassZModTorsion AlgebraicCurve.SemilinearAut.instMulSemiringActionSubtypeProdRingAutMemSubgroup AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation"
p2m_attr_erase "instance" "AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy WeierstrassCurve.Affine.instIsScalarTowerPolynomialRatFuncFunctionField_definitions WeierstrassCurve.Affine.instAlgebraRatFuncFunctionField_definitions WeierstrassCurve.Affine.instIsScalarTowerRatFuncFunctionField_definitions WeierstrassCurve.Affine.CoordinateRing.moduleFinite WeierstrassCurve.Affine.instDecidableEqFunctionField WeierstrassCurve.Affine.CoordinateRing.isIntegral ModularCurve.SpecializationWitnessData.addCommGroup ModularCurve.CommutingHeckeFamily.commRing_adjoin ModularCurve.Gamma0Pair.isElliptic"
p2m_attr_erase "simp" "AddMonoid.End.dualEndDataOfSurjective_trace AddMonoid.End.dualEndDataOfSurjective_norm compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two WeierstrassCurve.Universal.halveX_zero WeierstrassCurve.Universal.specialize_X_one WeierstrassCurve.Universal.coeff_halve WeierstrassCurve.Universal.specialize_X_two WeierstrassCurve.Universal.halveCoeff_zero"
p2m_attr_erase "simp" "WeierstrassCurve.Universal.specialize_X_four WeierstrassCurve.Universal.coeff_halveX WeierstrassCurve.Universal.specialize_X_three WeierstrassCurve.Universal.specialize_X_zero QuaternionAlgebra.baseChangeRight_tmul QuaternionAlgebra.mapOfAlgebraMapEq_apply QuaternionAlgebra.baseChange_tmul WeierstrassCurve.Affine.Point.netCol_one WeierstrassCurve.Affine.Point.xOrZero_zero WeierstrassCurve.Affine.Point.netPairing_zero_right WeierstrassCurve.Affine.Point.netW20_some WeierstrassCurve.Affine.Point.netCol_zero WeierstrassCurve.Affine.Point.netPairing_zero_left WeierstrassCurve.Affine.Point.xOrZero_some WeierstrassCurve.Affine.Point.netW20_zero TateCurve.cauchyMulInt_zero TateCurve.cauchyMulInt3_zero TateCurve.tent_one TateCurve.Gz_zero TateCurve.cauchyMulInt_one TateCurve.tent_zero TateCurve.Fz_zero TateCurve.xCoeffFull_succ TateCurve.a₆Coeff_zero TateCurve.a₄Coeff_succ TateCurve.a₄Coeff_zero TateCurve.cauchyMul_zero TateCurve.a₆Coeff_succ TateCurve.yCoeffFull_succ TateCurve.xCoeffFull_zero TateCurve.yCoeffFull_zero TateCurve.yfun_zero TateCurve.xfun_zero TateCurve.yTerm_zero TateCurve.xTerm_zero TateCurve.curve_a₂ TateCurve.b_one TateCurve.curve_a₁ TateCurve.term_zero TateCurve.curve_a₆"
p2m_attr_erase "simp" "TateCurve.curve_a₄ TateCurve.curve_a₃ FLT.DivisorConvolution.sigma_zero_right FLT.DivisorConvolution.sigma_one_right FLT.DivisorConvolution.sigmaConv_one FLT.DivisorConvolution.sigmaConv_zero WeierstrassCurve.veluWSum_empty WeierstrassCurve.veluQuotient_a₁ WeierstrassCurve.veluQuotient_a₃ WeierstrassCurve.veluQuotient_empty WeierstrassCurve.veluTSum_empty WeierstrassCurve.veluQuotient_a₂ WeierstrassCurve.veluX_empty WeierstrassCurve.veluY_empty WeierstrassCurve.Affine.Point.coordsOrZero_some WeierstrassCurve.Affine.Point.coordsOrZero_zero WeierstrassCurve.Affine.IsogenyEndDatum.mk.injEq WeierstrassCurve.Affine.IsogenyHomDatum.mk.sizeOf_spec WeierstrassCurve.Affine.IsogenyHomDatum.mk.injEq WeierstrassCurve.Affine.IsogenyEndDatum.mk.sizeOf_spec AlgebraicCurve.Pic0.coe_pushforwardAlongDegZero WeierstrassCurve.Affine.pointMapOfPushforward_apply AlgebraicCurve.Divisor.degree_pushforwardAlong AlgebraicCurve.Pic0.coe_degZeroCorrespondence AlgebraicCurve.Place.mem_fiberAlong AlgebraicCurve.Divisor.mapRestrict_single AlgebraicCurve.Divisor.pushforward_single AlgebraicCurve.Place.coe_restrictInclusion AlgebraicCurve.Place.mem_fiber AlgebraicCurve.Place.restrict_toValuationSubring AlgebraicCurve.Divisor.degree_pushforward AlgebraicCurve.Place.restrictResidueMap_residue AlgebraicCurve.Pic0.coe_pushforwardDegZeroHom AlgebraicCurve.Pic0.coe_pullbackDegZeroHom AlgebraicCurve.Place.mk.injEq AlgebraicCurve.Divisor.degree_single AlgebraicCurve.Divisor.smul_single AlgebraicCurve.Place.smul_toValuationSubring AlgebraicCurve.Place.heightOneSpectrum_asIdeal AlgebraicCurve.Place.coe_algebraMap"
p2m_attr_erase "simp" "AlgebraicCurve.Place.ord_one AlgebraicCurve.Place.coe_smulRingEquiv_apply AlgebraicCurve.Pic0.coe_degZeroSMulHom AlgebraicCurve.Place.deg_smul AlgebraicCurve.Pic0.mk_zero AlgebraicCurve.Place.mk.sizeOf_spec AlgebraicCurve.Divisor.degree_smul AlgebraicCurve.Pic0.mk_add AlgebraicCurve.Place.ord_zero AlgebraicCurve.Place.ofHeightOneSpectrum_toValuationSubring AlgebraicCurve.SemilinearAut.toRingAut_inv AlgebraicCurve.SemilinearAut.smul_def AlgebraicCurve.SemilinearAut.smul_single AlgebraicCurve.SemilinearAut.smul_toValuationSubring AlgebraicCurve.SemilinearAut.baseAut_inv AlgebraicCurve.SemilinearAut.baseAut_ofAlgAut AlgebraicCurve.SemilinearAut.toRingAut_ofAlgAut AlgebraicCurve.SemilinearAut.torsionRep_apply AlgebraicCurve.SemilinearAut.toRingAut_one AlgebraicCurve.SemilinearAut.deg_smul AlgebraicCurve.SemilinearAut.degree_smul AlgebraicCurve.SemilinearAut.coe_degZeroSMulHom AlgebraicCurve.SemilinearAut.baseAut_mul AlgebraicCurve.SemilinearAut.coe_smulValuationSubringEquiv_apply AlgebraicCurve.SemilinearAut.baseAut_one AlgebraicCurve.SemilinearAut.ofAlgAut_smul AlgebraicCurve.SemilinearAut.coe_torsion_smul AlgebraicCurve.SemilinearAut.toRingAut_mul WeierstrassCurve.Affine.pointClass_zero WeierstrassCurve.Affine.pic0ToPoint_pointClass WeierstrassCurve.Affine.deg_placeOfPoint WeierstrassCurve.Affine.coe_pointDivisor WeierstrassCurve.Affine.pointEquivPlace_symm_placeOfPoint WeierstrassCurve.Affine.pointEquivPlace_apply WeierstrassCurve.Affine.genusOnePic0Equiv_symm_apply WeierstrassCurve.Affine.pointDivisor_zero WeierstrassCurve.Affine.pic0ToPoint_mk WeierstrassCurve.Affine.divisorSum_single WeierstrassCurve.Affine.genusOnePic0Equiv_apply AlgebraicCurve.Place.placeOfPrime_toValuationSubring"
p2m_attr_erase "simp" "AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.jqNModC_one ModularCurve.qExpand_coeff_mul ModularCurve.qExpandₐ_apply ModularCurve.jqN_one ModularCurve.qExpand_single ModularCurve.dedekindPsi_one ModularCurve.ModularPolynomialData.mk.sizeOf_spec ModularCurve.evalAtJ_X ModularCurve.ModularPolynomialData.mk.injEq ModularCurve.constantCoeff_jNum ModularCurve.constantCoeff_eisenstein4 ModularCurve.qExpand_C ModularCurve.coeff_jq_neg_one"
p2m_attr_erase "simp" "ModularCurve.constantCoeff_jNumQ ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd FreyPackage.mk.sizeOf_spec FreyPackage.mk.injEq WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply WeierstrassCurve.vcInvEmbedding_apply WeierstrassCurve.Affine.vcY_vcYInv WeierstrassCurve.Affine.vcXInv_vcX WeierstrassCurve.Affine.Point.vcFun_zero WeierstrassCurve.Affine.vcX_vcXInv WeierstrassCurve.Affine.vcYInv_vcY WeierstrassCurve.Affine.Point.vcInvFun_zero WeierstrassCurve.map_veluU WeierstrassCurve.map_veluT WeierstrassCurve.map_veluW WeierstrassCurve.map_veluGy WeierstrassCurve.map_veluGx WeierstrassCurve.map_veluWSum_singleton WeierstrassCurve.map_veluTSum_singleton WeierstrassCurve.veluPointMap3_zero WeierstrassCurve.Affine.ratFuncToFunctionField_algebraMap AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one WeierstrassCurve.Affine.pointHom_mk_C_C WeierstrassCurve.Affine.Point.yc_some WeierstrassCurve.Affine.Point.xc_some WeierstrassCurve.Affine.pointPull_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_X WeierstrassCurve.Affine.pointHom_mk_Y WeierstrassCurve.Affine.placeOf_asIdeal"
p2m_attr_erase "simp" "ModularCurve.coe_levelAlphaC ModularCurve.SSLevelDatum.mk.sizeOf_spec ModularCurve.SSLevelDatum.mk.injEq ModularCurve.coe_levelBetaC ModularCurve.coe_heckeBetaC AlgebraicCurve.Divisor.coe_degZeroEnd ModularCurve.coe_heckeAlphaC ModularCurve.CommutingHeckeFamily.mk.injEq ModularCurve.SpecializationWitnessData.mk.sizeOf_spec ModularCurve.SpecializationWitnessData.mk.injEq ModularCurve.CommutingHeckeFamily.mk.sizeOf_spec ModularCurve.coe_nodeEquivOfPlaces_apply ModularCurve.widthOfPlaces_mk ModularCurve.smulNodePairEmb_apply ModularCurve.card_nodePairsOfPlaces ModularCurve.smulNodePair_snd ModularCurve.smulNodePair_fst ModularCurve.coe_nodeEquivOfPlaces_symm_apply ModularCurve.coe_jGeomGen ModularCurve.coe_jNGeomGen ModularCurve.coe_uniformizerMod ModularCurve.qSeriesBar_jModElt ModularCurve.qInftyPlaceMod_toValuationSubring ModularCurve.qInftyPlaceBar_toValuationSubring ModularCurve.qSeriesBar_zero ModularCurve.qSeriesBar_add ModularCurve.cuspInftyFull_toValuationSubring ModularCurve.qInftyPlaceRat_toValuationSubring ModularCurve.qSeriesBar_mul ModularCurve.qSeriesBar_div ModularCurve.qSeriesBar_eq_zero_iff ModularCurve.coe_uniformizerBar ModularCurve.qSeriesBar_pow ModularCurve.cuspInfty_toValuationSubring ModularCurve.qSeriesBar_one ModularCurve.qSeriesBar_inv ModularCurve.qSeriesBar_sub ModularCurve.qSeriesBar_neg ModularCurve.charLGeomModuliDictionary_single ModularCurve.specializeModuli_single"
p2m_attr_erase "simp" "ModularCurve.specializePlace_def ModularCurve.gamma0PairMap_gen ModularCurve.moduliPointMapRingHom_mk ModularCurve.Gamma0Pair.mk.injEq ModularCurve.ModuliPoint.j_mk ModularCurve.Gamma0Pair.mk.sizeOf_spec ModularCurve.gamma0PairMap_toCurve WeierstrassCurve.ratPointHom_apply WeierstrassCurve.ratPointMap_zero"

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

open scoped Quaternion TensorProduct NumberField Pointwise
p2m_open "QuaternionAlgebra~baseChange CerednikDrinfeld P2MW.S_CerednikDrinfeld_exists_mem_finiteAdeleBox_image_kernelIdealSet_comp_eq_star_smul_ofFiniteIdele_mul_of_dualPair.CerednikDrinfeld IsDedekindDomain"

noncomputable section

namespace CerednikDrinfeld
p2m_export "CerednikDrinfeld" "natCard_ker_sq_eq_relIndex_ofFiniteIdele_mul_of_image_kernelIdealSet_comp_eq"
namespace KernelIdealTransport
p2m_open "CerednikDrinfeld"

section Points

open Polynomial WeierstrassCurve

variable {F : Type*} [Field F] {k : Type*} [Field k] [Algebra F k]

abbrev Pt (k : Type*) [Field k] [Algebra F k] (W : WeierstrassCurve F) :=
  (W.baseChange k).toAffine.Point

variable [DecidableEq k]
variable {W₁ W₂ : WeierstrassCurve F}

theorem sub_mem_rationalHomSet [IsAlgClosed k] [W₁.IsElliptic] [W₂.IsElliptic]
    {α β : Pt k W₁ →+ Pt k W₂} (hα : α ∈ rationalHomSet k W₁ W₂)
    (hβ : β ∈ rationalHomSet k W₁ W₂) : α - β ∈ rationalHomSet k W₁ W₂ := by
  rw [sub_eq_add_neg]
  exact add_mem_rationalHomSet k W₁ W₂ hα (neg_mem_rationalHomSet k W₁ W₂ hβ)

theorem zsmul_mem_rationalHomSet [IsAlgClosed k] [W₁.IsElliptic] [W₂.IsElliptic]
    {α : Pt k W₁ →+ Pt k W₂} (hα : α ∈ rationalHomSet k W₁ W₂) (c : ℤ) :
    c • α ∈ rationalHomSet k W₁ W₂ := by
  induction c using Int.induction_on with
  | zero => rw [zero_zsmul]; exact zero_mem_rationalHomSet k W₁ W₂
  | succ n ih => rw [add_zsmul, one_zsmul]; exact add_mem_rationalHomSet k W₁ W₂ ih hα
  | pred n ih => rw [sub_zsmul, one_zsmul]; exact sub_mem_rationalHomSet ih hα

theorem nsmul_mem_rationalHomSet [IsAlgClosed k] [W₁.IsElliptic] [W₂.IsElliptic]
    {α : Pt k W₁ →+ Pt k W₂} (hα : α ∈ rationalHomSet k W₁ W₂) (c : ℕ) :
    c • α ∈ rationalHomSet k W₁ W₂ := by
  rw [← natCast_zsmul]; exact zsmul_mem_rationalHomSet hα c

end Points

section Quaternion

variable {a b : ℚ}

theorem star_mem_of_mem {Λ : Submodule ℤ ℍ[ℚ, a, b]} (hΛ : IsOrder Λ) {h : ℍ[ℚ, a, b]} (hh : h ∈ Λ) :
    star h ∈ Λ := by
  obtain ⟨-, t, ht⟩ := hΛ.exists_intCast_eq_nrd_and_exists_intCast_eq_trd hh
  have e : star h = ((trd h : ℚ) : ℍ[ℚ, a, b]) - h := by
    rw [← add_star_eq_coe_trd]; abel
  have e2 : ((trd h : ℚ) : ℍ[ℚ, a, b]) = t • (1 : ℍ[ℚ, a, b]) := by
    rw [← ht, coe_intCast, zsmul_eq_mul, mul_one]
  rw [e, e2]
  exact Λ.sub_mem (Λ.smul_mem t hΛ.one_mem) hh

theorem coe_units_smul (e : (ℍ[ℚ, a, b])ˣ) (I : Submodule ℤ ℍ[ℚ, a, b]) :
    ((e • I : Submodule ℤ ℍ[ℚ, a, b]) : Set ℍ[ℚ, a, b]) = (fun z => (e : ℍ[ℚ, a, b]) * z) '' (I : Set ℍ[ℚ, a, b]) := by
  ext z
  erw [Submodule.mem_smul_pointwise_iff_exists]

theorem mem_units_smul_iff (e : (ℍ[ℚ, a, b])ˣ) (I : Submodule ℤ ℍ[ℚ, a, b]) (z : ℍ[ℚ, a, b]) :
    z ∈ (e • I : Submodule ℤ ℍ[ℚ, a, b]) ↔ ((e⁻¹ : (ℍ[ℚ, a, b])ˣ) : ℍ[ℚ, a, b]) * z ∈ I := by
  rw [← SetLike.mem_coe, coe_units_smul, Set.mem_image]
  constructor
  · rintro ⟨w, hw, rfl⟩
    rwa [← mul_assoc, Units.inv_mul, one_mul]
  · intro h
    exact ⟨_, h, by rw [← mul_assoc, Units.mul_inv, one_mul]⟩

end Quaternion

section Adelic

variable {a b : ℚ}

theorem mul_mem_finiteAdeleBox {Λ : Submodule ℤ ℍ[ℚ, a, b]} (hΛ : IsOrder Λ)
    {x y : ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ}
    (hx : x ∈ Submodule.finiteAdeleBox Λ) (hy : y ∈ Submodule.finiteAdeleBox Λ) :
    x * y ∈ Submodule.finiteAdeleBox Λ := by
  induction hy using AddSubgroup.closure_induction with
  | mem y hy =>
    obtain ⟨z, hz, c, hc, rfl⟩ := hy
    induction hx using AddSubgroup.closure_induction with
    | mem x hx =>
      obtain ⟨z', hz', c', hc', rfl⟩ := hx
      refine AddSubgroup.subset_closure ⟨z' * z, hΛ.mul_mem hz' hz, c' * c, fun v => ?_, ?_⟩
      · exact mul_mem (hc' v) (hc v)
      · rw [Algebra.TensorProduct.tmul_mul_tmul]
    | zero => rw [zero_mul]; exact zero_mem _
    | add u w _ _ hu hw => rw [add_mul]; exact add_mem hu hw
    | neg u _ hu =>
      convert neg_mem hu using 1
      exact neg_mul u _
  | zero => rw [mul_zero]; exact zero_mem _
  | add u w _ _ hu hw => rw [mul_add]; exact add_mem hu hw
  | neg u _ hu =>
    convert neg_mem hu using 1
    exact mul_neg x u

theorem tmul_one_mem_finiteAdeleBox {Λ : Submodule ℤ ℍ[ℚ, a, b]} {z : ℍ[ℚ, a, b]} (hz : z ∈ Λ) :
    z ⊗ₜ[ℚ] (1 : FiniteAdeleRing (𝓞 ℚ) ℚ) ∈ Submodule.finiteAdeleBox Λ :=
  AddSubgroup.subset_closure ⟨z, hz, 1, fun v => one_mem _, rfl⟩

theorem mul_mem_ofFiniteIdele {Λ : Submodule ℤ ℍ[ℚ, a, b]} (hΛ : IsOrder Λ)
    (g : (ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) {z μ : ℍ[ℚ, a, b]}
    (hz : z ∈ Submodule.ofFiniteIdele Λ g) (hμ : μ ∈ Λ) : z * μ ∈ Submodule.ofFiniteIdele Λ g := by
  rw [Submodule.mem_ofFiniteIdele_iff, AddSubgroup.mem_map] at hz ⊢
  obtain ⟨w, hw, hwz⟩ := hz
  refine ⟨w * μ ⊗ₜ[ℚ] (1 : FiniteAdeleRing (𝓞 ℚ) ℚ), mul_mem_finiteAdeleBox hΛ hw (tmul_one_mem_finiteAdeleBox hμ), ?_⟩
  rw [AddMonoidHom.coe_mulLeft] at hwz ⊢
  rw [← mul_assoc, hwz, Algebra.TensorProduct.tmul_mul_tmul, mul_one]

theorem ofFiniteIdele_mul_le_of_mem {Λ : Submodule ℤ ℍ[ℚ, a, b]} (hΛ : IsOrder Λ)
    (x g : (ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ)
    (hg : ((g : (ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) : ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ) ∈
      Submodule.finiteAdeleBox Λ) :
    Submodule.ofFiniteIdele Λ (x * g) ≤ Submodule.ofFiniteIdele Λ x := by
  intro z hz
  rw [Submodule.mem_ofFiniteIdele_iff, AddSubgroup.mem_map] at hz ⊢
  obtain ⟨w, hw, hwz⟩ := hz
  refine ⟨(g : ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ) * w, mul_mem_finiteAdeleBox hΛ hg hw, ?_⟩
  rw [AddMonoidHom.coe_mulLeft] at hwz ⊢
  rw [← mul_assoc]
  exact hwz

end Adelic

section Frame

open WeierstrassCurve

variable {κ : Type} [Field κ] [IsAlgClosed κ] [DecidableEq κ]
variable {a b : ℚ}

def homGrp (W X₀ : WeierstrassCurve κ) [W.IsElliptic] [X₀.IsElliptic] : AddSubgroup (Pt κ W →+ Pt κ X₀) where
  carrier := rationalHomSet κ W X₀
  zero_mem' := zero_mem_rationalHomSet κ W X₀
  add_mem' ha hb := add_mem_rationalHomSet κ W X₀ ha hb
  neg_mem' ha := neg_mem_rationalHomSet κ W X₀ ha

variable {X₀ W : WeierstrassCurve κ} [X₀.IsElliptic] [W.IsElliptic]

theorem mem_homGrp {ρ : Pt κ W →+ Pt κ X₀} : ρ ∈ homGrp W X₀ ↔ ρ ∈ rationalHomSet κ W X₀ := Iff.rfl

theorem closure_rationalHomSet : AddSubgroup.closure (rationalHomSet κ W X₀) = homGrp W X₀ :=
  le_antisymm ((AddSubgroup.closure_le _).mpr fun _ h => h) fun _ h => AddSubgroup.subset_closure h

structure IsLatticeFrame (Λ : Submodule ℤ ℍ[ℚ, a, b])
    (θ : ↥(rationalEndSubring κ X₀) →+* ℍ[ℚ, a, b]) (χ : Pt κ X₀ →+ Pt κ W) (d : (ℍ[ℚ, a, b])ˣ)
    (J₀ : Submodule ℤ ℍ[ℚ, a, b]) : Prop where
  isOrder : IsOrder Λ
  inj : Function.Injective θ
  range_eq : Set.range θ = (Λ : Set ℍ[ℚ, a, b])
  mem : χ ∈ rationalHomSet κ X₀ W
  ne_zero : χ ≠ 0
  ker_eq : θ '' (kernelIdealSet κ X₀ W χ) = star '' ((d • J₀ : Submodule ℤ ℍ[ℚ, a, b]) : Set ℍ[ℚ, a, b])

def compEnd {χ : Pt κ X₀ →+ Pt κ W} (hχ : χ ∈ rationalHomSet κ X₀ W) (ρ : homGrp W X₀) :
    ↥(rationalEndSubring κ X₀) :=
  ⟨(ρ.1).comp χ, Subring.subset_closure (comp_mem_rationalHomSet κ X₀ W X₀ hχ ρ.2)⟩

@[scoped simp] theorem coe_compEnd {χ : Pt κ X₀ →+ Pt κ W} (hχ : χ ∈ rationalHomSet κ X₀ W) (ρ : homGrp W X₀) :
    ((compEnd hχ ρ : ↥(rationalEndSubring κ X₀)) : AddMonoid.End (Pt κ X₀)) = (ρ.1).comp χ := rfl

theorem compEnd_mem_kernelIdealSet {χ : Pt κ X₀ →+ Pt κ W} (hχ : χ ∈ rationalHomSet κ X₀ W) (ρ : homGrp W X₀) :
    compEnd hχ ρ ∈ kernelIdealSet κ X₀ W χ := ⟨ρ.1, ρ.2, rfl⟩

def tr (θ : ↥(rationalEndSubring κ X₀) →+* ℍ[ℚ, a, b]) {χ : Pt κ X₀ →+ Pt κ W} (hχ : χ ∈ rationalHomSet κ X₀ W)
    (d : (ℍ[ℚ, a, b])ˣ) : homGrp W X₀ →+ ℍ[ℚ, a, b] where
  toFun ρ := ((d⁻¹ : (ℍ[ℚ, a, b])ˣ) : ℍ[ℚ, a, b]) * star (θ (compEnd hχ ρ))
  map_zero' := by
    have : compEnd hχ (0 : homGrp W X₀) = 0 := Subtype.ext (by ext P; rfl)
    rw [this, map_zero, star_zero, mul_zero]
  map_add' ρ ρ' := by
    have : compEnd hχ (ρ + ρ') = compEnd hχ ρ + compEnd hχ ρ' := Subtype.ext (by ext P; rfl)
    rw [this, map_add, star_add, mul_add]

theorem tr_apply (θ : ↥(rationalEndSubring κ X₀) →+* ℍ[ℚ, a, b]) {χ : Pt κ X₀ →+ Pt κ W} (hχ : χ ∈ rationalHomSet κ X₀ W)
    (d : (ℍ[ℚ, a, b])ˣ) (ρ : homGrp W X₀) :
    tr θ hχ d ρ = ((d⁻¹ : (ℍ[ℚ, a, b])ˣ) : ℍ[ℚ, a, b]) * star (θ (compEnd hχ ρ)) := rfl

theorem theta_compEnd_eq (θ : ↥(rationalEndSubring κ X₀) →+* ℍ[ℚ, a, b]) {χ : Pt κ X₀ →+ Pt κ W}
    (hχ : χ ∈ rationalHomSet κ X₀ W) (d : (ℍ[ℚ, a, b])ˣ) (ρ : homGrp W X₀) :
    θ (compEnd hχ ρ) = star ((d : ℍ[ℚ, a, b]) * tr θ hχ d ρ) := by
  rw [tr_apply, ← mul_assoc, Units.mul_inv, one_mul, star_star]

variable {Λ : Submodule ℤ ℍ[ℚ, a, b]} {θ : ↥(rationalEndSubring κ X₀) →+* ℍ[ℚ, a, b]} {χ : Pt κ X₀ →+ Pt κ W}
  {d : (ℍ[ℚ, a, b])ˣ} {J₀ : Submodule ℤ ℍ[ℚ, a, b]}

theorem IsLatticeFrame.compEnd_injective (hF : IsLatticeFrame Λ θ χ d J₀) : Function.Injective (compEnd hF.mem) := by
  intro ρ ρ' h
  have h2 := congrArg (fun e : ↥(rationalEndSubring κ X₀) => (e : AddMonoid.End (Pt κ X₀))) h
  simp only [coe_compEnd] at h2
  apply Subtype.ext
  ext Q
  obtain ⟨P, rfl⟩ := WeierstrassCurve.surjective_of_mem_rationalHomSet κ hF.mem hF.ne_zero Q
  exact DFunLike.congr_fun h2 P

theorem IsLatticeFrame.tr_injective (hF : IsLatticeFrame Λ θ χ d J₀) : Function.Injective (tr θ hF.mem d) := by
  intro ρ ρ' h
  rw [tr_apply, tr_apply] at h
  have h1 := star_injective ((Units.mul_right_inj _).mp h)
  exact hF.compEnd_injective (hF.inj h1)

theorem IsLatticeFrame.range_tr (hF : IsLatticeFrame Λ θ χ d J₀) :
    Set.range (tr θ hF.mem d) = (J₀ : Set ℍ[ℚ, a, b]) := by
  ext z
  constructor
  · rintro ⟨ρ, rfl⟩
    have h1 : θ (compEnd hF.mem ρ) ∈ θ '' (kernelIdealSet κ X₀ W χ) := ⟨_, compEnd_mem_kernelIdealSet hF.mem ρ, rfl⟩
    rw [hF.ker_eq] at h1
    obtain ⟨w, hw, hw'⟩ := h1
    rw [SetLike.mem_coe, mem_units_smul_iff] at hw
    rw [SetLike.mem_coe, tr_apply, ← hw', star_star]
    exact hw
  · intro hz
    have h1 : star ((d : ℍ[ℚ, a, b]) * z) ∈ θ '' (kernelIdealSet κ X₀ W χ) := by
      rw [hF.ker_eq]
      refine ⟨(d : ℍ[ℚ, a, b]) * z, ?_, rfl⟩
      rw [SetLike.mem_coe, mem_units_smul_iff, ← mul_assoc, Units.inv_mul, one_mul]
      exact hz
    obtain ⟨e, ⟨ρ, hρ, he⟩, he'⟩ := h1
    refine ⟨⟨ρ, hρ⟩, ?_⟩
    have : compEnd hF.mem ⟨ρ, hρ⟩ = e := Subtype.ext (by rw [coe_compEnd, he])
    rw [tr_apply, this, he', star_star, ← mul_assoc, Units.inv_mul, one_mul]

theorem IsLatticeFrame.tr_mem (hF : IsLatticeFrame Λ θ χ d J₀) (ρ : homGrp W X₀) :
    tr θ hF.mem d ρ ∈ J₀ := by
  rw [← SetLike.mem_coe, ← hF.range_tr]; exact ⟨ρ, rfl⟩

theorem IsLatticeFrame.exists_tr_eq (hF : IsLatticeFrame Λ θ χ d J₀) {z : ℍ[ℚ, a, b]} (hz : z ∈ J₀) :
    ∃ ρ : homGrp W X₀, tr θ hF.mem d ρ = z := by
  have : z ∈ Set.range (tr θ hF.mem d) := by rw [hF.range_tr]; exact hz
  exact this

theorem tr_comp {χ : Pt κ X₀ →+ Pt κ W} (hχ : χ ∈ rationalHomSet κ X₀ W) (θ : ↥(rationalEndSubring κ X₀) →+* ℍ[ℚ, a, b])
    (d : (ℍ[ℚ, a, b])ˣ) (α : ↥(rationalEndSubring κ X₀)) (ρ : homGrp W X₀)
    (hαρ : ((α : AddMonoid.End (Pt κ X₀)) : Pt κ X₀ →+ Pt κ X₀).comp ρ.1 ∈ rationalHomSet κ W X₀) :
    tr θ hχ d ⟨((α : AddMonoid.End (Pt κ X₀)) : Pt κ X₀ →+ Pt κ X₀).comp ρ.1, hαρ⟩ = tr θ hχ d ρ * star (θ α) := by
  have : compEnd hχ ⟨((α : AddMonoid.End (Pt κ X₀)) : Pt κ X₀ →+ Pt κ X₀).comp ρ.1, hαρ⟩ = α * compEnd hχ ρ :=
    Subtype.ext (by ext P; rfl)
  rw [tr_apply, tr_apply, this, map_mul, star_mul, mul_assoc]

end Frame

section EndComp

open WeierstrassCurve

variable {κ : Type} [Field κ] [IsAlgClosed κ] [DecidableEq κ]
variable {X₀ V : WeierstrassCurve κ} [X₀.IsElliptic] [V.IsElliptic]

theorem comp_mem_rationalHomSet_of_mem_rationalEndSubring
    {α : AddMonoid.End (Pt κ X₀)} (hα : α ∈ rationalEndSubring κ X₀) :
    ∀ ρ : Pt κ V →+ Pt κ X₀, ρ ∈ rationalHomSet κ V X₀ →
      (α : Pt κ X₀ →+ Pt κ X₀).comp ρ ∈ rationalHomSet κ V X₀ := by
  unfold rationalEndSubring at hα
  induction hα using Subring.closure_induction with
  | mem β hβ =>
    intro ρ hρ
    exact comp_mem_rationalHomSet κ V X₀ X₀ hρ hβ
  | zero =>
    intro ρ hρ
    have : ((0 : AddMonoid.End (Pt κ X₀)) : Pt κ X₀ →+ Pt κ X₀).comp ρ = 0 := by ext P; rfl
    rw [this]
    exact zero_mem_rationalHomSet κ V X₀
  | one =>
    intro ρ hρ
    have : ((1 : AddMonoid.End (Pt κ X₀)) : Pt κ X₀ →+ Pt κ X₀).comp ρ = ρ := by ext P; rfl
    rw [this]
    exact hρ
  | add β γ _ _ hβ hγ =>
    intro ρ hρ
    have : ((β + γ : AddMonoid.End (Pt κ X₀)) : Pt κ X₀ →+ Pt κ X₀).comp ρ =
        (β : Pt κ X₀ →+ Pt κ X₀).comp ρ + (γ : Pt κ X₀ →+ Pt κ X₀).comp ρ := by ext P; rfl
    rw [this]
    exact add_mem_rationalHomSet κ V X₀ (hβ ρ hρ) (hγ ρ hρ)
  | neg β _ hβ =>
    intro ρ hρ
    have : ((-β : AddMonoid.End (Pt κ X₀)) : Pt κ X₀ →+ Pt κ X₀).comp ρ = -((β : Pt κ X₀ →+ Pt κ X₀).comp ρ) := by
      ext P; rfl
    rw [this]
    exact neg_mem_rationalHomSet κ V X₀ (hβ ρ hρ)
  | mul β γ _ _ hβ hγ =>
    intro ρ hρ
    have : ((β * γ : AddMonoid.End (Pt κ X₀)) : Pt κ X₀ →+ Pt κ X₀).comp ρ =
        (β : Pt κ X₀ →+ Pt κ X₀).comp ((γ : Pt κ X₀ →+ Pt κ X₀).comp ρ) := by ext P; rfl
    rw [this]
    exact hβ _ (hγ ρ hρ)

end EndComp

section Lattice

open WeierstrassCurve

variable {κ : Type} [Field κ] [IsAlgClosed κ] [DecidableEq κ]
variable {a b : ℚ}
variable {X₀ W W' : WeierstrassCurve κ} [X₀.IsElliptic] [W.IsElliptic] [W'.IsElliptic]

def precomp (X₀ : WeierstrassCurve κ) (ψ : Pt κ W →+ Pt κ W') : (Pt κ W' →+ Pt κ X₀) →+ (Pt κ W →+ Pt κ X₀) where
  toFun ρ' := ρ'.comp ψ
  map_zero' := AddMonoidHom.zero_comp ψ
  map_add' ρ₁ ρ₂ := AddMonoidHom.add_comp ρ₁ ρ₂ ψ

@[scoped simp] theorem precomp_apply (ψ : Pt κ W →+ Pt κ W') (ρ' : Pt κ W' →+ Pt κ X₀) : precomp X₀ ψ ρ' = ρ'.comp ψ := rfl

def pulled (X₀ : WeierstrassCurve κ) [X₀.IsElliptic] (ψ : Pt κ W →+ Pt κ W') : AddSubgroup (homGrp W X₀) :=
  ((homGrp W' X₀).map (precomp X₀ ψ)).comap (homGrp W X₀).subtype

theorem mem_pulled_iff (ψ : Pt κ W →+ Pt κ W') (ρ : homGrp W X₀) :
    ρ ∈ pulled X₀ ψ ↔ ∃ ρ' ∈ rationalHomSet κ W' X₀, ρ'.comp ψ = ρ.1 := by
  unfold pulled
  rw [AddSubgroup.mem_comap, AddSubgroup.mem_map]
  rfl

def latOf (θ : ↥(rationalEndSubring κ X₀) →+* ℍ[ℚ, a, b]) {χ : Pt κ X₀ →+ Pt κ W} (hχ : χ ∈ rationalHomSet κ X₀ W)
    (d : (ℍ[ℚ, a, b])ˣ) (ψ : Pt κ W →+ Pt κ W') : Submodule ℤ ℍ[ℚ, a, b] :=
  { ((pulled X₀ ψ).map (tr θ hχ d)).toAddSubmonoid with
    smul_mem' := fun c _ hz => ((pulled X₀ ψ).map (tr θ hχ d)).zsmul_mem hz c }

theorem mem_latOf_iff (θ : ↥(rationalEndSubring κ X₀) →+* ℍ[ℚ, a, b]) {χ : Pt κ X₀ →+ Pt κ W} (hχ : χ ∈ rationalHomSet κ X₀ W)
    (d : (ℍ[ℚ, a, b])ˣ) {ψ : Pt κ W →+ Pt κ W'} (hψ : ψ ∈ rationalHomSet κ W W') (z : ℍ[ℚ, a, b]) :
    z ∈ latOf θ hχ d ψ ↔ ∃ (ρ' : Pt κ W' →+ Pt κ X₀) (hρ' : ρ' ∈ rationalHomSet κ W' X₀),
      tr θ hχ d ⟨ρ'.comp ψ, comp_mem_rationalHomSet κ W W' X₀ hψ hρ'⟩ = z := by
  change z ∈ (pulled X₀ ψ).map (tr θ hχ d) ↔ _
  rw [AddSubgroup.mem_map]
  constructor
  · rintro ⟨ρ, hρ, rfl⟩
    obtain ⟨ρ', hρ', hρeq⟩ := (mem_pulled_iff ψ ρ).mp hρ
    refine ⟨ρ', hρ', ?_⟩
    congr 1
    exact Subtype.ext hρeq
  · rintro ⟨ρ', hρ', rfl⟩
    exact ⟨⟨ρ'.comp ψ, comp_mem_rationalHomSet κ W W' X₀ hψ hρ'⟩, (mem_pulled_iff ψ _).mpr ⟨ρ', hρ', rfl⟩, rfl⟩

variable {Λ : Submodule ℤ ℍ[ℚ, a, b]} {θ : ↥(rationalEndSubring κ X₀) →+* ℍ[ℚ, a, b]} {χ : Pt κ X₀ →+ Pt κ W}
  {d : (ℍ[ℚ, a, b])ˣ} {J₀ : Submodule ℤ ℍ[ℚ, a, b]}

theorem IsLatticeFrame.latOf_le (hF : IsLatticeFrame Λ θ χ d J₀) {ψ : Pt κ W →+ Pt κ W'} (hψ : ψ ∈ rationalHomSet κ W W') :
    latOf θ hF.mem d ψ ≤ J₀ := by
  intro z hz
  obtain ⟨ρ', hρ', rfl⟩ := (mem_latOf_iff θ hF.mem d hψ z).mp hz
  exact hF.tr_mem _

theorem IsLatticeFrame.mul_mem_latOf (hF : IsLatticeFrame Λ θ χ d J₀) {ψ : Pt κ W →+ Pt κ W'} (hψ : ψ ∈ rationalHomSet κ W W')
    {z : ℍ[ℚ, a, b]} (hz : z ∈ latOf θ hF.mem d ψ) {μ : ℍ[ℚ, a, b]} (hμ : μ ∈ Λ) :
    z * μ ∈ latOf θ hF.mem d ψ := by
  obtain ⟨ρ', hρ', rfl⟩ := (mem_latOf_iff θ hF.mem d hψ z).mp hz

  have hsμ : star μ ∈ Set.range θ := by
    rw [hF.range_eq]
    exact star_mem_of_mem hF.isOrder hμ
  obtain ⟨α, hα⟩ := hsμ
  have hμα : μ = star (θ α) := by rw [hα, star_star]
  have hαρ' : ((α : AddMonoid.End (Pt κ X₀)) : Pt κ X₀ →+ Pt κ X₀).comp ρ' ∈ rationalHomSet κ W' X₀ :=
    comp_mem_rationalHomSet_of_mem_rationalEndSubring α.2 ρ' hρ'
  have hαρ : ((α : AddMonoid.End (Pt κ X₀)) : Pt κ X₀ →+ Pt κ X₀).comp (ρ'.comp ψ) ∈ rationalHomSet κ W X₀ :=
    comp_mem_rationalHomSet κ W W' X₀ hψ hαρ'
  rw [hμα, ← tr_comp hF.mem θ d α ⟨ρ'.comp ψ, comp_mem_rationalHomSet κ W W' X₀ hψ hρ'⟩ hαρ]
  exact (mem_latOf_iff θ hF.mem d hψ _).mpr ⟨_, hαρ', rfl⟩

theorem IsLatticeFrame.zsmul_mem_latOf (hF : IsLatticeFrame Λ θ χ d J₀) {ψ : Pt κ W →+ Pt κ W'} (hψ : ψ ∈ rationalHomSet κ W W')
    {σ : Pt κ W' →+ Pt κ W} (hσ : σ ∈ rationalHomSet κ W' W) {m : ℤ} (hm : ∀ P, σ (ψ P) = m • P)
    {z : ℍ[ℚ, a, b]} (hz : z ∈ J₀) : m • z ∈ latOf θ hF.mem d ψ := by
  obtain ⟨ρ, rfl⟩ := hF.exists_tr_eq hz
  have hρσ : ρ.1.comp σ ∈ rationalHomSet κ W' X₀ := comp_mem_rationalHomSet κ W' W X₀ hσ ρ.2
  refine (mem_latOf_iff θ hF.mem d hψ _).mpr ⟨ρ.1.comp σ, hρσ, ?_⟩
  rw [← map_zsmul (tr θ hF.mem d) m ρ]
  congr 1
  apply Subtype.ext
  ext P
  change ρ.1 (σ (ψ P)) = ((m • ρ : homGrp W X₀) : Pt κ W →+ Pt κ X₀) P
  rw [hm, map_zsmul, AddSubgroupClass.coe_zsmul, AddMonoidHom.zsmul_apply]

theorem IsLatticeFrame.image_kernelIdealSet_comp_eq (hF : IsLatticeFrame Λ θ χ d J₀) {ψ : Pt κ W →+ Pt κ W'}
    (hψ : ψ ∈ rationalHomSet κ W W') :
    θ '' (kernelIdealSet κ X₀ W' (ψ.comp χ)) = star '' ((d • latOf θ hF.mem d ψ : Submodule ℤ ℍ[ℚ, a, b]) : Set ℍ[ℚ, a, b]) := by
  ext w
  constructor
  · rintro ⟨e, ⟨ρ', hρ', he⟩, rfl⟩
    have h : ρ'.comp ψ ∈ rationalHomSet κ W X₀ := comp_mem_rationalHomSet κ W W' X₀ hψ hρ'
    have hce : compEnd hF.mem ⟨ρ'.comp ψ, h⟩ = e := Subtype.ext (by rw [coe_compEnd, he]; rfl)
    refine ⟨(d : ℍ[ℚ, a, b]) * tr θ hF.mem d ⟨ρ'.comp ψ, h⟩, ?_, ?_⟩
    · rw [SetLike.mem_coe, mem_units_smul_iff, ← mul_assoc, Units.inv_mul, one_mul]
      exact (mem_latOf_iff θ hF.mem d hψ _).mpr ⟨ρ', hρ', rfl⟩
    · rw [← theta_compEnd_eq, hce]
  · rintro ⟨w', hw', rfl⟩
    rw [SetLike.mem_coe, mem_units_smul_iff] at hw'
    obtain ⟨ρ', hρ', htr⟩ := (mem_latOf_iff θ hF.mem d hψ _).mp hw'
    refine ⟨compEnd hF.mem ⟨ρ'.comp ψ, comp_mem_rationalHomSet κ W W' X₀ hψ hρ'⟩, ⟨ρ', hρ', by rw [coe_compEnd]; rfl⟩, ?_⟩
    rw [theta_compEnd_eq θ hF.mem d, htr, ← mul_assoc, Units.mul_inv, one_mul]

end Lattice

section Integral

variable {a b : ℚ}

theorem finiteAdeleBox_mono {I J : Submodule ℤ ℍ[ℚ, a, b]} (h : I ≤ J) :
    Submodule.finiteAdeleBox I ≤ Submodule.finiteAdeleBox J := by
  refine AddSubgroup.closure_mono ?_
  rintro _ ⟨z, hz, c, hc, rfl⟩
  exact ⟨z, h hz, c, hc, rfl⟩

theorem inv_mul_mem_finiteAdeleBox_of_ofFiniteIdele_le {Λ : Submodule ℤ ℍ[ℚ, a, b]} (hΛ : IsOrder Λ)
    {x y : (ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ} (h : Submodule.ofFiniteIdele Λ y ≤ Submodule.ofFiniteIdele Λ x) :
    ((x⁻¹ * y : (ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) : ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ) ∈
      Submodule.finiteAdeleBox Λ := by
  have hmono := finiteAdeleBox_mono h
  rw [Submodule.finiteAdeleBox_ofFiniteIdele Λ hΛ.fg hΛ.spanTop y,
    Submodule.finiteAdeleBox_ofFiniteIdele Λ hΛ.fg hΛ.spanTop x] at hmono
  have h1 : ((y : (ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) : ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ) ∈
      (Submodule.finiteAdeleBox Λ).map (AddMonoidHom.mulLeft ((y : (ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) :
        ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)) := by
    refine AddSubgroup.mem_map.mpr ⟨1, ?_, by rw [AddMonoidHom.coe_mulLeft, mul_one]⟩
    rw [Algebra.TensorProduct.one_def]
    exact tmul_one_mem_finiteAdeleBox hΛ.one_mem
  obtain ⟨w, hw, hyw⟩ := AddSubgroup.mem_map.mp (hmono h1)
  rw [AddMonoidHom.coe_mulLeft] at hyw
  have : ((x⁻¹ * y : (ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) : ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ) = w := by
    rw [Units.val_mul, ← hyw, ← mul_assoc, Units.inv_mul, one_mul]
  rw [this]
  exact hw

end Integral

end CerednikDrinfeld.KernelIdealTransport
p2m_reactivate "P2MW.S_CerednikDrinfeld_exists_mem_finiteAdeleBox_image_kernelIdealSet_comp_eq_star_smul_ofFiniteIdele_mul_of_dualPair.CerednikDrinfeld P2MW.S_CerednikDrinfeld_exists_mem_finiteAdeleBox_image_kernelIdealSet_comp_eq_star_smul_ofFiniteIdele_mul_of_dualPair.CerednikDrinfeld.KernelIdealTransport"
p2m_reactivate "P2MW.S_CerednikDrinfeld_exists_mem_finiteAdeleBox_image_kernelIdealSet_comp_eq_star_smul_ofFiniteIdele_mul_of_dualPair.CerednikDrinfeld"

end
p2m_reactivate "P2MW.S_CerednikDrinfeld_exists_mem_finiteAdeleBox_image_kernelIdealSet_comp_eq_star_smul_ofFiniteIdele_mul_of_dualPair.CerednikDrinfeld P2MW.S_CerednikDrinfeld_exists_mem_finiteAdeleBox_image_kernelIdealSet_comp_eq_star_smul_ofFiniteIdele_mul_of_dualPair.CerednikDrinfeld.KernelIdealTransport"

open CerednikDrinfeld.KernelIdealTransport WeierstrassCurve in
theorem solution
    {κ : Type} [Field κ] [IsAlgClosed κ] [DecidableEq κ]
    (q' : ℕ) [Fact q'.Prime] [CharP κ q'] [Algebra (ZMod q') κ] [Algebra.IsAlgebraic (ZMod q') κ]
    (X₁ : WeierstrassCurve κ) [X₁.IsElliptic] (hss : ∀ P : X₁.toAffine.Point, q' • P = 0 → P = 0)
    (a b : ℚ) (hdef : IsDefiniteRamifiedExactlyAt a b q')
    (Λ₁ : Submodule ℤ ℍ[ℚ, a, b]) (hΛ₁ : IsMaximalOrder Λ₁)
    (θ₁ : ↥(WeierstrassCurve.rationalEndSubring κ X₁) →+* ℍ[ℚ, a, b])
    (hθ₁ : Function.Injective θ₁) (hθ₁Λ : Set.range θ₁ = (Λ₁ : Set ℍ[ℚ, a, b]))
    (x : (ℍ[ℚ, a, b] ⊗[ℚ] IsDedekindDomain.FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ)
    (W : WeierstrassCurve κ) [W.IsElliptic] (χ : X₁.toAffine.Point →+ W.toAffine.Point)
    (hχ : χ ∈ WeierstrassCurve.rationalHomSet κ X₁ W) (hχ0 : χ ≠ 0) (d : (ℍ[ℚ, a, b])ˣ)
    (hK : θ₁ '' WeierstrassCurve.kernelIdealSet κ X₁ W χ =
      star '' ((d • Submodule.ofFiniteIdele Λ₁ x : Submodule ℤ ℍ[ℚ, a, b]) : Set ℍ[ℚ, a, b]))
    (W' : WeierstrassCurve κ) [W'.IsElliptic] (ψ : W.toAffine.Point →+ W'.toAffine.Point)
    (hψ : ψ ∈ WeierstrassCurve.rationalHomSet κ W W') (hψ0 : ψ ≠ 0) (ψ' : W'.toAffine.Point →+ W.toAffine.Point)
    (hψ' : ψ' ∈ WeierstrassCurve.rationalHomSet κ W' W)
    (hψd : ψ'.comp ψ = Nat.card ψ.ker • AddMonoidHom.id _ ∧ ψ.comp ψ' = Nat.card ψ.ker • AddMonoidHom.id _) :
    ∃ g : (ℍ[ℚ, a, b] ⊗[ℚ] IsDedekindDomain.FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ, ((g : (ℍ[ℚ, a, b] ⊗[ℚ] IsDedekindDomain.FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) : (ℍ[ℚ, a, b] ⊗[ℚ] IsDedekindDomain.FiniteAdeleRing (𝓞 ℚ) ℚ)) ∈ Submodule.finiteAdeleBox Λ₁ ∧
      θ₁ '' WeierstrassCurve.kernelIdealSet κ X₁ W' (ψ.comp χ) =
        star '' ((d • Submodule.ofFiniteIdele Λ₁ (x * g) : Submodule ℤ ℍ[ℚ, a, b]) : Set ℍ[ℚ, a, b]) ∧
      Nat.card ψ.ker ^ 2 = (Submodule.ofFiniteIdele Λ₁ (x * g)).toAddSubgroup.relIndex (Submodule.ofFiniteIdele Λ₁ x).toAddSubgroup := by

  have hF : IsLatticeFrame (X₀ := X₁) (W := W) Λ₁ θ₁ (χ : Pt κ X₁ →+ Pt κ W) d (Submodule.ofFiniteIdele Λ₁ x) :=
    ⟨hΛ₁.isOrder, hθ₁, hθ₁Λ, hχ, hχ0, hK⟩
  have hψW : (ψ : Pt κ W →+ Pt κ W') ∈ rationalHomSet κ W W' := hψ

  have hJle : latOf (X₀ := X₁) (W' := W') θ₁ hF.mem d (ψ : Pt κ W →+ Pt κ W') ≤ Submodule.ofFiniteIdele Λ₁ x := hF.latOf_le hψW
  have hJmul : ∀ z ∈ latOf (X₀ := X₁) (W' := W') θ₁ hF.mem d (ψ : Pt κ W →+ Pt κ W'), ∀ μ ∈ Λ₁,
      z * μ ∈ latOf (X₀ := X₁) (W' := W') θ₁ hF.mem d (ψ : Pt κ W →+ Pt κ W') :=
    fun z hz μ hμ => hF.mul_mem_latOf hψW hz hμ
  obtain ⟨σ, hσ, m, hm0, hdual⟩ := WeierstrassCurve.exists_isDualPair_of_mem_rationalHomSet κ W W' hψ hψ0
  have hJfull : ∃ n : ℕ, n ≠ 0 ∧ ∀ z ∈ Submodule.ofFiniteIdele Λ₁ x,
      (n : ℚ) • z ∈ latOf (X₀ := X₁) (W' := W') θ₁ hF.mem d (ψ : Pt κ W →+ Pt κ W') := by
    refine ⟨m.toNat, ?_, fun z hz => ?_⟩
    · intro h0
      have := Int.toNat_of_nonneg hm0.le
      omega
    · have e : ((m.toNat : ℕ) : ℚ) • z = m • z := by
        rw [← Int.cast_natCast, Int.toNat_of_nonneg hm0.le, Int.cast_smul_eq_zsmul]
      rw [e]
      exact hF.zsmul_mem_latOf hψW hσ hdual.comp_left hz

  obtain ⟨y, hy⟩ := QuaternionAlgebra.IsMaximalOrder.exists_eq_ofFiniteIdele_of_forall_mul_mem (Fact.out : q'.Prime) hdef hΛ₁ x
    (latOf (X₀ := X₁) (W' := W') θ₁ hF.mem d (ψ : Pt κ W →+ Pt κ W')) hJle hJmul hJfull

  have hxy : x * (x⁻¹ * y) = y := mul_inv_cancel_left x y
  have hg : ((x⁻¹ * y : (ℍ[ℚ, a, b] ⊗[ℚ] IsDedekindDomain.FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) :
      ℍ[ℚ, a, b] ⊗[ℚ] IsDedekindDomain.FiniteAdeleRing (𝓞 ℚ) ℚ) ∈ Submodule.finiteAdeleBox Λ₁ :=
    inv_mul_mem_finiteAdeleBox_of_ofFiniteIdele_le hΛ₁.isOrder (by rw [← hy]; exact hJle)
  have hKJ : θ₁ '' WeierstrassCurve.kernelIdealSet κ X₁ W' (ψ.comp χ) =
      star '' ((d • Submodule.ofFiniteIdele Λ₁ (x * (x⁻¹ * y)) : Submodule ℤ ℍ[ℚ, a, b]) : Set ℍ[ℚ, a, b]) := by
    rw [hxy, ← hy]
    exact hF.image_kernelIdealSet_comp_eq hψW
  exact ⟨x⁻¹ * y, hg, hKJ,
    CerednikDrinfeld.natCard_ker_sq_eq_relIndex_ofFiniteIdele_mul_of_image_kernelIdealSet_comp_eq q' X₁ hss a b hdef Λ₁ hΛ₁ θ₁
      hθ₁ hθ₁Λ x W χ hχ hχ0 d hK (x⁻¹ * y) hg W' ψ hψ ψ' hψ' hψd hKJ⟩

end S_CerednikDrinfeld_exists_mem_finiteAdeleBox_image_kernelIdealSet_comp_eq_star_smul_ofFiniteIdele_mul_of_dualPair
end P2MW
export P2MW.S_CerednikDrinfeld_exists_mem_finiteAdeleBox_image_kernelIdealSet_comp_eq_star_smul_ofFiniteIdele_mul_of_dualPair (solution)
