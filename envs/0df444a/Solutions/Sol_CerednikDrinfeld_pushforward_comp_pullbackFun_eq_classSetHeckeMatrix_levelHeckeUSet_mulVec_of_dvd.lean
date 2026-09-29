-- Prove2me | solution 1 for CerednikDrinfeld.pushforward_comp_pullbackFun_eq_classSetHeckeMatrix_levelHeckeUSet_mulVec_of_dvd
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.491319+00:00
-- url     : https://prove2.me/submissions/554f4ed8-fef2-5817-a020-3bc640b6b69c

import Mathlib
import Definitions.Def_CerednikDrinfeld_ClassSetGraph
import Definitions.Def_QuaternionAlgebra_ClassSetHecke
import Definitions.Def_QuaternionAlgebra_Order
import Definitions.Def_QuaternionAlgebra_Order_FiniteIdele
import Definitions.Def_QuaternionAlgebra_EichlerOrder
import Definitions.Def_Submodule_FiniteAdeleBox
import Definitions.Def_Submodule_LocalBox
import Definitions.Def_AlgebraicCurve_TotallyDegenerateCovering_Hom
import Theorems.Thm_QuaternionAlgebra_IsOrder_finiteAdeleBox_inf_conjByFiniteIdele_eq_and_finiteIdeleStabilizer_le
import Theorems.Thm_QuaternionAlgebra_IsOrder_finite_isUnitOf_and_nrd_eq_one
import Theorems.Thm_QuaternionAlgebra_IsOrder_conjByFiniteIdele
import Theorems.Thm_Submodule_finiteAdeleBox_conjByFiniteIdele
import Theorems.Thm_Submodule_mem_finiteAdeleBox_iff_forall_finiteAdeleEvalAt_mem_localBox
import Theorems.Thm_QuaternionAlgebra_IsOrder_mem_finiteIdeleStabilizer_iff_forall_map_finiteAdeleEvalAt_mem_localBoxUnits
import Theorems.Thm_Submodule_exists_units_finiteAdeleEvalAt_eq
import Theorems.Thm_QuaternionAlgebra_IsOrder_finite_setOf_exists_mem_quotientMk_eq_of_subset_primeHeckeSet
import Theorems.Thm_CerednikDrinfeld_mul_mem_levelHeckeUSet_and_mul_mem_levelHeckeUSet_of_mem_finiteIdeleStabilizer
import Theorems.Thm_CerednikDrinfeld_levelHeckeUSet_eq_doubleCoset_finiteIdeleStabilizer_of_dvd_of_squarefree
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_pushforward_comp_pullbackFun_eq_classSetHeckeMatrix_levelHeckeUSet_mulVec_of_dvd
p2m_attr_erase "instance" "IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue AlgebraicCurve.instFundamentalIdentityOfSumRamificationInertia AlgebraicCurve.Place.instIsScalarTowerResidueFieldRestrictPushforward AlgebraicCurve.Place.instAlgebraResidueFieldRestrictPushforward AlgebraicCurve.Place.instIsLocalHomRestrictInclusion AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupDivisor AlgebraicCurve.Pic0.instModuleZModTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instDistribMulActionTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instSMulTorsion AlgebraicCurve.SemilinearAut.instMulActionSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instSMulCommClassZModTorsion AlgebraicCurve.SemilinearAut.instMulSemiringActionSubtypeProdRingAutMemSubgroup ModularCurve.SpecializationWitnessData.addCommGroup ModularCurve.CommutingHeckeFamily.commRing_adjoin ModularCurve.Gamma0Pair.isElliptic ModularCurve.ModuliTestDatum.isElliptic_reduced ModularCurve.ModuliTestDatum.isElliptic_curve ModularCurve.ModuliTestDatum.isElliptic_generic"
p2m_attr_erase "simp" "QuaternionAlgebra.baseChangeRight_tmul QuaternionAlgebra.mapOfAlgebraMapEq_apply QuaternionAlgebra.baseChange_tmul LocalGL2.swapUnit_val ModularCurve.coe_levelAlphaC ModularCurve.SSLevelDatum.mk.sizeOf_spec ModularCurve.SSLevelDatum.mk.injEq ModularCurve.coe_levelBetaC ModularCurve.coe_heckeBetaC AlgebraicCurve.Divisor.coe_degZeroEnd ModularCurve.coe_heckeAlphaC AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Divisor.mapRestrict_single AlgebraicCurve.Divisor.pushforward_single AlgebraicCurve.Place.coe_restrictInclusion AlgebraicCurve.Place.mem_fiber AlgebraicCurve.Place.restrict_toValuationSubring AlgebraicCurve.Divisor.degree_pushforward AlgebraicCurve.Place.restrictResidueMap_residue AlgebraicCurve.Pic0.coe_pushforwardDegZeroHom AlgebraicCurve.Pic0.coe_pullbackDegZeroHom AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply"
p2m_attr_erase "simp" "AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.Divisor.degree_pushforwardAlong AlgebraicCurve.Pic0.coe_degZeroCorrespondence AlgebraicCurve.Place.mem_fiberAlong AlgebraicCurve.SemilinearAut.toRingAut_inv AlgebraicCurve.SemilinearAut.smul_def AlgebraicCurve.SemilinearAut.smul_single AlgebraicCurve.SemilinearAut.smul_toValuationSubring AlgebraicCurve.SemilinearAut.baseAut_inv AlgebraicCurve.SemilinearAut.baseAut_ofAlgAut AlgebraicCurve.SemilinearAut.toRingAut_ofAlgAut AlgebraicCurve.SemilinearAut.torsionRep_apply AlgebraicCurve.SemilinearAut.toRingAut_one AlgebraicCurve.SemilinearAut.deg_smul AlgebraicCurve.SemilinearAut.degree_smul AlgebraicCurve.SemilinearAut.coe_degZeroSMulHom AlgebraicCurve.SemilinearAut.baseAut_mul AlgebraicCurve.SemilinearAut.coe_smulValuationSubringEquiv_apply AlgebraicCurve.SemilinearAut.baseAut_one AlgebraicCurve.SemilinearAut.ofAlgAut_smul AlgebraicCurve.SemilinearAut.coe_torsion_smul AlgebraicCurve.SemilinearAut.toRingAut_mul AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.jqNModC_one ModularCurve.qExpand_coeff_mul ModularCurve.qExpandₐ_apply ModularCurve.jqN_one ModularCurve.qExpand_single ModularCurve.dedekindPsi_one ModularCurve.ModularPolynomialData.mk.sizeOf_spec ModularCurve.evalAtJ_X ModularCurve.ModularPolynomialData.mk.injEq ModularCurve.constantCoeff_jNum ModularCurve.constantCoeff_eisenstein4 ModularCurve.qExpand_C ModularCurve.coeff_jq_neg_one ModularCurve.constantCoeff_jNumQ ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff"
p2m_attr_erase "simp" "ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd ModularCurve.CommutingHeckeFamily.mk.injEq ModularCurve.SpecializationWitnessData.mk.sizeOf_spec ModularCurve.SpecializationWitnessData.mk.injEq ModularCurve.CommutingHeckeFamily.mk.sizeOf_spec ModularCurve.coe_nodeEquivOfPlaces_apply ModularCurve.widthOfPlaces_mk ModularCurve.smulNodePairEmb_apply ModularCurve.card_nodePairsOfPlaces ModularCurve.smulNodePair_snd ModularCurve.smulNodePair_fst ModularCurve.coe_nodeEquivOfPlaces_symm_apply ModularCurve.coe_jGeomGen ModularCurve.coe_jNGeomGen ModularCurve.coe_uniformizerMod ModularCurve.qSeriesBar_jModElt ModularCurve.qInftyPlaceMod_toValuationSubring ModularCurve.qInftyPlaceBar_toValuationSubring ModularCurve.qSeriesBar_zero ModularCurve.qSeriesBar_add ModularCurve.cuspInftyFull_toValuationSubring ModularCurve.qInftyPlaceRat_toValuationSubring ModularCurve.qSeriesBar_mul ModularCurve.qSeriesBar_div ModularCurve.qSeriesBar_eq_zero_iff ModularCurve.coe_uniformizerBar ModularCurve.qSeriesBar_pow ModularCurve.cuspInfty_toValuationSubring ModularCurve.qSeriesBar_one ModularCurve.qSeriesBar_inv ModularCurve.qSeriesBar_sub ModularCurve.qSeriesBar_neg"
p2m_attr_erase "simp" "ModularCurve.charLGeomModuliDictionary_single ModularCurve.specializeModuli_single ModularCurve.specializePlace_def ModularCurve.gamma0PairMap_gen ModularCurve.moduliPointMapRingHom_mk ModularCurve.Gamma0Pair.mk.injEq ModularCurve.ModuliPoint.j_mk ModularCurve.Gamma0Pair.mk.sizeOf_spec ModularCurve.gamma0PairMap_toCurve WeierstrassCurve.Affine.vcY_vcYInv WeierstrassCurve.Affine.vcXInv_vcX WeierstrassCurve.Affine.Point.vcFun_zero WeierstrassCurve.Affine.vcX_vcXInv WeierstrassCurve.Affine.vcYInv_vcY WeierstrassCurve.Affine.Point.vcInvFun_zero WeierstrassCurve.ratPointHom_apply WeierstrassCurve.ratPointMap_zero ModularCurve.ComapPlace.place_toValuationSubring ModularCurve.ModuliTestDatum.restrictLevel_emb ModularCurve.ModuliTestDatum.restrictLevel_res ModularCurve.ModuliTestDatum.mk.injEq ModularCurve.ModuliTestDatum.restrictLevel_W ModularCurve.ModuliTestDatum.place_toValuationSubring ModularCurve.ModuliTestDatum.restrictLevel_curve ModularCurve.ModuliTestDatum.resEquiv_apply ModularCurve.ModuliTestDatum.restrictLevel_gen ModularCurve.ModuliTestDatum.mk.sizeOf_spec ModularCurve.coe_jqNFull ModularCurve.qExpandAlgHomC_apply ModularCurve.coeffEmb_coeff ModularCurve.coeffMap_coeff ModularCurve.coeffMap_id ModularCurve.coeffMap_single ModularCurve.Gamma0Pair.map_toCurve WeierstrassCurve.mapPoint_eq_ratPointMap ModularCurve.Gamma0Pair.map_gen ModularCurve.Gamma0Pair.map_eq_gamma0PairMap ModularCurve.ModuliPoint.map_eq_moduliPointMapRingHom ModularCurve.ModuliPoint.map_mk WeierstrassCurve.mapPointHom_apply"
p2m_attr_erase "simp" "WeierstrassCurve.mapPoint_zero WeierstrassCurve.twoVeluCurve_a₁ WeierstrassCurve.twoVeluCurve_a₂ WeierstrassCurve.twoVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₂ WeierstrassCurve.xVeluCurve_a₁ WeierstrassCurve.veluWSum_empty WeierstrassCurve.veluQuotient_a₁ WeierstrassCurve.veluQuotient_a₃ WeierstrassCurve.veluQuotient_empty WeierstrassCurve.veluTSum_empty WeierstrassCurve.veluQuotient_a₂ WeierstrassCurve.veluQuotient2_a₂ WeierstrassCurve.veluQuotient2_a₃ WeierstrassCurve.veluQuotient2_a₁ WeierstrassCurve.veluPointMap2_zero WeierstrassCurve.Affine.Point.coordsOrZero_some WeierstrassCurve.Affine.Point.coordsOrZero_zero"

set_option autoImplicit false

open scoped TensorProduct Quaternion Pointwise
open IsDedekindDomain NumberField

namespace HeckeLocal

variable {a b : ℚ}

local notation "𝔸f" => FiniteAdeleRing (𝓞 ℚ) ℚ
local notation "ℍ𝔸" => ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ

def boxGen (Λ : Submodule ℤ ℍ[ℚ, a, b]) : Set ℍ𝔸 :=
  {x | ∃ z ∈ Λ, ∃ c : FiniteAdeleRing (𝓞 ℚ) ℚ,
      (∀ v : HeightOneSpectrum (𝓞 ℚ), c v ∈ v.adicCompletionIntegers ℚ) ∧ x = z ⊗ₜ[ℚ] c}

theorem box_eq_span (Λ : Submodule ℤ ℍ[ℚ, a, b]) :
    Submodule.finiteAdeleBox Λ = (Submodule.span ℤ (boxGen Λ)).toAddSubgroup := by
  rw [Submodule.span_int_eq_addSubgroupClosure]; rfl

theorem mem_box_iff {Λ : Submodule ℤ ℍ[ℚ, a, b]} {x : ℍ𝔸} :
    x ∈ Submodule.finiteAdeleBox Λ ↔ x ∈ Submodule.span ℤ (boxGen Λ) := by
  rw [box_eq_span]; rfl

theorem box_mul_mem {Λ : Submodule ℤ ℍ[ℚ, a, b]} (hΛ : QuaternionAlgebra.IsOrder Λ)
    {x y : ℍ𝔸} (hx : x ∈ Submodule.finiteAdeleBox Λ) (hy : y ∈ Submodule.finiteAdeleBox Λ) :
    x * y ∈ Submodule.finiteAdeleBox Λ := by
  rw [mem_box_iff] at hx hy ⊢
  induction hy using Submodule.span_induction with
  | mem y hy' =>
    obtain ⟨z, hz, c, hc, rfl⟩ := hy'
    induction hx using Submodule.span_induction with
    | mem x hx' =>
      obtain ⟨z', hz', c', hc', rfl⟩ := hx'
      refine Submodule.subset_span ⟨z' * z, hΛ.mul_mem hz' hz, c' * c, fun v => ?_, ?_⟩
      · have e : (c' * c) v = c' v * c v := rfl
        rw [e]
        exact mul_mem (hc' v) (hc v)
      · rw [Algebra.TensorProduct.tmul_mul_tmul]
    | zero => rw [zero_mul]; exact zero_mem _
    | add x₁ x₂ _ _ h₁ h₂ => rw [add_mul]; exact add_mem h₁ h₂
    | smul m x₁ _ h₁ => rw [smul_mul_assoc]; exact Submodule.smul_mem _ _ h₁
  | zero => rw [mul_zero]; exact zero_mem _
  | add y₁ y₂ _ _ h₁ h₂ => rw [mul_add]; exact add_mem h₁ h₂
  | smul m y₁ _ h₁ => rw [mul_smul_comm]; exact Submodule.smul_mem _ _ h₁

theorem one_mem_box {Λ : Submodule ℤ ℍ[ℚ, a, b]} (hΛ : QuaternionAlgebra.IsOrder Λ) :
    (1 : ℍ𝔸) ∈ Submodule.finiteAdeleBox Λ := by
  unfold Submodule.finiteAdeleBox
  refine AddSubgroup.subset_closure ⟨1, hΛ.one_mem, 1, fun v => ?_, ?_⟩
  · have e : (1 : FiniteAdeleRing (𝓞 ℚ) ℚ) v = 1 := rfl
    rw [e]; exact one_mem _
  · rfl

theorem coe_mem_box_of_mem_stabilizer {Λ : Submodule ℤ ℍ[ℚ, a, b]} (hΛ : QuaternionAlgebra.IsOrder Λ)
    {u : (ℍ𝔸)ˣ} (hu : u ∈ Submodule.finiteIdeleStabilizer Λ) :
    (u : ℍ𝔸) ∈ Submodule.finiteAdeleBox Λ := by
  have h := (Submodule.mem_finiteIdeleStabilizer_iff Λ u).mp hu

  have h1 : (u : ℍ𝔸) * 1 ∈ u • ((Submodule.finiteAdeleBox Λ : AddSubgroup ℍ𝔸) : Set ℍ𝔸) :=
    Set.smul_mem_smul_set (one_mem_box hΛ)
  rw [h, mul_one] at h1
  exact h1

theorem coe_inv_mem_box_of_mem_stabilizer {Λ : Submodule ℤ ℍ[ℚ, a, b]} (hΛ : QuaternionAlgebra.IsOrder Λ)
    {u : (ℍ𝔸)ˣ} (hu : u ∈ Submodule.finiteIdeleStabilizer Λ) :
    ((u⁻¹ : (ℍ𝔸)ˣ) : ℍ𝔸) ∈ Submodule.finiteAdeleBox Λ :=
  coe_mem_box_of_mem_stabilizer hΛ (inv_mem hu)

theorem mem_stabilizer_of_coe_mem_of_coe_inv_mem {Λ : Submodule ℤ ℍ[ℚ, a, b]} (hΛ : QuaternionAlgebra.IsOrder Λ)
    {u : (ℍ𝔸)ˣ} (hu : (u : ℍ𝔸) ∈ Submodule.finiteAdeleBox Λ) (hui : ((u⁻¹ : (ℍ𝔸)ˣ) : ℍ𝔸) ∈ Submodule.finiteAdeleBox Λ) :
    u ∈ Submodule.finiteIdeleStabilizer Λ := by
  rw [Submodule.mem_finiteIdeleStabilizer_iff]
  apply Set.Subset.antisymm
  · rintro _ ⟨x, hx, rfl⟩
    exact box_mul_mem hΛ hu hx
  · intro x hx
    refine ⟨(u⁻¹ : (ℍ𝔸)ˣ) • x, box_mul_mem hΛ hui hx, ?_⟩
    show (u : ℍ𝔸) * (((u⁻¹ : (ℍ𝔸)ˣ) : ℍ𝔸) * x) = x
    rw [← mul_assoc, Units.mul_inv, one_mul]

theorem mem_stabilizer_iff {Λ : Submodule ℤ ℍ[ℚ, a, b]} (hΛ : QuaternionAlgebra.IsOrder Λ) (u : (ℍ𝔸)ˣ) :
    u ∈ Submodule.finiteIdeleStabilizer Λ ↔
      (u : ℍ𝔸) ∈ Submodule.finiteAdeleBox Λ ∧ ((u⁻¹ : (ℍ𝔸)ˣ) : ℍ𝔸) ∈ Submodule.finiteAdeleBox Λ :=
  ⟨fun hu => ⟨coe_mem_box_of_mem_stabilizer hΛ hu, coe_inv_mem_box_of_mem_stabilizer hΛ hu⟩,
   fun h => mem_stabilizer_of_coe_mem_of_coe_inv_mem hΛ h.1 h.2⟩

theorem mul_mem_primeHeckeSet_of_mem_stabilizer {Λ : Submodule ℤ ℍ[ℚ, a, b]} (hΛ : QuaternionAlgebra.IsOrder Λ)
    (ℓ : ℕ) {u h : (ℍ𝔸)ˣ} (hu : u ∈ Submodule.finiteIdeleStabilizer Λ) (hh : h ∈ QuaternionAlgebra.primeHeckeSet Λ ℓ) :
    u * h ∈ QuaternionAlgebra.primeHeckeSet Λ ℓ := by
  obtain ⟨h1, h2, h3, h4⟩ := hh
  have hub := coe_mem_box_of_mem_stabilizer hΛ hu
  have huib := coe_inv_mem_box_of_mem_stabilizer hΛ hu
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [Units.val_mul]; exact box_mul_mem hΛ hub h1
  · rw [mul_inv_rev, Units.val_mul, ← smul_mul_assoc]
    exact box_mul_mem hΛ h2 huib
  · intro hmem
    apply h3
    have : ((h⁻¹ : (ℍ𝔸)ˣ) : ℍ𝔸) = (((u * h)⁻¹ : (ℍ𝔸)ˣ) : ℍ𝔸) * (u : ℍ𝔸) := by
      rw [mul_inv_rev, Units.val_mul, mul_assoc, Units.inv_mul, mul_one]
    rw [this]; exact box_mul_mem hΛ hmem hub
  · intro hmem
    apply h4
    have : (ℓ : ℚ)⁻¹ • (h : ℍ𝔸) = ((u⁻¹ : (ℍ𝔸)ˣ) : ℍ𝔸) * ((ℓ : ℚ)⁻¹ • ((u * h : (ℍ𝔸)ˣ) : ℍ𝔸)) := by
      rw [mul_smul_comm, Units.val_mul, ← mul_assoc, Units.inv_mul, one_mul]
    rw [this]; exact box_mul_mem hΛ huib hmem

end HeckeLocal

namespace GOODEQ

variable {a b : ℚ}

local notation "ℍ𝔸" => ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ

theorem mem_conjByFiniteIdele_iff (Λ : Submodule ℤ ℍ[ℚ, a, b]) (g : (ℍ𝔸)ˣ) (z : ℍ[ℚ, a, b]) :
    z ∈ Submodule.conjByFiniteIdele Λ g ↔
      ((g⁻¹ : (ℍ𝔸)ˣ) : ℍ𝔸) * (z ⊗ₜ[ℚ] (1 : FiniteAdeleRing (𝓞 ℚ) ℚ)) * (g : ℍ𝔸) ∈ Submodule.finiteAdeleBox Λ := by
  show z ⊗ₜ[ℚ] (1 : FiniteAdeleRing (𝓞 ℚ) ℚ) ∈ (Submodule.finiteAdeleBox Λ).map _ ↔ _
  rw [AddSubgroup.mem_map]
  constructor
  · rintro ⟨u, hu, h⟩
    rw [AddMonoidHom.comp_apply, AddMonoidHom.coe_mulLeft, AddMonoidHom.coe_mulRight] at h
    have : ((g⁻¹ : (ℍ𝔸)ˣ) : ℍ𝔸) * (z ⊗ₜ[ℚ] (1 : FiniteAdeleRing (𝓞 ℚ) ℚ)) * (g : ℍ𝔸) = u := by
      rw [← h, ← mul_assoc, ← mul_assoc, Units.inv_mul, one_mul, mul_assoc, Units.inv_mul, mul_one]
    rw [this]; exact hu
  · intro h
    refine ⟨_, h, ?_⟩
    rw [AddMonoidHom.comp_apply, AddMonoidHom.coe_mulLeft, AddMonoidHom.coe_mulRight]
    show (g : ℍ𝔸) * (((g⁻¹ : (ℍ𝔸)ˣ) : ℍ𝔸) * (z ⊗ₜ[ℚ] (1 : FiniteAdeleRing (𝓞 ℚ) ℚ)) * (g : ℍ𝔸)) * ((g⁻¹ : (ℍ𝔸)ˣ) : ℍ𝔸) = _
    rw [← mul_assoc, ← mul_assoc, Units.mul_inv, one_mul, mul_assoc, Units.mul_inv, mul_one]

section Frame

variable {R : Submodule ℤ ℍ[ℚ, a, b]} (hR : QuaternionAlgebra.IsOrder R)

include hR in
theorem isOrder_meetOrder (n : (ℍ𝔸)ˣ) : QuaternionAlgebra.IsOrder (CerednikDrinfeld.meetOrder R n) :=
  QuaternionAlgebra.IsOrder.inf hR (QuaternionAlgebra.IsOrder.conjByFiniteIdele R hR n)

end Frame

end GOODEQ

open scoped TensorProduct Quaternion NumberField
p2m_open "IsDedekindDomain NumberField QuaternionAlgebra CerednikDrinfeld P2MW.S_CerednikDrinfeld_pushforward_comp_pullbackFun_eq_classSetHeckeMatrix_levelHeckeUSet_mulVec_of_dvd.CerednikDrinfeld Finset"

namespace CerednikDrinfeld
p2m_export "CerednikDrinfeld" "meetOrder classSetForget classSetShift unitWeight classWeight classSetHeckeMatrix levelHeckeUSet classSetDegeneracyData DegeneracyData pushforward pushforward_apply_eq_sum_filter DegeneracyData.FiniteHom DegeneracyData.FiniteHom.pullbackFun_apply mul_mem_levelHeckeUSet_and_mul_mem_levelHeckeUSet_of_mem_finiteIdeleStabilizer levelHeckeUSet_eq_doubleCoset_finiteIdeleStabilizer_of_dvd_of_squarefree"
namespace HeckeDict
p2m_open "CerednikDrinfeld"

theorem pushforward_pullbackFun_apply {E₁ V₁ E₂ V₂ W : Type*} [Fintype E₁] [Fintype V₁] [DecidableEq V₁]
    [DecidableEq E₂] [DecidableEq V₂] [Fintype E₂] [DecidableEq W]
    {D₁ : DegeneracyData E₁ V₁} {D₂ : DegeneracyData E₂ V₂} (μ : D₁.FiniteHom D₂) (g : E₁ → W) (x : E₂ → ℤ) (i : W) :
    CerednikDrinfeld.pushforward g (μ.pullbackFun x) i =
      ∑ j : E₂, (∑ e ∈ univ.filter (fun e => μ.mapE e = j ∧ g e = i), (μ.deg e : ℤ)) * x j := by
  rw [pushforward_apply_eq_sum_filter,
    ← sum_fiberwise_of_maps_to (s := univ.filter (fun e => g e = i)) (t := (univ : Finset E₂)) (g := μ.mapE)
      (fun e _ => mem_univ _)]
  refine sum_congr rfl fun j _ => ?_
  rw [filter_filter, sum_mul]
  refine sum_congr (filter_congr fun e _ => ?_) fun e he => ?_
  · exact ⟨fun h => ⟨h.2, h.1⟩, fun h => ⟨h.2, h.1⟩⟩
  · rw [DegeneracyData.FiniteHom.pullbackFun_apply, (mem_filter.mp he).2.1]

theorem classSetHeckeMatrix_mulVec_apply {a b : ℚ}
    (U : Subgroup (ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) (T : Set (ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ)
    [Fintype (ClassSet U)] (x : ClassSet U → ℤ) (i : ClassSet U) :
    (classSetHeckeMatrix U T).mulVec x i = ∑ j, heckeKernel U T j i * x j := rfl

section Tower

variable {a b : ℚ}

local notation "ℍ𝔸" => ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ

theorem mem_map_conj_box_iff (B : AddSubgroup (ℍ𝔸)) (g : (ℍ𝔸)ˣ) (x : ℍ𝔸) :
    x ∈ B.map ((AddMonoidHom.mulRight ((g⁻¹ : (ℍ𝔸)ˣ) : ℍ𝔸)).comp (AddMonoidHom.mulLeft (g : ℍ𝔸))) ↔
      ((g⁻¹ : (ℍ𝔸)ˣ) : ℍ𝔸) * x * (g : ℍ𝔸) ∈ B := by
  rw [AddSubgroup.mem_map]
  constructor
  · rintro ⟨y, hy, rfl⟩
    rw [AddMonoidHom.comp_apply, AddMonoidHom.coe_mulLeft, AddMonoidHom.coe_mulRight]
    have : ((g⁻¹ : (ℍ𝔸)ˣ) : ℍ𝔸) * ((g : ℍ𝔸) * y * ((g⁻¹ : (ℍ𝔸)ˣ) : ℍ𝔸)) * (g : ℍ𝔸) = y := by
      rw [← mul_assoc, ← mul_assoc, Units.inv_mul, one_mul, mul_assoc, Units.inv_mul, mul_one]
    rw [this]; exact hy
  · intro h
    refine ⟨_, h, ?_⟩
    rw [AddMonoidHom.comp_apply, AddMonoidHom.coe_mulLeft, AddMonoidHom.coe_mulRight]
    show (g : ℍ𝔸) * (((g⁻¹ : (ℍ𝔸)ˣ) : ℍ𝔸) * x * (g : ℍ𝔸)) * ((g⁻¹ : (ℍ𝔸)ˣ) : ℍ𝔸) = x
    rw [← mul_assoc, ← mul_assoc, Units.mul_inv, one_mul, mul_assoc, Units.mul_inv, mul_one]

theorem mem_box_meetOrder_iff {Λ : Submodule ℤ ℍ[ℚ, a, b]} (hΛ : QuaternionAlgebra.IsOrder Λ) (g : (ℍ𝔸)ˣ) (x : ℍ𝔸) :
    x ∈ Submodule.finiteAdeleBox (meetOrder Λ g) ↔
      x ∈ Submodule.finiteAdeleBox Λ ∧ ((g⁻¹ : (ℍ𝔸)ˣ) : ℍ𝔸) * x * (g : ℍ𝔸) ∈ Submodule.finiteAdeleBox Λ := by
  have h := (QuaternionAlgebra.IsOrder.finiteAdeleBox_inf_conjByFiniteIdele_eq_and_finiteIdeleStabilizer_le Λ hΛ g).1
  show x ∈ Submodule.finiteAdeleBox (Λ ⊓ Submodule.conjByFiniteIdele Λ g) ↔ _
  rw [h, AddSubgroup.mem_inf, mem_map_conj_box_iff]

theorem conj_unit_mem_box_iff {Λ : Submodule ℤ ℍ[ℚ, a, b]} (hΛ : QuaternionAlgebra.IsOrder Λ) {w : (ℍ𝔸)ˣ}
    (hw : w ∈ Submodule.finiteIdeleStabilizer Λ) (y : ℍ𝔸) :
    ((w⁻¹ : (ℍ𝔸)ˣ) : ℍ𝔸) * y * (w : ℍ𝔸) ∈ Submodule.finiteAdeleBox Λ ↔ y ∈ Submodule.finiteAdeleBox Λ := by
  have hw' := (HeckeLocal.mem_stabilizer_iff hΛ w).mp hw
  constructor
  · intro h
    have := HeckeLocal.box_mul_mem hΛ (HeckeLocal.box_mul_mem hΛ hw'.1 h) hw'.2
    rwa [← mul_assoc, ← mul_assoc, Units.mul_inv, one_mul, mul_assoc, Units.mul_inv, mul_one] at this
  · intro h
    exact HeckeLocal.box_mul_mem hΛ (HeckeLocal.box_mul_mem hΛ hw'.2 h) hw'.1

theorem mem_box_tower_iff {R : Submodule ℤ ℍ[ℚ, a, b]} (hR : QuaternionAlgebra.IsOrder R) (n m n' : (ℍ𝔸)ˣ)
    (hnn' : n⁻¹ * n' ∈ Submodule.finiteIdeleStabilizer R) (hmn' : m * n' = n' * m) (x : ℍ𝔸) :
    x ∈ Submodule.finiteAdeleBox (meetOrder (meetOrder R m) n') ↔
      x ∈ Submodule.finiteAdeleBox (meetOrder R n) ∧
        ((m⁻¹ : (ℍ𝔸)ˣ) : ℍ𝔸) * x * (m : ℍ𝔸) ∈ Submodule.finiteAdeleBox (meetOrder R n) := by
  have hR' : QuaternionAlgebra.IsOrder (meetOrder R m) := GOODEQ.isOrder_meetOrder hR m

  have key : ∀ y : ℍ𝔸, ((n'⁻¹ : (ℍ𝔸)ˣ) : ℍ𝔸) * y * (n' : ℍ𝔸) ∈ Submodule.finiteAdeleBox R ↔
      ((n⁻¹ : (ℍ𝔸)ˣ) : ℍ𝔸) * y * (n : ℍ𝔸) ∈ Submodule.finiteAdeleBox R := by
    intro y
    have e : ((n'⁻¹ : (ℍ𝔸)ˣ) : ℍ𝔸) * y * (n' : ℍ𝔸) =
        (((n⁻¹ * n')⁻¹ : (ℍ𝔸)ˣ) : ℍ𝔸) * (((n⁻¹ : (ℍ𝔸)ˣ) : ℍ𝔸) * y * (n : ℍ𝔸)) * ((n⁻¹ * n' : (ℍ𝔸)ˣ) : ℍ𝔸) := by
      simp only [mul_inv_rev, inv_inv, Units.val_mul, mul_assoc, Units.mul_inv_cancel_left]
    rw [e]
    exact conj_unit_mem_box_iff hR hnn' _
  rw [mem_box_meetOrder_iff hR', mem_box_meetOrder_iff hR, mem_box_meetOrder_iff hR, mem_box_meetOrder_iff hR,
    mem_box_meetOrder_iff hR]

  have hcomm : ((m⁻¹ : (ℍ𝔸)ˣ) : ℍ𝔸) * (((n'⁻¹ : (ℍ𝔸)ˣ) : ℍ𝔸) * x * (n' : ℍ𝔸)) * (m : ℍ𝔸) =
      ((n'⁻¹ : (ℍ𝔸)ˣ) : ℍ𝔸) * (((m⁻¹ : (ℍ𝔸)ˣ) : ℍ𝔸) * x * (m : ℍ𝔸)) * (n' : ℍ𝔸) := by
    have h1 : ((n' : (ℍ𝔸)ˣ) : ℍ𝔸) * (m : ℍ𝔸) = (m : ℍ𝔸) * (n' : ℍ𝔸) := by
      rw [← Units.val_mul, ← Units.val_mul, hmn']
    have h2 : ((m⁻¹ : (ℍ𝔸)ˣ) : ℍ𝔸) * ((n'⁻¹ : (ℍ𝔸)ˣ) : ℍ𝔸) = ((n'⁻¹ : (ℍ𝔸)ˣ) : ℍ𝔸) * ((m⁻¹ : (ℍ𝔸)ˣ) : ℍ𝔸) := by
      rw [← Units.val_mul, ← Units.val_mul, ← mul_inv_rev, ← mul_inv_rev, hmn']
    simp only [mul_assoc]
    rw [← mul_assoc ((m⁻¹ : (ℍ𝔸)ˣ) : ℍ𝔸), h2, mul_assoc, h1]
  rw [hcomm, key, key]
  tauto

theorem mem_stab_tower_iff' {R : Submodule ℤ ℍ[ℚ, a, b]} (hR : QuaternionAlgebra.IsOrder R) (n m n' : (ℍ𝔸)ˣ)
    (hnn' : n⁻¹ * n' ∈ Submodule.finiteIdeleStabilizer R) (hmn' : m * n' = n' * m) (u : (ℍ𝔸)ˣ) :
    u ∈ Submodule.finiteIdeleStabilizer (meetOrder (meetOrder R m) n') ↔
      u ∈ Submodule.finiteIdeleStabilizer (meetOrder R n) ∧
        m⁻¹ * u * m ∈ Submodule.finiteIdeleStabilizer (meetOrder R n) := by
  have hS : QuaternionAlgebra.IsOrder (meetOrder R n) := GOODEQ.isOrder_meetOrder hR n
  have hS' : QuaternionAlgebra.IsOrder (meetOrder (meetOrder R m) n') :=
    GOODEQ.isOrder_meetOrder (GOODEQ.isOrder_meetOrder hR m) n'
  rw [HeckeLocal.mem_stabilizer_iff hS', HeckeLocal.mem_stabilizer_iff hS, HeckeLocal.mem_stabilizer_iff hS,
    mem_box_tower_iff hR n m n' hnn' hmn', mem_box_tower_iff hR n m n' hnn' hmn']
  simp only [Units.val_mul, mul_inv_rev, inv_inv, Units.val_inv_eq_inv_val, mul_assoc]
  tauto

theorem stab_tower_le' {R : Submodule ℤ ℍ[ℚ, a, b]} (hR : QuaternionAlgebra.IsOrder R) (n m n' : (ℍ𝔸)ˣ)
    (hnn' : n⁻¹ * n' ∈ Submodule.finiteIdeleStabilizer R) (hmn' : m * n' = n' * m) :
    Submodule.finiteIdeleStabilizer (meetOrder (meetOrder R m) n') ≤ Submodule.finiteIdeleStabilizer (meetOrder R n) :=
  fun u hu => ((mem_stab_tower_iff' hR n m n' hnn' hmn' u).mp hu).1

theorem conj_stab_tower_le' {R : Submodule ℤ ℍ[ℚ, a, b]} (hR : QuaternionAlgebra.IsOrder R) (n m n' : (ℍ𝔸)ˣ)
    (hnn' : n⁻¹ * n' ∈ Submodule.finiteIdeleStabilizer R) (hmn' : m * n' = n' * m) (w : (ℍ𝔸)ˣ)
    (hw : w ∈ Submodule.finiteIdeleStabilizer (meetOrder (meetOrder R m) n')) :
    m⁻¹ * w * m ∈ Submodule.finiteIdeleStabilizer (meetOrder R n) :=
  ((mem_stab_tower_iff' hR n m n' hnn' hmn' w).mp hw).2

end Tower

section Central

variable {a b : ℚ}

local notation "ℍ𝔸" => ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ

theorem finiteIdeleDiagonal_ratUnit_comm (c : ℚˣ) (y : (ℍ𝔸)ˣ) :
    y * Submodule.finiteIdeleDiagonal ℍ[ℚ, a, b] (Units.map (algebraMap ℚ ℍ[ℚ, a, b]).toMonoidHom c) =
      Submodule.finiteIdeleDiagonal ℍ[ℚ, a, b] (Units.map (algebraMap ℚ ℍ[ℚ, a, b]).toMonoidHom c) * y := by
  apply Units.ext
  rw [Units.val_mul, Units.val_mul, Submodule.val_finiteIdeleDiagonal_apply]
  show (y : ℍ𝔸) * ((algebraMap ℚ ℍ[ℚ, a, b] (c : ℚ)) ⊗ₜ[ℚ] (1 : FiniteAdeleRing (𝓞 ℚ) ℚ)) =
    ((algebraMap ℚ ℍ[ℚ, a, b] (c : ℚ)) ⊗ₜ[ℚ] (1 : FiniteAdeleRing (𝓞 ℚ) ℚ)) * (y : ℍ𝔸)
  rw [← Algebra.TensorProduct.algebraMap_apply, ← Algebra.commutes]

theorem classSet_mk_mul_ratUnit (U : Subgroup (ℍ𝔸)ˣ) (x : (ℍ𝔸)ˣ) (c : ℚˣ) :
    ClassSet.mk U (x * Submodule.finiteIdeleDiagonal ℍ[ℚ, a, b] (Units.map (algebraMap ℚ ℍ[ℚ, a, b]).toMonoidHom c)) =
      ClassSet.mk U x := by
  rw [finiteIdeleDiagonal_ratUnit_comm]
  exact ClassSet.mk_diagonal_mul _ x

end Central

section Entry

variable {a b : ℚ}

local notation "ℍ𝔸" => ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ

noncomputable def unitGroupAt (U₀ : Subgroup (ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) (x : (ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) : Subgroup (ℍ[ℚ, a, b])ˣ :=
  U₀.comap ((MulAut.conj x⁻¹).toMonoidHom.comp (Submodule.finiteIdeleDiagonal ℍ[ℚ, a, b]))

theorem mem_unitGroupAt_iff (U₀ : Subgroup (ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) (x : (ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) (γ : (ℍ[ℚ, a, b])ˣ) :
    γ ∈ unitGroupAt U₀ x ↔ x⁻¹ * Submodule.finiteIdeleDiagonal ℍ[ℚ, a, b] γ * x ∈ U₀ := by
  rw [unitGroupAt, Subgroup.mem_comap, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]

variable (U₀ U₁ : Subgroup (ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) (g : (ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ)
  (hU₁ : ∀ u : (ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ, u ∈ U₁ ↔ u ∈ U₀ ∧ g⁻¹ * u * g ∈ U₀)

include hU₁ in
theorem le_of_level : U₁ ≤ U₀ := fun u hu => ((hU₁ u).mp hu).1

include hU₁ in
theorem conj_mem_of_level {w : (ℍ𝔸)ˣ} (hw : w ∈ U₁) : g⁻¹ * w * g ∈ U₀ := ((hU₁ w).mp hw).2

include hU₁ in

theorem mk_out_mul_eq_mk_mul (y : (ℍ𝔸)ˣ) :
    ClassSet.mk U₀ ((ClassSet.mk U₁ y).out * g) = ClassSet.mk U₀ (y * g) := by
  obtain ⟨h, k, hh, hk, hout⟩ := DoubleCoset.mk_out_eq_mul (Submodule.finiteIdeleDiagonal ℍ[ℚ, a, b]).range U₁ y
  rw [show (ClassSet.mk U₁ y).out = h * y * k from hout]
  have e : h * y * k * g = h * (y * g) * (g⁻¹ * k * g) := by group
  rw [e]
  exact ((DoubleCoset.eq _ _ _ _).mpr ⟨h, hh, g⁻¹ * k * g, conj_mem_of_level U₀ U₁ g hU₁ hk, rfl⟩).symm

theorem exists_mem_mk_mul_eq_of_forget_eq (j : ClassSet U₀) (e : ClassSet U₁)
    (he : classSetForget U₁ U₀ e = j) : ∃ u ∈ U₀, ClassSet.mk U₁ (j.out * u) = e := by
  have h1 : ClassSet.mk U₀ j.out = ClassSet.mk U₀ e.out := by
    rw [show ClassSet.mk U₀ e.out = j from he]
    exact DoubleCoset.out_eq' _ _ j
  obtain ⟨h, hh, u, hu, heo⟩ := (DoubleCoset.eq _ _ _ _).mp h1
  obtain ⟨δ, rfl⟩ := MonoidHom.mem_range.mp hh
  refine ⟨u, hu, ?_⟩
  have e2 : j.out * u = Submodule.finiteIdeleDiagonal ℍ[ℚ, a, b] δ⁻¹ * e.out := by
    rw [heo, map_inv]; group
  rw [e2, ClassSet.mk_diagonal_mul]
  exact DoubleCoset.out_eq' _ _ e

theorem forget_mk_mul (j : ClassSet U₀) (u : (ℍ𝔸)ˣ) (hu : u ∈ U₀) (hle : U₁ ≤ U₀) :
    classSetForget U₁ U₀ (ClassSet.mk U₁ (j.out * u)) = j := by
  show ClassSet.mk U₀ (ClassSet.mk U₁ (j.out * u)).out = j
  obtain ⟨h, k, hh, hk, hout⟩ := DoubleCoset.mk_out_eq_mul (Submodule.finiteIdeleDiagonal ℍ[ℚ, a, b]).range U₁ (j.out * u)
  rw [show (ClassSet.mk U₁ (j.out * u)).out = h * (j.out * u) * k from hout]
  have e : h * (j.out * u) * k = h * j.out * (u * k) := by group
  rw [e]
  exact ((DoubleCoset.eq _ _ _ _).mpr ⟨h, hh, u * k, mul_mem hu (hle hk), rfl⟩).symm.trans (DoubleCoset.out_eq' _ _ j)

include hU₁ in

theorem mk_mul_eq_mk_mul_iff (j : ClassSet U₀) (u v : (ℍ𝔸)ˣ) (hu : u ∈ U₀) (hv : v ∈ U₀) :
    ClassSet.mk U₁ (j.out * u) = ClassSet.mk U₁ (j.out * v) ↔
      ∃ γ : (ℍ[ℚ, a, b])ˣ, j.out⁻¹ * Submodule.finiteIdeleDiagonal ℍ[ℚ, a, b] γ * j.out ∈ U₀ ∧
        ∃ w ∈ U₁, j.out⁻¹ * Submodule.finiteIdeleDiagonal ℍ[ℚ, a, b] γ * j.out * u * w = v := by
  constructor
  · intro h
    obtain ⟨d, hd, w, hw, hvw⟩ := (DoubleCoset.eq _ _ _ _).mp h
    obtain ⟨γ, rfl⟩ := MonoidHom.mem_range.mp hd
    have hv' : v = j.out⁻¹ * Submodule.finiteIdeleDiagonal ℍ[ℚ, a, b] γ * j.out * u * w := by
      have := congrArg (fun z => j.out⁻¹ * z) hvw
      simp only [inv_mul_cancel_left] at this
      rw [this]; group
    refine ⟨γ, ?_, w, hw, hv'.symm⟩
    have e : j.out⁻¹ * Submodule.finiteIdeleDiagonal ℍ[ℚ, a, b] γ * j.out = v * w⁻¹ * u⁻¹ := by
      rw [hv']; group
    rw [e]
    exact mul_mem (mul_mem hv (inv_mem (le_of_level U₀ U₁ g hU₁ hw))) (inv_mem hu)
  · rintro ⟨γ, -, w, hw, hvw⟩
    refine (DoubleCoset.eq _ _ _ _).mpr ⟨Submodule.finiteIdeleDiagonal ℍ[ℚ, a, b] γ,
      MonoidHom.mem_range.mpr ⟨γ, rfl⟩, w, hw, ?_⟩
    rw [← hvw]; group

theorem unitGroupAt_mul_le (j : ClassSet U₀) (u : (ℍ𝔸)ˣ) (hu : u ∈ U₀) (hle : U₁ ≤ U₀) :
    unitGroupAt U₁ (j.out * u) ≤ unitGroupAt U₀ j.out := by
  intro γ hγ
  rw [mem_unitGroupAt_iff] at hγ ⊢
  have h1 : u⁻¹ * (j.out⁻¹ * Submodule.finiteIdeleDiagonal ℍ[ℚ, a, b] γ * j.out) * u ∈ U₀ := by
    have e : u⁻¹ * (j.out⁻¹ * Submodule.finiteIdeleDiagonal ℍ[ℚ, a, b] γ * j.out) * u =
        (j.out * u)⁻¹ * Submodule.finiteIdeleDiagonal ℍ[ℚ, a, b] γ * (j.out * u) := by group
    rw [e]; exact hle hγ
  have h2 := mul_mem (mul_mem hu h1) (inv_mem hu)
  have e2 : u * (u⁻¹ * (j.out⁻¹ * Submodule.finiteIdeleDiagonal ℍ[ℚ, a, b] γ * j.out) * u) * u⁻¹ =
      j.out⁻¹ * Submodule.finiteIdeleDiagonal ℍ[ℚ, a, b] γ * j.out := by group
  rwa [e2] at h2

include hU₁ in

theorem natCard_heckeIncidence_eq_natCard_quot (T : Set (ℍ𝔸)ˣ)
    (hT : ∀ c : (ℍ𝔸)ˣ ⧸ U₀, (∃ t ∈ T, (t : (ℍ𝔸)ˣ ⧸ U₀) = c) ↔ ∃ u ∈ U₀, ((u * g : (ℍ𝔸)ˣ) : (ℍ𝔸)ˣ ⧸ U₀) = c)
    (x : (ℍ𝔸)ˣ) (i : ClassSet U₀) :
    Nat.card (HeckeIncidence U₀ T x i) =
      Nat.card {c : ↥U₀ ⧸ U₁.subgroupOf U₀ // ClassSet.mk U₀ (x * (c.out : ↥U₀) * g) = i} := by
  classical

  let ψ : ↥U₀ → (ℍ𝔸)ˣ ⧸ U₀ := fun u => (((u : (ℍ𝔸)ˣ) * g : (ℍ𝔸)ˣ) : (ℍ𝔸)ˣ ⧸ U₀)
  have hψ : ∀ u u' : ↥U₀, ψ u = ψ u' ↔ u⁻¹ * u' ∈ U₁.subgroupOf U₀ := by
    intro u u'
    rw [Subgroup.mem_subgroupOf, QuotientGroup.eq, hU₁]
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, mul_inv_rev]
    constructor
    · intro h
      refine ⟨mul_mem (inv_mem u.2) u'.2, ?_⟩
      have e : g⁻¹ * ((u : (ℍ𝔸)ˣ)⁻¹ * (u' : (ℍ𝔸)ˣ)) * g = g⁻¹ * (u : (ℍ𝔸)ˣ)⁻¹ * ((u' : (ℍ𝔸)ˣ) * g) := by group
      rw [e]; exact h
    · intro h
      have e : g⁻¹ * (u : (ℍ𝔸)ˣ)⁻¹ * ((u' : (ℍ𝔸)ˣ) * g) = g⁻¹ * ((u : (ℍ𝔸)ˣ)⁻¹ * (u' : (ℍ𝔸)ˣ)) * g := by group
      rw [e]; exact h.2

  have hcl : ∀ (y k : (ℍ𝔸)ˣ), k ∈ U₀ → ClassSet.mk U₀ (x * (y * k)) = ClassSet.mk U₀ (x * y) := by
    intro y k hk; rw [← mul_assoc]; exact ClassSet.mk_mul_of_mem _ _ hk

  have hout : ∀ u : ↥U₀, ∃ w : ↥U₀, (w : (ℍ𝔸)ˣ) ∈ U₁ ∧
      ((QuotientGroup.mk u : ↥U₀ ⧸ U₁.subgroupOf U₀).out : ↥U₀) = u * w := by
    intro u
    obtain ⟨w, hw⟩ := QuotientGroup.mk_out_eq_mul (U₁.subgroupOf U₀) u
    exact ⟨w, Subgroup.mem_subgroupOf.mp w.2, hw⟩

  have hF : ∀ q : {c : ↥U₀ ⧸ U₁.subgroupOf U₀ // ClassSet.mk U₀ (x * (c.out : ↥U₀) * g) = i},
      ∃ t ∈ T, (t : (ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ ⧸ U₀) = ψ q.1.out ∧ ClassSet.mk U₀ (x * t) = i := by
    intro q
    obtain ⟨t, ht, htc⟩ := (hT (ψ q.1.out)).mpr ⟨q.1.out, q.1.out.2, rfl⟩
    refine ⟨t, ht, htc, ?_⟩
    have hk : ((q.1.out : (ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) * g)⁻¹ * t ∈ U₀ := QuotientGroup.eq.mp htc.symm
    have e : t = (q.1.out : (ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) * g * (((q.1.out : (ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) * g)⁻¹ * t) := by group
    rw [e, hcl _ _ hk, ← mul_assoc]
    exact q.2
  let F : {c : ↥U₀ ⧸ U₁.subgroupOf U₀ // ClassSet.mk U₀ (x * (c.out : ↥U₀) * g) = i} → HeckeIncidence U₀ T x i :=
    fun q => ⟨ψ q.1.out, hF q⟩
  have hFval : ∀ q, (F q).1 = ψ q.1.out := fun q => rfl
  have hinj : Function.Injective F := by
    intro q q' h
    have h1 : ψ q.1.out = ψ q'.1.out := by rw [← hFval, ← hFval, h]
    rw [hψ] at h1
    apply Subtype.ext
    rw [← QuotientGroup.out_eq' q.1, ← QuotientGroup.out_eq' q'.1]
    exact QuotientGroup.eq.mpr h1
  have hsurj : Function.Surjective F := by
    rintro ⟨c, t, ht, htc, hti⟩
    obtain ⟨u, hu, huc⟩ := (hT c).mp ⟨t, ht, htc⟩
    obtain ⟨w, hw1, hw⟩ := hout ⟨u, hu⟩
    have hval : ClassSet.mk U₀ (x * (((QuotientGroup.mk (⟨u, hu⟩ : ↥U₀) : ↥U₀ ⧸ U₁.subgroupOf U₀).out : ↥U₀) : (ℍ𝔸)ˣ) * g) = i := by
      rw [hw, Subgroup.coe_mul]
      have e : x * ((u : (ℍ𝔸)ˣ) * (w : (ℍ𝔸)ˣ)) * g = x * (u * g * (g⁻¹ * (w : (ℍ𝔸)ˣ) * g)) := by
        group
      rw [e, hcl _ _ (conj_mem_of_level U₀ U₁ g hU₁ hw1)]

      have hk : (u * g)⁻¹ * t ∈ U₀ := QuotientGroup.eq.mp (huc.trans htc.symm)
      have e2 : x * (u * g) = x * (t * ((u * g)⁻¹ * t)⁻¹) := by group
      rw [e2, hcl _ _ (inv_mem hk)]
      exact hti
    refine ⟨⟨QuotientGroup.mk ⟨u, hu⟩, hval⟩, ?_⟩
    apply Subtype.ext
    rw [hFval]
    show ψ _ = c
    rw [← huc]
    show ψ _ = ψ ⟨u, hu⟩
    rw [hψ, hw]
    rw [show (⟨u, hu⟩ * w : ↥U₀)⁻¹ * ⟨u, hu⟩ = w⁻¹ from by group]
    exact inv_mem (Subgroup.mem_subgroupOf.mpr hw1)
  symm
  exact Nat.card_congr (Equiv.ofBijective F ⟨hinj, hsurj⟩)

end Entry

section OrbitFibre

open MulAction

variable {Γ X Y : Type*} [Group Γ] [MulAction Γ X] [Fintype X] [DecidableEq Y]

theorem card_fibre_eq_sum_orbits [Fintype (orbitRel.Quotient Γ X)] [DecidableEq (orbitRel.Quotient Γ X)]
    (β : X → Y) (hβ : ∀ (γ : Γ) (x : X), β (γ • x) = β x) (y : Y) :
    (univ.filter (fun x : X => β x = y)).card =
      ∑ O ∈ univ.filter (fun O : orbitRel.Quotient Γ X => β O.out = y),
        (univ.filter (fun x : X => Quotient.mk (orbitRel Γ X) x = O)).card := by
  classical

  have hconst : ∀ x : X, β (Quotient.mk (orbitRel Γ X) x).out = β x := by
    intro x
    have h : (orbitRel Γ X) (Quotient.mk (orbitRel Γ X) x).out x := Quotient.mk_out x
    obtain ⟨γ, hγ⟩ := h
    rw [← hγ]
    exact hβ γ x
  rw [card_eq_sum_ones, ← sum_fiberwise_of_maps_to (g := Quotient.mk (orbitRel Γ X))
    (t := univ.filter (fun O : orbitRel.Quotient Γ X => β O.out = y))
    (fun x hx => by rw [mem_filter] at hx ⊢; exact ⟨mem_univ _, by rw [hconst]; exact hx.2⟩)]
  refine sum_congr rfl fun O hO => ?_
  rw [card_eq_sum_ones, filter_filter]
  refine sum_congr (filter_congr fun x _ => ?_) fun _ _ => rfl
  constructor
  · exact fun h => h.2
  · intro h
    refine ⟨?_, h⟩
    rw [← hconst x, h]
    exact (mem_filter.mp hO).2

omit [Fintype X] in

theorem card_orbit_eq_index [Fintype Γ] (x : X) [Fintype (orbit Γ x)] :
    Fintype.card (orbit Γ x) = (stabilizer Γ x).index := by
  rw [← Nat.card_eq_fintype_card, Subgroup.index_eq_card, Nat.card_congr (orbitEquivQuotientStabilizer Γ x)]

theorem card_filter_mk_eq_index [Fintype Γ] [DecidableEq (orbitRel.Quotient Γ X)] (x : X) :
    (univ.filter (fun z : X => Quotient.mk (orbitRel Γ X) z = Quotient.mk (orbitRel Γ X) x)).card =
      (stabilizer Γ x).index := by
  classical
  rw [← card_orbit_eq_index x]
  refine (Fintype.card_of_subtype _ fun z => ?_).symm
  rw [mem_filter, mem_orbit_iff]
  simp only [mem_univ, true_and]
  rw [Quotient.eq]
  exact orbitRel_apply.trans mem_orbit_iff

end OrbitFibre

section Entry6

variable {a b : ℚ}

local notation "ℍ𝔸" => ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ

open MulAction in

theorem sum_idx_filter_forget_shift_eq_natCard
    (U₀ U₁ : Subgroup (ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) (g : (ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ)
    (hU₁ : ∀ u : (ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ, u ∈ U₁ ↔ u ∈ U₀ ∧ g⁻¹ * u * g ∈ U₀)
    [Fintype (ClassSet U₁)] [DecidableEq (ClassSet U₀)] [DecidableEq (ClassSet U₁)]
    [(U₁.subgroupOf U₀).FiniteIndex]
    (j i : ClassSet U₀) (_hfin : Finite ↥(unitGroupAt U₀ j.out))
    (idx : ClassSet U₁ → ℕ)
    (hidx : ∀ u ∈ U₀, idx (ClassSet.mk U₁ (j.out * u)) =
      ((unitGroupAt U₁ (j.out * u)).subgroupOf (unitGroupAt U₀ j.out)).index) :
    (∑ e ∈ Finset.univ.filter (fun e : ClassSet U₁ => classSetForget U₁ U₀ e = j ∧ ClassSet.mk U₀ (e.out * g) = i),
        idx e) =
      Nat.card {c : ↥U₀ ⧸ U₁.subgroupOf U₀ // ClassSet.mk U₀ (j.out * (c.out : ↥U₀) * g) = i} := by
  classical
  have hle : U₁ ≤ U₀ := le_of_level U₀ U₁ g hU₁

  let Q := ↥U₀ ⧸ U₁.subgroupOf U₀
  haveI : Fintype Q := Fintype.ofFinite Q
  let Γ : Subgroup (ℍ[ℚ, a, b])ˣ := unitGroupAt U₀ j.out

  let Φ : (ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ → ClassSet U₁ := fun v => ClassSet.mk U₁ (j.out * v)
  let Ψ : (ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ → ClassSet U₀ := fun v => ClassSet.mk U₀ (j.out * v * g)
  have hΦ_mul : ∀ (v w : (ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ), w ∈ U₁ → Φ (v * w) = Φ v := fun v w hw => by
    show ClassSet.mk U₁ (j.out * (v * w)) = ClassSet.mk U₁ (j.out * v)
    rw [← mul_assoc]; exact ClassSet.mk_mul_of_mem _ _ hw
  have hΨ_mul : ∀ (v w : (ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ), w ∈ U₁ → Ψ (v * w) = Ψ v := fun v w hw => by
    show ClassSet.mk U₀ (j.out * (v * w) * g) = ClassSet.mk U₀ (j.out * v * g)
    have e : j.out * (v * w) * g = j.out * v * g * (g⁻¹ * w * g) := by group
    rw [e]; exact ClassSet.mk_mul_of_mem _ _ (conj_mem_of_level U₀ U₁ g hU₁ hw)

  have hrep : ∀ v : ↥U₀, ∃ w : ↥U₀, (w : (ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) ∈ U₁ ∧ ((QuotientGroup.mk v : Q).out : ↥U₀) = v * w := by
    intro v
    have h := QuotientGroup.mk_out_eq_mul (U₁.subgroupOf U₀) v
    exact ⟨h.choose, Subgroup.mem_subgroupOf.mp h.choose.2, h.choose_spec⟩
  let θ : Q → ClassSet U₁ := fun q => Φ (q.out : ↥U₀)
  let β' : Q → ClassSet U₀ := fun q => Ψ (q.out : ↥U₀)
  have hθ_mk : ∀ v : ↥U₀, θ (QuotientGroup.mk v) = Φ v := by
    intro v
    have h := hrep v
    show Φ _ = Φ v
    rw [h.choose_spec.2, Subgroup.coe_mul]
    exact hΦ_mul _ _ h.choose_spec.1
  have hβ'_mk : ∀ v : ↥U₀, β' (QuotientGroup.mk v) = Ψ v := by
    intro v
    have h := hrep v
    show Ψ _ = Ψ v
    rw [h.choose_spec.2, Subgroup.coe_mul]
    exact hΨ_mul _ _ h.choose_spec.1

  have hβ'_θ : ∀ q : Q, β' q = ClassSet.mk U₀ ((θ q).out * g) := by
    intro q
    show ClassSet.mk U₀ (j.out * _ * g) = ClassSet.mk U₀ ((ClassSet.mk U₁ (j.out * _)).out * g)
    rw [mk_out_mul_eq_mk_mul U₀ U₁ g hU₁]

  have hθ_forget : ∀ q : Q, classSetForget U₁ U₀ (θ q) = j := fun q =>
    forget_mk_mul U₀ U₁ j _ (q.out : ↥U₀).2 hle

  have hfibre : ∀ v (hv : v ∈ U₀), Nat.card {q : Q // θ q = Φ v} =
      ((unitGroupAt U₁ (j.out * v)).subgroupOf Γ).index := by
    intro v hv

    let ρ : ↥Γ → ↥U₀ := fun γ => ⟨j.out⁻¹ * Submodule.finiteIdeleDiagonal ℍ[ℚ, a, b] γ * j.out,
      (mem_unitGroupAt_iff U₀ j.out γ).mp γ.2⟩

    let F : ↥Γ → {q : Q // θ q = Φ v} := fun γ => ⟨QuotientGroup.mk (ρ γ * ⟨v, hv⟩), by
      rw [hθ_mk, Subgroup.coe_mul]
      exact (mk_mul_eq_mk_mul_iff U₀ U₁ g hU₁ j _ _ (mul_mem (ρ γ).2 hv) hv).mpr
        ⟨(γ : (ℍ[ℚ, a, b])ˣ)⁻¹, by
            have h0 := inv_mem ((mem_unitGroupAt_iff U₀ j.out γ).mp γ.2)
            have e0 : (j.out⁻¹ * Submodule.finiteIdeleDiagonal ℍ[ℚ, a, b] γ * j.out)⁻¹ =
                j.out⁻¹ * (Submodule.finiteIdeleDiagonal ℍ[ℚ, a, b] γ)⁻¹ * j.out := by group
            rw [map_inv]; rwa [e0] at h0, 1, one_mem _,
          by rw [map_inv, mul_one]; show _ * ((j.out⁻¹ * _ * j.out) * v) = v; group⟩⟩
    have hFsurj : Function.Surjective F := by
      rintro ⟨q, hq⟩

      have hq' : ClassSet.mk U₁ (j.out * (q.out : ↥U₀)) = ClassSet.mk U₁ (j.out * v) := hq
      have h4 := (mk_mul_eq_mk_mul_iff U₀ U₁ g hU₁ j _ _ (q.out : ↥U₀).2 hv).mp hq'
      let γ : (ℍ[ℚ, a, b])ˣ := h4.choose
      have hγ : j.out⁻¹ * Submodule.finiteIdeleDiagonal ℍ[ℚ, a, b] γ * j.out ∈ U₀ := h4.choose_spec.1
      have hw := h4.choose_spec.2
      let w : (ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ := hw.choose
      have hw1 : w ∈ U₁ := hw.choose_spec.1
      have hwv : j.out⁻¹ * Submodule.finiteIdeleDiagonal ℍ[ℚ, a, b] γ * j.out * (q.out : ↥U₀) * w = v :=
        hw.choose_spec.2
      have hγΓ : γ⁻¹ ∈ Γ := by
        rw [mem_unitGroupAt_iff, map_inv]
        have := inv_mem hγ
        have e : (j.out⁻¹ * Submodule.finiteIdeleDiagonal ℍ[ℚ, a, b] γ * j.out)⁻¹ =
            j.out⁻¹ * (Submodule.finiteIdeleDiagonal ℍ[ℚ, a, b] γ)⁻¹ * j.out := by group
        rwa [e] at this
      refine ⟨⟨γ⁻¹, hγΓ⟩, ?_⟩
      apply Subtype.ext
      show (QuotientGroup.mk (ρ ⟨γ⁻¹, hγΓ⟩ * ⟨v, hv⟩) : Q) = q
      rw [← QuotientGroup.out_eq' q]
      apply QuotientGroup.eq.mpr
      rw [Subgroup.mem_subgroupOf]
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      show ((j.out⁻¹ * Submodule.finiteIdeleDiagonal ℍ[ℚ, a, b] γ⁻¹ * j.out) * v)⁻¹ * (q.out : ↥U₀) ∈ U₁
      have e : ((j.out⁻¹ * Submodule.finiteIdeleDiagonal ℍ[ℚ, a, b] γ⁻¹ * j.out) * v)⁻¹ *
          ((q.out : ↥U₀) : (ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) = w⁻¹ := by
        rw [← hwv, map_inv]; group
      rw [e]; exact inv_mem hw1

    have hFeq : ∀ γ γ' : ↥Γ, F γ = F γ' ↔ γ⁻¹ * γ' ∈ (unitGroupAt U₁ (j.out * v)).subgroupOf Γ := by
      intro γ γ'
      rw [Subgroup.mem_subgroupOf, mem_unitGroupAt_iff, Subtype.ext_iff]
      show (QuotientGroup.mk (ρ γ * ⟨v, hv⟩) : Q) = QuotientGroup.mk (ρ γ' * ⟨v, hv⟩) ↔ _
      rw [QuotientGroup.eq, Subgroup.mem_subgroupOf]
      simp only [Subgroup.coe_mul, Subgroup.coe_inv, map_mul, map_inv]
      have e : ((j.out⁻¹ * Submodule.finiteIdeleDiagonal ℍ[ℚ, a, b] γ * j.out) * v)⁻¹ *
          ((j.out⁻¹ * Submodule.finiteIdeleDiagonal ℍ[ℚ, a, b] γ' * j.out) * v) =
          (j.out * v)⁻¹ *
            ((Submodule.finiteIdeleDiagonal ℍ[ℚ, a, b] γ)⁻¹ * Submodule.finiteIdeleDiagonal ℍ[ℚ, a, b] γ') *
            (j.out * v) := by group
      rw [e]

    rw [Subgroup.index]
    symm
    refine Nat.card_congr (Equiv.ofBijective
      (Quotient.lift (s := QuotientGroup.leftRel ((unitGroupAt U₁ (j.out * v)).subgroupOf Γ)) F
        (fun γ γ' h => (hFeq γ γ').mpr (QuotientGroup.leftRel_apply.mp h))) ⟨?_, ?_⟩)
    · intro p p' h
      induction p using QuotientGroup.induction_on with
      | H γ =>
      induction p' using QuotientGroup.induction_on with
      | H γ' =>
      exact Quotient.sound (QuotientGroup.leftRel_apply.mpr ((hFeq γ γ').mp h))
    · intro y
      obtain ⟨γ, hγ⟩ := hFsurj y
      exact ⟨QuotientGroup.mk γ, hγ⟩

  have hLHS : Nat.card {c : Q // ClassSet.mk U₀ (j.out * (c.out : ↥U₀) * g) = i} =
      (Finset.univ.filter (fun q : Q => β' q = i)).card := by
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  rw [hLHS, Finset.card_eq_sum_card_fiberwise (f := θ) (t := Finset.univ) (fun _ _ => Finset.mem_univ _)]
  rw [Finset.sum_filter]
  symm
  refine Finset.sum_congr rfl fun e _ => ?_

  by_cases he : classSetForget U₁ U₀ e = j ∧ ClassSet.mk U₀ (e.out * g) = i
  · rw [if_pos he]

    have h3 := exists_mem_mk_mul_eq_of_forget_eq U₀ U₁ j e he.1
    let u : (ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ := h3.choose
    have hu : u ∈ U₀ := h3.choose_spec.1
    have hue : Φ u = e := h3.choose_spec.2
    rw [Finset.filter_filter]
    have hset : (Finset.univ.filter fun q : Q => β' q = i ∧ θ q = e) = Finset.univ.filter fun q : Q => θ q = Φ u := by
      apply Finset.filter_congr
      intro q _
      constructor
      · intro h; rw [h.2, hue]
      · intro h
        refine ⟨?_, by rw [h, hue]⟩
        rw [hβ'_θ, h]
        show ClassSet.mk U₀ ((Φ u).out * g) = i
        rw [hue]; exact he.2
    rw [hset, ← hue, hidx u hu, ← hfibre u hu, Nat.card_eq_fintype_card, Fintype.card_subtype]
  · rw [if_neg he]
    rw [Finset.card_eq_zero, Finset.filter_filter, Finset.filter_eq_empty_iff]
    intro q _ hq
    apply he
    refine ⟨by rw [← hq.2]; exact hθ_forget q, ?_⟩
    rw [← hq.2, ← hβ'_θ]; exact hq.1

end Entry6

section Transport

variable {a b : ℚ}

theorem classSetForget_mk {U U' : Subgroup (ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ} (hle : U ≤ U') (v : (ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) :
    classSetForget U U' (ClassSet.mk U v) = ClassSet.mk U' v := by
  show ClassSet.mk U' (ClassSet.mk U v).out = ClassSet.mk U' v
  obtain ⟨h, k, hh, hk, hout⟩ := DoubleCoset.mk_out_eq_mul (Submodule.finiteIdeleDiagonal ℍ[ℚ, a, b]).range U v
  rw [show (ClassSet.mk U v).out = h * v * k from hout]
  exact ((DoubleCoset.eq _ _ _ _).mpr ⟨h, hh, k, hle hk, rfl⟩).symm

variable (U₀ U₁ U₂ : Subgroup (ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) (s : (ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ)
  (hU₁ : ∀ u : (ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ, u ∈ U₁ ↔ u ∈ U₀ ∧ s⁻¹ * u * s ∈ U₀)
  (hU₂ : ∀ u : (ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ, u ∈ U₂ ↔ u ∈ U₀ ∧ s * u * s⁻¹ ∈ U₀)

include hU₁ hU₂ in
theorem conj_mem_U₂_of_mem_U₁ {w : (ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ} (hw : w ∈ U₁) : s⁻¹ * w * s ∈ U₂ := by
  rw [hU₂]
  refine ⟨((hU₁ w).mp hw).2, ?_⟩
  rw [show s * (s⁻¹ * w * s) * s⁻¹ = w from by group]
  exact ((hU₁ w).mp hw).1

include hU₁ hU₂ in
theorem conj_mem_U₁_of_mem_U₂ {w : (ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ} (hw : w ∈ U₂) : s * w * s⁻¹ ∈ U₁ := by
  rw [hU₁]
  refine ⟨((hU₂ w).mp hw).2, ?_⟩
  rw [show s⁻¹ * (s * w * s⁻¹) * s = w from by group]
  exact ((hU₂ w).mp hw).1

noncomputable def transportEquiv : ClassSet U₁ ≃ ClassSet U₂ where
  toFun := Quotient.map' (fun y => y * s) fun y y' h => by
    obtain ⟨c, hc, d, hd, rfl⟩ := DoubleCoset.rel_iff.mp h
    exact DoubleCoset.rel_iff.mpr ⟨c, hc, s⁻¹ * d * s, conj_mem_U₂_of_mem_U₁ U₀ U₁ U₂ s hU₁ hU₂ hd, by group⟩
  invFun := Quotient.map' (fun z => z * s⁻¹) fun z z' h => by
    obtain ⟨c, hc, d, hd, rfl⟩ := DoubleCoset.rel_iff.mp h
    exact DoubleCoset.rel_iff.mpr ⟨c, hc, s * d * s⁻¹, conj_mem_U₁_of_mem_U₂ U₀ U₁ U₂ s hU₁ hU₂ hd, by group⟩
  left_inv := fun e => Quotient.inductionOn' e fun y => by
    show Quotient.mk'' (y * s * s⁻¹) = Quotient.mk'' y
    rw [mul_inv_cancel_right]
  right_inv := fun e => Quotient.inductionOn' e fun z => by
    show Quotient.mk'' (z * s⁻¹ * s) = Quotient.mk'' z
    rw [inv_mul_cancel_right]

theorem transportEquiv_mk (y : (ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) :
    transportEquiv U₀ U₁ U₂ s hU₁ hU₂ (ClassSet.mk U₁ y) = ClassSet.mk U₂ (y * s) := rfl

theorem transportEquiv_symm_mk (z : (ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) :
    (transportEquiv U₀ U₁ U₂ s hU₁ hU₂).symm (ClassSet.mk U₂ z) = ClassSet.mk U₁ (z * s⁻¹) := rfl

include hU₁ hU₂ in

theorem forget_transport (e : ClassSet U₁) :
    classSetForget U₂ U₀ (transportEquiv U₀ U₁ U₂ s hU₁ hU₂ e) = ClassSet.mk U₀ (e.out * s) := by
  have he : e = ClassSet.mk U₁ e.out := (DoubleCoset.out_eq' _ _ e).symm
  conv_lhs => rw [he, transportEquiv_mk]
  exact classSetForget_mk (fun u hu => ((hU₂ u).mp hu).1) _

include hU₁ hU₂ in

theorem shift_transport (e : ClassSet U₁) :
    ClassSet.mk U₀ ((transportEquiv U₀ U₁ U₂ s hU₁ hU₂ e).out * s⁻¹) = classSetForget U₁ U₀ e := by
  have he : e = ClassSet.mk U₁ e.out := (DoubleCoset.out_eq' _ _ e).symm
  conv_lhs => rw [he, transportEquiv_mk]
  show ClassSet.mk U₀ ((ClassSet.mk U₂ (e.out * s)).out * s⁻¹) = ClassSet.mk U₀ e.out
  obtain ⟨h, k, hh, hk, hout⟩ :=
    DoubleCoset.mk_out_eq_mul (Submodule.finiteIdeleDiagonal ℍ[ℚ, a, b]).range U₂ (e.out * s)
  rw [show (ClassSet.mk U₂ (e.out * s)).out = h * (e.out * s) * k from hout]
  rw [show h * (e.out * s) * k * s⁻¹ = h * e.out * (s * k * s⁻¹) from by group]
  exact ((DoubleCoset.eq _ _ _ _).mpr ⟨h, hh, s * k * s⁻¹, ((hU₂ k).mp hk).2, rfl⟩).symm

include hU₁ hU₂ in

theorem unitGroupAt_transport (y : (ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) :
    unitGroupAt U₂ (y * s) = unitGroupAt U₁ y := by
  ext γ
  rw [mem_unitGroupAt_iff, mem_unitGroupAt_iff, hU₂, hU₁]
  rw [show s * ((y * s)⁻¹ * Submodule.finiteIdeleDiagonal ℍ[ℚ, a, b] γ * (y * s)) * s⁻¹ =
      y⁻¹ * Submodule.finiteIdeleDiagonal ℍ[ℚ, a, b] γ * y from by group,
    show (y * s)⁻¹ * Submodule.finiteIdeleDiagonal ℍ[ℚ, a, b] γ * (y * s) =
      s⁻¹ * (y⁻¹ * Submodule.finiteIdeleDiagonal ℍ[ℚ, a, b] γ * y) * s from by group]
  tauto

end Transport

section Scalar2

variable {a b : ℚ}

theorem natCard_quot_shift_eq_of_central (U₀ U₂ : Subgroup (ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) (s : (ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) (c : ℚˣ)
    (x : (ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) (i : ClassSet U₀) :
    Nat.card {q : ↥U₀ ⧸ U₂.subgroupOf U₀ // ClassSet.mk U₀ (x * (q.out : ↥U₀) * s⁻¹) = i} =
      Nat.card {q : ↥U₀ ⧸ U₂.subgroupOf U₀ //
        ClassSet.mk U₀ (x * (q.out : ↥U₀) *
          (Submodule.finiteIdeleDiagonal ℍ[ℚ, a, b] (Units.map (algebraMap ℚ ℍ[ℚ, a, b]).toMonoidHom c) * s⁻¹)) = i} := by
  refine Nat.card_congr (Equiv.subtypeEquivRight fun q => ?_)
  rw [← finiteIdeleDiagonal_ratUnit_comm c s⁻¹, ← mul_assoc, classSet_mk_mul_ratUnit]

end Scalar2

section Bridge

variable {a b : ℚ}

local notation "ℍ𝔸" => ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ

theorem mem_unitGroupAt_stab_iff {Λ : Submodule ℤ ℍ[ℚ, a, b]} (hΛ : QuaternionAlgebra.IsOrder Λ) (x : (ℍ𝔸)ˣ)
    (γ : (ℍ[ℚ, a, b])ˣ) :
    γ ∈ unitGroupAt (Submodule.finiteIdeleStabilizer Λ) x ↔
      (γ : ℍ[ℚ, a, b]) ∈ Submodule.conjByFiniteIdele Λ x ∧ ((γ⁻¹ : (ℍ[ℚ, a, b])ˣ) : ℍ[ℚ, a, b]) ∈ Submodule.conjByFiniteIdele Λ x := by
  rw [mem_unitGroupAt_iff, HeckeLocal.mem_stabilizer_iff hΛ, GOODEQ.mem_conjByFiniteIdele_iff,
    GOODEQ.mem_conjByFiniteIdele_iff]
  simp only [Units.val_mul, mul_inv_rev, inv_inv, Submodule.val_finiteIdeleDiagonal_apply, ← map_inv, Units.val_inv_eq_inv_val]
  simp only [mul_assoc]

noncomputable def isUnitOfEquivUnitGroupAt {Λ : Submodule ℤ ℍ[ℚ, a, b]} (hΛ : QuaternionAlgebra.IsOrder Λ) (x : (ℍ𝔸)ˣ) :
    {u : ℍ[ℚ, a, b] // IsUnitOf (Submodule.conjByFiniteIdele Λ x) u} ≃
      ↥(unitGroupAt (Submodule.finiteIdeleStabilizer Λ) x) where
  toFun p := ⟨⟨p.1, p.2.2.choose, p.2.2.choose_spec.2.1, p.2.2.choose_spec.2.2⟩,
    (mem_unitGroupAt_stab_iff hΛ x _).mpr ⟨p.2.1, p.2.2.choose_spec.1⟩⟩
  invFun γ := ⟨((γ : (ℍ[ℚ, a, b])ˣ) : ℍ[ℚ, a, b]),
    ⟨((mem_unitGroupAt_stab_iff hΛ x _).mp γ.2).1, ((γ : (ℍ[ℚ, a, b])ˣ)⁻¹ : (ℍ[ℚ, a, b])ˣ),
      ((mem_unitGroupAt_stab_iff hΛ x _).mp γ.2).2, (γ : (ℍ[ℚ, a, b])ˣ).mul_inv, (γ : (ℍ[ℚ, a, b])ˣ).inv_mul⟩⟩
  left_inv _ := Subtype.ext rfl
  right_inv _ := Subtype.ext (Units.ext rfl)

theorem natCard_isUnitOf_eq {Λ : Submodule ℤ ℍ[ℚ, a, b]} (hΛ : QuaternionAlgebra.IsOrder Λ) (x : (ℍ𝔸)ˣ) :
    Nat.card {u : ℍ[ℚ, a, b] // IsUnitOf (Submodule.conjByFiniteIdele Λ x) u} =
      Nat.card ↥(unitGroupAt (Submodule.finiteIdeleStabilizer Λ) x) :=
  Nat.card_congr (isUnitOfEquivUnitGroupAt hΛ x)

end Bridge

section AsmHelpers

variable {a b : ℚ}

local notation "ℍ𝔸" => ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ

theorem natCard_unitGroupAt_diag_mul_mul (U₀ : Subgroup (ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) (d : (ℍ[ℚ, a, b])ˣ) (y w : (ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) (hw : w ∈ U₀) :
    Nat.card ↥(unitGroupAt U₀ (Submodule.finiteIdeleDiagonal ℍ[ℚ, a, b] d * y * w)) = Nat.card ↥(unitGroupAt U₀ y) := by
  have key : ∀ γ : (ℍ[ℚ, a, b])ˣ, γ ∈ unitGroupAt U₀ (Submodule.finiteIdeleDiagonal ℍ[ℚ, a, b] d * y * w) ↔
      d⁻¹ * γ * d ∈ unitGroupAt U₀ y := by
    intro γ
    rw [mem_unitGroupAt_iff, mem_unitGroupAt_iff, map_mul, map_mul, map_inv]
    rw [show (Submodule.finiteIdeleDiagonal ℍ[ℚ, a, b] d * y * w)⁻¹ * Submodule.finiteIdeleDiagonal ℍ[ℚ, a, b] γ *
        (Submodule.finiteIdeleDiagonal ℍ[ℚ, a, b] d * y * w) =
        w⁻¹ * (y⁻¹ * ((Submodule.finiteIdeleDiagonal ℍ[ℚ, a, b] d)⁻¹ * Submodule.finiteIdeleDiagonal ℍ[ℚ, a, b] γ *
          Submodule.finiteIdeleDiagonal ℍ[ℚ, a, b] d) * y) * w from by group]
    constructor
    · intro h
      have := mul_mem (mul_mem hw h) (inv_mem hw)
      rwa [show w * (w⁻¹ * (y⁻¹ * ((Submodule.finiteIdeleDiagonal ℍ[ℚ, a, b] d)⁻¹ * Submodule.finiteIdeleDiagonal ℍ[ℚ, a, b] γ *
          Submodule.finiteIdeleDiagonal ℍ[ℚ, a, b] d) * y) * w) * w⁻¹ =
          y⁻¹ * ((Submodule.finiteIdeleDiagonal ℍ[ℚ, a, b] d)⁻¹ * Submodule.finiteIdeleDiagonal ℍ[ℚ, a, b] γ *
            Submodule.finiteIdeleDiagonal ℍ[ℚ, a, b] d) * y from by group] at this
    · intro h
      exact mul_mem (mul_mem (inv_mem hw) h) hw
  exact Nat.card_congr
    { toFun := fun γ => ⟨d⁻¹ * γ * d, (key γ).mp γ.2⟩
      invFun := fun γ => ⟨d * γ * d⁻¹, (key _).mpr (by
        rw [show d⁻¹ * (d * (γ : (ℍ[ℚ, a, b])ˣ) * d⁻¹) * d = γ from by group]; exact γ.2)⟩
      left_inv := fun γ => Subtype.ext (by show d * (d⁻¹ * (γ : (ℍ[ℚ, a, b])ˣ) * d) * d⁻¹ = γ; group)
      right_inv := fun γ => Subtype.ext (by show d⁻¹ * (d * (γ : (ℍ[ℚ, a, b])ˣ) * d⁻¹) * d = γ; group) }

theorem neg_one_mem_unitGroupAt {Λ : Submodule ℤ ℍ[ℚ, a, b]} (hΛ : QuaternionAlgebra.IsOrder Λ) (y : (ℍ𝔸)ˣ) :
    (-1 : (ℍ[ℚ, a, b])ˣ) ∈ unitGroupAt (Submodule.finiteIdeleStabilizer Λ) y := by
  rw [mem_unitGroupAt_iff]
  have hc : Submodule.finiteIdeleDiagonal ℍ[ℚ, a, b] (-1 : (ℍ[ℚ, a, b])ˣ) =
      Submodule.finiteIdeleDiagonal ℍ[ℚ, a, b] (Units.map (algebraMap ℚ ℍ[ℚ, a, b]).toMonoidHom (-1 : ℚˣ)) := by
    congr 1
  rw [hc, mul_assoc, ← finiteIdeleDiagonal_ratUnit_comm (-1 : ℚˣ) y, ← mul_assoc, inv_mul_cancel, one_mul, ← hc]
  have hval : ((Submodule.finiteIdeleDiagonal ℍ[ℚ, a, b] (-1 : (ℍ[ℚ, a, b])ˣ) : (ℍ𝔸)ˣ) : ℍ𝔸) = -1 := by
    rw [Submodule.val_finiteIdeleDiagonal_apply, Units.val_neg, Units.val_one, TensorProduct.neg_tmul]
    rfl
  have hinv : (Submodule.finiteIdeleDiagonal ℍ[ℚ, a, b] (-1 : (ℍ[ℚ, a, b])ˣ))⁻¹ =
      Submodule.finiteIdeleDiagonal ℍ[ℚ, a, b] (-1 : (ℍ[ℚ, a, b])ˣ) := by
    rw [← map_inv, inv_neg, inv_one]
  rw [HeckeLocal.mem_stabilizer_iff hΛ, hinv, hval]
  exact ⟨AddSubgroup.neg_mem _ (HeckeLocal.one_mem_box hΛ), AddSubgroup.neg_mem _ (HeckeLocal.one_mem_box hΛ)⟩

theorem finite_unitGroupAt (ha : a < 0) (hb : b < 0) {Λ : Submodule ℤ ℍ[ℚ, a, b]} (hΛ : QuaternionAlgebra.IsOrder Λ)
    (y : (ℍ𝔸)ˣ) : Finite ↥(unitGroupAt (Submodule.finiteIdeleStabilizer Λ) y) := by
  have hΛy : QuaternionAlgebra.IsOrder (Submodule.conjByFiniteIdele Λ y) := QuaternionAlgebra.IsOrder.conjByFiniteIdele Λ hΛ y
  haveI := (QuaternionAlgebra.IsOrder.finite_isUnitOf_and_nrd_eq_one ha hb hΛy).1
  exact Finite.of_equiv _ (isUnitOfEquivUnitGroupAt hΛ y)

theorem two_dvd_natCard_unitGroupAt (_ha : a < 0) (_hb : b < 0) {Λ : Submodule ℤ ℍ[ℚ, a, b]}
    (hΛ : QuaternionAlgebra.IsOrder Λ) (y : (ℍ𝔸)ˣ) :
    2 ∣ Nat.card ↥(unitGroupAt (Submodule.finiteIdeleStabilizer Λ) y) := by
  have h2 : orderOf (⟨-1, neg_one_mem_unitGroupAt hΛ y⟩ : ↥(unitGroupAt (Submodule.finiteIdeleStabilizer Λ) y)) = 2 := by
    rw [Subgroup.orderOf_mk]
    refine orderOf_eq_prime (by rw [neg_one_sq]) ?_
    intro h
    have h1 : ((-1 : (ℍ[ℚ, a, b])ˣ) : ℍ[ℚ, a, b]) = 1 := by rw [h, Units.val_one]
    rw [Units.val_neg, Units.val_one] at h1
    have h2 := congrArg QuaternionAlgebra.re h1
    simp at h2
    norm_num at h2
  rw [← h2]
  exact orderOf_dvd_natCard _

theorem natCard_unitGroupAt_pos (ha : a < 0) (hb : b < 0) {Λ : Submodule ℤ ℍ[ℚ, a, b]}
    (hΛ : QuaternionAlgebra.IsOrder Λ) (y : (ℍ𝔸)ˣ) :
    0 < Nat.card ↥(unitGroupAt (Submodule.finiteIdeleStabilizer Λ) y) := by
  haveI := finite_unitGroupAt ha hb hΛ y
  exact Nat.card_pos

theorem two_mul_classWeight_eq (ha : a < 0) (hb : b < 0) {Λ : Submodule ℤ ℍ[ℚ, a, b]} (hΛ : QuaternionAlgebra.IsOrder Λ)
    {U₀ : Subgroup (ℍ𝔸)ˣ} (z : ClassSet U₀) :
    2 * (classWeight U₀ Λ z : ℕ) = Nat.card ↥(unitGroupAt (Submodule.finiteIdeleStabilizer Λ) z.out) := by
  rw [classWeight, unitWeight, natCard_isUnitOf_eq hΛ]
  obtain ⟨k, hk⟩ := two_dvd_natCard_unitGroupAt ha hb hΛ z.out
  have hpos := natCard_unitGroupAt_pos ha hb hΛ z.out
  rw [hk] at hpos ⊢
  have hk0 : 0 < k := by omega
  rw [Nat.mul_div_cancel_left k two_pos, PNat.toPNat'_coe hk0]

theorem quotientMk_mul_eq_iff (U₀ U₁ : Subgroup (ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) (g : (ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ)
    (hU₁ : ∀ u : (ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ, u ∈ U₁ ↔ u ∈ U₀ ∧ g⁻¹ * u * g ∈ U₀) (u u' : ↥U₀) :
    (((u : (ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) * g : (ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) : (ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ ⧸ U₀) = (((u' : (ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) * g : (ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) : (ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ ⧸ U₀) ↔
      u⁻¹ * u' ∈ U₁.subgroupOf U₀ := by
  rw [Subgroup.mem_subgroupOf, QuotientGroup.eq, hU₁]
  simp only [Subgroup.coe_mul, Subgroup.coe_inv, mul_inv_rev]
  constructor
  · intro h
    refine ⟨mul_mem (inv_mem u.2) u'.2, ?_⟩
    rw [show g⁻¹ * ((u : (ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ)⁻¹ * (u' : (ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ)) * g = g⁻¹ * (u : (ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ)⁻¹ * ((u' : (ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) * g) from by group]
    exact h
  · intro h
    rw [show g⁻¹ * (u : (ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ)⁻¹ * ((u' : (ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) * g) = g⁻¹ * ((u : (ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ)⁻¹ * (u' : (ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ)) * g from by group]
    exact h.2

theorem quot_mul_injective (U₀ U₁ : Subgroup (ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) (g : (ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ)
    (hU₁ : ∀ u : (ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ, u ∈ U₁ ↔ u ∈ U₀ ∧ g⁻¹ * u * g ∈ U₀) :
    Function.Injective (fun q : ↥U₀ ⧸ U₁.subgroupOf U₀ => ((((q.out : ↥U₀) : (ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) * g : (ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) : (ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ ⧸ U₀)) := by
  intro q q' h
  have h1 := (quotientMk_mul_eq_iff U₀ U₁ g hU₁ q.out q'.out).mp h
  rw [← QuotientGroup.out_eq' q, ← QuotientGroup.out_eq' q']
  exact QuotientGroup.eq.mpr h1

end AsmHelpers

end CerednikDrinfeld.HeckeDict

namespace CerednikDrinfeld p2m_export "CerednikDrinfeld" "meetOrder classSetForget classSetShift unitWeight classWeight classSetHeckeMatrix levelHeckeUSet classSetDegeneracyData DegeneracyData pushforward pushforward_apply_eq_sum_filter DegeneracyData.FiniteHom DegeneracyData.FiniteHom.pullbackFun_apply mul_mem_levelHeckeUSet_and_mul_mem_levelHeckeUSet_of_mem_finiteIdeleStabilizer levelHeckeUSet_eq_doubleCoset_finiteIdeleStabilizer_of_dvd_of_squarefree" namespace HeckeDict end CerednikDrinfeld.HeckeDict
p2m_open_scoped "CerednikDrinfeld" in
theorem CerednikDrinfeld.HeckeDict.hecke_dict_U

    {a b : ℚ} {N q q' : ℕ} [NeZero N] (hN : Squarefree N) [Fact q.Prime] [Fact q'.Prime]
    (hqN : ¬ q ∣ N) (hq'N : ¬ q' ∣ N) (hqq' : q' ≠ q) (hq'5 : 5 ≤ q')
    (hdef : IsDefiniteRamifiedExactlyAt a b q')
    (Λ R : Submodule ℤ ℍ[ℚ, a, b]) (hΛ : IsMaximalOrder Λ) (hR : IsEichlerOrder R N) (hRΛ : R ≤ Λ)
    (n : (ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) (hn : n ∈ primeHeckeSet R q)
    (hS : IsEichlerOrder (meetOrder R n) (N * q))
    (hnorm : Submodule.conjByFiniteIdele (meetOrder R n) n = meetOrder R n)
    (hsq : ∀ x : ClassSet (Submodule.finiteIdeleStabilizer (meetOrder R n)),
      classSetShift _ n (classSetShift _ n x) = x)
    [Fintype (ClassSet (Submodule.finiteIdeleStabilizer (meetOrder R n)))]
    [Fintype (ClassSet (Submodule.finiteIdeleStabilizer R))]
    [DecidableEq (ClassSet (Submodule.finiteIdeleStabilizer (meetOrder R n)))]
    [DecidableEq (ClassSet (Submodule.finiteIdeleStabilizer R))]

    (ℓ : ℕ) [Fact ℓ.Prime] (hℓ : ℓ ∣ N)
    (s : (ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ)
    (hs : Submodule.finiteIdeleDiagonal ℍ[ℚ, a, b]
        (Units.map (algebraMap ℚ ℍ[ℚ, a, b]).toMonoidHom
          (Units.mk0 (ℓ : ℚ) (Nat.cast_ne_zero.mpr (Fact.out : ℓ.Prime).ne_zero))) * s⁻¹ ∈
      levelHeckeUSet Λ (meetOrder R n) ℓ)
    (hR' : IsEichlerOrder (meetOrder R s) (N * ℓ))
    (n' : (ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) (hn' : n' ∈ primeHeckeSet (meetOrder R s) q)
    (hS' : IsEichlerOrder (meetOrder (meetOrder R s) n') (N * ℓ * q))
    (hnorm' : Submodule.conjByFiniteIdele (meetOrder (meetOrder R s) n') n' = meetOrder (meetOrder R s) n')
    (hsq' : ∀ x : ClassSet (Submodule.finiteIdeleStabilizer (meetOrder (meetOrder R s) n')),
      classSetShift _ n' (classSetShift _ n' x) = x)
    (hnn' : n⁻¹ * n' ∈ Submodule.finiteIdeleStabilizer R) (hsn' : s * n' = n' * s)
    [Fintype (ClassSet (Submodule.finiteIdeleStabilizer (meetOrder (meetOrder R s) n')))]
    [Fintype (ClassSet (Submodule.finiteIdeleStabilizer (meetOrder R s)))]
    [DecidableEq (ClassSet (Submodule.finiteIdeleStabilizer (meetOrder R s)))]
    (α β : (classSetDegeneracyData (meetOrder R s) n').FiniteHom (classSetDegeneracyData R n))
    (hα : α.mapE = classSetForget _ _) (hβ : β.mapE = fun e => ClassSet.mk _ (e.out * s))
    (x : ClassSet (Submodule.finiteIdeleStabilizer (meetOrder R n)) → ℤ) :
    CerednikDrinfeld.pushforward α.mapE (β.pullbackFun x) =
      (classSetHeckeMatrix (Submodule.finiteIdeleStabilizer (meetOrder R n))
        (levelHeckeUSet Λ (meetOrder R n) ℓ)).mulVec x := by
  classical

  have hRo : QuaternionAlgebra.IsOrder R := hR.isOrder
  have hSo : QuaternionAlgebra.IsOrder (meetOrder R n) := GOODEQ.isOrder_meetOrder hRo n
  have hS'o : QuaternionAlgebra.IsOrder (meetOrder (meetOrder R s) n') :=
    GOODEQ.isOrder_meetOrder (GOODEQ.isOrder_meetOrder hRo s) n'
  have ha : a < 0 := hdef.neg_left
  have hb : b < 0 := hdef.neg_right

  have hU' : ∀ u : (ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ, u ∈ Submodule.finiteIdeleStabilizer (meetOrder (meetOrder R s) n') ↔ u ∈ Submodule.finiteIdeleStabilizer (meetOrder R n) ∧ s⁻¹ * u * s ∈ Submodule.finiteIdeleStabilizer (meetOrder R n) :=
    mem_stab_tower_iff' hRo n s n' hnn' hsn'

  let U₂ : Subgroup (ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ := Submodule.finiteIdeleStabilizer (meetOrder R n) ⊓ (Submodule.finiteIdeleStabilizer (meetOrder R n)).comap (MulAut.conj s).toMonoidHom
  have hU₂ : ∀ u : (ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ, u ∈ U₂ ↔ u ∈ Submodule.finiteIdeleStabilizer (meetOrder R n) ∧ s * u * s⁻¹ ∈ Submodule.finiteIdeleStabilizer (meetOrder R n) := by
    intro u
    show u ∈ Submodule.finiteIdeleStabilizer (meetOrder R n) ⊓ (Submodule.finiteIdeleStabilizer (meetOrder R n)).comap (MulAut.conj s).toMonoidHom ↔ _
    rw [Subgroup.mem_inf, Subgroup.mem_comap, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
  have hU₂inv : ∀ u : (ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ, u ∈ U₂ ↔ u ∈ Submodule.finiteIdeleStabilizer (meetOrder R n) ∧ (s⁻¹)⁻¹ * u * s⁻¹ ∈ Submodule.finiteIdeleStabilizer (meetOrder R n) := by
    intro u; rw [inv_inv]; exact hU₂ u
  have hcen : ∀ u : (ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ, (Submodule.finiteIdeleDiagonal ℍ[ℚ, a, b] (Units.map (algebraMap ℚ ℍ[ℚ, a, b]).toMonoidHom (Units.mk0 (ℓ : ℚ) (Nat.cast_ne_zero.mpr (Fact.out : ℓ.Prime).ne_zero))) * s⁻¹)⁻¹ * u * (Submodule.finiteIdeleDiagonal ℍ[ℚ, a, b] (Units.map (algebraMap ℚ ℍ[ℚ, a, b]).toMonoidHom (Units.mk0 (ℓ : ℚ) (Nat.cast_ne_zero.mpr (Fact.out : ℓ.Prime).ne_zero))) * s⁻¹) = s * u * s⁻¹ := by
    intro u
    have hc := finiteIdeleDiagonal_ratUnit_comm (Units.mk0 (ℓ : ℚ) (Nat.cast_ne_zero.mpr (Fact.out : ℓ.Prime).ne_zero)) u
    calc (Submodule.finiteIdeleDiagonal ℍ[ℚ, a, b] (Units.map (algebraMap ℚ ℍ[ℚ, a, b]).toMonoidHom (Units.mk0 (ℓ : ℚ) (Nat.cast_ne_zero.mpr (Fact.out : ℓ.Prime).ne_zero))) * s⁻¹)⁻¹ * u * (Submodule.finiteIdeleDiagonal ℍ[ℚ, a, b] (Units.map (algebraMap ℚ ℍ[ℚ, a, b]).toMonoidHom (Units.mk0 (ℓ : ℚ) (Nat.cast_ne_zero.mpr (Fact.out : ℓ.Prime).ne_zero))) * s⁻¹)
        = s * ((Submodule.finiteIdeleDiagonal ℍ[ℚ, a, b] (Units.map (algebraMap ℚ ℍ[ℚ, a, b]).toMonoidHom (Units.mk0 (ℓ : ℚ) (Nat.cast_ne_zero.mpr (Fact.out : ℓ.Prime).ne_zero))))⁻¹ * (u * Submodule.finiteIdeleDiagonal ℍ[ℚ, a, b] (Units.map (algebraMap ℚ ℍ[ℚ, a, b]).toMonoidHom (Units.mk0 (ℓ : ℚ) (Nat.cast_ne_zero.mpr (Fact.out : ℓ.Prime).ne_zero))))) * s⁻¹ := by group
      _ = s * ((Submodule.finiteIdeleDiagonal ℍ[ℚ, a, b] (Units.map (algebraMap ℚ ℍ[ℚ, a, b]).toMonoidHom (Units.mk0 (ℓ : ℚ) (Nat.cast_ne_zero.mpr (Fact.out : ℓ.Prime).ne_zero))))⁻¹ * (Submodule.finiteIdeleDiagonal ℍ[ℚ, a, b] (Units.map (algebraMap ℚ ℍ[ℚ, a, b]).toMonoidHom (Units.mk0 (ℓ : ℚ) (Nat.cast_ne_zero.mpr (Fact.out : ℓ.Prime).ne_zero))) * u)) * s⁻¹ := by rw [hc]
      _ = s * u * s⁻¹ := by group
  have hU₂g : ∀ u : (ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ, u ∈ U₂ ↔ u ∈ Submodule.finiteIdeleStabilizer (meetOrder R n) ∧ (Submodule.finiteIdeleDiagonal ℍ[ℚ, a, b] (Units.map (algebraMap ℚ ℍ[ℚ, a, b]).toMonoidHom (Units.mk0 (ℓ : ℚ) (Nat.cast_ne_zero.mpr (Fact.out : ℓ.Prime).ne_zero))) * s⁻¹)⁻¹ * u * (Submodule.finiteIdeleDiagonal ℍ[ℚ, a, b] (Units.map (algebraMap ℚ ℍ[ℚ, a, b]).toMonoidHom (Units.mk0 (ℓ : ℚ) (Nat.cast_ne_zero.mpr (Fact.out : ℓ.Prime).ne_zero))) * s⁻¹) ∈ Submodule.finiteIdeleStabilizer (meetOrder R n) := by
    intro u; rw [hcen]; exact hU₂ u
  have hle₂ : U₂ ≤ Submodule.finiteIdeleStabilizer (meetOrder R n) := fun u hu => ((hU₂ u).mp hu).1

  let τ := transportEquiv (Submodule.finiteIdeleStabilizer (meetOrder R n)) (Submodule.finiteIdeleStabilizer (meetOrder (meetOrder R s) n')) U₂ s hU' hU₂
  haveI : Fintype (ClassSet U₂) := Fintype.ofEquiv _ τ

  have hΛo : QuaternionAlgebra.IsOrder Λ := hΛ.isOrder
  have hSΛ : meetOrder R n ≤ Λ := le_trans inf_le_left hRΛ
  have hTsub : levelHeckeUSet Λ (meetOrder R n) ℓ ⊆ primeHeckeSet (meetOrder R n) ℓ := fun _ hh => hh.1
  haveI hBfin : Finite {c : (ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ ⧸ Submodule.finiteIdeleStabilizer (meetOrder R n) // ∃ g ∈ levelHeckeUSet Λ (meetOrder R n) ℓ, (QuotientGroup.mk g : (ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ ⧸ Submodule.finiteIdeleStabilizer (meetOrder R n)) = c} :=
    (QuaternionAlgebra.IsOrder.finite_setOf_exists_mem_quotientMk_eq_of_subset_primeHeckeSet hSo ℓ _ hTsub).to_subtype
  have hsbar : Submodule.finiteIdeleDiagonal ℍ[ℚ, a, b] (Units.map (algebraMap ℚ ℍ[ℚ, a, b]).toMonoidHom (Units.mk0 (ℓ : ℚ) (Nat.cast_ne_zero.mpr (Fact.out : ℓ.Prime).ne_zero))) * s⁻¹ ∈ levelHeckeUSet Λ (meetOrder R n) ℓ := hs
  have hmulT : ∀ u ∈ Submodule.finiteIdeleStabilizer (meetOrder R n), ∀ t ∈ levelHeckeUSet Λ (meetOrder R n) ℓ, u * t ∈ levelHeckeUSet Λ (meetOrder R n) ℓ := fun u hu t ht =>
    (CerednikDrinfeld.mul_mem_levelHeckeUSet_and_mul_mem_levelHeckeUSet_of_mem_finiteIdeleStabilizer Λ (meetOrder R n) hΛo hSo hSΛ ℓ hu ht).1
  let ψ : ↥(Submodule.finiteIdeleStabilizer (meetOrder R n)) ⧸ U₂.subgroupOf (Submodule.finiteIdeleStabilizer (meetOrder R n)) →
      {c : (ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ ⧸ Submodule.finiteIdeleStabilizer (meetOrder R n) // ∃ g ∈ levelHeckeUSet Λ (meetOrder R n) ℓ, (QuotientGroup.mk g : (ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ ⧸ Submodule.finiteIdeleStabilizer (meetOrder R n)) = c} :=
    fun q => ⟨QuotientGroup.mk (((q.out : ↥(Submodule.finiteIdeleStabilizer (meetOrder R n))) : (ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) * (Submodule.finiteIdeleDiagonal ℍ[ℚ, a, b] (Units.map (algebraMap ℚ ℍ[ℚ, a, b]).toMonoidHom (Units.mk0 (ℓ : ℚ) (Nat.cast_ne_zero.mpr (Fact.out : ℓ.Prime).ne_zero))) * s⁻¹)),
      ⟨_, hmulT _ (q.out : ↥(Submodule.finiteIdeleStabilizer (meetOrder R n))).2 _ hsbar, rfl⟩⟩
  have hψinj : Function.Injective ψ := by
    intro q q' h
    exact quot_mul_injective (Submodule.finiteIdeleStabilizer (meetOrder R n)) U₂ (Submodule.finiteIdeleDiagonal ℍ[ℚ, a, b] (Units.map (algebraMap ℚ ℍ[ℚ, a, b]).toMonoidHom (Units.mk0 (ℓ : ℚ) (Nat.cast_ne_zero.mpr (Fact.out : ℓ.Prime).ne_zero))) * s⁻¹) hU₂g (congrArg Subtype.val h)
  haveI : Finite (↥(Submodule.finiteIdeleStabilizer (meetOrder R n)) ⧸ U₂.subgroupOf (Submodule.finiteIdeleStabilizer (meetOrder R n))) := Finite.of_injective ψ hψinj
  haveI : (U₂.subgroupOf (Submodule.finiteIdeleStabilizer (meetOrder R n))).FiniteIndex := Subgroup.finiteIndex_of_finite_quotient

  suffices hentry : ∀ i j : ClassSet (Submodule.finiteIdeleStabilizer (meetOrder R n)),
      (∑ e ∈ Finset.univ.filter (fun e => β.mapE e = j ∧ α.mapE e = i), (β.deg e : ℤ)) =
        heckeKernel (Submodule.finiteIdeleStabilizer (meetOrder R n)) (levelHeckeUSet Λ (meetOrder R n) ℓ) j i by
    funext i
    rw [pushforward_pullbackFun_apply β α.mapE x i, classSetHeckeMatrix_mulVec_apply]
    exact Finset.sum_congr rfl fun j _ => by rw [hentry i j]

  have hENT : ∀ i j : ClassSet (Submodule.finiteIdeleStabilizer (meetOrder R n)),
      (∑ e ∈ Finset.univ.filter (fun e => β.mapE e = j ∧ α.mapE e = i), (β.deg e : ℕ)) =
        Nat.card {c : ↥(Submodule.finiteIdeleStabilizer (meetOrder R n)) ⧸ U₂.subgroupOf (Submodule.finiteIdeleStabilizer (meetOrder R n)) //
          ClassSet.mk (Submodule.finiteIdeleStabilizer (meetOrder R n)) (j.out * ((c.out : ↥(Submodule.finiteIdeleStabilizer (meetOrder R n))) : (ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) * s⁻¹) = i} := by
    intro i j

    have hreidx : (∑ e ∈ Finset.univ.filter (fun e => β.mapE e = j ∧ α.mapE e = i), (β.deg e : ℕ)) =
        ∑ e'' ∈ Finset.univ.filter (fun e'' : ClassSet U₂ =>
          classSetForget U₂ (Submodule.finiteIdeleStabilizer (meetOrder R n)) e'' = j ∧ ClassSet.mk (Submodule.finiteIdeleStabilizer (meetOrder R n)) (e''.out * s⁻¹) = i), (β.deg (τ.symm e'') : ℕ) := by
      refine Finset.sum_equiv τ (fun e => ?_) (fun e _ => by rw [Equiv.symm_apply_apply])
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, hα, hβ]
      rw [← forget_transport (Submodule.finiteIdeleStabilizer (meetOrder R n)) (Submodule.finiteIdeleStabilizer (meetOrder (meetOrder R s) n')) U₂ s hU' hU₂ e, ← shift_transport (Submodule.finiteIdeleStabilizer (meetOrder R n)) (Submodule.finiteIdeleStabilizer (meetOrder (meetOrder R s) n')) U₂ s hU' hU₂ e]
    rw [hreidx]

    refine sum_idx_filter_forget_shift_eq_natCard (Submodule.finiteIdeleStabilizer (meetOrder R n)) U₂ s⁻¹ hU₂inv j i (finite_unitGroupAt ha hb hSo j.out)
      (fun e'' => (β.deg (τ.symm e'') : ℕ)) ?_

    intro u hu
    have hsymm : τ.symm (ClassSet.mk U₂ (j.out * u)) = ClassSet.mk (Submodule.finiteIdeleStabilizer (meetOrder (meetOrder R s) n')) (j.out * u * s⁻¹) :=
      transportEquiv_symm_mk (Submodule.finiteIdeleStabilizer (meetOrder R n)) (Submodule.finiteIdeleStabilizer (meetOrder (meetOrder R s) n')) U₂ s hU' hU₂ _
    show (β.deg (τ.symm (ClassSet.mk U₂ (j.out * u))) : ℕ) = _
    rw [hsymm]

    have hβe : β.mapE (ClassSet.mk (Submodule.finiteIdeleStabilizer (meetOrder (meetOrder R s) n')) (j.out * u * s⁻¹)) = j := by
      rw [hβ]
      show ClassSet.mk (Submodule.finiteIdeleStabilizer (meetOrder R n)) ((ClassSet.mk (Submodule.finiteIdeleStabilizer (meetOrder (meetOrder R s) n')) (j.out * u * s⁻¹)).out * s) = j
      have h1 := forget_transport (Submodule.finiteIdeleStabilizer (meetOrder R n)) (Submodule.finiteIdeleStabilizer (meetOrder (meetOrder R s) n')) U₂ s hU' hU₂ (ClassSet.mk (Submodule.finiteIdeleStabilizer (meetOrder (meetOrder R s) n')) (j.out * u * s⁻¹))
      rw [transportEquiv_mk, inv_mul_cancel_right] at h1
      rw [← h1]
      exact forget_mk_mul (Submodule.finiteIdeleStabilizer (meetOrder R n)) U₂ j u hu hle₂

    have hw := β.w_mapE (ClassSet.mk (Submodule.finiteIdeleStabilizer (meetOrder (meetOrder R s) n')) (j.out * u * s⁻¹))
    rw [hβe] at hw
    have hwN := congrArg (fun z : ℕ+ => 2 * (z : ℕ)) hw
    simp only [PNat.mul_coe] at hwN

    have hΓ : 2 * ((classSetDegeneracyData R n).w j : ℕ) = Nat.card ↥(unitGroupAt (Submodule.finiteIdeleStabilizer (meetOrder R n)) j.out) :=
      two_mul_classWeight_eq ha hb hSo j
    have hH0 : 2 * ((classSetDegeneracyData (meetOrder R s) n').w (ClassSet.mk (Submodule.finiteIdeleStabilizer (meetOrder (meetOrder R s) n')) (j.out * u * s⁻¹)) : ℕ) =
        Nat.card ↥(unitGroupAt (Submodule.finiteIdeleStabilizer (meetOrder (meetOrder R s) n')) (ClassSet.mk (Submodule.finiteIdeleStabilizer (meetOrder (meetOrder R s) n')) (j.out * u * s⁻¹)).out) :=
      two_mul_classWeight_eq ha hb hS'o _

    have hH : Nat.card ↥(unitGroupAt (Submodule.finiteIdeleStabilizer (meetOrder (meetOrder R s) n')) (ClassSet.mk (Submodule.finiteIdeleStabilizer (meetOrder (meetOrder R s) n')) (j.out * u * s⁻¹)).out) =
        Nat.card ↥(unitGroupAt U₂ (j.out * u)) := by
      obtain ⟨d0, w0, hd0, hw0, hout⟩ :=
        DoubleCoset.mk_out_eq_mul (Submodule.finiteIdeleDiagonal ℍ[ℚ, a, b]).range (Submodule.finiteIdeleStabilizer (meetOrder (meetOrder R s) n')) (j.out * u * s⁻¹)
      obtain ⟨δ, rfl⟩ := MonoidHom.mem_range.mp hd0
      rw [show (ClassSet.mk (Submodule.finiteIdeleStabilizer (meetOrder (meetOrder R s) n')) (j.out * u * s⁻¹)).out = _ * (j.out * u * s⁻¹) * w0 from hout,
        natCard_unitGroupAt_diag_mul_mul _ δ _ w0 hw0,
        ← unitGroupAt_transport (Submodule.finiteIdeleStabilizer (meetOrder R n)) (Submodule.finiteIdeleStabilizer (meetOrder (meetOrder R s) n')) U₂ s hU' hU₂ (j.out * u * s⁻¹), inv_mul_cancel_right]

    have hle5 : unitGroupAt U₂ (j.out * u) ≤ unitGroupAt (Submodule.finiteIdeleStabilizer (meetOrder R n)) j.out := unitGroupAt_mul_le (Submodule.finiteIdeleStabilizer (meetOrder R n)) U₂ j u hu hle₂
    haveI := finite_unitGroupAt ha hb hSo j.out
    have hLag := ((unitGroupAt U₂ (j.out * u)).subgroupOf (unitGroupAt (Submodule.finiteIdeleStabilizer (meetOrder R n)) j.out)).index_mul_card
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hle5).toEquiv] at hLag

    have hHpos : 0 < Nat.card ↥(unitGroupAt U₂ (j.out * u)) := by
      rw [← hH, ← hH0]; exact Nat.mul_pos two_pos (PNat.pos _)
    have e1 : Nat.card ↥(unitGroupAt (Submodule.finiteIdeleStabilizer (meetOrder R n)) j.out) = (β.deg (ClassSet.mk (Submodule.finiteIdeleStabilizer (meetOrder (meetOrder R s) n')) (j.out * u * s⁻¹)) : ℕ) *
        Nat.card ↥(unitGroupAt U₂ (j.out * u)) := by
      rw [← hΓ, hwN, ← hH, ← hH0]; ring
    rw [e1] at hLag
    exact (Nat.eq_of_mul_eq_mul_right hHpos hLag).symm

  intro i j
  haveI : NeZero (N * q) := ⟨mul_ne_zero (NeZero.ne N) (Fact.out : q.Prime).ne_zero⟩
  have hNq : Squarefree (N * q) :=
    (Nat.squarefree_mul ((Nat.Prime.coprime_iff_not_dvd Fact.out).mpr hqN).symm).mpr
      ⟨hN, Irreducible.squarefree (Fact.out : q.Prime)⟩
  have hq'Nq : ¬ q' ∣ N * q := fun h =>
    ((Nat.Prime.dvd_mul Fact.out).mp h).elim hq'N
      (fun h2 => hqq' ((Nat.prime_dvd_prime_iff_eq Fact.out Fact.out).mp h2))
  have hℓNq : ℓ ∣ N * q := Dvd.dvd.mul_right hℓ q
  have hDCU : levelHeckeUSet Λ (meetOrder R n) ℓ = DoubleCoset.doubleCoset (Submodule.finiteIdeleDiagonal ℍ[ℚ, a, b] (Units.map (algebraMap ℚ ℍ[ℚ, a, b]).toMonoidHom (Units.mk0 (ℓ : ℚ) (Nat.cast_ne_zero.mpr (Fact.out : ℓ.Prime).ne_zero))) * s⁻¹) (Submodule.finiteIdeleStabilizer (meetOrder R n) : Set (ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) (Submodule.finiteIdeleStabilizer (meetOrder R n) : Set (ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) :=
    CerednikDrinfeld.levelHeckeUSet_eq_doubleCoset_finiteIdeleStabilizer_of_dvd_of_squarefree hdef hNq hS hΛ hSΛ hq'Nq ℓ hℓNq hs
  have hT : ∀ c : (ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ ⧸ Submodule.finiteIdeleStabilizer (meetOrder R n), (∃ t ∈ levelHeckeUSet Λ (meetOrder R n) ℓ, (t : (ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ ⧸ Submodule.finiteIdeleStabilizer (meetOrder R n)) = c) ↔
      ∃ u ∈ Submodule.finiteIdeleStabilizer (meetOrder R n), ((u * (Submodule.finiteIdeleDiagonal ℍ[ℚ, a, b] (Units.map (algebraMap ℚ ℍ[ℚ, a, b]).toMonoidHom (Units.mk0 (ℓ : ℚ) (Nat.cast_ne_zero.mpr (Fact.out : ℓ.Prime).ne_zero))) * s⁻¹) : (ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) : (ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ ⧸ Submodule.finiteIdeleStabilizer (meetOrder R n)) = c := by
    intro c
    constructor
    · rintro ⟨t, ht, rfl⟩
      rw [hDCU] at ht
      obtain ⟨u, hu, u', hu', rfl⟩ := DoubleCoset.mem_doubleCoset.mp ht
      refine ⟨u, hu, ?_⟩
      apply QuotientGroup.eq.mpr
      have e : (u * (Submodule.finiteIdeleDiagonal ℍ[ℚ, a, b] (Units.map (algebraMap ℚ ℍ[ℚ, a, b]).toMonoidHom (Units.mk0 (ℓ : ℚ) (Nat.cast_ne_zero.mpr (Fact.out : ℓ.Prime).ne_zero))) * s⁻¹))⁻¹ * (u * (Submodule.finiteIdeleDiagonal ℍ[ℚ, a, b] (Units.map (algebraMap ℚ ℍ[ℚ, a, b]).toMonoidHom (Units.mk0 (ℓ : ℚ) (Nat.cast_ne_zero.mpr (Fact.out : ℓ.Prime).ne_zero))) * s⁻¹) * u') = u' := by group
      rw [e]; exact hu'
    · rintro ⟨u, hu, rfl⟩
      exact ⟨_, hmulT u hu _ hsbar, rfl⟩

  rw [show (∑ e ∈ Finset.univ.filter (fun e => β.mapE e = j ∧ α.mapE e = i), (β.deg e : ℤ)) =
      ((∑ e ∈ Finset.univ.filter (fun e => β.mapE e = j ∧ α.mapE e = i), (β.deg e : ℕ) : ℕ) : ℤ) from by
        rw [Nat.cast_sum]]
  rw [hENT i j, natCard_quot_shift_eq_of_central (Submodule.finiteIdeleStabilizer (meetOrder R n)) U₂ s (Units.mk0 (ℓ : ℚ) (Nat.cast_ne_zero.mpr (Fact.out : ℓ.Prime).ne_zero)) j.out i,
    ← natCard_heckeIncidence_eq_natCard_quot (Submodule.finiteIdeleStabilizer (meetOrder R n)) U₂ (Submodule.finiteIdeleDiagonal ℍ[ℚ, a, b] (Units.map (algebraMap ℚ ℍ[ℚ, a, b]).toMonoidHom (Units.mk0 (ℓ : ℚ) (Nat.cast_ne_zero.mpr (Fact.out : ℓ.Prime).ne_zero))) * s⁻¹) hU₂g (levelHeckeUSet Λ (meetOrder R n) ℓ) hT j.out i]
  rfl

theorem solution

    {a b : ℚ} {N q q' : ℕ} [NeZero N] (hN : Squarefree N) [Fact q.Prime] [Fact q'.Prime]
    (hqN : ¬ q ∣ N) (hq'N : ¬ q' ∣ N) (hqq' : q' ≠ q) (hq'5 : 5 ≤ q')
    (hdef : IsDefiniteRamifiedExactlyAt a b q')
    (Λ R : Submodule ℤ ℍ[ℚ, a, b]) (hΛ : IsMaximalOrder Λ) (hR : IsEichlerOrder R N) (hRΛ : R ≤ Λ)
    (n : (ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) (hn : n ∈ primeHeckeSet R q)
    (hS : IsEichlerOrder (meetOrder R n) (N * q))
    (hnorm : Submodule.conjByFiniteIdele (meetOrder R n) n = meetOrder R n)
    (hsq : ∀ x : ClassSet (Submodule.finiteIdeleStabilizer (meetOrder R n)),
      classSetShift _ n (classSetShift _ n x) = x)
    [Fintype (ClassSet (Submodule.finiteIdeleStabilizer (meetOrder R n)))]
    [Fintype (ClassSet (Submodule.finiteIdeleStabilizer R))]
    [DecidableEq (ClassSet (Submodule.finiteIdeleStabilizer (meetOrder R n)))]
    [DecidableEq (ClassSet (Submodule.finiteIdeleStabilizer R))]

    (ℓ : ℕ) [Fact ℓ.Prime] (hℓ : ℓ ∣ N)
    (s : (ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ)
    (hs : Submodule.finiteIdeleDiagonal ℍ[ℚ, a, b]
        (Units.map (algebraMap ℚ ℍ[ℚ, a, b]).toMonoidHom
          (Units.mk0 (ℓ : ℚ) (Nat.cast_ne_zero.mpr (Fact.out : ℓ.Prime).ne_zero))) * s⁻¹ ∈
      levelHeckeUSet Λ (meetOrder R n) ℓ)
    (hR' : IsEichlerOrder (meetOrder R s) (N * ℓ))
    (n' : (ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) (hn' : n' ∈ primeHeckeSet (meetOrder R s) q)
    (hS' : IsEichlerOrder (meetOrder (meetOrder R s) n') (N * ℓ * q))
    (hnorm' : Submodule.conjByFiniteIdele (meetOrder (meetOrder R s) n') n' = meetOrder (meetOrder R s) n')
    (hsq' : ∀ x : ClassSet (Submodule.finiteIdeleStabilizer (meetOrder (meetOrder R s) n')),
      classSetShift _ n' (classSetShift _ n' x) = x)
    (hnn' : n⁻¹ * n' ∈ Submodule.finiteIdeleStabilizer R) (hsn' : s * n' = n' * s)
    [Fintype (ClassSet (Submodule.finiteIdeleStabilizer (meetOrder (meetOrder R s) n')))]
    [Fintype (ClassSet (Submodule.finiteIdeleStabilizer (meetOrder R s)))]
    [DecidableEq (ClassSet (Submodule.finiteIdeleStabilizer (meetOrder R s)))]
    (α β : (classSetDegeneracyData (meetOrder R s) n').FiniteHom (classSetDegeneracyData R n))
    (hα : α.mapE = classSetForget _ _) (hβ : β.mapE = fun e => ClassSet.mk _ (e.out * s))
    (x : ClassSet (Submodule.finiteIdeleStabilizer (meetOrder R n)) → ℤ) :
    CerednikDrinfeld.pushforward α.mapE (β.pullbackFun x) =
      (classSetHeckeMatrix (Submodule.finiteIdeleStabilizer (meetOrder R n))
        (levelHeckeUSet Λ (meetOrder R n) ℓ)).mulVec x :=
  CerednikDrinfeld.HeckeDict.hecke_dict_U hN hqN hq'N hqq' hq'5 hdef Λ R hΛ hR hRΛ n hn hS hnorm hsq ℓ hℓ s hs hR' n' hn' hS' hnorm' hsq' hnn' hsn' α β hα hβ x

end S_CerednikDrinfeld_pushforward_comp_pullbackFun_eq_classSetHeckeMatrix_levelHeckeUSet_mulVec_of_dvd
end P2MW
export P2MW.S_CerednikDrinfeld_pushforward_comp_pullbackFun_eq_classSetHeckeMatrix_levelHeckeUSet_mulVec_of_dvd (solution)
