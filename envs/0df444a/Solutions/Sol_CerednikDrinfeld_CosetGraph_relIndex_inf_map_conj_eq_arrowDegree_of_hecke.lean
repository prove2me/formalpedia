-- Prove2me | solution 1 for CerednikDrinfeld.CosetGraph.relIndex_inf_map_conj_eq_arrowDegree_of_hecke
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.340288+00:00
-- url     : https://prove2.me/submissions/9bf3a769-9bf4-5ce3-91f9-a9be6a949125

import Definitions.Def_CerednikDrinfeld_HeckeTower
import Definitions.Def_CerednikDrinfeld_CosetGraphAtPrime
import Definitions.Def_CerednikDrinfeld_ClassSetGraph
import Definitions.Def_QuaternionAlgebra_EichlerOrder
import Definitions.Def_QuaternionAlgebra_Order
import Definitions.Def_QuaternionAlgebra_ReducedNorm
import Definitions.Def_QuaternionAlgebra_ClassSetHecke
import Definitions.Def_Submodule_LocalBox
import Definitions.Def_Submodule_FiniteAdeleBox
import Theorems.Thm_Submodule_mem_finiteAdeleBox_iff_forall_finiteAdeleEvalAt_mem_localBox
import Theorems.Thm_Submodule_localBox_inf
import Theorems.Thm_Submodule_mem_localBox_conjByFiniteIdele_iff
import Theorems.Thm_QuaternionAlgebra_IsOrder_conjByFiniteIdele
import Theorems.Thm_QuaternionAlgebra_IsOrder_mem_finiteIdeleStabilizer_iff_forall_map_finiteAdeleEvalAt_mem_localBoxUnits
import Theorems.Thm_QuaternionAlgebra_IsOrder_finiteAdeleBox_inf_conjByFiniteIdele_eq_and_finiteIdeleStabilizer_le
import Theorems.Thm_Submodule_exists_units_finiteAdeleEvalAt_eq
import Theorems.Thm_CerednikDrinfeld_CosetGraph_awayUnits_meetOrder_eq_inf_map_conj_of_finiteAdeleEvalAt_eq
import Theorems.Thm_QuaternionAlgebra_IsOrder_exists_nrd_eq_one_and_eq_finiteIdeleDiagonal_mul_mul_of_forall_nrd_eq_one
import Theorems.Thm_QuaternionAlgebra_IsEichlerOrder_exists_mem_finiteIdeleStabilizer_forall_nrd_eq
import Theorems.Thm_QuaternionAlgebra_IsEichlerOrder_exists_ringEquiv_mem_localBox_iff_of_notMem
import Theorems.Thm_CerednikDrinfeld_CSTower_isEichlerOrder_meetOrder_of_finiteIdeleDiagonal_mul_inv_mem_primeHeckeSet_meetOrder
import Theorems.Thm_CerednikDrinfeld_CSTower_isEichlerOrder_meetOrder_of_finiteIdeleDiagonal_mul_inv_mem_levelHeckeUSet_meetOrder
import Theorems.Thm_CerednikDrinfeld_relIndex_finiteIdeleStabilizer_meetOrder_eq_succ_of_mem_primeHeckeSet
import Theorems.Thm_CerednikDrinfeld_relIndex_finiteIdeleStabilizer_meetOrder_eq_of_mem_levelHeckeUSet_meetOrder_of_dvd
import Theorems.Thm_QuaternionAlgebra_mem_primeHeckeSet_iff_finiteIdeleDiagonal_mul_inv_mem
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

p2m_attr_erase "ext" "IsDedekindDomain.HeightOneSpectrum.adicCompletion.ext"
namespace P2MW.S_CerednikDrinfeld_CosetGraph_relIndex_inf_map_conj_eq_arrowDegree_of_hecke
p2m_attr_erase "instance" "IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation ModularCurve.SpecializationWitnessData.addCommGroup ModularCurve.CommutingHeckeFamily.commRing_adjoin ModularCurve.Gamma0Pair.isElliptic ModularCurve.ModuliTestDatum.isElliptic_reduced ModularCurve.ModuliTestDatum.isElliptic_curve ModularCurve.ModuliTestDatum.isElliptic_generic"
p2m_attr_erase "simp" "QuaternionAlgebra.baseChangeRight_tmul QuaternionAlgebra.mapOfAlgebraMapEq_apply QuaternionAlgebra.baseChange_tmul LocalGL2.swapUnit_val ModularCurve.coe_levelAlphaC ModularCurve.SSLevelDatum.mk.sizeOf_spec ModularCurve.SSLevelDatum.mk.injEq ModularCurve.coe_levelBetaC ModularCurve.coe_heckeBetaC AlgebraicCurve.Divisor.coe_degZeroEnd ModularCurve.coe_heckeAlphaC AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.jqNModC_one ModularCurve.qExpand_coeff_mul ModularCurve.qExpandₐ_apply ModularCurve.jqN_one ModularCurve.qExpand_single ModularCurve.dedekindPsi_one"
p2m_attr_erase "simp" "ModularCurve.ModularPolynomialData.mk.sizeOf_spec ModularCurve.evalAtJ_X ModularCurve.ModularPolynomialData.mk.injEq ModularCurve.constantCoeff_jNum ModularCurve.constantCoeff_eisenstein4 ModularCurve.qExpand_C ModularCurve.coeff_jq_neg_one ModularCurve.constantCoeff_jNumQ ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd ModularCurve.CommutingHeckeFamily.mk.injEq ModularCurve.SpecializationWitnessData.mk.sizeOf_spec ModularCurve.SpecializationWitnessData.mk.injEq ModularCurve.CommutingHeckeFamily.mk.sizeOf_spec ModularCurve.coe_nodeEquivOfPlaces_apply ModularCurve.widthOfPlaces_mk ModularCurve.smulNodePairEmb_apply ModularCurve.card_nodePairsOfPlaces ModularCurve.smulNodePair_snd ModularCurve.smulNodePair_fst ModularCurve.coe_nodeEquivOfPlaces_symm_apply ModularCurve.coe_jGeomGen ModularCurve.coe_jNGeomGen ModularCurve.coe_uniformizerMod ModularCurve.qSeriesBar_jModElt ModularCurve.qInftyPlaceMod_toValuationSubring ModularCurve.qInftyPlaceBar_toValuationSubring ModularCurve.qSeriesBar_zero ModularCurve.qSeriesBar_add ModularCurve.cuspInftyFull_toValuationSubring ModularCurve.qInftyPlaceRat_toValuationSubring"
p2m_attr_erase "simp" "ModularCurve.qSeriesBar_mul ModularCurve.qSeriesBar_div ModularCurve.qSeriesBar_eq_zero_iff ModularCurve.coe_uniformizerBar ModularCurve.qSeriesBar_pow ModularCurve.cuspInfty_toValuationSubring ModularCurve.qSeriesBar_one ModularCurve.qSeriesBar_inv ModularCurve.qSeriesBar_sub ModularCurve.qSeriesBar_neg ModularCurve.charLGeomModuliDictionary_single ModularCurve.specializeModuli_single ModularCurve.specializePlace_def ModularCurve.gamma0PairMap_gen ModularCurve.moduliPointMapRingHom_mk ModularCurve.Gamma0Pair.mk.injEq ModularCurve.ModuliPoint.j_mk ModularCurve.Gamma0Pair.mk.sizeOf_spec ModularCurve.gamma0PairMap_toCurve WeierstrassCurve.Affine.vcY_vcYInv WeierstrassCurve.Affine.vcXInv_vcX WeierstrassCurve.Affine.Point.vcFun_zero WeierstrassCurve.Affine.vcX_vcXInv WeierstrassCurve.Affine.vcYInv_vcY WeierstrassCurve.Affine.Point.vcInvFun_zero WeierstrassCurve.ratPointHom_apply WeierstrassCurve.ratPointMap_zero ModularCurve.ComapPlace.place_toValuationSubring ModularCurve.ModuliTestDatum.restrictLevel_emb ModularCurve.ModuliTestDatum.restrictLevel_res ModularCurve.ModuliTestDatum.mk.injEq ModularCurve.ModuliTestDatum.restrictLevel_W ModularCurve.ModuliTestDatum.place_toValuationSubring ModularCurve.ModuliTestDatum.restrictLevel_curve ModularCurve.ModuliTestDatum.resEquiv_apply ModularCurve.ModuliTestDatum.restrictLevel_gen ModularCurve.ModuliTestDatum.mk.sizeOf_spec ModularCurve.coe_jqNFull ModularCurve.qExpandAlgHomC_apply ModularCurve.coeffEmb_coeff"
p2m_attr_erase "simp" "ModularCurve.coeffMap_coeff ModularCurve.coeffMap_id ModularCurve.coeffMap_single ModularCurve.Gamma0Pair.map_toCurve WeierstrassCurve.mapPoint_eq_ratPointMap ModularCurve.Gamma0Pair.map_gen ModularCurve.Gamma0Pair.map_eq_gamma0PairMap ModularCurve.ModuliPoint.map_eq_moduliPointMapRingHom ModularCurve.ModuliPoint.map_mk WeierstrassCurve.mapPointHom_apply WeierstrassCurve.mapPoint_zero WeierstrassCurve.twoVeluCurve_a₁ WeierstrassCurve.twoVeluCurve_a₂ WeierstrassCurve.twoVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₂ WeierstrassCurve.xVeluCurve_a₁ WeierstrassCurve.veluWSum_empty WeierstrassCurve.veluQuotient_a₁ WeierstrassCurve.veluQuotient_a₃ WeierstrassCurve.veluQuotient_empty WeierstrassCurve.veluTSum_empty WeierstrassCurve.veluQuotient_a₂ WeierstrassCurve.veluQuotient2_a₂ WeierstrassCurve.veluQuotient2_a₃ WeierstrassCurve.veluQuotient2_a₁ WeierstrassCurve.veluPointMap2_zero WeierstrassCurve.Affine.Point.coordsOrZero_some WeierstrassCurve.Affine.Point.coordsOrZero_zero"

set_option autoImplicit false

set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

open scoped TensorProduct Quaternion NumberField Pointwise
open IsDedekindDomain NumberField QuaternionAlgebra CerednikDrinfeld

namespace CSTowerT21
namespace Stab

variable {a b : ℚ}

local notation "ℍ𝔸" => ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ
local notation "ev" w => Submodule.finiteAdeleEvalAt ℍ[ℚ, a, b] w

noncomputable abbrev evU (w : HeightOneSpectrum (𝓞 ℚ)) :
    (ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ →* (ℍ[ℚ, a, b] ⊗[ℚ] w.adicCompletion ℚ)ˣ :=
  Units.map (Submodule.finiteAdeleEvalAt ℍ[ℚ, a, b] w).toRingHom.toMonoidHom

def boxGen (Λ : Submodule ℤ ℍ[ℚ, a, b]) : Set (ℍ𝔸) :=
  {x | ∃ z ∈ Λ, ∃ c : FiniteAdeleRing (𝓞 ℚ) ℚ,
      (∀ v : HeightOneSpectrum (𝓞 ℚ), c v ∈ v.adicCompletionIntegers ℚ) ∧ x = z ⊗ₜ[ℚ] c}

theorem mem_box_iff_span {Λ : Submodule ℤ ℍ[ℚ, a, b]} {x : ℍ𝔸} :
    x ∈ Submodule.finiteAdeleBox Λ ↔ x ∈ Submodule.span ℤ (boxGen Λ) := by
  have e : Submodule.finiteAdeleBox Λ = (Submodule.span ℤ (boxGen Λ)).toAddSubgroup := by
    rw [Submodule.span_int_eq_addSubgroupClosure]; rfl
  rw [e]; rfl

theorem box_mul_mem {Λ : Submodule ℤ ℍ[ℚ, a, b]} (hΛ : IsOrder Λ)
    {x y : ℍ𝔸} (hx : x ∈ Submodule.finiteAdeleBox Λ) (hy : y ∈ Submodule.finiteAdeleBox Λ) :
    x * y ∈ Submodule.finiteAdeleBox Λ := by
  rw [mem_box_iff_span] at hx hy ⊢
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

theorem one_mem_box {Λ : Submodule ℤ ℍ[ℚ, a, b]} (hΛ : IsOrder Λ) : (1 : ℍ𝔸) ∈ Submodule.finiteAdeleBox Λ := by
  unfold Submodule.finiteAdeleBox
  refine AddSubgroup.subset_closure ⟨1, hΛ.one_mem, 1, fun v => ?_, rfl⟩
  have e : (1 : FiniteAdeleRing (𝓞 ℚ) ℚ) v = 1 := rfl
  rw [e]; exact one_mem _

private theorem _root_.CSTowerT21.Stab.mem_stabilizer_iff {Λ : Submodule ℤ ℍ[ℚ, a, b]} (hΛ : IsOrder Λ) (u : (ℍ𝔸)ˣ) :
    u ∈ Submodule.finiteIdeleStabilizer Λ ↔
      (u : ℍ𝔸) ∈ Submodule.finiteAdeleBox Λ ∧ ((u⁻¹ : (ℍ𝔸)ˣ) : ℍ𝔸) ∈ Submodule.finiteAdeleBox Λ := by
  constructor
  · intro hu
    have key : ∀ w : (ℍ𝔸)ˣ, w ∈ Submodule.finiteIdeleStabilizer Λ → (w : ℍ𝔸) ∈ Submodule.finiteAdeleBox Λ := by
      intro w hw
      have h := (Submodule.mem_finiteIdeleStabilizer_iff Λ w).mp hw
      have h1 : (w : ℍ𝔸) * 1 ∈ w • ((Submodule.finiteAdeleBox Λ : AddSubgroup ℍ𝔸) : Set ℍ𝔸) :=
        Set.smul_mem_smul_set (one_mem_box hΛ)
      rw [h, mul_one] at h1
      exact h1
    exact ⟨key u hu, key u⁻¹ (inv_mem hu)⟩
  · rintro ⟨hu, hui⟩
    rw [Submodule.mem_finiteIdeleStabilizer_iff]
    apply Set.Subset.antisymm
    · rintro _ ⟨x, hx, rfl⟩
      exact box_mul_mem hΛ hu hx
    · intro x hx
      refine ⟨(u⁻¹ : (ℍ𝔸)ˣ) • x, box_mul_mem hΛ hui hx, ?_⟩
      show (u : ℍ𝔸) * (((u⁻¹ : (ℍ𝔸)ˣ) : ℍ𝔸) * x) = x
      rw [← mul_assoc, Units.mul_inv, one_mul]

p2m_export "CSTowerT21.Stab" "mem_stabilizer_iff"

theorem isOrder_meetOrder {R : Submodule ℤ ℍ[ℚ, a, b]} (hR : IsOrder R) (g : (ℍ𝔸)ˣ) :
    IsOrder (meetOrder R g) :=
  hR.inf (IsOrder.conjByFiniteIdele R hR g)

theorem mem_finiteIdeleStabilizer_meetOrder_iff {R : Submodule ℤ ℍ[ℚ, a, b]} (hR : IsOrder R) (g u : (ℍ𝔸)ˣ) :
    u ∈ Submodule.finiteIdeleStabilizer (meetOrder R g) ↔
      u ∈ Submodule.finiteIdeleStabilizer R ∧ g⁻¹ * u * g ∈ Submodule.finiteIdeleStabilizer R := by
  obtain ⟨hbox, -, hle, hconj⟩ := IsOrder.finiteAdeleBox_inf_conjByFiniteIdele_eq_and_finiteIdeleStabilizer_le R hR g
  constructor
  · intro hu
    exact ⟨hle hu, hconj u hu⟩
  · rintro ⟨hu, hgu⟩
    have hRg : IsOrder (meetOrder R g) := isOrder_meetOrder hR g
    rw [mem_stabilizer_iff hR] at hu hgu
    rw [mem_stabilizer_iff hRg]
    rw [show meetOrder R g = R ⊓ Submodule.conjByFiniteIdele R g from rfl, hbox]
    have key : ∀ w : ℍ𝔸, w ∈ Submodule.finiteAdeleBox R →
        ((g⁻¹ : (ℍ𝔸)ˣ) : ℍ𝔸) * w * (g : ℍ𝔸) ∈ Submodule.finiteAdeleBox R →
        w ∈ Submodule.finiteAdeleBox R ⊓ (Submodule.finiteAdeleBox R).map
          ((AddMonoidHom.mulRight ((g⁻¹ : (ℍ𝔸)ˣ) : ℍ𝔸)).comp (AddMonoidHom.mulLeft (g : ℍ𝔸))) := by
      intro w hw hgw
      refine ⟨hw, ⟨_, hgw, ?_⟩⟩
      simp only [AddMonoidHom.coe_comp, Function.comp_apply, AddMonoidHom.coe_mulLeft, AddMonoidHom.coe_mulRight]
      rw [← mul_assoc, ← mul_assoc, Units.mul_inv, one_mul, mul_assoc, Units.mul_inv, mul_one]
    refine ⟨key _ hu.1 ?_, key _ hu.2 ?_⟩
    · simpa only [Units.val_mul] using hgu.1
    · have e : (((g⁻¹ * u * g)⁻¹ : (ℍ𝔸)ˣ) : ℍ𝔸) = ((g⁻¹ : (ℍ𝔸)ˣ) : ℍ𝔸) * ((u⁻¹ : (ℍ𝔸)ˣ) : ℍ𝔸) * (g : ℍ𝔸) := by
        rw [mul_inv_rev, mul_inv_rev, inv_inv, Units.val_mul, Units.val_mul, mul_assoc]
      rw [← e]; exact hgu.2

theorem finiteIdeleStabilizer_meetOrder_eq {R : Submodule ℤ ℍ[ℚ, a, b]} (hR : IsOrder R) (g : (ℍ𝔸)ˣ) :
    Submodule.finiteIdeleStabilizer (meetOrder R g) =
      Submodule.finiteIdeleStabilizer R ⊓ (Submodule.finiteIdeleStabilizer R).map (MulAut.conj g).toMonoidHom := by
  ext u
  rw [mem_finiteIdeleStabilizer_meetOrder_iff hR, Subgroup.mem_inf, Subgroup.mem_map_equiv, MulAut.conj_symm_apply]

def localBoxGen (Λ : Submodule ℤ ℍ[ℚ, a, b]) (v : HeightOneSpectrum (𝓞 ℚ)) : Set (ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ) :=
  {x | ∃ z ∈ Λ, ∃ c : v.adicCompletion ℚ, c ∈ v.adicCompletionIntegers ℚ ∧ x = z ⊗ₜ[ℚ] c}

theorem mem_localBox_iff_span {Λ : Submodule ℤ ℍ[ℚ, a, b]} {v : HeightOneSpectrum (𝓞 ℚ)}
    {x : ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ} :
    x ∈ Submodule.localBox Λ v ↔ x ∈ Submodule.span ℤ (localBoxGen Λ v) := by
  have : Submodule.localBox Λ v = (Submodule.span ℤ (localBoxGen Λ v)).toAddSubgroup := by
    rw [Submodule.span_int_eq_addSubgroupClosure]; rfl
  rw [this]; rfl

theorem finiteAdeleEvalAt_mem_localBox {Λ : Submodule ℤ ℍ[ℚ, a, b]} (v : HeightOneSpectrum (𝓞 ℚ))
    {x : ℍ𝔸} (hx : x ∈ Submodule.finiteAdeleBox Λ) :
    (ev v) x ∈ Submodule.localBox Λ v := by
  rw [mem_box_iff_span] at hx
  rw [mem_localBox_iff_span]
  induction hx using Submodule.span_induction with
  | mem x hx' =>
    obtain ⟨z, hz, c, hc, rfl⟩ := hx'
    refine Submodule.subset_span ⟨z, hz, c v, hc v, ?_⟩
    simp [Submodule.finiteAdeleEvalAt, Submodule.finiteAdeleEvalAlgHom_apply]
  | zero => rw [map_zero]; exact zero_mem _
  | add x₁ x₂ _ _ h₁ h₂ => rw [map_add]; exact add_mem h₁ h₂
  | smul m x₁ _ h₁ => rw [map_zsmul]; exact Submodule.smul_mem _ _ h₁

theorem localBox_mul_mem {Λ : Submodule ℤ ℍ[ℚ, a, b]} (hΛ : IsOrder Λ) (v : HeightOneSpectrum (𝓞 ℚ))
    {x y : ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ} (hx : x ∈ Submodule.localBox Λ v) (hy : y ∈ Submodule.localBox Λ v) :
    x * y ∈ Submodule.localBox Λ v := by
  rw [mem_localBox_iff_span] at hx hy ⊢
  induction hy using Submodule.span_induction with
  | mem y hy' =>
    obtain ⟨z, hz, c, hc, rfl⟩ := hy'
    induction hx using Submodule.span_induction with
    | mem x hx' =>
      obtain ⟨z', hz', c', hc', rfl⟩ := hx'
      refine Submodule.subset_span ⟨z' * z, hΛ.mul_mem hz' hz, c' * c, mul_mem hc' hc, ?_⟩
      rw [Algebra.TensorProduct.tmul_mul_tmul]
    | zero => rw [zero_mul]; exact zero_mem _
    | add x₁ x₂ _ _ h₁ h₂ => rw [add_mul]; exact add_mem h₁ h₂
    | smul m x₁ _ h₁ => rw [smul_mul_assoc]; exact Submodule.smul_mem _ _ h₁
  | zero => rw [mul_zero]; exact zero_mem _
  | add y₁ y₂ _ _ h₁ h₂ => rw [mul_add]; exact add_mem h₁ h₂
  | smul m y₁ _ h₁ => rw [mul_smul_comm]; exact Submodule.smul_mem _ _ h₁

theorem one_mem_localBox {Λ : Submodule ℤ ℍ[ℚ, a, b]} (hΛ : IsOrder Λ) (v : HeightOneSpectrum (𝓞 ℚ)) :
    (1 : ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ) ∈ Submodule.localBox Λ v := by
  rw [mem_localBox_iff_span]
  exact Submodule.subset_span ⟨1, hΛ.one_mem, 1, one_mem _, rfl⟩

theorem ev_smul (v : HeightOneSpectrum (𝓞 ℚ)) (c : ℚ) (x : ℍ𝔸) : (ev v) (c • x) = c • (ev v) x := map_smul _ _ _

theorem ratSmul_eq_one_tmul_mul (v : HeightOneSpectrum (𝓞 ℚ)) (c : ℚ) (x : ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ) :
    c • x = ((1 : ℍ[ℚ, a, b]) ⊗ₜ[ℚ] algebraMap ℚ (v.adicCompletion ℚ) c) * x := by
  have e1 : ((1 : ℍ[ℚ, a, b]) ⊗ₜ[ℚ] algebraMap ℚ (v.adicCompletion ℚ) c) = c • (1 : ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ) := by
    rw [Algebra.TensorProduct.one_def, TensorProduct.smul_tmul', TensorProduct.smul_tmul, Algebra.smul_def, mul_one]
  rw [e1, smul_mul_assoc, one_mul]

theorem smul_mem_localBox {Λ : Submodule ℤ ℍ[ℚ, a, b]} (v : HeightOneSpectrum (𝓞 ℚ)) {c : ℚ}
    (hc : algebraMap ℚ (v.adicCompletion ℚ) c ∈ v.adicCompletionIntegers ℚ)
    {x : ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ} (hx : x ∈ Submodule.localBox Λ v) : c • x ∈ Submodule.localBox Λ v := by
  rw [ratSmul_eq_one_tmul_mul, mem_localBox_iff_span]
  rw [mem_localBox_iff_span] at hx
  induction hx using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨z, hz, c', hc', rfl⟩ := hy
    refine Submodule.subset_span ⟨z, hz, algebraMap ℚ (v.adicCompletion ℚ) c * c', mul_mem hc hc', ?_⟩
    rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul]
  | zero => rw [mul_zero]; exact zero_mem _
  | add x₁ x₂ _ _ h₁ h₂ => rw [mul_add]; exact add_mem h₁ h₂
  | smul m x₁ _ h₁ => rw [mul_smul_comm]; exact Submodule.smul_mem _ _ h₁

theorem inv_natCast_mem_adicCompletionIntegers (v : HeightOneSpectrum (𝓞 ℚ)) (n : ℕ)
    (hnv : ((n : ℕ) : 𝓞 ℚ) ∉ v.asIdeal) :
    ((n : v.adicCompletion ℚ))⁻¹ ∈ v.adicCompletionIntegers ℚ := by
  have h1 : ((n : ℕ) : v.adicCompletion ℚ) = algebraMap (𝓞 ℚ) (v.adicCompletion ℚ) ((n : ℕ) : 𝓞 ℚ) := by
    rw [map_natCast]
  rw [HeightOneSpectrum.mem_adicCompletionIntegers, map_inv₀, h1]
  have h2 := HeightOneSpectrum.valuedAdicCompletion_eq_valuation (K := ℚ) v ((n : ℕ) : 𝓞 ℚ)
  erw [h2, (HeightOneSpectrum.valuation_eq_one_iff_notMem (K := ℚ) v).mpr hnv, inv_one]

theorem algebraMap_inv_natCast_mem (v : HeightOneSpectrum (𝓞 ℚ)) (n : ℕ) (hnv : ((n : ℕ) : 𝓞 ℚ) ∉ v.asIdeal) :
    algebraMap ℚ (v.adicCompletion ℚ) ((n : ℚ)⁻¹) ∈ v.adicCompletionIntegers ℚ := by
  rw [map_inv₀, map_natCast]; exact inv_natCast_mem_adicCompletionIntegers v n hnv

theorem ev_mem_localBox_of_smul_mem {Λ : Submodule ℤ ℍ[ℚ, a, b]} {c : ℕ} (hc : c ≠ 0) (v : HeightOneSpectrum (𝓞 ℚ))
    (hv : ((c : ℕ) : 𝓞 ℚ) ∉ v.asIdeal) {y : ℍ𝔸} (hy : (c : ℚ) • y ∈ Submodule.finiteAdeleBox Λ) :
    (ev v) y ∈ Submodule.localBox Λ v := by
  have := smul_mem_localBox v (algebraMap_inv_natCast_mem v c hv) (finiteAdeleEvalAt_mem_localBox v hy)
  rwa [ev_smul, smul_smul, inv_mul_cancel₀ (by exact_mod_cast hc : (c : ℚ) ≠ 0), one_smul] at this

theorem natGenerator_dvd_iff' (v : HeightOneSpectrum (𝓞 ℚ)) (n : ℕ) :
    Rat.HeightOneSpectrum.natGenerator v ∣ n ↔ ((n : ℕ) : 𝓞 ℚ) ∈ v.asIdeal := by
  rw [Rat.HeightOneSpectrum.natGenerator_dvd_iff, ← map_natCast (Rat.IsIntegralClosure.intEquiv (𝓞 ℚ)) n,
    Ideal.apply_mem_of_equiv_iff]

theorem not_mem_of_prime_ne {p ℓ : ℕ} (hp : p.Prime) (hℓ : ℓ.Prime) (hne : ℓ ≠ p) {v : HeightOneSpectrum (𝓞 ℚ)}
    (hv : ((p : ℕ) : 𝓞 ℚ) ∈ v.asIdeal) : ((ℓ : ℕ) : 𝓞 ℚ) ∉ v.asIdeal := by
  intro hℓv
  rw [← natGenerator_dvd_iff'] at hv hℓv
  have h1 := (Nat.prime_dvd_prime_iff_eq (Rat.HeightOneSpectrum.prime_natGenerator v) hp).mp hv
  have h2 := (Nat.prime_dvd_prime_iff_eq (Rat.HeightOneSpectrum.prime_natGenerator v) hℓ).mp hℓv
  exact hne (h2.symm.trans h1)

theorem exists_place (p : ℕ) (hp : p.Prime) : ∃ v : HeightOneSpectrum (𝓞 ℚ), ((p : ℕ) : 𝓞 ℚ) ∈ v.asIdeal := by
  refine ⟨(Rat.HeightOneSpectrum.primesEquiv (R := 𝓞 ℚ)).symm ⟨p, hp⟩, ?_⟩
  rw [← natGenerator_dvd_iff']
  have : Rat.HeightOneSpectrum.natGenerator ((Rat.HeightOneSpectrum.primesEquiv (R := 𝓞 ℚ)).symm ⟨p, hp⟩) = p := by
    have e := (Rat.HeightOneSpectrum.primesEquiv (R := 𝓞 ℚ)).apply_symm_apply ⟨p, hp⟩
    exact congrArg Subtype.val e
  rw [this]

theorem mem_localBoxUnits_iff' (Λ : Submodule ℤ ℍ[ℚ, a, b]) (v : HeightOneSpectrum (𝓞 ℚ))
    (t : (ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ)ˣ) :
    t ∈ Submodule.localBoxUnits Λ v ↔
      (t : ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ) ∈ Submodule.localBox Λ v ∧
        ((t⁻¹ : (ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ)ˣ) : ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ) ∈ Submodule.localBox Λ v :=
  Submodule.mem_localBoxUnits_iff Λ v t

theorem conj_mem_localBoxUnits_iff {Λ : Submodule ℤ ℍ[ℚ, a, b]} (hΛ : IsOrder Λ) (v : HeightOneSpectrum (𝓞 ℚ))
    {g : (ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ)ˣ} (hg : g ∈ Submodule.localBoxUnits Λ v)
    (t : (ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ)ˣ) :
    g⁻¹ * t * g ∈ Submodule.localBoxUnits Λ v ↔ t ∈ Submodule.localBoxUnits Λ v := by
  rw [mem_localBoxUnits_iff'] at hg
  have key : ∀ s : (ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ)ˣ, s ∈ Submodule.localBoxUnits Λ v →
      g⁻¹ * s * g ∈ Submodule.localBoxUnits Λ v := by
    intro s hs
    rw [mem_localBoxUnits_iff'] at hs ⊢
    refine ⟨?_, ?_⟩
    · rw [Units.val_mul, Units.val_mul]
      exact localBox_mul_mem hΛ v (localBox_mul_mem hΛ v hg.2 hs.1) hg.1
    · rw [mul_inv_rev, mul_inv_rev, inv_inv, Units.val_mul, Units.val_mul]
      exact localBox_mul_mem hΛ v hg.2 (localBox_mul_mem hΛ v hs.2 hg.1)
  constructor
  · intro h
    have hgi : g⁻¹ ∈ Submodule.localBoxUnits Λ v := by
      rw [mem_localBoxUnits_iff', inv_inv]; exact ⟨hg.2, hg.1⟩
    have h2 := key _ h

    have key' : ∀ s : (ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ)ˣ, s ∈ Submodule.localBoxUnits Λ v →
        g * s * g⁻¹ ∈ Submodule.localBoxUnits Λ v := by
      intro s hs
      rw [mem_localBoxUnits_iff'] at hs ⊢
      refine ⟨?_, ?_⟩
      · rw [Units.val_mul, Units.val_mul]
        exact localBox_mul_mem hΛ v (localBox_mul_mem hΛ v hg.1 hs.1) hg.2
      · rw [mul_inv_rev, mul_inv_rev, inv_inv, Units.val_mul, Units.val_mul]
        exact localBox_mul_mem hΛ v hg.1 (localBox_mul_mem hΛ v hs.2 hg.2)
    have h3 := key' _ h
    have e : g * (g⁻¹ * t * g) * g⁻¹ = t := by group
    rwa [e] at h3
  · exact key t

theorem map_mem_localBoxUnits_of_mem_stabilizer {Λ : Submodule ℤ ℍ[ℚ, a, b]} (hΛ : IsOrder Λ) {u : (ℍ𝔸)ˣ}
    (hu : u ∈ Submodule.finiteIdeleStabilizer Λ) (v : HeightOneSpectrum (𝓞 ℚ)) :
    (evU (a := a) (b := b) v) u ∈ Submodule.localBoxUnits Λ v :=
  (IsOrder.mem_finiteIdeleStabilizer_iff_forall_map_finiteAdeleEvalAt_mem_localBoxUnits Λ hΛ u).mp hu v

theorem map_mem_localBoxUnits_of_mem_primeHeckeSet {Λ : Submodule ℤ ℍ[ℚ, a, b]} {p : ℕ} (hp : p ≠ 0)
    {g : (ℍ𝔸)ˣ} (hg : g ∈ primeHeckeSet Λ p) {v : HeightOneSpectrum (𝓞 ℚ)} (hv : ((p : ℕ) : 𝓞 ℚ) ∉ v.asIdeal) :
    (evU (a := a) (b := b) v) g ∈ Submodule.localBoxUnits Λ v := by
  obtain ⟨h1, h2, -, -⟩ := hg
  rw [mem_localBoxUnits_iff', Units.coe_map, Units.coe_map_inv]
  exact ⟨finiteAdeleEvalAt_mem_localBox v h1, ev_mem_localBox_of_smul_mem hp v hv h2⟩

theorem mem_localBoxUnits_meetOrder_iff {R : Submodule ℤ ℍ[ℚ, a, b]} (hR : IsOrder R) (g : (ℍ𝔸)ˣ)
    (v : HeightOneSpectrum (𝓞 ℚ)) (t : (ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ)ˣ) :
    t ∈ Submodule.localBoxUnits (meetOrder R g) v ↔
      t ∈ Submodule.localBoxUnits R v ∧ ((evU (a := a) (b := b) v) g)⁻¹ * t * (evU (a := a) (b := b) v) g ∈ Submodule.localBoxUnits R v := by
  have hc : IsOrder (Submodule.conjByFiniteIdele R g) := IsOrder.conjByFiniteIdele R hR g
  have hbox : ∀ x : ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ, x ∈ Submodule.localBox (meetOrder R g) v ↔
      x ∈ Submodule.localBox R v ∧
        (ev v) ((g⁻¹ : (ℍ𝔸)ˣ) : ℍ𝔸) * x * (ev v) (g : ℍ𝔸) ∈ Submodule.localBox R v := by
    intro x
    rw [show meetOrder R g = R ⊓ Submodule.conjByFiniteIdele R g from rfl,
      Submodule.localBox_inf R (Submodule.conjByFiniteIdele R g) hR.fg hR.spanTop hc.fg hc.spanTop v,
      AddSubgroup.mem_inf, Submodule.mem_localBox_conjByFiniteIdele_iff R hR.fg hR.spanTop g v]
    have i3 : (ev v) (g : ℍ𝔸) * (ev v) ((g⁻¹ : (ℍ𝔸)ˣ) : ℍ𝔸) = 1 := by rw [← map_mul, Units.mul_inv, map_one]
    have i4 : (ev v) ((g⁻¹ : (ℍ𝔸)ˣ) : ℍ𝔸) * (ev v) (g : ℍ𝔸) = 1 := by rw [← map_mul, Units.inv_mul, map_one]
    refine and_congr Iff.rfl ⟨?_, ?_⟩
    · rintro ⟨y, hy, rfl⟩
      rw [← mul_assoc, ← mul_assoc, i4, one_mul, mul_assoc, i4, mul_one]; exact hy
    · intro h
      refine ⟨_, h, ?_⟩
      rw [← mul_assoc, ← mul_assoc, i3, one_mul, mul_assoc, i3, mul_one]
  rw [mem_localBoxUnits_iff', mem_localBoxUnits_iff', mem_localBoxUnits_iff', hbox, hbox]
  simp only [Units.val_mul, Units.coe_map, Units.coe_map_inv, mul_inv_rev, inv_inv, MonoidHom.coe_coe,
    RingHom.coe_coe, RingHom.toMonoidHom_eq_coe, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom]
  constructor
  · rintro ⟨⟨h1, h2⟩, h3, h4⟩
    exact ⟨⟨h1, h3⟩, by simpa only [mul_assoc, MonoidHom.coe_coe, RingHom.coe_coe, AlgHom.coe_toRingHom] using h2,
      by simpa only [mul_assoc, MonoidHom.coe_coe, RingHom.coe_coe, AlgHom.coe_toRingHom] using h4⟩
  · rintro ⟨⟨h1, h3⟩, h2, h4⟩
    exact ⟨⟨h1, by simpa only [mul_assoc, MonoidHom.coe_coe, RingHom.coe_coe, AlgHom.coe_toRingHom] using h2⟩, h3,
      by simpa only [mul_assoc, MonoidHom.coe_coe, RingHom.coe_coe, AlgHom.coe_toRingHom] using h4⟩

theorem one_mem_localBoxUnits {Λ : Submodule ℤ ℍ[ℚ, a, b]} (hΛ : IsOrder Λ) (v : HeightOneSpectrum (𝓞 ℚ)) :
    (1 : (ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ)ˣ) ∈ Submodule.localBoxUnits Λ v := by
  rw [mem_localBoxUnits_iff', inv_one, Units.val_one]
  exact ⟨one_mem_localBox hΛ v, one_mem_localBox hΛ v⟩

theorem mem_stabilizer_iff_forall {Λ : Submodule ℤ ℍ[ℚ, a, b]} (hΛ : IsOrder Λ) (u : (ℍ𝔸)ˣ) :
    u ∈ Submodule.finiteIdeleStabilizer Λ ↔ ∀ v, (evU (a := a) (b := b) v) u ∈ Submodule.localBoxUnits Λ v :=
  IsOrder.mem_finiteIdeleStabilizer_iff_forall_map_finiteAdeleEvalAt_mem_localBoxUnits Λ hΛ u

private theorem _root_.CSTowerT21.Stab.eq_of_natCast_prime_mem {ℓ : ℕ} (hℓ : ℓ.Prime) {v w : HeightOneSpectrum (𝓞 ℚ)}
    (hv : ((ℓ : ℕ) : 𝓞 ℚ) ∈ v.asIdeal) (hw : ((ℓ : ℕ) : 𝓞 ℚ) ∈ w.asIdeal) : v = w := by
  apply (Rat.HeightOneSpectrum.primesEquiv (R := 𝓞 ℚ)).injective
  apply Subtype.ext
  show Rat.HeightOneSpectrum.natGenerator v = Rat.HeightOneSpectrum.natGenerator w
  rw [← natGenerator_dvd_iff'] at hv hw
  rw [(Nat.prime_dvd_prime_iff_eq (Rat.HeightOneSpectrum.prime_natGenerator v) hℓ).mp hv,
    (Nat.prime_dvd_prime_iff_eq (Rat.HeightOneSpectrum.prime_natGenerator w) hℓ).mp hw]

p2m_export "CSTowerT21.Stab" "eq_of_natCast_prime_mem"
end CSTowerT21.Stab

namespace CSTowerT21
namespace Nat

noncomputable def placesOf (ℓ : ℕ) : Finset (HeightOneSpectrum (𝓞 ℚ)) :=
  if h : (Ideal.span {(ℓ : 𝓞 ℚ)} : Ideal (𝓞 ℚ)) = ⊥ then ∅ else (Ideal.finite_factors h).toFinset

theorem span_natCast_ne_bot {ℓ : ℕ} (hℓ : ℓ ≠ 0) : (Ideal.span {(ℓ : 𝓞 ℚ)} : Ideal (𝓞 ℚ)) ≠ ⊥ := by
  rw [Ne, Ideal.span_singleton_eq_bot]
  exact_mod_cast hℓ

theorem mem_placesOf_iff {ℓ : ℕ} (hℓ : ℓ ≠ 0) (v : HeightOneSpectrum (𝓞 ℚ)) :
    v ∈ placesOf ℓ ↔ (ℓ : 𝓞 ℚ) ∈ v.asIdeal := by
  rw [placesOf, dif_neg (span_natCast_ne_bot hℓ), Set.Finite.mem_toFinset, Set.mem_setOf_eq,
    Ideal.dvd_span_singleton]

theorem inv_natCast_mem_adicCompletionIntegers_of_not_mem_placesOf {ℓ : ℕ} (hℓ : ℓ ≠ 0)
    {v : HeightOneSpectrum (𝓞 ℚ)} (hv : v ∉ placesOf ℓ) :
    algebraMap ℚ (v.adicCompletion ℚ) ((ℓ : ℚ)⁻¹) ∈ v.adicCompletionIntegers ℚ := by
  rw [mem_placesOf_iff hℓ] at hv
  rw [HeightOneSpectrum.mem_adicCompletionIntegers,
    show Valued.v (algebraMap ℚ (v.adicCompletion ℚ) ((ℓ : ℚ)⁻¹)) = v.valuation ℚ ((ℓ : ℚ)⁻¹) from
      HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v _, map_inv₀]
  have h1 : v.valuation ℚ (ℓ : ℚ) = 1 := by
    have : (ℓ : ℚ) = algebraMap (𝓞 ℚ) ℚ (ℓ : 𝓞 ℚ) := by simp
    rw [this, HeightOneSpectrum.valuation_of_algebraMap]
    have hle := v.intValuation_le_one (ℓ : 𝓞 ℚ)
    have hnlt : ¬ v.intValuation (ℓ : 𝓞 ℚ) < 1 := by
      rw [HeightOneSpectrum.intValuation_lt_one_iff_mem]
      exact hv
    exact le_antisymm hle (not_lt.mp hnlt)
  rw [h1, inv_one]

theorem disjoint_placesOf_of_coprime {ℓ ℓ' : ℕ} (hℓ : ℓ ≠ 0) (hℓ' : ℓ' ≠ 0) (h : ℓ.Coprime ℓ') :
    Disjoint (placesOf ℓ) (placesOf ℓ') := by
  rw [Finset.disjoint_left]
  intro v hv hv'
  rw [mem_placesOf_iff hℓ] at hv
  rw [mem_placesOf_iff hℓ'] at hv'
  have hcop : IsCoprime (ℓ : 𝓞 ℚ) (ℓ' : 𝓞 ℚ) := by
    have := (Nat.isCoprime_iff_coprime.mpr h : IsCoprime (ℓ : ℤ) (ℓ' : ℤ))
    simpa using this.map (Int.castRingHom (𝓞 ℚ))
  obtain ⟨x, y, hxy⟩ := hcop
  apply v.isPrime.ne_top
  rw [Ideal.eq_top_iff_one, ← hxy]
  exact Ideal.add_mem _ (Ideal.mul_mem_left _ _ hv) (Ideal.mul_mem_left _ _ hv')

theorem not_mem_placesOf_of_mem_placesOf_of_coprime {ℓ ℓ' : ℕ} (hℓ : ℓ ≠ 0) (hℓ' : ℓ' ≠ 0) (h : ℓ.Coprime ℓ')
    {v : HeightOneSpectrum (𝓞 ℚ)} (hv : v ∈ placesOf ℓ) : v ∉ placesOf ℓ' :=
  Finset.disjoint_left.mp (disjoint_placesOf_of_coprime hℓ hℓ' h) hv

theorem isMaximal_span_natCast_of_prime {p : ℕ} (hp : p.Prime) :
    (Ideal.span {(p : 𝓞 ℚ)} : Ideal (𝓞 ℚ)).IsMaximal := by
  have e : 𝓞 ℚ ≃+* ℤ := Rat.ringOfIntegersEquiv
  have hpZ : _root_.Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp
  have hpO : _root_.Prime (p : 𝓞 ℚ) := by
    have : (p : 𝓞 ℚ) = e.symm (p : ℤ) := by rw [map_natCast]
    rw [this]
    exact (MulEquiv.prime_iff (e.symm : ℤ ≃* 𝓞 ℚ)).mpr hpZ
  have hprime : (Ideal.span {(p : 𝓞 ℚ)} : Ideal (𝓞 ℚ)).IsPrime := (Ideal.span_singleton_prime hpO.ne_zero).mpr hpO
  exact hprime.isMaximal (span_natCast_ne_bot hp.ne_zero)

namespace HeightOneSpectrum

private theorem _root_.CSTowerT21.Nat.HeightOneSpectrum.eq_of_natCast_prime_mem {p : ℕ} (hp : p.Prime) {v v' : HeightOneSpectrum (𝓞 ℚ)}
    (hv : (p : 𝓞 ℚ) ∈ v.asIdeal) (hv' : (p : 𝓞 ℚ) ∈ v'.asIdeal) : v = v' := by
  have hmax := isMaximal_span_natCast_of_prime hp
  have h1 : v.asIdeal = Ideal.span {(p : 𝓞 ℚ)} :=
    (hmax.eq_of_le v.isPrime.ne_top ((Ideal.span_singleton_le_iff_mem _).mpr hv)).symm
  have h2 : v'.asIdeal = Ideal.span {(p : 𝓞 ℚ)} :=
    (hmax.eq_of_le v'.isPrime.ne_top ((Ideal.span_singleton_le_iff_mem _).mpr hv')).symm
  exact HeightOneSpectrum.ext (h1.trans h2.symm)

end HeightOneSpectrum
p2m_export "CSTowerT21.Nat" "HeightOneSpectrum.eq_of_natCast_prime_mem"
end CSTowerT21.Nat

namespace CSTowerT21
namespace HL

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

theorem mul_mem_primeHeckeSet_of_mem_stabilizer' {Λ : Submodule ℤ ℍ[ℚ, a, b]} (hΛ : QuaternionAlgebra.IsOrder Λ)
    (ℓ : ℕ) {u h : (ℍ𝔸)ˣ} (hu : u ∈ Submodule.finiteIdeleStabilizer Λ) (hh : h ∈ QuaternionAlgebra.primeHeckeSet Λ ℓ) :
    h * u ∈ QuaternionAlgebra.primeHeckeSet Λ ℓ := by
  obtain ⟨h1, h2, h3, h4⟩ := hh
  have hub := coe_mem_box_of_mem_stabilizer hΛ hu
  have huib := coe_inv_mem_box_of_mem_stabilizer hΛ hu
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [Units.val_mul]; exact box_mul_mem hΛ h1 hub
  · rw [mul_inv_rev, Units.val_mul, ← mul_smul_comm]
    exact box_mul_mem hΛ huib h2
  · intro hmem
    apply h3
    have : ((h⁻¹ : (ℍ𝔸)ˣ) : ℍ𝔸) = (u : ℍ𝔸) * (((h * u)⁻¹ : (ℍ𝔸)ˣ) : ℍ𝔸) := by
      rw [mul_inv_rev, Units.val_mul, ← mul_assoc, Units.mul_inv, one_mul]
    rw [this]; exact box_mul_mem hΛ hub hmem
  · intro hmem
    apply h4
    have : (ℓ : ℚ)⁻¹ • (h : ℍ𝔸) = ((ℓ : ℚ)⁻¹ • ((h * u : (ℍ𝔸)ˣ) : ℍ𝔸)) * ((u⁻¹ : (ℍ𝔸)ˣ) : ℍ𝔸) := by
      rw [smul_mul_assoc, Units.val_mul, mul_assoc, Units.mul_inv, mul_one]
    rw [this]; exact box_mul_mem hΛ hmem huib

theorem box_mono {Λ Λ' : Submodule ℤ ℍ[ℚ, a, b]} (h : Λ ≤ Λ') :
    Submodule.finiteAdeleBox Λ ≤ Submodule.finiteAdeleBox Λ' := by
  unfold Submodule.finiteAdeleBox
  refine AddSubgroup.closure_mono ?_
  rintro x ⟨z, hz, c, hc, rfl⟩
  exact ⟨z, h hz, c, hc, rfl⟩

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

theorem stabilizer_mono {S R : Submodule ℤ ℍ[ℚ, a, b]} (hS : QuaternionAlgebra.IsOrder S) (hR : QuaternionAlgebra.IsOrder R)
    (h : S ≤ R) : Submodule.finiteIdeleStabilizer S ≤ Submodule.finiteIdeleStabilizer R := by
  intro u hu
  exact mem_stabilizer_of_coe_mem_of_coe_inv_mem hR (box_mono h (coe_mem_box_of_mem_stabilizer hS hu))
    (box_mono h (coe_inv_mem_box_of_mem_stabilizer hS hu))

private theorem _root_.CSTowerT21.HL.mem_stabilizer_iff {Λ : Submodule ℤ ℍ[ℚ, a, b]} (hΛ : QuaternionAlgebra.IsOrder Λ) (u : (ℍ𝔸)ˣ) :
    u ∈ Submodule.finiteIdeleStabilizer Λ ↔
      (u : ℍ𝔸) ∈ Submodule.finiteAdeleBox Λ ∧ ((u⁻¹ : (ℍ𝔸)ˣ) : ℍ𝔸) ∈ Submodule.finiteAdeleBox Λ :=
  ⟨fun hu => ⟨coe_mem_box_of_mem_stabilizer hΛ hu, coe_inv_mem_box_of_mem_stabilizer hΛ hu⟩,
   fun h => mem_stabilizer_of_coe_mem_of_coe_inv_mem hΛ h.1 h.2⟩

p2m_export "CSTowerT21.HL" "mem_stabilizer_iff"

def localBoxGen (Λ : Submodule ℤ ℍ[ℚ, a, b]) (v : HeightOneSpectrum (𝓞 ℚ)) : Set (ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ) :=
  {x | ∃ z ∈ Λ, ∃ c : v.adicCompletion ℚ, c ∈ v.adicCompletionIntegers ℚ ∧ x = z ⊗ₜ[ℚ] c}

theorem mem_localBox_iff_span {Λ : Submodule ℤ ℍ[ℚ, a, b]} {v : HeightOneSpectrum (𝓞 ℚ)} {x : ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ} :
    x ∈ Submodule.localBox Λ v ↔ x ∈ Submodule.span ℤ (localBoxGen Λ v) := by
  have : Submodule.localBox Λ v = (Submodule.span ℤ (localBoxGen Λ v)).toAddSubgroup := by
    rw [Submodule.span_int_eq_addSubgroupClosure]; rfl
  rw [this]; rfl

theorem finiteAdeleEvalAt_mem_localBox {Λ : Submodule ℤ ℍ[ℚ, a, b]} (v : HeightOneSpectrum (𝓞 ℚ))
    {x : ℍ𝔸} (hx : x ∈ Submodule.finiteAdeleBox Λ) :
    Submodule.finiteAdeleEvalAt ℍ[ℚ, a, b] v x ∈ Submodule.localBox Λ v := by
  rw [mem_box_iff] at hx
  rw [mem_localBox_iff_span]
  induction hx using Submodule.span_induction with
  | mem x hx' =>
    obtain ⟨z, hz, c, hc, rfl⟩ := hx'
    refine Submodule.subset_span ⟨z, hz, c v, hc v, ?_⟩
    simp [Submodule.finiteAdeleEvalAt, Submodule.finiteAdeleEvalAlgHom_apply]
  | zero => rw [map_zero]; exact zero_mem _
  | add x₁ x₂ _ _ h₁ h₂ => rw [map_add]; exact add_mem h₁ h₂
  | smul m x₁ _ h₁ => rw [map_zsmul]; exact Submodule.smul_mem _ _ h₁

theorem tmul_one_mul_mem_localBox {Λ : Submodule ℤ ℍ[ℚ, a, b]} (v : HeightOneSpectrum (𝓞 ℚ))
    {c : v.adicCompletion ℚ} (hc : c ∈ v.adicCompletionIntegers ℚ)
    {x : ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ} (hx : x ∈ Submodule.localBox Λ v) :
    ((1 : ℍ[ℚ, a, b]) ⊗ₜ[ℚ] c) * x ∈ Submodule.localBox Λ v := by
  rw [mem_localBox_iff_span] at hx ⊢
  induction hx using Submodule.span_induction with
  | mem x hx' =>
    obtain ⟨z, hz, c', hc', rfl⟩ := hx'
    refine Submodule.subset_span ⟨z, hz, c * c', mul_mem hc hc', ?_⟩
    rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul]
  | zero => rw [mul_zero]; exact zero_mem _
  | add x₁ x₂ _ _ h₁ h₂ => rw [mul_add]; exact add_mem h₁ h₂
  | smul m x₁ _ h₁ => rw [mul_smul_comm]; exact Submodule.smul_mem _ _ h₁

theorem map_finiteAdeleEvalAt_mem_localBoxUnits_of_mem_primeHeckeSet {Λ : Submodule ℤ ℍ[ℚ, a, b]}
    (ℓ : ℕ) {h : (ℍ𝔸)ˣ} (hh : h ∈ QuaternionAlgebra.primeHeckeSet Λ ℓ)
    (v : HeightOneSpectrum (𝓞 ℚ)) (hℓv : algebraMap ℚ (v.adicCompletion ℚ) ((ℓ : ℚ)⁻¹) ∈ v.adicCompletionIntegers ℚ) :
    Units.map (Submodule.finiteAdeleEvalAt ℍ[ℚ, a, b] v).toRingHom.toMonoidHom h ∈ Submodule.localBoxUnits Λ v := by
  obtain ⟨h1, h2, -, h4⟩ := hh
  rcases Nat.eq_zero_or_pos ℓ with rfl | hℓpos
  · exfalso; apply h4
    rw [Nat.cast_zero, inv_zero, zero_smul]; exact zero_mem _
  have hℓ0 : (ℓ : ℚ) ≠ 0 := by exact_mod_cast hℓpos.ne'
  rw [Submodule.mem_localBoxUnits_iff]
  refine ⟨finiteAdeleEvalAt_mem_localBox v h1, ?_⟩

  set f := Submodule.finiteAdeleEvalAt ℍ[ℚ, a, b] v with hf
  have e1 : (((Units.map f.toRingHom.toMonoidHom h)⁻¹ : (ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ)ˣ) : ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ)
      = f ((h⁻¹ : (ℍ𝔸)ˣ) : ℍ𝔸) := Units.coe_map_inv _ _
  have e2 : f ((h⁻¹ : (ℍ𝔸)ˣ) : ℍ𝔸) =
      ((1 : ℍ[ℚ, a, b]) ⊗ₜ[ℚ] algebraMap ℚ (v.adicCompletion ℚ) ((ℓ : ℚ)⁻¹)) * f ((ℓ : ℚ) • ((h⁻¹ : (ℍ𝔸)ˣ) : ℍ𝔸)) := by
    rw [map_smul, ← Algebra.TensorProduct.algebraMap_apply', ← Algebra.smul_def, smul_smul, inv_mul_cancel₀ hℓ0, one_smul]
  show (((Units.map f.toRingHom.toMonoidHom h)⁻¹ : (ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ)ˣ) : ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ) ∈ _
  rw [e1, e2]
  exact tmul_one_mul_mem_localBox v hℓv (finiteAdeleEvalAt_mem_localBox v h2)

theorem localBox_mono {Λ Λ' : Submodule ℤ ℍ[ℚ, a, b]} (h : Λ ≤ Λ') (v : HeightOneSpectrum (𝓞 ℚ)) :
    Submodule.localBox Λ v ≤ Submodule.localBox Λ' v := by
  unfold Submodule.localBox
  refine AddSubgroup.closure_mono ?_
  rintro x ⟨z, hz, c, hc, rfl⟩
  exact ⟨z, h hz, c, hc, rfl⟩

theorem mul_tmul_one_mem_localBox {Λ : Submodule ℤ ℍ[ℚ, a, b]} (v : HeightOneSpectrum (𝓞 ℚ))
    {c : v.adicCompletion ℚ} (hc : c ∈ v.adicCompletionIntegers ℚ)
    {x : ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ} (hx : x ∈ Submodule.localBox Λ v) :
    x * ((1 : ℍ[ℚ, a, b]) ⊗ₜ[ℚ] c) ∈ Submodule.localBox Λ v := by
  rw [mem_localBox_iff_span] at hx ⊢
  induction hx using Submodule.span_induction with
  | mem x hx' =>
    obtain ⟨z, hz, c', hc', rfl⟩ := hx'
    refine Submodule.subset_span ⟨z, hz, c' * c, mul_mem hc' hc, ?_⟩
    rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one]
  | zero => rw [zero_mul]; exact zero_mem _
  | add x₁ x₂ _ _ h₁ h₂ => rw [add_mul]; exact add_mem h₁ h₂
  | smul m x₁ _ h₁ => rw [smul_mul_assoc]; exact Submodule.smul_mem _ _ h₁

theorem localBox_mul_mem {Λ : Submodule ℤ ℍ[ℚ, a, b]} (hΛ : QuaternionAlgebra.IsOrder Λ) (v : HeightOneSpectrum (𝓞 ℚ))
    {x y : ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ} (hx : x ∈ Submodule.localBox Λ v) (hy : y ∈ Submodule.localBox Λ v) :
    x * y ∈ Submodule.localBox Λ v := by
  rw [mem_localBox_iff_span] at hx hy ⊢
  induction hy using Submodule.span_induction with
  | mem y hy' =>
    obtain ⟨z, hz, c, hc, rfl⟩ := hy'
    induction hx using Submodule.span_induction with
    | mem x hx' =>
      obtain ⟨z', hz', c', hc', rfl⟩ := hx'
      refine Submodule.subset_span ⟨z' * z, hΛ.mul_mem hz' hz, c' * c, mul_mem hc' hc, ?_⟩
      rw [Algebra.TensorProduct.tmul_mul_tmul]
    | zero => rw [zero_mul]; exact zero_mem _
    | add x₁ x₂ _ _ h₁ h₂ => rw [add_mul]; exact add_mem h₁ h₂
    | smul m x₁ _ h₁ => rw [smul_mul_assoc]; exact Submodule.smul_mem _ _ h₁
  | zero => rw [mul_zero]; exact zero_mem _
  | add y₁ y₂ _ _ h₁ h₂ => rw [mul_add]; exact add_mem h₁ h₂
  | smul m y₁ _ h₁ => rw [mul_smul_comm]; exact Submodule.smul_mem _ _ h₁

theorem one_mem_localBox {Λ : Submodule ℤ ℍ[ℚ, a, b]} (hΛ : QuaternionAlgebra.IsOrder Λ) (v : HeightOneSpectrum (𝓞 ℚ)) :
    (1 : ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ) ∈ Submodule.localBox Λ v := by
  rw [mem_localBox_iff_span]
  exact Submodule.subset_span ⟨1, hΛ.one_mem, 1, one_mem _, rfl⟩

theorem tmul_one_mem_localBox {Λ : Submodule ℤ ℍ[ℚ, a, b]} {z : ℍ[ℚ, a, b]} (hz : z ∈ Λ) (v : HeightOneSpectrum (𝓞 ℚ)) :
    z ⊗ₜ[ℚ] (1 : v.adicCompletion ℚ) ∈ Submodule.localBox Λ v := by
  rw [mem_localBox_iff_span]
  exact Submodule.subset_span ⟨z, hz, 1, one_mem _, rfl⟩

end CSTowerT21.HL

namespace CSTowerT21
namespace C4T

variable {a b : ℚ}

local notation "ℍ𝔸" => ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ

open CSTowerT21.HL

theorem mul_mem_localBoxUnits {Λ : Submodule ℤ ℍ[ℚ, a, b]} (hΛ : QuaternionAlgebra.IsOrder Λ) (w : HeightOneSpectrum (𝓞 ℚ))
    {u u' : (ℍ[ℚ, a, b] ⊗[ℚ] w.adicCompletion ℚ)ˣ} (hu : u ∈ Submodule.localBoxUnits Λ w) (hu' : u' ∈ Submodule.localBoxUnits Λ w) :
    u * u' ∈ Submodule.localBoxUnits Λ w := by
  refine ⟨?_, ?_⟩
  · rw [Units.val_mul]; exact localBox_mul_mem hΛ w hu.1 hu'.1
  · rw [mul_inv_rev, Units.val_mul]; exact localBox_mul_mem hΛ w hu'.2 hu.2

theorem inv_mem_localBoxUnits {Λ : Submodule ℤ ℍ[ℚ, a, b]} (w : HeightOneSpectrum (𝓞 ℚ))
    {u : (ℍ[ℚ, a, b] ⊗[ℚ] w.adicCompletion ℚ)ˣ} (hu : u ∈ Submodule.localBoxUnits Λ w) : u⁻¹ ∈ Submodule.localBoxUnits Λ w :=
  ⟨hu.2, by rw [inv_inv]; exact hu.1⟩

private theorem _root_.CSTowerT21.C4T.one_mem_localBoxUnits {Λ : Submodule ℤ ℍ[ℚ, a, b]} (hΛ : QuaternionAlgebra.IsOrder Λ) (w : HeightOneSpectrum (𝓞 ℚ)) :
    (1 : (ℍ[ℚ, a, b] ⊗[ℚ] w.adicCompletion ℚ)ˣ) ∈ Submodule.localBoxUnits Λ w :=
  ⟨by rw [Units.val_one]; exact one_mem_localBox hΛ w, by rw [inv_one, Units.val_one]; exact one_mem_localBox hΛ w⟩

p2m_export "CSTowerT21.C4T" "one_mem_localBoxUnits"

theorem mem_stabilizer_localBox_iff {Λ : Submodule ℤ ℍ[ℚ, a, b]} (hΛ : QuaternionAlgebra.IsOrder Λ) (w : HeightOneSpectrum (𝓞 ℚ))
    (g : (ℍ[ℚ, a, b] ⊗[ℚ] w.adicCompletion ℚ)ˣ) :
    g ∈ MulAction.stabilizer (ℍ[ℚ, a, b] ⊗[ℚ] w.adicCompletion ℚ)ˣ ((Submodule.localBox Λ w : AddSubgroup (ℍ[ℚ, a, b] ⊗[ℚ] w.adicCompletion ℚ)) : Set (ℍ[ℚ, a, b] ⊗[ℚ] w.adicCompletion ℚ)) ↔
      g ∈ Submodule.localBoxUnits Λ w := by
  constructor
  · intro hg
    have hg' : g⁻¹ ∈ MulAction.stabilizer (ℍ[ℚ, a, b] ⊗[ℚ] w.adicCompletion ℚ)ˣ ((Submodule.localBox Λ w : AddSubgroup (ℍ[ℚ, a, b] ⊗[ℚ] w.adicCompletion ℚ)) : Set (ℍ[ℚ, a, b] ⊗[ℚ] w.adicCompletion ℚ)) := inv_mem hg
    rw [MulAction.mem_stabilizer_iff] at hg hg'
    refine ⟨?_, ?_⟩
    · have h1 : (g : ℍ[ℚ, a, b] ⊗[ℚ] w.adicCompletion ℚ) * 1 ∈ g • ((Submodule.localBox Λ w : AddSubgroup (ℍ[ℚ, a, b] ⊗[ℚ] w.adicCompletion ℚ)) : Set (ℍ[ℚ, a, b] ⊗[ℚ] w.adicCompletion ℚ)) :=
        Set.smul_mem_smul_set (one_mem_localBox hΛ w)
      rw [hg, mul_one] at h1; exact h1
    · have h1 : ((g⁻¹ : (ℍ[ℚ, a, b] ⊗[ℚ] w.adicCompletion ℚ)ˣ) : ℍ[ℚ, a, b] ⊗[ℚ] w.adicCompletion ℚ) * 1 ∈ g⁻¹ • ((Submodule.localBox Λ w : AddSubgroup (ℍ[ℚ, a, b] ⊗[ℚ] w.adicCompletion ℚ)) : Set (ℍ[ℚ, a, b] ⊗[ℚ] w.adicCompletion ℚ)) :=
        Set.smul_mem_smul_set (one_mem_localBox hΛ w)
      rw [hg', mul_one] at h1; exact h1
  · rintro ⟨h1, h2⟩
    rw [MulAction.mem_stabilizer_iff]
    apply Set.Subset.antisymm
    · rintro _ ⟨x, hx, rfl⟩
      exact localBox_mul_mem hΛ w h1 hx
    · intro x hx
      refine ⟨(g⁻¹ : (ℍ[ℚ, a, b] ⊗[ℚ] w.adicCompletion ℚ)ˣ) • x, localBox_mul_mem hΛ w h2 hx, ?_⟩
      show (g : ℍ[ℚ, a, b] ⊗[ℚ] w.adicCompletion ℚ) * (((g⁻¹ : (ℍ[ℚ, a, b] ⊗[ℚ] w.adicCompletion ℚ)ˣ) : ℍ[ℚ, a, b] ⊗[ℚ] w.adicCompletion ℚ) * x) = x
      rw [← mul_assoc, Units.mul_inv, one_mul]

theorem finiteAdeleEvalAt_smul (w : HeightOneSpectrum (𝓞 ℚ)) (c : ℚ) (x : ℍ𝔸) :
    Submodule.finiteAdeleEvalAt ℍ[ℚ, a, b] w (c • x) =
      ((1 : ℍ[ℚ, a, b]) ⊗ₜ[ℚ] algebraMap ℚ (w.adicCompletion ℚ) c) * Submodule.finiteAdeleEvalAt ℍ[ℚ, a, b] w x := by
  rw [map_smul, ← Algebra.TensorProduct.algebraMap_apply', ← Algebra.smul_def]
  try rfl

theorem natCast_smul_mem_localBox {Λ : Submodule ℤ ℍ[ℚ, a, b]} (w : HeightOneSpectrum (𝓞 ℚ)) (q : ℕ)
    {y : ℍ[ℚ, a, b] ⊗[ℚ] w.adicCompletion ℚ} (hy : y ∈ Submodule.localBox Λ w) : (q : ℚ) • y ∈ Submodule.localBox Λ w := by
  rw [Nat.cast_smul_eq_nsmul ℚ]; exact AddSubgroup.nsmul_mem _ hy q

theorem inv_natCast_integral_of_ne {q : ℕ} (hq : q.Prime) {v w : HeightOneSpectrum (𝓞 ℚ)}
    (hqv : ((q : ℕ) : 𝓞 ℚ) ∈ v.asIdeal) (hw : w ≠ v) :
    algebraMap ℚ (w.adicCompletion ℚ) ((q : ℚ)⁻¹) ∈ w.adicCompletionIntegers ℚ := by
  apply Nat.inv_natCast_mem_adicCompletionIntegers_of_not_mem_placesOf hq.ne_zero
  intro hmem
  rw [Nat.mem_placesOf_iff hq.ne_zero] at hmem
  exact hw (Nat.HeightOneSpectrum.eq_of_natCast_prime_mem hq hmem hqv)

theorem exists_natCast_mem_asIdeal {q : ℕ} (hq : q.Prime) :
    ∃ v : HeightOneSpectrum (𝓞 ℚ), ((q : ℕ) : 𝓞 ℚ) ∈ v.asIdeal :=
  ⟨⟨Ideal.span {(q : 𝓞 ℚ)}, (Nat.isMaximal_span_natCast_of_prime hq).isPrime, Nat.span_natCast_ne_bot hq.ne_zero⟩,
    Ideal.mem_span_singleton_self _⟩

def OffUnit (Λ : Submodule ℤ ℍ[ℚ, a, b]) (v : HeightOneSpectrum (𝓞 ℚ)) (h : (ℍ𝔸)ˣ) : Prop :=
  ∀ w : HeightOneSpectrum (𝓞 ℚ), w ≠ v → Units.map (Submodule.finiteAdeleEvalAt ℍ[ℚ, a, b] w).toRingHom.toMonoidHom h ∈ Submodule.localBoxUnits Λ w

theorem offUnit_of_mem_primeHeckeSet {Λ : Submodule ℤ ℍ[ℚ, a, b]} {q : ℕ} (hq : q.Prime)
    {v : HeightOneSpectrum (𝓞 ℚ)} (hqv : ((q : ℕ) : 𝓞 ℚ) ∈ v.asIdeal)
    {h : (ℍ𝔸)ˣ} (hh : h ∈ QuaternionAlgebra.primeHeckeSet Λ q) : OffUnit Λ v h :=
  fun w hw => map_finiteAdeleEvalAt_mem_localBoxUnits_of_mem_primeHeckeSet q hh w (inv_natCast_integral_of_ne hq hqv hw)

theorem exists_offUnit_map_eq {Λ : Submodule ℤ ℍ[ℚ, a, b]} (hΛ : QuaternionAlgebra.IsOrder Λ)
    (v : HeightOneSpectrum (𝓞 ℚ)) (g : (ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ)ˣ) :
    ∃ β : (ℍ𝔸)ˣ, Units.map (Submodule.finiteAdeleEvalAt ℍ[ℚ, a, b] v).toRingHom.toMonoidHom β = g ∧ OffUnit Λ v β := by
  classical
  obtain ⟨β, h1, h2⟩ := Submodule.exists_units_finiteAdeleEvalAt_eq (D := ℍ[ℚ, a, b]) {v}
    (Function.update (fun w : HeightOneSpectrum (𝓞 ℚ) => (1 : (ℍ[ℚ, a, b] ⊗[ℚ] w.adicCompletion ℚ)ˣ)) v g)
  have h1v := h1 v (Finset.mem_singleton_self v)
  rw [Function.update_self] at h1v
  refine ⟨β, Units.ext h1v, fun w hw => ?_⟩
  have e : Units.map (Submodule.finiteAdeleEvalAt ℍ[ℚ, a, b] w).toRingHom.toMonoidHom β = 1 := Units.ext (h2 w (fun hmem => hw (Finset.mem_singleton.mp hmem)))
  rw [e]; exact one_mem_localBoxUnits hΛ w

theorem mem_box_iff_local {X : Submodule ℤ ℍ[ℚ, a, b]} (hX : QuaternionAlgebra.IsOrder X) (v : HeightOneSpectrum (𝓞 ℚ))
    {x : ℍ𝔸} (hx : ∀ w : HeightOneSpectrum (𝓞 ℚ), w ≠ v → Submodule.finiteAdeleEvalAt ℍ[ℚ, a, b] w x ∈ Submodule.localBox X w) :
    x ∈ Submodule.finiteAdeleBox X ↔ Submodule.finiteAdeleEvalAt ℍ[ℚ, a, b] v x ∈ Submodule.localBox X v := by
  rw [Submodule.mem_finiteAdeleBox_iff_forall_finiteAdeleEvalAt_mem_localBox X hX.fg hX.spanTop]
  refine ⟨fun h => h v, fun h w => ?_⟩
  by_cases hw : w = v
  · subst hw; exact h
  · exact hx w hw

def locT (R : Submodule ℤ ℍ[ℚ, a, b]) (q : ℕ) (v : HeightOneSpectrum (𝓞 ℚ)) : Set (ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ)ˣ :=
  {g |
        ((g : ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ) ∈ Submodule.localBox R v ∧
          (q : ℚ) • ((g⁻¹ : (ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ)ˣ) : ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ) ∈ Submodule.localBox R v ∧
          ((g⁻¹ : (ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ)ˣ) : ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ) ∉ Submodule.localBox R v ∧
          (q : ℚ)⁻¹ • (g : ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ) ∉ Submodule.localBox R v)}

theorem mem_primeHeckeSet_iff_local {R : Submodule ℤ ℍ[ℚ, a, b]} (hRo : QuaternionAlgebra.IsOrder R) {q : ℕ} (hq : q.Prime)
    {v : HeightOneSpectrum (𝓞 ℚ)} (hqv : ((q : ℕ) : 𝓞 ℚ) ∈ v.asIdeal) {h : (ℍ𝔸)ˣ} (hoff : OffUnit R v h) :
    h ∈ QuaternionAlgebra.primeHeckeSet R q ↔ Units.map (Submodule.finiteAdeleEvalAt ℍ[ℚ, a, b] v).toRingHom.toMonoidHom h ∈ locT R q v := by
  have off1 : ∀ w : HeightOneSpectrum (𝓞 ℚ), w ≠ v → Submodule.finiteAdeleEvalAt ℍ[ℚ, a, b] w (h : ℍ𝔸) ∈ Submodule.localBox R w :=
    fun w hw => (hoff w hw).1
  have off2 : ∀ w : HeightOneSpectrum (𝓞 ℚ), w ≠ v → Submodule.finiteAdeleEvalAt ℍ[ℚ, a, b] w ((h⁻¹ : (ℍ𝔸)ˣ) : ℍ𝔸) ∈ Submodule.localBox R w :=
    fun w hw => (hoff w hw).2
  have off3 : ∀ w : HeightOneSpectrum (𝓞 ℚ), w ≠ v →
      Submodule.finiteAdeleEvalAt ℍ[ℚ, a, b] w ((q : ℚ) • ((h⁻¹ : (ℍ𝔸)ˣ) : ℍ𝔸)) ∈ Submodule.localBox R w :=
    fun w hw => by rw [map_smul]; exact natCast_smul_mem_localBox w q (off2 w hw)
  have off4 : ∀ w : HeightOneSpectrum (𝓞 ℚ), w ≠ v → Submodule.finiteAdeleEvalAt ℍ[ℚ, a, b] w ((q : ℚ)⁻¹ • (h : ℍ𝔸)) ∈ Submodule.localBox R w :=
    fun w hw => by
      rw [finiteAdeleEvalAt_smul]
      exact tmul_one_mul_mem_localBox w (inv_natCast_integral_of_ne hq hqv hw) (off1 w hw)
  rw [QuaternionAlgebra.mem_primeHeckeSet_iff, mem_box_iff_local hRo v off1, mem_box_iff_local hRo v off3,
    mem_box_iff_local hRo v off2, mem_box_iff_local hRo v off4, map_smul, map_smul]
  exact Iff.rfl

theorem map_mem_stabilizer_of_mem_finiteIdeleStabilizer {R : Submodule ℤ ℍ[ℚ, a, b]} (hRo : QuaternionAlgebra.IsOrder R)
    (v : HeightOneSpectrum (𝓞 ℚ)) {u : (ℍ𝔸)ˣ} (hu : u ∈ Submodule.finiteIdeleStabilizer R) :
    Units.map (Submodule.finiteAdeleEvalAt ℍ[ℚ, a, b] v).toRingHom.toMonoidHom u ∈ MulAction.stabilizer (ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ)ˣ ((Submodule.localBox R v : AddSubgroup (ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ)) : Set (ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ)) := by
  rw [QuaternionAlgebra.IsOrder.mem_finiteIdeleStabilizer_iff_forall_map_finiteAdeleEvalAt_mem_localBoxUnits _ hRo] at hu
  exact (mem_stabilizer_localBox_iff hRo v _).mpr (hu v)

theorem inv_mul_mem_finiteIdeleStabilizer_of_local {R : Submodule ℤ ℍ[ℚ, a, b]} (hRo : QuaternionAlgebra.IsOrder R)
    {v : HeightOneSpectrum (𝓞 ℚ)} {h h' : (ℍ𝔸)ˣ} (hoff : OffUnit R v h) (hoff' : OffUnit R v h')
    (hK : (Units.map (Submodule.finiteAdeleEvalAt ℍ[ℚ, a, b] v).toRingHom.toMonoidHom h)⁻¹ * Units.map (Submodule.finiteAdeleEvalAt ℍ[ℚ, a, b] v).toRingHom.toMonoidHom h' ∈ MulAction.stabilizer (ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ)ˣ ((Submodule.localBox R v : AddSubgroup (ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ)) : Set (ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ))) :
    h⁻¹ * h' ∈ Submodule.finiteIdeleStabilizer R := by
  rw [QuaternionAlgebra.IsOrder.mem_finiteIdeleStabilizer_iff_forall_map_finiteAdeleEvalAt_mem_localBoxUnits _ hRo]
  intro w
  rw [map_mul, map_inv]
  by_cases hw : w = v
  · subst hw; exact (mem_stabilizer_localBox_iff hRo _ _).mp hK
  · exact mul_mem_localBoxUnits hRo w (inv_mem_localBoxUnits w (hoff w hw)) (hoff' w hw)

end CSTowerT21.C4T

namespace HeckeH1p
open QuaternionAlgebra CerednikDrinfeld
variable {a b : ℚ}
theorem mem_closure_localBoxUnits_iff {Λ : Submodule ℤ ℍ[ℚ, a, b]} (hΛ : IsOrder Λ) (w : HeightOneSpectrum (𝓞 ℚ))
    (t : (ℍ[ℚ, a, b] ⊗[ℚ] w.adicCompletion ℚ)ˣ) :
    t ∈ Subgroup.closure (Submodule.localBoxUnits Λ w) ↔ t ∈ Submodule.localBoxUnits Λ w := by
  let S : Subgroup (ℍ[ℚ, a, b] ⊗[ℚ] w.adicCompletion ℚ)ˣ :=
    { carrier := Submodule.localBoxUnits Λ w
      one_mem' := CSTowerT21.Stab.one_mem_localBoxUnits hΛ w
      mul_mem' := fun hx hy => CSTowerT21.C4T.mul_mem_localBoxUnits hΛ w hx hy
      inv_mem' := fun hx => CSTowerT21.C4T.inv_mem_localBoxUnits w hx }
  have : Subgroup.closure (Submodule.localBoxUnits Λ w) = S := Subgroup.closure_eq S
  rw [this]; rfl
end HeckeH1p

namespace L5Index

open CSTowerT21.Stab

variable {a b : ℚ}

local notation "ℍ𝔸" => ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ
local notation "ev" w => Submodule.finiteAdeleEvalAt ℍ[ℚ, a, b] w

theorem relIndex_eq_of_cover {G : Type*} [Group G] (H K L : Subgroup G) (hKL : K ≤ L)
    (hcov : ∀ l ∈ L, ∃ k ∈ K, k⁻¹ * l ∈ H) : H.relIndex K = H.relIndex L := by
  rw [Subgroup.relIndex, Subgroup.relIndex, Subgroup.index_eq_card, Subgroup.index_eq_card]
  refine Nat.card_congr (Equiv.ofBijective (Subgroup.quotientSubgroupOfEmbeddingOfLE H hKL)
    ⟨(Subgroup.quotientSubgroupOfEmbeddingOfLE H hKL).injective, fun y => ?_⟩)
  induction y using QuotientGroup.induction_on with
  | H l =>
    obtain ⟨k, hk, hkl⟩ := hcov (l : G) l.2
    refine ⟨QuotientGroup.mk ⟨k, hk⟩, ?_⟩
    rw [Subgroup.quotientSubgroupOfEmbeddingOfLE_apply_mk, QuotientGroup.eq, Subgroup.mem_subgroupOf]
    simpa using hkl

theorem relIndex_inf_comap_eq {G L : Type*} [Group G] [Group L] (f : G →* L) (Γ : Subgroup G)
    (B B' : Subgroup L) (hΓB : Γ.map f ≤ B)
    (hcov : ∀ y ∈ B, ∃ x ∈ Γ, (f x)⁻¹ * y ∈ B') :
    (Γ ⊓ B'.comap f).relIndex Γ = B'.relIndex B := by
  rw [Subgroup.inf_relIndex_left, Subgroup.relIndex_comap]
  refine relIndex_eq_of_cover B' (Γ.map f) B hΓB fun y hy => ?_
  obtain ⟨x, hx, hxy⟩ := hcov y hy
  exact ⟨f x, Subgroup.mem_map_of_mem f hx, hxy⟩

theorem nrd_mul' {K : Type*} [CommRing K] {a' b' : K} (x y : ℍ[K, a', b']) :
    QuaternionAlgebra.nrd (x * y) = QuaternionAlgebra.nrd x * QuaternionAlgebra.nrd y := by
  obtain ⟨x₀, x₁, x₂, x₃⟩ := x
  obtain ⟨y₀, y₁, y₂, y₃⟩ := y
  simp only [QuaternionAlgebra.mk_mul_mk, QuaternionAlgebra.nrd_mk]
  ring

theorem nrd_val_inv (B : (ℍ[ℚ, a, b])ˣ) :
    QuaternionAlgebra.nrd ((B⁻¹ : (ℍ[ℚ, a, b])ˣ) : ℍ[ℚ, a, b]) = (QuaternionAlgebra.nrd (B : ℍ[ℚ, a, b]))⁻¹ := by
  have h : QuaternionAlgebra.nrd (B : ℍ[ℚ, a, b]) * QuaternionAlgebra.nrd ((B⁻¹ : (ℍ[ℚ, a, b])ˣ) : ℍ[ℚ, a, b]) = 1 := by
    rw [← nrd_mul', Units.mul_inv, QuaternionAlgebra.nrd_one]
  exact (eq_inv_of_mul_eq_one_right h)

theorem unitsMap_finiteAdeleEvalAt_diagonal (w : HeightOneSpectrum (𝓞 ℚ)) (γ : (ℍ[ℚ, a, b])ˣ) :
    Units.map (Submodule.finiteAdeleEvalAt ℍ[ℚ, a, b] w).toRingHom.toMonoidHom (Submodule.finiteIdeleDiagonal ℍ[ℚ, a, b] γ) =
      CosetGraph.toLoc w γ := by
  apply Units.ext
  rw [Units.coe_map]
  show (Submodule.finiteAdeleEvalAt ℍ[ℚ, a, b] w) ((Submodule.finiteIdeleDiagonal ℍ[ℚ, a, b] γ : (ℍ𝔸)ˣ) : ℍ𝔸) =
    Algebra.TensorProduct.includeLeft (γ : ℍ[ℚ, a, b])
  rw [Submodule.val_finiteIdeleDiagonal_apply, Submodule.finiteAdeleEvalAt_tmul, Algebra.TensorProduct.includeLeft_apply]
  rfl

theorem ev_mul' (w : HeightOneSpectrum (𝓞 ℚ)) (x y : ℍ𝔸) : (ev w) (x * y) = (ev w) x * (ev w) y := map_mul _ x y

theorem mat_smul_mul {v : HeightOneSpectrum (𝓞 ℚ)} (c : v.adicCompletion ℚ)
    (M N : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)) : (c • M) * N = c • (M * N) := by
  ext i j
  simp only [Matrix.mul_apply, Matrix.smul_apply, smul_eq_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun k _ => by ring

theorem cayley_hamilton_two {v : HeightOneSpectrum (𝓞 ℚ)} (X : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)) :
    X * X = X.trace • X - X.det • (1 : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)) := by
  ext i j
  rw [Matrix.trace_fin_two, Matrix.det_fin_two]
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.one_apply] <;> ring

theorem mul_self_eq' {K : Type*} [CommRing K] {a' b' : K} (x : ℍ[K, a', b']) :
    x * x = (QuaternionAlgebra.trd x) • x - (QuaternionAlgebra.nrd x) • (1 : ℍ[K, a', b']) := by
  obtain ⟨x₀, x₁, x₂, x₃⟩ := x
  ext <;> simp [QuaternionAlgebra.mk_mul_mk, QuaternionAlgebra.nrd, QuaternionAlgebra.trd] <;> ring

section LocalDetNrd

variable {v : HeightOneSpectrum (𝓞 ℚ)}
  (φ : ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ ≃+* Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ))
  (hφ : ∀ t : v.adicCompletion ℚ, φ ((1 : ℍ[ℚ, a, b]) ⊗ₜ[ℚ] t) = t • (1 : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)))
  (ψ : ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ ≃+*
      ℍ[v.adicCompletion ℚ, algebraMap ℚ (v.adicCompletion ℚ) a, algebraMap ℚ (v.adicCompletion ℚ) b])
  (hψ : ∀ (z : ℍ[ℚ, a, b]) (t : v.adicCompletion ℚ),
      ψ (z ⊗ₜ[ℚ] t) = t • (⟨algebraMap ℚ (v.adicCompletion ℚ) z.re,
        algebraMap ℚ (v.adicCompletion ℚ) z.imI, algebraMap ℚ (v.adicCompletion ℚ) z.imJ,
        algebraMap ℚ (v.adicCompletion ℚ) z.imK⟩ :
          ℍ[v.adicCompletion ℚ, algebraMap ℚ (v.adicCompletion ℚ) a, algebraMap ℚ (v.adicCompletion ℚ) b]))

include hψ in
theorem psi_one_tmul (t : v.adicCompletion ℚ) :
    ψ ((1 : ℍ[ℚ, a, b]) ⊗ₜ[ℚ] t) =
      ((t : v.adicCompletion ℚ) : ℍ[v.adicCompletion ℚ, algebraMap ℚ (v.adicCompletion ℚ) a, algebraMap ℚ (v.adicCompletion ℚ) b]) := by
  rw [hψ]
  ext <;> simp

include hψ in
theorem symm_smul (t : v.adicCompletion ℚ)
    (ξ : ℍ[v.adicCompletion ℚ, algebraMap ℚ (v.adicCompletion ℚ) a, algebraMap ℚ (v.adicCompletion ℚ) b]) :
    ψ.symm (t • ξ) = ((1 : ℍ[ℚ, a, b]) ⊗ₜ[ℚ] t) * ψ.symm ξ := by
  apply ψ.injective
  rw [ψ.apply_symm_apply, ψ.map_mul, psi_one_tmul ψ hψ, ψ.apply_symm_apply, QuaternionAlgebra.coe_mul_eq_smul]

include hφ hψ in

theorem det_eq_nrd (x : ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ) :
    (φ x).det = QuaternionAlgebra.nrd (ψ x) := by
  set ξ := ψ x with hξ
  have hx : x = ψ.symm ξ := by rw [hξ, ψ.symm_apply_apply]
  have hrel : φ x * φ x = QuaternionAlgebra.trd ξ • φ x - QuaternionAlgebra.nrd ξ • (1 : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)) := by
    have h0 : x * x = ((1 : ℍ[ℚ, a, b]) ⊗ₜ[ℚ] QuaternionAlgebra.trd ξ) * x - ((1 : ℍ[ℚ, a, b]) ⊗ₜ[ℚ] QuaternionAlgebra.nrd ξ) := by
      have := congrArg ψ.symm (mul_self_eq' ξ)
      rw [ψ.symm.map_mul, ψ.symm.map_sub, symm_smul ψ hψ, symm_smul ψ hψ, ψ.symm.map_one, mul_one, ← hx] at this
      exact this
    rw [← φ.map_mul, h0, φ.map_sub, φ.map_mul, hφ, hφ, mat_smul_mul, one_mul]
  have hCH := cayley_hamilton_two (φ x)
  have hdiff : (QuaternionAlgebra.trd ξ - (φ x).trace) • φ x =
      (QuaternionAlgebra.nrd ξ - (φ x).det) • (1 : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)) := by
    rw [sub_smul, sub_smul, sub_eq_sub_iff_sub_eq_sub, ← hrel, ← hCH]
  by_cases hs : QuaternionAlgebra.trd ξ - (φ x).trace = 0
  · rw [hs, zero_smul] at hdiff
    have h00 := congrFun (congrFun hdiff 0) 0
    simp only [Matrix.zero_apply, Matrix.smul_apply, Matrix.one_apply_eq, smul_eq_mul, mul_one] at h00
    exact (sub_eq_zero.mp h00.symm).symm
  · have hXs : φ x = ((QuaternionAlgebra.trd ξ - (φ x).trace)⁻¹ * (QuaternionAlgebra.nrd ξ - (φ x).det)) •
        (1 : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)) := by
      have := congrArg (fun M : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ) => (QuaternionAlgebra.trd ξ - (φ x).trace)⁻¹ • M) hdiff
      simp only [smul_smul, inv_mul_cancel₀ hs, one_smul] at this
      exact this
    obtain ⟨c, hc⟩ : ∃ c : v.adicCompletion ℚ, φ x = c • (1 : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)) := ⟨_, hXs⟩
    have hx1 : x = (1 : ℍ[ℚ, a, b]) ⊗ₜ[ℚ] c := by
      apply φ.injective; rw [hc, hφ]
    have hξc : ξ = ((c : v.adicCompletion ℚ) : ℍ[v.adicCompletion ℚ, algebraMap ℚ (v.adicCompletion ℚ) a,
        algebraMap ℚ (v.adicCompletion ℚ) b]) := by rw [hξ, hx1, psi_one_tmul ψ hψ]
    rw [hc, Matrix.det_smul, Matrix.det_one, mul_one, Fintype.card_fin, hξc, QuaternionAlgebra.nrd_coe]

end LocalDetNrd

theorem det_mem {w : HeightOneSpectrum (𝓞 ℚ)} (M : Matrix (Fin 2) (Fin 2) (w.adicCompletion ℚ))
    (hM : ∀ i j, M i j ∈ w.adicCompletionIntegers ℚ) :
    M.det ∈ w.adicCompletionIntegers ℚ := by
  rw [Matrix.det_fin_two]
  exact sub_mem (mul_mem (hM 0 0) (hM 1 1)) (mul_mem (hM 0 1) (hM 1 0))

theorem localBoxUnits_meetOrder_eq_of_mem {R : Submodule ℤ ℍ[ℚ, a, b]} (hR : IsOrder R) (n : (ℍ𝔸)ˣ)
    (w : HeightOneSpectrum (𝓞 ℚ)) (hn : evU (a := a) (b := b) w n ∈ Submodule.localBoxUnits R w) :
    Submodule.localBoxUnits (meetOrder R n) w = Submodule.localBoxUnits R w := by
  ext t
  rw [mem_localBoxUnits_meetOrder_iff hR n w, conj_mem_localBoxUnits_iff hR w hn]
  exact ⟨fun h => h.1, fun h => ⟨h, h⟩⟩

theorem localBoxUnits_meetOrder_meetOrder_eq {R : Submodule ℤ ℍ[ℚ, a, b]} (hR : IsOrder R) (n g : (ℍ𝔸)ˣ)
    (w : HeightOneSpectrum (𝓞 ℚ)) (hn : evU (a := a) (b := b) w n ∈ Submodule.localBoxUnits R w) :
    Submodule.localBoxUnits (meetOrder (meetOrder R n) g) w = Submodule.localBoxUnits (meetOrder R g) w := by
  have hRn : IsOrder (meetOrder R n) := isOrder_meetOrder hR n
  ext t
  rw [mem_localBoxUnits_meetOrder_iff hRn g w, mem_localBoxUnits_meetOrder_iff hR g w,
    localBoxUnits_meetOrder_eq_of_mem hR n w hn]

theorem U_side {O : Submodule ℤ ℍ[ℚ, a, b]} (hO : IsOrder O) (v vl : HeightOneSpectrum (𝓞 ℚ)) (hvl : vl ≠ v)
    (sf : (ℍ𝔸)ˣ) (hsfv : evU (a := a) (b := b) v sf = 1)
    (hsfw : ∀ w : HeightOneSpectrum (𝓞 ℚ), w ≠ v → w ≠ vl → evU (a := a) (b := b) w sf ∈ Submodule.localBoxUnits O w) :
    (Submodule.finiteIdeleStabilizer (meetOrder O sf)).relIndex (Submodule.finiteIdeleStabilizer O) =
      (Subgroup.closure (Submodule.localBoxUnits (meetOrder O sf) vl)).relIndex
        (Subgroup.closure (Submodule.localBoxUnits O vl)) := by
  have hO' : IsOrder (meetOrder O sf) := isOrder_meetOrder hO sf
  have key : Submodule.finiteIdeleStabilizer (meetOrder O sf) =
      Submodule.finiteIdeleStabilizer O ⊓
        (Subgroup.closure (Submodule.localBoxUnits (meetOrder O sf) vl)).comap (evU (a := a) (b := b) vl) := by
    ext u
    rw [Subgroup.mem_inf, Subgroup.mem_comap, mem_stabilizer_iff_forall hO', mem_stabilizer_iff_forall hO,
      HeckeH1p.mem_closure_localBoxUnits_iff hO']
    constructor
    · intro h
      exact ⟨fun w => ((mem_localBoxUnits_meetOrder_iff hO sf w _).1 (h w)).1, h vl⟩
    · rintro ⟨h, hl⟩ w
      by_cases hwl : w = vl
      · rw [hwl]; exact hl
      rw [mem_localBoxUnits_meetOrder_iff hO sf w]
      refine ⟨h w, ?_⟩
      by_cases hwv : w = v
      · rw [hwv, hsfv, inv_one, one_mul, mul_one]; exact h v
      · exact (conj_mem_localBoxUnits_iff hO w (hsfw w hwv hwl) _).2 (h w)
  rw [key]
  apply relIndex_inf_comap_eq
  · rintro _ ⟨u, hu, rfl⟩
    exact Subgroup.subset_closure (map_mem_localBoxUnits_of_mem_stabilizer hO hu vl)
  · intro y hy
    have hy' := (HeckeH1p.mem_closure_localBoxUnits_iff hO vl y).1 hy
    obtain ⟨β, hβ, hoff⟩ := CSTowerT21.C4T.exists_offUnit_map_eq hO vl y
    refine ⟨β, (mem_stabilizer_iff_forall hO β).2 (fun w => ?_), ?_⟩
    · by_cases hw : w = vl
      · rw [hw]; rw [show evU (a := a) (b := b) vl β = y from hβ]; exact hy'
      · exact hoff w hw
    · rw [show evU (a := a) (b := b) vl β = y from hβ, inv_mul_cancel]; exact one_mem _

theorem Gamma_side
    {q' : ℕ} [Fact q'.Prime] (hdef : IsDefiniteRamifiedExactlyAt a b q') (hq'2 : q' ≠ 2)
    {R : Submodule ℤ ℍ[ℚ, a, b]} (hRo : IsOrder R)
    {Λ : Submodule ℤ ℍ[ℚ, a, b]} (hΛ : IsMaximalOrder Λ) (hRΛ : R ≤ Λ)
    (q : ℕ) [Fact q.Prime] (hqq' : q ≠ q') (v : HeightOneSpectrum (𝓞 ℚ)) (hv : ((q : ℕ) : 𝓞 ℚ) ∈ v.asIdeal)
    (ℓ : ℕ) [Fact ℓ.Prime] (hℓq : ℓ ≠ q) (hℓq' : ℓ ≠ q')
    (vl : HeightOneSpectrum (𝓞 ℚ)) (hvl : ((ℓ : ℕ) : 𝓞 ℚ) ∈ vl.asIdeal)
    (s : (ℍ[ℚ, a, b])ˣ) (hsnrd : QuaternionAlgebra.nrd (s : ℍ[ℚ, a, b]) = (ℓ : ℚ)) (sf : (ℍ𝔸)ˣ)
    (hsf : ∀ u : HeightOneSpectrum (𝓞 ℚ), ((q : ℕ) : 𝓞 ℚ) ∉ u.asIdeal →
      (ev u) (sf : ℍ𝔸) = (s : ℍ[ℚ, a, b]) ⊗ₜ[ℚ] (1 : u.adicCompletion ℚ))
    (hsfw : ∀ w : HeightOneSpectrum (𝓞 ℚ), w ≠ v → w ≠ vl → evU (a := a) (b := b) w sf ∈ Submodule.localBoxUnits R w)
    {M : ℕ} (hO' : IsEichlerOrder (meetOrder R sf) M)
    (Γ : Subgroup (ℍ[ℚ, a, b])ˣ)
    (hΓ0 : ∀ x : (ℍ[ℚ, a, b])ˣ, x ∈ Γ ↔
      x ∈ CosetGraph.awayUnits R v ∧ Even (padicValRat q (QuaternionAlgebra.nrd (x : ℍ[ℚ, a, b])))) :
    (Γ ⊓ Γ.map (MulAut.conj s).toMonoidHom).relIndex Γ =
      (Subgroup.closure (Submodule.localBoxUnits (meetOrder R sf) vl)).relIndex
        (Subgroup.closure (Submodule.localBoxUnits R vl)) := by
  classical
  have hqp : q.Prime := Fact.out
  have hq'p : q'.Prime := Fact.out
  have hℓp : ℓ.Prime := Fact.out
  have hℓ0 : (ℓ : ℚ) ≠ 0 := by exact_mod_cast hℓp.ne_zero
  have hRs : IsOrder (meetOrder R sf) := isOrder_meetOrder hRo sf
  have hvlv : vl ≠ v := fun h => not_mem_of_prime_ne hqp hℓp hℓq hv (h ▸ hvl)
  have hne : ∀ u : HeightOneSpectrum (𝓞 ℚ), u ≠ v → ((q : ℕ) : 𝓞 ℚ) ∉ u.asIdeal :=
    fun u hu h => hu (eq_of_natCast_prime_mem hqp h hv)
  have hA : CosetGraph.awayUnits (meetOrder R sf) v =
      CosetGraph.awayUnits R v ⊓ (CosetGraph.awayUnits R v).map (MulAut.conj s).toMonoidHom :=
    CerednikDrinfeld.CosetGraph.awayUnits_meetOrder_eq_inf_map_conj_of_finiteAdeleEvalAt_eq R hRo q v hv s sf hsf
  have nrd_conj : ∀ x : (ℍ[ℚ, a, b])ˣ,
      QuaternionAlgebra.nrd ((s⁻¹ * x * s : (ℍ[ℚ, a, b])ˣ) : ℍ[ℚ, a, b]) = QuaternionAlgebra.nrd (x : ℍ[ℚ, a, b]) := by
    intro x
    rw [Units.val_mul, Units.val_mul, nrd_mul', nrd_mul', nrd_val_inv, hsnrd, mul_comm ((ℓ : ℚ)⁻¹), mul_assoc,
      inv_mul_cancel₀ hℓ0, mul_one]

  have hsub : ∀ (w : HeightOneSpectrum (𝓞 ℚ)) (t : (ℍ[ℚ, a, b] ⊗[ℚ] w.adicCompletion ℚ)ˣ),
      t ∈ Submodule.localBoxUnits (meetOrder R sf) w → t ∈ Submodule.localBoxUnits R w :=
    fun w t ht => ((mem_localBoxUnits_meetOrder_iff hRo sf w t).1 ht).1
  have hup : ∀ (w : HeightOneSpectrum (𝓞 ℚ)), w ≠ v → w ≠ vl → ∀ (t : (ℍ[ℚ, a, b] ⊗[ℚ] w.adicCompletion ℚ)ˣ),
      t ∈ Submodule.localBoxUnits R w → t ∈ Submodule.localBoxUnits (meetOrder R sf) w :=
    fun w hw hwl t ht => (mem_localBoxUnits_meetOrder_iff hRo sf w t).2
      ⟨ht, (conj_mem_localBoxUnits_iff hRo w (hsfw w hw hwl) _).2 ht⟩

  have key : Γ ⊓ Γ.map (MulAut.conj s).toMonoidHom =
      Γ ⊓ (Subgroup.closure (Submodule.localBoxUnits (meetOrder R sf) vl)).comap (CosetGraph.toLoc vl) := by
    ext x
    simp only [Subgroup.mem_inf, Subgroup.mem_comap, Subgroup.mem_map_equiv, MulAut.conj_symm_apply]
    constructor
    · rintro ⟨hx, hx'⟩
      refine ⟨hx, ?_⟩
      have h1 : x ∈ CosetGraph.awayUnits (meetOrder R sf) v := by
        rw [hA, Subgroup.mem_inf, Subgroup.mem_map_equiv, MulAut.conj_symm_apply]
        exact ⟨((hΓ0 x).1 hx).1, ((hΓ0 _).1 hx').1⟩
      simp only [CosetGraph.awayUnits, Subgroup.mem_iInf, Subgroup.mem_comap] at h1
      exact h1 vl hvlv
    · rintro ⟨hx, hl⟩
      refine ⟨hx, ?_⟩
      rw [hΓ0, nrd_conj]
      refine ⟨?_, ((hΓ0 x).1 hx).2⟩
      have hxA : x ∈ CosetGraph.awayUnits R v := ((hΓ0 x).1 hx).1
      have h1 : x ∈ CosetGraph.awayUnits (meetOrder R sf) v := by
        simp only [CosetGraph.awayUnits, Subgroup.mem_iInf, Subgroup.mem_comap] at hxA ⊢
        intro w hw
        by_cases hwl : w = vl
        · rw [hwl]; exact hl
        · refine (HeckeH1p.mem_closure_localBoxUnits_iff hRs w _).2 ?_
          exact hup w hw hwl _ ((HeckeH1p.mem_closure_localBoxUnits_iff hRo w _).1 (hxA w hw))
      rw [hA, Subgroup.mem_inf, Subgroup.mem_map_equiv, MulAut.conj_symm_apply] at h1
      exact h1.2
  rw [key]
  apply relIndex_inf_comap_eq
  · rintro _ ⟨x, hx, rfl⟩
    have hxA : x ∈ CosetGraph.awayUnits R v := ((hΓ0 x).1 hx).1
    simp only [CosetGraph.awayUnits, Subgroup.mem_iInf, Subgroup.mem_comap] at hxA
    exact hxA vl hvlv
  ·
    intro y hy
    have hy' : y ∈ Submodule.localBoxUnits R vl := (HeckeH1p.mem_closure_localBoxUnits_iff hRo vl y).1 hy

    have hΛE : IsEichlerOrder Λ 1 :=
      ⟨Λ, Λ, hΛ, hΛ, le_antisymm (le_inf le_rfl le_rfl) inf_le_left, AddSubgroup.relIndex_self _⟩
    have hq'vl : (q' : 𝓞 ℚ) ∉ vl.asIdeal := not_mem_of_prime_ne hℓp hq'p (Ne.symm hℓq') hvl
    have h1vl : ((1 : ℕ) : 𝓞 ℚ) ∉ vl.asIdeal := by
      rw [Nat.cast_one]; exact (Ideal.ne_top_iff_one _).1 vl.isPrime.ne_top
    obtain ⟨φ, hφ, hφΛ⟩ :=
      QuaternionAlgebra.IsEichlerOrder.exists_ringEquiv_mem_localBox_iff_of_notMem hdef hΛE vl hq'vl h1vl
    have hyΛ : ((y : (ℍ[ℚ, a, b] ⊗[ℚ] vl.adicCompletion ℚ)ˣ) : ℍ[ℚ, a, b] ⊗[ℚ] vl.adicCompletion ℚ) ∈
        Submodule.localBox Λ vl := CSTowerT21.HL.localBox_mono hRΛ vl hy'.1
    have hyiΛ : ((y⁻¹ : (ℍ[ℚ, a, b] ⊗[ℚ] vl.adicCompletion ℚ)ˣ) : ℍ[ℚ, a, b] ⊗[ℚ] vl.adicCompletion ℚ) ∈
        Submodule.localBox Λ vl := CSTowerT21.HL.localBox_mono hRΛ vl hy'.2
    obtain ⟨d, hd⟩ : ∃ d : vl.adicCompletion ℚ,
        (φ ((y : (ℍ[ℚ, a, b] ⊗[ℚ] vl.adicCompletion ℚ)ˣ) : ℍ[ℚ, a, b] ⊗[ℚ] vl.adicCompletion ℚ)).det = d := ⟨_, rfl⟩
    have hdi : d * (φ ((y⁻¹ : (ℍ[ℚ, a, b] ⊗[ℚ] vl.adicCompletion ℚ)ˣ) : ℍ[ℚ, a, b] ⊗[ℚ] vl.adicCompletion ℚ)).det = 1 := by
      rw [← hd, ← Matrix.det_mul, ← φ.map_mul, Units.mul_inv, φ.map_one, Matrix.det_one]
    have hd1 : Valued.v d = 1 := by
      have h1 : Valued.v d ≤ 1 := by
        rw [← hd]; exact (HeightOneSpectrum.mem_adicCompletionIntegers (𝓞 ℚ) ℚ vl).1 (det_mem _ ((hφΛ _).1 hyΛ))
      have h2 : Valued.v ((φ ((y⁻¹ : (ℍ[ℚ, a, b] ⊗[ℚ] vl.adicCompletion ℚ)ˣ) :
          ℍ[ℚ, a, b] ⊗[ℚ] vl.adicCompletion ℚ)).det) ≤ 1 :=
        (HeightOneSpectrum.mem_adicCompletionIntegers (𝓞 ℚ) ℚ vl).1 (det_mem _ ((hφΛ _).1 hyiΛ))
      have h3 := congrArg Valued.v hdi
      rw [map_mul, map_one] at h3
      refine le_antisymm h1 ?_
      calc (1 : WithZero (Multiplicative ℤ)) = Valued.v d * _ := h3.symm
        _ ≤ Valued.v d * 1 := mul_le_mul_right h2 _
        _ = Valued.v d := mul_one _
    have hd0 : d ≠ 0 := fun h => by rw [h, map_zero] at hd1; exact zero_ne_one hd1

    let ε : (w : HeightOneSpectrum (𝓞 ℚ)) → w.adicCompletion ℚ :=
      Function.update (fun w : HeightOneSpectrum (𝓞 ℚ) => (1 : w.adicCompletion ℚ)) vl d⁻¹
    have hεl : ε vl = d⁻¹ := by simp only [ε, Function.update_self]
    have hεw : ∀ w : HeightOneSpectrum (𝓞 ℚ), w ≠ vl → ε w = 1 := fun w hw => by
      simp only [ε, Function.update_of_ne hw]
    have hε : ∀ w : HeightOneSpectrum (𝓞 ℚ), Valued.v (ε w) = 1 := by
      intro w
      by_cases hw : w = vl
      · subst hw; rw [hεl, map_inv₀, hd1, inv_one]
      · rw [hεw w hw, map_one]
    obtain ⟨m, hmU, hm⟩ :=
      QuaternionAlgebra.IsEichlerOrder.exists_mem_finiteIdeleStabilizer_forall_nrd_eq hq'2 hdef hO' ε hε

    obtain ⟨y0, hy0v, hy0w⟩ := Submodule.exists_units_finiteAdeleEvalAt_eq (D := ℍ[ℚ, a, b]) {vl}
      (Function.update (fun w : HeightOneSpectrum (𝓞 ℚ) => (1 : (ℍ[ℚ, a, b] ⊗[ℚ] w.adicCompletion ℚ)ˣ)) vl y)
    have hy0l : evU (a := a) (b := b) vl y0 = y := by
      have h := hy0v vl (Finset.mem_singleton_self vl)
      rw [Function.update_self] at h
      exact Units.ext h
    have hy0o : ∀ w : HeightOneSpectrum (𝓞 ℚ), w ≠ vl → evU (a := a) (b := b) w y0 = 1 := fun w hw =>
      Units.ext (hy0w w (fun h => hw (Finset.mem_singleton.mp h)))

    have hsplit : ∃ z : ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ, z ≠ 0 ∧ ¬ IsUnit z := by
      by_contra hcon
      push_neg at hcon
      exact not_mem_of_prime_ne hqp hq'p (Ne.symm hqq') hv ((hdef.2.2 v).mp hcon)
    obtain ⟨β, g, u, hβ1, huU, hg, hyeq⟩ :=
      QuaternionAlgebra.IsOrder.exists_nrd_eq_one_and_eq_finiteIdeleDiagonal_mul_mul_of_forall_nrd_eq_one
        hdef.1 hdef.2.1 hRs v hsplit (y0 * m) (by
          intro w hw ψ hψ
          rw [Units.val_mul, ev_mul', ψ.map_mul, nrd_mul', hm w ψ hψ]
          by_cases hwl : w = vl
          · subst hwl
            rw [show (ev w) (y0 : ℍ𝔸) = ((y : (ℍ[ℚ, a, b] ⊗[ℚ] w.adicCompletion ℚ)ˣ) : ℍ[ℚ, a, b] ⊗[ℚ] w.adicCompletion ℚ)
                from congrArg Units.val hy0l,
              ← det_eq_nrd φ hφ ψ hψ, hd, hεl, mul_inv_cancel₀ hd0]
          · rw [show (ev w) (y0 : ℍ𝔸) = 1 from congrArg Units.val (hy0o w hwl), ψ.map_one,
              QuaternionAlgebra.nrd_one, hεw w hwl, mul_one])

    have hg' : ∀ w : HeightOneSpectrum (𝓞 ℚ), w ≠ v → evU (a := a) (b := b) w g = 1 := fun w hw => Units.ext (hg w hw)
    have hdiag : Submodule.finiteIdeleDiagonal ℍ[ℚ, a, b] β = y0 * m * u⁻¹ * g⁻¹ := by
      rw [hyeq]; group
    have hβw : ∀ w : HeightOneSpectrum (𝓞 ℚ), CosetGraph.toLoc w β =
        evU (a := a) (b := b) w y0 * evU (a := a) (b := b) w m * (evU (a := a) (b := b) w u)⁻¹ *
          (evU (a := a) (b := b) w g)⁻¹ := by
      intro w
      rw [← unitsMap_finiteAdeleEvalAt_diagonal, hdiag, map_mul, map_mul, map_mul, map_inv, map_inv]
    refine ⟨β, ?_, ?_⟩
    · rw [hΓ0]
      refine ⟨?_, by rw [hβ1, padicValRat.one]; exact Even.zero⟩
      simp only [CosetGraph.awayUnits, Subgroup.mem_iInf, Subgroup.mem_comap]
      intro w hw
      rw [hβw w, hg' w hw, inv_one, mul_one]
      refine Subgroup.mul_mem _ (Subgroup.mul_mem _ ?_ ?_) (Subgroup.inv_mem _ ?_)
      · by_cases hwl : w = vl
        · subst hwl; rw [hy0l]; exact hy
        · rw [hy0o w hwl]; exact Subgroup.subset_closure (one_mem_localBoxUnits hRo w)
      · exact Subgroup.subset_closure (hsub w _ (map_mem_localBoxUnits_of_mem_stabilizer hRs hmU w))
      · exact Subgroup.subset_closure (hsub w _ (map_mem_localBoxUnits_of_mem_stabilizer hRs huU w))
    · rw [hβw vl, hy0l, hg' vl hvlv]
      have e : (y * evU (a := a) (b := b) vl m * (evU (a := a) (b := b) vl u)⁻¹ * (1 : (ℍ[ℚ, a, b] ⊗[ℚ] vl.adicCompletion ℚ)ˣ)⁻¹)⁻¹ * y =
          evU (a := a) (b := b) vl u * (evU (a := a) (b := b) vl m)⁻¹ := by group
      rw [e]
      exact Subgroup.mul_mem _ (Subgroup.subset_closure (map_mem_localBoxUnits_of_mem_stabilizer hRs huU vl))
        (Subgroup.inv_mem _ (Subgroup.subset_closure (map_mem_localBoxUnits_of_mem_stabilizer hRs hmU vl)))

end L5Index

open scoped TensorProduct Quaternion NumberField
open IsDedekindDomain QuaternionAlgebra CerednikDrinfeld
open scoped Classical

theorem solution

    {a₁ b₁ : ℚ} {N q q' : ℕ} [NeZero N] (hN : Squarefree N) [Fact q.Prime] [Fact q'.Prime]
    (hqN : ¬ q ∣ N) (hq'N : ¬ q' ∣ N) (hqq' : q' ≠ q) (hq5 : 5 ≤ q) (hq'5 : 5 ≤ q')
    (hdef₁ : IsDefiniteRamifiedExactlyAt a₁ b₁ q')
    (Λ₁ R₁ : Submodule ℤ ℍ[ℚ, a₁, b₁]) (hΛ₁ : IsMaximalOrder Λ₁) (hR₁ : IsEichlerOrder R₁ N) (hRΛ₁ : R₁ ≤ Λ₁)
    (n₁ : (ℍ[ℚ, a₁, b₁] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) (hn₁ : n₁ ∈ primeHeckeSet R₁ q)
    (hS₁ : IsEichlerOrder (meetOrder R₁ n₁) (N * q))
    (v₂ : HeightOneSpectrum (𝓞 ℚ)) (hv₂ : ((q : ℕ) : 𝓞 ℚ) ∈ v₂.asIdeal)

    (ℓ : HeckeTower.AwayPrime q q')
    (s : (ℍ[ℚ, a₁, b₁])ˣ) (sf : (ℍ[ℚ, a₁, b₁] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ)
    (hs :
      (∀ u : HeightOneSpectrum (𝓞 ℚ), ((q : ℕ) : 𝓞 ℚ) ∉ u.asIdeal →
        Submodule.finiteAdeleEvalAt ℍ[ℚ, a₁, b₁] u (sf : ℍ[ℚ, a₁, b₁] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ) =
          (s : ℍ[ℚ, a₁, b₁]) ⊗ₜ[ℚ] (1 : u.adicCompletion ℚ)) ∧
      (∀ u : HeightOneSpectrum (𝓞 ℚ), ((q : ℕ) : 𝓞 ℚ) ∈ u.asIdeal →
        Submodule.finiteAdeleEvalAt ℍ[ℚ, a₁, b₁] u (sf : ℍ[ℚ, a₁, b₁] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ) = 1) ∧
      Submodule.finiteIdeleDiagonal ℍ[ℚ, a₁, b₁]
          (Units.map (algebraMap ℚ ℍ[ℚ, a₁, b₁]).toMonoidHom
            (Units.mk0 ((ℓ.1 : ℕ) : ℚ) (Nat.cast_ne_zero.mpr ℓ.1.prop.ne_zero))) * sf⁻¹ ∈
        (if (ℓ.1 : ℕ) ∣ N then levelHeckeUSet Λ₁ (meetOrder R₁ n₁) (ℓ.1 : ℕ)
          else primeHeckeSet (meetOrder R₁ n₁) (ℓ.1 : ℕ)) ∧
      nrd (s : ℍ[ℚ, a₁, b₁]) = ((ℓ.1 : ℕ) : ℚ))

    (Γ : Subgroup (ℍ[ℚ, a₁, b₁])ˣ)
    (hΓ0 : ∀ x : (ℍ[ℚ, a₁, b₁])ˣ, x ∈ Γ ↔
      x ∈ CerednikDrinfeld.CosetGraph.awayUnits R₁ v₂ ∧ Even (padicValRat q (nrd (x : ℍ[ℚ, a₁, b₁])))) :
    (Γ ⊓ Γ.map (MulAut.conj s).toMonoidHom).relIndex Γ = HeckeTower.arrowDegree N ((ℓ, 0) : HeckeTower.Arr q q') := by
  classical
  obtain ⟨hsf1, hsf2, hs3, hsnrd⟩ := hs
  haveI hℓF : Fact ((ℓ.1 : ℕ).Prime) := ⟨ℓ.1.prop⟩
  have hℓp : (ℓ.1 : ℕ).Prime := ℓ.1.prop
  have hℓq : (ℓ.1 : ℕ) ≠ q := ℓ.2.1
  have hℓq' : (ℓ.1 : ℕ) ≠ q' := ℓ.2.2
  have hqp : q.Prime := Fact.out
  have hq'p : q'.Prime := Fact.out
  have hq'2 : q' ≠ 2 := by omega
  have hRo : IsOrder R₁ := hR₁.isOrder
  have hSo : IsOrder (meetOrder R₁ n₁) := hS₁.isOrder
  obtain ⟨vl, hvl⟩ := CSTowerT21.Stab.exists_place (ℓ.1 : ℕ) hℓp
  have hvlv : vl ≠ v₂ := fun h => CSTowerT21.Stab.not_mem_of_prime_ne hqp hℓp hℓq hv₂ (h ▸ hvl)
  have hsfv : CSTowerT21.Stab.evU (a := a₁) (b := b₁) v₂ sf = 1 := Units.ext (hsf2 v₂ hv₂)

  have hsfT : sf ∈ primeHeckeSet (meetOrder R₁ n₁) (ℓ.1 : ℕ) := by
    apply (QuaternionAlgebra.mem_primeHeckeSet_iff_finiteIdeleDiagonal_mul_inv_mem (meetOrder R₁ n₁) (ℓ.1 : ℕ) sf).2
    by_cases hdiv : (ℓ.1 : ℕ) ∣ N
    · rw [if_pos hdiv] at hs3; exact hs3.1
    · rw [if_neg hdiv] at hs3; exact hs3
  have hsfwS : ∀ w : HeightOneSpectrum (𝓞 ℚ), w ≠ v₂ → w ≠ vl →
      CSTowerT21.Stab.evU (a := a₁) (b := b₁) w sf ∈ Submodule.localBoxUnits (meetOrder R₁ n₁) w :=
    fun w _ hwl => CSTowerT21.Stab.map_mem_localBoxUnits_of_mem_primeHeckeSet hℓp.ne_zero hsfT
      (fun h => hwl (CSTowerT21.Stab.eq_of_natCast_prime_mem hℓp h hvl))
  have hsfwR : ∀ w : HeightOneSpectrum (𝓞 ℚ), w ≠ v₂ → w ≠ vl →
      CSTowerT21.Stab.evU (a := a₁) (b := b₁) w sf ∈ Submodule.localBoxUnits R₁ w :=
    fun w hw hwl => ((CSTowerT21.Stab.mem_localBoxUnits_meetOrder_iff hRo n₁ w _).1 (hsfwS w hw hwl)).1
  have hn1l : CSTowerT21.Stab.evU (a := a₁) (b := b₁) vl n₁ ∈ Submodule.localBoxUnits R₁ vl :=
    CSTowerT21.Stab.map_mem_localBoxUnits_of_mem_primeHeckeSet hqp.ne_zero hn₁
      (CSTowerT21.Stab.not_mem_of_prime_ne hℓp hqp (Ne.symm hℓq) hvl)

  unfold HeckeTower.arrowDegree
  dsimp only
  by_cases hdiv : (ℓ.1 : ℕ) ∣ N
  ·
    rw [if_pos hdiv] at hs3
    rw [if_pos hdiv]
    have hO' : IsEichlerOrder (meetOrder R₁ sf) (N * (ℓ.1 : ℕ)) :=
      CSTower.isEichlerOrder_meetOrder_of_finiteIdeleDiagonal_mul_inv_mem_levelHeckeUSet_meetOrder
        hN hqN hq'N hqq' hdef₁ Λ₁ R₁ hΛ₁ hR₁ hRΛ₁ n₁ hn₁ hS₁ (ℓ.1 : ℕ) hdiv sf hs3
    rw [L5Index.Gamma_side hdef₁ hq'2 hRo hΛ₁ hRΛ₁ q (Ne.symm hqq') v₂ hv₂ (ℓ.1 : ℕ) hℓq hℓq' vl hvl s hsnrd sf
      hsf1 hsfwR hO' Γ hΓ0,
      ← L5Index.U_side hRo v₂ vl hvlv sf hsfv hsfwR]
    exact relIndex_finiteIdeleStabilizer_meetOrder_eq_of_mem_levelHeckeUSet_meetOrder_of_dvd hN hqN hq'N hqq' hq'5
      hdef₁ Λ₁ R₁ hΛ₁ hR₁ hRΛ₁ n₁ hn₁ (ℓ.1 : ℕ) hdiv sf hs3
  ·
    rw [if_neg hdiv] at hs3
    rw [if_neg hdiv]
    have hℓNqq' : ¬ (ℓ.1 : ℕ) ∣ N * q * q' := fun h => by
      rcases (Nat.Prime.dvd_mul hℓp).1 h with h | h
      · rcases (Nat.Prime.dvd_mul hℓp).1 h with h | h
        · exact hdiv h
        · exact hℓq ((Nat.prime_dvd_prime_iff_eq hℓp hqp).1 h)
      · exact hℓq' ((Nat.prime_dvd_prime_iff_eq hℓp hq'p).1 h)
    have hℓNq : ¬ (ℓ.1 : ℕ) ∣ N * q := fun h => hℓNqq' (Dvd.dvd.mul_right h q')
    have hO' : IsEichlerOrder (meetOrder R₁ sf) (N * (ℓ.1 : ℕ)) :=
      CSTower.isEichlerOrder_meetOrder_of_finiteIdeleDiagonal_mul_inv_mem_primeHeckeSet_meetOrder
        hdef₁ hR₁ n₁ hS₁ (ℓ.1 : ℕ) hℓNqq' sf hs3
    rw [L5Index.Gamma_side hdef₁ hq'2 hRo hΛ₁ hRΛ₁ q (Ne.symm hqq') v₂ hv₂ (ℓ.1 : ℕ) hℓq hℓq' vl hvl s hsnrd sf
      hsf1 hsfwR hO' Γ hΓ0,
      ← L5Index.localBoxUnits_meetOrder_eq_of_mem hRo n₁ vl hn1l,
      ← L5Index.localBoxUnits_meetOrder_meetOrder_eq hRo n₁ sf vl hn1l,
      ← L5Index.U_side hSo v₂ vl hvlv sf hsfv hsfwS]
    exact relIndex_finiteIdeleStabilizer_meetOrder_eq_succ_of_mem_primeHeckeSet hdef₁ hS₁ (ℓ.1 : ℕ) hℓNq hℓq' hsfT

end S_CerednikDrinfeld_CosetGraph_relIndex_inf_map_conj_eq_arrowDegree_of_hecke
end P2MW
export P2MW.S_CerednikDrinfeld_CosetGraph_relIndex_inf_map_conj_eq_arrowDegree_of_hecke (solution)
