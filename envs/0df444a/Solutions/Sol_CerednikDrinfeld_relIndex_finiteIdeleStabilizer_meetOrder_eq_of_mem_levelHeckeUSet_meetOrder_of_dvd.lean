-- Prove2me | solution 1 for CerednikDrinfeld.relIndex_finiteIdeleStabilizer_meetOrder_eq_of_mem_levelHeckeUSet_meetOrder_of_dvd
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.491319+00:00
-- url     : https://prove2.me/submissions/fd41d2f9-3614-5f7f-9ac6-2438850e75ba

import Definitions.Def_CerednikDrinfeld_ClassSetGraph
import Definitions.Def_QuaternionAlgebra_EichlerOrder
import Theorems.Thm_Submodule_mem_finiteAdeleBox_iff_forall_finiteAdeleEvalAt_mem_localBox
import Theorems.Thm_Submodule_localBox_inf
import Theorems.Thm_Submodule_mem_localBox_conjByFiniteIdele_iff
import Theorems.Thm_Submodule_ofFiniteIdele_one
import Theorems.Thm_QuaternionAlgebra_IsOrder_conjByFiniteIdele
import Theorems.Thm_QuaternionAlgebra_IsOrder_mem_finiteIdeleStabilizer_iff_forall_map_finiteAdeleEvalAt_mem_localBoxUnits
import Theorems.Thm_QuaternionAlgebra_IsOrder_finiteAdeleBox_inf_conjByFiniteIdele_eq_and_finiteIdeleStabilizer_le
import Theorems.Thm_QuaternionAlgebra_IsOrder_relIndex_finiteIdeleStabilizer_inf_map_conj_eq_local
import Theorems.Thm_QuaternionAlgebra_IsEichlerOrder_natCard_setOf_exists_quotientMk_stabilizer_localBox_levelU_eq_of_dvd_of_squarefree
import Definitions.Def_AlgebraicCurve_TotallyDegenerateCovering_Hom
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_relIndex_finiteIdeleStabilizer_meetOrder_eq_of_mem_levelHeckeUSet_meetOrder_of_dvd
p2m_attr_erase "instance" "IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue AlgebraicCurve.instFundamentalIdentityOfSumRamificationInertia AlgebraicCurve.Place.instIsScalarTowerResidueFieldRestrictPushforward AlgebraicCurve.Place.instAlgebraResidueFieldRestrictPushforward AlgebraicCurve.Place.instIsLocalHomRestrictInclusion AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupDivisor AlgebraicCurve.Pic0.instModuleZModTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instDistribMulActionTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instSMulTorsion AlgebraicCurve.SemilinearAut.instMulActionSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instSMulCommClassZModTorsion AlgebraicCurve.SemilinearAut.instMulSemiringActionSubtypeProdRingAutMemSubgroup ModularCurve.SpecializationWitnessData.addCommGroup ModularCurve.CommutingHeckeFamily.commRing_adjoin ModularCurve.Gamma0Pair.isElliptic ModularCurve.ModuliTestDatum.isElliptic_reduced ModularCurve.ModuliTestDatum.isElliptic_curve ModularCurve.ModuliTestDatum.isElliptic_generic"
p2m_attr_erase "simp" "LocalGL2.swapUnit_val QuaternionAlgebra.baseChangeRight_tmul QuaternionAlgebra.mapOfAlgebraMapEq_apply QuaternionAlgebra.baseChange_tmul ModularCurve.coe_levelAlphaC ModularCurve.SSLevelDatum.mk.sizeOf_spec ModularCurve.SSLevelDatum.mk.injEq ModularCurve.coe_levelBetaC ModularCurve.coe_heckeBetaC AlgebraicCurve.Divisor.coe_degZeroEnd ModularCurve.coe_heckeAlphaC AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Divisor.mapRestrict_single AlgebraicCurve.Divisor.pushforward_single AlgebraicCurve.Place.coe_restrictInclusion AlgebraicCurve.Place.mem_fiber AlgebraicCurve.Place.restrict_toValuationSubring AlgebraicCurve.Divisor.degree_pushforward AlgebraicCurve.Place.restrictResidueMap_residue AlgebraicCurve.Pic0.coe_pushforwardDegZeroHom AlgebraicCurve.Pic0.coe_pullbackDegZeroHom AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply"
p2m_attr_erase "simp" "AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.Divisor.degree_pushforwardAlong AlgebraicCurve.Pic0.coe_degZeroCorrespondence AlgebraicCurve.Place.mem_fiberAlong AlgebraicCurve.SemilinearAut.toRingAut_inv AlgebraicCurve.SemilinearAut.smul_def AlgebraicCurve.SemilinearAut.smul_single AlgebraicCurve.SemilinearAut.smul_toValuationSubring AlgebraicCurve.SemilinearAut.baseAut_inv AlgebraicCurve.SemilinearAut.baseAut_ofAlgAut AlgebraicCurve.SemilinearAut.toRingAut_ofAlgAut AlgebraicCurve.SemilinearAut.torsionRep_apply AlgebraicCurve.SemilinearAut.toRingAut_one AlgebraicCurve.SemilinearAut.deg_smul AlgebraicCurve.SemilinearAut.degree_smul AlgebraicCurve.SemilinearAut.coe_degZeroSMulHom AlgebraicCurve.SemilinearAut.baseAut_mul AlgebraicCurve.SemilinearAut.coe_smulValuationSubringEquiv_apply AlgebraicCurve.SemilinearAut.baseAut_one AlgebraicCurve.SemilinearAut.ofAlgAut_smul AlgebraicCurve.SemilinearAut.coe_torsion_smul AlgebraicCurve.SemilinearAut.toRingAut_mul AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.jqNModC_one ModularCurve.qExpand_coeff_mul ModularCurve.qExpandₐ_apply ModularCurve.jqN_one ModularCurve.qExpand_single ModularCurve.dedekindPsi_one ModularCurve.ModularPolynomialData.mk.sizeOf_spec ModularCurve.evalAtJ_X ModularCurve.ModularPolynomialData.mk.injEq ModularCurve.constantCoeff_jNum ModularCurve.constantCoeff_eisenstein4 ModularCurve.qExpand_C ModularCurve.coeff_jq_neg_one ModularCurve.constantCoeff_jNumQ ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff"
p2m_attr_erase "simp" "ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd ModularCurve.CommutingHeckeFamily.mk.injEq ModularCurve.SpecializationWitnessData.mk.sizeOf_spec ModularCurve.SpecializationWitnessData.mk.injEq ModularCurve.CommutingHeckeFamily.mk.sizeOf_spec ModularCurve.coe_nodeEquivOfPlaces_apply ModularCurve.widthOfPlaces_mk ModularCurve.smulNodePairEmb_apply ModularCurve.card_nodePairsOfPlaces ModularCurve.smulNodePair_snd ModularCurve.smulNodePair_fst ModularCurve.coe_nodeEquivOfPlaces_symm_apply ModularCurve.coe_jGeomGen ModularCurve.coe_jNGeomGen ModularCurve.coe_uniformizerMod ModularCurve.qSeriesBar_jModElt ModularCurve.qInftyPlaceMod_toValuationSubring ModularCurve.qInftyPlaceBar_toValuationSubring ModularCurve.qSeriesBar_zero ModularCurve.qSeriesBar_add ModularCurve.cuspInftyFull_toValuationSubring ModularCurve.qInftyPlaceRat_toValuationSubring ModularCurve.qSeriesBar_mul ModularCurve.qSeriesBar_div ModularCurve.qSeriesBar_eq_zero_iff ModularCurve.coe_uniformizerBar ModularCurve.qSeriesBar_pow ModularCurve.cuspInfty_toValuationSubring ModularCurve.qSeriesBar_one ModularCurve.qSeriesBar_inv ModularCurve.qSeriesBar_sub ModularCurve.qSeriesBar_neg"
p2m_attr_erase "simp" "ModularCurve.charLGeomModuliDictionary_single ModularCurve.specializeModuli_single ModularCurve.specializePlace_def ModularCurve.gamma0PairMap_gen ModularCurve.moduliPointMapRingHom_mk ModularCurve.Gamma0Pair.mk.injEq ModularCurve.ModuliPoint.j_mk ModularCurve.Gamma0Pair.mk.sizeOf_spec ModularCurve.gamma0PairMap_toCurve WeierstrassCurve.Affine.vcY_vcYInv WeierstrassCurve.Affine.vcXInv_vcX WeierstrassCurve.Affine.Point.vcFun_zero WeierstrassCurve.Affine.vcX_vcXInv WeierstrassCurve.Affine.vcYInv_vcY WeierstrassCurve.Affine.Point.vcInvFun_zero WeierstrassCurve.ratPointHom_apply WeierstrassCurve.ratPointMap_zero ModularCurve.ComapPlace.place_toValuationSubring ModularCurve.ModuliTestDatum.restrictLevel_emb ModularCurve.ModuliTestDatum.restrictLevel_res ModularCurve.ModuliTestDatum.mk.injEq ModularCurve.ModuliTestDatum.restrictLevel_W ModularCurve.ModuliTestDatum.place_toValuationSubring ModularCurve.ModuliTestDatum.restrictLevel_curve ModularCurve.ModuliTestDatum.resEquiv_apply ModularCurve.ModuliTestDatum.restrictLevel_gen ModularCurve.ModuliTestDatum.mk.sizeOf_spec ModularCurve.coe_jqNFull ModularCurve.qExpandAlgHomC_apply ModularCurve.coeffEmb_coeff ModularCurve.coeffMap_coeff ModularCurve.coeffMap_id ModularCurve.coeffMap_single ModularCurve.Gamma0Pair.map_toCurve WeierstrassCurve.mapPoint_eq_ratPointMap ModularCurve.Gamma0Pair.map_gen ModularCurve.Gamma0Pair.map_eq_gamma0PairMap ModularCurve.ModuliPoint.map_eq_moduliPointMapRingHom ModularCurve.ModuliPoint.map_mk WeierstrassCurve.mapPointHom_apply"
p2m_attr_erase "simp" "WeierstrassCurve.mapPoint_zero WeierstrassCurve.twoVeluCurve_a₁ WeierstrassCurve.twoVeluCurve_a₂ WeierstrassCurve.twoVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₂ WeierstrassCurve.xVeluCurve_a₁ WeierstrassCurve.veluWSum_empty WeierstrassCurve.veluQuotient_a₁ WeierstrassCurve.veluQuotient_a₃ WeierstrassCurve.veluQuotient_empty WeierstrassCurve.veluTSum_empty WeierstrassCurve.veluQuotient_a₂ WeierstrassCurve.veluQuotient2_a₂ WeierstrassCurve.veluQuotient2_a₃ WeierstrassCurve.veluQuotient2_a₁ WeierstrassCurve.veluPointMap2_zero WeierstrassCurve.Affine.Point.coordsOrZero_some WeierstrassCurve.Affine.Point.coordsOrZero_zero"

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

open scoped TensorProduct Quaternion NumberField Pointwise
open IsDedekindDomain NumberField QuaternionAlgebra CerednikDrinfeld

namespace INDEXU48

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

private theorem _root_.INDEXU48.mem_stabilizer_iff {Λ : Submodule ℤ ℍ[ℚ, a, b]} (hΛ : IsOrder Λ) (u : (ℍ𝔸)ˣ) :
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

p2m_export "INDEXU48" "mem_stabilizer_iff"

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

theorem eq_of_natCast_prime_mem {ℓ : ℕ} (hℓ : ℓ.Prime) {v w : HeightOneSpectrum (𝓞 ℚ)}
    (hv : ((ℓ : ℕ) : 𝓞 ℚ) ∈ v.asIdeal) (hw : ((ℓ : ℕ) : 𝓞 ℚ) ∈ w.asIdeal) : v = w := by
  apply (Rat.HeightOneSpectrum.primesEquiv (R := 𝓞 ℚ)).injective
  apply Subtype.ext
  show Rat.HeightOneSpectrum.natGenerator v = Rat.HeightOneSpectrum.natGenerator w
  rw [← natGenerator_dvd_iff'] at hv hw
  rw [(Nat.prime_dvd_prime_iff_eq (Rat.HeightOneSpectrum.prime_natGenerator v) hℓ).mp hv,
    (Nat.prime_dvd_prime_iff_eq (Rat.HeightOneSpectrum.prime_natGenerator w) hℓ).mp hw]

theorem box_mono {Λ Λ' : Submodule ℤ ℍ[ℚ, a, b]} (h : Λ ≤ Λ') :
    Submodule.finiteAdeleBox Λ ≤ Submodule.finiteAdeleBox Λ' := by
  unfold Submodule.finiteAdeleBox
  refine AddSubgroup.closure_mono ?_
  rintro x ⟨z, hz, c, hc, rfl⟩
  exact ⟨z, h hz, c, hc, rfl⟩

theorem localBox_mono {Λ Λ' : Submodule ℤ ℍ[ℚ, a, b]} (h : Λ ≤ Λ') (v : HeightOneSpectrum (𝓞 ℚ)) :
    Submodule.localBox Λ v ≤ Submodule.localBox Λ' v := by
  unfold Submodule.localBox
  refine AddSubgroup.closure_mono ?_
  rintro x ⟨z, hz, c, hc, rfl⟩
  exact ⟨z, h hz, c, hc, rfl⟩

theorem tmul_one_mem_localBox {Λ : Submodule ℤ ℍ[ℚ, a, b]} {z : ℍ[ℚ, a, b]} (hz : z ∈ Λ) (v : HeightOneSpectrum (𝓞 ℚ)) :
    z ⊗ₜ[ℚ] (1 : v.adicCompletion ℚ) ∈ Submodule.localBox Λ v := by
  rw [mem_localBox_iff_span]
  exact Submodule.subset_span ⟨z, hz, 1, one_mem _, rfl⟩

theorem tmul_one_mem_box {Λ : Submodule ℤ ℍ[ℚ, a, b]} {z : ℍ[ℚ, a, b]} (hz : z ∈ Λ) :
    z ⊗ₜ[ℚ] (1 : FiniteAdeleRing (𝓞 ℚ) ℚ) ∈ Submodule.finiteAdeleBox Λ := by
  rw [mem_box_iff_span]
  refine Submodule.subset_span ⟨z, hz, 1, fun v => ?_, rfl⟩
  have e : (1 : FiniteAdeleRing (𝓞 ℚ) ℚ) v = 1 := rfl
  rw [e]; exact one_mem _

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

theorem inv_mul_mul_conj_eq {M : Type*} [Monoid M] (u : Mˣ) (y : M) :
    ((u⁻¹ : Mˣ) : M) * ((u : M) * y * ((u⁻¹ : Mˣ) : M)) * (u : M) = y := by
  rw [← mul_assoc, ← mul_assoc, Units.inv_mul, one_mul, Units.inv_mul_cancel_right]

theorem mul_inv_mul_conj_eq {M : Type*} [Monoid M] (u : Mˣ) (y : M) :
    (u : M) * (((u⁻¹ : Mˣ) : M) * y * (u : M)) * ((u⁻¹ : Mˣ) : M) = y := by
  rw [← mul_assoc, ← mul_assoc, Units.mul_inv, one_mul, Units.mul_inv_cancel_right]

theorem mem_of_tmul_one_mem_box {Λ : Submodule ℤ ℍ[ℚ, a, b]} (hΛ : IsOrder Λ) {z : ℍ[ℚ, a, b]}
    (hz : z ⊗ₜ[ℚ] (1 : FiniteAdeleRing (𝓞 ℚ) ℚ) ∈ Submodule.finiteAdeleBox Λ) : z ∈ Λ := by
  have key : z ∈ Submodule.ofFiniteIdele Λ 1 := by
    rw [Submodule.mem_ofFiniteIdele_iff, AddSubgroup.mem_map]
    exact ⟨_, hz, by rw [AddMonoidHom.coe_mulLeft, Units.val_one, one_mul]⟩
  rwa [Submodule.ofFiniteIdele_one Λ hΛ.fg hΛ.spanTop] at key

theorem localBoxUnits_mono {S R : Submodule ℤ ℍ[ℚ, a, b]} (h : S ≤ R) (w : HeightOneSpectrum (𝓞 ℚ))
    {t : (ℍ[ℚ, a, b] ⊗[ℚ] w.adicCompletion ℚ)ˣ} (ht : t ∈ Submodule.localBoxUnits S w) :
    t ∈ Submodule.localBoxUnits R w :=
  ⟨localBox_mono h w ht.1, localBox_mono h w ht.2⟩

theorem conj_mem_stabilizer_of_mem_localBoxUnits {Λ : Submodule ℤ ℍ[ℚ, a, b]} (hΛ : IsOrder Λ)
    (w : HeightOneSpectrum (𝓞 ℚ)) {t : (ℍ[ℚ, a, b] ⊗[ℚ] w.adicCompletion ℚ)ˣ} (ht : t ∈ Submodule.localBoxUnits Λ w)
    (u : (ℍ[ℚ, a, b] ⊗[ℚ] w.adicCompletion ℚ)ˣ)
    (hu : u ∈ MulAction.stabilizer (ℍ[ℚ, a, b] ⊗[ℚ] w.adicCompletion ℚ)ˣ
      ((Submodule.localBox Λ w : AddSubgroup (ℍ[ℚ, a, b] ⊗[ℚ] w.adicCompletion ℚ)) : Set (ℍ[ℚ, a, b] ⊗[ℚ] w.adicCompletion ℚ))) :
    t⁻¹ * u * t ∈ MulAction.stabilizer (ℍ[ℚ, a, b] ⊗[ℚ] w.adicCompletion ℚ)ˣ
      ((Submodule.localBox Λ w : AddSubgroup (ℍ[ℚ, a, b] ⊗[ℚ] w.adicCompletion ℚ)) : Set (ℍ[ℚ, a, b] ⊗[ℚ] w.adicCompletion ℚ)) := by
  rw [mem_stabilizer_localBox_iff hΛ] at hu ⊢
  exact (conj_mem_localBoxUnits_iff hΛ w ht u).mpr hu

theorem inv_mem_localBoxUnits {Λ : Submodule ℤ ℍ[ℚ, a, b]} (w : HeightOneSpectrum (𝓞 ℚ))
    {t : (ℍ[ℚ, a, b] ⊗[ℚ] w.adicCompletion ℚ)ˣ} (ht : t ∈ Submodule.localBoxUnits Λ w) :
    t⁻¹ ∈ Submodule.localBoxUnits Λ w := by
  rw [mem_localBoxUnits_iff'] at ht ⊢
  rw [inv_inv]; exact ⟨ht.2, ht.1⟩

theorem offUnit_of_mem_levelHeckeUSet {O Λ : Submodule ℤ ℍ[ℚ, a, b]} (hO : IsOrder O) {ℓ : ℕ} (hℓ : ℓ.Prime)
    {h : (ℍ𝔸)ˣ} (hh : h ∈ levelHeckeUSet Λ O ℓ) {v : HeightOneSpectrum (𝓞 ℚ)} (hℓv : ((ℓ : ℕ) : 𝓞 ℚ) ∈ v.asIdeal)
    (w : HeightOneSpectrum (𝓞 ℚ)) (hw : w ≠ v) :
    (evU (a := a) (b := b) w) h ∈ Submodule.localBoxUnits O w :=
  map_mem_localBoxUnits_of_mem_primeHeckeSet hℓ.ne_zero hh.1 (fun hℓw => hw (eq_of_natCast_prime_mem hℓ hℓw hℓv))

theorem localBox_meetOrder_eq {R : Submodule ℤ ℍ[ℚ, a, b]} (hR : IsOrder R) {n : (ℍ𝔸)ˣ} (v : HeightOneSpectrum (𝓞 ℚ))
    (hn : (evU (a := a) (b := b) v) n ∈ Submodule.localBoxUnits R v) :
    Submodule.localBox (meetOrder R n) v = Submodule.localBox R v := by
  have hc : IsOrder (Submodule.conjByFiniteIdele R n) := IsOrder.conjByFiniteIdele R hR n
  rw [show meetOrder R n = R ⊓ Submodule.conjByFiniteIdele R n from rfl,
    Submodule.localBox_inf R (Submodule.conjByFiniteIdele R n) hR.fg hR.spanTop hc.fg hc.spanTop v]
  refine le_antisymm inf_le_left (le_inf le_rfl ?_)
  intro x hx
  rw [Submodule.mem_localBox_conjByFiniteIdele_iff R hR.fg hR.spanTop n v]
  have hu := (mem_localBoxUnits_iff' R v _).mp hn
  refine ⟨(ev v) ((n⁻¹ : (ℍ𝔸)ˣ) : ℍ𝔸) * x * (ev v) (n : ℍ𝔸),
    localBox_mul_mem hR v (localBox_mul_mem hR v hu.2 hx) hu.1, ?_⟩
  exact (mul_inv_mul_conj_eq ((evU (a := a) (b := b) v) n) x).symm

theorem localClauses_of_mem_levelHeckeUSet {O Λ : Submodule ℤ ℍ[ℚ, a, b]} (hO : IsOrder O) (hΛ : IsOrder Λ)
    (hOΛ : O ≤ Λ) {ℓ : ℕ} (hℓ : ℓ.Prime) {h : (ℍ𝔸)ˣ} (hh : h ∈ levelHeckeUSet Λ O ℓ)
    (v : HeightOneSpectrum (𝓞 ℚ)) (hℓv : ((ℓ : ℕ) : 𝓞 ℚ) ∈ v.asIdeal) :
    ((((Units.map (Submodule.finiteAdeleEvalAt ℍ[ℚ, a, b] v).toRingHom.toMonoidHom h) : ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ) ∈ Submodule.localBox O v ∧
            (ℓ : ℚ) • (((Units.map (Submodule.finiteAdeleEvalAt ℍ[ℚ, a, b] v).toRingHom.toMonoidHom h)⁻¹ : (ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ)ˣ) : ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ) ∈ Submodule.localBox O v ∧
            (((Units.map (Submodule.finiteAdeleEvalAt ℍ[ℚ, a, b] v).toRingHom.toMonoidHom h)⁻¹ : (ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ)ˣ) : ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ) ∉ Submodule.localBox O v ∧
            (ℓ : ℚ)⁻¹ • ((Units.map (Submodule.finiteAdeleEvalAt ℍ[ℚ, a, b] v).toRingHom.toMonoidHom h) : ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ) ∉ Submodule.localBox O v) ∧
           ¬ (∀ z : ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ,
                (((Units.map (Submodule.finiteAdeleEvalAt ℍ[ℚ, a, b] v).toRingHom.toMonoidHom h)⁻¹ : (ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ)ˣ) : ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ) * z * ((Units.map (Submodule.finiteAdeleEvalAt ℍ[ℚ, a, b] v).toRingHom.toMonoidHom h) : ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ) ∈ Submodule.localBox O v ↔ z ∈ Submodule.localBox O v) ∧
           ¬ (∀ z : ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ, z ∈ Submodule.localBox O v →
                (((Units.map (Submodule.finiteAdeleEvalAt ℍ[ℚ, a, b] v).toRingHom.toMonoidHom h)⁻¹ : (ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ)ˣ) : ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ) * z * ((Units.map (Submodule.finiteAdeleEvalAt ℍ[ℚ, a, b] v).toRingHom.toMonoidHom h) : ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ) ∈ Submodule.localBox Λ v)) := by
  obtain ⟨hhT, hne, hnle⟩ := hh
  obtain ⟨h1, h2, h3, h4⟩ := hhT
  have hoff : ∀ w : HeightOneSpectrum (𝓞 ℚ), w ≠ v →
      (evU (a := a) (b := b) w) h ∈ Submodule.localBoxUnits O w := fun w hw =>
    map_mem_localBoxUnits_of_mem_primeHeckeSet hℓ.ne_zero ⟨h1, h2, h3, h4⟩
      (fun hℓw => hw (eq_of_natCast_prime_mem hℓ hℓw hℓv))
  have cg : (((evU (a := a) (b := b) v) h : (ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ)ˣ) : ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ) = (ev v) (h : ℍ𝔸) := rfl
  have cgi : ((((evU (a := a) (b := b) v) h)⁻¹ : (ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ)ˣ) : ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ) = (ev v) ((h⁻¹ : (ℍ𝔸)ˣ) : ℍ𝔸) := rfl
  refine ⟨⟨?_, ?_, ?_, ?_⟩, ?_, ?_⟩
  ·
    rw [cg]; exact finiteAdeleEvalAt_mem_localBox v h1
  ·
    rw [cgi, ← ev_smul]; exact finiteAdeleEvalAt_mem_localBox v h2
  ·
    intro H
    apply h3
    rw [Submodule.mem_finiteAdeleBox_iff_forall_finiteAdeleEvalAt_mem_localBox O hO.fg hO.spanTop]
    intro w
    by_cases hw : w = v
    · subst hw; rwa [cgi] at H
    · exact ((mem_localBoxUnits_iff' O w _).mp (hoff w hw)).2
  ·
    intro H
    apply h4
    rw [Submodule.mem_finiteAdeleBox_iff_forall_finiteAdeleEvalAt_mem_localBox O hO.fg hO.spanTop]
    intro w
    rw [ev_smul]
    by_cases hw : w = v
    · subst hw; rwa [cg] at H
    · have hℓw : ((ℓ : ℕ) : 𝓞 ℚ) ∉ w.asIdeal := fun hℓw => hw (eq_of_natCast_prime_mem hℓ hℓw hℓv)
      exact smul_mem_localBox w (algebraMap_inv_natCast_mem w ℓ hℓw) (finiteAdeleEvalAt_mem_localBox w h1)
  ·
    intro H
    apply hne
    ext z
    rw [Submodule.mem_conjByFiniteIdele_iff, AddSubgroup.mem_map]
    constructor
    · rintro ⟨y, hy, hyz⟩
      change (h : ℍ𝔸) * y * ((h⁻¹ : (ℍ𝔸)ˣ) : ℍ𝔸) = z ⊗ₜ[ℚ] (1 : FiniteAdeleRing (𝓞 ℚ) ℚ) at hyz
      apply mem_of_tmul_one_mem_box hO
      rw [Submodule.mem_finiteAdeleBox_iff_forall_finiteAdeleEvalAt_mem_localBox O hO.fg hO.spanTop] at hy ⊢
      intro w
      rw [← hyz, map_mul, map_mul]
      by_cases hw : w = v
      · subst hw
        rw [← cg, ← cgi]
        refine (H _).mp ?_
        rw [inv_mul_mul_conj_eq]
        exact hy _
      · have hu := (mem_localBoxUnits_iff' O w _).mp (hoff w hw)
        exact localBox_mul_mem hO w (localBox_mul_mem hO w hu.1 (hy w)) hu.2
    · intro hz
      refine ⟨((h⁻¹ : (ℍ𝔸)ˣ) : ℍ𝔸) * (z ⊗ₜ[ℚ] (1 : FiniteAdeleRing (𝓞 ℚ) ℚ)) * (h : ℍ𝔸), ?_,
        mul_inv_mul_conj_eq h _⟩
      rw [Submodule.mem_finiteAdeleBox_iff_forall_finiteAdeleEvalAt_mem_localBox O hO.fg hO.spanTop]
      intro w
      rw [map_mul, map_mul]
      by_cases hw : w = v
      · subst hw
        rw [← cg, ← cgi, H]
        exact finiteAdeleEvalAt_mem_localBox _ (tmul_one_mem_box hz)
      · have hu := (mem_localBoxUnits_iff' O w _).mp (hoff w hw)
        exact localBox_mul_mem hO w (localBox_mul_mem hO w hu.2
          (finiteAdeleEvalAt_mem_localBox w (tmul_one_mem_box hz))) hu.1
  ·
    intro H
    apply hnle
    intro z hz
    rw [Submodule.mem_conjByFiniteIdele_iff, AddSubgroup.mem_map]
    refine ⟨((h⁻¹ : (ℍ𝔸)ˣ) : ℍ𝔸) * (z ⊗ₜ[ℚ] (1 : FiniteAdeleRing (𝓞 ℚ) ℚ)) * (h : ℍ𝔸), ?_,
      mul_inv_mul_conj_eq h _⟩
    rw [Submodule.mem_finiteAdeleBox_iff_forall_finiteAdeleEvalAt_mem_localBox Λ hΛ.fg hΛ.spanTop]
    intro w
    rw [map_mul, map_mul]
    by_cases hw : w = v
    · subst hw
      rw [← cg, ← cgi]
      exact H _ (finiteAdeleEvalAt_mem_localBox _ (tmul_one_mem_box hz))
    · have hu := (mem_localBoxUnits_iff' O w _).mp (hoff w hw)
      exact localBox_mono hOΛ w (localBox_mul_mem hO w (localBox_mul_mem hO w hu.2
        (finiteAdeleEvalAt_mem_localBox w (tmul_one_mem_box hz))) hu.1)

theorem finiteIdeleDiagonal_algebraMap_mul_comm (c : ℚˣ) (x : (ℍ𝔸)ˣ) :
    Submodule.finiteIdeleDiagonal ℍ[ℚ, a, b] (Units.map (algebraMap ℚ ℍ[ℚ, a, b]).toMonoidHom c) * x =
      x * Submodule.finiteIdeleDiagonal ℍ[ℚ, a, b] (Units.map (algebraMap ℚ ℍ[ℚ, a, b]).toMonoidHom c) := by
  apply Units.ext
  have e : ((Submodule.finiteIdeleDiagonal ℍ[ℚ, a, b] (Units.map (algebraMap ℚ ℍ[ℚ, a, b]).toMonoidHom c) : (ℍ𝔸)ˣ) :
      ℍ𝔸) = algebraMap ℚ (ℍ𝔸) (c : ℚ) := by
    rw [Submodule.val_finiteIdeleDiagonal_apply, Algebra.TensorProduct.algebraMap_apply]; rfl
  rw [Units.val_mul, Units.val_mul, e]
  exact Algebra.commutes _ _

theorem conj_finiteIdeleDiagonal_algebraMap_eq_one (c : ℚˣ) :
    MulAut.conj (Submodule.finiteIdeleDiagonal ℍ[ℚ, a, b] (Units.map (algebraMap ℚ ℍ[ℚ, a, b]).toMonoidHom c)) = 1 := by
  ext x
  rw [MulAut.conj_apply, finiteIdeleDiagonal_algebraMap_mul_comm, mul_inv_cancel_right, MulAut.one_apply]

end INDEXU48

open INDEXU48 in

theorem solution

    {a b : ℚ} {N q q' : ℕ} [NeZero N] (hN : Squarefree N) [Fact q.Prime] [Fact q'.Prime]
    (hqN : ¬ q ∣ N) (hq'N : ¬ q' ∣ N) (hqq' : q' ≠ q) (hq'5 : 5 ≤ q')
    (hdef : IsDefiniteRamifiedExactlyAt a b q')
    (Λ R : Submodule ℤ ℍ[ℚ, a, b]) (hΛ : IsMaximalOrder Λ) (hR : IsEichlerOrder R N) (hRΛ : R ≤ Λ)
    (n : (ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) (hn : n ∈ primeHeckeSet R q)

    (ℓ : ℕ) [Fact ℓ.Prime] (hℓ : ℓ ∣ N)
    (s : (ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ)
    (hs : Submodule.finiteIdeleDiagonal ℍ[ℚ, a, b]
        (Units.map (algebraMap ℚ ℍ[ℚ, a, b]).toMonoidHom
          (Units.mk0 (ℓ : ℚ) (Nat.cast_ne_zero.mpr (Fact.out : ℓ.Prime).ne_zero))) * s⁻¹ ∈
      levelHeckeUSet Λ (meetOrder R n) ℓ) :
    (Submodule.finiteIdeleStabilizer (meetOrder R s)).relIndex (Submodule.finiteIdeleStabilizer R) = ℓ := by
  have hRo : IsOrder R := hR.isOrder
  have hΛo : IsOrder Λ := hΛ.isOrder
  have hS : IsOrder (meetOrder R n) := isOrder_meetOrder hRo n
  have hSR : meetOrder R n ≤ R := inf_le_left
  have hℓp : ℓ.Prime := Fact.out
  have hq : q.Prime := Fact.out
  have hqℓ : q ≠ ℓ := fun e => hqN (by rw [e]; exact hℓ)
  have hℓq' : q' ≠ ℓ := fun e => hq'N (by rw [e]; exact hℓ)
  obtain ⟨v, hℓv⟩ := exists_place ℓ hℓp
  have hqv : ((q : ℕ) : 𝓞 ℚ) ∉ v.asIdeal := not_mem_of_prime_ne hℓp hq hqℓ hℓv
  have hnv : (Units.map (Submodule.finiteAdeleEvalAt ℍ[ℚ, a, b] v).toRingHom.toMonoidHom) n ∈ Submodule.localBoxUnits R v :=
    map_mem_localBoxUnits_of_mem_primeHeckeSet hq.ne_zero hn hqv
  have eS : Submodule.localBox (meetOrder R n) v = Submodule.localBox R v := localBox_meetOrder_eq hRo v hnv

  have econj : MulAut.conj ((Submodule.finiteIdeleDiagonal ℍ[ℚ, a, b]
        (Units.map (algebraMap ℚ ℍ[ℚ, a, b]).toMonoidHom
          (Units.mk0 (ℓ : ℚ) (Nat.cast_ne_zero.mpr (Fact.out : ℓ.Prime).ne_zero))) * s⁻¹)⁻¹) = MulAut.conj s := by
    rw [mul_inv_rev, inv_inv, map_mul, map_inv, conj_finiteIdeleDiagonal_algebraMap_eq_one, inv_one, mul_one]

  have key := IsOrder.relIndex_finiteIdeleStabilizer_inf_map_conj_eq_local R hRo v
    ((Submodule.finiteIdeleDiagonal ℍ[ℚ, a, b]
        (Units.map (algebraMap ℚ ℍ[ℚ, a, b]).toMonoidHom
          (Units.mk0 (ℓ : ℚ) (Nat.cast_ne_zero.mpr (Fact.out : ℓ.Prime).ne_zero))) * s⁻¹)⁻¹) (by
    intro w hw u hu
    rw [map_inv, inv_inv]
    have hm := localBoxUnits_mono hSR w (offUnit_of_mem_levelHeckeUSet hS hℓp hs hℓv w hw)
    have := conj_mem_stabilizer_of_mem_localBoxUnits hRo w (inv_mem_localBoxUnits w hm) u hu
    rwa [inv_inv] at this)
  have hloc := localClauses_of_mem_levelHeckeUSet hS hΛo (hSR.trans hRΛ) hℓp hs v hℓv
  rw [eS] at hloc
  rw [finiteIdeleStabilizer_meetOrder_eq hRo s, ← econj, key, map_inv]
  exact ((IsEichlerOrder.natCard_setOf_exists_quotientMk_stabilizer_localBox_levelU_eq_of_dvd_of_squarefree
    R Λ hN hR hΛ hRΛ ℓ hℓ hℓq' hdef hq'N v hℓv).2 _ hloc).2

end S_CerednikDrinfeld_relIndex_finiteIdeleStabilizer_meetOrder_eq_of_mem_levelHeckeUSet_meetOrder_of_dvd
end P2MW
export P2MW.S_CerednikDrinfeld_relIndex_finiteIdeleStabilizer_meetOrder_eq_of_mem_levelHeckeUSet_meetOrder_of_dvd (solution)
