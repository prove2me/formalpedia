-- Prove2me | solution 1 for BalanceSpecification.IsGibbsMeasure.ergodic
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T03:18:28.436383+00:00
-- url     : https://prove2.me/submissions/03ffba01-ec5d-45f9-ad57-4d385dad15c0

module
public import Definitions.Def_BalanceSpecificaton_CylinderAlgebra
public import Mathlib.Dynamics.Ergodic.Ergodic
public import Mathlib.Tactic
public import Definitions.Def_BalanceSpecificaton_GibbsErgodic
public import Theorems.Thm_BalanceSpecification_invariant_inter_cylinder_real_eq_zero
public import Theorems.Thm_BalanceSpecification_exists_near_pure_cylinder
public import Theorems.Thm_BalanceSpecification_GibbsBounds_invariant_inter_prefix_cross_bound
public import Theorems.Thm_BalanceSpecification_GibbsBounds_invariant_inter_suffix_cross_bound
public import Theorems.Thm_BalanceSpecification_GibbsBounds_cylinder_real_pos
public import Theorems.Thm_BalanceSpecification_IsGibbsMeasure_cylinder_real_pos
public import Theorems.Thm_BalanceSpecification_IsInvariant_cylinder_real_eq_zero
public import Theorems.Thm_BalanceSpecification_cylinder_nil
public import Theorems.Thm_BalanceSpecification_follower_card_reverseLanguage
public import Theorems.Thm_BalanceSpecification_getElem_block
public import Theorems.Thm_BalanceSpecification_length_block
public import Theorems.Thm_BalanceSpecification_mem_allWords
public import Theorems.Thm_BalanceSpecification_mem_followerFinset
public import Theorems.Thm_BalanceSpecification_mem_forbiddenShift_iff
public import Theorems.Thm_BalanceSpecification_mem_predecessorFinset
public import Theorems.Thm_BalanceSpecification_mem_shortWords
public import Theorems.Thm_BalanceSpecification_mem_wordFinset
public import Theorems.Thm_BalanceSpecification_wordCount_reverseLanguage
attribute [local simp] BalanceSpecification.cylinder_nil
attribute [local simp] BalanceSpecification.follower_card_reverseLanguage
attribute [local simp] BalanceSpecification.getElem_block
attribute [local simp] BalanceSpecification.length_block
attribute [local simp] BalanceSpecification.mem_allWords
attribute [local simp] BalanceSpecification.mem_followerFinset
attribute [local simp] BalanceSpecification.mem_forbiddenShift_iff
attribute [local simp] BalanceSpecification.mem_predecessorFinset
attribute [local simp] BalanceSpecification.mem_shortWords
attribute [local simp] BalanceSpecification.mem_wordFinset
attribute [local simp] BalanceSpecification.wordCount_reverseLanguage



set_option autoImplicit true
@[expose] public section
public section
noncomputable section
open MeasureTheory Set
open scoped symmDiff ENNReal
open BalanceSpecification
variable {A : Type*} [TopologicalSpace A] [Fintype A] [DiscreteTopology A]
  [MeasurableSpace A] [BorelSpace A]
namespace BalanceSpecification
namespace IsGibbsMeasure
theorem _root_.solution {X : ShiftSpace A} {hX : X.carrier.Nonempty}
    {μ : ProbabilityMeasure X.carrier} (hG : IsGibbsMeasure hX μ)
    (hirr : Irreducible X) : Ergodic (shiftMap X) (μ : Measure X.carrier) := by
  refine ⟨hG.1, ⟨fun B hB hBinv => ?_⟩⟩
  rw [Filter.eventuallyConst_set', ae_eq_empty, ae_eq_univ]
  by_contra hz
  push Not at hz
  let ρ : Measure X.carrier := μ
  have hBpos : 0 < ρ.real B := ENNReal.toReal_pos hz.1 (measure_ne_top ρ B)
  have hBcpos : 0 < ρ.real Bᶜ := ENNReal.toReal_pos hz.2 (measure_ne_top ρ Bᶜ)
  obtain ⟨K, hK⟩ := hG.2
  let C := K ^ 6
  have hC : 0 < C := pow_pos hK.1 6
  let δ := 1 / (2 * C)
  have hδ : 0 < δ := div_pos zero_lt_one (mul_pos (by norm_num) hC)
  have hCδ : C * δ = 1 / 2 := by
    dsimp only [δ]
    field_simp
  have hBcinv : (shiftMap X) ⁻¹' Bᶜ = Bᶜ := by rw [Set.preimage_compl, hBinv]
  obtain ⟨v, hv, k, _, hvnear⟩ := exists_near_pure_cylinder ρ hB.compl hBcpos hδ
  obtain ⟨w, hw, l, _, hwnear⟩ := exists_near_pure_cylinder ρ hB hBpos hδ
  let P : Word A → ℝ := fun z => ρ.real (cylinder X z 0)
  let R : Word A → ℝ := fun z => ρ.real (B ∩ cylinder X z 0)
  let T : Word A → ℝ := fun z => ρ.real (Bᶜ ∩ cylinder X z 0)
  have hparts (z : Word A) : R z + T z = P z := by
    have H := measureReal_inter_add_sdiff (μ := ρ) (s := cylinder X z 0) hB
      (measure_ne_top ρ _)
    simpa only [Set.sdiff_eq, Set.inter_comm, R, T, P] using H
  rw [hG.1.cylinder_real_eq_zero v k,
    invariant_inter_cylinder_real_eq_zero hG.1 hB.compl hBcinv v k] at hvnear
  rw [hG.1.cylinder_real_eq_zero w l,
    invariant_inter_cylinder_real_eq_zero hG.1 hB hBinv w l] at hwnear
  change (1 - δ) * P v < T v at hvnear
  change (1 - δ) * P w < R w at hwnear
  have hvsmall : R v < δ * P v := by linarith only [hvnear, hparts v]
  have hwsmall : T w < δ * P w := by linarith only [hwnear, hparts w]
  obtain ⟨a, _, hwhole⟩ := hirr v hv w hw
  let u := v ++ a ++ w
  have hu : u ∈ language X := hwhole
  have hPv : 0 < P v := hK.cylinder_real_pos hv
  have hPw : 0 < P w := hK.cylinder_real_pos hw
  have hPu : 0 < P u := hK.cylinder_real_pos hu
  have hpref : R u * P v ≤ C * R v * P u := by
    have H := hK.invariant_inter_prefix_cross_bound hG.1 hB hBinv
      (v := v) (w := a ++ w) (by simpa only [List.append_assoc] using hwhole)
    simpa only [u, P, R, C, List.append_assoc] using H
  have hsuff : T u * P w ≤ C * T w * P u := by
    have H := hK.invariant_inter_suffix_cross_bound hG.1 hB.compl hBcinv hwhole
    simpa only [u, P, T, C] using H
  have hvhalf : C * R v < P v / 2 := by
    calc
      C * R v < C * (δ * P v) := mul_lt_mul_of_pos_left hvsmall hC
      _ = P v / 2 := by rw [← mul_assoc, hCδ]; ring
  have hwhalf : C * T w < P w / 2 := by
    calc
      C * T w < C * (δ * P w) := mul_lt_mul_of_pos_left hwsmall hC
      _ = P w / 2 := by rw [← mul_assoc, hCδ]; ring
  have hRu : R u < P u / 2 := by
    have H := hpref.trans_lt (mul_lt_mul_of_pos_right hvhalf hPu)
    nlinarith only [H, hPv]
  have hTu : T u < P u / 2 := by
    have H := hsuff.trans_lt (mul_lt_mul_of_pos_right hwhalf hPu)
    nlinarith only [H, hPw]
  linarith only [hRu, hTu, hparts u]
end IsGibbsMeasure
end BalanceSpecification
