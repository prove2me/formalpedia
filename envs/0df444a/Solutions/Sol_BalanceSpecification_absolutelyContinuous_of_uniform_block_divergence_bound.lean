-- Prove2me | solution 1 for BalanceSpecification.absolutelyContinuous_of_uniform_block_divergence_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T03:15:30.459045+00:00
-- url     : https://prove2.me/submissions/ada18a44-d627-42be-a71e-9c4af891a176

module
public import Definitions.Def_BalanceSpecificaton_EntropyAlgebra
public import Definitions.Def_BalanceSpecificaton_CylinderAlgebra
public import Definitions.Def_BalanceSpecificaton_BlockEntropy
public import Mathlib.Tactic
public import Definitions.Def_BalanceSpecificaton_AbsoluteContinuity
public import Theorems.Thm_BalanceSpecification_cylinderUnion_log_inverse_le_of_divergence_bound
public import Theorems.Thm_BalanceSpecification_FiniteEntropy_divergence_nonneg
public import Theorems.Thm_BalanceSpecification_GibbsBounds_cylinder_real_pos
public import Theorems.Thm_BalanceSpecification_IsGibbsMeasure_cylinder_real_pos
public import Theorems.Thm_BalanceSpecification_cylinder_nil
public import Theorems.Thm_BalanceSpecification_exists_centered_cylinder_approximation_real
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
open BalanceSpecification
open MeasureTheory Set Filter
open scoped Topology symmDiff
variable {A : Type*} [Fintype A] [TopologicalSpace A] [DiscreteTopology A]
  [MeasurableSpace A] [BorelSpace A] {X : ShiftSpace A}
namespace BalanceSpecification
theorem _root_.solution
    {hX : X.carrier.Nonempty} {μ ν : ProbabilityMeasure X.carrier}
    (hG : IsGibbsMeasure hX μ) (hν : IsInvariant ν) {C : ℝ}
    (hD : ∀ n : ℕ, FiniteEntropy.divergence
      (blockDistribution ν (2 * n + 1)) (blockDistribution μ (2 * n + 1)) ≤ C) :
    (ν : Measure X.carrier) ≪ (μ : Measure X.carrier) := by
  have hC : 0 ≤ C := by
    have H := FiniteEntropy.divergence_nonneg
      (p := blockDistribution ν 1) (q := blockDistribution μ 1)
      (fun _ => measureReal_nonneg) (fun _ => measureReal_nonneg)
      (blockDistribution_sum ν 1) (blockDistribution_sum μ 1)
      (fun w _ => hG.cylinder_real_pos (mem_wordFinset.mp w.property).1 0)
    exact H.trans (by simpa only [Nat.mul_zero, zero_add] using hD 0)
  apply Measure.AbsolutelyContinuous.mk
  intro E hE hμE
  apply (measureReal_eq_zero_iff (μ := (ν : Measure X.carrier))).mp
  by_contra hνE
  let δ := (ν : Measure X.carrier).real E
  have hδ : 0 < δ := lt_of_le_of_ne measureReal_nonneg (Ne.symm hνE)
  have hlog2 : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  let T : ℝ := 2 * (C + Real.log 2 + 1) / δ
  have hT : 0 < T := div_pos (by linarith only [hC, hlog2]) hδ
  let ε : ℝ := min (δ / 4) (Real.exp (-T) / 2)
  have hε : 0 < ε := lt_min (div_pos hδ (by norm_num))
    (div_pos (Real.exp_pos _) (by norm_num))
  obtain ⟨n, S, hS, happ⟩ := exists_centered_cylinder_approximation_real
    ((μ : Measure X.carrier) + (ν : Measure X.carrier)) hE hε
  let B : Set X.carrier := ⋃ w ∈ S, cylinder X w (-(n : ℤ))
  have happ' : (μ : Measure X.carrier).real (E ∆ B) +
      (ν : Measure X.carrier).real (E ∆ B) < ε := by
    have H := measureReal_add_apply
      (μ₁ := (μ : Measure X.carrier)) (μ₂ := (ν : Measure X.carrier)) (s := E ∆ B)
    rw [← H]
    exact happ
  have hμdiff : (μ : Measure X.carrier).real (E ∆ B) < ε := by
    linarith only [happ', (measureReal_nonneg : 0 ≤ (ν : Measure X.carrier).real (E ∆ B))]
  have hνdiff : (ν : Measure X.carrier).real (E ∆ B) < ε := by
    linarith only [happ', (measureReal_nonneg : 0 ≤ (μ : Measure X.carrier).real (E ∆ B))]
  have hBsub : B ⊆ E ∪ (E ∆ B) := by
    intro x hx
    by_cases hxE : x ∈ E
    · exact Or.inl hxE
    · exact Or.inr (Or.inr ⟨hx, hxE⟩)
  have hEsub : E ⊆ B ∪ (E ∆ B) := by
    intro x hx
    by_cases hxB : x ∈ B
    · exact Or.inl hxB
    · exact Or.inr (Or.inl ⟨hx, hxB⟩)
  have hμB : (μ : Measure X.carrier).real B < ε := by
    have H := (measureReal_mono (μ := (μ : Measure X.carrier)) hBsub).trans
      (measureReal_union_le E (E ∆ B))
    have hz : (μ : Measure X.carrier).real E = 0 := by
      simp only [measureReal_def, hμE, ENNReal.toReal_zero]
    linarith only [H, hz, hμdiff]
  have hνB : δ / 2 ≤ (ν : Measure X.carrier).real B := by
    have H := (measureReal_mono (μ := (ν : Measure X.carrier)) hEsub).trans
      (measureReal_union_le B (E ∆ B))
    have hεle : ε ≤ δ / 4 := min_le_left _ _
    change δ ≤ _ at H
    linarith only [H, hνdiff, hεle, hδ]
  have hνBpos : 0 < (ν : Measure X.carrier).real B :=
    (div_pos hδ (by norm_num)).trans_le hνB
  have hμBpos : 0 < (μ : Measure X.carrier).real B := by
    have hBne : B.Nonempty := by
      by_contra h
      have hz : B = ∅ := Set.not_nonempty_iff_eq_empty.mp h
      rw [hz, measureReal_empty] at hνBpos
      exact lt_irrefl _ hνBpos
    obtain ⟨x, hx⟩ := hBne
    obtain ⟨w, hw, hxw⟩ := Set.mem_iUnion₂.mp hx
    have hsub : cylinder X w (-(n : ℤ)) ⊆ B := by
      intro y hy
      exact Set.mem_iUnion₂.mpr ⟨w, hw, hy⟩
    exact (hG.cylinder_real_pos (hS w hw).1 _).trans_le (measureReal_mono (μ := (μ : Measure X.carrier)) hsub
      (measure_ne_top (μ : Measure X.carrier) B))
  have hμBexp : (μ : Measure X.carrier).real B < Real.exp (-T) := by
    have hεle : ε ≤ Real.exp (-T) / 2 := min_le_right _ _
    linarith only [hμB, hεle, Real.exp_pos (-T)]
  have hlogB : T < Real.log (1 / (μ : Measure X.carrier).real B) := by
    have H := Real.log_lt_log hμBpos hμBexp
    rw [Real.log_exp] at H
    simp only [one_div, Real.log_inv]
    linarith only [H]
  have hbound := cylinderUnion_log_inverse_le_of_divergence_bound hG hν hD n S hS hμBpos
  change (ν : Measure X.carrier).real B * Real.log (1 / (μ : Measure X.carrier).real B) ≤ _ at hbound
  have H1 := mul_le_mul_of_nonneg_right hνB hT.le
  have H2 := mul_lt_mul_of_pos_left hlogB hνBpos
  have HT : (δ / 2) * T = C + Real.log 2 + 1 := by
    dsimp only [T]
    field_simp
  linarith only [hbound, H1, H2, HT]
end BalanceSpecification
