-- Prove2me | solution 1 for BalanceSpecification.sGap_partial_pressure_le_one_of_entropy_lt
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:38:02.149099+00:00
-- url     : https://prove2.me/submissions/bb369856-8de9-4e52-ab92-8e4274be1cd3

module
public import Definitions.Def_BalanceSpecificaton_SGapRenewal
public import Definitions.Def_BalanceSpecificaton_GrowthUpperBounds
public import Mathlib.Analysis.SpecificLimits.Normed
public import Mathlib.Topology.Algebra.InfiniteSum.Real
public import Mathlib.Tactic
public import Definitions.Def_BalanceSpecificaton_SGapEntropy
public import Theorems.Thm_BalanceSpecification_finite_code_pressure_le_one_of_growth_bound
public import Theorems.Thm_BalanceSpecification_exists_wordCount_exp_bound_of_entropy_lt_log
public import Theorems.Thm_BalanceSpecification_follower_card_reverseLanguage
public import Theorems.Thm_BalanceSpecification_getElem_block
public import Theorems.Thm_BalanceSpecification_length_block
public import Theorems.Thm_BalanceSpecification_mem_allWords
public import Theorems.Thm_BalanceSpecification_mem_followerFinset
public import Theorems.Thm_BalanceSpecification_mem_forbiddenShift_iff
public import Theorems.Thm_BalanceSpecification_mem_language_codedShift_of_mem_generatedWords
public import Theorems.Thm_BalanceSpecification_mem_predecessorFinset
public import Theorems.Thm_BalanceSpecification_mem_renewalFinset
public import Theorems.Thm_BalanceSpecification_mem_renewalGaps
public import Theorems.Thm_BalanceSpecification_mem_shortWords
public import Theorems.Thm_BalanceSpecification_mem_wordFinset
public import Theorems.Thm_BalanceSpecification_nil_mem_generatedWords
public import Theorems.Thm_BalanceSpecification_periodicConfiguration_shift
public import Theorems.Thm_BalanceSpecification_renewalCount_zero
public import Theorems.Thm_BalanceSpecification_sGapCode_has_nonempty_word
public import Theorems.Thm_BalanceSpecification_sGapConcat_injective
public import Theorems.Thm_BalanceSpecification_sGapConcat_mem_generatedWords
public import Theorems.Thm_BalanceSpecification_sGapListConcat_cons
public import Theorems.Thm_BalanceSpecification_sGapListConcat_nil
public import Theorems.Thm_BalanceSpecification_sGapShift_nonempty
public import Theorems.Thm_BalanceSpecification_wordCount_reverseLanguage
attribute [local simp] BalanceSpecification.follower_card_reverseLanguage
attribute [local simp] BalanceSpecification.getElem_block
attribute [local simp] BalanceSpecification.length_block
attribute [local simp] BalanceSpecification.mem_allWords
attribute [local simp] BalanceSpecification.mem_followerFinset
attribute [local simp] BalanceSpecification.mem_forbiddenShift_iff
attribute [local simp] BalanceSpecification.mem_predecessorFinset
attribute [local simp] BalanceSpecification.mem_renewalFinset
attribute [local simp] BalanceSpecification.mem_renewalGaps
attribute [local simp] BalanceSpecification.mem_shortWords
attribute [local simp] BalanceSpecification.mem_wordFinset
attribute [local simp] BalanceSpecification.nil_mem_generatedWords
attribute [local simp] BalanceSpecification.periodicConfiguration_shift
attribute [local simp] BalanceSpecification.renewalCount_zero
attribute [local simp] BalanceSpecification.sGapListConcat_cons
attribute [local simp] BalanceSpecification.sGapListConcat_nil
attribute [local simp] BalanceSpecification.wordCount_reverseLanguage



set_option autoImplicit true
@[expose] public section
public section
noncomputable section
open BalanceSpecification
open Filter Set
open scoped Topology
namespace BalanceSpecification
theorem _root_.solution
    [TopologicalSpace Bool] [DiscreteTopology Bool] {S : Set ℕ} (hS : S.Nonempty)
    {γ : ℝ} (hγ : 0 < γ)
    (hgap : entropy (sGapShift S) (sGapShift_nonempty hS) < Real.log γ)
    (F : Finset ℕ) (hF : ∀ s ∈ F, s ∈ S) :
    ∑ s ∈ F, (γ⁻¹)^(s + 1) ≤ 1 := by
  classical
  obtain ⟨C, hC, hcounts⟩ := exists_wordCount_exp_bound_of_entropy_lt_log
    (sGapShift_nonempty hS) hγ hgap
  have hinj (r : ℕ) : Function.Injective (fun f : Fin r → ↥F =>
      (List.ofFn (fun i => true :: List.replicate (f i).val false)).flatten) := by
    intro f g h
    have h' : sGapConcat (fun i => (f i).val) = sGapConcat (fun i => (g i).val) := by
      simpa only [sGapConcat, sGapListConcat, List.map_ofFn, Function.comp_def] using h
    have heq := sGapConcat_injective h'
    funext i
    exact Subtype.ext (congrFun heq i)
  have hmem (r : ℕ) (f : Fin r → ↥F) :
      (List.ofFn (fun i => true :: List.replicate (f i).val false)).flatten ∈
        language (sGapShift S) := by
    apply mem_language_codedShift_of_mem_generatedWords (sGapCode_has_nonempty_word hS)
    have hh := sGapConcat_mem_generatedWords (fun i => hF (f i).val (f i).property)
    simpa only [sGapConcat, sGapListConcat, List.map_ofFn, Function.comp_def] using hh
  have h := finite_code_pressure_le_one_of_growth_bound
    (X := sGapShift S) (fun s : ↥F => true :: List.replicate s.val false) hγ hC hcounts hinj hmem
  simp only [List.length_cons, List.length_replicate] at h
  rwa [Finset.sum_coe_sort F (fun s => (γ⁻¹)^(s + 1))] at h
end BalanceSpecification
