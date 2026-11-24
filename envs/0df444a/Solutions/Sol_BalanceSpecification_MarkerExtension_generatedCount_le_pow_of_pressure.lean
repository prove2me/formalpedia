-- Prove2me | solution 1 for BalanceSpecification.MarkerExtension.generatedCount_le_pow_of_pressure
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:28:33.568293+00:00
-- url     : https://prove2.me/submissions/bc2accfc-80f8-408f-a4a6-c5f4763a2b91

module
public import Definitions.Def_BalanceSpecificaton_MarkerExtension
public import Definitions.Def_BalanceSpecificaton_RenewalBounds
public import Mathlib.Tactic
public import Definitions.Def_BalanceSpecificaton_MarkedRenewal
public import Theorems.Thm_BalanceSpecification_MarkerExtension_generatedCount_zero
public import Theorems.Thm_BalanceSpecification_MarkerExtension_generatedCount_recurrence_le
public import Theorems.Thm_BalanceSpecification_MarkerEmbedding_block_mapConfiguration
public import Theorems.Thm_BalanceSpecification_follower_card_reverseLanguage
public import Theorems.Thm_BalanceSpecification_getElem_block
public import Theorems.Thm_BalanceSpecification_length_block
public import Theorems.Thm_BalanceSpecification_mem_allWords
public import Theorems.Thm_BalanceSpecification_mem_followerFinset
public import Theorems.Thm_BalanceSpecification_mem_forbiddenShift_iff
public import Theorems.Thm_BalanceSpecification_mem_predecessorFinset
public import Theorems.Thm_BalanceSpecification_mem_shortWords
public import Theorems.Thm_BalanceSpecification_mem_wordFinset
public import Theorems.Thm_BalanceSpecification_nil_mem_generatedWords
public import Theorems.Thm_BalanceSpecification_periodicConfiguration_shift
public import Theorems.Thm_BalanceSpecification_renewal_le_pow_of_pressure_le_one
public import Theorems.Thm_BalanceSpecification_wordCount_reverseLanguage
attribute [local simp] BalanceSpecification.MarkerEmbedding.block_mapConfiguration
attribute [local simp] BalanceSpecification.follower_card_reverseLanguage
attribute [local simp] BalanceSpecification.getElem_block
attribute [local simp] BalanceSpecification.length_block
attribute [local simp] BalanceSpecification.mem_allWords
attribute [local simp] BalanceSpecification.mem_followerFinset
attribute [local simp] BalanceSpecification.mem_forbiddenShift_iff
attribute [local simp] BalanceSpecification.mem_predecessorFinset
attribute [local simp] BalanceSpecification.mem_shortWords
attribute [local simp] BalanceSpecification.mem_wordFinset
attribute [local simp] BalanceSpecification.nil_mem_generatedWords
attribute [local simp] BalanceSpecification.periodicConfiguration_shift
attribute [local simp] BalanceSpecification.wordCount_reverseLanguage



set_option autoImplicit true
@[expose] public section
public section
noncomputable section
open BalanceSpecification BalanceSpecification.MarkerExtension
variable {A : Type*} [Fintype A]
namespace BalanceSpecification.MarkerExtension
theorem _root_.solution (P : Set (Word A)) {ρ : ℝ} (hρ : 0 < ρ)
    (hpressure : ∀ n : ℕ,
      (∑ l ∈ Finset.range (n + 1), (generatorCount P (l + 1) : ℝ) / ρ ^ (l + 1)) ≤ 1)
    (n : ℕ) : (generatedCount P n : ℝ) ≤ ρ ^ n := by
  apply renewal_le_pow_of_pressure_le_one hρ (fun _ => Nat.cast_nonneg _) ?_ ?_ hpressure n
  · simp only [generatedCount_zero, Nat.cast_one, le_refl]
  · intro k
    exact_mod_cast generatedCount_recurrence_le P k
end BalanceSpecification.MarkerExtension
