-- Prove2me | solution 1 for BalanceSpecification.nonempty_languageShift_of_words_all_lengths
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:41:30.65033+00:00
-- url     : https://prove2.me/submissions/d05aad47-353a-489a-bc2f-8fd60c4cb9dd

module
public import Definitions.Def_BalanceSpecificaton_Forbidden
public import Definitions.Def_BalanceSpecificaton_Counting
public import Definitions.Def_BalanceSpecificaton_TilingBounds
public import Definitions.Def_BalanceSpecificaton_Entropy
public import Definitions.Def_BalanceSpecificaton_GrowthTiling
public import Mathlib.Analysis.SpecialFunctions.Log.ENNRealLog
public import Mathlib.Topology.Instances.EReal.Lemmas
public import Mathlib.Topology.Compactness.Compact
public import Mathlib.Tactic
public import Definitions.Def_BalanceSpecificaton_FactorialEntropy
public import Theorems.Thm_BalanceSpecification_mem_languageShift_iff
public import Theorems.Thm_BalanceSpecification_mem_languageShift_of_arbitrary_contexts
public import Theorems.Thm_BalanceSpecification_follower_card_reverseLanguage
public import Theorems.Thm_BalanceSpecification_getElem_block
public import Theorems.Thm_BalanceSpecification_length_block
public import Theorems.Thm_BalanceSpecification_mem_allWords
public import Theorems.Thm_BalanceSpecification_mem_followerFinset
public import Theorems.Thm_BalanceSpecification_mem_forbiddenShift_iff
public import Theorems.Thm_BalanceSpecification_mem_predecessorFinset
public import Theorems.Thm_BalanceSpecification_mem_wordFinset
public import Theorems.Thm_BalanceSpecification_nil_mem_language_iff
public import Theorems.Thm_BalanceSpecification_wordCount_reverseLanguage
attribute [local simp] BalanceSpecification.follower_card_reverseLanguage
attribute [local simp] BalanceSpecification.getElem_block
attribute [local simp] BalanceSpecification.length_block
attribute [local simp] BalanceSpecification.mem_allWords
attribute [local simp] BalanceSpecification.mem_followerFinset
attribute [local simp] BalanceSpecification.mem_forbiddenShift_iff
attribute [local simp] BalanceSpecification.mem_predecessorFinset
attribute [local simp] BalanceSpecification.mem_wordFinset
attribute [local simp] BalanceSpecification.wordCount_reverseLanguage


attribute [local simp] BalanceSpecification.mem_languageShift_iff

set_option autoImplicit true
@[expose] public section
public section
noncomputable section
open scoped ENNReal
open BalanceSpecification
variable {A : Type*}
variable [TopologicalSpace A] [DiscreteTopology A]
variable [Fintype A]
namespace BalanceSpecification
theorem _root_.solution [Nonempty A]
    {L : Set (Word A)} (hL : IsFactorial L)
    (hlen : ∀ n : ℕ, ∃ w ∈ L, w.length = n) : (languageShift L).carrier.Nonempty := by
  have hnil : ([] : Word A) ∈ language (languageShift L) := by
    apply mem_languageShift_of_arbitrary_contexts hL
    intro M
    obtain ⟨w, hw, hwlen⟩ := hlen (2 * M)
    refine ⟨w.take M, w.drop M, ?_, ?_, ?_⟩
    · simp only [List.length_take, hwlen]
      omega
    · simp only [List.length_drop, hwlen]
      omega
    · simpa only [List.append_nil, List.take_append_drop] using hw
  exact nil_mem_language_iff.mp hnil
end BalanceSpecification
