-- Prove2me | solution 1 for BalanceSpecification.languageShift_empty_of_missing_length
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:39:57.353421+00:00
-- url     : https://prove2.me/submissions/e6cc599c-22da-4da7-baa1-291e28c62d97

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
public import Theorems.Thm_BalanceSpecification_follower_card_reverseLanguage
public import Theorems.Thm_BalanceSpecification_getElem_block
public import Theorems.Thm_BalanceSpecification_length_block
public import Theorems.Thm_BalanceSpecification_mem_allWords
public import Theorems.Thm_BalanceSpecification_mem_followerFinset
public import Theorems.Thm_BalanceSpecification_mem_forbiddenShift_iff
public import Theorems.Thm_BalanceSpecification_mem_predecessorFinset
public import Theorems.Thm_BalanceSpecification_mem_wordFinset
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
theorem _root_.solution {L : Set (Word A)}
    {n : ℕ} (hn : wordCount L n = 0) : (languageShift L).carrier = ∅ := by
  apply Set.eq_empty_iff_forall_notMem.mpr
  intro x hx
  have hsmall : block x 0 n ∈ wordFinset L n := mem_wordFinset.mpr
    ⟨mem_languageShift_iff.mp hx 0 n, length_block _ _ _⟩
  have hempty : wordFinset L n = ∅ := Finset.card_eq_zero.mp hn
  simp only [hempty, Finset.notMem_empty] at hsmall
end BalanceSpecification
