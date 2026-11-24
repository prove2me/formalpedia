-- Prove2me | solution 1 for BalanceSpecification.sGap_follower_eq_replicate_of_successive_gap
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:35:04.484289+00:00
-- url     : https://prove2.me/submissions/aa9f4ded-61ad-4b40-886e-e1a853a46a2b

module
public import Definitions.Def_BalanceSpecificaton_CodedLanguage
public import Definitions.Def_BalanceSpecificaton_Periodicity
public import Definitions.Def_BalanceSpecificaton_SGapBounds
public import Mathlib.Tactic
public import Definitions.Def_BalanceSpecificaton_SGap
public import Theorems.Thm_BalanceSpecification_GapRead_split
public import Theorems.Thm_BalanceSpecification_GapRead_replicate_false_iff
public import Theorems.Thm_BalanceSpecification_mem_language_sGapShift_iff
public import Theorems.Thm_BalanceSpecification_GapRead_eq_replicate_false_of_length_le
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
public import Theorems.Thm_BalanceSpecification_wordCount_reverseLanguage
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
open BalanceSpecification
namespace BalanceSpecification
theorem _root_.solution
    [TopologicalSpace Bool] [DiscreteTopology Bool] {S : Set ℕ} (hS : S.Nonempty)
    {a b k : ℕ} (hnext : ∀ s ∈ S, a < s → b ≤ s) (hgap : a + k < b)
    {w : Word Bool}
    (hw : (true :: List.replicate (a + 1) false) ++ w ∈ language (sGapShift S))
    (hlen : w.length = k) : w = List.replicate k false := by
  obtain ⟨i, j, _, hread⟩ := (mem_language_sGapShift_iff hS).mp hw
  cases hread with
  | one hs htail =>
    obtain ⟨r, hzeros, hwRead⟩ := GapRead.split htail
    have hstate := GapRead.replicate_false_iff.mp hzeros
    have hbs := hnext _ hs (by omega)
    have hlenr : w.length ≤ r := by omega
    simpa only [hlen] using hwRead.eq_replicate_false_of_length_le hlenr
end BalanceSpecification
