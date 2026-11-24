-- Prove2me | solution 1 for BalanceSpecification.mem_language_sGapShift_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:33:55.045112+00:00
-- url     : https://prove2.me/submissions/f7c2e677-d18a-456c-9dde-84b04955ca8f

module
public import Definitions.Def_BalanceSpecificaton_CodedLanguage
public import Definitions.Def_BalanceSpecificaton_Periodicity
public import Definitions.Def_BalanceSpecificaton_SGapBounds
public import Mathlib.Tactic
public import Definitions.Def_BalanceSpecificaton_SGap
public import Theorems.Thm_BalanceSpecification_GapRead_append
public import Theorems.Thm_BalanceSpecification_GapRead_split
public import Theorems.Thm_BalanceSpecification_GapRead_replicate_false
public import Theorems.Thm_BalanceSpecification_GapRead_gapState_end
public import Theorems.Thm_BalanceSpecification_GapRead_of_generatedWords
public import Theorems.Thm_BalanceSpecification_GapRead_mem_generatedWords
public import Theorems.Thm_BalanceSpecification_sGapCode_has_nonempty_word
public import Theorems.Thm_BalanceSpecification_follower_card_reverseLanguage
public import Theorems.Thm_BalanceSpecification_getElem_block
public import Theorems.Thm_BalanceSpecification_language_codedShift_infix_generatedWords
public import Theorems.Thm_BalanceSpecification_length_block
public import Theorems.Thm_BalanceSpecification_mem_allWords
public import Theorems.Thm_BalanceSpecification_mem_followerFinset
public import Theorems.Thm_BalanceSpecification_mem_forbiddenShift_iff
public import Theorems.Thm_BalanceSpecification_mem_language_codedShift_iff
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
theorem _root_.solution [TopologicalSpace Bool] [DiscreteTopology Bool]
    {S : Set ℕ} (hS : S.Nonempty) {w : Word Bool} :
    w ∈ language (sGapShift S) ↔ ∃ a b, GapState S a ∧ GapRead S a w b := by
  constructor
  · intro hw
    obtain ⟨v, hv, ⟨p, q, rfl⟩⟩ := language_codedShift_infix_generatedWords hw
    have hread := GapRead.of_generatedWords hv
    rw [List.append_assoc] at hread
    obtain ⟨a, hp, htail⟩ := GapRead.split (u := p) hread
    obtain ⟨b, hw, _⟩ := htail.split
    refine ⟨a, b, hp.gapState_end ?_, hw⟩
    obtain ⟨s, hs⟩ := hS
    exact ⟨s, hs, Nat.zero_le s⟩
  · rintro ⟨a, b, ⟨s, hs, has⟩, hw⟩
    have hprefix : GapRead S 0 (true :: List.replicate (s - a) false) a := by
      apply GapRead.one hs
      simpa only [Nat.add_sub_of_le has] using GapRead.replicate_false (S := S) a (s - a)
    have hsuffix : GapRead S b (List.replicate b false) 0 := by
      simpa only [Nat.zero_add] using GapRead.replicate_false (S := S) 0 b
    apply (mem_language_codedShift_iff (sGapCode_has_nonempty_word hS)).mpr
    refine ⟨(true :: List.replicate (s - a) false) ++ w ++ List.replicate b false,
      (hprefix.append hw |>.append hsuffix).mem_generatedWords, ?_⟩
    exact ⟨true :: List.replicate (s - a) false, List.replicate b false, rfl⟩
end BalanceSpecification
