-- Prove2me | solution 1 for BalanceSpecification.GapRead.exists_small_end
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:33:12.520611+00:00
-- url     : https://prove2.me/submissions/34205631-7f5e-4086-bbc7-2c2176642555

module
public import Definitions.Def_BalanceSpecificaton_CodedLanguage
public import Definitions.Def_BalanceSpecificaton_Periodicity
public import Definitions.Def_BalanceSpecificaton_SGapBounds
public import Mathlib.Tactic
public import Definitions.Def_BalanceSpecificaton_SGap
public import Theorems.Thm_BalanceSpecification_GapRead_replicate_false
public import Theorems.Thm_BalanceSpecification_GapRead_replicate_false_iff
public import Theorems.Thm_BalanceSpecification_eq_replicate_false_of_true_not_mem
public import Theorems.Thm_BalanceSpecification_GapRead_small_end_of_true_mem
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
open BalanceSpecification.GapRead
variable {S : Set ℕ} {N a b : ℕ} {w : Word Bool}
namespace BalanceSpecification.GapRead
theorem _root_.solution
    (hN : ∀ t, GapState S t → ∃ s ∈ S, t ≤ s ∧ s ≤ t + N)
    (h : GapRead S a w b) (ha : GapState S a) :
    ∃ a' b', GapState S a' ∧ GapRead S a' w b' ∧ b' ≤ N := by
  by_cases ht : true ∈ w
  · obtain ⟨b', hb', hread⟩ := small_end_of_true_mem hN h ht
    exact ⟨a, b', ha, hread, hb'⟩
  · have hw := eq_replicate_false_of_true_not_mem ht
    have hreadzeros : GapRead S a (List.replicate w.length false) b := hw ▸ h
    have hlen : a = b + w.length := replicate_false_iff.mp hreadzeros
    obtain ⟨s, hs, has⟩ := ha
    refine ⟨w.length, 0, ⟨s, hs, by omega⟩, ?_, Nat.zero_le _⟩
    have hnew : GapRead S w.length (List.replicate w.length false) 0 := by
      simpa only [Nat.zero_add] using replicate_false (S := S) 0 w.length
    exact (congrArg (fun t : Word Bool => GapRead S w.length t 0) hw).mpr hnew
end BalanceSpecification.GapRead
