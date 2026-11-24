-- Prove2me | solution 1 for BalanceSpecification.GapRead.decompose_markers
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:36:00.628258+00:00
-- url     : https://prove2.me/submissions/5617a9ed-c875-4241-92a8-3986c9b004f6

module
public import Definitions.Def_BalanceSpecificaton_SGap
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.Group.List.Defs
public import Mathlib.Tactic
public import Definitions.Def_BalanceSpecificaton_SGapRenewal
public import Theorems.Thm_BalanceSpecification_sGapListConcat_nil
public import Theorems.Thm_BalanceSpecification_sGapListConcat_cons
public import Theorems.Thm_BalanceSpecification_mem_renewalFinset
public import Theorems.Thm_BalanceSpecification_renewalCount_zero
public import Theorems.Thm_BalanceSpecification_mem_renewalGaps
public import Theorems.Thm_BalanceSpecification_append_mem_generatedWords
public import Theorems.Thm_BalanceSpecification_eq_replicate_false_of_true_not_mem
public import Theorems.Thm_BalanceSpecification_follower_card_reverseLanguage
public import Theorems.Thm_BalanceSpecification_getElem_block
public import Theorems.Thm_BalanceSpecification_length_block
public import Theorems.Thm_BalanceSpecification_mem_allWords
public import Theorems.Thm_BalanceSpecification_mem_followerFinset
public import Theorems.Thm_BalanceSpecification_mem_forbiddenShift_iff
public import Theorems.Thm_BalanceSpecification_mem_generatedWords_of_mem
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


attribute [local simp] BalanceSpecification.sGapListConcat_nil
attribute [local simp] BalanceSpecification.sGapListConcat_cons
attribute [local simp] BalanceSpecification.mem_renewalFinset
attribute [local simp] BalanceSpecification.renewalCount_zero
attribute [local simp] BalanceSpecification.mem_renewalGaps

set_option autoImplicit true
@[expose] public section
public section
noncomputable section
open BalanceSpecification
namespace BalanceSpecification
namespace GapRead
theorem _root_.solution {S : Set ℕ} {a b : ℕ} {w : Word Bool}
    (h : GapRead S a w b) (ht : true ∈ w) :
    ∃ v : Word Bool, ∃ m : ℕ, v ∈ generatedWords (sGapCode S) ∧
      w = List.replicate a false ++ v ++ true :: List.replicate m false := by
  induction h with
  | nil => exact False.elim (List.not_mem_nil ht)
  | @zero i j w h ih =>
    have ht' : true ∈ w := by
      obtain heq | hmem := List.mem_cons.mp ht
      · cases heq
      · exact hmem
    obtain ⟨v, m, hv, heq⟩ := ih ht'
    refine ⟨v, m, hv, ?_⟩
    simpa only [List.replicate_succ, List.cons_append] using congrArg (List.cons false) heq
  | @one s j w hs h ih =>
    by_cases htrue : true ∈ w
    · obtain ⟨v, m, hv, heq⟩ := ih htrue
      refine ⟨(true :: List.replicate s false) ++ v, m,
        append_mem_generatedWords (mem_generatedWords_of_mem ⟨s, hs, rfl⟩) hv, ?_⟩
      simpa only [List.replicate_zero, List.nil_append, List.cons_append,
        List.append_assoc] using congrArg (List.cons true) heq
    · refine ⟨[], w.length, nil_mem_generatedWords _, ?_⟩
      have hw := eq_replicate_false_of_true_not_mem htrue
      simpa only [List.replicate_zero, List.nil_append] using congrArg (List.cons true) hw
end GapRead
end BalanceSpecification
