-- Prove2me | solution 1 for BalanceSpecification.generated_sGap_marker_reverse
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:33:53.342352+00:00
-- url     : https://prove2.me/submissions/d5bd3f01-5417-441f-b4fc-d797143d377d

module
public import Definitions.Def_BalanceSpecificaton_CodedLanguage
public import Definitions.Def_BalanceSpecificaton_Periodicity
public import Definitions.Def_BalanceSpecificaton_SGapBounds
public import Mathlib.Tactic
public import Definitions.Def_BalanceSpecificaton_SGap
public import Theorems.Thm_BalanceSpecification_append_mem_generatedWords
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



set_option autoImplicit true
@[expose] public section
public section
open BalanceSpecification
namespace BalanceSpecification
theorem _root_.solution {S : Set ℕ} {w : Word Bool}
    (hw : w ∈ generatedWords (sGapCode S)) :
    ∃ r ∈ generatedWords (sGapCode S), [true] ++ w.reverse = r ++ [true] := by
  obtain ⟨ws, hws, rfl⟩ := hw
  induction ws with
  | nil => exact ⟨[], nil_mem_generatedWords _, rfl⟩
  | cons w ws ih =>
    obtain ⟨s, hs, hw⟩ := hws w List.mem_cons_self
    obtain ⟨r, hr, heq⟩ := ih (fun v hv => hws v (List.mem_cons_of_mem _ hv))
    refine ⟨r ++ w, append_mem_generatedWords hr
      (mem_generatedWords_of_mem (hws w List.mem_cons_self)), ?_⟩
    calc
      [true] ++ (w :: ws).flatten.reverse = ([true] ++ ws.flatten.reverse) ++ w.reverse := by
        simp only [List.flatten_cons, List.reverse_append, List.append_assoc]
      _ = (r ++ [true]) ++ w.reverse := congrArg (fun t : Word Bool => t ++ w.reverse) heq
      _ = (r ++ w) ++ [true] := by
        rw [hw]
        simp only [List.reverse_cons, List.reverse_replicate, List.append_assoc,
          List.cons_append, List.nil_append]
end BalanceSpecification
