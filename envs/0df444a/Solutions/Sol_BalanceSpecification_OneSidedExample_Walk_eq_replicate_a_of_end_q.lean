-- Prove2me | solution 1 for BalanceSpecification.OneSidedExample.Walk.eq_replicate_a_of_end_q
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:49:42.08431+00:00
-- url     : https://prove2.me/submissions/a34c9666-7238-4710-8717-796c61ee7a5d

module
public import Definitions.Def_BalanceSpecificaton_OneSidedGraphLanguage
public import Definitions.Def_BalanceSpecificaton_CountBounds
public import Definitions.Def_BalanceSpecificaton_Entropy
public import Mathlib.Data.List.Induction
public import Mathlib.Tactic
public import Definitions.Def_BalanceSpecificaton_OneSidedBounds
public import Theorems.Thm_BalanceSpecification_OneSidedExample_Walk_split
public import Theorems.Thm_BalanceSpecification_OneSidedExample_length_runWord
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
attribute [local simp] BalanceSpecification.OneSidedExample.length_runWord
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
open Filter
open scoped Topology
open BalanceSpecification BalanceSpecification.OneSidedExample
namespace BalanceSpecification.OneSidedExample
namespace Walk
theorem _root_.solution {s : Vertex} {k : ℕ} {w : Word Alphabet}
    (h : Walk s w (.q k)) (hlen : w.length ≤ k + 1) :
    w = List.replicate w.length a := by
  induction w using List.reverseRecOn generalizing s k with
  | nil => rfl
  | append_singleton w d ih =>
    obtain ⟨t, hw, hd⟩ := h.split
    cases hd with
    | cons he hend =>
      cases hend
      cases he with
      | qa j =>
        have hlen' : w.length ≤ j + 1 := by
          simp only [List.length_append, List.length_singleton] at hlen
          omega
        rw [ih hw hlen', List.length_append, List.length_replicate,
          List.length_singleton, List.replicate_succ']
      | pa =>
        have hwlen : w.length = 0 := by
          simp only [List.length_append, List.length_singleton] at hlen
          omega
        have hwzero := List.length_eq_zero_iff.mp hwlen
        simp only [hwzero, List.nil_append, List.length_singleton,
          List.replicate_one]
end Walk
end BalanceSpecification.OneSidedExample
