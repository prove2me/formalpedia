-- Prove2me | solution 1 for BalanceSpecification.first_sGap_generator_unique
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:35:11.445076+00:00
-- url     : https://prove2.me/submissions/28998665-7ee0-499b-b050-5b63b25fb349

module
public import Definitions.Def_BalanceSpecificaton_SGap
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.Group.List.Defs
public import Mathlib.Tactic
public import Definitions.Def_BalanceSpecificaton_SGapRenewal
public import Theorems.Thm_BalanceSpecification_zeros_marker_prefix_ne
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
noncomputable section
open BalanceSpecification
namespace BalanceSpecification
theorem _root_.solution {s t : ℕ} {u v : Word Bool}
    (hu : u = [] ∨ ∃ z, u = true :: z)
    (hv : v = [] ∨ ∃ z, v = true :: z)
    (h : (true :: List.replicate s false) ++ u =
      (true :: List.replicate t false) ++ v) : s = t ∧ u = v := by
  have htail : List.replicate s false ++ u = List.replicate t false ++ v := by
    simpa only [List.cons_append, List.cons.injEq, true_and] using h
  have hst : s = t := by
    rcases lt_trichotomy s t with hlt | heq | hgt
    · exact False.elim (zeros_marker_prefix_ne hlt hu htail)
    · exact heq
    · exact False.elim (zeros_marker_prefix_ne hgt hv htail.symm)
  refine ⟨hst, ?_⟩
  subst t
  exact (List.append_right_inj _).mp htail
end BalanceSpecification
