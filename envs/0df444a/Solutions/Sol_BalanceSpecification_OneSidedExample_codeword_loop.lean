-- Prove2me | solution 1 for BalanceSpecification.OneSidedExample.codeword_loop
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:49:16.301162+00:00
-- url     : https://prove2.me/submissions/30f592ea-8380-4ca3-8b76-041c214eaf95

module
public import Definitions.Def_BalanceSpecificaton_OneSidedGraph
public import Mathlib.Tactic
public import Definitions.Def_BalanceSpecificaton_OneSidedGraphLanguage
public import Theorems.Thm_BalanceSpecification_OneSidedExample_ascending_from_base_walk
public import Theorems.Thm_BalanceSpecification_OneSidedExample_descending_q_walk
public import Theorems.Thm_BalanceSpecification_OneSidedExample_Walk_append
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
open BalanceSpecification BalanceSpecification.OneSidedExample
namespace BalanceSpecification.OneSidedExample
theorem _root_.solution {w : Word Alphabet} (hw : w ∈ code) : Walk (.p 0) w (.p 0) := by
  rcases hw with rfl | ⟨n, hn, rfl⟩ | ⟨l, m, hm, hlm, rfl⟩
  · exact Walk.cons (.pc 0) (.nil _)
  · have hn0 : n ≠ 0 := by omega
    obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn0
    exact (ascending_from_base_walk k).append (by
      simpa only [Nat.zero_add] using descending_q_walk 0 k)
  · let d := l - m
    let k := m - 1
    have hlenl : d + k + 1 = l := by dsimp only [d, k]; omega
    have hlenm : k + 1 = m := by dsimp only [k]; omega
    have H := ((ascending_from_base_walk (d + k)).append
      (descending_q_walk d k)).append (Walk.cons (.pc d) (.nil _))
    simpa only [hlenl, hlenm] using H
end BalanceSpecification.OneSidedExample
