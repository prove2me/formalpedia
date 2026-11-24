-- Prove2me | solution 1 for BalanceSpecification.OneSidedExample.walk_pending_generated
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:48:56.115862+00:00
-- url     : https://prove2.me/submissions/68114ed6-9593-4081-9eb0-3978e9c8bbe9

module
public import Definitions.Def_BalanceSpecificaton_OneSidedGraph
public import Mathlib.Tactic
public import Definitions.Def_BalanceSpecificaton_OneSidedGraphLanguage
public import Theorems.Thm_BalanceSpecification_OneSidedExample_c_mem_code
public import Theorems.Thm_BalanceSpecification_OneSidedExample_length_runWord
public import Theorems.Thm_BalanceSpecification_OneSidedExample_paired_mem_code
public import Theorems.Thm_BalanceSpecification_OneSidedExample_unequal_mem_code
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
theorem _root_.solution (w : Word Alphabet) :
    (Walk (.p 0) w (.p 0) → w ∈ generatedWords code) ∧
    (∀ n : ℕ, Walk (.q n) w (.p 0) →
      List.replicate (n + 1) a ++ w ∈ generatedWords code) ∧
    (∀ d m : ℕ, 0 < d → 1 ≤ m → Walk (.p d) w (.p 0) →
      List.replicate (d + m) a ++ List.replicate m b ++ w ∈ generatedWords code) := by
  induction w with
  | nil =>
    refine ⟨fun _ => nil_mem_generatedWords code, ?_, ?_⟩
    · intro n h
      cases h
    · intro d m hd hm h
      cases h
      omega
  | cons z w ih =>
    obtain ⟨hloop, hq, hp⟩ := ih
    refine ⟨?_, ?_, ?_⟩
    · intro h
      cases h with
      | cons he hw =>
        cases he with
        | pa => simpa only [List.replicate_one, List.singleton_append, Nat.zero_add, List.cons_append, List.nil_append] using hq 0 hw
        | pc =>
          simpa only [List.singleton_append, Nat.zero_add, List.cons_append, List.nil_append] using
            append_mem_generatedWords (mem_generatedWords_of_mem c_mem_code) (hloop hw)
    · intro n h
      cases h with
      | cons he hw =>
        cases he with
        | qa =>
          have H := hq (n + 1) hw
          simpa only [List.replicate_succ', List.append_assoc,
            List.singleton_append, Nat.zero_add, List.cons_append, List.nil_append] using H
        | qb =>
          cases n with
          | zero =>
            have H := append_mem_generatedWords
              (mem_generatedWords_of_mem (paired_mem_code (n := 1) (by omega))) (hloop hw)
            simpa only [List.replicate_one, List.singleton_append, List.append_assoc, Nat.zero_add, List.cons_append, List.nil_append] using H
          | succ n =>
            have H := hp (n + 1) 1 (by omega) (by omega) hw
            simpa only [List.replicate_one, List.append_assoc, List.singleton_append, Nat.zero_add, List.cons_append, List.nil_append] using H
    · intro d m hd hm h
      cases d with
      | zero => omega
      | succ d =>
        cases h with
        | cons he hw =>
          cases he with
          | pc =>
            have H := append_mem_generatedWords
              (mem_generatedWords_of_mem (unequal_mem_code hm
                (show m < d + 1 + m by omega))) (hloop hw)
            simpa only [List.append_assoc, List.singleton_append, Nat.zero_add, List.cons_append, List.nil_append] using H
          | pb =>
            cases d with
            | zero =>
              have H := append_mem_generatedWords
                (mem_generatedWords_of_mem (paired_mem_code (n := m + 1) (by omega)))
                (hloop hw)
              have heq : 0 + 1 + m = m + 1 := by omega
              rw [heq]
              simpa only [List.replicate_succ', List.append_assoc,
                List.singleton_append, Nat.zero_add, List.cons_append, List.nil_append] using H
            | succ d =>
              have H := hp (d + 1) (m + 1) (by omega) (by omega) hw
              have heq : d + 1 + 1 + m = d + 1 + (m + 1) := by omega
              rw [heq]
              simpa only [List.replicate_succ', List.append_assoc,
                List.singleton_append, Nat.zero_add, List.cons_append, List.nil_append] using H
end BalanceSpecification.OneSidedExample
