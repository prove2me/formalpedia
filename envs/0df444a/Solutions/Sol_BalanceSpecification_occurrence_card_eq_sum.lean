-- Prove2me | solution 1 for BalanceSpecification.occurrence_card_eq_sum
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T01:56:41.467196+00:00
-- url     : https://prove2.me/submissions/21ca3001-4a7f-42e3-ac20-876db90d0966

module
public import Definitions.Def_BalanceSpecificaton_CountBounds
public import Definitions.Def_BalanceSpecificaton_Synchronization
public import Mathlib.Data.Finset.Sigma
public import Mathlib.Tactic
public import Definitions.Def_BalanceSpecificaton_TwoSidedCounts
public import Theorems.Thm_BalanceSpecification_mem_extensionPairs
public import Theorems.Thm_BalanceSpecification_follower_card_reverseLanguage
public import Theorems.Thm_BalanceSpecification_getElem_block
public import Theorems.Thm_BalanceSpecification_length_block
public import Theorems.Thm_BalanceSpecification_mem_allWords
public import Theorems.Thm_BalanceSpecification_mem_followerFinset
public import Theorems.Thm_BalanceSpecification_mem_predecessorFinset
public import Theorems.Thm_BalanceSpecification_mem_wordFinset
public import Theorems.Thm_BalanceSpecification_wordCount_reverseLanguage
attribute [local simp] BalanceSpecification.follower_card_reverseLanguage
attribute [local simp] BalanceSpecification.getElem_block
attribute [local simp] BalanceSpecification.length_block
attribute [local simp] BalanceSpecification.mem_allWords
attribute [local simp] BalanceSpecification.mem_followerFinset
attribute [local simp] BalanceSpecification.mem_predecessorFinset
attribute [local simp] BalanceSpecification.mem_wordFinset
attribute [local simp] BalanceSpecification.wordCount_reverseLanguage


attribute [local simp] BalanceSpecification.mem_extensionPairs

set_option autoImplicit true
@[expose] public section
public section
noncomputable section
open BalanceSpecification
variable {A : Type*} [Fintype A] {L : Set (Word A)}
namespace BalanceSpecification
theorem _root_.solution (u : Word A) (a b : ℕ) :
    (occurrenceFinset L u a b).card =
      ∑ p ∈ predecessorFinset L u a, (followerFinset L (p ++ u) b).card := by
  classical
  have hinj : Set.InjOn (fun ps : (_ : Word A) × Word A => ps.1 ++ u ++ ps.2)
      (extensionPairs L u a b : Set _) := by
    intro ps hps qt hqt heq
    obtain ⟨hp, hs⟩ := mem_extensionPairs.mp hps
    obtain ⟨hq, ht⟩ := mem_extensionPairs.mp hqt
    have hpa := (mem_predecessorFinset.mp hp).2.1
    have hqa := (mem_predecessorFinset.mp hq).2.1
    have hprefix := congrArg (List.take a) heq
    have hsuffix := congrArg (List.drop (a + u.length)) heq
    have htakep : (ps.1 ++ u ++ ps.2).take a = ps.1 := by
      rw [← hpa, List.append_assoc, List.take_left]
    have htakeq : (qt.1 ++ u ++ qt.2).take a = qt.1 := by
      rw [← hqa, List.append_assoc, List.take_left]
    have hpq : ps.1 = qt.1 := htakep.symm.trans (hprefix.trans htakeq)
    have hdropp : (ps.1 ++ u ++ ps.2).drop (a + u.length) = ps.2 := by
      rw [← hpa, ← List.length_append, List.drop_left]
    have hdropq : (qt.1 ++ u ++ qt.2).drop (a + u.length) = qt.2 := by
      rw [← hqa, ← List.length_append, List.drop_left]
    have hst : ps.2 = qt.2 := hdropp.symm.trans (hsuffix.trans hdropq)
    exact Sigma.ext hpq (heq_of_eq hst)
  rw [occurrenceFinset, Finset.card_image_iff.mpr hinj]
  exact Finset.card_sigma _ _
end BalanceSpecification
