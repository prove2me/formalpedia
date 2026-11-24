-- Prove2me | solution 1 for BalanceSpecification.mem_occurrenceFinset_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:27:11.530436+00:00
-- url     : https://prove2.me/submissions/95bd0da5-6ae1-4fe3-b76f-d76374cd280f

module
public import Definitions.Def_BalanceSpecificaton_CountBounds
public import Definitions.Def_BalanceSpecificaton_Synchronization
public import Mathlib.Data.Finset.Sigma
public import Mathlib.Tactic
public import Definitions.Def_BalanceSpecificaton_TwoSidedCounts
public import Theorems.Thm_BalanceSpecification_mem_extensionPairs
public import Theorems.Thm_BalanceSpecification_IsFactorial_prefix
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
theorem _root_.solution (hL : IsFactorial L) {u w : Word A} {a b : ℕ} :
    w ∈ occurrenceFinset L u a b ↔
      w ∈ L ∧ w.length = a + u.length + b ∧ (w.drop a).take u.length = u := by
  classical
  constructor
  · intro hw
    obtain ⟨ps, hps, rfl⟩ := Finset.mem_image.mp hw
    obtain ⟨hp, hs⟩ := mem_extensionPairs.mp hps
    obtain ⟨_, hplen, _⟩ := mem_predecessorFinset.mp hp
    obtain ⟨_, hslen, hword⟩ := mem_followerFinset.mp hs
    refine ⟨hword, by simp only [List.length_append, hplen, hslen], ?_⟩
    simp only [List.append_assoc, ← hplen, List.drop_left, List.take_left]
  · rintro ⟨hwL, hwlen, hmid⟩
    let p := w.take a
    let s := w.drop (a + u.length)
    have hplen : p.length = a := by
      simp only [p, List.length_take, hwlen]
      omega
    have hslen : s.length = b := by
      simp only [s, List.length_drop, hwlen]
      omega
    have hword : p ++ u ++ s = w := by
      rw [← hmid]
      simp only [p, s, List.append_assoc, ← List.drop_drop,
        List.take_append_drop]
    refine Finset.mem_image.mpr ⟨⟨p, s⟩, mem_extensionPairs.mpr ⟨?_, ?_⟩, hword⟩
    · refine mem_predecessorFinset.mpr ⟨?_, hplen, ?_⟩
      · exact hL (List.take_prefix a w).isInfix hwL
      · apply hL.prefix (v := s)
        simpa only [hword] using hwL
    · refine mem_followerFinset.mpr ⟨?_, hslen, ?_⟩
      · exact hL (List.drop_suffix (a + u.length) w).isInfix hwL
      · simpa only [hword] using hwL
end BalanceSpecification
