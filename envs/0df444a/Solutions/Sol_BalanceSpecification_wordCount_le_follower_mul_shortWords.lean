-- Prove2me | solution 1 for BalanceSpecification.wordCount_le_follower_mul_shortWords
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:17:05.369677+00:00
-- url     : https://prove2.me/submissions/feca1277-ed0a-493a-8fcb-4316f469069c

module
public import Definitions.Def_BalanceSpecificaton_CountBounds
public import Definitions.Def_BalanceSpecificaton_LanguageProperties
public import Mathlib.Tactic
public import Definitions.Def_BalanceSpecificaton_Specification
public import Theorems.Thm_BalanceSpecification_mem_shortWords
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


attribute [local simp] BalanceSpecification.mem_shortWords

set_option autoImplicit true
@[expose] public section
public section
noncomputable section
open BalanceSpecification
variable {A : Type*} [Fintype A] {L : Set (Word A)}
namespace BalanceSpecification
theorem _root_.solution (hL : IsFactorial L)
    {N : ℕ} {u : Word A}
    (hbridge : ∀ v ∈ L, ∃ w : Word A, w.length ≤ N ∧ u ++ w ++ v ∈ L)
    (n : ℕ) :
    wordCount L n ≤ (followerFinset L u n).card * (shortWords (A := A) N).card := by
  classical
  rw [wordCount, ← Finset.card_product]
  apply Finset.card_le_card_of_surjOn
    (fun p : Word A × Word A => (p.1 ++ p.2).drop p.2.length)
  intro v hv
  obtain ⟨hvL, hvlen⟩ := mem_wordFinset.mp hv
  obtain ⟨w, hwN, huw⟩ := hbridge v hvL
  let z := w ++ v
  have hzL : z ∈ L := by
    apply hL (u := z) (v := u ++ z) _ (by simpa only [z, List.append_assoc] using huw)
    exact ⟨u, [], by simp only [List.append_nil]⟩
  have hzlen : n ≤ z.length := by simp only [z, List.length_append, hvlen]; omega
  have htake : (z.take n).length = n := by
    simpa only [List.length_take] using Nat.min_eq_left hzlen
  have htail : (z.drop n).length = w.length := by
    simp only [List.length_drop, z, List.length_append, hvlen]
    omega
  refine ⟨(z.take n, z.drop n), Finset.mem_product.mpr ⟨?_, ?_⟩, ?_⟩
  · apply mem_followerFinset.mpr
    refine ⟨hL (List.take_prefix n z).isInfix hzL, htake, ?_⟩
    apply hL (u := u ++ z.take n) (v := u ++ z) _
      (by simpa only [z, List.append_assoc] using huw)
    exact ⟨[], z.drop n, by simp only [List.nil_append, List.append_assoc,
      List.take_append_drop]⟩
  · exact mem_shortWords.mpr (htail.trans_le hwN)
  · change (z.take n ++ z.drop n).drop (z.drop n).length = v
    rw [List.take_append_drop, htail]
    exact List.drop_left
end BalanceSpecification
