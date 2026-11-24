-- Prove2me | solution 1 for BalanceSpecification.FiveSymbol.four_mul_wordCount_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:47:05.433352+00:00
-- url     : https://prove2.me/submissions/37bcdf11-fe17-4e6a-87ea-fb9674e1629d

module
public import Definitions.Def_BalanceSpecificaton_FiveSymbol
public import Definitions.Def_BalanceSpecificaton_CountBounds
public import Mathlib.Tactic
public import Definitions.Def_BalanceSpecificaton_FiveSymbolBalance
public import Theorems.Thm_BalanceSpecification_FiveSymbol_append_mem_language
public import Theorems.Thm_BalanceSpecification_follower_card_reverseLanguage
public import Theorems.Thm_BalanceSpecification_getElem_block
public import Theorems.Thm_BalanceSpecification_length_block
public import Theorems.Thm_BalanceSpecification_mem_allWords
public import Theorems.Thm_BalanceSpecification_mem_followerFinset
public import Theorems.Thm_BalanceSpecification_mem_forbiddenShift_iff
public import Theorems.Thm_BalanceSpecification_mem_predecessorFinset
public import Theorems.Thm_BalanceSpecification_mem_wordFinset
public import Theorems.Thm_BalanceSpecification_shortlexWord_zero
public import Theorems.Thm_BalanceSpecification_wordCount_reverseLanguage
attribute [local simp] BalanceSpecification.follower_card_reverseLanguage
attribute [local simp] BalanceSpecification.getElem_block
attribute [local simp] BalanceSpecification.length_block
attribute [local simp] BalanceSpecification.mem_allWords
attribute [local simp] BalanceSpecification.mem_followerFinset
attribute [local simp] BalanceSpecification.mem_forbiddenShift_iff
attribute [local simp] BalanceSpecification.mem_predecessorFinset
attribute [local simp] BalanceSpecification.mem_wordFinset
attribute [local simp] BalanceSpecification.shortlexWord_zero
attribute [local simp] BalanceSpecification.wordCount_reverseLanguage



set_option autoImplicit true
@[expose] public section
public section
noncomputable section
open BalanceSpecification BalanceSpecification.FiveSymbol
namespace BalanceSpecification.FiveSymbol
theorem _root_.solution (n : ℕ) :
    4 * wordCount (language shift) n ≤ wordCount (language shift) (n + 1) := by
  classical
  let Q : Finset Alphabet := {0, 1, 2, 3}
  have hQcard : Q.card = 4 := by decide
  have hQ : ∀ a ∈ Q, a ≠ (4 : Alphabet) := by decide
  have H : ((wordFinset (language shift) n) ×ˢ Q).card ≤
      (wordFinset (language shift) (n + 1)).card := by
    apply Finset.card_le_card_of_injOn (fun z : Word Alphabet × Alphabet => z.1 ++ [z.2])
    · intro z hz
      obtain ⟨hw, ha⟩ := Finset.mem_product.mp hz
      obtain ⟨hwL, hwlen⟩ := mem_wordFinset.mp hw
      exact mem_wordFinset.mpr ⟨append_mem_language hwL (hQ _ ha),
        by simp only [List.length_append, List.length_singleton, hwlen]⟩
    · intro z hz t ht he
      have hlen : z.1.length = t.1.length :=
        (mem_wordFinset.mp (Finset.mem_product.mp hz).1).2.trans
          (mem_wordFinset.mp (Finset.mem_product.mp ht).1).2.symm
      obtain ⟨hfst, hsnd⟩ := List.append_inj he hlen
      exact Prod.ext hfst (by simpa only [List.singleton_inj] using hsnd)
  simpa only [Finset.card_product, hQcard, wordCount, Nat.mul_comm] using H
end BalanceSpecification.FiveSymbol
