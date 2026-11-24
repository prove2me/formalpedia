-- Prove2me | solution 1 for BalanceSpecification.card_allWords
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T01:46:07.835888+00:00
-- url     : https://prove2.me/submissions/6667d53a-4de1-4fb3-9e71-a7bd98146978

module
public import Definitions.Def_BalanceSpecificaton_CountBounds
public import Mathlib.Data.Fintype.Prod
public import Mathlib.Tactic
public import Definitions.Def_BalanceSpecificaton_TilingBounds
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



set_option autoImplicit true
@[expose] public section
public section
noncomputable section
open BalanceSpecification
variable {A : Type*}
variable [Fintype A]
namespace BalanceSpecification
theorem _root_.solution (n : ℕ) : (allWords (A := A) n).card = (Fintype.card A) ^ n := by
  classical
  have hinj : Function.Injective (fun f : Fin n → A => List.ofFn f) := by
    intro f g h
    funext i
    have he := List.getElem_of_eq h (show i.val < (List.ofFn f).length by
      simpa only [List.length_ofFn] using i.isLt)
    simpa only [List.getElem_ofFn] using he
  unfold allWords
  rw [Finset.card_image_of_injective _ hinj, Finset.card_univ, Fintype.card_fun,
    Fintype.card_fin]
end BalanceSpecification
