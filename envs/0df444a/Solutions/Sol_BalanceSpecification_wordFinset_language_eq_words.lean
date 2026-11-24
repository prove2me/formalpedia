-- Prove2me | solution 1 for BalanceSpecification.wordFinset_language_eq_words
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:54:01.739071+00:00
-- url     : https://prove2.me/submissions/d89eff53-641a-4b4a-b37e-f0b2d0f9b509

module
public import Definitions.Def_BalanceSpecificaton_Language
public import Mathlib.Data.Fintype.Pi
public import Mathlib.Data.Real.Basic
public import Mathlib.Tactic
public import Definitions.Def_BalanceSpecificaton_Counting
public import Theorems.Thm_BalanceSpecification_mem_allWords
public import Theorems.Thm_BalanceSpecification_mem_wordFinset
public import Theorems.Thm_BalanceSpecification_mem_followerFinset
public import Theorems.Thm_BalanceSpecification_mem_predecessorFinset
public import Theorems.Thm_BalanceSpecification_getElem_block
public import Theorems.Thm_BalanceSpecification_length_block
attribute [local simp] BalanceSpecification.getElem_block
attribute [local simp] BalanceSpecification.length_block


attribute [local simp] BalanceSpecification.mem_allWords
attribute [local simp] BalanceSpecification.mem_wordFinset
attribute [local simp] BalanceSpecification.mem_followerFinset
attribute [local simp] BalanceSpecification.mem_predecessorFinset

set_option autoImplicit true
@[expose] public section
public section
noncomputable section
open BalanceSpecification
variable {A : Type*} [Fintype A]
namespace BalanceSpecification
theorem _root_.solution [TopologicalSpace A] (X : ShiftSpace A) (n : ℕ) :
    (wordFinset (language X) n : Set (Word A)) = words X n := by
  ext w
  exact mem_wordFinset
end BalanceSpecification
