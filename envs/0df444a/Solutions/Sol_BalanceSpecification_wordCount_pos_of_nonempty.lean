-- Prove2me | solution 1 for BalanceSpecification.wordCount_pos_of_nonempty
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T01:34:58.442327+00:00
-- url     : https://prove2.me/submissions/6e1de834-e710-4a59-96ce-2116cc80c35f

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
theorem _root_.solution [TopologicalSpace A] {X : ShiftSpace A}
    (hX : X.carrier.Nonempty) (n : ℕ) : 0 < wordCount (language X) n := by
  obtain ⟨x, hx⟩ := hX
  apply Finset.card_pos.mpr
  refine ⟨block x 0 n, mem_wordFinset.mpr ⟨?_, length_block x 0 n⟩⟩
  exact ⟨x, hx, 0, by simp only [length_block]⟩
end BalanceSpecification
