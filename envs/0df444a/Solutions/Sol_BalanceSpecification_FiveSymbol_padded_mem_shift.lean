-- Prove2me | solution 1 for BalanceSpecification.FiveSymbol.padded_mem_shift
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:44:31.056797+00:00
-- url     : https://prove2.me/submissions/e8324b93-d8ad-4406-8383-9ab5816ddbc8

module
public import Definitions.Def_BalanceSpecificaton_Shortlex
public import Definitions.Def_BalanceSpecificaton_Forbidden
public import Definitions.Def_BalanceSpecificaton_Synchronization
public import Mathlib.Tactic
public import Definitions.Def_BalanceSpecificaton_FiveSymbol
public import Theorems.Thm_BalanceSpecification_FiveSymbol_forbiddenWord_get_zero
public import Theorems.Thm_BalanceSpecification_FiveSymbol_forbiddenWord_get_last
public import Theorems.Thm_BalanceSpecification_FiveSymbol_block_padded_infix
public import Theorems.Thm_BalanceSpecification_getElem_block
public import Theorems.Thm_BalanceSpecification_length_block
public import Theorems.Thm_BalanceSpecification_mem_allWords
public import Theorems.Thm_BalanceSpecification_mem_followerFinset
public import Theorems.Thm_BalanceSpecification_mem_forbiddenShift_iff
public import Theorems.Thm_BalanceSpecification_mem_predecessorFinset
public import Theorems.Thm_BalanceSpecification_mem_wordFinset
public import Theorems.Thm_BalanceSpecification_shortlexWord_zero
attribute [local simp] BalanceSpecification.getElem_block
attribute [local simp] BalanceSpecification.length_block
attribute [local simp] BalanceSpecification.mem_allWords
attribute [local simp] BalanceSpecification.mem_followerFinset
attribute [local simp] BalanceSpecification.mem_forbiddenShift_iff
attribute [local simp] BalanceSpecification.mem_predecessorFinset
attribute [local simp] BalanceSpecification.mem_wordFinset
attribute [local simp] BalanceSpecification.shortlexWord_zero



set_option autoImplicit true
@[expose] public section
public section
noncomputable section
open BalanceSpecification BalanceSpecification.FiveSymbol
namespace BalanceSpecification.FiveSymbol
theorem _root_.solution {w : Word Alphabet}
    (hw : ∀ j : ℕ, 1 ≤ j → ¬ forbiddenWord j <:+: w) :
    padded w ∈ shift.carrier := by
  rintro f ⟨j, hj, rfl⟩ k hocc
  have hfirst := List.getElem_of_eq hocc
    (show 0 < (block (padded w) k (forbiddenWord j).length).length by
      simpa only [length_block] using forbiddenWord_length_pos j)
  simp only [block, List.getElem_ofFn, Nat.cast_zero, add_zero,
    forbiddenWord_get_zero] at hfirst
  have hk : 0 ≤ k := by
    by_contra h
    have hkneg : k < 0 := by omega
    simp only [padded, hkneg, ↓reduceDIte] at hfirst
    exact (by decide : (4 : Alphabet) ≠ 0) hfirst
  have hlast := List.getElem_of_eq hocc
    (show (forbiddenWord j).length - 1 <
      (block (padded w) k (forbiddenWord j).length).length by
      have := forbiddenWord_length_pos j; simp only [length_block]; omega)
  simp only [block, List.getElem_ofFn, forbiddenWord_get_last] at hlast
  have hend : k + ((forbiddenWord j).length : ℤ) ≤ w.length := by
    by_contra h
    have hindex : 0 ≤ k + (((forbiddenWord j).length - 1 : ℕ) : ℤ) := by omega
    have houtside : ¬ k + (((forbiddenWord j).length - 1 : ℕ) : ℤ) < w.length := by omega
    simp only [padded, not_lt.mpr hindex, ↓reduceDIte, houtside] at hlast
    exact (by decide : (0 : Alphabet) ≠ 4) hlast
  exact hw j hj (by rw [← hocc]; exact block_padded_infix w hk hend)
end BalanceSpecification.FiveSymbol
