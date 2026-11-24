-- Prove2me | solution 1 for BalanceSpecification.exists_positive_shortlex_index
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:58:05.916215+00:00
-- url     : https://prove2.me/submissions/2c2c319d-ef7b-46b5-bdc4-1f7cd1432237

module
public import Definitions.Def_BalanceSpecificaton_Counting
public import Mathlib.Data.List.Shortlex
public import Mathlib.Data.List.Lex
public import Mathlib.Data.Finset.Sort
public import Mathlib.Tactic
public import Definitions.Def_BalanceSpecificaton_Shortlex
public import Theorems.Thm_BalanceSpecification_shortlexWord_surjective
public import Theorems.Thm_BalanceSpecification_shortlexWord_zero
public import Theorems.Thm_BalanceSpecification_getElem_block
public import Theorems.Thm_BalanceSpecification_length_block
public import Theorems.Thm_BalanceSpecification_mem_allWords
public import Theorems.Thm_BalanceSpecification_mem_followerFinset
public import Theorems.Thm_BalanceSpecification_mem_predecessorFinset
public import Theorems.Thm_BalanceSpecification_mem_wordFinset
attribute [local simp] BalanceSpecification.getElem_block
attribute [local simp] BalanceSpecification.length_block
attribute [local simp] BalanceSpecification.mem_allWords
attribute [local simp] BalanceSpecification.mem_followerFinset
attribute [local simp] BalanceSpecification.mem_predecessorFinset
attribute [local simp] BalanceSpecification.mem_wordFinset


attribute [local simp] BalanceSpecification.shortlexWord_zero

set_option autoImplicit true
@[expose] public section
public section
noncomputable section
open BalanceSpecification
variable {A : Type*} [Fintype A] [LinearOrder A]
variable [Nonempty A]
namespace BalanceSpecification
theorem _root_.solution {w : Word A} (hw : w ≠ []) :
    ∃ j : ℕ, 1 ≤ j ∧ shortlexWord (A := A) j = w := by
  obtain ⟨j, hj⟩ := shortlexWord_surjective (A := A) w
  refine ⟨j, ?_, hj⟩
  by_contra h
  have hjzero : j = 0 := by omega
  subst j
  exact hw (hj.symm.trans shortlexWord_zero)
end BalanceSpecification
