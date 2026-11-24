-- Prove2me | solution 1 for BalanceSpecification.shortlexThrough_prefix
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:42:02.573194+00:00
-- url     : https://prove2.me/submissions/284f7e17-d657-440d-a71e-5038c5b60161

module
public import Definitions.Def_BalanceSpecificaton_Counting
public import Mathlib.Data.List.Shortlex
public import Mathlib.Data.List.Lex
public import Mathlib.Data.Finset.Sort
public import Mathlib.Tactic
public import Definitions.Def_BalanceSpecificaton_Shortlex
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



set_option autoImplicit true
@[expose] public section
public section
noncomputable section
open BalanceSpecification
variable {A : Type*} [Fintype A] [LinearOrder A]
namespace BalanceSpecification
theorem _root_.solution {n m : ℕ} (hnm : n ≤ m) :
    shortlexThrough (A := A) n <+: shortlexThrough m := by
  induction m, hnm using Nat.le_induction with
  | base => exact ⟨[], by simp only [List.append_nil]⟩
  | succ m hnm ih =>
    exact ih.trans (by rw [shortlexThrough_succ]; exact List.prefix_append _ _)
end BalanceSpecification
