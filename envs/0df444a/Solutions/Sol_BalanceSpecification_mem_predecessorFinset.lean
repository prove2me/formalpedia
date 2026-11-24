-- Prove2me | solution 1 for BalanceSpecification.mem_predecessorFinset
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T01:33:46.483664+00:00
-- url     : https://prove2.me/submissions/71bcbc01-fd84-46e6-b8a3-b8c9021b2dbb

module
public import Definitions.Def_BalanceSpecificaton_Language
public import Mathlib.Data.Fintype.Pi
public import Mathlib.Data.Real.Basic
public import Mathlib.Tactic
public import Definitions.Def_BalanceSpecificaton_Counting
public import Theorems.Thm_BalanceSpecification_mem_allWords
public import Theorems.Thm_BalanceSpecification_mem_wordFinset
public import Theorems.Thm_BalanceSpecification_mem_followerFinset
public import Theorems.Thm_BalanceSpecification_getElem_block
public import Theorems.Thm_BalanceSpecification_length_block
attribute [local simp] BalanceSpecification.getElem_block
attribute [local simp] BalanceSpecification.length_block


attribute [local simp] BalanceSpecification.mem_allWords
attribute [local simp] BalanceSpecification.mem_wordFinset
attribute [local simp] BalanceSpecification.mem_followerFinset

set_option autoImplicit true
@[expose] public section
public section
noncomputable section
open BalanceSpecification
variable {A : Type*} [Fintype A]
namespace BalanceSpecification
theorem _root_.solution {L : Set (Word A)} {u w : Word A} {n : ℕ} :
    w ∈ predecessorFinset L u n ↔ w ∈ L ∧ w.length = n ∧ w ++ u ∈ L := by
  classical
  simp only [predecessorFinset, Finset.mem_filter, mem_wordFinset, and_assoc]
end BalanceSpecification
