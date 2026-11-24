-- Prove2me | solution 1 for BalanceSpecification.mem_followerFinset
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T01:32:49.004464+00:00
-- url     : https://prove2.me/submissions/d69ad7ba-c55e-46c2-a922-5db1bd20c288

module
public import Definitions.Def_BalanceSpecificaton_Language
public import Mathlib.Data.Fintype.Pi
public import Mathlib.Data.Real.Basic
public import Mathlib.Tactic
public import Definitions.Def_BalanceSpecificaton_Counting
public import Theorems.Thm_BalanceSpecification_mem_allWords
public import Theorems.Thm_BalanceSpecification_mem_wordFinset
public import Theorems.Thm_BalanceSpecification_getElem_block
public import Theorems.Thm_BalanceSpecification_length_block
attribute [local simp] BalanceSpecification.getElem_block
attribute [local simp] BalanceSpecification.length_block


attribute [local simp] BalanceSpecification.mem_allWords
attribute [local simp] BalanceSpecification.mem_wordFinset

set_option autoImplicit true
@[expose] public section
public section
noncomputable section
open BalanceSpecification
variable {A : Type*} [Fintype A]
namespace BalanceSpecification
theorem _root_.solution {L : Set (Word A)} {u w : Word A} {n : ℕ} :
    w ∈ followerFinset L u n ↔ w ∈ L ∧ w.length = n ∧ u ++ w ∈ L := by
  classical
  simp only [followerFinset, Finset.mem_filter, mem_wordFinset, and_assoc]
end BalanceSpecification
