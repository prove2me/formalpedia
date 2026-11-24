-- Prove2me | solution 1 for BalanceSpecification.mem_wordFinset
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T01:31:52.537666+00:00
-- url     : https://prove2.me/submissions/12063e1d-c635-4617-a040-eb4975d2f2f5

module
public import Definitions.Def_BalanceSpecificaton_Language
public import Mathlib.Data.Fintype.Pi
public import Mathlib.Data.Real.Basic
public import Mathlib.Tactic
public import Definitions.Def_BalanceSpecificaton_Counting
public import Theorems.Thm_BalanceSpecification_mem_allWords
public import Theorems.Thm_BalanceSpecification_getElem_block
public import Theorems.Thm_BalanceSpecification_length_block
attribute [local simp] BalanceSpecification.getElem_block
attribute [local simp] BalanceSpecification.length_block


attribute [local simp] BalanceSpecification.mem_allWords

set_option autoImplicit true
@[expose] public section
public section
noncomputable section
open BalanceSpecification
variable {A : Type*} [Fintype A]
namespace BalanceSpecification
theorem _root_.solution {L : Set (Word A)} {w : Word A} {n : ℕ} :
    w ∈ wordFinset L n ↔ w ∈ L ∧ w.length = n := by
  classical
  simp only [wordFinset, Finset.mem_filter, mem_allWords, and_comm]
end BalanceSpecification
