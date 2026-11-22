-- Prove2me | solution 1 for DeciSigma1.Readers.StructuralReader.immortal_of_not_fresh
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T13:13:30.957795+00:00
-- url     : https://prove2.me/submissions/66d0e89a-edc8-42f9-9aca-3d8066b0e25a

module
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Definitions.Def_LeanPool_DeciSigma1_Automata_Basic
public import Mathlib.Order.Nat
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Data.Fintype.Pi
public import Mathlib.Data.Fintype.Pigeonhole
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Tactic.Linarith
public import Mathlib.Data.Finset.Prod
public import Definitions.Def_LeanPool_DeciSigma1_Readers_Basic
public import Theorems.Thm_DeciSigma1_Readers_Table_runFrom_runPrefix_drop
public import Theorems.Thm_DeciSigma1_Readers_Table_fresh_iff
public import Theorems.Thm_DeciSigma1_Readers_StructuralReader_Eligible_liveAlong
public import Theorems.Thm_DeciSigma1_Automata_mem_wordsUpTo
public import Theorems.Thm_DeciSigma1_runFrom_cons
public import Theorems.Thm_DeciSigma1_runFrom_nil
public import Theorems.Thm_DeciSigma1_runFrom_snoc
attribute [local simp] DeciSigma1.Automata.mem_wordsUpTo
attribute [local simp] DeciSigma1.runFrom_cons
attribute [local simp] DeciSigma1.runFrom_nil
attribute [local simp] DeciSigma1.runFrom_snoc



set_option autoImplicit true
@[expose] public section
public section
open DeciSigma1 DeciSigma1.Readers
open DeciSigma1.Automata
variable {α S : Type} {k : ℕ}
open Table
open DeciSigma1.Readers.StructuralReader
variable (M : StructuralReader α S k)
variable {M}
namespace DeciSigma1.Readers.StructuralReader
theorem _root_.solution [DecidableEq S] {W : Fin k → List α} {i : Fin k}
    (h : M.Eligible W i) (hf : ¬ M.Fresh W i) : M.Immortal (M.endState W i) := by
  rw [fresh_iff] at hf
  push Not at hf
  obtain ⟨c, hc, he⟩ := hf
  have hl := h.liveAlong c
  rw [he] at hl
  refine immortal_of_cycle (u := []) (v := (W i).drop c) (by simp; omega) (by simpa using hl) ?_
  simp only [runFrom_nil]
  rw [← he, runFrom_runPrefix_drop, he]
end DeciSigma1.Readers.StructuralReader
