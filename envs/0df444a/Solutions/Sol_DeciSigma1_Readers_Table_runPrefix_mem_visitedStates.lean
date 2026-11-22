-- Prove2me | solution 1 for DeciSigma1.Readers.Table.runPrefix_mem_visitedStates
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:52:18.969686+00:00
-- url     : https://prove2.me/submissions/3c7b62da-d67a-4f1c-9946-ce7014ef0ce3

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
public import Theorems.Thm_DeciSigma1_Readers_Table_mem_visitedStates

set_option autoImplicit true
@[expose] public section
public section
open DeciSigma1 DeciSigma1.Readers
open DeciSigma1.Automata
variable {α S : Type} {k : ℕ}
open DeciSigma1.Readers.Table
variable (T : Table α S k)
variable {T}
namespace DeciSigma1.Readers.Table
theorem _root_.solution [DecidableEq S] (W : Fin k → List α) (i : Fin k) {a : ℕ}
    (h : a ≤ (W i).length) : T.runPrefix W i a ∈ T.visitedStates W i :=
        mem_visitedStates.mpr ⟨a, h, rfl⟩
end DeciSigma1.Readers.Table
