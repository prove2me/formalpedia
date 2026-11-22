-- Prove2me | solution 1 for DeciSigma1.Readers.StructuralReader.Eligible.runPrefix_ne
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T13:12:15.282513+00:00
-- url     : https://prove2.me/submissions/d6ad8c8f-5d23-4b37-8aa2-afcbc4f2a5b3

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
public import Theorems.Thm_DeciSigma1_Readers_Table_runPrefix_of_le

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
namespace Eligible
theorem _root_.solution {W : Fin k → List α} {i : Fin k} (h : M.Eligible W i) (a : ℕ) :
    M.runPrefix W i a ≠ M.dead := by
  by_cases ha : a ≤ (W i).length
  · exact h.1 a ha
  · rw [runPrefix_of_le W i (by omega)]; exact h.1 _ le_rfl
end Eligible
end DeciSigma1.Readers.StructuralReader
