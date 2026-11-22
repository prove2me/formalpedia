-- Prove2me | solution 1 for DeciSigma1.Readers.StructuralReader.Eligible.liveAlong
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T13:12:51.622796+00:00
-- url     : https://prove2.me/submissions/3caf000a-3a80-4484-b812-1a02611e7e2b

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
public import Theorems.Thm_DeciSigma1_Readers_Table_runPrefix_add
public import Theorems.Thm_DeciSigma1_Readers_StructuralReader_Eligible_runPrefix_ne

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
    M.LiveAlong (M.runPrefix W i a) ((W i).drop a) := by
  intro t _
  rw [← runPrefix_add]
  exact h.runPrefix_ne _
end Eligible
end DeciSigma1.Readers.StructuralReader
