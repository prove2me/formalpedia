-- Prove2me | solution 1 for DeciSigma1.Readers.Dominates.trans
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:42:08.722407+00:00
-- url     : https://prove2.me/submissions/4fc975d0-f54a-4f81-9436-37d877254c62

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

set_option autoImplicit true
@[expose] public section
public section
open DeciSigma1 DeciSigma1.Readers
open DeciSigma1.Automata
variable {α S : Type} {k : ℕ}
open Table
variable [DecidableEq α] [DecidableEq S]
variable {T : Table α S k} {U V W : Fin k → List α}
namespace DeciSigma1.Readers
namespace Dominates
theorem _root_.solution (h₁ : Dominates T U V) (h₂ : Dominates T V W) : Dominates T U W :=
  ⟨fun i => (h₁.endState_eq i).trans (h₂.endState_eq i),
      fun i => (h₁.visitedStates_subset i).trans (h₂.visitedStates_subset i),
    fun i j => (h₁.channel_subset i j).trans (h₂.channel_subset i j)⟩
end Dominates
end DeciSigma1.Readers
