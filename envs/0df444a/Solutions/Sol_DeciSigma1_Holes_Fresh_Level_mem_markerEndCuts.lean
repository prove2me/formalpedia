-- Prove2me | solution 1 for DeciSigma1.Holes.Fresh.Level.mem_markerEndCuts
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:46:31.584802+00:00
-- url     : https://prove2.me/submissions/12b68603-44e9-4301-be87-e597a874f263

module
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Definitions.Def_LeanPool_DeciSigma1_Readers_Basic
public import Mathlib.Order.Nat
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Order.Interval.Finset.Nat
public import Definitions.Def_LeanPool_DeciSigma1_Holes_Fresh_Hierarchy
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
open DeciSigma1 DeciSigma1.Holes DeciSigma1.Holes.Fresh
open DeciSigma1.Readers
open Finset
variable {α : Type} {k : ℕ}
open DeciSigma1.Holes.Fresh.Level
variable [DecidableEq α] (L : Level α k)
variable {L}
namespace DeciSigma1.Holes.Fresh.Level
theorem _root_.solution {u : List α} {e : ℕ} :
    e ∈ L.markerEndCuts u ↔ e ≤ u.length ∧ ∃ m ∈ L.active, L.marker m <:+ u.take e := by
  simp [markerEndCuts, Nat.lt_succ_iff]
end DeciSigma1.Holes.Fresh.Level
