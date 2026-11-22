-- Prove2me | solution 1 for DeciSigma1.Holes.Fresh.Level.next_active_subset
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:52:40.714671+00:00
-- url     : https://prove2.me/submissions/a0c6da1a-78c3-4060-9800-106df5730af1

module
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Definitions.Def_LeanPool_DeciSigma1_Readers_Basic
public import Mathlib.Order.Nat
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Order.Interval.Finset.Nat
public import Definitions.Def_LeanPool_DeciSigma1_Holes_Fresh_Hierarchy

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
theorem _root_.solution (W : Fin k → List α) : (L.next W).active ⊆ L.active := filter_subset _ _
end DeciSigma1.Holes.Fresh.Level
