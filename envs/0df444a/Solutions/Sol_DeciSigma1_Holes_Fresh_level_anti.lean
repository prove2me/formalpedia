-- Prove2me | solution 1 for DeciSigma1.Holes.Fresh.level_anti
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T13:20:51.186156+00:00
-- url     : https://prove2.me/submissions/0d83543e-b562-4b86-9dc2-552a7b548afa

module
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Definitions.Def_LeanPool_DeciSigma1_Readers_Basic
public import Mathlib.Order.Nat
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Order.Interval.Finset.Nat
public import Definitions.Def_LeanPool_DeciSigma1_Holes_Fresh_Hierarchy
public import Theorems.Thm_DeciSigma1_Holes_Fresh_Level_next_anti
public import Theorems.Thm_DeciSigma1_Holes_Fresh_markers_are_suffixes
public import Theorems.Thm_DeciSigma1_Holes_Fresh_level_one_anti

set_option autoImplicit true
@[expose] public section
public section
open DeciSigma1 DeciSigma1.Holes DeciSigma1.Holes.Fresh
open DeciSigma1.Readers
open Finset
variable {α : Type} {k : ℕ}
variable [DecidableEq α]
variable {W : Fin k → List α}
namespace DeciSigma1.Holes.Fresh
theorem _root_.solution : ∀ t, (level W (t + 1)).FactorAntichain
  | 0 => level_one_anti
  | t + 1 => Level.next_anti (solution t) (markers_are_suffixes W (t + 1))
end DeciSigma1.Holes.Fresh
