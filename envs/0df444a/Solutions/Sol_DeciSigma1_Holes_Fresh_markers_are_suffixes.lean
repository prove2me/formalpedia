-- Prove2me | solution 1 for DeciSigma1.Holes.Fresh.markers_are_suffixes
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:49:36.489161+00:00
-- url     : https://prove2.me/submissions/74d3384e-0bd4-4b77-827c-43672dd8bdd4

module
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Definitions.Def_LeanPool_DeciSigma1_Readers_Basic
public import Mathlib.Order.Nat
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Order.Interval.Finset.Nat
public import Definitions.Def_LeanPool_DeciSigma1_Holes_Fresh_Hierarchy
public import Theorems.Thm_DeciSigma1_Holes_Fresh_marker_suffix

set_option autoImplicit true
@[expose] public section
public section
open DeciSigma1 DeciSigma1.Holes DeciSigma1.Holes.Fresh
open DeciSigma1.Readers
open Finset
variable {α : Type} {k : ℕ}
variable [DecidableEq α]
variable (W : Fin k → List α)
namespace DeciSigma1.Holes.Fresh
theorem _root_.solution (t : ℕ) :
    (level W t).MarkersAreSuffixes W := fun m _ => marker_suffix W t m
end DeciSigma1.Holes.Fresh
