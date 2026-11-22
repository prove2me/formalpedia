-- Prove2me | solution 1 for DeciSigma1.Holes.Fresh.occ_of_suffix
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:52:37.647798+00:00
-- url     : https://prove2.me/submissions/aa97f426-87d0-4631-af07-cd654702a35f

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
variable {x u v : List α}
namespace DeciSigma1.Holes.Fresh
theorem _root_.solution {w : List α} (hu : u <:+ w) : u <+: w.drop (w.length - u.length) := by
  rw [← List.suffix_iff_eq_drop.mp hu]
end DeciSigma1.Holes.Fresh
