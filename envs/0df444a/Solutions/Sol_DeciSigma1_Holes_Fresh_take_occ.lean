-- Prove2me | solution 1 for DeciSigma1.Holes.Fresh.take_occ
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T13:00:50.656299+00:00
-- url     : https://prove2.me/submissions/c099cb11-f7d2-4934-b4a2-d747b8a89804

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
theorem _root_.solution {i : ℕ} (hu : u <+: x.drop i) : x.take (i + u.length) = x.take i ++ u := by
  rw [List.take_add, ← List.prefix_iff_eq_take.mp hu]
end DeciSigma1.Holes.Fresh
