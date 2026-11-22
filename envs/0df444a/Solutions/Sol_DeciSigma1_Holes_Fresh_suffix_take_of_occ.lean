-- Prove2me | solution 1 for DeciSigma1.Holes.Fresh.suffix_take_of_occ
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T13:01:28.361881+00:00
-- url     : https://prove2.me/submissions/7e278da1-f635-47ed-8945-7d7aabefe4ac

module
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Definitions.Def_LeanPool_DeciSigma1_Readers_Basic
public import Mathlib.Order.Nat
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Order.Interval.Finset.Nat
public import Definitions.Def_LeanPool_DeciSigma1_Holes_Fresh_Hierarchy
public import Theorems.Thm_DeciSigma1_Holes_Fresh_take_occ

set_option autoImplicit true
@[expose] public section
public section
open DeciSigma1 DeciSigma1.Holes DeciSigma1.Holes.Fresh
open DeciSigma1.Readers
open Finset
variable {α : Type} {k : ℕ}
variable {x u v : List α}
namespace DeciSigma1.Holes.Fresh
theorem _root_.solution {i : ℕ} (hu : u <+: x.drop i) : u <:+ x.take (i + u.length) := by
  rw [take_occ hu]; exact List.suffix_append _ _
end DeciSigma1.Holes.Fresh
