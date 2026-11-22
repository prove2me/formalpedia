-- Prove2me | solution 1 for DeciSigma1.Holes.Fresh.suffix_of_suffix_of_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T13:16:15.850155+00:00
-- url     : https://prove2.me/submissions/7575b75f-7841-4b8d-adf9-ca73aa124f27

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
theorem _root_.solution {w : List α} (hu : u <:+ w) (hv : v <:+ w)
    (h : u.length ≤ v.length) : u <:+ v := List.suffix_of_suffix_length_le hu hv h
end DeciSigma1.Holes.Fresh
