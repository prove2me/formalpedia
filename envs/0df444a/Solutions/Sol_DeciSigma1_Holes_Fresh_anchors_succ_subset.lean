-- Prove2me | solution 1 for DeciSigma1.Holes.Fresh.anchors_succ_subset
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T13:25:43.796271+00:00
-- url     : https://prove2.me/submissions/e7a7644a-a650-485a-8e6d-f17f243ae82c

module
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Definitions.Def_LeanPool_DeciSigma1_Readers_Basic
public import Mathlib.Order.Nat
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Order.Interval.Finset.Nat
public import Definitions.Def_LeanPool_DeciSigma1_Holes_Fresh_Hierarchy
public import Theorems.Thm_DeciSigma1_Holes_Fresh_contextAnchors_succ_subset

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
theorem _root_.solution (t : ℕ) (l : Fin k) :
    anchors W (t + 1) l ⊆ anchors W t l :=
  insert_subset_insert _ (contextAnchors_succ_subset t _)
end DeciSigma1.Holes.Fresh
