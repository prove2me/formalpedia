-- Prove2me | solution 1 for DeciSigma1.Holes.Fresh.active_succ_subset
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:53:06.889621+00:00
-- url     : https://prove2.me/submissions/2ba0fe5d-0142-4a89-936d-907d396c630f

module
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Definitions.Def_LeanPool_DeciSigma1_Readers_Basic
public import Mathlib.Order.Nat
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Order.Interval.Finset.Nat
public import Definitions.Def_LeanPool_DeciSigma1_Holes_Fresh_Hierarchy
public import Theorems.Thm_DeciSigma1_Holes_Fresh_Level_next_active_subset

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
theorem _root_.solution (t : ℕ) : active W (t + 1) ⊆ active W t := by
  rcases t with _ | t
  · exact subset_refl _
  · exact Level.next_active_subset W
end DeciSigma1.Holes.Fresh
