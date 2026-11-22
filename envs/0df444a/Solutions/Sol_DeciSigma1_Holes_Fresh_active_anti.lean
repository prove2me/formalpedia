-- Prove2me | solution 1 for DeciSigma1.Holes.Fresh.active_anti
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T13:01:14.966361+00:00
-- url     : https://prove2.me/submissions/b131a627-4cb1-4a56-abbb-6203e5d7a6c3

module
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Definitions.Def_LeanPool_DeciSigma1_Readers_Basic
public import Mathlib.Order.Nat
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Order.Interval.Finset.Nat
public import Definitions.Def_LeanPool_DeciSigma1_Holes_Fresh_Hierarchy
public import Theorems.Thm_DeciSigma1_Holes_Fresh_active_succ_subset
public import Theorems.Thm_DeciSigma1_Readers_Dominates_refl
public import Theorems.Thm_DeciSigma1_Readers_Dominates_trans
public import Theorems.Thm_DeciSigma1_Readers_FreshDominates_refl
public import Theorems.Thm_DeciSigma1_Readers_FreshDominates_trans


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
theorem _root_.solution {s t : ℕ} (h : s ≤ t) : active W t ⊆ active W s := by
  induction h with
  | refl => exact subset_refl _
  | step _ ih => exact (active_succ_subset W _).trans ih
end DeciSigma1.Holes.Fresh
