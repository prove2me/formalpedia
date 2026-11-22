-- Prove2me | solution 1 for DeciSigma1.Holes.Fresh.marker_suffix_succ
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T13:24:27.70768+00:00
-- url     : https://prove2.me/submissions/288ff407-6587-4651-afa7-40ccc047e1c4

module
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Definitions.Def_LeanPool_DeciSigma1_Readers_Basic
public import Mathlib.Order.Nat
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Order.Interval.Finset.Nat
public import Definitions.Def_LeanPool_DeciSigma1_Holes_Fresh_Hierarchy
public import Theorems.Thm_DeciSigma1_Holes_Fresh_Level_next_suffix
public import Theorems.Thm_DeciSigma1_Holes_Fresh_markers_are_suffixes
public import Theorems.Thm_DeciSigma1_Holes_Fresh_level_anti

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
theorem _root_.solution {t : ℕ} {l : Fin k}
    (hl : l ∈ active W (t + 1)) : marker W t l <:+ marker W (t + 1) l := by
  rcases t with _ | t
  · exact List.nil_suffix
  · exact (Level.next_suffix (level_anti t) (markers_are_suffixes W (t + 1)) hl).1
end DeciSigma1.Holes.Fresh
