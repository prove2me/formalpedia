-- Prove2me | solution 1 for DeciSigma1.Holes.Fresh.contextAnchors_marker_succ
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T13:24:28.17271+00:00
-- url     : https://prove2.me/submissions/4e5532ef-136a-4285-b238-3c22f8f4bb2b

module
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Definitions.Def_LeanPool_DeciSigma1_Readers_Basic
public import Mathlib.Order.Nat
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Order.Interval.Finset.Nat
public import Definitions.Def_LeanPool_DeciSigma1_Holes_Fresh_Hierarchy
public import Theorems.Thm_DeciSigma1_Holes_Fresh_Level_next_markerEndCuts_eq
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
theorem _root_.solution {t : ℕ} (ht : 1 ≤ t) {l : Fin k} (hl : l ∈ active W (t + 1)) :
    ∃ m ∈ active W t, marker W t m <+: marker W (t + 1) l ∧
      (marker W t m).length < (marker W (t + 1) l).length ∧
      contextAnchors W t (marker W (t + 1) l) =
        {(marker W t m).length, (marker W (t + 1) l).length} := by
  obtain ⟨t, rfl⟩ : ∃ t', t = t' + 1 := ⟨t - 1, by omega⟩
  exact Level.next_markerEndCuts_eq (level_anti t) (markers_are_suffixes W (t + 1)) hl
end DeciSigma1.Holes.Fresh
