-- Prove2me | solution 1 for Falmagne.exists_chosen
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T02:14:30.845808+00:00
-- url     : https://prove2.me/submissions/a93351c4-fb61-47ea-ba72-1dce018b0e73

module
public import Mathlib.Data.Finsupp.Basic
public import Mathlib.Data.Finsupp.Defs
public import Mathlib.Data.List.NodupEquivFin
public import Mathlib.Data.Finset.Max
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Tactic
public import Definitions.Def_EconomicsNextProof_Basic
public import Theorems.Thm_Falmagne_lowerContour_subset_iff

set_option autoImplicit true
@[expose] public section
public section
open Falmagne
variable {X : Type*} [Fintype X] [DecidableEq X]
variable {l : List X} {A : Finset X} {x y : X}
namespace Falmagne
theorem _root_.solution (hl : IsRanking l) (hA : A.Nonempty) :
    ∃ x ∈ A, A ⊆ lowerContour l x := by
  obtain ⟨x, hx, hmin⟩ := Finset.exists_min_image A (fun x => l.idxOf x) hA
  exact ⟨x, hx, (lowerContour_subset_iff hl).mpr hmin⟩
end Falmagne
