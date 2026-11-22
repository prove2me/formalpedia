-- Prove2me | solution 1 for DeciSigma1.Holes.Fresh.lowerLevelTypes_mem_choices
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T14:37:10.303491+00:00
-- url     : https://prove2.me/submissions/86e4767d-6462-4b5b-a861-db3e2df456d8

module
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Definitions.Def_LeanPool_DeciSigma1_Holes_Fresh_ChannelPreservation
public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Data.Finset.Powerset
public import Mathlib.Data.Finset.Max
public import Definitions.Def_LeanPool_DeciSigma1_Holes_Fresh_Bound
public import Theorems.Thm_DeciSigma1_Holes_Fresh_markerTypes_mem_choices

set_option autoImplicit true
@[expose] public section
public section
open DeciSigma1 DeciSigma1.Holes DeciSigma1.Holes.Fresh
open DeciSigma1.Readers
open Finset
variable {α : Type} [DecidableEq α] {k : ℕ} {W : Fin k → List α}
variable {S : Type} [Fintype S] [DecidableEq S] {T : Table α S k}
namespace DeciSigma1.Holes.Fresh
theorem _root_.solution (t : ℕ) (u : List α) (c : ℕ) :
    lowerLevelTypes W t u c ∈ lowerLevelTypeChoices W t :=
  Fintype.mem_piFinset.mpr fun r => markerTypes_mem_choices (r.val + 1) u c
end DeciSigma1.Holes.Fresh
