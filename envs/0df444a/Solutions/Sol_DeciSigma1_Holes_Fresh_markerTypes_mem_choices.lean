-- Prove2me | solution 1 for DeciSigma1.Holes.Fresh.markerTypes_mem_choices
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T14:36:34.099939+00:00
-- url     : https://prove2.me/submissions/076e4198-310b-40c6-9919-555d58e78c52

module
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Definitions.Def_LeanPool_DeciSigma1_Holes_Fresh_ChannelPreservation
public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Data.Finset.Powerset
public import Mathlib.Data.Finset.Max
public import Definitions.Def_LeanPool_DeciSigma1_Holes_Fresh_Bound
public import Theorems.Thm_DeciSigma1_Holes_Fresh_markerTypes_card_le_one
public import Theorems.Thm_DeciSigma1_Holes_Fresh_mem_markerTypes


set_option autoImplicit true
@[expose] public section
public section
open DeciSigma1 DeciSigma1.Holes DeciSigma1.Holes.Fresh
open DeciSigma1.Readers
open Finset
variable {α : Type} [DecidableEq α] {k : ℕ} {W : Fin k → List α}
variable {S : Type} [Fintype S] [DecidableEq S] {T : Table α S k}
namespace DeciSigma1.Holes.Fresh
theorem _root_.solution (r : ℕ) (u : List α) (c : ℕ) :
    markerTypes W r u c ∈ typeChoices W r := by
  by_cases h : markerTypes W r u c = ∅
  · rw [h]; exact mem_insert_self _ _
  · obtain ⟨τ, hτ⟩ := nonempty_iff_ne_empty.mpr h
    obtain ⟨m, hm, _, he⟩ := mem_markerTypes.mp hτ
    have heq : markerTypes W r u c = {marker W r m} := by
      rw [he]
      exact eq_singleton_iff_unique_mem.mpr ⟨hτ, fun x hx =>
        (card_le_one.mp (markerTypes_card_le_one u c)) _ hx _ hτ⟩
    rw [heq]
    exact mem_insert_of_mem (mem_image_of_mem _ hm)
end DeciSigma1.Holes.Fresh
