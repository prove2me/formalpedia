-- Prove2me | solution 1 for BooleanIsoperimetry.coordinateDown_eq_image
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:19:32.312597+00:00
-- url     : https://prove2.me/submissions/f8fdcf00-b6b2-4f9b-8f48-fed389192724

module
public import Definitions.Def_LeanPool_BooleanIsoperimetry_Cube
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Data.Rat.Cast.Order
public import Mathlib.Tactic.NormNum.Abs
public import Mathlib.Tactic.NormNum.DivMod
public import Mathlib.Tactic.NormNum.OfScientific
public import Mathlib.Tactic.NormNum.Pow
public import Definitions.Def_LeanPool_BooleanIsoperimetry_SimplicialCompression
public import Theorems.Thm_BooleanIsoperimetry_mem_neighborhood_iff
attribute [local simp] BooleanIsoperimetry.mem_neighborhood_iff



set_option autoImplicit true
@[expose] public section
public section
open scoped BigOperators
open Finset
open BooleanIsoperimetry
namespace BooleanIsoperimetry
theorem _root_.solution {N : ℕ} (i : Fin N) (A : Finset (Cube N)) :
    coordinateDown i A = A.image (downMap i A) := by
  unfold coordinateDown downMap
  ext y
  simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_image]
  constructor
  · rintro (⟨hyA, hcond⟩ | ⟨z, hz, rfl⟩)
    · refine ⟨y, hyA, ?_⟩
      rw [if_neg]
      rintro ⟨hiy, hey⟩
      rcases hcond with h | h
      · exact h hiy
      · exact hey h
    · exact ⟨z, hz.1, by rw [if_pos hz.2]⟩
  · rintro ⟨z, hz, rfl⟩
    by_cases hcond : i ∈ z ∧ z.erase i ∉ A
    · right
      rw [if_pos hcond]
      exact ⟨z, ⟨hz, hcond⟩, rfl⟩
    · left
      rw [if_neg hcond]
      refine ⟨hz, ?_⟩
      rw [not_and_or, not_not] at hcond
      exact hcond
end BooleanIsoperimetry
