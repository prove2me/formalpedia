-- Prove2me | solution 1 for BooleanIsoperimetry.neighborhood_coordinateDown_subset
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:32:33.323629+00:00
-- url     : https://prove2.me/submissions/6ece84cf-423f-4dc1-996f-f6bcfaa7a462

module
public import Definitions.Def_LeanPool_BooleanIsoperimetry_Cube
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Data.Rat.Cast.Order
public import Mathlib.Tactic.NormNum.Abs
public import Mathlib.Tactic.NormNum.DivMod
public import Mathlib.Tactic.NormNum.OfScientific
public import Mathlib.Tactic.NormNum.Pow
public import Definitions.Def_LeanPool_BooleanIsoperimetry_SimplicialCompression
public import Theorems.Thm_BooleanIsoperimetry_coordinateDown_mem_of_mem
public import Theorems.Thm_BooleanIsoperimetry_coordinateDown_mem_of_not_mem
public import Theorems.Thm_BooleanIsoperimetry_hDist_self_le_one
public import Theorems.Thm_BooleanIsoperimetry_hDist_erase_le_hDist
public import Theorems.Thm_BooleanIsoperimetry_hDist_insert_le_hDist
public import Theorems.Thm_BooleanIsoperimetry_hDist_erase_self_le_one
public import Theorems.Thm_BooleanIsoperimetry_hDist_self_erase_le_one
public import Theorems.Thm_BooleanIsoperimetry_eq_erase_of_hDist_le_one_of_mem_of_not_mem
public import Theorems.Thm_BooleanIsoperimetry_mem_neighborhood_iff
attribute [local simp] BooleanIsoperimetry.mem_neighborhood_iff



set_option autoImplicit true
@[expose] public section
public section
open scoped BigOperators
open Finset
open BooleanIsoperimetry
namespace BooleanIsoperimetry
theorem _root_.solution {N : ℕ} {i : Fin N} {A : Finset (Cube N)} :
    neighborhood 1 (coordinateDown i A) ⊆ coordinateDown i (neighborhood 1 A) := by
  intro y hy
  rw [mem_neighborhood_iff] at hy
  rcases hy with ⟨x, hx, hdist⟩
  by_cases hiy : i ∉ y
  · rw [coordinateDown_mem_of_not_mem i _ y hiy]
    by_cases hix : i ∉ x
    · rw [coordinateDown_mem_of_not_mem i A x hix] at hx
      rcases hx with hxB | hx_insert
      · exact Or.inl (mem_neighborhood_iff.mpr ⟨x, hxB, hdist⟩)
      · exact Or.inr (mem_neighborhood_iff.mpr
          ⟨insert i x, hx_insert, hDist_insert_le_hDist i x y hdist⟩)
    · rw [coordinateDown_mem_of_mem i A x (by rwa [not_not] at hix)] at hx
      have hxy : y = x.erase i :=
        eq_erase_of_hDist_le_one_of_mem_of_not_mem hdist (by rwa [not_not] at hix) hiy
      subst hxy
      exact Or.inl (mem_neighborhood_iff.mpr ⟨x.erase i, hx.2, hDist_self_le_one (x.erase i)⟩)
  · rw [coordinateDown_mem_of_mem i _ y (by rwa [not_not] at hiy)]
    by_cases hix : i ∉ x
    · have hdist2 : hDist y x ≤ 1 := by unfold hDist at hdist ⊢; rw [symmDiff_comm]; exact hdist
      have hyx : x = y.erase i :=
        eq_erase_of_hDist_le_one_of_mem_of_not_mem hdist2 (by rwa [not_not] at hiy) hix
      subst hyx
      rw [coordinateDown_mem_of_not_mem i A _ (by simp)] at hx
      rcases hx with hxB | hx_insert
      · exact ⟨mem_neighborhood_iff.mpr ⟨y.erase i, hxB, hDist_erase_self_le_one i y⟩,
               mem_neighborhood_iff.mpr ⟨y.erase i, hxB, hDist_self_le_one (y.erase i)⟩⟩
      · rw [insert_erase (by rwa [not_not] at hiy)] at hx_insert
        exact ⟨mem_neighborhood_iff.mpr ⟨y, hx_insert, hDist_self_le_one y⟩,
               mem_neighborhood_iff.mpr ⟨y, hx_insert, hDist_self_erase_le_one i y⟩⟩
    · rw [coordinateDown_mem_of_mem i A x (by rwa [not_not] at hix)] at hx
      exact ⟨mem_neighborhood_iff.mpr ⟨x, hx.1, hdist⟩,
             mem_neighborhood_iff.mpr ⟨x.erase i, hx.2, hDist_erase_le_hDist i x y hdist⟩⟩
end BooleanIsoperimetry
