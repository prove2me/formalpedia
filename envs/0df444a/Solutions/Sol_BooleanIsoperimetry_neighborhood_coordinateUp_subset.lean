-- Prove2me | solution 1 for BooleanIsoperimetry.neighborhood_coordinateUp_subset
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:32:24.5645+00:00
-- url     : https://prove2.me/submissions/e8b6e971-6585-4321-ac18-2274885d7a91

module
public import Definitions.Def_LeanPool_BooleanIsoperimetry_Cube
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Data.Rat.Cast.Order
public import Mathlib.Tactic.NormNum.Abs
public import Mathlib.Tactic.NormNum.DivMod
public import Mathlib.Tactic.NormNum.OfScientific
public import Mathlib.Tactic.NormNum.Pow
public import Definitions.Def_LeanPool_BooleanIsoperimetry_SimplicialCompression
public import Theorems.Thm_BooleanIsoperimetry_coordinateUp_mem_of_not_mem
public import Theorems.Thm_BooleanIsoperimetry_coordinateUp_mem_of_mem
public import Theorems.Thm_BooleanIsoperimetry_hDist_comm
public import Theorems.Thm_BooleanIsoperimetry_hDist_self_le_one
public import Theorems.Thm_BooleanIsoperimetry_hDist_erase_le_hDist
public import Theorems.Thm_BooleanIsoperimetry_hDist_insert_le_hDist
public import Theorems.Thm_BooleanIsoperimetry_hDist_insert_self_le_one
public import Theorems.Thm_BooleanIsoperimetry_hDist_self_insert_le_one
public import Theorems.Thm_BooleanIsoperimetry_eq_insert_of_hDist_le_one_of_not_mem_of_mem
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
    neighborhood 1 (coordinateUp i A) ⊆ coordinateUp i (neighborhood 1 A) := by
  intro y hy
  rw [mem_neighborhood_iff] at hy
  rcases hy with ⟨x, hx, hdist⟩
  by_cases hiy : i ∈ y
  · rw [coordinateUp_mem_of_mem i _ y hiy]
    by_cases hix : i ∈ x
    · rw [coordinateUp_mem_of_mem i A x hix] at hx
      rcases hx with hxA | hx_erase
      · exact Or.inl (mem_neighborhood_iff.mpr ⟨x, hxA, hdist⟩)
      · exact Or.inr (mem_neighborhood_iff.mpr
          ⟨x.erase i, hx_erase, hDist_erase_le_hDist i x y hdist⟩)
    · rw [coordinateUp_mem_of_not_mem i A x hix] at hx
      have hxy : y = insert i x := eq_insert_of_hDist_le_one_of_not_mem_of_mem hdist hix hiy
      subst hxy
      exact Or.inl (mem_neighborhood_iff.mpr ⟨insert i x, hx.2, hDist_self_le_one (insert i x)⟩)
  · rw [coordinateUp_mem_of_not_mem i _ y hiy]
    by_cases hix : i ∈ x
    · have hdist2 : hDist y x ≤ 1 := by rwa [hDist_comm]
      have hyx : x = insert i y := eq_insert_of_hDist_le_one_of_not_mem_of_mem hdist2 hiy hix
      subst hyx
      rw [coordinateUp_mem_of_mem i A _ (mem_insert_self _ _)] at hx
      rcases hx with hxA | hx_erase
      · exact ⟨mem_neighborhood_iff.mpr ⟨insert i y, hxA, hDist_insert_self_le_one i y⟩,
               mem_neighborhood_iff.mpr ⟨insert i y, hxA, hDist_self_le_one (insert i y)⟩⟩
      · rw [erase_insert hiy] at hx_erase
        exact ⟨mem_neighborhood_iff.mpr ⟨y, hx_erase, hDist_self_le_one y⟩,
               mem_neighborhood_iff.mpr ⟨y, hx_erase, hDist_self_insert_le_one i y⟩⟩
    · rw [coordinateUp_mem_of_not_mem i A x hix] at hx
      exact ⟨mem_neighborhood_iff.mpr ⟨x, hx.1, hdist⟩,
             mem_neighborhood_iff.mpr ⟨insert i x, hx.2, hDist_insert_le_hDist i x y hdist⟩⟩
end BooleanIsoperimetry
