-- Prove2me | solution 1 for BooleanIsoperimetry.slice1_initialSlicePair
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:32:58.743647+00:00
-- url     : https://prove2.me/submissions/0e6948c5-0e97-48d8-a00f-0ccf7bb5c9c5

module
public import Definitions.Def_LeanPool_BooleanIsoperimetry_Cube
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Data.Rat.Cast.Order
public import Mathlib.Tactic.NormNum.Abs
public import Mathlib.Tactic.NormNum.DivMod
public import Mathlib.Tactic.NormNum.OfScientific
public import Mathlib.Tactic.NormNum.Pow
public import Definitions.Def_LeanPool_BooleanIsoperimetry_SimplicialCompression
public import Theorems.Thm_BooleanIsoperimetry_initialSlicePair_last_not_mem_embed0
public import Theorems.Thm_BooleanIsoperimetry_initialSlicePair_embed1_injective
public import Theorems.Thm_BooleanIsoperimetry_mem_neighborhood_iff
attribute [local simp] BooleanIsoperimetry.mem_neighborhood_iff



set_option autoImplicit true
@[expose] public section
public section
open scoped BigOperators
open Finset
open BooleanIsoperimetry
namespace BooleanIsoperimetry
theorem _root_.solution {N a b : ℕ} :
    slice1 (initialSlicePair N a b) = simplicialInitSeg N b := by
  ext x
  simp only [slice1, initialSlicePair, Finset.mem_filter, Finset.mem_univ, true_and,
    Finset.mem_union, Finset.mem_image]
  constructor
  · rintro (⟨y, _hy, hxy⟩ | ⟨y, hy, hxy⟩)
    · have hlast : Fin.last N ∈ embed1 x := by simp [embed1]
      rw [← hxy] at hlast
      exact (initialSlicePair_last_not_mem_embed0 y hlast).elim
    · have hyx : y = x := initialSlicePair_embed1_injective hxy
      simpa [← hyx] using hy
  · intro hx
    exact Or.inr ⟨x, hx, rfl⟩
end BooleanIsoperimetry
