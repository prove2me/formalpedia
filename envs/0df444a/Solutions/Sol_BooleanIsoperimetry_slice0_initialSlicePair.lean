-- Prove2me | solution 1 for BooleanIsoperimetry.slice0_initialSlicePair
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:32:36.238701+00:00
-- url     : https://prove2.me/submissions/35522102-2228-41a0-a824-06851d76f3df

module
public import Definitions.Def_LeanPool_BooleanIsoperimetry_Cube
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Data.Rat.Cast.Order
public import Mathlib.Tactic.NormNum.Abs
public import Mathlib.Tactic.NormNum.DivMod
public import Mathlib.Tactic.NormNum.OfScientific
public import Mathlib.Tactic.NormNum.Pow
public import Definitions.Def_LeanPool_BooleanIsoperimetry_SimplicialCompression
public import Theorems.Thm_BooleanIsoperimetry_initialSlicePair_embed0_injective
public import Theorems.Thm_BooleanIsoperimetry_initialSlicePair_last_not_mem_embed0
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
    slice0 (initialSlicePair N a b) = simplicialInitSeg N a := by
  ext x
  simp only [slice0, initialSlicePair, Finset.mem_filter, Finset.mem_univ, true_and,
    Finset.mem_union, Finset.mem_image]
  constructor
  · rintro (⟨y, hy, hxy⟩ | ⟨y, _hy, hxy⟩)
    · have hyx : y = x := initialSlicePair_embed0_injective hxy
      simpa [← hyx] using hy
    · have hlast : Fin.last N ∈ embed1 y := by simp [embed1]
      rw [hxy] at hlast
      exact (initialSlicePair_last_not_mem_embed0 x hlast).elim
  · intro hx
    exact Or.inl ⟨x, hx, rfl⟩
end BooleanIsoperimetry
