-- Prove2me | solution 1 for BooleanIsoperimetry.slice1_union_embed
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:44:12.268124+00:00
-- url     : https://prove2.me/submissions/ec6e6828-b0be-4a64-b49b-f071ac6b5f00

module
public import Definitions.Def_LeanPool_BooleanIsoperimetry_Cascade
public import Definitions.Def_LeanPool_BooleanIsoperimetry_Compression
public import Definitions.Def_LeanPool_BooleanIsoperimetry_Macaulay
public import Mathlib.Data.Rat.Cast.Order
public import Mathlib.Tactic.NormNum.Abs
public import Mathlib.Tactic.NormNum.DivMod
public import Mathlib.Tactic.NormNum.OfScientific
public import Mathlib.Tactic.NormNum.Pow
public import Definitions.Def_LeanPool_BooleanIsoperimetry_Shadow
public import Theorems.Thm_BooleanIsoperimetry_last_not_mem_image_castSucc
public import Theorems.Thm_BooleanIsoperimetry_embed1_injective
public import Theorems.Thm_BooleanIsoperimetry_mem_neighborhood_iff
attribute [local simp] BooleanIsoperimetry.mem_neighborhood_iff



set_option autoImplicit true
@[expose] public section
public section
open scoped BigOperators
open BooleanIsoperimetry
namespace BooleanIsoperimetry
theorem _root_.solution {N a b : ℕ} :
    slice1 ((simplicialInitSeg N a).image embed0 ∪ (simplicialInitSeg N b).image embed1) =
      simplicialInitSeg N b := by
  ext x
  simp only [slice1, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union,
    Finset.mem_image]
  constructor
  · rintro (⟨y, hy, hxy⟩ | ⟨y, hy, hxy⟩)
    · have hlast : Fin.last N ∈ embed1 x := Finset.mem_insert_self _ _
      rw [← hxy] at hlast
      exact ((last_not_mem_image_castSucc y) hlast).elim
    · rwa [embed1_injective hxy] at hy
  · intro hx
    exact Or.inr ⟨x, hx, rfl⟩
end BooleanIsoperimetry
