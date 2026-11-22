-- Prove2me | solution 1 for BooleanIsoperimetry.slice0_union_embed
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:44:11.771536+00:00
-- url     : https://prove2.me/submissions/228024a9-17f2-42d8-bb01-4f32e92a8ce4

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
public import Theorems.Thm_BooleanIsoperimetry_embed0_injective
public import Theorems.Thm_BooleanIsoperimetry_mem_neighborhood_iff
attribute [local simp] BooleanIsoperimetry.mem_neighborhood_iff



set_option autoImplicit true
@[expose] public section
public section
open scoped BigOperators
open BooleanIsoperimetry
namespace BooleanIsoperimetry
theorem _root_.solution {N a b : ℕ} :
    slice0 ((simplicialInitSeg N a).image embed0 ∪ (simplicialInitSeg N b).image embed1) =
      simplicialInitSeg N a := by
  ext x
  simp only [slice0, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union,
    Finset.mem_image]
  constructor
  · rintro (⟨y, hy, hxy⟩ | ⟨y, hy, hxy⟩)
    · rwa [embed0_injective hxy] at hy
    · have hlast : Fin.last N ∈ embed1 y := Finset.mem_insert_self _ _
      rw [hxy] at hlast
      exact ((last_not_mem_image_castSucc x) hlast).elim
  · intro hx
    exact Or.inl ⟨x, hx, rfl⟩
end BooleanIsoperimetry
