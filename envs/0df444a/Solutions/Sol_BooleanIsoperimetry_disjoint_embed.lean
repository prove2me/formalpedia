-- Prove2me | solution 1 for BooleanIsoperimetry.disjoint_embed
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:44:12.815804+00:00
-- url     : https://prove2.me/submissions/1bfe695a-6dc0-40a8-8895-b40273e070ed

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
public import Theorems.Thm_BooleanIsoperimetry_mem_neighborhood_iff
attribute [local simp] BooleanIsoperimetry.mem_neighborhood_iff



set_option autoImplicit true
@[expose] public section
public section
open scoped BigOperators
open BooleanIsoperimetry
namespace BooleanIsoperimetry
theorem _root_.solution {N a b : ℕ} :
    Disjoint ((simplicialInitSeg N a).image embed0) ((simplicialInitSeg N b).image embed1) := by
  rw [Finset.disjoint_left]
  rintro z hz0 hz1
  simp only [Finset.mem_image] at hz0 hz1
  obtain ⟨x, _, hx⟩ := hz0
  obtain ⟨y, _, hy⟩ := hz1
  have hlast : Fin.last N ∈ embed1 y := Finset.mem_insert_self _ _
  rw [hy, ← hx] at hlast
  exact (last_not_mem_image_castSucc x) hlast
end BooleanIsoperimetry
