-- Prove2me | solution 1 for BooleanIsoperimetry.layerPart_initSeg_uniform
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:33:07.172803+00:00
-- url     : https://prove2.me/submissions/f32e50cd-2092-4417-a3c0-d2335e4501da

module
public import Definitions.Def_LeanPool_BooleanIsoperimetry_KruskalKatona
public import Definitions.Def_LeanPool_BooleanIsoperimetry_Cascade
public import Mathlib.Data.Rat.Cast.Order
public import Mathlib.Tactic.Linarith.Frontend
public import Mathlib.Tactic.NormNum.Abs
public import Mathlib.Tactic.NormNum.DivMod
public import Mathlib.Tactic.NormNum.OfScientific
public import Definitions.Def_LeanPool_BooleanIsoperimetry_LayerWindows
public import Theorems.Thm_BooleanIsoperimetry_mem_neighborhood_iff
attribute [local simp] BooleanIsoperimetry.mem_neighborhood_iff



set_option autoImplicit true
@[expose] public section
public section
open BooleanIsoperimetry
open Finset
namespace BooleanIsoperimetry
theorem _root_.solution (N r a : ℕ) :
    ∀ x ∈ layerPart N r (simplicialInitSeg N a), x.card = r := by
  intro x hx
  simp only [layerPart, Finset.mem_filter] at hx
  exact hx.2
end BooleanIsoperimetry
