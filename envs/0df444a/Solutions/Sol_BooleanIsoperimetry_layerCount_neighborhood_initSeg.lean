-- Prove2me | solution 1 for BooleanIsoperimetry.layerCount_neighborhood_initSeg
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:31:51.610993+00:00
-- url     : https://prove2.me/submissions/fa87d4e1-4525-4192-8be3-1b2170f9b68c

module
public import Definitions.Def_LeanPool_BooleanIsoperimetry_KruskalKatona
public import Definitions.Def_LeanPool_BooleanIsoperimetry_Cascade
public import Mathlib.Data.Rat.Cast.Order
public import Mathlib.Tactic.Linarith.Frontend
public import Mathlib.Tactic.NormNum.Abs
public import Mathlib.Tactic.NormNum.DivMod
public import Mathlib.Tactic.NormNum.OfScientific
public import Definitions.Def_LeanPool_BooleanIsoperimetry_LayerWindows
public import Theorems.Thm_BooleanIsoperimetry_neighborhood_initSeg_eq


set_option autoImplicit true
@[expose] public section
public section
open BooleanIsoperimetry
open Finset
namespace BooleanIsoperimetry
theorem _root_.solution (N r a : ℕ) :
    layerCount N r (neighborhood 1 (simplicialInitSeg N a)) =
      layerCount N r (simplicialInitSeg N (H N a)) := by
  rw [neighborhood_initSeg_eq]
end BooleanIsoperimetry
