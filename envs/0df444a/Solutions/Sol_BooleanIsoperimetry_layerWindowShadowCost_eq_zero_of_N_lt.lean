-- Prove2me | solution 1 for BooleanIsoperimetry.layerWindowShadowCost_eq_zero_of_N_lt
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:32:30.828164+00:00
-- url     : https://prove2.me/submissions/88b63686-3291-49ef-9b1b-1ba4acb30afb

module
public import Definitions.Def_LeanPool_BooleanIsoperimetry_KruskalKatona
public import Definitions.Def_LeanPool_BooleanIsoperimetry_Cascade
public import Mathlib.Data.Rat.Cast.Order
public import Mathlib.Tactic.Linarith.Frontend
public import Mathlib.Tactic.NormNum.Abs
public import Mathlib.Tactic.NormNum.DivMod
public import Mathlib.Tactic.NormNum.OfScientific
public import Definitions.Def_LeanPool_BooleanIsoperimetry_LayerWindows
public import Theorems.Thm_BooleanIsoperimetry_layerCount_eq_zero_of_N_lt

set_option autoImplicit true
@[expose] public section
public section
open BooleanIsoperimetry
open Finset
namespace BooleanIsoperimetry
theorem _root_.solution {N r a : ℕ} (hNr : N < r) :
    layerWindowShadowCost N r a = 0 := by
  unfold layerWindowShadowCost
  exact layerCount_eq_zero_of_N_lt hNr (neighborhood 1 (simplicialInitSeg N a))
end BooleanIsoperimetry
