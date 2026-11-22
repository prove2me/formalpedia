-- Prove2me | solution 1 for BooleanIsoperimetry.layerWindowRemainder_eq_zero_of_N_lt
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:32:30.199441+00:00
-- url     : https://prove2.me/submissions/cca47fa6-7311-42e4-8f74-2ff038e0e48f

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
    layerWindowRemainder N r a = 0 := by
  unfold layerWindowRemainder
  exact layerCount_eq_zero_of_N_lt hNr (simplicialInitSeg N a)
end BooleanIsoperimetry
