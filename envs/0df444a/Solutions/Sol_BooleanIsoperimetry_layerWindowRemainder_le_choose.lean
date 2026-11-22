-- Prove2me | solution 1 for BooleanIsoperimetry.layerWindowRemainder_le_choose
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:42:09.757382+00:00
-- url     : https://prove2.me/submissions/4a2539a6-74b4-4515-8162-245092cab7d0

module
public import Definitions.Def_LeanPool_BooleanIsoperimetry_KruskalKatona
public import Definitions.Def_LeanPool_BooleanIsoperimetry_Cascade
public import Mathlib.Data.Rat.Cast.Order
public import Mathlib.Tactic.Linarith.Frontend
public import Mathlib.Tactic.NormNum.Abs
public import Mathlib.Tactic.NormNum.DivMod
public import Mathlib.Tactic.NormNum.OfScientific
public import Definitions.Def_LeanPool_BooleanIsoperimetry_LayerWindows
public import Theorems.Thm_BooleanIsoperimetry_layerPart_initSeg_uniform
public import Theorems.Thm_BooleanIsoperimetry_card_le_choose_of_uniform


set_option autoImplicit true
@[expose] public section
public section
open BooleanIsoperimetry
open Finset
namespace BooleanIsoperimetry
theorem _root_.solution (N r a : ℕ) :
    layerWindowRemainder N r a ≤ Nat.choose N r := by
  unfold layerWindowRemainder layerCount
  exact card_le_choose_of_uniform (layerPart_initSeg_uniform N r a)
end BooleanIsoperimetry
