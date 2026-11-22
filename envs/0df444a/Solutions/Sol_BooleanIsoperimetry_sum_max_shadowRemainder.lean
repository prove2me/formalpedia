-- Prove2me | solution 1 for BooleanIsoperimetry.sum_max_shadowRemainder
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:33:11.320997+00:00
-- url     : https://prove2.me/submissions/b2585421-dfad-4dd0-b08c-a48bb64701fb

module
public import Definitions.Def_LeanPool_BooleanIsoperimetry_KruskalKatona
public import Definitions.Def_LeanPool_BooleanIsoperimetry_Cascade
public import Mathlib.Data.Rat.Cast.Order
public import Mathlib.Tactic.Linarith.Frontend
public import Mathlib.Tactic.NormNum.Abs
public import Mathlib.Tactic.NormNum.DivMod
public import Mathlib.Tactic.NormNum.OfScientific
public import Definitions.Def_LeanPool_BooleanIsoperimetry_LayerWindows
public import Theorems.Thm_BooleanIsoperimetry_layerCount_neighborhood_initSeg
public import Theorems.Thm_BooleanIsoperimetry_max_layerWindow_eq_union_card
public import Theorems.Thm_BooleanIsoperimetry_sum_layerCount_eq_card
public import Theorems.Thm_BooleanIsoperimetry_H_le_cube
public import Theorems.Thm_BooleanIsoperimetry_card_simplicialInitSeg


set_option autoImplicit true
@[expose] public section
public section
open BooleanIsoperimetry
open Finset
namespace BooleanIsoperimetry
theorem _root_.solution (N a b : ℕ) (hb : b ≤ 2 ^ N) :
    ∑ r ∈ Finset.range (N + 2),
        max (layerWindowShadowCost N r a) (layerWindowRemainder N r b)
      = max (H N a) b := by
  have hstep : ∀ r ∈ Finset.range (N + 2),
      max (layerWindowShadowCost N r a) (layerWindowRemainder N r b)
        = layerCount N r (simplicialInitSeg N (max (H N a) b)) := by
    intro r _
    unfold layerWindowShadowCost layerWindowRemainder
    rw [layerCount_neighborhood_initSeg, max_layerWindow_eq_union_card]
  rw [Finset.sum_congr rfl hstep, sum_layerCount_eq_card, card_simplicialInitSeg]
  exact min_eq_left (max_le (H_le_cube N a) hb)
end BooleanIsoperimetry
