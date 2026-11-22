-- Prove2me | solution 1 for BooleanIsoperimetry.max_layerWindow_eq_union_card
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:24:16.945931+00:00
-- url     : https://prove2.me/submissions/84d1fa35-bee6-485d-9c72-3256489f0c93

module
public import Definitions.Def_LeanPool_BooleanIsoperimetry_KruskalKatona
public import Definitions.Def_LeanPool_BooleanIsoperimetry_Cascade
public import Mathlib.Data.Rat.Cast.Order
public import Mathlib.Tactic.Linarith.Frontend
public import Mathlib.Tactic.NormNum.Abs
public import Mathlib.Tactic.NormNum.DivMod
public import Mathlib.Tactic.NormNum.OfScientific
public import Definitions.Def_LeanPool_BooleanIsoperimetry_LayerWindows
public import Theorems.Thm_BooleanIsoperimetry_initSeg_nested


set_option autoImplicit true
@[expose] public section
public section
open BooleanIsoperimetry
open Finset
namespace BooleanIsoperimetry
theorem _root_.solution (N r X Y : ℕ) :
    max (layerCount N r (simplicialInitSeg N X)) (layerCount N r (simplicialInitSeg N Y)) =
    layerCount N r (simplicialInitSeg N (max X Y)) := by
  rcases le_total X Y with hXY | hYX
  · rw [max_eq_right hXY]
    have hsub : simplicialInitSeg N X ⊆ simplicialInitSeg N Y :=
      initSeg_nested hXY
    have hsub_layer :
        layerPart N r (simplicialInitSeg N X) ⊆ layerPart N r (simplicialInitSeg N Y) :=
      Finset.filter_subset_filter _ hsub
    unfold layerCount
    rw [max_eq_right (Finset.card_le_card hsub_layer)]
  · rw [max_eq_left hYX]
    have hsub : simplicialInitSeg N Y ⊆ simplicialInitSeg N X :=
      initSeg_nested hYX
    have hsub_layer :
        layerPart N r (simplicialInitSeg N Y) ⊆ layerPart N r (simplicialInitSeg N X) :=
      Finset.filter_subset_filter _ hsub
    unfold layerCount
    rw [max_eq_left (Finset.card_le_card hsub_layer)]
end BooleanIsoperimetry
