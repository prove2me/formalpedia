-- Prove2me | solution 1 for BooleanIsoperimetry.upperShadow_eq_card_upperLayerShadow
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:45:09.261774+00:00
-- url     : https://prove2.me/submissions/692f6d6a-af3c-4ca7-999d-90dede875b57

module
public import Definitions.Def_LeanPool_BooleanIsoperimetry_Shadow
public import Definitions.Def_LeanPool_BooleanIsoperimetry_KruskalKatona
public import Mathlib.Data.Rat.Cast.Order
public import Mathlib.Tactic.NormNum.Abs
public import Mathlib.Tactic.NormNum.DivMod
public import Mathlib.Tactic.NormNum.OfScientific
public import Mathlib.Tactic.NormNum.Pow
public import Definitions.Def_LeanPool_BooleanIsoperimetry_SetFamilyShadow
public import Theorems.Thm_BooleanIsoperimetry_upperShadow_eq_upperShadowVal
public import Theorems.Thm_BooleanIsoperimetry_upperShadowVal_eq_card_upperLayerShadow


set_option autoImplicit true
@[expose] public section
public section
open scoped BigOperators
open Finset
open BooleanIsoperimetry
namespace BooleanIsoperimetry
theorem _root_.solution {N r t : ℕ} (hr : 1 ≤ r)
    (ht : t ≤ Nat.choose N r) :
    upperShadow N r t = (upperLayerShadow N r (layerInitSeg N r t)).card := by
  rw [upperShadow_eq_upperShadowVal]
  exact upperShadowVal_eq_card_upperLayerShadow hr ht
end BooleanIsoperimetry
