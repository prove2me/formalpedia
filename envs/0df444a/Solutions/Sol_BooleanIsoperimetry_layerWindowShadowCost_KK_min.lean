-- Prove2me | solution 1 for BooleanIsoperimetry.layerWindowShadowCost_KK_min
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:43:16.341971+00:00
-- url     : https://prove2.me/submissions/500a07c8-ce05-4ad8-b243-0b76e8ae4ad1

module
public import Definitions.Def_LeanPool_BooleanIsoperimetry_KruskalKatona
public import Definitions.Def_LeanPool_BooleanIsoperimetry_Cascade
public import Mathlib.Data.Rat.Cast.Order
public import Mathlib.Tactic.Linarith.Frontend
public import Mathlib.Tactic.NormNum.Abs
public import Mathlib.Tactic.NormNum.DivMod
public import Mathlib.Tactic.NormNum.OfScientific
public import Definitions.Def_LeanPool_BooleanIsoperimetry_LayerWindows
public import Theorems.Thm_BooleanIsoperimetry_card_le_choose_of_uniform
public import Theorems.Thm_BooleanIsoperimetry_upperShadowVal_numeric_min


set_option autoImplicit true
@[expose] public section
public section
open BooleanIsoperimetry
open Finset
namespace BooleanIsoperimetry
theorem _root_.solution {N r : ℕ} (hr : 1 ≤ r) {A : Finset (Cube N)}
    (hA : ∀ x ∈ A, x.card = r) :
    upperShadowVal N r A.card ≤ (upperLayerShadow N r A).card :=
  upperShadowVal_numeric_min hr (card_le_choose_of_uniform hA) hA rfl
end BooleanIsoperimetry
