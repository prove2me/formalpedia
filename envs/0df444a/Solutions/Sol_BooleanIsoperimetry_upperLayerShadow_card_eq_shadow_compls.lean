-- Prove2me | solution 1 for BooleanIsoperimetry.upperLayerShadow_card_eq_shadow_compls
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:32:59.395543+00:00
-- url     : https://prove2.me/submissions/7017f8d8-3133-4486-9d50-13981aff8e2c

module
public import Definitions.Def_LeanPool_BooleanIsoperimetry_Cube
public import Mathlib.Combinatorics.Colex
public import Mathlib.Combinatorics.SetFamily.Shadow
public import Definitions.Def_LeanPool_BooleanIsoperimetry_Macaulay
public import Mathlib.Combinatorics.SetFamily.KruskalKatona
public import Mathlib.Data.Rat.Cast.Order
public import Mathlib.Tactic.NormNum.Abs
public import Mathlib.Tactic.NormNum.DivMod
public import Mathlib.Tactic.NormNum.OfScientific
public import Mathlib.Tactic.NormNum.Pow
public import Definitions.Def_LeanPool_BooleanIsoperimetry_KruskalKatona
public import Theorems.Thm_BooleanIsoperimetry_upShadow_eq_upperLayerShadow_of_uniform

set_option autoImplicit true
@[expose] public section
public section
open scoped BigOperators
open scoped FinsetFamily
open Finset
open Finset.Colex
open BooleanIsoperimetry
namespace BooleanIsoperimetry
theorem _root_.solution {N r : ℕ} {A : Finset (Cube N)}
    (hA : ∀ x ∈ A, x.card = r) :
    (upperLayerShadow N r A).card = (Finset.shadow Aᶜˢ).card := by
  rw [← upShadow_eq_upperLayerShadow_of_uniform hA]
  rw [Finset.shadow_compls, Finset.card_compls]
end BooleanIsoperimetry
