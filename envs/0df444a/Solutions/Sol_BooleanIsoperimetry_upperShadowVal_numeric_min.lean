-- Prove2me | solution 1 for BooleanIsoperimetry.upperShadowVal_numeric_min
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:41:11.225818+00:00
-- url     : https://prove2.me/submissions/acb73329-4831-4639-a29f-87c0250b9e21

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
public import Theorems.Thm_BooleanIsoperimetry_upperShadowVal_eq_card_upperLayerShadow
public import Theorems.Thm_BooleanIsoperimetry_upperLayerShadow_min

set_option autoImplicit true
@[expose] public section
public section
open scoped BigOperators
open scoped FinsetFamily
open Finset
open Finset.Colex
open BooleanIsoperimetry
namespace BooleanIsoperimetry
theorem _root_.solution {N r t : ℕ} (hr : 1 ≤ r)
    (ht : t ≤ Nat.choose N r) {A : Finset (Cube N)}
    (hA : ∀ x ∈ A, x.card = r) (hcard : A.card = t) :
    upperShadowVal N r t ≤ (upperLayerShadow N r A).card := by
  rw [upperShadowVal_eq_card_upperLayerShadow hr ht, ← hcard]
  exact upperLayerShadow_min hA
end BooleanIsoperimetry
