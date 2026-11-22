-- Prove2me | solution 1 for BooleanIsoperimetry.upperShadow_numeric_min
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:45:12.517128+00:00
-- url     : https://prove2.me/submissions/758fc769-c6eb-4cbc-98cc-80d72df7dffb

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
public import Theorems.Thm_BooleanIsoperimetry_upperShadowVal_numeric_min


set_option autoImplicit true
@[expose] public section
public section
open scoped BigOperators
open Finset
open BooleanIsoperimetry
namespace BooleanIsoperimetry
theorem _root_.solution {N r t : ℕ} (hr : 1 ≤ r)
    (ht : t ≤ Nat.choose N r) {A : Finset (Cube N)}
    (hA : ∀ x ∈ A, x.card = r) (hcard : A.card = t) :
    upperShadow N r t ≤ (upperLayerShadow N r A).card := by
  rw [upperShadow_eq_upperShadowVal]
  exact upperShadowVal_numeric_min hr ht hA hcard
end BooleanIsoperimetry
