-- Prove2me | solution 1 for BooleanIsoperimetry.upperShadow_eq_upperShadowVal
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:26:50.99185+00:00
-- url     : https://prove2.me/submissions/d4170374-258d-4121-a9e5-f97dd5b8346c

module
public import Definitions.Def_LeanPool_BooleanIsoperimetry_Shadow
public import Definitions.Def_LeanPool_BooleanIsoperimetry_KruskalKatona
public import Mathlib.Data.Rat.Cast.Order
public import Mathlib.Tactic.NormNum.Abs
public import Mathlib.Tactic.NormNum.DivMod
public import Mathlib.Tactic.NormNum.OfScientific
public import Mathlib.Tactic.NormNum.Pow
public import Definitions.Def_LeanPool_BooleanIsoperimetry_SetFamilyShadow

set_option autoImplicit true
@[expose] public section
public section
open scoped BigOperators
open Finset
open BooleanIsoperimetry
namespace BooleanIsoperimetry
theorem _root_.solution (N r t : ℕ) :
    upperShadow N r t = upperShadowVal N r t := rfl
end BooleanIsoperimetry
