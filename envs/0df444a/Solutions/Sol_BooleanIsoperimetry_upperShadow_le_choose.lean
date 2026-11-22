-- Prove2me | solution 1 for BooleanIsoperimetry.upperShadow_le_choose
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:44:11.287239+00:00
-- url     : https://prove2.me/submissions/292187f5-faec-4e20-81ee-46751d88242e

module
public import Definitions.Def_LeanPool_BooleanIsoperimetry_Cascade
public import Definitions.Def_LeanPool_BooleanIsoperimetry_Compression
public import Definitions.Def_LeanPool_BooleanIsoperimetry_Macaulay
public import Mathlib.Data.Rat.Cast.Order
public import Mathlib.Tactic.NormNum.Abs
public import Mathlib.Tactic.NormNum.DivMod
public import Mathlib.Tactic.NormNum.OfScientific
public import Mathlib.Tactic.NormNum.Pow
public import Definitions.Def_LeanPool_BooleanIsoperimetry_Shadow
public import Theorems.Thm_BooleanIsoperimetry_upperShadow_mono
public import Theorems.Thm_BooleanIsoperimetry_upperShadow_full

set_option autoImplicit true
@[expose] public section
public section
open scoped BigOperators
open BooleanIsoperimetry
namespace BooleanIsoperimetry
theorem _root_.solution (N r t : ℕ) (hr : 1 ≤ r)
    (ht : t ≤ Nat.choose N r) :
    upperShadow N r t ≤ Nat.choose N (r + 1) := by
  calc upperShadow N r t ≤ upperShadow N r (Nat.choose N r) := upperShadow_mono N r ht
    _ = Nat.choose N (r + 1) := upperShadow_full N r hr
end BooleanIsoperimetry
