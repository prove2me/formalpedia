-- Prove2me | solution 1 for BooleanIsoperimetry.upperShadow_mono
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:38:04.765192+00:00
-- url     : https://prove2.me/submissions/93cff5c1-fc25-4962-962b-739be891d99a

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
public import Theorems.Thm_BooleanIsoperimetry_H_mono


set_option autoImplicit true
@[expose] public section
public section
open scoped BigOperators
open BooleanIsoperimetry
namespace BooleanIsoperimetry
theorem _root_.solution (N r : ℕ) {t t' : ℕ} (h : t ≤ t') :
    upperShadow N r t ≤ upperShadow N r t' := by
  unfold upperShadow
  exact Nat.sub_le_sub_right (H_mono (by omega)) _
end BooleanIsoperimetry
