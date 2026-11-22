-- Prove2me | solution 1 for BooleanIsoperimetry.upperShadow_full
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:38:50.988177+00:00
-- url     : https://prove2.me/submissions/d515e562-18ae-4eec-b6f1-43db933cf9cb

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
public import Theorems.Thm_BooleanIsoperimetry_H_binomPrefix
public import Theorems.Thm_BooleanIsoperimetry_binomPrefix_succ


set_option autoImplicit true
@[expose] public section
public section
open scoped BigOperators
open BooleanIsoperimetry
namespace BooleanIsoperimetry
theorem _root_.solution (N r : ℕ) (hr : 1 ≤ r) :
    upperShadow N r (Nat.choose N r) = Nat.choose N (r + 1) := by
  unfold upperShadow
  have hsucc : binomPrefix N r + Nat.choose N r = binomPrefix N (r + 1) :=
    (binomPrefix_succ N r).symm
  rw [hsucc, H_binomPrefix N (r + 1) (by omega), binomPrefix_succ N (r + 1)]
  omega
end BooleanIsoperimetry
