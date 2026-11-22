-- Prove2me | solution 1 for BooleanIsoperimetry.cascade_left_window_endpoints
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:39:25.734386+00:00
-- url     : https://prove2.me/submissions/95bca570-00ad-43e5-a12e-91f1b1b7e5f9

module
public import Definitions.Def_LeanPool_BooleanIsoperimetry_Macaulay
public import Definitions.Def_LeanPool_BooleanIsoperimetry_Shadow
public import Mathlib.Algebra.BigOperators.Intervals
public import Mathlib.Data.Rat.Cast.Order
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.NormNum.Abs
public import Mathlib.Tactic.NormNum.DivMod
public import Mathlib.Tactic.NormNum.OfScientific
public import Mathlib.Tactic.Ring.RingNF
public import Definitions.Def_LeanPool_BooleanIsoperimetry_Harper
public import Theorems.Thm_BooleanIsoperimetry_cascade_split_add


set_option autoImplicit true
@[expose] public section
public section
open scoped BigOperators
open BooleanIsoperimetry
namespace BooleanIsoperimetry
theorem _root_.solution {N a b p q : ℕ}
    (hcasc : CascadeSplit N (a + b) p q) (hpa : p ≤ a) :
    b ≤ q ∧ a - p = q - b := by
  have hsum : p + q = a + b := cascade_split_add hcasc
  omega
end BooleanIsoperimetry
