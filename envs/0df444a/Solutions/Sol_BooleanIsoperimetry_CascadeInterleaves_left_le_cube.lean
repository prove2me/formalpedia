-- Prove2me | solution 1 for BooleanIsoperimetry.CascadeInterleaves.left_le_cube
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:45:00.974996+00:00
-- url     : https://prove2.me/submissions/4b675b96-2388-498f-8511-080800cf7e24

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
public import Theorems.Thm_BooleanIsoperimetry_CascadeInterleaves_cascade
public import Theorems.Thm_BooleanIsoperimetry_cascade_p_le


set_option autoImplicit true
@[expose] public section
public section
open scoped BigOperators
open BooleanIsoperimetry
namespace BooleanIsoperimetry
namespace CascadeInterleaves
theorem _root_.solution {n p q a b : ℕ}
    (h_inter : CascadeInterleaves n p q a b) :
    p ≤ 2 ^ n :=
  cascade_p_le h_inter.cascade
end CascadeInterleaves
end BooleanIsoperimetry
