-- Prove2me | solution 1 for BooleanIsoperimetry.gShiftIntervalCount_add_adjacent
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:44:39.74845+00:00
-- url     : https://prove2.me/submissions/14385b5f-9de1-4c4c-81f4-4d6ffd86b56b

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
public import Theorems.Thm_BooleanIsoperimetry_gShiftIntervalCount_eq_H_sub
public import Theorems.Thm_BooleanIsoperimetry_H_mono


set_option autoImplicit true
@[expose] public section
public section
open scoped BigOperators
open BooleanIsoperimetry
namespace BooleanIsoperimetry
theorem _root_.solution (n lo mid hi : ℕ)
    (h1 : lo ≤ mid) (h2 : mid ≤ hi) :
    gShiftIntervalCount n lo mid + gShiftIntervalCount n mid hi
      = gShiftIntervalCount n lo hi := by
  rw [gShiftIntervalCount_eq_H_sub n lo mid h1,
      gShiftIntervalCount_eq_H_sub n mid hi h2,
      gShiftIntervalCount_eq_H_sub n lo hi (h1.trans h2)]
  have hm1 : H n lo ≤ H n mid := H_mono h1
  have hm2 : H n mid ≤ H n hi := H_mono h2
  omega
end BooleanIsoperimetry
