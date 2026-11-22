-- Prove2me | solution 1 for BooleanIsoperimetry.harper_step_sum_form_of_window_shift
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:44:28.560906+00:00
-- url     : https://prove2.me/submissions/203d7ff7-949d-4754-8196-91a63d09459d

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
theorem _root_.solution (n : ℕ)
    {a b p q : ℕ}
    (hap : a ≤ p) (hqb : q ≤ b)
    (hwin :
      gShiftIntervalCount (n + 1) a p ≤
        gShiftIntervalCount (n + 1) q b) :
    H (n + 1) p + H (n + 1) q ≤ H (n + 1) a + H (n + 1) b := by
  have hpa := gShiftIntervalCount_eq_H_sub (n + 1) a p hap
  have hqb' := gShiftIntervalCount_eq_H_sub (n + 1) q b hqb
  rw [hpa, hqb'] at hwin
  have hHa : H (n + 1) a ≤ H (n + 1) p := H_mono hap
  have hHq : H (n + 1) q ≤ H (n + 1) b := H_mono hqb
  omega
end BooleanIsoperimetry
