-- Prove2me | solution 1 for BooleanIsoperimetry.harper_macaulay_LE_sum_q_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:39:44.614802+00:00
-- url     : https://prove2.me/submissions/9c04f49d-5b48-4926-bb96-f1ce29741131

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
public import Theorems.Thm_BooleanIsoperimetry_cascade_split_q_zero_total_le_one
public import Theorems.Thm_BooleanIsoperimetry_H_one
public import Theorems.Thm_BooleanIsoperimetry_H_zero
public import Theorems.Thm_BooleanIsoperimetry_cascade_split_add
public import Theorems.Thm_BooleanIsoperimetry_mem_neighborhood_iff
attribute [local simp] BooleanIsoperimetry.mem_neighborhood_iff



set_option autoImplicit true
@[expose] public section
public section
open scoped BigOperators
open BooleanIsoperimetry
namespace BooleanIsoperimetry
theorem _root_.solution (n : ℕ)
    {a b p : ℕ}
    (hcasc : CascadeSplit (n + 1) (a + b) p 0)
    (hba : b ≤ a) :
    H (n + 1) p + H (n + 1) 0 ≤ H (n + 1) a + H (n + 1) b := by
  have htotal : a + b ≤ 1 := cascade_split_q_zero_total_le_one hcasc
  have hp_eq : p = a + b := by
    have hsum := cascade_split_add hcasc
    omega
  subst p
  have hb_zero : b = 0 := by omega
  subst b
  have ha_val : a = 0 ∨ a = 1 := by omega
  rcases ha_val with rfl | rfl
  · simp [H_zero]
  · simp [H_zero, H_one]
end BooleanIsoperimetry
