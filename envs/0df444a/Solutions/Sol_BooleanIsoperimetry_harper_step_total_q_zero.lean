-- Prove2me | solution 1 for BooleanIsoperimetry.harper_step_total_q_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:44:23.394796+00:00
-- url     : https://prove2.me/submissions/786af484-ed3f-49f2-8ff2-27a31e676791

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
public import Theorems.Thm_BooleanIsoperimetry_mem_neighborhood_iff
attribute [local simp] BooleanIsoperimetry.mem_neighborhood_iff



set_option autoImplicit true
@[expose] public section
public section
open scoped BigOperators
open BooleanIsoperimetry
namespace BooleanIsoperimetry
theorem _root_.solution (n : ℕ) {a b p : ℕ}
    (hcasc : CascadeSplit (n + 1) (a + b) p 0) :
    H (n + 2) (a + b) ≤ boundaryCostH (n + 1) a b := by
  have h_le_one : a + b ≤ 1 := cascade_split_q_zero_total_le_one hcasc
  have h0 : a = 0 ∨ a = 1 := by omega
  have h1 : b = 0 ∨ b = 1 := by omega
  rcases h0 with rfl | rfl
  · rcases h1 with rfl | rfl
    · simp [H_zero, boundaryCostH]
    · simp [H_zero, H_one, boundaryCostH]
  · rcases h1 with rfl | rfl
    · simp [H_zero, H_one, boundaryCostH]
    · omega
end BooleanIsoperimetry
