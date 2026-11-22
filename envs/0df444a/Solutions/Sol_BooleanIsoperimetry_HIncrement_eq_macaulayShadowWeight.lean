-- Prove2me | solution 1 for BooleanIsoperimetry.HIncrement_eq_macaulayShadowWeight
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:38:27.097771+00:00
-- url     : https://prove2.me/submissions/2572a599-8a9b-4f65-bdf6-003163d492aa

module
public import Definitions.Def_LeanPool_BooleanIsoperimetry_Cascade
public import Mathlib.Order.Interval.Finset.Nat
public import Mathlib.Algebra.BigOperators.Intervals
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Data.Rat.Cast.Order
public import Mathlib.Tactic.Linarith.Frontend
public import Mathlib.Tactic.NormNum.Abs
public import Mathlib.Tactic.NormNum.DivMod
public import Mathlib.Tactic.NormNum.OfScientific
public import Definitions.Def_LeanPool_BooleanIsoperimetry_Macaulay
public import Theorems.Thm_P2M_BooleanIsoperimetry_HIncrement_eq_min__d487d18fa7b9
public import Theorems.Thm_BooleanIsoperimetry_HIncrement_zero
public import Theorems.Thm_BooleanIsoperimetry_rank_eq_zero_of_not_nonempty
public import Theorems.Thm_BooleanIsoperimetry_mem_neighborhood_iff
attribute [local simp] BooleanIsoperimetry.mem_neighborhood_iff



set_option autoImplicit true
@[expose] public section
public section
open scoped BigOperators
open BooleanIsoperimetry
namespace BooleanIsoperimetry
theorem _root_.solution {n : ℕ} (p : ℕ) (w : Cube n)
    (hw : rank w = p) :
    HIncrement n p = macaulayShadowWeight w := by
  unfold macaulayShadowWeight
  by_cases h : w.Nonempty
  · simp [h, HIncrement_eq_min' p w hw h]
  · rw [dif_neg h]
    have hp0 : p = 0 := rank_eq_zero_of_not_nonempty w hw h
    rw [hp0]
    exact HIncrement_zero n
end BooleanIsoperimetry
