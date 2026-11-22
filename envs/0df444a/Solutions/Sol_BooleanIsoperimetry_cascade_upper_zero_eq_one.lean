-- Prove2me | solution 1 for BooleanIsoperimetry.cascade_upper_zero_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:29:18.564629+00:00
-- url     : https://prove2.me/submissions/73a876ce-b36f-45f7-b577-1fee00a22edd

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
public import Theorems.Thm_BooleanIsoperimetry_one_le_binomPrefix_succ
public import Theorems.Thm_BooleanIsoperimetry_binomPrefix_succ
public import Theorems.Thm_BooleanIsoperimetry_binomPrefix_zero
public import Theorems.Thm_BooleanIsoperimetry_mem_neighborhood_iff
attribute [local simp] BooleanIsoperimetry.mem_neighborhood_iff



set_option autoImplicit true
@[expose] public section
public section
open scoped BigOperators
open BooleanIsoperimetry
namespace BooleanIsoperimetry
theorem _root_.solution {n q q0 q1 : ℕ}
    (h : CascadeSplit n q q0 q1) (hq_pos : 1 ≤ q) (hq1_zero : q1 = 0) :
    q = 1 := by
  rcases h with ⟨r, t, hr, _hq0, hq1⟩
  rcases hr with ⟨_hrle, _ht, hqeq, hcanon⟩
  rw [hq1] at hq1_zero
  unfold cascadeSlice1Value at hq1_zero
  rcases r with _ | r
  · simp [binomPrefix_zero] at hq1_zero
    simp [binomPrefix_zero] at hqeq
    have hcanon' : t < 1 := by
      rcases hcanon with hcanon | hcanon
      · simpa using hcanon
      · omega
    omega
  · rcases r with _ | r
    · simp [binomPrefix_zero, choosePred] at hq1_zero
      simp [binomPrefix_succ, binomPrefix_zero] at hqeq
      omega
    · have hpos := one_le_binomPrefix_succ n r
      simp [choosePred] at hq1_zero
      omega
end BooleanIsoperimetry
