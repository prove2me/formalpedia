-- Prove2me | solution 1 for BooleanIsoperimetry.cascade_split_q_zero_total_le_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:23:39.624117+00:00
-- url     : https://prove2.me/submissions/f434c57e-4b2b-4166-9cd3-15f7ef769d41

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
public import Theorems.Thm_BooleanIsoperimetry_binomPrefix_succ
public import Theorems.Thm_BooleanIsoperimetry_binomPrefix_zero
public import Theorems.Thm_BooleanIsoperimetry_mem_neighborhood_iff
public import Theorems.Thm_BooleanIsoperimetry_one_le_binomPrefix_succ
attribute [local simp] BooleanIsoperimetry.mem_neighborhood_iff



set_option autoImplicit true
@[expose] public section
public section
open scoped BigOperators
open BooleanIsoperimetry
namespace BooleanIsoperimetry
theorem _root_.solution {n k p : ℕ}
    (h : CascadeSplit n k p 0) : k ≤ 1 := by
  rcases h with ⟨r, t, hc, _hp, hq⟩
  rcases hc with ⟨_hrle, ht, hk, hcanon⟩
  rcases r with _ | r
  · simp [cascadeSlice1Value, binomPrefix_zero] at hq
    simp [binomPrefix_zero] at hk
    have ht' : t ≤ 1 := by simpa using ht
    omega
  · rcases r with _ | r
    · simp [cascadeSlice1Value, binomPrefix_zero, choosePred] at hq
      simp [binomPrefix_succ, binomPrefix_zero] at hk
      omega
    · have hpos := one_le_binomPrefix_succ n r
      simp [cascadeSlice1Value, choosePred] at hq
      omega
end BooleanIsoperimetry
