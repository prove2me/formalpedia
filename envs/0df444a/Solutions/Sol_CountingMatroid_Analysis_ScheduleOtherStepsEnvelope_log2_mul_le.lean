-- Prove2me | solution 1 for CountingMatroid.Analysis.ScheduleOtherStepsEnvelope.log2_mul_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-24T11:46:05.17588+00:00
-- url     : https://prove2.me/submissions/179513a0-6a60-4222-9457-45a3b16f9a97

import Definitions.Def_CountingMatroidSupport_Computation_Charged
import Definitions.Def_CountingMatroidSupport_Computation_Cost
import Definitions.Def_CountingMatroidSupport_Computation_Dict
import Definitions.Def_CountingMatroidSupport_Computation_Heap
import Definitions.Def_CountingMatroidSupport_Computation_Machine
import Definitions.Def_CountingMatroidSupport_Computation_Num
import Definitions.Def_CountingMatroidSupport_Computation_Queue
import Definitions.Def_CountingMatroidSupport_Computation_Rand
import Definitions.Def_CountingMatroidSupport_Computation_Roster
import Definitions.Def_CountingMatroidSupport_Computation_Slot
import Definitions.Def_CountingMatroidSupport_Computation_Space
import Definitions.Def_CountingMatroidSupport_Computation_Std
import Definitions.Def_CountingMatroid_Analysis_ScheduleOpeningCost
import Definitions.Def_CountingMatroid_Analysis_ScheduleThermalSetupCost
import Definitions.Def_CountingMatroid_Model_Operations
import Definitions.Def_CountingMatroid_Model_Prelude
import Definitions.Def_CountingMatroid_Model_Program
import Definitions.Def_CountingMatroid_Model_Run
import Definitions.Def_CountingMatroid_Model_Subroutines
import Lean
import Mathlib.Algebra.BigOperators.Group.Finset.Defs
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Algebra.Order.Floor.Defs
import Mathlib.Algebra.Order.Group.Int
import Mathlib.Combinatorics.Matroid.Rank.ENat
import Mathlib.Data.BitVec
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.List.Basic
import Mathlib.Data.List.Nodup
import Mathlib.Data.List.Sort
import Mathlib.Data.Multiset.Basic
import Mathlib.Data.Nat.Log
import Mathlib.Data.Rat.Defs
import Mathlib.Data.Real.Basic
import Mathlib.Order.Interval.Set.Basic
import Mathlib.Probability.ProbabilityMassFunction.Constructions
import Mathlib.Tactic.Abel
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Push
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Ring.RingNF

set_option autoImplicit false

namespace CountingMatroid.Analysis.ScheduleOtherStepsEnvelope
end CountingMatroid.Analysis.ScheduleOtherStepsEnvelope
open CountingMatroid CountingMatroid.Analysis CountingMatroid.Analysis.ScheduleOtherStepsEnvelope

open CountingMatroid.Model
open CountingMatroid.Model.Subroutines

/-- INTERNAL: A product's binary length is at most the sum of the factor
lengths, with one carry bit. -/
theorem solution (a b : ℕ) :
    (a * b).log2 ≤ a.log2 + b.log2 + 1 := by
  simp only [Nat.log2_eq_log_two]
  by_cases ha : a = 0
  · simp [ha]
  by_cases hb : b = 0
  · simp [hb]
  have ha' : a < 2 ^ (Nat.log 2 a + 1) := by
    simpa only [Nat.succ_eq_add_one] using Nat.lt_pow_succ_log_self Nat.one_lt_two a
  have hb' : b < 2 ^ (Nat.log 2 b + 1) := by
    simpa only [Nat.succ_eq_add_one] using Nat.lt_pow_succ_log_self Nat.one_lt_two b
  have hp : a * b < 2 ^ (Nat.log 2 a + Nat.log 2 b + 2) := by
    calc
      a * b < 2 ^ (Nat.log 2 a + 1) * b := Nat.mul_lt_mul_of_pos_right ha' (Nat.pos_of_ne_zero hb)
      _ ≤ 2 ^ (Nat.log 2 a + 1) * 2 ^ (Nat.log 2 b + 1) :=
        Nat.mul_le_mul_left _ hb'.le
      _ = 2 ^ (Nat.log 2 a + Nat.log 2 b + 2) := by ring
  have hlog := (Nat.log_lt_iff_lt_pow Nat.one_lt_two (Nat.mul_ne_zero ha hb)).2 hp
  omega
