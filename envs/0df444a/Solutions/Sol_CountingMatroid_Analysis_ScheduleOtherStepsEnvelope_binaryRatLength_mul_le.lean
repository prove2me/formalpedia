-- Prove2me | solution 1 for CountingMatroid.Analysis.ScheduleOtherStepsEnvelope.binaryRatLength_mul_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-24T11:47:19.39812+00:00
-- url     : https://prove2.me/submissions/de60d064-5169-4dcf-bb9b-eff201b9f658

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
import Theorems.Thm_CountingMatroid_Analysis_ScheduleOtherStepsEnvelope_log2_mul_le

set_option autoImplicit false

namespace CountingMatroid.Analysis.ScheduleOtherStepsEnvelope
end CountingMatroid.Analysis.ScheduleOtherStepsEnvelope
open CountingMatroid CountingMatroid.Analysis CountingMatroid.Analysis.ScheduleOtherStepsEnvelope

open CountingMatroid.Model
open CountingMatroid.Model.Subroutines

/-- INTERNAL: Multiplying two reduced rational numbers adds at most their
binary encoding lengths. -/
theorem solution (q s : ℚ) :
    binaryRatLength (q * s) ≤ binaryRatLength q + binaryRatLength s := by
  have hg : 0 < (q.num * s.num).natAbs.gcd (q.den * s.den) :=
    Nat.gcd_pos_of_pos_right _ (Nat.mul_pos q.den_pos s.den_pos)
  simp only [Int.natAbs_mul] at hg
  have hnumEq := congrArg Int.natAbs (Rat.num_mul_num_eq_num_mul_gcd q s)
  simp only [Int.natAbs_mul, Int.natAbs_natCast] at hnumEq
  have hnum : (q * s).num.natAbs ≤ q.num.natAbs * s.num.natAbs := by
    calc
      (q * s).num.natAbs ≤ (q * s).num.natAbs *
          (q.num.natAbs * s.num.natAbs).gcd (q.den * s.den) :=
        Nat.le_mul_of_pos_right _ hg
      _ = q.num.natAbs * s.num.natAbs := hnumEq.symm
  have hden : (q * s).den ≤ q.den * s.den :=
    Nat.le_of_dvd (Nat.mul_pos q.den_pos s.den_pos) (Rat.mul_den_dvd q s)
  have hnlog : (q * s).num.natAbs.log2 ≤
      q.num.natAbs.log2 + s.num.natAbs.log2 + 1 := by
    have hm := log2_mul_le q.num.natAbs s.num.natAbs
    simp only [Nat.log2_eq_log_two] at hm ⊢
    exact (Nat.log_mono_right (b := 2) hnum).trans hm
  have hdlog : (q * s).den.log2 ≤ q.den.log2 + s.den.log2 + 1 := by
    have hm := log2_mul_le q.den s.den
    simp only [Nat.log2_eq_log_two] at hm ⊢
    exact (Nat.log_mono_right (b := 2) hden).trans hm
  unfold binaryRatLength binaryNatLength
  omega
