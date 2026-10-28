-- Prove2me | solution 1 for CountingMatroid.Analysis.RationalHeight.rationalHeight_add_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-24T12:54:01.289051+00:00
-- url     : https://prove2.me/submissions/4d7c8429-d65e-4dd6-ac1f-b197994ad681

import Definitions.Def_CountingMatroidSupport_Computation_Charged
import Definitions.Def_CountingMatroidSupport_Computation_Charged_Extension1
import Definitions.Def_CountingMatroidSupport_Computation_Charged_Extension2
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
import Definitions.Def_CountingMatroid_Analysis_RationalHeight
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

namespace CountingMatroid.Analysis.ScheduleOtherStepsEnvelope
end CountingMatroid.Analysis.ScheduleOtherStepsEnvelope
namespace CountingMatroid.Analysis.LeastHalvingsCost
end CountingMatroid.Analysis.LeastHalvingsCost
namespace CountingMatroid.Analysis.ResourceBound
end CountingMatroid.Analysis.ResourceBound
namespace CountingMatroid.Analysis
end CountingMatroid.Analysis
namespace CountingMatroid.Meta
end CountingMatroid.Meta
namespace Arlib
end Arlib
section


set_option autoImplicit false

namespace CountingMatroid.Analysis.RationalHeight
open CountingMatroid.Model







/-- INTERNAL: Each rational component fits in the power of two specified by its height. -/
private theorem components_lt (q : ℚ) :
    q.num.natAbs < 2 ^ rationalHeight q ∧ q.den < 2 ^ rationalHeight q := by
  have bound (a b : ℕ) (h : a.log2 ≤ b) : a < 2 ^ (b + 1) := by
    have ha := Nat.lt_pow_succ_log_self Nat.one_lt_two a
    rw [← Nat.log2_eq_log_two] at ha
    exact ha.trans_le (Nat.pow_le_pow_right (by decide) (by omega))
  exact ⟨bound _ _ (le_max_left _ _), bound _ _ (le_max_right _ _)⟩


end CountingMatroid.Analysis.RationalHeight

end
set_option autoImplicit false

namespace CountingMatroid.Analysis.RationalHeight
end CountingMatroid.Analysis.RationalHeight
open CountingMatroid CountingMatroid.Analysis CountingMatroid.Analysis.RationalHeight
open CountingMatroid.Model

/-- INTERNAL: Rational addition increases component height by at most the sum
of the operand heights and one carry bit. TEXLINE: main.tex:1362-1378 -/
theorem solution (a b : ℚ) :
    rationalHeight (a + b) ≤ rationalHeight a + rationalHeight b + 1 := by
  have hd : (a + b).den ≤ a.den * b.den :=
    Nat.le_of_dvd (Nat.mul_pos a.den_pos b.den_pos) (Rat.add_den_dvd a b)
  have heq := congrArg Int.natAbs (Rat.add_num_den' a b)
  simp only [Int.natAbs_mul, Int.natAbs_natCast] at heq
  have hn := Int.natAbs_add_le (a.num * b.den) (b.num * a.den)
  simp only [Int.natAbs_mul, Int.natAbs_natCast] at hn
  have hnum : (a + b).num.natAbs ≤ a.num.natAbs * b.den + b.num.natAbs * a.den := by
    have hdenpos := Nat.mul_pos a.den_pos b.den_pos
    have hmul := Nat.mul_le_mul hn hd
    nlinarith
  obtain ⟨han, had⟩ := components_lt a
  obtain ⟨hbn, hbd⟩ := components_lt b
  have hp : 0 < 2 ^ (rationalHeight a + rationalHeight b) := by positivity
  have hprod₁ : a.num.natAbs * b.den < 2 ^ (rationalHeight a + rationalHeight b) := by
    rw [pow_add]
    exact Nat.mul_lt_mul_of_lt_of_le han hbd.le (by positivity)
  have hprod₂ : b.num.natAbs * a.den < 2 ^ (rationalHeight a + rationalHeight b) := by
    rw [add_comm, pow_add]
    exact Nat.mul_lt_mul_of_lt_of_le hbn had.le (by positivity)
  have hdprod : a.den * b.den < 2 ^ (rationalHeight a + rationalHeight b) := by
    rw [pow_add]
    exact Nat.mul_lt_mul_of_lt_of_le had hbd.le (by positivity)
  have hnlt : (a + b).num.natAbs < 2 ^ (rationalHeight a + rationalHeight b + 1) := by
    rw [pow_succ]
    omega
  have hdlt : (a + b).den < 2 ^ (rationalHeight a + rationalHeight b + 1) := by
    rw [pow_succ]
    omega
  have logbound (m : ℕ) (hm : m < 2 ^ (rationalHeight a + rationalHeight b + 1)) :
      m.log2 < rationalHeight a + rationalHeight b + 1 := by
    by_cases hz : m = 0
    · subst m; simp
    · rw [Nat.log2_eq_log_two]
      exact (Nat.log_lt_iff_lt_pow (by decide) hz).2 hm
  have hnlog := logbound _ hnlt
  have hdlog := logbound _ hdlt
  change max (a + b).num.natAbs.log2 (a + b).den.log2 + 1 ≤ _
  omega
