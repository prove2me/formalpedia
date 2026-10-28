-- Prove2me | solution 1 for CountingMatroid.Analysis.ScheduleAbortBudget.least_draw_trials_threshold
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-24T15:14:13.519835+00:00
-- url     : https://prove2.me/submissions/853eb180-688c-49fe-9a6f-51c2daa99c9b

import Definitions.Def_CountingMatroidSupport_Computation_Charged
import Definitions.Def_CountingMatroidSupport_Computation_Charged_Extension1
import Definitions.Def_CountingMatroidSupport_Computation_Charged_Extension2
import Definitions.Def_CountingMatroidSupport_Computation_Cost
import Definitions.Def_CountingMatroidSupport_Computation_Cost_Extension1
import Definitions.Def_CountingMatroidSupport_Computation_Dict
import Definitions.Def_CountingMatroidSupport_Computation_Heap
import Definitions.Def_CountingMatroidSupport_Computation_Machine
import Definitions.Def_CountingMatroidSupport_Computation_Machine_Extension1
import Definitions.Def_CountingMatroidSupport_Computation_Num
import Definitions.Def_CountingMatroidSupport_Computation_Queue
import Definitions.Def_CountingMatroidSupport_Computation_Rand
import Definitions.Def_CountingMatroidSupport_Computation_Roster
import Definitions.Def_CountingMatroidSupport_Computation_Slot
import Definitions.Def_CountingMatroidSupport_Computation_Space
import Definitions.Def_CountingMatroidSupport_Computation_Std
import Definitions.Def_CountingMatroid_Analysis_ScheduleAbortBudget
import Definitions.Def_CountingMatroid_Interface_Pseudocode
import Definitions.Def_CountingMatroid_Interface_Pseudocode_Extension1
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

namespace CountingMatroid.Interface
end CountingMatroid.Interface
namespace CountingMatroid.Meta
end CountingMatroid.Meta
namespace Arlib
end Arlib
section


set_option autoImplicit false

/-!
The concrete doubling search meets the capped-draw probability threshold.
The schedule budget combines its per-phase draw terms with the restart-tail
term. These are deterministic numerical bounds; operational event bounds
are supplied separately by the conditional abort modules.
-/

namespace CountingMatroid.Analysis.ScheduleAbortBudget

open CountingMatroid.Model CountingMatroid.Model.Operations
open Arlib.Computation (Charged)



/-- INTERNAL: Value equation for the capped doubling search. -/
private theorem doubling_cons
    (target : ℕ) (i : ℕ) (l : List ℕ) (acc : ℕ × ℕ) :
    (Charged.foldlWhile (doublingStep target) (i :: l) acc).val =
      if acc.2 < target then
        (Charged.foldlWhile (doublingStep target) l (acc.1 + 1, acc.2 * 2)).val
      else acc := by
  by_cases h : acc.2 < target
  · have hs : (doublingStep target acc i).val = some (acc.1 + 1, acc.2 * 2) := by
      simp [doublingStep, lessThan, successor, natMul, h]
    simp only [Charged.val] at hs
    simp [Charged.foldlWhile, Charged.val, hs, h]
  · have hs : (doublingStep target acc i).val = none := by
      simp [doublingStep, lessThan, h]
    simp only [Charged.val] at hs
    simp [Charged.foldlWhile, Charged.val, hs, h]

/-- INTERNAL: The doubling search reaches its threshold or stops only after
it has already met it. -/
private theorem doubling_threshold (target : ℕ) :
    ∀ (l : List ℕ) (d power : ℕ), power = 2 ^ d →
      target ≤ 2 ^ (d + l.length) →
      target ≤ 2 ^ (Charged.foldlWhile (doublingStep target) l (d, power)).val.1 := by
  intro l
  induction l with
  | nil =>
      intro d power hp ht
      simpa using ht
  | cons i l ih =>
      intro d power hp ht
      rw [doubling_cons]
      by_cases h : power < target
      · rw [if_pos h]
        apply ih
        · rw [hp, pow_succ]
        · simpa only [List.length_cons, Nat.add_assoc, Nat.add_comm 1] using ht
      · rw [if_neg h]
        simpa only [hp] using le_of_not_gt h

















end CountingMatroid.Analysis.ScheduleAbortBudget

/-! ### Run record
Newest first. History, not instruction — what this file claims is above.

* r24 · proved · the actual capped doubling search meets `32*M ≤ 2^D`; positive phase count and the charged schedule tail give the combined `3/[32(L+1)]` abort budget. Direct field reduction was replaced by continuation-property propagation and separate numerical arithmetic.
-/

end
set_option autoImplicit false

/-!
The concrete doubling search meets the capped-draw probability threshold.
The schedule budget combines its per-phase draw terms with the restart-tail
term. These are deterministic numerical bounds; operational event bounds
are supplied separately by the conditional abort modules.
-/

namespace CountingMatroid.Analysis.ScheduleAbortBudget
end CountingMatroid.Analysis.ScheduleAbortBudget
open CountingMatroid CountingMatroid.Analysis CountingMatroid.Analysis.ScheduleAbortBudget

open CountingMatroid.Model CountingMatroid.Model.Operations
open Arlib.Computation (Charged)

/-- INTERNAL: The actual capped integer search meets the paper's rejection
probability threshold, including zero requested calls.
TEXLINE: main.tex:1405-1421 -/
theorem solution (M : ℕ) :
    32 * M ≤ 2 ^ (CountingMatroid.Program.leastDrawTrials M).val := by
  unfold CountingMatroid.Program.leastDrawTrials
  simp only [Charged.val_bind, binaryLoopBound, Charged.val_op,
    Charged.val_pure, natMul, Charged.repeatWhile]
  change 32 * M ≤ 2 ^ (Charged.foldlWhile (doublingStep (32 * M))
    (List.range (M.log2 + 8)) (1, 2)).val.1
  apply doubling_threshold (32 * M) (List.range (M.log2 + 8)) 1 2 (by norm_num)
  have hM : M ≤ 2 ^ (M.log2 + 1) := by
    have h := Nat.lt_pow_succ_log_self Nat.one_lt_two M
    rw [← Nat.log2_eq_log_two] at h
    exact Nat.le_of_lt h
  simp only [List.length_range]
  calc
    32 * M ≤ 32 * 2 ^ (M.log2 + 1) := Nat.mul_le_mul_left _ hM
    _ = 2 ^ (M.log2 + 6) := by
      simp only [pow_add]
      norm_num
      omega
    _ ≤ 2 ^ (1 + (M.log2 + 8)) := pow_le_pow_right' (by decide : 1 ≤ (2 : ℕ)) (by omega)
