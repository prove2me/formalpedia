-- Prove2me | solution 1 for CountingMatroid.Analysis.FiniteStoppedFiberMass.fairMass_split
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-24T15:37:18.48975+00:00
-- url     : https://prove2.me/submissions/ee371c75-84b4-4b64-9188-9c646c4b3c69

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
import Definitions.Def_CountingMatroid_Analysis_BoundedUniformReplay
import Definitions.Def_CountingMatroid_Analysis_ChainStepIntervalReplay
import Definitions.Def_CountingMatroid_Analysis_FiniteStoppedFiberMass
import Definitions.Def_CountingMatroid_Model_Operations
import Definitions.Def_CountingMatroid_Model_Prelude
import Definitions.Def_CountingMatroid_Model_Program
import Definitions.Def_CountingMatroid_Model_Subroutines
import Lean
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
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
import Mathlib.Data.Fintype.Vector
import Mathlib.Data.List.Basic
import Mathlib.Data.List.Nodup
import Mathlib.Data.List.Sort
import Mathlib.Data.Multiset.Basic
import Mathlib.Data.Nat.Log
import Mathlib.Data.Rat.Defs
import Mathlib.Data.Real.Basic
import Mathlib.Order.Interval.Set.Basic
import Mathlib.Tactic
import Mathlib.Tactic.Abel
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Push
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Ring.RingNF
import Theorems.Thm_CountingMatroid_Analysis_FiniteStoppedFiberMass_sum_split

namespace CountingMatroid.Meta
end CountingMatroid.Meta
namespace Arlib
end Arlib
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

/-! Finite uniform tape disintegration at a successful fixed endpoint cursor. -/
namespace CountingMatroid.Analysis.FiniteStoppedFiberMass
end CountingMatroid.Analysis.FiniteStoppedFiberMass
open CountingMatroid CountingMatroid.Analysis CountingMatroid.Analysis.FiniteStoppedFiberMass

/-- INTERNAL: Uniform event mass factors across a deterministic suffix cut. -/
theorem solution (head : List Bool) (t k : ℕ) (hk : k ≤ t)
    (E : (ℕ → Bool) → Prop) :
    fairMass head t E = ∑ pref : List.Vector Bool k,
      (1 / (2 : ℝ) ^ k) * fairMass (head ++ pref.val) (t-k) E := by
  classical
  unfold fairMass
  rw [sum_split t k hk (fun bits => if E (finiteTape (head ++ bits)) then 1 / (2 : ℝ)^t else 0)]
  have hp : (1 / (2 : ℝ) ^ t) =
      (1 / (2 : ℝ) ^ k) * (1 / (2 : ℝ) ^ (t-k)) := by
    rw [one_div_mul_one_div, ← pow_add, Nat.add_sub_of_le hk]
  simp only [Finset.mul_sum, List.append_assoc]
  apply Finset.sum_congr rfl
  intro pref _
  apply Finset.sum_congr rfl
  intro tail _
  split_ifs <;> simp [hp]
