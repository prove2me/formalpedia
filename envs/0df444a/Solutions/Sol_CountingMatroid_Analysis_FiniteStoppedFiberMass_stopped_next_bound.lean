-- Prove2me | solution 1 for CountingMatroid.Analysis.FiniteStoppedFiberMass.stopped_next_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-24T16:12:06.259119+00:00
-- url     : https://prove2.me/submissions/b5c9bdfe-3e2e-40df-93d0-bc776ca83c46

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
import Theorems.Thm_CountingMatroid_Analysis_FiniteStoppedFiberMass_fairMass_stop_sum
import Theorems.Thm_CountingMatroid_Analysis_FiniteStoppedFiberMass_stopped_fiber_bound

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

/-- INTERNAL: A stopped one-step event followed by uniformly bounded fresh
continuations has at most its covered marginal mass times that bound. -/
theorem solution {α : Type} (head : List Bool) (t : ℕ)
    (f : (ℕ → Bool) → Option (α × ℕ))
    (hf : ChainStepIntervalReplay.SuccessReplay f Prod.snd head.length)
    (a : α) (E : (ℕ → Bool) → ℕ → Prop) (B : ℝ) (hB : 0 ≤ B)
    (hcont : ∀ stop, head.length ≤ stop → stop ≤ head.length+t →
      ∀ pref : List.Vector Bool (stop-head.length),
      f (finiteTape (head ++ pref.val)) = some (a, stop) →
      fairMass (head ++ pref.val) (t-(stop-head.length)) (fun tape => E tape stop) ≤ B) :
    fairMass head t (fun tape => ∃ stop, stop ≤ head.length + t ∧
      f tape = some (a, stop) ∧ E tape stop) ≤
    fairMass head t (fun tape => ∃ stop, stop ≤ head.length + t ∧
      f tape = some (a, stop)) * B := by
  classical
  have hsplit := fairMass_stop_sum head t f a (fun _ _ => True)
  simp only [and_true] at hsplit
  rw [fairMass_stop_sum head t f a E, hsplit, Finset.sum_mul]
  apply Finset.sum_le_sum
  intro stop _
  by_cases hstart : head.length ≤ stop.val
  · exact stopped_fiber_bound head t f Prod.snd hf (a, stop.val) hstart (by omega)
      (fun tape => E tape stop.val) B hB (hcont stop.val hstart (by omega))
  · have hnone : ∀ tape, f tape ≠ some (a, stop.val) := by
      intro tape hrun
      exact hstart (hf tape _ hrun).1
    have hz : fairMass head t (fun tape => f tape = some (a, stop.val)) = 0 := by
      unfold fairMass
      simp only [hnone, if_false, Finset.sum_const_zero]
    have hz' : fairMass head t (fun tape => f tape = some (a, stop.val) ∧ E tape stop.val) = 0 := by
      unfold fairMass
      simp only [hnone, false_and, if_false, Finset.sum_const_zero]
    rw [hz, hz']
    simp
