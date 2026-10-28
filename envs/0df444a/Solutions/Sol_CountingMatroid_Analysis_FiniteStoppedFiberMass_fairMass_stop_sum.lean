-- Prove2me | solution 1 for CountingMatroid.Analysis.FiniteStoppedFiberMass.fairMass_stop_sum
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-24T15:06:46.197308+00:00
-- url     : https://prove2.me/submissions/3f5a37bf-7496-4bce-9114-eb400955bb3c

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

/-- INTERNAL: Sum disjoint stopping-cursor fibers, keeping their continuation events. -/
theorem solution {α : Type} (head : List Bool) (t : ℕ)
    (f : (ℕ → Bool) → Option (α × ℕ)) (a : α) (E : (ℕ → Bool) → ℕ → Prop) :
    fairMass head t (fun tape => ∃ stop, stop ≤ head.length + t ∧
      f tape = some (a, stop) ∧ E tape stop) =
    ∑ stop : Fin (head.length + t + 1),
      fairMass head t (fun tape => f tape = some (a, stop.val) ∧ E tape stop.val) := by
  classical
  unfold fairMass
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro bits _
  let tape := finiteTape (head ++ bits.val)
  dsimp only
  simp only [show finiteTape (head ++ bits.val) = tape from rfl]
  by_cases he : ∃ stop, stop ≤ head.length + t ∧ f tape = some (a, stop) ∧ E tape stop
  · obtain ⟨stop, hs, hf, hE⟩ := he
    let k : Fin (head.length + t + 1) := ⟨stop, by omega⟩
    rw [if_pos ⟨stop, hs, hf, hE⟩, Finset.sum_eq_single k]
    · simp only [k, hf, hE, and_self, if_true]
    · intro j _ hj
      apply if_neg
      rintro ⟨hjf, _⟩
      have hval := congrArg Prod.snd (Option.some.inj (hf.symm.trans hjf))
      apply hj
      exact Fin.ext hval.symm
    · simp
  · rw [if_neg he]
    symm
    apply Finset.sum_eq_zero
    intro j _
    apply if_neg
    intro hj
    exact he ⟨j.val, by omega, hj⟩
