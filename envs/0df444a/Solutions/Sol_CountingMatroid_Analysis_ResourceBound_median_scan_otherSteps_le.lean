-- Prove2me | solution 1 for CountingMatroid.Analysis.ResourceBound.median_scan_otherSteps_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-24T12:52:03.609854+00:00
-- url     : https://prove2.me/submissions/e1caa89c-95f6-4a13-8e7c-588d216116a5

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
import Definitions.Def_CountingMatroid_Model_Operations
import Definitions.Def_CountingMatroid_Model_Prelude
import Definitions.Def_CountingMatroid_Model_Program
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
import Mathlib.Tactic.Abel
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Push
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Ring.RingNF
import Theorems.Thm_CountingMatroid_Analysis_ResourceBound_sortedInsert_otherSteps_le
import Theorems.Thm_CountingMatroid_Analysis_sortedInsert_value_eq

namespace CountingMatroid.Analysis.ResourceBound
end CountingMatroid.Analysis.ResourceBound
namespace CountingMatroid.Analysis
end CountingMatroid.Analysis
namespace CountingMatroid.Meta
end CountingMatroid.Meta
namespace Arlib
end Arlib
section


/-!
# Resource bounds for the charged rational median

The insertion scan preserves sorted values and has polynomial charged cost
when its input rational encodings have a common bound.
-/

set_option autoImplicit false

namespace CountingMatroid.Analysis.ResourceBound

open CountingMatroid.Model
open CountingMatroid.Model.Subroutines
open CountingMatroid.Model.Operations

/-- INTERNAL: The word-operation fold in `otherSteps` distributes over
two charged cost vectors. -/
theorem foldl_word_add (l : List Arlib.Computation.Op)
    (f g : Arlib.Computation.Op → ℕ) :
    ∀ a b, l.foldl (fun z x => z + (f x + g x)) (a + b) =
      l.foldl (fun z x => z + f x) a + l.foldl (fun z x => z + g x) b := by
  induction l with
  | nil => simp
  | cons x xs ih =>
      intro a b
      simpa [List.foldl, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
        ih (a + f x) (b + g x)

/-- INTERNAL: Nonoracle charges add when charged computations are sequenced. -/
theorem otherSteps_bind {α β : Type}
    (p : Arlib.Computation.Charged Op Cell α)
    (f : α → Arlib.Computation.Charged Op Cell β) :
    otherSteps (p >>= f) = otherSteps p + otherSteps (f p.val) := by
  simp only [otherSteps, Arlib.Computation.Charged.cost_bind, Pi.add_apply]
  have h := foldl_word_add Arlib.Computation.Op.all
    (fun x => p.cost (Op.word x)) (fun x => (f p.val).cost (Op.word x)) 0 0
  simp only [Nat.zero_add] at h
  rw [h]
  omega















end CountingMatroid.Analysis.ResourceBound

/-! ### Run record
Newest first. History, not instruction — what this file claims is above.

* r8 · proved · extracted and closed the median length, sign, and charge invariants used by the estimator.
-/

end
/-!
# Resource bounds for the charged rational median

The insertion scan preserves sorted values and has polynomial charged cost
when its input rational encodings have a common bound.
-/

set_option autoImplicit false

namespace CountingMatroid.Analysis.ResourceBound
end CountingMatroid.Analysis.ResourceBound
open CountingMatroid CountingMatroid.Analysis CountingMatroid.Analysis.ResourceBound

open CountingMatroid.Model
open CountingMatroid.Model.Subroutines
open CountingMatroid.Model.Operations

/-- INTERNAL: The charged insertion-sort scan takes quadratic many bounded
rational comparisons. -/
theorem solution (xs acc : List ℚ) (K : ℕ)
    (haccSort : acc.Pairwise (· ≤ ·))
    (haccSize : ∀ q ∈ acc, binaryRatLength q ≤ K)
    (hxsSize : ∀ q ∈ xs, binaryRatLength q ≤ K) :
    otherSteps (Arlib.Computation.Charged.foldl
      (fun acc value => CountingMatroid.Program.sortedInsert value acc)
      xs acc) ≤ xs.length * (acc.length + xs.length + 1) * (2 * K + 6) := by
  induction xs generalizing acc with
  | nil => simp [otherSteps]
  | cons value xs ih =>
      have hv : binaryRatLength value ≤ K := hxsSize value (by simp)
      have htailSize : ∀ q ∈ xs, binaryRatLength q ≤ K := by
        intro q hq
        exact hxsSize q (by simp [hq])
      let next := (CountingMatroid.Program.sortedInsert value acc).val
      have hins : next = acc.orderedInsert (· ≤ ·) value :=
        CountingMatroid.Analysis.sortedInsert_value_eq value acc haccSort
      have hnextSort : next.Pairwise (· ≤ ·) := by
        rw [hins]
        exact haccSort.orderedInsert value acc
      have hnextSize : ∀ q ∈ next, binaryRatLength q ≤ K := by
        intro q hq
        rw [hins] at hq
        rcases (List.mem_orderedInsert (· ≤ ·)).mp hq with rfl | ha
        · exact hv
        · exact haccSize q ha
      have hnextLen : next.length = acc.length + 1 := by
        rw [hins]
        exact List.orderedInsert_length (· ≤ ·) acc value
      have hhead := sortedInsert_otherSteps_le value acc K hv haccSize
      have htail := ih next hnextSort hnextSize htailSize
      have hhead' : otherSteps (CountingMatroid.Program.sortedInsert value acc) ≤
          (acc.length + (xs.length + 1) + 1) * (2 * K + 6) := by
        apply le_trans hhead
        exact Nat.mul_le_mul_right _ (by omega)
      have htail' : otherSteps (Arlib.Computation.Charged.foldl
          (fun acc value => CountingMatroid.Program.sortedInsert value acc)
          xs next) ≤ xs.length *
            ((acc.length + (xs.length + 1) + 1) * (2 * K + 6)) := by
        rw [hnextLen] at htail
        convert htail using 1 <;> ring
      change otherSteps ((CountingMatroid.Program.sortedInsert value acc) >>=
        fun next => Arlib.Computation.Charged.foldl
          (fun acc value => CountingMatroid.Program.sortedInsert value acc)
          xs next) ≤ _
      rw [otherSteps_bind]
      change otherSteps (CountingMatroid.Program.sortedInsert value acc) +
        otherSteps (Arlib.Computation.Charged.foldl
          (fun acc value => CountingMatroid.Program.sortedInsert value acc)
          xs next) ≤ _
      calc
        _ ≤ (acc.length + (xs.length + 1) + 1) * (2 * K + 6) +
            xs.length * ((acc.length + (xs.length + 1) + 1) * (2 * K + 6)) :=
          Nat.add_le_add hhead' htail'
        _ = (xs.length + 1) * (acc.length + (xs.length + 1) + 1) *
            (2 * K + 6) := by ring
