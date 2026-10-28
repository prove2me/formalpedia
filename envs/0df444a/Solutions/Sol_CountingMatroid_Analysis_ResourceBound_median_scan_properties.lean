-- Prove2me | solution 1 for CountingMatroid.Analysis.ResourceBound.median_scan_properties
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-24T13:05:50.816444+00:00
-- url     : https://prove2.me/submissions/d7dd8b4b-3c6d-4c01-a297-597f425d99bd

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
import Definitions.Def_CountingMatroid_Analysis_EstimateMedianResource
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
import Theorems.Thm_CountingMatroid_Analysis_sortedInsert_value_eq

namespace CountingMatroid.Analysis
end CountingMatroid.Analysis
namespace CountingMatroid.Meta
end CountingMatroid.Meta
namespace Arlib
end Arlib
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

/-- INTERNAL: The charged median scan retains sortedness, bounded element
encodings, and the expected list length after every insertion. -/
theorem solution (xs acc : List ℚ) (K : ℕ)
    (haccSort : acc.Pairwise (· ≤ ·))
    (haccSize : ∀ q ∈ acc, binaryRatLength q ≤ K)
    (hxsSize : ∀ q ∈ xs, binaryRatLength q ≤ K) :
    let out := (Arlib.Computation.Charged.foldl
      (fun acc value => CountingMatroid.Program.sortedInsert value acc)
      xs acc).val
    out.Pairwise (· ≤ ·) ∧
      (∀ q ∈ out, binaryRatLength q ≤ K) ∧
      out.length = acc.length + xs.length := by
  induction xs generalizing acc with
  | nil => exact ⟨haccSort, haccSize, by simp⟩
  | cons value xs ih =>
      have hv : binaryRatLength value ≤ K := hxsSize value (by simp)
      have htail : ∀ q ∈ xs, binaryRatLength q ≤ K := by
        intro q hq
        exact hxsSize q (by simp [hq])
      have hins := CountingMatroid.Analysis.sortedInsert_value_eq
        value acc haccSort
      have hsort : (acc.orderedInsert (· ≤ ·) value).Pairwise (· ≤ ·) :=
        haccSort.orderedInsert value acc
      have hsize : ∀ q ∈ acc.orderedInsert (· ≤ ·) value,
          binaryRatLength q ≤ K := by
        intro q hq
        rcases (List.mem_orderedInsert (· ≤ ·)).mp hq with rfl | ha
        · exact hv
        · exact haccSize q ha
      have hnext := ih (acc.orderedInsert (· ≤ ·) value) hsort hsize htail
      simpa [Arlib.Computation.Charged.val_foldl_cons, hins,
        List.orderedInsert_length, Nat.add_assoc, Nat.add_comm,
        Nat.add_left_comm] using hnext
