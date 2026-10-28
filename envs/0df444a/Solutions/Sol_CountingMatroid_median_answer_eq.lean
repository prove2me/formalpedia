-- Prove2me | solution 1 for CountingMatroid.median_answer_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-24T14:06:29.917206+00:00
-- url     : https://prove2.me/submissions/34715e4f-eac9-446c-a5b8-6c27e200d8c1

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
import Theorems.Thm_CountingMatroid_Analysis_sortedInsert_value_eq

namespace CountingMatroid
end CountingMatroid
namespace CountingMatroid.Analysis
end CountingMatroid.Analysis
namespace CountingMatroid.Meta
end CountingMatroid.Meta
namespace Arlib
end Arlib
namespace CountingMatroid.Interface
end CountingMatroid.Interface
/-!
# The program and the model are the same algorithm

`CountingMatroid.Model.Program` is what the paper's claims are about: a charged
computation whose state is sealed and whose cost is an operator applied to it.
`CountingMatroid.Interface.Pseudocode` is the same algorithm as mathematics for the
answer/output object the correctness theorem measures. Time and space stay over
`CountingMatroid.Model.Program`; this file is only the transport for correctness.

It is a ladder. Each theorem below is proved from the ones above it, and
`outputLaw_answer_eq` is the top: it is the one lemma the analysis rewrites
through, and the only one anything outside this file should need.

The bridge is closed by a charged insertion lemma and the resulting median,
estimator, and PMF law equalities.
-/

set_option autoImplicit false

namespace CountingMatroid
end CountingMatroid
open CountingMatroid

/-- The charged estimator accumulates run answers by cons, while the pseudocode lists them in run order. Prove that the charged insertion sort computes the same median and that reversing the input does not change it. -/
theorem solution (values : List ℚ) : (CountingMatroid.Program.medianRational values.reverse).val = CountingMatroid.Interface.Pseudocode.median values := by
  have hsort : ∀ (l : List ℚ) (acc : List ℚ), acc.Pairwise (· ≤ ·) →
      (Arlib.Computation.Charged.foldl
        (fun acc value => CountingMatroid.Program.sortedInsert value acc) l acc).val =
      l.foldl (fun acc value => acc.orderedInsert (· ≤ ·) value) acc := by
    intro l
    induction l with
    | nil => intro acc _; rfl
    | cons value rest ih =>
        intro acc hac
        have hac' : (acc.orderedInsert (· ≤ ·) value).Pairwise (· ≤ ·) :=
          List.Pairwise.orderedInsert (r := (· ≤ ·)) value acc hac
        simpa only [Arlib.Computation.Charged.val_foldl_cons, List.foldl_cons,
          CountingMatroid.Analysis.sortedInsert_value_eq value acc hac] using
          ih (acc.orderedInsert (· ≤ ·) value) hac'
  simp [CountingMatroid.Program.medianRational,
    CountingMatroid.Interface.Pseudocode.median, List.insertionSort,
    CountingMatroid.Model.Operations.nthRational,
    CountingMatroid.Model.Operations.halfNat]
  rw [hsort values.reverse [] List.Pairwise.nil, List.foldl_reverse]
