-- Prove2me | solution 1 for CountingMatroid.Analysis.DefectPartitionPositive.defect_state_classified
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-24T14:11:44.422795+00:00
-- url     : https://prove2.me/submissions/697b9c7b-b2e6-4770-befa-7ce98e7604a2

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
import Definitions.Def_CountingMatroid_Analysis_BoundedRunPhase
import Definitions.Def_CountingMatroid_Analysis_DefectPartitionPositive
import Definitions.Def_CountingMatroid_Analysis_FirstPhaseFailure
import Definitions.Def_CountingMatroid_Analysis_ScheduleConfidence
import Definitions.Def_CountingMatroid_Analysis_TransversalPartition
import Definitions.Def_CountingMatroid_Analysis_TransversalProjection
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
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Combinatorics.Matroid.Rank.ENat
import Mathlib.Data.BitVec
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.List.Basic
import Mathlib.Data.List.Induction
import Mathlib.Data.List.Nodup
import Mathlib.Data.List.Sort
import Mathlib.Data.Multiset.Basic
import Mathlib.Data.Nat.Log
import Mathlib.Data.Rat.Defs
import Mathlib.Data.Real.Basic
import Mathlib.Data.Set.Card.Arithmetic
import Mathlib.Data.Set.Finite.List
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

namespace CountingMatroid.Meta
end CountingMatroid.Meta
namespace Arlib
end Arlib
namespace CountingMatroid.Interface
end CountingMatroid.Interface
namespace CountingMatroid.Analysis.TransversalRankBridge
end CountingMatroid.Analysis.TransversalRankBridge
namespace CountingMatroid.Analysis.GreedyRankCorrect
end CountingMatroid.Analysis.GreedyRankCorrect
section


set_option autoImplicit false

namespace CountingMatroid.Analysis.DefectPartitionPositive

open CountingMatroid.Model CountingMatroid.Model.Operations CountingMatroid.Program



/-- INTERNAL: Occupancy of the explicit defect witness, used to evaluate the
program's classifier rather than assume a mathematical classifier.
TEXLINE: main.tex:712-735 -/
private theorem defectState_membership {n : ℕ} (index : DefectIndex n)
    (i : Fin n) :
    ((i, false) ∈ defectState index ↔ i ≠ index.emptyPair) ∧
      ((i, true) ∈ defectState index ↔ i = index.fullPair) := by
  classical
  simp [defectState]

/-- INTERNAL: A charged fold's return value is the ordinary fold of return
values. The classifier's implementation is inspected through this equality. -/
private theorem foldl_value {α β : Type}
    (f : β → α → Arlib.Computation.Charged Op Cell β) (l : List α) (b : β) :
    (Arlib.Computation.Charged.foldl f l b).val =
      l.foldl (fun acc a => (f acc a).val) b := by
  induction l generalizing b with
  | nil => rfl
  | cons a l ih =>
      simpa only [Arlib.Computation.Charged.val_foldl_cons, List.foldl_cons]
        using ih (f b a).val





end CountingMatroid.Analysis.DefectPartitionPositive

end
set_option autoImplicit false

namespace CountingMatroid.Analysis.DefectPartitionPositive
end CountingMatroid.Analysis.DefectPartitionPositive
open CountingMatroid CountingMatroid.Analysis CountingMatroid.Analysis.DefectPartitionPositive

open CountingMatroid.Model CountingMatroid.Model.Operations CountingMatroid.Program

/-- INTERNAL: The actual pair scan accepts the explicit ordered-defect
witness. Repeated empty/full-pair checks are controlled by the duplicate-free
enumeration, and its off-diagonal check uses the index's distinctness proof.
TEXLINE: main.tex:712-735,746-751 -/
theorem solution {n : ℕ} (index : DefectIndex n) :
    (classifyState (defectState index)).val =
      .defect index.emptyPair index.fullPair := by
  classical
  let step : (Option (Fin n) × Option (Fin n) × Bool) → Fin n →
      Arlib.Computation.Charged Op Cell (Option (Fin n) × Option (Fin n) × Bool) :=
    fun acc i => do
      let x ← containsPaired (defectState index) (i, false)
      let y ← containsPaired (defectState index) (i, true)
      if x then
        if y then
          let seen ← isSome acc.2.1
          if seen then pure (acc.1, acc.2.1, true)
          else pure (acc.1, some i, acc.2.2)
        else pure acc
      else
        if y then pure acc
        else
          let seen ← isSome acc.1
          if seen then pure (acc.1, acc.2.1, true)
          else pure (some i, acc.2.1, acc.2.2)
  let scan := fun (acc : Option (Fin n) × Option (Fin n) × Bool) (i : Fin n) =>
    if i = index.emptyPair then
      if acc.1.isSome then (acc.1, acc.2.1, true)
      else (some i, acc.2.1, acc.2.2)
    else if i = index.fullPair then
      if acc.2.1.isSome then (acc.1, acc.2.1, true)
      else (acc.1, some i, acc.2.2)
    else acc
  have hstep (acc : Option (Fin n) × Option (Fin n) × Bool) (i : Fin n) :
      (step acc i).val = scan acc i := by
    by_cases he : i = index.emptyPair
    · simp [step, scan, containsPaired, isSome, defectState_membership, he,
        index.distinct]
      split <;> rename_i hseen <;> simp [hseen]
    · by_cases hf : i = index.fullPair
      · simp [step, scan, containsPaired, isSome, defectState_membership, hf,
          index.distinct.symm]
        split <;> rename_i hseen <;> simp [hseen]
      · simp [step, scan, containsPaired, isSome, defectState_membership, he, hf]
  have hfold (l : List (Fin n)) (hl : l.Nodup) :
      l.foldl scan (none, none, false) =
        (if index.emptyPair ∈ l then some index.emptyPair else none,
         if index.fullPair ∈ l then some index.fullPair else none, false) := by
    induction l using List.reverseRecOn with
    | nil => simp
    | append_singleton l i ih =>
      have hnodup : (l.concat i).Nodup := by
        simpa only [List.concat_eq_append] using hl
      obtain ⟨hi, hl'⟩ := (List.nodup_concat l i).mp hnodup
      rw [List.foldl_append, ih hl', List.foldl_cons, List.foldl_nil]
      by_cases he : i = index.emptyPair
      · subst i
        simp [scan, hi, index.distinct.symm]
      · by_cases hf : i = index.fullPair
        · subst i
          simp [scan, hi, he, index.distinct]
        · simp [scan, he, hf, Ne.symm he, Ne.symm hf]
  have hscan : (Arlib.Computation.Charged.foldl step (List.finRange n)
      (none, none, false)).val = (some index.emptyPair, some index.fullPair, false) := by
    rw [foldl_value]
    simp_rw [hstep]
    simpa using hfold (List.finRange n) (List.nodup_finRange n)
  unfold classifyState
  change ((do
    let result ← Arlib.Computation.Charged.foldl step (List.finRange n)
      (none, none, false)
    if result.2.2 then pure .invalid else
      match result.1, result.2.1 with
      | none, none => pure .transversal
      | some i, some j => do
          let diagonal ← indexEqual i j
          if diagonal then pure .invalid else pure (.defect i j)
      | _, _ => pure .invalid) : Arlib.Computation.Charged Op Cell (StateKind n)).val = _
  simp [hscan, indexEqual, index.distinct]
