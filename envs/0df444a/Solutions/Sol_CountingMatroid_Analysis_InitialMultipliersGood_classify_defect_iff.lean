-- Prove2me | solution 1 for CountingMatroid.Analysis.InitialMultipliersGood.classify_defect_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-24T14:24:20.23946+00:00
-- url     : https://prove2.me/submissions/a49f7467-b71f-4303-96e9-07816489d414

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
import Definitions.Def_CountingMatroid_Analysis_BoundedRunPhaseHistory
import Definitions.Def_CountingMatroid_Analysis_FirstPhaseFailure
import Definitions.Def_CountingMatroid_Analysis_InitialMultipliersGood
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

namespace CountingMatroid.Interface
end CountingMatroid.Interface
namespace CountingMatroid.Meta
end CountingMatroid.Meta
namespace Arlib
end Arlib
namespace CountingMatroid.Analysis.TransversalRankBridge
end CountingMatroid.Analysis.TransversalRankBridge
namespace CountingMatroid.Analysis.GreedyRankCorrect
end CountingMatroid.Analysis.GreedyRankCorrect
section


set_option autoImplicit false

namespace CountingMatroid.Analysis.InitialMultipliersGood

open CountingMatroid.Model CountingMatroid.Analysis
open CountingMatroid.Program CountingMatroid.Model.Operations





/-- INTERNAL: Evaluate one charged visit, preserving all duplicate flags. -/
private theorem classifier_visit_value {n : ℕ} (state : PairedSet n)
    (acc : Option (Fin n) × Option (Fin n) × Bool) (i : Fin n) :
    (classifierVisit state acc i).val = scanPair state acc i := by
  rcases acc with ⟨empty, full, flag⟩
  by_cases hx : (i, false) ∈ state <;> by_cases hy : (i, true) ∈ state <;>
    cases empty <;> cases full <;>
    simp [classifierVisit, scanPair, containsPaired, isSome, hx, hy]

/-- INTERNAL: Evaluate a classifier fold as the ordinary fold of its
per-pair return values. -/
private theorem classifier_fold_value {n : ℕ} (state : PairedSet n)
    (l : List (Fin n)) (acc : Option (Fin n) × Option (Fin n) × Bool) :
    (Arlib.Computation.Charged.foldl (classifierVisit state) l acc).val =
      l.foldl (scanPair state) acc := by
  induction l generalizing acc with
  | nil => rfl
  | cons i l ih =>
      rw [Arlib.Computation.Charged.val_foldl_cons, classifier_visit_value,
        List.foldl_cons, ih]

/-- INTERNAL: Evaluate the final classifier decision after its pair scan.
The last off-diagonal check is retained as ordinary index equality. -/
private theorem classify_value {n : ℕ} (state : PairedSet n) :
    let result := (List.finRange n).foldl (scanPair state) (none, none, false)
    (classifyState state).val =
      if result.2.2 then .invalid else
        match result.1, result.2.1 with
        | none, none => .transversal
        | some i, some j => if i = j then .invalid else .defect i j
        | _, _ => .invalid := by
  unfold classifyState
  change ((do
    let result ← Arlib.Computation.Charged.foldl (classifierVisit state)
      (List.finRange n) (none, none, false)
    if result.2.2 then pure .invalid else
      match result.1, result.2.1 with
      | none, none => pure .transversal
      | some i, some j => do
          let diagonal ← indexEqual i j
          if diagonal then pure .invalid else pure (.defect i j)
      | _, _ => pure .invalid) : Arlib.Computation.Charged Op Cell (StateKind n)).val = _
  rw [Arlib.Computation.Charged.val_bind, classifier_fold_value]
  generalize (List.finRange n).foldl (scanPair state) (none, none, false) = result
  rcases result with ⟨empty, full, flag⟩
  cases flag <;> cases empty <;> cases full <;> simp [indexEqual, apply_ite]


/-- INTERNAL: A classifier visit with a false duplicate flag retains every
previously recorded hole/full pair, and records precisely this visit's pair. -/
private theorem scan_pair_false {n : ℕ} (state : PairedSet n)
    (acc : Option (Fin n) × Option (Fin n) × Bool) (i : Fin n)
    (hflag : (scanPair state acc i).2.2 = false) :
    acc.2.2 = false ∧
    (∀ k, (scanPair state acc i).1 = some k ↔ acc.1 = some k ∨
      (i = k ∧ (i, false) ∉ state ∧ (i, true) ∉ state)) ∧
    (∀ k, (scanPair state acc i).2.1 = some k ↔ acc.2.1 = some k ∨
      (i = k ∧ (i, false) ∈ state ∧ (i, true) ∈ state)) := by
  rcases acc with ⟨empty, full, flag⟩
  by_cases hx : (i, false) ∈ state <;> by_cases hy : (i, true) ∈ state <;>
    cases empty <;> cases full <;> cases flag <;>
    simp_all [scanPair]

/-- INTERNAL: If the final duplicate flag is false, the two recorded indices
are exactly the empty/full pairs visited by the classifier fold. -/
private theorem scan_fold_false {n : ℕ} (state : PairedSet n)
    (l : List (Fin n)) (acc : Option (Fin n) × Option (Fin n) × Bool)
    (hflag : (l.foldl (scanPair state) acc).2.2 = false) :
    acc.2.2 = false ∧
    (∀ k, (l.foldl (scanPair state) acc).1 = some k ↔ acc.1 = some k ∨
      (k ∈ l ∧ (k, false) ∉ state ∧ (k, true) ∉ state)) ∧
    (∀ k, (l.foldl (scanPair state) acc).2.1 = some k ↔ acc.2.1 = some k ∨
      (k ∈ l ∧ (k, false) ∈ state ∧ (k, true) ∈ state)) := by
  induction l generalizing acc with
  | nil => simpa using hflag
  | cons i l ih =>
    obtain ⟨hstep, he, hf⟩ := ih (scanPair state acc i) hflag
    obtain ⟨hacc, hse, hsf⟩ := scan_pair_false state acc i hstep
    refine ⟨hacc, ?_, ?_⟩
    · intro k
      rw [List.foldl_cons, he, hse, List.mem_cons]
      aesop
    · intro k
      rw [List.foldl_cons, hf, hsf, List.mem_cons]
      aesop




















end CountingMatroid.Analysis.InitialMultipliersGood

end
set_option autoImplicit false

namespace CountingMatroid.Analysis.InitialMultipliersGood
end CountingMatroid.Analysis.InitialMultipliersGood
open CountingMatroid CountingMatroid.Analysis CountingMatroid.Analysis.InitialMultipliersGood

open CountingMatroid.Model CountingMatroid.Analysis
open CountingMatroid.Program CountingMatroid.Model.Operations

/-- INTERNAL: Recover the entire occupancy description of an accepted
ordered defect from the executable classifier, and conversely. -/
theorem solution {n : ℕ} (state : PairedSet n)
    (index : DefectIndex n) :
    (classifyState state).val = .defect index.emptyPair index.fullPair ↔
      (∀ i, ((i, false) ∉ state ∧ (i, true) ∉ state) ↔ i = index.emptyPair) ∧
      (∀ i, ((i, false) ∈ state ∧ (i, true) ∈ state) ↔ i = index.fullPair) := by
  classical
  constructor
  · intro hclass
    have hvalue := classify_value state
    rw [hclass] at hvalue
    have hresult : (List.finRange n).foldl (scanPair state) (none, none, false) =
        (some index.emptyPair, some index.fullPair, false) := by
      generalize (List.finRange n).foldl (scanPair state) (none, none, false) = result
        at hvalue ⊢
      rcases result with ⟨empty, full, flag⟩
      cases flag <;> cases empty <;> cases full
      all_goals simp only [Bool.false_eq_true, if_true, if_false] at hvalue ⊢
      all_goals first
        | cases hvalue
        | (split_ifs at hvalue <;> simp_all)
    obtain ⟨_, he, hf⟩ := scan_fold_false state (List.finRange n)
      (none, none, false) (by rw [hresult])
    constructor
    · intro i
      have hi := he i
      simpa [hresult, eq_comm] using hi.symm
    · intro i
      have hi := hf i
      simpa [hresult, eq_comm] using hi.symm
  · rintro ⟨he, hf⟩
    let scan := fun (acc : Option (Fin n) × Option (Fin n) × Bool) (i : Fin n) =>
      if i = index.emptyPair then
        if acc.1.isSome then (acc.1, acc.2.1, true)
        else (some i, acc.2.1, acc.2.2)
      else if i = index.fullPair then
        if acc.2.1.isSome then (acc.1, acc.2.1, true)
        else (acc.1, some i, acc.2.2)
      else acc
    have hstep (acc : Option (Fin n) × Option (Fin n) × Bool) (i : Fin n) :
        scanPair state acc i = scan acc i := by
      have hei := he i
      have hfi := hf i
      by_cases hx : (i, false) ∈ state <;> by_cases hy : (i, true) ∈ state <;>
        simp_all [scanPair, scan]
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
        by_cases hei : i = index.emptyPair
        · subst i
          simp [scan, hi, index.distinct.symm]
        · by_cases hfi : i = index.fullPair
          · subst i
            simp [scan, hi, hei, index.distinct]
          · simp [scan, hei, hfi, Ne.symm hei, Ne.symm hfi]
    rw [classify_value]
    rw [show scanPair state = scan from funext (fun acc => funext (hstep acc))]
    simp [hfold (List.finRange n) (List.nodup_finRange n), index.distinct]
