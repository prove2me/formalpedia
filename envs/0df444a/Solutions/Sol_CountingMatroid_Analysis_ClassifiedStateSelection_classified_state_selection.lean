-- Prove2me | solution 1 for CountingMatroid.Analysis.ClassifiedStateSelection.classified_state_selection
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-24T15:16:02.584339+00:00
-- url     : https://prove2.me/submissions/d20672c1-3a3c-49bb-b367-8517d37f13cd

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
import Definitions.Def_CountingMatroid_Analysis_TransversalClassPartition
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

namespace CountingMatroid.Analysis.ClassifiedStateSelection
end CountingMatroid.Analysis.ClassifiedStateSelection
namespace Arlib
end Arlib
namespace CountingMatroid.Interface
end CountingMatroid.Interface
namespace CountingMatroid.Meta
end CountingMatroid.Meta
namespace CountingMatroid.Analysis.TransversalRankBridge
end CountingMatroid.Analysis.TransversalRankBridge
namespace CountingMatroid.Analysis.GreedyRankCorrect
end CountingMatroid.Analysis.GreedyRankCorrect
set_option autoImplicit false

/-!
Correctness of the executable occupied/unoccupied selection scan.
A classifier-valid paired set has n labels in each of the two lists, and
selecting an index below n must therefore succeed.
-/

namespace CountingMatroid.Analysis.ClassifiedStateSelection
end CountingMatroid.Analysis.ClassifiedStateSelection
open CountingMatroid CountingMatroid.Analysis CountingMatroid.Analysis.ClassifiedStateSelection
open CountingMatroid.Model CountingMatroid.Program

/-- INTERNAL: Every in-range occupied or unoccupied index is found by the
actual charged selection scan on a classifier-valid paired set.
TEXLINE: main.tex:712-751 -/
theorem solution {n : ℕ} (state : PairedSet n)
    (hvalid : (classifyState state).val ≠ .invalid)
    (occupied : Bool) (k : ℕ) (hk : k < n) :
    ∃ element, (selectPaired state occupied k).val = some element := by
  have hvisit (acc : Option (PairedGround n) × ℕ) (element : PairedGround n) :
      (selectionVisit state occupied k acc element).val =
        if decide (element ∈ state) = occupied then
          (if acc.2 = k then some element else acc.1, acc.2 + 1)
        else acc := by
    cases occupied <;> by_cases hinside : element ∈ state <;>
      by_cases hhit : acc.2 = k <;>
      simp [selectionVisit, Model.Operations.containsPaired,
        Model.Operations.natEqual, Model.Operations.successor, hinside, hhit]
  let P : Option (PairedGround n) × ℕ → Prop := fun acc =>
    acc.1 = none → acc.2 ≤ k
  have hstep (acc : Option (PairedGround n) × ℕ) (element : PairedGround n)
      (hp : P acc) : P (selectionVisit state occupied k acc element).val := by
    rw [hvisit]
    by_cases heligible : decide (element ∈ state) = occupied
    · rw [if_pos heligible]
      by_cases hhit : acc.2 = k
      · simp only [hhit, ite_true, P]
        intro h
        cases h
      · simp only [hhit, ite_false, P]
        intro h
        have hle := hp h
        omega
    · rw [if_neg heligible]
      exact hp
  have hlist (xs : List (PairedGround n)) (acc : Option (PairedGround n) × ℕ)
      (hp : P acc) :
      P (Arlib.Computation.Charged.foldl (selectionVisit state occupied k) xs acc).val := by
    induction xs generalizing acc with
    | nil => exact hp
    | cons element xs ih =>
        rw [Arlib.Computation.Charged.val_foldl_cons]
        exact ih _ (hstep acc element hp)
  let f := fun (acc : Option (PairedGround n) × ℕ) (i : Fin n) =>
    Arlib.Computation.Charged.foldl (selectionVisit state occupied k)
      [((i, false) : PairedGround n), (i, true)] acc
  have houter (xs : List (Fin n)) (acc : Option (PairedGround n) × ℕ)
      (hp : P acc) : P (Arlib.Computation.Charged.foldl f xs acc).val := by
    induction xs generalizing acc with
    | nil => exact hp
    | cons i xs ih =>
        rw [Arlib.Computation.Charged.val_foldl_cons]
        exact ih _ (hlist _ acc hp)
  let countPair := fun i : Fin n =>
    (if decide ((i, false) ∈ state) = occupied then 1 else 0 : ℕ) +
    (if decide ((i, true) ∈ state) = occupied then 1 else 0 : ℕ)
  have hpaircount (acc : Option (PairedGround n) × ℕ) (i : Fin n) :
      (f acc i).val.2 = acc.2 + countPair i := by
    simp only [f, Arlib.Computation.Charged.val_foldl_cons,
      Arlib.Computation.Charged.val_foldl_nil, hvisit]
    dsimp only [countPair]
    split_ifs <;> rfl
  have hcount (xs : List (Fin n)) (acc : Option (PairedGround n) × ℕ) :
      (Arlib.Computation.Charged.foldl f xs acc).val.2 =
        acc.2 + (xs.map countPair).sum := by
    induction xs generalizing acc with
    | nil => simp
    | cons i xs ih =>
        rw [Arlib.Computation.Charged.val_foldl_cons, ih, hpaircount]
        simp only [List.map_cons, List.sum_cons]
        omega
  have hpopulation : ((List.finRange n).map countPair).sum = n := by
    let cv := fun (acc : Option (Fin n) × Option (Fin n) × Bool) (i : Fin n) => do
      let x ← Model.Operations.containsPaired state (i, false)
      let y ← Model.Operations.containsPaired state (i, true)
      if x then
        if y then
          let seen ← Model.Operations.isSome acc.2.1
          if seen then pure (acc.1, acc.2.1, true)
          else pure (acc.1, some i, acc.2.2)
        else pure acc
      else
        if y then pure acc
        else
          let seen ← Model.Operations.isSome acc.1
          if seen then pure (acc.1, acc.2.1, true)
          else pure (some i, acc.2.1, acc.2.2)
    let hole := fun acc : Option (Fin n) × Option (Fin n) × Bool =>
      if occupied then (if acc.1.isSome then 1 else 0 : ℕ)
      else (if acc.2.1.isSome then 1 else 0 : ℕ)
    let full := fun acc : Option (Fin n) × Option (Fin n) × Bool =>
      if occupied then (if acc.2.1.isSome then 1 else 0 : ℕ)
      else (if acc.1.isSome then 1 else 0 : ℕ)
    have hclassStep (acc : Option (Fin n) × Option (Fin n) × Bool) (i : Fin n)
        (hflag : (cv acc i).val.2.2 = false) :
        acc.2.2 = false ∧
          countPair i + hole (cv acc i).val + full acc =
            1 + full (cv acc i).val + hole acc := by
      rcases acc with ⟨empty, fullIndex, flag⟩
      cases occupied <;> by_cases hx : (i, false) ∈ state <;>
        by_cases hy : (i, true) ∈ state <;> cases empty <;> cases fullIndex <;>
        cases flag <;>
        simp [cv, hole, full, countPair, hx, hy, Model.Operations.containsPaired,
          Model.Operations.isSome] at hflag ⊢
    have hclassFold (xs : List (Fin n))
        (acc : Option (Fin n) × Option (Fin n) × Bool)
        (hflag : (Arlib.Computation.Charged.foldl cv xs acc).val.2.2 = false) :
        acc.2.2 = false ∧
          (xs.map countPair).sum +
              hole (Arlib.Computation.Charged.foldl cv xs acc).val + full acc =
            xs.length + full (Arlib.Computation.Charged.foldl cv xs acc).val + hole acc := by
      induction xs generalizing acc with
      | nil =>
          refine ⟨hflag, ?_⟩
          simp only [Arlib.Computation.Charged.val_foldl_nil, List.map_nil,
            List.sum_nil, List.length_nil]
          omega
      | cons i xs ih =>
          rw [Arlib.Computation.Charged.val_foldl_cons] at hflag ⊢
          obtain ⟨hmiddle, hsum⟩ := ih (cv acc i).val hflag
          obtain ⟨hacc, hstep⟩ := hclassStep acc i hmiddle
          refine ⟨hacc, ?_⟩
          simp only [List.map_cons, List.sum_cons, List.length_cons]
          omega
    let classified := (Arlib.Computation.Charged.foldl cv
      (List.finRange n) (none, none, false)).val
    unfold classifyState at hvalid
    simp only [Arlib.Computation.Charged.val_bind] at hvalid
    change (if classified.2.2 then pure .invalid else
      match classified.1, classified.2.1 with
      | none, none => pure .transversal
      | some i, some j => do
          let diagonal ← Model.Operations.indexEqual i j
          if diagonal then pure .invalid else pure (.defect i j)
      | _, _ => pure .invalid : Arlib.Computation.Charged Model.Operations.Op
        Model.Operations.Cell (StateKind n)).val ≠ .invalid at hvalid
    by_cases hbadflag : classified.2.2 = true
    · rw [if_pos hbadflag] at hvalid
      exact False.elim (hvalid rfl)
    · rw [if_neg hbadflag] at hvalid
      have hflag : classified.2.2 = false := by
        cases hb : classified.2.2 <;> simp_all
      have hbalance : hole classified = full classified := by
        cases he : classified.1 <;> cases hf : classified.2.1
        · simp [hole, full, he, hf]
        · simp only [he, hf, Arlib.Computation.Charged.val_pure] at hvalid
          exact False.elim (hvalid rfl)
        · simp only [he, hf, Arlib.Computation.Charged.val_pure] at hvalid
          exact False.elim (hvalid rfl)
        · simp [hole, full, he, hf]
      have hsum := (hclassFold (List.finRange n) (none, none, false) hflag).2
      change ((List.finRange n).map countPair).sum + hole classified +
          full (none, none, false) =
        (List.finRange n).length + full classified + hole (none, none, false) at hsum
      have hzH : hole (none, none, false) = 0 := by simp [hole]
      have hzF : full (none, none, false) = 0 := by simp [full]
      have hlength : (List.finRange n).length = n := by simp
      rw [hzH, hzF, hlength, hbalance] at hsum
      omega
  let result := (Arlib.Computation.Charged.foldl f (List.finRange n) (none, 0)).val
  have hbound : result.1 = none → result.2 ≤ k :=
    houter (List.finRange n) (none, 0) (by intro _; omega)
  change ∃ element, result.1 = some element
  cases hout : result.1 with
  | none =>
      have hle := hbound hout
      have hn : result.2 = n := by
        simpa only [result, hpopulation, Nat.zero_add] using
          hcount (List.finRange n) (none, 0)
      omega
  | some element => exact ⟨element, rfl⟩
