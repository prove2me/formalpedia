-- Prove2me | solution 1 for CountingMatroid.Analysis.RestartPhaseTransversal.freshTransversal_transversal
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-24T15:09:51.925787+00:00
-- url     : https://prove2.me/submissions/e2728223-a61e-4082-b8c4-515ed2bb082f

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
import Definitions.Def_CountingMatroid_Analysis_BoundedUniformReplay
import Definitions.Def_CountingMatroid_Analysis_ChainStepIntervalReplay
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
import Mathlib.Data.List.Nodup
import Mathlib.Data.List.OfFn
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

namespace CountingMatroid.Analysis.InitialRestartLaw
end CountingMatroid.Analysis.InitialRestartLaw
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
namespace CountingMatroid.Analysis.RestartPhaseTransversal
end CountingMatroid.Analysis.RestartPhaseTransversal
namespace CountingMatroid.Analysis.RestartPhaseIntervalReplay
end CountingMatroid.Analysis.RestartPhaseIntervalReplay
namespace CountingMatroid.Analysis.TraceReturnIntervalReplay
end CountingMatroid.Analysis.TraceReturnIntervalReplay
section


set_option autoImplicit false

/-!
The phase-zero restart is exactly a fresh uniform transversal, with no return
excursion or restart-cap failure. The lemmas below retain the actual bit cursor
and the finite-tape suffix, rather than supplying a new random source.
-/

namespace CountingMatroid.Analysis.InitialRestartLaw

open CountingMatroid.Model CountingMatroid.Model.Operations CountingMatroid.Program

/-- INTERNAL: Split a charged fold's value at a list boundary. -/
private theorem foldl_append_value {α β : Type}
    (f : β → α → Arlib.Computation.Charged Op Cell β)
    (xs ys : List α) (initial : β) :
    (Arlib.Computation.Charged.foldl f (xs ++ ys) initial).val =
      (Arlib.Computation.Charged.foldl f ys
        (Arlib.Computation.Charged.foldl f xs initial).val).val := by
  induction xs generalizing initial with
  | nil => rfl
  | cons x xs ih =>
      simpa only [List.cons_append, Arlib.Computation.Charged.val_foldl_cons]
        using ih (f initial x).val

/-- INTERNAL: Evaluate the fresh-bit scan on an indexed list, including its
cursor movement and all elements inserted into the actual paired set.
TEXLINE: main.tex:1163-1176 -/
private theorem fresh_scan_value {n : ℕ} (tape : ℕ → Bool) (k : ℕ)
    (indices : Fin k → Fin n) (state : PairedSet n) (cursor : ℕ) :
    (Arlib.Computation.Charged.foldl (fun acc i => do
      let bit ← fairBit tape acc.2
      let state ← insertPaired acc.1 (i, bit)
      let next ← successor acc.2
      pure (state, next)) (List.ofFn indices) (state, cursor)).val =
      (state ∪ Finset.univ.image (fun i : Fin k => (indices i, tape (cursor + i))),
        cursor + k) := by
  induction k generalizing state cursor with
  | zero => simp
  | succ k ih =>
      rw [List.ofFn_succ', List.concat_eq_append]
      change (Arlib.Computation.Charged.foldl _
        (List.ofFn (fun i : Fin k => indices i.castSucc) ++ [indices (Fin.last k)])
          (state, cursor)).val = _
      rw [foldl_append_value, ih]
      simp only [Arlib.Computation.Charged.val_foldl_cons,
        Arlib.Computation.Charged.val_foldl_nil, Arlib.Computation.Charged.val_bind,
        fairBit, insertPaired, successor, Arlib.Computation.Charged.val_op,
        Arlib.Computation.Charged.val_opMany, Arlib.Computation.Charged.val_pure]
      congr 1
      · rw [Fin.univ_castSuccEmb, Finset.cons_eq_insert, Finset.image_insert,
          Finset.map_eq_image, Finset.image_image]
        simp only [Fin.coe_castSuccEmb, Fin.val_last]
        simp only [Finset.union_insert]
        rfl

/-- PAPER: main.tex:1163-1176
A fresh restart reads precisely the next n bits and selects one element from
each pair. This equality also identifies the law when those bits are fair. -/
theorem freshTransversal_value (n : ℕ) (tape : ℕ → Bool) (cursor : ℕ) :
    (freshTransversal n tape cursor).val =
      (Finset.univ.image (fun i : Fin n => (i, tape (cursor + i))), cursor + n) := by
  simpa only [freshTransversal, ← List.ofFn_id, Finset.empty_union, id_eq] using
    fresh_scan_value tape n id (∅ : PairedSet n) cursor




















end CountingMatroid.Analysis.InitialRestartLaw

/-! ### Run record
Newest first. History, not instruction — what this file claims is above.

* r19 · proved · evaluated the actual fresh-bit scan and phase-zero restart,
  split finite tapes into equally weighted prefixes and observation suffixes,
  and derived the exact initial certificate-failure mass identity. No chain
  concentration bound, extra hypothesis, or unproved declaration introduced.
-/

end
set_option autoImplicit false

/-!
Every successful capped return ends in the transversal class. Consequently
successful restarts return a transversal, including phases with no crossed
levels or no trace transitions. These are deterministic operational facts;
they make no probability or finite-tape coverage claim.
-/

namespace CountingMatroid.Analysis.RestartPhaseTransversal
end CountingMatroid.Analysis.RestartPhaseTransversal
open CountingMatroid CountingMatroid.Analysis CountingMatroid.Analysis.RestartPhaseTransversal

open CountingMatroid.Model CountingMatroid.Model.Operations CountingMatroid.Program

/-- INTERNAL: The concrete fresh-bit restart set is classified as a
transversal on every tape, including the empty ground.
TEXLINE: main.tex:1163-1176 -/
theorem solution (n : ℕ) (tape : ℕ → Bool) (cursor : ℕ) :
    (classifyState (freshTransversal n tape cursor).val.1).val = .transversal := by
  rw [InitialRestartLaw.freshTransversal_value]
  let state : PairedSet n := Finset.univ.image (fun i : Fin n => (i, tape (cursor + i)))
  have hpair (i : Fin n) (b : Bool) : (i, b) ∈ state ↔ tape (cursor + i) = b := by
    simp [state, Finset.mem_image, Prod.mk.injEq]
  let visit := fun (acc : Option (Fin n) × Option (Fin n) × Bool) (i : Fin n) => do
    let x ← containsPaired state (i, false)
    let y ← containsPaired state (i, true)
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
  have hvisit (acc : Option (Fin n) × Option (Fin n) × Bool) (i : Fin n) :
      (visit acc i).val = acc := by
    cases ht : tape (cursor + i) <;>
      simp [visit, containsPaired, hpair, ht]
  have hfold (xs : List (Fin n)) (acc : Option (Fin n) × Option (Fin n) × Bool) :
      (Arlib.Computation.Charged.foldl visit xs acc).val = acc := by
    induction xs generalizing acc with
    | nil => rfl
    | cons i xs ih => rw [Arlib.Computation.Charged.val_foldl_cons, hvisit, ih]
  change (classifyState state).val = .transversal
  unfold classifyState
  change ((do
    let result ← Arlib.Computation.Charged.foldl visit (List.finRange n) (none, none, false)
    if result.2.2 then pure .invalid else
      match result.1, result.2.1 with
      | none, none => pure .transversal
      | some i, some j => do
          let diagonal ← indexEqual i j
          if diagonal then pure .invalid else pure (.defect i j)
      | _, _ => pure .invalid) : Arlib.Computation.Charged Op Cell (StateKind n)).val = _
  rw [Arlib.Computation.Charged.val_bind, hfold]
  rfl
