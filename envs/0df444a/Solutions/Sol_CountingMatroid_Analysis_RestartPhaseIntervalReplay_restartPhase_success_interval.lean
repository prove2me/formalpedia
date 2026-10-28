-- Prove2me | solution 1 for CountingMatroid.Analysis.RestartPhaseIntervalReplay.restartPhase_success_interval
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-24T16:18:12.224408+00:00
-- url     : https://prove2.me/submissions/609f5bdc-8bae-49ce-99ba-b405ada7b277

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
import Theorems.Thm_CountingMatroid_Analysis_ChainStepIntervalReplay_foldl_successReplay
import Theorems.Thm_CountingMatroid_Analysis_TraceReturnIntervalReplay_traceReturn_success_interval

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
Successful capped phase restarts have monotone fair-bit cursors and replay
from their consumed intervals. The proof composes the exact fresh transversal
scan, capped trace-return replay, and the two nested absorbing-option folds.
No probability estimate or independence premise is assumed here.
-/

namespace CountingMatroid.Analysis.RestartPhaseIntervalReplay
end CountingMatroid.Analysis.RestartPhaseIntervalReplay
open CountingMatroid CountingMatroid.Analysis CountingMatroid.Analysis.RestartPhaseIntervalReplay
open CountingMatroid.Model CountingMatroid.Model.Operations CountingMatroid.Program
open CountingMatroid.Analysis.ChainStepIntervalReplay

/-- INTERNAL: A successful capped restart has a monotone fair-bit cursor and
replays from exactly the interval consumed, including all trace-return stages.
TEXLINE: main.tex:1163-1176,1392-1421 -/
theorem solution {n : ℕ} (r : ℕ)
    (o₁ o₂ : IndependenceOracle n) (s : AnnealingSchedule)
    (tables : LearnedWeights n) (j start : ℕ) :
    SuccessReplay (fun tape => (restartPhase r o₁ o₂ tape s tables j start).val)
      Prod.snd start := by
  let stage : (ℕ → Bool) → Option (RestartCursor n) → ℕ →
      Arlib.Computation.Charged CountingMatroid.Model.Operations.Op
        CountingMatroid.Model.Operations.Cell (Option (RestartCursor n)) :=
    fun tape current index => do
      match current with
      | none => pure none
      | some current =>
          let a ← CountingMatroid.Model.Operations.successor index
          let q ← ratPower s.ρ a
          let weights ← CountingMatroid.Model.Operations.learnedWeightRead tables a s.L
          Arlib.Computation.Charged.repeatFor (fun _ current => do
            match current with
            | none => pure none
            | some current => traceReturn r o₁ o₂ tape s q weights current)
            s.τ (some current)
  let cross := fun tape current =>
    (Arlib.Computation.Charged.foldl (stage tape) (List.range j) (some current)).val
  have hcross : ∀ current, SuccessReplay (fun tape => cross tape current)
      RestartCursor.bitCursor current.bitCursor := by
    intro current
    apply foldl_successReplay
    · intro tape a
      rfl
    · intro current index
      dsimp only [stage]
      simp only [Arlib.Computation.Charged.val_bind, Arlib.Computation.Charged.repeatFor]
      apply foldl_successReplay
      · intro tape a
        rfl
      · intro current a
        exact TraceReturnIntervalReplay.traceReturn_success_interval r o₁ o₂ s _ _ current
  intro tape out hrun
  let initial : RestartCursor n :=
    ⟨(freshTransversal n tape start).val.1, (freshTransversal n tape start).val.2, 0⟩
  unfold restartPhase at hrun
  simp only [Arlib.Computation.Charged.val_bind, Arlib.Computation.Charged.repeatFor] at hrun
  change (match cross tape initial with
    | none => pure none
    | some result => pure (some (result.state, result.bitCursor)) :
      Arlib.Computation.Charged Op Cell (Option (PairedSet n × ℕ))).val = some out at hrun
  cases hresult : cross tape initial with
  | none =>
      simp only [hresult, Arlib.Computation.Charged.val_pure] at hrun
      contradiction
  | some result =>
      simp only [hresult, Arlib.Computation.Charged.val_pure] at hrun
      have hout : (result.state, result.bitCursor) = out := Option.some.inj hrun
      subst out
      have hlocal := hcross initial tape result hresult
      have hinit : initial.bitCursor = start + n := by
        simp only [initial, InitialRestartLaw.freshTransversal_value]
      have hstart : start ≤ initial.bitCursor := by rw [hinit]; omega
      refine ⟨hstart.trans hlocal.1, ?_⟩
      intro other hagree
      have hfresh : (freshTransversal n other start).val =
          (freshTransversal n tape start).val := by
        rw [InitialRestartLaw.freshTransversal_value, InitialRestartLaw.freshTransversal_value]
        congr 1
        apply Finset.image_congr
        intro i _
        change (i, other (start + i.val)) = (i, tape (start + i.val))
        congr 1
        exact (hagree (start + i.val) (by omega) (by
          have hi := i.isLt
          rw [hinit] at hlocal
          omega)).symm
      have heq := hlocal.2 other (fun i hlo hhi => hagree i (hstart.trans hlo) hhi)
      dsimp only at heq
      unfold restartPhase
      simp only [Arlib.Computation.Charged.val_bind, hfresh,
        Arlib.Computation.Charged.repeatFor]
      change (match cross other initial with
        | none => pure none
        | some result => pure (some (result.state, result.bitCursor)) :
      Arlib.Computation.Charged Op Cell (Option (PairedSet n × ℕ))).val =
          some (result.state, result.bitCursor)
      rw [heq]
      rfl
