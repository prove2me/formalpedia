-- Prove2me | solution 1 for CountingMatroid.Analysis.CappedTraceReturnSubkernel.trace_return_scan_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-24T15:06:51.281557+00:00
-- url     : https://prove2.me/submissions/54abb11b-87cf-4e6d-abf0-1578c64d8770

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
import Definitions.Def_CountingMatroidSupport_MarkovChains_Techniques_Dirichlet
import Definitions.Def_CountingMatroidSupport_MarkovChains_Techniques_HittingTime
import Definitions.Def_CountingMatroidSupport_MarkovChains_Techniques_PotentialDecay
import Definitions.Def_CountingMatroidSupport_MarkovChains_Techniques_SpectralGap
import Definitions.Def_CountingMatroidSupport_Probability_Bilinear
import Definitions.Def_CountingMatroidSupport_Probability_FinDist
import Definitions.Def_CountingMatroidSupport_Probability_FinDistFunctional
import Definitions.Def_CountingMatroid_Analysis_BoundedUniformReplay
import Definitions.Def_CountingMatroid_Analysis_CappedTraceReturnSubkernel
import Definitions.Def_CountingMatroid_Analysis_ChainStepIntervalReplay
import Definitions.Def_CountingMatroid_Analysis_FiniteStoppedFiberMass
import Definitions.Def_CountingMatroid_Analysis_PositiveTimeTraceKernel
import Definitions.Def_CountingMatroid_Model_Operations
import Definitions.Def_CountingMatroid_Model_Prelude
import Definitions.Def_CountingMatroid_Model_Program
import Definitions.Def_CountingMatroid_Model_Subroutines
import Lean
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Defs
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Algebra.Order.Floor.Defs
import Mathlib.Algebra.Order.Group.Int
import Mathlib.Algebra.QuadraticDiscriminant
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Analysis.SpecialFunctions.Log.Basic
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
import Mathlib.Topology.Order.MonotoneConvergence

namespace Arlib.MarkovChains
end Arlib.MarkovChains
namespace Arlib.MarkovChains.FinChain
end Arlib.MarkovChains.FinChain
namespace Arlib.MarkovChains.FinKernel
end Arlib.MarkovChains.FinKernel
namespace Arlib
end Arlib
namespace Arlib.Probability
end Arlib.Probability
namespace Arlib.Probability.FinDist
end Arlib.Probability.FinDist
namespace Arlib.Probability.FinKernel
end Arlib.Probability.FinKernel
namespace CountingMatroid.Meta
end CountingMatroid.Meta
namespace CountingMatroid.Analysis.ChainStepNoninvalid
end CountingMatroid.Analysis.ChainStepNoninvalid
section


set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

/-! The successful finite-tape sublaw of an operational positive-time return.
The recursive scan keeps the global attempt counter and aborts explicitly. -/
namespace CountingMatroid.Analysis.CappedTraceReturnSubkernel
open CountingMatroid.Model CountingMatroid.Program
open CountingMatroid.Analysis.FiniteStoppedFiberMass
open CountingMatroid.Analysis.PositiveTimeTraceKernel









/-- INTERNAL: Expose the value recursion of a charged early-break fold. -/
private theorem foldlWhile_cons_value {α β : Type}
    (f : β → α → Arlib.Computation.Charged Model.Operations.Op Model.Operations.Cell (Option β))
    (a : α) (xs : List α) (b : β) :
    (Arlib.Computation.Charged.foldlWhile f (a :: xs) b).val =
      match (f b a).val with
      | none => b
      | some next => (Arlib.Computation.Charged.foldlWhile f xs next).val := by
  cases h : (f b a).val <;>
    simp only [Arlib.Computation.Charged.val] at h ⊢ <;>
    simp [Arlib.Computation.Charged.foldlWhile, h]





end CountingMatroid.Analysis.CappedTraceReturnSubkernel

/-! ### Run record
Newest first. History, not instruction — what this file claims is above.

* 2026-10-09 · proved · recursive globally capped return scan equals traceReturn; induction on its horizon composes the covered one-step comparison with finite stopped-prefix bounds.
-/

end
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

/-! The successful finite-tape sublaw of an operational positive-time return.
The recursive scan keeps the global attempt counter and aborts explicitly. -/
namespace CountingMatroid.Analysis.CappedTraceReturnSubkernel
end CountingMatroid.Analysis.CappedTraceReturnSubkernel
open CountingMatroid CountingMatroid.Analysis CountingMatroid.Analysis.CappedTraceReturnSubkernel
open CountingMatroid.Model CountingMatroid.Program
open CountingMatroid.Analysis.FiniteStoppedFiberMass
open CountingMatroid.Analysis.PositiveTimeTraceKernel

/-- INTERNAL: The recursive return scan equals the actual charged scan,
including its positive-time convention, global cap guard, and abort branches.
TEXLINE: main.tex:1163-1176 -/
theorem solution {n : ℕ} (r : ℕ) (o₁ o₂ : IndependenceOracle n)
    (tape : ℕ → Bool) (s : AnnealingSchedule) (q : ℚ) (w : Multipliers n)
    (current : RestartCursor n) :
    (traceReturn r o₁ o₂ tape s q w current).val =
      returnScan r o₁ o₂ tape s q w s.restartCap current := by
  let body : (Option (RestartCursor n) × Bool) → ℕ →
      Arlib.Computation.Charged Model.Operations.Op Model.Operations.Cell
        (Option (Option (RestartCursor n) × Bool)) := fun acc _ => do
    if acc.2 then pure none
    else match acc.1 with
      | none => pure none
      | some current =>
          let allowed ← Model.Operations.lessThan current.attempts s.restartCap
          if allowed then
            let attempted ← chainStep r o₁ o₂ tape s.drawTrials q w current.state current.bitCursor
            let attempts ← Model.Operations.successor current.attempts
            match attempted with
            | none => pure (some (none, true))
            | some (state, bitCursor) =>
                let kind ← classifyState state
                let returned ← match kind with
                  | .transversal => pure true
                  | _ => pure false
                pure (some (some ⟨state, bitCursor, attempts⟩, returned))
          else pure (some (none, true))
  let scan := fun xs acc => (Arlib.Computation.Charged.foldlWhile body xs acc).val
  have hstopped (xs : List ℕ) (acc : Option (RestartCursor n)) :
      scan xs (acc, true) = (acc, true) := by
    cases xs with
    | nil => rfl
    | cons a xs =>
      rw [show scan (a::xs) (acc,true) = _ from foldlWhile_cons_value _ _ _ _]
      rfl
  have hrec : ∀ (xs : List ℕ) (current : RestartCursor n),
      (if (scan xs (some current,false)).2 then (scan xs (some current,false)).1 else none) =
        returnScan r o₁ o₂ tape s q w xs.length current := by
    intro xs
    induction xs with
    | nil => intro current; rfl
    | cons a xs ih =>
      intro current
      have hvalue : scan (a::xs) (some current,false) =
          match (body (some current,false) a).val with
          | none => (some current,false)
          | some next => scan xs next := by
        dsimp only [scan]
        rw [foldlWhile_cons_value]
        cases (body (some current,false) a).val <;> rfl
      rw [hvalue]
      simp only [body, Bool.false_eq_true, if_false, Arlib.Computation.Charged.val_bind,
        Model.Operations.lessThan, Arlib.Computation.Charged.val_op, List.length_cons,
        returnScan, decide_eq_true_eq]
      by_cases ha : current.attempts < s.restartCap
      · simp only [ha, if_true, Arlib.Computation.Charged.val_bind]
        cases hs : (chainStep r o₁ o₂ tape s.drawTrials q w current.state current.bitCursor).val with
        | none => simp only [Arlib.Computation.Charged.val_pure, hstopped, if_true, Option.bind_none]
        | some step =>
          simp only [Arlib.Computation.Charged.val_bind, Model.Operations.successor,
            Arlib.Computation.Charged.val_op, Option.bind_some]
          cases step with
          | mk state stop =>
            cases hk : (classifyState state).val <;>
              simp only [hk, Arlib.Computation.Charged.val_bind, Arlib.Computation.Charged.val_pure]
            · simp only [hstopped, if_true]
            · exact ih ⟨state, stop, current.attempts+1⟩
            · exact ih ⟨state, stop, current.attempts+1⟩
      · simp only [ha, if_false, Arlib.Computation.Charged.val_pure, hstopped, if_true]
  unfold traceReturn
  simp only [Arlib.Computation.Charged.val_bind, Arlib.Computation.Charged.repeatWhile]
  change (if (scan (List.range s.restartCap) (some current,false)).2 then
    pure (scan (List.range s.restartCap) (some current,false)).1 else pure none :
    Arlib.Computation.Charged Model.Operations.Op Model.Operations.Cell
      (Option (RestartCursor n))).val = _
  have heq := hrec (List.range s.restartCap) current
  simp only [List.length_range] at heq
  split <;> rename_i hdone
  · simpa only [hdone, if_true, Arlib.Computation.Charged.val_pure] using heq
  · simpa only [hdone, Bool.false_eq_true, if_false, Arlib.Computation.Charged.val_pure] using heq
