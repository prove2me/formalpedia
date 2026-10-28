-- Prove2me | solution 1 for CountingMatroid.Analysis.ReturnAttemptTail.counted_return_count
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-24T15:17:25.871849+00:00
-- url     : https://prove2.me/submissions/12433343-e3d0-4fbc-9cb7-965b8e3857c7

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
import Definitions.Def_CountingMatroid_Analysis_AnnealingPartitionDrift
import Definitions.Def_CountingMatroid_Analysis_BoundedRunPhase
import Definitions.Def_CountingMatroid_Analysis_BoundedRunPhaseHistory
import Definitions.Def_CountingMatroid_Analysis_BoundedRunPhaseWork
import Definitions.Def_CountingMatroid_Analysis_BoundedUniformAbortMass
import Definitions.Def_CountingMatroid_Analysis_BoundedUniformReplay
import Definitions.Def_CountingMatroid_Analysis_CappedTraceReturnSubkernel
import Definitions.Def_CountingMatroid_Analysis_ChainStepIntervalReplay
import Definitions.Def_CountingMatroid_Analysis_DefectPartitionPositive
import Definitions.Def_CountingMatroid_Analysis_EmpiricalPhaseCertificate
import Definitions.Def_CountingMatroid_Analysis_EstimateMedianResource
import Definitions.Def_CountingMatroid_Analysis_FinishPhaseEmpiricalUpdate
import Definitions.Def_CountingMatroid_Analysis_FinishPhaseWork
import Definitions.Def_CountingMatroid_Analysis_FiniteStoppedFiberMass
import Definitions.Def_CountingMatroid_Analysis_FirstPhaseFailure
import Definitions.Def_CountingMatroid_Analysis_InitialMultipliersGood
import Definitions.Def_CountingMatroid_Analysis_ObservePhaseWork
import Definitions.Def_CountingMatroid_Analysis_PhaseChainWork
import Definitions.Def_CountingMatroid_Analysis_PhaseMeanCertificate
import Definitions.Def_CountingMatroid_Analysis_PhaseObservationExperiment
import Definitions.Def_CountingMatroid_Analysis_PhaseResourcePrimitives
import Definitions.Def_CountingMatroid_Analysis_PositiveTimeTraceKernel
import Definitions.Def_CountingMatroid_Analysis_RationalHeight
import Definitions.Def_CountingMatroid_Analysis_RelativeObservationBounds
import Definitions.Def_CountingMatroid_Analysis_RestartAttemptAccounting
import Definitions.Def_CountingMatroid_Analysis_ReturnAttemptTail
import Definitions.Def_CountingMatroid_Analysis_ScheduleConfidence
import Definitions.Def_CountingMatroid_Analysis_ScheduleOpeningCost
import Definitions.Def_CountingMatroid_Analysis_ScheduleThermalSetupCost
import Definitions.Def_CountingMatroid_Analysis_StationaryMeanIdentities
import Definitions.Def_CountingMatroid_Analysis_StationaryReturnOccupation
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
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Defs
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Algebra.Order.Floor.Defs
import Mathlib.Algebra.Order.Group.Int
import Mathlib.Algebra.Order.Ring.Pow
import Mathlib.Algebra.QuadraticDiscriminant
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Combinatorics.Matroid.Rank.ENat
import Mathlib.Data.BitVec
import Mathlib.Data.ENNReal.Inv
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Vector
import Mathlib.Data.List.Basic
import Mathlib.Data.List.Induction
import Mathlib.Data.List.Infix
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
namespace CountingMatroid.Analysis.FiniteObservationMarkov
end CountingMatroid.Analysis.FiniteObservationMarkov
namespace CountingMatroid.Analysis.FiniteTapePrefixBound
end CountingMatroid.Analysis.FiniteTapePrefixBound
namespace CountingMatroid.Analysis.InitialRestartLaw
end CountingMatroid.Analysis.InitialRestartLaw
namespace CountingMatroid.Interface
end CountingMatroid.Interface
namespace CountingMatroid.Analysis.TransversalRankBridge
end CountingMatroid.Analysis.TransversalRankBridge
namespace CountingMatroid.Analysis.GreedyRankCorrect
end CountingMatroid.Analysis.GreedyRankCorrect
namespace CountingMatroid.Analysis.SuccessfulPrefixAbortBound
end CountingMatroid.Analysis.SuccessfulPrefixAbortBound
namespace CountingMatroid.Analysis.BoundedRunResourceEnvelope
end CountingMatroid.Analysis.BoundedRunResourceEnvelope
namespace CountingMatroid.Analysis.BoundedRunOtherSteps
end CountingMatroid.Analysis.BoundedRunOtherSteps
namespace CountingMatroid.Analysis.ScheduleOtherStepsEnvelope
end CountingMatroid.Analysis.ScheduleOtherStepsEnvelope
namespace CountingMatroid.Analysis.LeastHalvingsCost
end CountingMatroid.Analysis.LeastHalvingsCost
namespace CountingMatroid.Analysis
end CountingMatroid.Analysis
namespace CountingMatroid.Analysis.RestartPhaseWork
end CountingMatroid.Analysis.RestartPhaseWork
namespace CountingMatroid.Analysis.BoundedRunPhase
end CountingMatroid.Analysis.BoundedRunPhase
namespace CountingMatroid.Analysis.FinishPhaseWeightsSize
end CountingMatroid.Analysis.FinishPhaseWeightsSize
namespace CountingMatroid.Analysis.BoundedRunOracleCalls
end CountingMatroid.Analysis.BoundedRunOracleCalls
namespace CountingMatroid.Analysis.ResourceBound
end CountingMatroid.Analysis.ResourceBound
section


set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

/-!
The number of `chainStep` attempts made by one actual positive-time return,
as a value recursion. The instrumented return adds exactly this number to its
retained counter, including the attempt that ends in a draw abort. On a fresh
finite suffix whose every attempted step stays inside the block, the chance of
making more than m attempts is at most the ideal positive-time survival tail.
-/
namespace CountingMatroid.Analysis.ReturnAttemptTail

open CountingMatroid.Model CountingMatroid.Program
open CountingMatroid.Analysis.FiniteStoppedFiberMass
open CountingMatroid.Analysis.PositiveTimeTraceKernel
open CountingMatroid.Analysis.RestartAttemptAccounting
open Arlib.Probability Arlib.MarkovChains





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















end CountingMatroid.Analysis.ReturnAttemptTail

/-! ### Run record
Newest first. History, not instruction — what this file claims is above.

* 2026-10-09 · created · per-return attempt recursion, exact retained-count identity for the instrumented return, occupation budget as tail sums, and the covered attempt-tail bound.
-/

end
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

/-!
The number of `chainStep` attempts made by one actual positive-time return,
as a value recursion. The instrumented return adds exactly this number to its
retained counter, including the attempt that ends in a draw abort. On a fresh
finite suffix whose every attempted step stays inside the block, the chance of
making more than m attempts is at most the ideal positive-time survival tail.
-/
namespace CountingMatroid.Analysis.ReturnAttemptTail
end CountingMatroid.Analysis.ReturnAttemptTail
open CountingMatroid CountingMatroid.Analysis CountingMatroid.Analysis.ReturnAttemptTail

open CountingMatroid.Model CountingMatroid.Program
open CountingMatroid.Analysis.FiniteStoppedFiberMass
open CountingMatroid.Analysis.PositiveTimeTraceKernel
open CountingMatroid.Analysis.RestartAttemptAccounting
open Arlib.Probability Arlib.MarkovChains

/-- INTERNAL: The instrumented return adds exactly the scan's attempts to its
retained counter, whatever the outcome.
TEXLINE: main.tex:1163-1176 -/
theorem solution {n : ℕ} (r : ℕ) (o₁ o₂ : IndependenceOracle n)
    (tape : ℕ → Bool) (s : AnnealingSchedule) (q : ℚ) (w : Multipliers n)
    (start : RestartCursor n) (count : ℕ) :
    (countedReturn r o₁ o₂ tape s q w start count).val.2 =
      count + attemptScan r o₁ o₂ tape s q w s.restartCap start := by
  let body := fun (acc : (Option (RestartCursor n) × Bool) × ℕ) (_ : ℕ) =>
    countedBody r o₁ o₂ tape s q w acc
  let scan := fun xs acc => (Arlib.Computation.Charged.foldlWhile body xs acc).val
  have hstopped (xs : List ℕ) (acc : Option (RestartCursor n)) (c : ℕ) :
      scan xs ((acc, true), c) = ((acc, true), c) := by
    cases xs with
    | nil => rfl
    | cons a xs =>
      rw [show scan (a::xs) ((acc,true),c) = _ from foldlWhile_cons_value _ _ _ _]
      rfl
  have hnone (xs : List ℕ) (c : ℕ) :
      scan xs ((none, false), c) = ((none, false), c) := by
    cases xs with
    | nil => rfl
    | cons a xs =>
      rw [show scan (a::xs) ((none,false),c) = _ from foldlWhile_cons_value _ _ _ _]
      rfl
  have hrec : ∀ (xs : List ℕ) (current : RestartCursor n) (c : ℕ),
      (scan xs ((some current, false), c)).2 =
        c + attemptScan r o₁ o₂ tape s q w xs.length current := by
    intro xs
    induction xs with
    | nil => intro current c; rfl
    | cons a xs ih =>
      intro current c
      have hvalue : scan (a::xs) ((some current, false), c) =
          match (body ((some current, false), c) a).val with
          | none => ((some current, false), c)
          | some next => scan xs next := by
        dsimp only [scan]
        rw [foldlWhile_cons_value]
        cases (body ((some current, false), c) a).val <;> rfl
      rw [hvalue]
      simp only [body, countedBody, traceBody, attemptIncrement, Bool.false_eq_true,
        if_false, Arlib.Computation.Charged.val_bind, Model.Operations.lessThan,
        Arlib.Computation.Charged.val_op, List.length_cons, attemptScan,
        decide_eq_true_eq, Arlib.Computation.Charged.val_pure]
      by_cases ha : current.attempts < s.restartCap
      · simp only [ha, if_true, Arlib.Computation.Charged.val_bind]
        cases hs : (chainStep r o₁ o₂ tape s.drawTrials q w current.state
            current.bitCursor).val with
        | none =>
            simp only [Arlib.Computation.Charged.val_pure, Option.map_some, hstopped]
        | some step =>
          simp only [Arlib.Computation.Charged.val_bind, Model.Operations.successor,
            Arlib.Computation.Charged.val_op]
          cases step with
          | mk state stop =>
            cases hk : (classifyState state).val <;>
              simp only [hk, Arlib.Computation.Charged.val_bind,
                Arlib.Computation.Charged.val_pure, Option.map_some, reduceCtorEq,
                if_true, if_false]
            · simp only [hstopped]
            · rw [ih]; omega
            · rw [ih]; omega
      · simp only [ha, if_false, Arlib.Computation.Charged.val_pure, Option.map_some,
          hstopped]
  unfold countedReturn
  simp only [Arlib.Computation.Charged.val_bind, Arlib.Computation.Charged.val_pure,
    Arlib.Computation.Charged.repeatWhile]
  have h := hrec (List.range s.restartCap) start count
  simp only [List.length_range] at h
  exact h
