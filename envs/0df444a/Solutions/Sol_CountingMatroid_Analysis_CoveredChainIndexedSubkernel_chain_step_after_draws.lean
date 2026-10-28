-- Prove2me | solution 1 for CountingMatroid.Analysis.CoveredChainIndexedSubkernel.chain_step_after_draws
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-24T15:10:22.599366+00:00
-- url     : https://prove2.me/submissions/fbb2e65a-272f-40ea-8655-3ad9135642fe

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
import Definitions.Def_CountingMatroidSupport_MarkovChains_Chains_Metropolis
import Definitions.Def_CountingMatroidSupport_Probability_Bilinear
import Definitions.Def_CountingMatroidSupport_Probability_FinDist
import Definitions.Def_CountingMatroidSupport_Probability_FinDistFunctional
import Definitions.Def_CountingMatroid_Analysis_BoundedRunPhase
import Definitions.Def_CountingMatroid_Analysis_BoundedRunPhaseHistory
import Definitions.Def_CountingMatroid_Analysis_BoundedRunPhaseWork
import Definitions.Def_CountingMatroid_Analysis_BoundedUniformAbortMass
import Definitions.Def_CountingMatroid_Analysis_BoundedUniformReplay
import Definitions.Def_CountingMatroid_Analysis_ChainDrawSiteReplay
import Definitions.Def_CountingMatroid_Analysis_ChainStepIntervalReplay
import Definitions.Def_CountingMatroid_Analysis_CoveredChainIndexedSubkernel
import Definitions.Def_CountingMatroid_Analysis_DefectPartitionPositive
import Definitions.Def_CountingMatroid_Analysis_EstimateMedianResource
import Definitions.Def_CountingMatroid_Analysis_FinishPhaseWork
import Definitions.Def_CountingMatroid_Analysis_FiniteStoppedFiberMass
import Definitions.Def_CountingMatroid_Analysis_FirstPhaseFailure
import Definitions.Def_CountingMatroid_Analysis_IdealExchangeChain
import Definitions.Def_CountingMatroid_Analysis_InitialMultipliersGood
import Definitions.Def_CountingMatroid_Analysis_ObservePhaseWork
import Definitions.Def_CountingMatroid_Analysis_PhaseChainWork
import Definitions.Def_CountingMatroid_Analysis_PhaseResourcePrimitives
import Definitions.Def_CountingMatroid_Analysis_ProgramExchangeAcceptanceSubkernel
import Definitions.Def_CountingMatroid_Analysis_RationalAcceptanceSubkernel
import Definitions.Def_CountingMatroid_Analysis_RationalHeight
import Definitions.Def_CountingMatroid_Analysis_RelativeObservationBounds
import Definitions.Def_CountingMatroid_Analysis_ScheduleConfidence
import Definitions.Def_CountingMatroid_Analysis_ScheduleOpeningCost
import Definitions.Def_CountingMatroid_Analysis_ScheduleThermalSetupCost
import Definitions.Def_CountingMatroid_Analysis_SelectedMetropolisKernel
import Definitions.Def_CountingMatroid_Analysis_SelectedPairedBijection
import Definitions.Def_CountingMatroid_Analysis_StationaryMeanIdentities
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
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Defs
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Algebra.Order.Floor.Defs
import Mathlib.Algebra.Order.Group.Int
import Mathlib.Algebra.QuadraticDiscriminant
import Mathlib.Analysis.Complex.ExponentialBounds
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
import Mathlib.Order.Interval.Finset.Fin
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
namespace CountingMatroid.Analysis.ObservationRoundDrawSites
end CountingMatroid.Analysis.ObservationRoundDrawSites
namespace CountingMatroid.Analysis.FiniteObservationMarkov
end CountingMatroid.Analysis.FiniteObservationMarkov
namespace CountingMatroid.Analysis.FiniteTapePrefixBound
end CountingMatroid.Analysis.FiniteTapePrefixBound
namespace CountingMatroid.Analysis.InitialRestartLaw
end CountingMatroid.Analysis.InitialRestartLaw
namespace CountingMatroid.Analysis.ExchangeProposalGeometry
end CountingMatroid.Analysis.ExchangeProposalGeometry
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
namespace CountingMatroid.Analysis.BoundedUniformSubkernel
end CountingMatroid.Analysis.BoundedUniformSubkernel
namespace CountingMatroid.Analysis.BoundedUniformSuccessWords
end CountingMatroid.Analysis.BoundedUniformSuccessWords
section


set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

/-! The charged selector enumerates the occupied and unoccupied labels
without repetition, in the program's fixed x/y order. -/
namespace CountingMatroid.Analysis.SelectedPairedBijection
open CountingMatroid.Model CountingMatroid.Program















/-- INTERNAL: Split a charged selector fold at a deterministic list boundary. -/
private theorem selection_fold_append {α β : Type}
    (f : β → α → Arlib.Computation.Charged Model.Operations.Op Model.Operations.Cell β)
    (xs ys : List α) (acc : β) :
    (Arlib.Computation.Charged.foldl f (xs ++ ys) acc).val =
      (Arlib.Computation.Charged.foldl f ys
        (Arlib.Computation.Charged.foldl f xs acc).val).val := by
  induction xs generalizing acc with
  | nil => rfl
  | cons x xs ih =>
      simpa only [List.cons_append, Arlib.Computation.Charged.val_foldl_cons]
        using ih (f acc x).val

/-- INTERNAL: One selection visit increments its eligible counter and records
only the unique matching position. -/
private theorem selection_visit_value {n : ℕ} (state : PairedSet n)
    (occupied : Bool) (k : ℕ) (acc : Option (PairedGround n) × ℕ)
    (a : PairedGround n) :
    (selectionVisit state occupied k acc a).val =
      if decide (a ∈ state) = occupied then
        (if acc.2 = k then some a else acc.1, acc.2 + 1) else acc := by
  cases occupied <;> by_cases ha : a ∈ state <;> by_cases hk : acc.2 = k <;>
    simp [selectionVisit, Model.Operations.containsPaired,
      Model.Operations.natEqual, Model.Operations.successor, ha, hk]

/-- INTERNAL: The charged scan is exactly indexed lookup in the filtered list. -/
private theorem selection_fold_lookup {n : ℕ} (state : PairedSet n)
    (occupied : Bool) (k : ℕ) (xs : List (PairedGround n)) :
    (Arlib.Computation.Charged.foldl (selectionVisit state occupied k)
      xs (none, 0)).val =
    ((xs.filter (fun a => decide (decide (a ∈ state) = occupied)))[k]?,
      (xs.filter (fun a => decide (decide (a ∈ state) = occupied))).length) := by
  induction xs using List.reverseRecOn with
  | nil => simp
  | append_singleton xs a ih =>
      rw [selection_fold_append, ih]
      simp only [Arlib.Computation.Charged.val_foldl_cons,
        Arlib.Computation.Charged.val_foldl_nil, selection_visit_value,
        List.filter_append, List.filter_cons, List.filter_nil]
      by_cases ha : decide (a ∈ state) = occupied
      · simp only [ha, decide_true, ite_true, List.length_append,
          List.length_cons, List.length_nil, Nat.add_zero]
        congr 1
        rw [List.getElem?_append]
        by_cases hk : k < (xs.filter (fun a => decide (decide (a ∈ state) = occupied))).length
        · rw [if_pos hk, if_neg (by omega)]
        · rw [if_neg hk]
          by_cases heq : (xs.filter (fun a => decide (decide (a ∈ state) = occupied))).length = k
          · simp [heq]
          · rw [if_neg heq, List.getElem?_eq_none (by omega),
              List.getElem?_eq_none (by simp; omega)]
      · simp [ha]

/-- INTERNAL: Flattening the two visits per index preserves the charged scan. -/
private theorem selection_fold_flatten {n : ℕ} (state : PairedSet n)
    (occupied : Bool) (k : ℕ) (xs : List (Fin n))
    (acc : Option (PairedGround n) × ℕ) :
    (Arlib.Computation.Charged.foldl (fun acc i =>
      Arlib.Computation.Charged.foldl (selectionVisit state occupied k)
        [(i, false), (i, true)] acc) xs acc).val =
    (Arlib.Computation.Charged.foldl (selectionVisit state occupied k)
      (xs.flatMap (fun i => [(i, false), (i, true)])) acc).val := by
  induction xs generalizing acc with
  | nil => rfl
  | cons i xs ih =>
      rw [Arlib.Computation.Charged.val_foldl_cons, ih, List.flatMap_cons,
        selection_fold_append]

/-- INTERNAL: Actual program lookup equals lookup in its ordered eligible list. -/
theorem select_paired_list {n : ℕ} (state : PairedSet n) (occupied : Bool) (k : ℕ) :
    (selectPaired state occupied k).val = (selectedLabels state occupied)[k]? := by
  simp only [selectPaired, Arlib.Computation.Charged.val_bind,
    Arlib.Computation.Charged.val_pure, selection_fold_flatten]
  rw [selection_fold_lookup]
  rfl



/-- INTERNAL: The selectedLabel map agrees with the executable selection result. -/
theorem select_paired_selectedLabel {n : ℕ} (state : PairedSet n)
    (occupied : Bool) (hcard : state.card = n) (k : Fin n) :
    (selectPaired state occupied k.val).val = some (selectedLabel state occupied hcard k).val := by
  rw [select_paired_list]
  exact List.getElem?_eq_getElem (by rw [selectedLabels_length state occupied hcard]; exact k.isLt)





end CountingMatroid.Analysis.SelectedPairedBijection

end
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

/-! Compose the three adaptive draw subkernels and the initial fair holding
bit in the selection-index coordinates of the executable chain. -/
namespace CountingMatroid.Analysis.CoveredChainIndexedSubkernel
end CountingMatroid.Analysis.CoveredChainIndexedSubkernel
open CountingMatroid CountingMatroid.Analysis CountingMatroid.Analysis.CoveredChainIndexedSubkernel
open CountingMatroid.Model CountingMatroid.Program
open CountingMatroid.Analysis.FiniteStoppedFiberMass
open CountingMatroid.Analysis.BoundedUniformSubkernel
open CountingMatroid.Analysis.SelectedPairedBijection
open CountingMatroid.Analysis.SelectedMetropolisKernel
open CountingMatroid.Analysis.RationalAcceptanceSubkernel
open CountingMatroid.Analysis.ProgramExchangeAcceptanceSubkernel
open CountingMatroid.Analysis.IdealExchangeChain

/-- INTERNAL: Once the two index draws are fixed, the actual chain step is
precisely its remaining classifier/weight/acceptance continuation. -/
theorem solution {n : ℕ} (r : ℕ) (o₁ o₂ : IndependenceOracle n)
    (trials : ℕ) (q : ℚ) (weights : Multipliers n) (state : PairedSet n)
    (hcard : state.card = n) (tape : ℕ → Bool) (start stopA stopB : ℕ)
    (i j : Fin n) (hhold : tape start = false)
    (ha : (boundedUniform tape trials n (start + 1)).val = (some i.val, stopA))
    (hb : (boundedUniform tape trials n stopA).val = (some j.val, stopB)) :
    (chainStep r o₁ o₂ tape trials q weights state start).val =
      proposalAttempt r o₁ o₂ trials q weights state
        (indexedCandidate state hcard i j) tape stopB := by
  simp +instances only [chainStep, Arlib.Computation.Charged.val_bind,
    Model.Operations.fairBit, Model.Operations.successor,
    Arlib.Computation.Charged.val_op, hhold, Bool.false_eq_true, ite_false,
    ha, hb, select_paired_selectedLabel state true hcard i,
    select_paired_selectedLabel state false hcard j,
    Model.Operations.erasePaired, Model.Operations.insertPaired,
    Arlib.Computation.Charged.val_opMany]
  cases hk : (classifyState (indexedCandidate state hcard i j)).val <;>
    simp +instances only [proposalAttempt, indexedCandidate] at hk ⊢
  all_goals
    simp +instances only [hk, reduceCtorEq, if_false, if_true, Arlib.Computation.Charged.val_pure,
      Arlib.Computation.Charged.val_bind]
  all_goals
    cases ho : (weightOfKind r o₁ o₂ q weights state (classifyState state).val).val <;>
    cases hn : (weightOfKind r o₁ o₂ q weights
      (indexedCandidate state hcard i j) (classifyState (indexedCandidate state hcard i j)).val).val <;>
    simp +instances [indexedCandidate, hk] at hn <;>
    simp +instances [ho, hn, rationalAccept, Model.Operations.ratDiv,
      Model.Operations.ratLess, Model.Operations.rationalDenominator,
      Model.Operations.rationalNumerator, Model.Operations.lessThan]
  all_goals
    split <;> simp +instances only [*, Arlib.Computation.Charged.val_pure,
      Arlib.Computation.Charged.val_bind, Arlib.Computation.Charged.val_opMany,
      Arlib.Computation.Charged.val_op]
  all_goals
    split <;> simp +instances [*, Arlib.Computation.Charged.val_bind,
      Arlib.Computation.Charged.val_pure, Arlib.Computation.Charged.val_op]

  all_goals split_ifs <;> rfl
