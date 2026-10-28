-- Prove2me | solution 1 for CountingMatroid.Analysis.StationaryMeanLowerBound.normalizer_decomposition
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-24T14:16:46.266753+00:00
-- url     : https://prove2.me/submissions/74b0616b-f4fb-462d-9bdf-adf3e3cffeb0

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
import Definitions.Def_CountingMatroid_Analysis_AnnealingPartitionDrift
import Definitions.Def_CountingMatroid_Analysis_BoundedRunPhase
import Definitions.Def_CountingMatroid_Analysis_BoundedRunPhaseHistory
import Definitions.Def_CountingMatroid_Analysis_BoundedRunPhaseWork
import Definitions.Def_CountingMatroid_Analysis_DefectPartitionPositive
import Definitions.Def_CountingMatroid_Analysis_EmpiricalPhaseCertificate
import Definitions.Def_CountingMatroid_Analysis_EstimateMedianResource
import Definitions.Def_CountingMatroid_Analysis_FinishPhaseEmpiricalUpdate
import Definitions.Def_CountingMatroid_Analysis_FinishPhaseWork
import Definitions.Def_CountingMatroid_Analysis_FirstPhaseFailure
import Definitions.Def_CountingMatroid_Analysis_ObservePhaseWork
import Definitions.Def_CountingMatroid_Analysis_PhaseChainWork
import Definitions.Def_CountingMatroid_Analysis_PhaseMeanCertificate
import Definitions.Def_CountingMatroid_Analysis_PhaseObservationExperiment
import Definitions.Def_CountingMatroid_Analysis_PhaseResourcePrimitives
import Definitions.Def_CountingMatroid_Analysis_RationalHeight
import Definitions.Def_CountingMatroid_Analysis_RelativeObservationBounds
import Definitions.Def_CountingMatroid_Analysis_ScheduleConfidence
import Definitions.Def_CountingMatroid_Analysis_ScheduleOpeningCost
import Definitions.Def_CountingMatroid_Analysis_ScheduleThermalSetupCost
import Definitions.Def_CountingMatroid_Analysis_StationaryMeanIdentities
import Definitions.Def_CountingMatroid_Analysis_StationaryMeanLowerBound
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
import Mathlib.Algebra.Order.Ring.Pow
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Combinatorics.Matroid.Rank.ENat
import Mathlib.Data.BitVec
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.Card
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
namespace CountingMatroid.Meta
end CountingMatroid.Meta
namespace Arlib
end Arlib
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
namespace CountingMatroid.Interface
end CountingMatroid.Interface
namespace CountingMatroid.Analysis.TransversalRankBridge
end CountingMatroid.Analysis.TransversalRankBridge
namespace CountingMatroid.Analysis.GreedyRankCorrect
end CountingMatroid.Analysis.GreedyRankCorrect
set_option autoImplicit false

namespace CountingMatroid.Analysis.StationaryMeanLowerBound
end CountingMatroid.Analysis.StationaryMeanLowerBound
open CountingMatroid CountingMatroid.Analysis CountingMatroid.Analysis.StationaryMeanLowerBound

open CountingMatroid.Model CountingMatroid.Program CountingMatroid.Model.Operations
open CountingMatroid.Analysis.StationaryMeanIdentities
open CountingMatroid.Analysis.PhaseObservationExperiment

/-- INTERNAL: Partition the operational normalizer into its transversal
and off-diagonal class masses. Rejected and diagonal states have zero weight.
TEXLINE: main.tex:721-735 -/
theorem solution {n : ℕ} (r : ℕ)
    (o₁ o₂ : IndependenceOracle n) (q : ℚ) (w : Multipliers n)
    (hq : 0 < q) (hw : ∀ index, 0 < w index) :
    normalizer r o₁ o₂ q w = TransversalPartition.partitionSum r o₁ o₂ q +
      ∑ index : DefectIndex n, w index * FirstPhaseFailure.defectPartition r o₁ o₂ q index := by
  classical
  obtain ⟨hZ, ht, _, hd⟩ := stationary_mean_identities r o₁ o₂ q 1 w hq hw
  have hpartition (state : PairedSet n) :
      stateWeight r o₁ o₂ q w state =
        (if (classifyState state).val = .transversal then stateWeight r o₁ o₂ q w state else 0) +
        ∑ index : DefectIndex n,
          if (classifyState state).val = .defect index.emptyPair index.fullPair
          then stateWeight r o₁ o₂ q w state else 0 := by
    cases hk : (classifyState state).val with
    | invalid => simp [stateWeight, hk, weightOfKind]
    | transversal => simp
    | defect i k =>
      by_cases hik : i ≠ k
      · let index : DefectIndex n := ⟨i, k, hik⟩
        have hsum : (∑ a : DefectIndex n,
            if StateKind.defect i k = .defect a.emptyPair a.fullPair
            then stateWeight r o₁ o₂ q w state else 0) = stateWeight r o₁ o₂ q w state := by
          rw [Finset.sum_eq_single index]
          · simp [index]
          · intro a _ ha
            apply if_neg
            intro he
            have hpair := StateKind.defect.inj he
            apply ha
            cases a
            simp_all [index]
          · simp
        have hneq : StateKind.defect i k ≠ StateKind.transversal := by
          intro he
          cases he
        rw [if_neg hneq, zero_add]
        exact hsum.symm
      · have hzero : stateWeight r o₁ o₂ q w state = 0 := by
          simp [stateWeight, hk, weightOfKind, hik]
        simp [hzero]
  have hmass := congrArg (fun x : ℚ => x * normalizer r o₁ o₂ q w) ht
  have hdef (index : DefectIndex n) :=
    congrArg (fun x : ℚ => x * normalizer r o₁ o₂ q w) (hd index)
  simp only [typeMean, div_mul_cancel₀ _ hZ.ne'] at hmass hdef
  calc
    normalizer r o₁ o₂ q w = ∑ state : PairedSet n,
        ((if (classifyState state).val = .transversal then stateWeight r o₁ o₂ q w state else 0) +
          ∑ index : DefectIndex n,
            if (classifyState state).val = .defect index.emptyPair index.fullPair
            then stateWeight r o₁ o₂ q w state else 0) :=
      Finset.sum_congr rfl (fun state _ => hpartition state)
    _ = _ := by
      rw [Finset.sum_add_distrib, hmass, Finset.sum_comm]
      simp_rw [hdef]
