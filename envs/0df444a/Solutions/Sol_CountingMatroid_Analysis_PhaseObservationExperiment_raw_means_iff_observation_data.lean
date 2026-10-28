-- Prove2me | solution 1 for CountingMatroid.Analysis.PhaseObservationExperiment.raw_means_iff_observation_data
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-24T14:16:46.418773+00:00
-- url     : https://prove2.me/submissions/37c5c6b1-07e1-4bc1-ad20-bb947ca9fb6a

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
section


set_option autoImplicit false

namespace CountingMatroid.Analysis.PhaseObservationExperiment

open CountingMatroid.Model CountingMatroid.Program
open CountingMatroid.Analysis.StationaryMeanIdentities
open CountingMatroid.Analysis.RelativeObservationBounds













/-- INTERNAL: Evaluate the observation experiment by its actual restart and
observation witnesses, without replacing their tape or starting state.
TEXLINE: main.tex:1163-1187 -/
theorem observation_data_iff {n : ℕ} (r : ℕ) (o₁ o₂ : IndependenceOracle n)
    (tape : ℕ → Bool) (s : AnnealingSchedule) (j : ℕ)
    (current : AnnealingCursor n) (observed : ObservationCursor n) :
    phaseObservationData r o₁ o₂ tape s j = some (current, observed) ↔
      BoundedRunPhaseHistory.phaseHistory r o₁ o₂ tape s j = some current ∧
      ∃ start, (restartPhase r o₁ o₂ tape s current.tables j current.bitCursor).val =
        some start ∧ (observePhase r o₁ o₂ tape s (s.ρ ^ j)
          current.currentWeights start).val = some observed := by
  simp only [phaseObservationData, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
    Option.some.injEq, Prod.mk.injEq]
  constructor
  · rintro ⟨current', hh, start, hs, observed', ho, hc, hob⟩
    subst current'
    subst observed'
    exact ⟨hh, start, hs, ho⟩
  · rintro ⟨hh, start, hs, ho⟩
    exact ⟨current, hh, start, hs, observed, ho, rfl, rfl⟩







end CountingMatroid.Analysis.PhaseObservationExperiment

end
set_option autoImplicit false

namespace CountingMatroid.Analysis.PhaseObservationExperiment
end CountingMatroid.Analysis.PhaseObservationExperiment
open CountingMatroid CountingMatroid.Analysis CountingMatroid.Analysis.PhaseObservationExperiment

open CountingMatroid.Model CountingMatroid.Program
open CountingMatroid.Analysis.StationaryMeanIdentities
open CountingMatroid.Analysis.RelativeObservationBounds

/-- INTERNAL: Relative accuracy of the finite family of concrete empirical
observables is exactly the raw phase boundary, once the operational data are
retained. Diagonal pair indices repeat an existing condition.
TEXLINE: main.tex:1241-1266 -/
theorem solution {n : ℕ} (r : ℕ)
    (o₁ o₂ : IndependenceOracle n) (tape : ℕ → Bool) (s : AnnealingSchedule) (j : ℕ) :
    PhaseMeanCertificate.RawPhaseMeans r o₁ o₂ tape s j ↔
      ∃ current observed,
        phaseObservationData r o₁ o₂ tape s j = some (current, observed) ∧
        FirstPhaseFailure.GoodStoredMultipliers r o₁ o₂ s j current ∧
        0 < s.observations ∧ ∀ index : Observable n,
          RelativeEstimate s.η (observableMean r o₁ o₂ s j current index)
            (empiricalMean s observed index) := by
  constructor
  · rintro ⟨current, start, observed, hh, hg, hs, ho, hN, hz, hu, hd⟩
    refine ⟨current, observed, (observation_data_iff _ _ _ _ _ _ _ _).mpr
      ⟨hh, start, hs, ho⟩, hg, hN, ?_⟩
    intro index
    cases index with
    | inl b => cases b <;> assumption
    | inr pair =>
      rcases pair with ⟨i, k⟩
      by_cases hik : i = k
      · simpa only [observableMean, empiricalMean, if_pos hik] using hz
      · simpa only [observableMean, empiricalMean, if_neg hik] using hd ⟨i, k, hik⟩
  · rintro ⟨current, observed, hdata, hg, hN, hall⟩
    obtain ⟨hh, start, hs, ho⟩ := (observation_data_iff _ _ _ _ _ _ _ _).mp hdata
    refine ⟨current, start, observed, hh, hg, hs, ho, hN,
      hall (.inl false), hall (.inl true), ?_⟩
    intro index
    simpa only [observableMean, empiricalMean, if_neg index.distinct] using
      hall (.inr (index.emptyPair, index.fullPair))
