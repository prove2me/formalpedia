-- Prove2me | solution 1 for CountingMatroid.Analysis.ExchangeProposalGeometry.exchange_sum_partition
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-24T14:27:14.794896+00:00
-- url     : https://prove2.me/submissions/f4132d37-1955-420f-943e-6afa8110d8f8

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
import Definitions.Def_CountingMatroid_Analysis_BoundedRunPhaseWork
import Definitions.Def_CountingMatroid_Analysis_DefectPartitionPositive
import Definitions.Def_CountingMatroid_Analysis_EstimateMedianResource
import Definitions.Def_CountingMatroid_Analysis_FinishPhaseWork
import Definitions.Def_CountingMatroid_Analysis_FirstPhaseFailure
import Definitions.Def_CountingMatroid_Analysis_IdealExchangeChain
import Definitions.Def_CountingMatroid_Analysis_ObservePhaseWork
import Definitions.Def_CountingMatroid_Analysis_PhaseChainWork
import Definitions.Def_CountingMatroid_Analysis_PhaseResourcePrimitives
import Definitions.Def_CountingMatroid_Analysis_RationalHeight
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
import Mathlib.Algebra.QuadraticDiscriminant
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
import Theorems.Thm_CountingMatroid_Analysis_ExchangeProposalGeometry_exchange_state_erase_insert
import Theorems.Thm_CountingMatroid_Analysis_ExchangeProposalGeometry_exchange_state_same_occupancy

namespace CountingMatroid.Analysis.ExchangeProposalGeometry
end CountingMatroid.Analysis.ExchangeProposalGeometry
namespace Arlib
end Arlib
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

namespace CountingMatroid.Analysis.ExchangeProposalGeometry
end CountingMatroid.Analysis.ExchangeProposalGeometry
open CountingMatroid CountingMatroid.Analysis CountingMatroid.Analysis.ExchangeProposalGeometry

open CountingMatroid.Model CountingMatroid.Analysis.IdealExchangeChain

/-- INTERNAL: Split the uniform two-label exchange average into its two
holding blocks and twice the occupied/unoccupied exchange block.
TEXLINE: main.tex:746-751 -/
theorem solution {n : ℕ} (state : PairedSet n)
    (F : PairedSet n → ℝ) :
    (∑ a : PairedGround n, ∑ b : PairedGround n, F (exchangeState a b state)) =
      ((state.card : ℝ) ^ 2 + (stateᶜ.card : ℝ) ^ 2) * F state +
        2 * ∑ a ∈ state, ∑ b ∈ stateᶜ, F (insert b (state.erase a)) := by
  classical
  have hin (a : PairedGround n) (ha : a ∈ state) :
      (∑ b : PairedGround n, F (exchangeState a b state)) =
        (state.card : ℝ) * F state +
          ∑ b ∈ stateᶜ, F (insert b (state.erase a)) := by
    rw [← Finset.sum_add_sum_compl state]
    congr 1
    · rw [Finset.sum_congr rfl (fun b hb =>
        congrArg F (exchange_state_same_occupancy state a b (by simp [ha, hb])))]
      simp
    · apply Finset.sum_congr rfl
      intro b hb
      rw [exchange_state_erase_insert state a b ha (Finset.mem_compl.mp hb)]
  have hout (a : PairedGround n) (ha : a ∈ stateᶜ) :
      (∑ b : PairedGround n, F (exchangeState a b state)) =
        (∑ b ∈ state, F (insert a (state.erase b))) +
          (stateᶜ.card : ℝ) * F state := by
    rw [← Finset.sum_add_sum_compl state]
    congr 1
    · apply Finset.sum_congr rfl
      intro b hb
      rw [exchangeState, Equiv.swap_comm a b]
      change F (exchangeState b a state) = _
      rw [exchange_state_erase_insert state b a hb (Finset.mem_compl.mp ha)]
    · rw [Finset.sum_congr rfl (fun b hb =>
        congrArg F (exchange_state_same_occupancy state a b
          (by simp [Finset.mem_compl.mp ha, Finset.mem_compl.mp hb])))]
      simp
  rw [← Finset.sum_add_sum_compl state,
    Finset.sum_congr rfl hin, Finset.sum_congr rfl hout,
    Finset.sum_add_distrib, Finset.sum_add_distrib]
  have hcross : (∑ a ∈ stateᶜ, ∑ b ∈ state, F (insert a (state.erase b))) =
      ∑ b ∈ state, ∑ a ∈ stateᶜ, F (insert a (state.erase b)) := Finset.sum_comm
  rw [hcross]
  simp only [Finset.sum_const, nsmul_eq_mul]
  ring
