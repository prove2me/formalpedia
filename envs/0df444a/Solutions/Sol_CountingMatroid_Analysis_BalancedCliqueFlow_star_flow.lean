-- Prove2me | solution 1 for CountingMatroid.Analysis.BalancedCliqueFlow.star_flow
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-24T15:26:36.374378+00:00
-- url     : https://prove2.me/submissions/e231d6ee-da15-40df-9d6b-fa5bedfc4a22

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
import Definitions.Def_CountingMatroidSupport_MarkovChains_Techniques_Dirichlet
import Definitions.Def_CountingMatroidSupport_Probability_Bilinear
import Definitions.Def_CountingMatroidSupport_Probability_FinDist
import Definitions.Def_CountingMatroidSupport_Probability_FinDistFunctional
import Definitions.Def_CountingMatroid_Analysis_AnnealingPartitionDrift
import Definitions.Def_CountingMatroid_Analysis_BalancedCliqueFlow
import Definitions.Def_CountingMatroid_Analysis_BoundedRunPhase
import Definitions.Def_CountingMatroid_Analysis_BoundedRunPhaseHistory
import Definitions.Def_CountingMatroid_Analysis_BoundedRunPhaseWork
import Definitions.Def_CountingMatroid_Analysis_DefectPartitionPositive
import Definitions.Def_CountingMatroid_Analysis_EmpiricalPhaseCertificate
import Definitions.Def_CountingMatroid_Analysis_EstimateMedianResource
import Definitions.Def_CountingMatroid_Analysis_ExchangeFlowEnergy
import Definitions.Def_CountingMatroid_Analysis_FinishPhaseEmpiricalUpdate
import Definitions.Def_CountingMatroid_Analysis_FinishPhaseWork
import Definitions.Def_CountingMatroid_Analysis_FirstPhaseFailure
import Definitions.Def_CountingMatroid_Analysis_IdealExchangeChain
import Definitions.Def_CountingMatroid_Analysis_ObservableProjection
import Definitions.Def_CountingMatroid_Analysis_ObservableVarianceDecomposition
import Definitions.Def_CountingMatroid_Analysis_ObservePhaseWork
import Definitions.Def_CountingMatroid_Analysis_PhaseChainWork
import Definitions.Def_CountingMatroid_Analysis_PhaseMeanCertificate
import Definitions.Def_CountingMatroid_Analysis_PhaseResourcePrimitives
import Definitions.Def_CountingMatroid_Analysis_RationalHeight
import Definitions.Def_CountingMatroid_Analysis_RelativeObservationBounds
import Definitions.Def_CountingMatroid_Analysis_ScheduleConfidence
import Definitions.Def_CountingMatroid_Analysis_ScheduleOpeningCost
import Definitions.Def_CountingMatroid_Analysis_ScheduleThermalSetupCost
import Definitions.Def_CountingMatroid_Analysis_StationaryMeanIdentities
import Definitions.Def_CountingMatroid_Analysis_TransversalClassPartition
import Definitions.Def_CountingMatroid_Analysis_TransversalEventMean
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
import Theorems.Thm_CountingMatroid_Analysis_BalancedCliqueFlow_star_current_divergence
import Theorems.Thm_CountingMatroid_Analysis_BalancedCliqueFlow_star_current_energy

namespace Arlib
end Arlib
namespace CountingMatroid.Analysis.TypeMassLowerBounds
end CountingMatroid.Analysis.TypeMassLowerBounds
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
section


set_option autoImplicit false

/-!
The signed star current used at a balanced leaf clique. Its divergence is
exactly the prescribed demand, and its energy is bounded by the sum of
squared demands divided by the vertex capacities at a maximizing hub.
-/

namespace CountingMatroid.Analysis.BalancedCliqueFlow

open CountingMatroid.Analysis.ExchangeFlowEnergy



/-- INTERNAL: Reversing a star edge reverses its current.
TEXLINE: main.tex:675-680 -/
theorem star_current_antisymmetric {α : Type*} [DecidableEq α]
    (g : α → ℝ) (hub x y : α) :
    starCurrent g hub x y = -starCurrent g hub y x := by
  unfold starCurrent
  ring









end CountingMatroid.Analysis.BalancedCliqueFlow

end
set_option autoImplicit false

/-!
The signed star current used at a balanced leaf clique. Its divergence is
exactly the prescribed demand, and its energy is bounded by the sum of
squared demands divided by the vertex capacities at a maximizing hub.
-/

namespace CountingMatroid.Analysis.BalancedCliqueFlow
end CountingMatroid.Analysis.BalancedCliqueFlow
open CountingMatroid CountingMatroid.Analysis CountingMatroid.Analysis.BalancedCliqueFlow

open CountingMatroid.Analysis.ExchangeFlowEnergy

/-- PAPER: main.tex:675-683
Positive hub-edge conductances bounded below by the vertex capacities
realize every balanced demand, with energy at most its weighted cost. -/
theorem solution {α : Type*} [Fintype α] [DecidableEq α]
    (κ : α → α → ℝ) (c g : α → ℝ) (hub : α)
    (hbalance : ∑ x, g x = 0)
    (hsym : ∀ x, κ hub x = κ x hub)
    (hc : ∀ x, 0 < c x)
    (hbound : ∀ x, x ≠ hub → c x ≤ κ x hub) :
    ∃ flow : FlowCertificate κ g,
      flow.current = starCurrent g hub ∧
      flowEnergy κ flow.current ≤ ∑ x, (g x) ^ 2 / c x := by
  classical
  have hsupport : ∀ x y, κ x y = 0 → starCurrent g hub x y = 0 := by
    intro x y hz
    by_cases hx : x = hub <;> by_cases hy : y = hub
    · subst x; subst y; simp [starCurrent]
    · subst x
      have hp := (hc y).trans_le (hbound y hy)
      rw [← hsym y, hz] at hp
      exact False.elim (lt_irrefl _ hp)
    · subst y
      have hp := (hc x).trans_le (hbound x hx)
      rw [hz] at hp
      exact False.elim (lt_irrefl _ hp)
    · simp [starCurrent, hx, hy]
  refine ⟨⟨starCurrent g hub, star_current_antisymmetric g hub,
    hsupport, star_current_divergence g hub hbalance⟩, rfl, ?_⟩
  change flowEnergy κ (starCurrent g hub) ≤ _
  rw [star_current_energy κ g hub hsym]
  calc
    _ ≤ ∑ x ∈ Finset.univ.erase hub, (g x) ^ 2 / c x := by
      apply Finset.sum_le_sum
      intro x hx
      exact div_le_div_of_nonneg_left (sq_nonneg _) (hc x)
        (hbound x (Finset.ne_of_mem_erase hx))
    _ ≤ ∑ x, (g x) ^ 2 / c x :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.erase_subset _ _)
        (fun x _ _ => div_nonneg (sq_nonneg _) (hc x).le)
