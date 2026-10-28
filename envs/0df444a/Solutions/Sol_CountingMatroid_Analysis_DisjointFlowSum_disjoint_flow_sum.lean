-- Prove2me | solution 1 for CountingMatroid.Analysis.DisjointFlowSum.disjoint_flow_sum
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-24T14:27:30.170956+00:00
-- url     : https://prove2.me/submissions/1f8d1ed1-8efe-46d4-8426-8dd9853c16a6

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
import Definitions.Def_CountingMatroid_Analysis_BoundedRunPhase
import Definitions.Def_CountingMatroid_Analysis_BoundedRunPhaseHistory
import Definitions.Def_CountingMatroid_Analysis_BoundedRunPhaseWork
import Definitions.Def_CountingMatroid_Analysis_DefectPartitionPositive
import Definitions.Def_CountingMatroid_Analysis_DisjointFlowSum
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
Summation of signed finite flows with disjoint used edges. Divergences add,
and edge disjointness makes the energy additive even at zero conductances.
-/

namespace CountingMatroid.Analysis.DisjointFlowSum

open CountingMatroid.Analysis.ExchangeFlowEnergy



/-- INTERNAL: Divergence commutes with a finite sum of currents.
TEXLINE: main.tex:684-709 -/
theorem sum_current_divergence {ι α : Type*} [Fintype α]
    (J : ι → α → α → ℝ) (leaves : List ι) (x : α) :
    divergence (sumCurrent J leaves) x =
      (leaves.map (fun i => divergence (J i) x)).sum := by
  induction leaves with
  | nil => simp [divergence, sumCurrent]
  | cons i rest ih =>
    simp only [divergence, sumCurrent, Finset.sum_add_distrib] at ih ⊢
    simp only [List.map_cons, List.sum_cons]
    rw [ih]

/-- INTERNAL: Multiplication by a current disjoint from every member
also annihilates their finite sum.
TEXLINE: main.tex:681-683 -/
private theorem mul_sum_current_zero {ι α : Type*} (J : ι → α → α → ℝ)
    (leaves : List ι) (a : ℝ) (x y : α)
    (hzero : ∀ i ∈ leaves, a * J i x y = 0) : a * sumCurrent J leaves x y = 0 := by
  induction leaves with
  | nil => simp [sumCurrent]
  | cons i rest ih =>
    rw [sumCurrent, mul_add, hzero i List.mem_cons_self,
      ih (fun j hj => hzero j (List.mem_cons_of_mem i hj)), zero_add]

/-- INTERNAL: Disjoint currents have additive unoriented energy.
TEXLINE: main.tex:681-683 -/
theorem disjoint_current_energy_add {α : Type*} [Fintype α]
    (κ J K : α → α → ℝ) (hdisjoint : ∀ x y, J x y * K x y = 0) :
    flowEnergy κ (fun x y => J x y + K x y) = flowEnergy κ J + flowEnergy κ K := by
  have hsq (x y : α) : (J x y + K x y) ^ 2 = (J x y) ^ 2 + (K x y) ^ 2 := by
    nlinarith [hdisjoint x y]
  simp only [flowEnergy, hsq, add_div, Finset.sum_add_distrib, mul_add]

/-- PAPER: main.tex:681-683
A sum of edge-disjoint leaf currents has exactly the sum of their energies. -/
theorem sum_current_energy {ι α : Type*} [Fintype α]
    (κ : α → α → ℝ) (J : ι → α → α → ℝ) (leaves : List ι)
    (hdisjoint : leaves.Pairwise (fun i j => ∀ x y, J i x y * J j x y = 0)) :
    flowEnergy κ (sumCurrent J leaves) =
      (leaves.map (fun i => flowEnergy κ (J i))).sum := by
  induction leaves with
  | nil => simp [flowEnergy, sumCurrent]
  | cons i rest ih =>
    obtain ⟨hhead, htail⟩ := List.pairwise_cons.mp hdisjoint
    have hc : ∀ x y, J i x y * sumCurrent J rest x y = 0 := by
      intro x y
      exact mul_sum_current_zero J rest (J i x y) x y (fun j hj => hhead j hj x y)
    change flowEnergy κ (fun x y => J i x y + sumCurrent J rest x y) = _
    rw [disjoint_current_energy_add κ (J i) (sumCurrent J rest) hc, ih htail]
    rfl



end CountingMatroid.Analysis.DisjointFlowSum

end
set_option autoImplicit false

/-!
Summation of signed finite flows with disjoint used edges. Divergences add,
and edge disjointness makes the energy additive even at zero conductances.
-/

namespace CountingMatroid.Analysis.DisjointFlowSum
end CountingMatroid.Analysis.DisjointFlowSum
open CountingMatroid CountingMatroid.Analysis CountingMatroid.Analysis.DisjointFlowSum

open CountingMatroid.Analysis.ExchangeFlowEnergy

/-- INTERNAL: Summing supported antisymmetric currents produces a flow
certificate with summed divergence and, for disjoint edges, summed energy.
TEXLINE: main.tex:681-709 -/
theorem solution {ι α : Type*} [Fintype α]
    (κ : α → α → ℝ) (J : ι → α → α → ℝ) (d : ι → α → ℝ) (leaves : List ι)
    (hanti : ∀ i ∈ leaves, ∀ x y, J i x y = -J i y x)
    (hsupport : ∀ i ∈ leaves, ∀ x y, κ x y = 0 → J i x y = 0)
    (hdiv : ∀ i ∈ leaves, ∀ x, divergence (J i) x = d i x)
    (hdisjoint : leaves.Pairwise (fun i j => ∀ x y, J i x y * J j x y = 0)) :
    ∃ flow : FlowCertificate κ (fun x => (leaves.map (fun i => d i x)).sum),
      flow.current = sumCurrent J leaves ∧
      flowEnergy κ flow.current = (leaves.map (fun i => flowEnergy κ (J i))).sum := by
  have ha : ∀ x y, sumCurrent J leaves x y = -sumCurrent J leaves y x := by
    intro x y
    clear hsupport hdiv hdisjoint
    induction leaves with
    | nil => simp [sumCurrent]
    | cons i rest ih =>
      rw [sumCurrent, sumCurrent, hanti i List.mem_cons_self,
        ih (fun j hj => hanti j (List.mem_cons_of_mem i hj))]
      ring
  have hs : ∀ x y, κ x y = 0 → sumCurrent J leaves x y = 0 := by
    intro x y hz
    clear ha hanti hdiv hdisjoint
    induction leaves with
    | nil => rfl
    | cons i rest ih =>
      rw [sumCurrent, hsupport i List.mem_cons_self x y hz,
        ih (fun j hj => hsupport j (List.mem_cons_of_mem i hj)), zero_add]
  have hd : ∀ x, divergence (sumCurrent J leaves) x =
      (leaves.map (fun i => d i x)).sum := by
    intro x
    rw [sum_current_divergence]
    congr 1
    apply List.map_congr_left
    intro i hi
    exact hdiv i hi x
  exact ⟨⟨sumCurrent J leaves, ha, hs, hd⟩, rfl,
    sum_current_energy κ J leaves hdisjoint⟩
