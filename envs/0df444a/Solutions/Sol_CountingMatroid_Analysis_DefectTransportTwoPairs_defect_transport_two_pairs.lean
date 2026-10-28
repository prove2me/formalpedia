-- Prove2me | solution 1 for CountingMatroid.Analysis.DefectTransportTwoPairs.defect_transport_two_pairs
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-24T14:53:49.12183+00:00
-- url     : https://prove2.me/submissions/a25eec29-a6ce-47e8-8b55-e16750f3e380

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
import Theorems.Thm_CountingMatroid_Analysis_DefectPartitionPositive_defect_partition_pos

namespace CountingMatroid.Analysis.DefectTransportTwoPairs
end CountingMatroid.Analysis.DefectTransportTwoPairs
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

namespace CountingMatroid.Analysis.IdealExchangeChain

open CountingMatroid.Model CountingMatroid.Program
open CountingMatroid.Analysis.StationaryMeanIdentities
open Arlib.Probability Arlib.MarkovChains























/-- INTERNAL: Identify the operational rational type mean with expectation
under the concrete ideal stationary law, for correlated-observation analysis.
TEXLINE: main.tex:1241-1247 -/
theorem operational_type_mean {n : ℕ} (r : ℕ) (o₁ o₂ : IndependenceOracle n)
    (q : ℚ) (w : Multipliers n) (hq : 0 < q) (hw : ∀ index, 0 < w index)
    (kind : StateKind n) :
    Ex (operationalLaw r o₁ o₂ q w hq hw) (typeIndicator kind) =
      (typeMean r o₁ o₂ q w kind : ℝ) := by
  classical
  unfold Ex typeMean
  push_cast
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro state _
  by_cases hk : (classifyState state).val = kind
  · simp [operationalLaw, typeIndicator, hk]
  · simp [operationalLaw, typeIndicator, hk]





end CountingMatroid.Analysis.IdealExchangeChain

end

section


set_option autoImplicit false

/-!
Weighted moments for the operational classifier, and the first inequality
in the paper's observable Poincare proof. These identities do not assert
the quantitative transversal variance or defect transport estimates.
-/

namespace CountingMatroid.Analysis.ObservableVarianceDecomposition

open CountingMatroid.Model CountingMatroid.Program
open CountingMatroid.Analysis.IdealExchangeChain
open CountingMatroid.Analysis.ObservableProjection
open Arlib.Probability Arlib.Probability.FinDist













/-- INTERNAL: The classifier-fiber mass equals the operational type mean.
TEXLINE: main.tex:721-744 -/
theorem operational_class_mass {n : ℕ} (r : ℕ)
    (o₁ o₂ : IndependenceOracle n) (q : ℚ) (w : Multipliers n)
    (hq : 0 < q) (hw : ∀ index, 0 < w index) (kind : StateKind n) :
    classMass (operationalLaw r o₁ o₂ q w hq hw) kind =
      (StationaryMeanIdentities.typeMean r o₁ o₂ q w kind : ℝ) := by
  classical
  rw [← operational_type_mean r o₁ o₂ q w hq hw kind]
  simp [classMass, Ex, typeIndicator]









end CountingMatroid.Analysis.ObservableVarianceDecomposition

/-! ### Run record
Newest first. History, not instruction — what this file claims is above.

* current · proved · classifier mass identities, nonnegative transversal variance, and the projection's squared-deviation decomposition, including rejected and diagonal zero-mass classes.
-/

end

section


set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000

/-!
The no-ordinary-slot case of the paper's transport construction. With two
original pairs, an ordered defect fiber and a prescribed transversal event
are singleton states joined by one exchange. The certified unit current
has energy bounded by the sum of the two reciprocal conditional masses.
-/

namespace CountingMatroid.Analysis.DefectTransportTwoPairs

open CountingMatroid.Model CountingMatroid.Program
open CountingMatroid.Analysis.IdealExchangeChain
open CountingMatroid.Analysis.ObservableVarianceDecomposition
open CountingMatroid.Analysis.TransversalEventMean
open CountingMatroid.Analysis.ExchangeFlowEnergy

/-- INTERNAL: A two-pair ordered defect fiber consists of the full pair alone.
TEXLINE: main.tex:875-892 -/
private theorem two_pair_defect_shape : ∀ i k : Fin 2, i ≠ k →
    ∀ state : PairedSet 2,
    (classifyState state).val = .defect i k ↔ state = {(k, false), (k, true)} := by
  decide

/-- INTERNAL: Prescribing both transversal choices on two pairs leaves one state.
TEXLINE: main.tex:868-873 -/
private theorem two_pair_event_shape : ∀ i k : Fin 2, i ≠ k → ∀ a b : Bool,
    pairEvent i k a b = {({(i, !a), (k, !b)} : PairedSet 2)} := by
  decide

/-- INTERNAL: The two orientations of the unique occupied/unoccupied exchange
have total proposal probability one eighth on four labels.
TEXLINE: main.tex:746-751 -/
private theorem two_pair_exchange_probability (hn : 0 < 2)
    (i k : Fin 2) (hik : i ≠ k) (a b : Bool) :
    exchangeProposal 2 hn {(k, false), (k, true)} {(i, !a), (k, !b)} =
      (1 / 8 : ℝ) := by
  fin_cases i <;> fin_cases k <;> cases a <;> cases b <;>
    simp_all [exchangeProposal, exchangeState, Fin.sum_univ_two,
      Finset.image_insert, Finset.image_singleton,
      Equiv.swap_apply_def, PairedGround, Fintype.sum_prod_type] <;>
    norm_num [Finset.ext_iff, Fin.forall_fin_two, Bool.forall_bool]

/-- INTERNAL: A unit current along one positive symmetric edge realizes the
point-source minus point-sink demand, with energy the reciprocal conductance.
TEXLINE: main.tex:670-688 -/
private theorem unit_edge_flow {α : Type*} [Fintype α] [DecidableEq α]
    (κ : α → α → ℝ) (x y : α) (hxy : x ≠ y)
    (hκ : 0 < κ x y) (hsym : κ x y = κ y x) :
    ∃ flow : FlowCertificate κ (fun z => (if z = x then 1 else 0) -
        (if z = y then 1 else 0)),
      flowEnergy κ flow.current = 1 / κ x y := by
  classical
  let J := fun s t : α =>
    (if s = x ∧ t = y then 1 else 0 : ℝ) - (if s = y ∧ t = x then 1 else 0)
  have hanti : ∀ s t, J s t = -J t s := by
    intro s t
    simp only [J, and_comm]
    ring
  have hsupport : ∀ s t, κ s t = 0 → J s t = 0 := by
    intro s t hz
    by_cases hforward : s = x ∧ t = y
    · obtain ⟨rfl, rfl⟩ := hforward
      exact False.elim (hκ.ne' hz)
    by_cases hbackward : s = y ∧ t = x
    · obtain ⟨rfl, rfl⟩ := hbackward
      exact False.elim (hκ.ne' (hsym.trans hz))
    simp [J, hforward, hbackward]
  have hdiv : ∀ s, divergence J s =
      (if s = x then 1 else 0) - (if s = y then 1 else 0) := by
    intro s
    simp only [divergence, J, Finset.sum_sub_distrib, ite_and]
    simp
  refine ⟨⟨J, hanti, hsupport, hdiv⟩, ?_⟩
  change flowEnergy κ J = _
  have hsq (s t : α) : (J s t) ^ 2 / κ s t =
      (if s = x ∧ t = y then 1 / κ x y else 0) +
      (if s = y ∧ t = x then 1 / κ y x else 0) := by
    by_cases hforward : s = x ∧ t = y
    · obtain ⟨rfl, rfl⟩ := hforward
      simp [J, hxy, hxy.symm]
    by_cases hbackward : s = y ∧ t = x
    · obtain ⟨rfl, rfl⟩ := hbackward
      simp [J, hxy, hxy.symm]
    simp [J, hforward, hbackward]
  simp only [flowEnergy, hsq, Finset.sum_add_distrib, ite_and]
  simp only [Finset.sum_ite_irrel, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  rw [← hsym]
  simp
  ring



end CountingMatroid.Analysis.DefectTransportTwoPairs

end
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000

/-!
The no-ordinary-slot case of the paper's transport construction. With two
original pairs, an ordered defect fiber and a prescribed transversal event
are singleton states joined by one exchange. The certified unit current
has energy bounded by the sum of the two reciprocal conditional masses.
-/

namespace CountingMatroid.Analysis.DefectTransportTwoPairs
end CountingMatroid.Analysis.DefectTransportTwoPairs
open CountingMatroid CountingMatroid.Analysis CountingMatroid.Analysis.DefectTransportTwoPairs

open CountingMatroid.Model CountingMatroid.Program
open CountingMatroid.Analysis.IdealExchangeChain
open CountingMatroid.Analysis.ObservableVarianceDecomposition
open CountingMatroid.Analysis.TransversalEventMean
open CountingMatroid.Analysis.ExchangeFlowEnergy

/-- INTERNAL: The defect-to-prescribed-event transport bound when no ordinary
slots remain; this uses the actual operational classifier and exchange proposal.
TEXLINE: main.tex:670-709,875-898 -/
theorem solution (r : ℕ) (o₁ o₂ : IndependenceOracle 2)
    (q : ℚ) (w : Multipliers 2) (hn : 0 < 2) (hq : 0 < q)
    (hw : ∀ index, 0 < w index) (i k : Fin 2) (hik : i ≠ k) (a b : Bool)
    (hA : 0 < eventMass (operationalLaw r o₁ o₂ q w hq hw) (pairEvent i k a b)) :
    let π := operationalLaw r o₁ o₂ q w hq hw
    let κ := fun state next : PairedSet 2 =>
      exchangeProposal 2 hn state next * min (π state) (π next)
    ∃ flow : FlowCertificate κ
        (conditionalMeanDemand π (.defect i k) (pairEvent i k a b)),
      flowEnergy κ flow.current ≤ 8 *
        (1 / classMass π (.defect i k) + 1 / eventMass π (pairEvent i k a b)) := by
  classical
  intro π κ
  let x : PairedSet 2 := {(k, false), (k, true)}
  let y : PairedSet 2 := {(i, !a), (k, !b)}
  have hshape : ∀ state, (classifyState state).val = .defect i k ↔ state = x :=
    two_pair_defect_shape i k hik
  have hevent : pairEvent i k a b = {y} := two_pair_event_shape i k hik a b
  have hmass : classMass π (.defect i k) = π x := by
    simp only [classMass, hshape]
    simp
  have hemass : eventMass π (pairEvent i k a b) = π y := by
    rw [hevent]
    simp [eventMass]
  have hx : 0 < π x := by
    obtain ⟨hZ, _, _, hdef⟩ :=
      StationaryMeanIdentities.stationary_mean_identities r o₁ o₂ q 1 w hq hw
    rw [← hmass]
    dsimp only [π]
    rw [operational_class_mass, hdef ⟨i, k, hik⟩]
    exact_mod_cast div_pos (mul_pos (hw _)
      (DefectPartitionPositive.defect_partition_pos r o₁ o₂ q hq _)) hZ
  have hy : 0 < π y := by rwa [hemass] at hA
  have hxy : x ≠ y := by
    intro h
    have hi : (i, !a) ∈ x := by rw [h]; simp [y]
    simp [x, hik] at hi
  have hconductance : κ x y = (1 / 8 : ℝ) * min (π x) (π y) := by
    dsimp only [κ, x, y]
    rw [two_pair_exchange_probability hn i k hik a b]
  have hkpos : 0 < κ x y := by rw [hconductance]; exact mul_pos (by norm_num) (lt_min hx hy)
  have hksym : κ x y = κ y x := by
    dsimp only [κ]
    rw [exchange_proposal_symmetric, min_comm]
  have hdemand : conditionalMeanDemand π (.defect i k) (pairEvent i k a b) =
      fun z => (if z = x then 1 else 0) - (if z = y then 1 else 0) := by
    funext z
    simp only [conditionalMeanDemand, hshape, hmass, hemass, hevent,
      Finset.mem_singleton]
    by_cases hzx : z = x <;> by_cases hzy : z = y <;>
      simp_all [hx.ne', hy.ne']
  rw [hdemand]
  obtain ⟨flow, henergy⟩ := unit_edge_flow κ x y hxy hkpos hksym
  refine ⟨flow, ?_⟩
  rw [henergy, hconductance, hmass, hemass]
  have hmin : 0 < min (π x) (π y) := lt_min hx hy
  have hrecip : 1 / min (π x) (π y) ≤ 1 / π x + 1 / π y := by
    rcases le_total (π x) (π y) with h | h
    · rw [min_eq_left h]
      exact le_add_of_nonneg_right (div_nonneg (by norm_num) hy.le)
    · rw [min_eq_right h]
      exact le_add_of_nonneg_left (div_nonneg (by norm_num) hx.le)
  calc
    1 / ((1 / 8 : ℝ) * min (π x) (π y)) = 8 * (1 / min (π x) (π y)) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hrecip (by norm_num)
