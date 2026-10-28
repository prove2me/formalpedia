-- Prove2me | solution 1 for CountingMatroid.Analysis.EmbeddedFlow.embedded_current_energy
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-24T14:29:46.768676+00:00
-- url     : https://prove2.me/submissions/06b6f850-efde-444e-be1e-34112770b4f9

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
import Definitions.Def_CountingMatroid_Analysis_EmbeddedFlow
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
Embed a finite signed flow into a larger state space. Injectivity preserves
its divergence, support, and energy, including zero conductances.
-/

namespace CountingMatroid.Analysis.EmbeddedFlow

open CountingMatroid.Analysis.ExchangeFlowEnergy



/-- INTERNAL: Injectivity recovers the original current on embedded vertices.
TEXLINE: main.tex:670-683 -/
theorem embedded_current_apply {α β : Type*} [Fintype α] [DecidableEq β]
    (v : α → β) (hv : Function.Injective v) (J : α → α → ℝ) (x y : α) :
    embeddedCurrent v J (v x) (v y) = J x y := by
  classical
  simp [embeddedCurrent, hv.eq_iff, ite_and]

/-- INTERNAL: An extended current vanishes if either endpoint is outside
its embedded vertex set.
TEXLINE: main.tex:670-683 -/
theorem embedded_current_off_image {α β : Type*} [Fintype α] [DecidableEq β]
    (v : α → β) (J : α → α → ℝ) (s t : β)
    (hoff : (∀ x, v x ≠ s) ∨ (∀ y, v y ≠ t)) : embeddedCurrent v J s t = 0 := by
  rcases hoff with hs | ht
  · simp [embeddedCurrent, hs]
  · simp [embeddedCurrent, ht]





/-- INTERNAL: Reindex a function supported on an injective finite image.
TEXLINE: main.tex:670-683 -/
private theorem sum_supported_image {α β : Type*} [Fintype α] [Fintype β]
    [DecidableEq β] (v : α → β) (hv : Function.Injective v) (f : β → ℝ)
    (hoff : ∀ s, (∀ x, v x ≠ s) → f s = 0) :
    (∑ s, f s) = ∑ x, f (v x) := by
  classical
  have hsum : (∑ s ∈ Finset.univ.image v, f s) = ∑ s, f s := by
    apply Finset.sum_subset (Finset.subset_univ _)
    intro s _ hs
    apply hoff s
    intro x hx
    exact hs (Finset.mem_image.mpr ⟨x, Finset.mem_univ x, hx⟩)
  rw [← hsum, Finset.sum_image (fun x _ y _ h => hv h)]





end CountingMatroid.Analysis.EmbeddedFlow

end
set_option autoImplicit false

/-!
Embed a finite signed flow into a larger state space. Injectivity preserves
its divergence, support, and energy, including zero conductances.
-/

namespace CountingMatroid.Analysis.EmbeddedFlow
end CountingMatroid.Analysis.EmbeddedFlow
open CountingMatroid CountingMatroid.Analysis CountingMatroid.Analysis.EmbeddedFlow

open CountingMatroid.Analysis.ExchangeFlowEnergy

/-- INTERNAL: Extending a current preserves its unoriented energy when
conductances agree on the embedded vertices.
TEXLINE: main.tex:670-683 -/
theorem solution {α β : Type*} [Fintype α] [Fintype β]
    [DecidableEq β] (v : α → β) (hv : Function.Injective v)
    (κ : β → β → ℝ) (J : α → α → ℝ) :
    flowEnergy κ (embeddedCurrent v J) =
      flowEnergy (fun x y => κ (v x) (v y)) J := by
  classical
  unfold flowEnergy
  congr 1
  rw [sum_supported_image v hv
    (fun s => ∑ t, (embeddedCurrent v J s t) ^ 2 / κ s t) (by
      intro s hs
      simp only [embedded_current_off_image v J s _ (Or.inl hs),
        zero_pow (by decide : 2 ≠ 0), zero_div, Finset.sum_const_zero])]
  apply Finset.sum_congr rfl
  intro x _
  rw [sum_supported_image v hv
    (fun t => (embeddedCurrent v J (v x) t) ^ 2 / κ (v x) t) (by
      intro t ht
      rw [embedded_current_off_image v J (v x) t (Or.inr ht)]
      simp)]
  simp only [embedded_current_apply v hv J]
