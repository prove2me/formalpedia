-- Prove2me | solution 1 for CountingMatroid.Analysis.RestartAttemptDrawSites.restart_attempt_draw_sites
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-24T16:44:14.726443+00:00
-- url     : https://prove2.me/submissions/b7447c5a-be9d-434e-b134-1548fb1045f3

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
import Definitions.Def_CountingMatroid_Analysis_BoundedUniformAbortMass
import Definitions.Def_CountingMatroid_Analysis_BoundedUniformReplay
import Definitions.Def_CountingMatroid_Analysis_ChainDrawSiteReplay
import Definitions.Def_CountingMatroid_Analysis_ChainStepIntervalReplay
import Definitions.Def_CountingMatroid_Analysis_ConditionalDefectCoefficients
import Definitions.Def_CountingMatroid_Analysis_ConditionalDefectExtractionCoefficients
import Definitions.Def_CountingMatroid_Analysis_ConditionalDefectQuadratics
import Definitions.Def_CountingMatroid_Analysis_ConditionalTransversalSlots
import Definitions.Def_CountingMatroid_Analysis_ConditionalTransversalSplitTransport
import Definitions.Def_CountingMatroid_Analysis_ConditionalVarianceTree
import Definitions.Def_CountingMatroid_Analysis_CubicTensorContraction
import Definitions.Def_CountingMatroid_Analysis_DefectPartitionPositive
import Definitions.Def_CountingMatroid_Analysis_DefectPartitionQuadraticConstruction
import Definitions.Def_CountingMatroid_Analysis_DefectSlotConservation
import Definitions.Def_CountingMatroid_Analysis_DefectSlotSplitSignature
import Definitions.Def_CountingMatroid_Analysis_DisjointFlowSum
import Definitions.Def_CountingMatroid_Analysis_EmbeddedFlow
import Definitions.Def_CountingMatroid_Analysis_EmpiricalPhaseCertificate
import Definitions.Def_CountingMatroid_Analysis_EstimateMedianResource
import Definitions.Def_CountingMatroid_Analysis_ExchangeFlowEnergy
import Definitions.Def_CountingMatroid_Analysis_FinishPhaseEmpiricalUpdate
import Definitions.Def_CountingMatroid_Analysis_FinishPhaseWork
import Definitions.Def_CountingMatroid_Analysis_FirstPhaseFailure
import Definitions.Def_CountingMatroid_Analysis_IdealExchangeChain
import Definitions.Def_CountingMatroid_Analysis_InitialMultipliersGood
import Definitions.Def_CountingMatroid_Analysis_LeafCliqueFlow
import Definitions.Def_CountingMatroid_Analysis_LorentzianDirectionalSignature
import Definitions.Def_CountingMatroid_Analysis_ObservableProjection
import Definitions.Def_CountingMatroid_Analysis_ObservableVarianceDecomposition
import Definitions.Def_CountingMatroid_Analysis_ObservePhaseWork
import Definitions.Def_CountingMatroid_Analysis_OmittedRankWeightPolynomial
import Definitions.Def_CountingMatroid_Analysis_OmittedSlotCoefficientFormula
import Definitions.Def_CountingMatroid_Analysis_OmittedSlotQuadratic
import Definitions.Def_CountingMatroid_Analysis_OmittedTutteNormalization
import Definitions.Def_CountingMatroid_Analysis_PhaseChainWork
import Definitions.Def_CountingMatroid_Analysis_PhaseMeanCertificate
import Definitions.Def_CountingMatroid_Analysis_PhaseObservationExperiment
import Definitions.Def_CountingMatroid_Analysis_PhaseResourcePrimitives
import Definitions.Def_CountingMatroid_Analysis_QuadraticNonpositiveHyperplane
import Definitions.Def_CountingMatroid_Analysis_RankWeightQuadraticSignature
import Definitions.Def_CountingMatroid_Analysis_RankWeightSupportExchange
import Definitions.Def_CountingMatroid_Analysis_RationalHeight
import Definitions.Def_CountingMatroid_Analysis_RelativeObservationBounds
import Definitions.Def_CountingMatroid_Analysis_RestartAttemptAccounting
import Definitions.Def_CountingMatroid_Analysis_RestartDrawProbe
import Definitions.Def_CountingMatroid_Analysis_RestartDrawProbeAbort
import Definitions.Def_CountingMatroid_Analysis_RestartDrawProbeBitBound
import Definitions.Def_CountingMatroid_Analysis_RestartDrawProbeCoverage
import Definitions.Def_CountingMatroid_Analysis_RestartDrawProbeReplay
import Definitions.Def_CountingMatroid_Analysis_RestartDrawProbeScanReplay
import Definitions.Def_CountingMatroid_Analysis_RestartPhaseBitCoverage
import Definitions.Def_CountingMatroid_Analysis_RestartReturnAbortAttribution
import Definitions.Def_CountingMatroid_Analysis_RestartStageAbortAttribution
import Definitions.Def_CountingMatroid_Analysis_ScheduleConfidence
import Definitions.Def_CountingMatroid_Analysis_ScheduleDrawTrialsBridge
import Definitions.Def_CountingMatroid_Analysis_ScheduleOpeningCost
import Definitions.Def_CountingMatroid_Analysis_ScheduleThermalSetupCost
import Definitions.Def_CountingMatroid_Analysis_SlotBlockSignature
import Definitions.Def_CountingMatroid_Analysis_SlotDemandPairing
import Definitions.Def_CountingMatroid_Analysis_SlotDemandRecursion
import Definitions.Def_CountingMatroid_Analysis_SlotTransportFlow
import Definitions.Def_CountingMatroid_Analysis_SquarefreeCoordinateHessian
import Definitions.Def_CountingMatroid_Analysis_StationaryMeanIdentities
import Definitions.Def_CountingMatroid_Analysis_StoppedDrawHistory
import Definitions.Def_CountingMatroid_Analysis_ThreePairSignatureSchur
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
import Mathlib.Algebra.MvPolynomial.Degrees
import Mathlib.Algebra.MvPolynomial.PDeriv
import Mathlib.Algebra.MvPolynomial.Rename
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Algebra.Order.Floor.Defs
import Mathlib.Algebra.Order.Group.Int
import Mathlib.Algebra.Order.Ring.Pow
import Mathlib.Algebra.QuadraticDiscriminant
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.InnerProductSpace.Spectrum
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Combinatorics.Matroid.Rank.ENat
import Mathlib.Combinatorics.Matroid.Sum
import Mathlib.Data.BitVec
import Mathlib.Data.ENNReal.Inv
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Finsupp.Indicator
import Mathlib.Data.Finsupp.Multiset
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.List.Basic
import Mathlib.Data.List.Induction
import Mathlib.Data.List.Infix
import Mathlib.Data.List.Nodup
import Mathlib.Data.List.OfFn
import Mathlib.Data.List.Sort
import Mathlib.Data.Multiset.Basic
import Mathlib.Data.Multiset.Count
import Mathlib.Data.Nat.Log
import Mathlib.Data.Rat.Defs
import Mathlib.Data.Real.Basic
import Mathlib.Data.Set.Card.Arithmetic
import Mathlib.Data.Set.Finite.List
import Mathlib.LinearAlgebra.Matrix.BilinearForm
import Mathlib.LinearAlgebra.QuadraticForm.Basic
import Mathlib.LinearAlgebra.QuadraticForm.Signature
import Mathlib.Order.Interval.Set.Basic
import Mathlib.Probability.ProbabilityMassFunction.Constructions
import Mathlib.RingTheory.MvPolynomial.EulerIdentity
import Mathlib.RingTheory.MvPolynomial.Homogeneous
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
import Mathlib.Topology.Algebra.Order.Field
import Mathlib.Topology.Instances.Rat
import Mathlib.Topology.Instances.Real.Lemmas
import Theorems.Thm_CountingMatroid_Analysis_RestartAttemptDrawSites_stopped_draw_of_absolute_probe
import Theorems.Thm_CountingMatroid_Analysis_RestartDrawProbeAbort_restart_draw_probe_abort
import Theorems.Thm_CountingMatroid_Analysis_RestartDrawProbeCoverage_restart_draw_probe_coverage
import Theorems.Thm_CountingMatroid_Analysis_RestartDrawProbeReplay_restart_draw_probe_replay
import Theorems.Thm_CountingMatroid_Analysis_RestartDrawProbe_restartDrawProbe_positive
import Theorems.Thm_CountingMatroid_Analysis_RestartDrawProbe_while_observer_projection

namespace CountingMatroid.Meta
end CountingMatroid.Meta
namespace Arlib
end Arlib
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
namespace CountingMatroid.Analysis.RestartAttemptDrawSites
end CountingMatroid.Analysis.RestartAttemptDrawSites
namespace CountingMatroid.Analysis.ConditionalLeafClassifier
end CountingMatroid.Analysis.ConditionalLeafClassifier
namespace CountingMatroid.Analysis.SlotOmissionPatternCharacterization
end CountingMatroid.Analysis.SlotOmissionPatternCharacterization
namespace CountingMatroid.Analysis.TwoLabelDerivativeNilpotence
end CountingMatroid.Analysis.TwoLabelDerivativeNilpotence
namespace CountingMatroid.Analysis.MixedDirectionalRankWeightSignature
end CountingMatroid.Analysis.MixedDirectionalRankWeightSignature
namespace CountingMatroid.Analysis.RankWeightCoordinateLorentzian
end CountingMatroid.Analysis.RankWeightCoordinateLorentzian
namespace CountingMatroid.Analysis.RankWeightCoordinateSignature
end CountingMatroid.Analysis.RankWeightCoordinateSignature
namespace CountingMatroid.Analysis.RankWeightResidualSignature
end CountingMatroid.Analysis.RankWeightResidualSignature
namespace CountingMatroid.Analysis.RankWeightClosurePair
end CountingMatroid.Analysis.RankWeightClosurePair
namespace CountingMatroid.Analysis.ClosureClassQuadraticBound
end CountingMatroid.Analysis.ClosureClassQuadraticBound
namespace CountingMatroid.Analysis.SquarefreeFullDerivative
end CountingMatroid.Analysis.SquarefreeFullDerivative
namespace CountingMatroid.Analysis.BinaryRankWeightSignature
end CountingMatroid.Analysis.BinaryRankWeightSignature
namespace CountingMatroid.Analysis.CubicDirectionalSignature
end CountingMatroid.Analysis.CubicDirectionalSignature
namespace CountingMatroid.Analysis.CubicTensorRayleighContraction
end CountingMatroid.Analysis.CubicTensorRayleighContraction
namespace CountingMatroid.Analysis.NonnegativeContractionLimit
end CountingMatroid.Analysis.NonnegativeContractionLimit
namespace CountingMatroid.Analysis.QuadraticHyperplanePointwiseLimit
end CountingMatroid.Analysis.QuadraticHyperplanePointwiseLimit
namespace CountingMatroid.Analysis.ConnectedRayleighHyperplane
end CountingMatroid.Analysis.ConnectedRayleighHyperplane
namespace CountingMatroid.Analysis.ConnectedNormalizedRayleigh
end CountingMatroid.Analysis.ConnectedNormalizedRayleigh
namespace CountingMatroid.Analysis.ConnectedLaplacianKernel
end CountingMatroid.Analysis.ConnectedLaplacianKernel
namespace CountingMatroid.Analysis.RayleighFixedKernel
end CountingMatroid.Analysis.RayleighFixedKernel
namespace CountingMatroid.Analysis.QuadraticSignatureHyperplane
end CountingMatroid.Analysis.QuadraticSignatureHyperplane
namespace CountingMatroid.Analysis.CubicExchangeCut
end CountingMatroid.Analysis.CubicExchangeCut
namespace CountingMatroid.Analysis.CubicThirdDerivativeSupport
end CountingMatroid.Analysis.CubicThirdDerivativeSupport
namespace CountingMatroid.Analysis.NonnegativeDirectionalMConvexSupport
end CountingMatroid.Analysis.NonnegativeDirectionalMConvexSupport
namespace CountingMatroid.Analysis.LinearSubstitutionHessian
end CountingMatroid.Analysis.LinearSubstitutionHessian
namespace CountingMatroid.Analysis.LinearPolynomialChainRule
end CountingMatroid.Analysis.LinearPolynomialChainRule
namespace CountingMatroid.Analysis.PairedRankValue
end CountingMatroid.Analysis.PairedRankValue
namespace CountingMatroid.Analysis.SignatureOrthogonalNonpositive
end CountingMatroid.Analysis.SignatureOrthogonalNonpositive
namespace CountingMatroid.Analysis.TypeMassLowerBounds
end CountingMatroid.Analysis.TypeMassLowerBounds
namespace CountingMatroid.Analysis.ExchangeProposalGeometry
end CountingMatroid.Analysis.ExchangeProposalGeometry
namespace CountingMatroid.Analysis.SlotLeafGeometry
end CountingMatroid.Analysis.SlotLeafGeometry
namespace CountingMatroid.Analysis.LeafExchangeProposal
end CountingMatroid.Analysis.LeafExchangeProposal
namespace CountingMatroid.Analysis.BalancedCliqueEnergy
end CountingMatroid.Analysis.BalancedCliqueEnergy
namespace CountingMatroid.Analysis.OnePairObservablePoincare
end CountingMatroid.Analysis.OnePairObservablePoincare
namespace CountingMatroid.Analysis.ChainStepNoninvalid
end CountingMatroid.Analysis.ChainStepNoninvalid
namespace CountingMatroid.Analysis.ObservationRoundDrawSites
end CountingMatroid.Analysis.ObservationRoundDrawSites
namespace CountingMatroid.Analysis.ClassifiedStateSelection
end CountingMatroid.Analysis.ClassifiedStateSelection
namespace CountingMatroid.Analysis.ChainStepBitBound
end CountingMatroid.Analysis.ChainStepBitBound
namespace CountingMatroid.Analysis.PhaseBitCursorBound
end CountingMatroid.Analysis.PhaseBitCursorBound
namespace CountingMatroid.Analysis.PhaseHistoryMultiplierLength
end CountingMatroid.Analysis.PhaseHistoryMultiplierLength
namespace CountingMatroid.Analysis.ScheduleResourceEnvelope
end CountingMatroid.Analysis.ScheduleResourceEnvelope
namespace CountingMatroid.Analysis.ScheduleCostEnvelope
end CountingMatroid.Analysis.ScheduleCostEnvelope
namespace CountingMatroid.Analysis.ScheduleValueEnvelope
end CountingMatroid.Analysis.ScheduleValueEnvelope
section


set_option autoImplicit false

/-!
A concrete ordinal pre-draw probe for the counted restart. The probe observes
an allowed chain attempt before its trials and retains its first descriptor,
including when the ensuing attempt aborts. Forgetting the descriptor preserves
both components of the counted restart, not just its public result.
No stopping law, finite-block bound, or abort attribution is asserted here.
-/
namespace CountingMatroid.Analysis.RestartDrawProbe
open CountingMatroid.Model CountingMatroid.Program CountingMatroid.Model.Operations
open CountingMatroid.Analysis.RestartAttemptAccounting
open CountingMatroid.Analysis.ObservationRoundDrawSites

/-- INTERNAL: Lift a fixed fold through a value-preserving observer. -/
theorem fold_observer_projection {α β γ : Type}
    (f : β → α → Arlib.Computation.Charged Op Cell β)
    (g : (β × γ) → α → Arlib.Computation.Charged Op Cell (β × γ))
    (h : ∀ b c a, (g (b,c) a).val.1 = (f b a).val)
    (xs : List α) (b : β) (c : γ) :
    (Arlib.Computation.Charged.foldl g xs (b,c)).val.1 =
      (Arlib.Computation.Charged.foldl f xs b).val := by
  induction xs generalizing b c with
  | nil => rfl
  | cons a xs ih =>
    rw [Arlib.Computation.Charged.val_foldl_cons,
      Arlib.Computation.Charged.val_foldl_cons]
    have hi := ih (g (b,c) a).val.1 (g (b,c) a).val.2
    rw [← h b c a]
    exact hi







/-- INTERNAL: Probing preserves the exact body continuation and count. -/
theorem probedBody_projection {n : ℕ} (r : ℕ) (o₁ o₂ : IndependenceOracle n)
    (tape : ℕ → Bool) (s : AnnealingSchedule) (q : ℚ) (w : Multipliers n)
    (ordinal : ℕ) (draw : Fin 3)
    (acc : (Option (RestartCursor n) × Bool) × ℕ) (observed : Option (ℕ × ℕ)) :
    (probedBody r o₁ o₂ tape s q w ordinal draw (acc, observed)).val.map Prod.fst =
      (countedBody r o₁ o₂ tape s q w acc).val := by
  simp only [probedBody, Arlib.Computation.Charged.val_bind,
    Arlib.Computation.Charged.val_pure, Option.map_map]
  cases (countedBody r o₁ o₂ tape s q w acc).val <;> rfl



/-- INTERNAL: Forgetting the probe preserves return failure and retained cost. -/
theorem probedReturn_projection {n : ℕ} (r : ℕ) (o₁ o₂ : IndependenceOracle n)
    (tape : ℕ → Bool) (s : AnnealingSchedule) (q : ℚ) (w : Multipliers n)
    (ordinal : ℕ) (draw : Fin 3) (start : RestartCursor n) (count : ℕ)
    (observed : Option (ℕ × ℕ)) :
    (probedReturn r o₁ o₂ tape s q w ordinal draw start count observed).val.1 =
      (countedReturn r o₁ o₂ tape s q w start count).val := by
  have hp := while_observer_projection
    (fun acc (_ : ℕ) => countedBody r o₁ o₂ tape s q w acc)
    (fun acc (_ : ℕ) => probedBody r o₁ o₂ tape s q w ordinal draw acc)
    (fun b c _ => probedBody_projection r o₁ o₂ tape s q w ordinal draw b c)
    (List.range s.restartCap) ((some start, false), count) observed
  simp only [probedReturn, countedReturn, Arlib.Computation.Charged.val_bind,
    Arlib.Computation.Charged.val_pure, Arlib.Computation.Charged.repeatWhile]
  rw [hp]



/-- INTERNAL: The transition observer preserves both counted components. -/
theorem probedTransition_projection {n : ℕ} (r : ℕ) (o₁ o₂ : IndependenceOracle n)
    (tape : ℕ → Bool) (s : AnnealingSchedule) (q : ℚ) (w : Multipliers n)
    (ordinal : ℕ) (draw : Fin 3) (acc : Option (RestartCursor n) × ℕ)
    (observed : Option (ℕ × ℕ)) :
    (probedTransition r o₁ o₂ tape s q w ordinal draw (acc,observed)).val.1 =
      (countedTransition r o₁ o₂ tape s q w acc).val := by
  cases h : acc.1 <;> simp only [probedTransition, countedTransition, h,
    Arlib.Computation.Charged.val_pure, probedReturn_projection]



/-- INTERNAL: The stage observer preserves result and cost with arbitrary
stored weights; no multiplier accuracy assumption enters this identity. -/
theorem probedStage_projection {n : ℕ} (r : ℕ) (o₁ o₂ : IndependenceOracle n)
    (tape : ℕ → Bool) (s : AnnealingSchedule) (tables : LearnedWeights n)
    (ordinal : ℕ) (draw : Fin 3) (index : ℕ) (acc : Option (RestartCursor n) × ℕ)
    (observed : Option (ℕ × ℕ)) :
    (probedStage r o₁ o₂ tape s tables ordinal draw index (acc,observed)).val.1 =
      (countedStage r o₁ o₂ tape s tables index acc).val := by
  simp only [probedStage, countedStage, Arlib.Computation.Charged.val_bind,
    Arlib.Computation.Charged.repeatFor]
  exact fold_observer_projection _ _
    (fun b c _ => probedTransition_projection r o₁ o₂ tape s _ _ ordinal draw b c)
    _ acc observed



/-- INTERNAL: The complete probe is value preserving even on an abort.
Both the public result and the retained attempted-transition count agree. -/
theorem probed_restart_projection {n : ℕ} (r : ℕ) (o₁ o₂ : IndependenceOracle n)
    (tape : ℕ → Bool) (s : AnnealingSchedule) (tables : LearnedWeights n)
    (j cursor ordinal : ℕ) (draw : Fin 3) :
    (probedRestart r o₁ o₂ tape s tables j cursor ordinal draw).val.1 =
      (countedRestart r o₁ o₂ tape s tables j cursor).val := by
  have hp := fold_observer_projection
    (fun acc index => countedStage r o₁ o₂ tape s tables index acc)
    (fun acc index => probedStage r o₁ o₂ tape s tables ordinal draw index acc)
    (fun b c index => probedStage_projection r o₁ o₂ tape s tables ordinal draw index b c)
    (List.range j)
    (some ⟨(freshTransversal n tape cursor).val.1,
      (freshTransversal n tape cursor).val.2, 0⟩, 0) none
  simp only [probedRestart, countedRestart, Arlib.Computation.Charged.val_bind,
    Arlib.Computation.Charged.val_pure, Arlib.Computation.Charged.repeatFor]
  rw [hp]













end CountingMatroid.Analysis.RestartDrawProbe

/-! ### Run record
Newest first. History, not instruction — what this file claims is above.

* 2026-10-09 · proved · return scans retain already-captured descriptors independently of later tape; used this latch in denominator positivity.
* 2026-10-09 · proved · concrete sticky ordinal probes preserve the counted body,
  return, transition, stage, and complete restart, including the abort cost.
-/

end
set_option autoImplicit false

/-!
Operational boundary for the deterministic restart abort cover. Concrete
sticky ordinal probes are defined in RestartDrawProbe, with exact counted-value
projection, denominator positivity, and post-capture retention proved there.
Relative-prefix packaging is proved below. The parent proof is closed relative
to three separate open operational obligations: RestartDrawProbeReplay,
RestartDrawProbeCoverage, and RestartDrawProbeAbort. These concern only fixed
probe functions and require no finite-prefix enumeration or probabilistic bound.
-/
namespace CountingMatroid.Analysis.RestartAttemptDrawSites
end CountingMatroid.Analysis.RestartAttemptDrawSites
open CountingMatroid CountingMatroid.Analysis CountingMatroid.Analysis.RestartAttemptDrawSites

open CountingMatroid.Model CountingMatroid.Program
open CountingMatroid.Analysis.RestartAttemptAccounting
open CountingMatroid.Analysis.StoppedDrawHistory

/-- INTERNAL: Ordinal partial draw descriptors for the counted restart.
Descriptors use the concrete sticky probes in RestartDrawProbe. The imported
operational lemmas state their stopping law, full-trial coverage, and attribution.
Only the actual counted result is used for attribution.
This is the operational part of restart_attempt_draw_cover; it contains no
finite-prefix enumeration or prefix-free combinatorics.
TEXLINE: main.tex:1163-1176,1392-1421 -/
theorem solution (n r : ℕ) (o₁ o₂ : IndependenceOracle n)
    (p : InputParams) (hn : 0 < n) (j : ℕ)
    (hj : j < (CountingMatroid.Interface.Pseudocode.setup n p).L)
    (pref : List Bool) (history : RestartPrefixWitness n r o₁ o₂ p j pref) :
    let s := CountingMatroid.Interface.Pseudocode.setup n p
    let t := CountingMatroid.Model.Run.blockLength n r p - pref.length
    ∃ sites : Fin (3 * s.restartCap) → StoppedDraw t s.drawTrials,
      ∀ suffix : List Bool, suffix.length = t →
        (countedRestart r o₁ o₂ (fun i => ((pref ++ suffix)[i]?).getD false)
          s history.current.tables j history.current.bitCursor).val.1 = none →
        s.restartCap ≤ prefixAttemptCost history suffix ∨
          ∃ k head v, (sites k).site suffix = some (head, v) ∧
            (boundedUniform (fun i => ((pref ++ suffix)[i]?).getD false)
              s.drawTrials v (pref.length + head.length)).val.1 = none := by
  classical
  dsimp only
  by_cases hz : j = 0
  · subst j
    refine ⟨fun _ => ⟨fun _ => none, ?_, ?_, ?_, ?_⟩, ?_⟩
    · intro bits head v hlen hs
      cases hs
    · intro bits other head v hlen hother hs hp
      cases hs
    · intro bits head v hlen hs
      cases hs
    · intro bits head v hlen hs
      cases hs
    · intro suffix hlen habort
      simp only [countedRestart, Arlib.Computation.Charged.val_bind,
        Arlib.Computation.Charged.repeatFor, List.range_zero,
        Arlib.Computation.Charged.val_foldl_nil,
        Arlib.Computation.Charged.val_pure, Option.map_some] at habort
      cases habort
  · let s := CountingMatroid.Interface.Pseudocode.setup n p
    let t := CountingMatroid.Model.Run.blockLength n r p - pref.length
    let tape := fun (suffix : List Bool) (i : ℕ) => ((pref ++ suffix)[i]?).getD false
    let probe := fun (k : Fin (3 * s.restartCap)) (suffix : List Bool) => RestartDrawProbe.restartDrawProbe r o₁ o₂
      (tape suffix) s history.current.tables j history.current.bitCursor k
    let run := fun (suffix : List Bool) => (RestartDrawProbe.probedRestart r o₁ o₂
      (tape suffix) s history.current.tables j history.current.bitCursor
      0 ⟨0, by decide⟩).val.1
    have hprojection (suffix : List Bool) :
        run suffix = (countedRestart r o₁ o₂ (tape suffix) s
          history.current.tables j history.current.bitCursor).val :=
      RestartDrawProbe.probed_restart_projection r o₁ o₂ (tape suffix) s
        history.current.tables j history.current.bitCursor 0 ⟨0, by decide⟩
    have hoperational :
        (∀ (k : Fin (3 * s.restartCap)) bits d, bits.length = t →
          probe k bits = some d →
          pref.length ≤ d.1 ∧
          d.1 + s.drawTrials * ((d.2 - 1).log2 + 1) ≤ pref.length + t ∧
          ∀ other, other.length = t → bits.take (d.1 - pref.length) <+: other →
            probe k other = some d) ∧
        (∀ suffix : List Bool, suffix.length = t → (run suffix).1 = none →
          s.restartCap ≤ (run suffix).2 ∨ ∃ k d,
            probe k suffix = some d ∧
            (boundedUniform (tape suffix) s.drawTrials d.2 d.1).val.1 = none) := by
      constructor
      · intro k bits d hlen hd
        have hr := RestartDrawProbeReplay.restart_draw_probe_replay r o₁ o₂
          s history.current.tables j history.current.bitCursor k (tape bits) d hd
        have hb := RestartDrawProbeCoverage.restart_draw_probe_coverage n r o₁ o₂
          p hn j hj pref history (tape bits) k d hd
        have hstart : pref.length ≤ history.current.bitCursor := by
          have he := congrArg List.length history.consumed
          rw [List.length_take] at he
          exact he.le.trans (Nat.min_le_left _ _)
        have hpref : pref.length ≤ CountingMatroid.Model.Run.blockLength n r p := by
          rw [history.consumed, List.length_take, history.length]
          exact Nat.min_le_right _ _
        have hm : pref.length + t = CountingMatroid.Model.Run.blockLength n r p :=
          Nat.add_sub_of_le hpref
        have hbase := hstart.trans hr.1
        refine ⟨hbase, by simpa only [hm] using hb, ?_⟩
        intro other hother hp
        apply hr.2 (tape other)
        intro i hlo hhi
        change ((pref ++ bits)[i]?).getD false = ((pref ++ other)[i]?).getD false
        by_cases hi : i < pref.length
        · rw [List.getElem?_append_left hi, List.getElem?_append_left hi]
        · rw [List.getElem?_append_right (by omega),
            List.getElem?_append_right (by omega)]
          have htake : (bits.take (d.1 - pref.length)).length = d.1 - pref.length := by
            rw [List.length_take, hlen, Nat.min_eq_left (by omega)]
          obtain ⟨tail, he⟩ := hp
          rw [← he, List.getElem?_append_left (by rw [htake]; omega),
            List.getElem?_take_of_lt (by omega)]
      · intro suffix hlen habort
        have hc : (countedRestart r o₁ o₂ (tape suffix) s history.current.tables
            j history.current.bitCursor).val.1 = none := by
          rw [← hprojection]
          exact habort
        have ha := RestartDrawProbeAbort.restart_draw_probe_abort r o₁ o₂
          (tape suffix) s history.current.tables j history.current.bitCursor hn hc
        simpa only [hprojection, probe] using ha
    choose sites hsites using fun k => stopped_draw_of_absolute_probe
      pref.length t s.drawTrials (probe k)
      (fun bits d _ hd => RestartDrawProbe.restartDrawProbe_positive r o₁ o₂
        (tape bits) s history.current.tables j history.current.bitCursor k d hn hd)
      (hoperational.1 k)
    refine ⟨sites, ?_⟩
    intro suffix hlen habort
    have hrun : (run suffix).1 = none := by
      rw [hprojection]
      exact habort
    rcases hoperational.2 suffix hlen hrun with hcap | ⟨k, d, hd, hfail⟩
    · left
      simpa only [hprojection, prefixAttemptCost, run, tape, s] using hcap
    · obtain ⟨hbase, hbudget, _⟩ := hoperational.1 k suffix d hlen hd
      have htake : (suffix.take (d.1 - pref.length)).length = d.1 - pref.length := by
        rw [List.length_take, hlen, Nat.min_eq_left (by omega)]
      right
      refine ⟨k, suffix.take (d.1 - pref.length), d.2, ?_, ?_⟩
      · rw [hsites k suffix, hd, Option.map_some]
      · rw [htake, Nat.add_sub_of_le hbase]
        exact hfail
