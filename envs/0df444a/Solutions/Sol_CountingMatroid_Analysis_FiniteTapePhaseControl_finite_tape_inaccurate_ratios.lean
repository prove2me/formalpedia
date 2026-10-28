-- Prove2me | solution 1 for CountingMatroid.Analysis.FiniteTapePhaseControl.finite_tape_inaccurate_ratios
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-24T17:02:49.090368+00:00
-- url     : https://prove2.me/submissions/bb9f1687-8184-4a6f-83ca-a4fe513b91d6

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
import Definitions.Def_CountingMatroidSupport_MarkovChains_Techniques_HittingTime
import Definitions.Def_CountingMatroidSupport_MarkovChains_Techniques_PotentialDecay
import Definitions.Def_CountingMatroidSupport_MarkovChains_Techniques_SpectralGap
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
import Definitions.Def_CountingMatroid_Analysis_CappedRestartFinalTraceDomination
import Definitions.Def_CountingMatroid_Analysis_CappedReturnSubstationary
import Definitions.Def_CountingMatroid_Analysis_CappedTraceIterationSubkernel
import Definitions.Def_CountingMatroid_Analysis_CappedTraceReturnSubkernel
import Definitions.Def_CountingMatroid_Analysis_ChainDrawSiteReplay
import Definitions.Def_CountingMatroid_Analysis_ChainStepIntervalReplay
import Definitions.Def_CountingMatroid_Analysis_ConditionalDefectCoefficients
import Definitions.Def_CountingMatroid_Analysis_ConditionalDefectExtractionCoefficients
import Definitions.Def_CountingMatroid_Analysis_ConditionalDefectQuadratics
import Definitions.Def_CountingMatroid_Analysis_ConditionalObservationAbortMass
import Definitions.Def_CountingMatroid_Analysis_ConditionalSelectedStateSum
import Definitions.Def_CountingMatroid_Analysis_ConditionalTransversalSlots
import Definitions.Def_CountingMatroid_Analysis_ConditionalTransversalSplitTransport
import Definitions.Def_CountingMatroid_Analysis_ConditionalVarianceTree
import Definitions.Def_CountingMatroid_Analysis_CoveredChainIndexedSubkernel
import Definitions.Def_CountingMatroid_Analysis_CoveredChainStepSubkernel
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
import Definitions.Def_CountingMatroid_Analysis_FiniteStoppedFiberMass
import Definitions.Def_CountingMatroid_Analysis_FiniteSuffixDrawAbortMass
import Definitions.Def_CountingMatroid_Analysis_FiniteTapePhaseControl
import Definitions.Def_CountingMatroid_Analysis_FirstPhaseFailure
import Definitions.Def_CountingMatroid_Analysis_IdealExchangeChain
import Definitions.Def_CountingMatroid_Analysis_InitialMultipliersGood
import Definitions.Def_CountingMatroid_Analysis_LeafCliqueFlow
import Definitions.Def_CountingMatroid_Analysis_LorentzianDirectionalSignature
import Definitions.Def_CountingMatroid_Analysis_ObservableProjection
import Definitions.Def_CountingMatroid_Analysis_ObservableVarianceDecomposition
import Definitions.Def_CountingMatroid_Analysis_ObservationRoundDrawSiteCovered
import Definitions.Def_CountingMatroid_Analysis_ObservationRoundDrawSites
import Definitions.Def_CountingMatroid_Analysis_ObservePhaseWork
import Definitions.Def_CountingMatroid_Analysis_OmittedRankWeightPolynomial
import Definitions.Def_CountingMatroid_Analysis_OmittedSlotCoefficientFormula
import Definitions.Def_CountingMatroid_Analysis_OmittedSlotQuadratic
import Definitions.Def_CountingMatroid_Analysis_OmittedTutteNormalization
import Definitions.Def_CountingMatroid_Analysis_PhaseChainWork
import Definitions.Def_CountingMatroid_Analysis_PhaseMeanCertificate
import Definitions.Def_CountingMatroid_Analysis_PhaseObservationBitCoverage
import Definitions.Def_CountingMatroid_Analysis_PhaseObservationExperiment
import Definitions.Def_CountingMatroid_Analysis_PhaseResourcePrimitives
import Definitions.Def_CountingMatroid_Analysis_PositiveTimeTraceChain
import Definitions.Def_CountingMatroid_Analysis_PositiveTimeTraceHarmonic
import Definitions.Def_CountingMatroid_Analysis_PositiveTimeTraceKernel
import Definitions.Def_CountingMatroid_Analysis_ProgramExchangeAcceptanceSubkernel
import Definitions.Def_CountingMatroid_Analysis_QuadraticNonpositiveHyperplane
import Definitions.Def_CountingMatroid_Analysis_RankWeightQuadraticSignature
import Definitions.Def_CountingMatroid_Analysis_RankWeightSupportExchange
import Definitions.Def_CountingMatroid_Analysis_RationalAcceptanceSubkernel
import Definitions.Def_CountingMatroid_Analysis_RationalHeight
import Definitions.Def_CountingMatroid_Analysis_RecordedObservationTrajectory
import Definitions.Def_CountingMatroid_Analysis_RecordedTraceContinuationBound
import Definitions.Def_CountingMatroid_Analysis_RelativeObservationBounds
import Definitions.Def_CountingMatroid_Analysis_RestartAttemptAccounting
import Definitions.Def_CountingMatroid_Analysis_RestartAttemptBudget
import Definitions.Def_CountingMatroid_Analysis_RestartAttemptMoment
import Definitions.Def_CountingMatroid_Analysis_RestartDrawProbe
import Definitions.Def_CountingMatroid_Analysis_RestartDrawProbeAbort
import Definitions.Def_CountingMatroid_Analysis_RestartDrawProbeBitBound
import Definitions.Def_CountingMatroid_Analysis_RestartDrawProbeCoverage
import Definitions.Def_CountingMatroid_Analysis_RestartDrawProbeReplay
import Definitions.Def_CountingMatroid_Analysis_RestartDrawProbeScanReplay
import Definitions.Def_CountingMatroid_Analysis_RestartPhaseBitCoverage
import Definitions.Def_CountingMatroid_Analysis_RestartReturnAbortAttribution
import Definitions.Def_CountingMatroid_Analysis_RestartStageAbortAttribution
import Definitions.Def_CountingMatroid_Analysis_RestartStageAttemptMean
import Definitions.Def_CountingMatroid_Analysis_RestartStageWarmStart
import Definitions.Def_CountingMatroid_Analysis_RestartSuffixMassDefinition
import Definitions.Def_CountingMatroid_Analysis_ReturnAttemptTail
import Definitions.Def_CountingMatroid_Analysis_ScheduleAbortBudget
import Definitions.Def_CountingMatroid_Analysis_ScheduleConfidence
import Definitions.Def_CountingMatroid_Analysis_ScheduleDrawTrialsBridge
import Definitions.Def_CountingMatroid_Analysis_ScheduleOpeningCost
import Definitions.Def_CountingMatroid_Analysis_ScheduleThermalSetupCost
import Definitions.Def_CountingMatroid_Analysis_SelectedMetropolisKernel
import Definitions.Def_CountingMatroid_Analysis_SelectedPairedBijection
import Definitions.Def_CountingMatroid_Analysis_SlotBlockSignature
import Definitions.Def_CountingMatroid_Analysis_SlotDemandPairing
import Definitions.Def_CountingMatroid_Analysis_SlotDemandRecursion
import Definitions.Def_CountingMatroid_Analysis_SlotTransportFlow
import Definitions.Def_CountingMatroid_Analysis_SquarefreeCoordinateHessian
import Definitions.Def_CountingMatroid_Analysis_StationaryMeanIdentities
import Definitions.Def_CountingMatroid_Analysis_StationaryMeanLowerBound
import Definitions.Def_CountingMatroid_Analysis_StationaryObservableMSE
import Definitions.Def_CountingMatroid_Analysis_StationaryPathMoment
import Definitions.Def_CountingMatroid_Analysis_StationaryReturnOccupation
import Definitions.Def_CountingMatroid_Analysis_StoppedDrawHistory
import Definitions.Def_CountingMatroid_Analysis_SuccessfulPrefixObservationMSE
import Definitions.Def_CountingMatroid_Analysis_SuccessfulPrefixRecordedPathMass
import Definitions.Def_CountingMatroid_Analysis_SuccessfulPrefixRecordedTraceSubkernel
import Definitions.Def_CountingMatroid_Analysis_ThreePairSignatureSchur
import Definitions.Def_CountingMatroid_Analysis_TransversalClassPartition
import Definitions.Def_CountingMatroid_Analysis_TransversalEventMean
import Definitions.Def_CountingMatroid_Analysis_TransversalPartition
import Definitions.Def_CountingMatroid_Analysis_TransversalProjection
import Definitions.Def_CountingMatroid_Analysis_TransversalTraceSpectralGap
import Definitions.Def_CountingMatroid_Analysis_TwoPairSignatureBound
import Definitions.Def_CountingMatroid_Interface_Pseudocode
import Definitions.Def_CountingMatroid_Interface_Pseudocode_Extension1
import Definitions.Def_CountingMatroid_Model_Operations
import Definitions.Def_CountingMatroid_Model_Prelude
import Definitions.Def_CountingMatroid_Model_Program
import Definitions.Def_CountingMatroid_Model_Run
import Definitions.Def_CountingMatroid_Model_Subroutines
import Lean
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
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
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Combinatorics.Matroid.Rank.ENat
import Mathlib.Combinatorics.Matroid.Sum
import Mathlib.Data.BitVec
import Mathlib.Data.ENNReal.Inv
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Finsupp.Indicator
import Mathlib.Data.Finsupp.Multiset
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Fintype.Vector
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
import Mathlib.Order.Interval.Finset.Fin
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
import Mathlib.Topology.Order.MonotoneConvergence
import Theorems.Thm_CountingMatroid_Analysis_AnnealingPartitionDrift_partition_step_bounds
import Theorems.Thm_CountingMatroid_Analysis_DefectPartitionPositive_defect_partition_pos
import Theorems.Thm_CountingMatroid_Analysis_EmpiricalPhaseCertificate_raw_phase_certified
import Theorems.Thm_CountingMatroid_Analysis_ExchangeProposalGeometry_exchange_proposal_average
import Theorems.Thm_CountingMatroid_Analysis_ExchangeProposalGeometry_ideal_chain_lazy
import Theorems.Thm_CountingMatroid_Analysis_FiniteTapeRawPhaseFailureBound_finite_tape_raw_phase_failure_bound
import Theorems.Thm_CountingMatroid_Analysis_FirstPhaseFailure_uncertified_card_le_sum
import Theorems.Thm_CountingMatroid_Analysis_InitialMultipliersGood_defect_partition_one
import Theorems.Thm_CountingMatroid_Analysis_ObservablePoincare_observable_poincare
import Theorems.Thm_CountingMatroid_Analysis_ObservableProjection_numerator_observable_projected
import Theorems.Thm_CountingMatroid_Analysis_ObservableProjection_type_indicator_projected
import Theorems.Thm_CountingMatroid_Analysis_PhaseMeanCertificate_raw_phase_means_estimates
import Theorems.Thm_CountingMatroid_Analysis_TypeMassLowerBounds_good_numerator_mean_lower_bound
import Theorems.Thm_CountingMatroid_Analysis_TypeMassLowerBounds_good_type_mass_bounds

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
namespace CountingMatroid.Analysis.FiniteTapeRawPhaseFailureBound
end CountingMatroid.Analysis.FiniteTapeRawPhaseFailureBound
namespace CountingMatroid.Analysis.FiniteTapePrefixBound
end CountingMatroid.Analysis.FiniteTapePrefixBound
namespace CountingMatroid.Analysis.SinglePhaseIntervalReplay
end CountingMatroid.Analysis.SinglePhaseIntervalReplay
namespace CountingMatroid.Analysis.RestartPhaseIntervalReplay
end CountingMatroid.Analysis.RestartPhaseIntervalReplay
namespace CountingMatroid.Analysis.InitialRestartLaw
end CountingMatroid.Analysis.InitialRestartLaw
namespace CountingMatroid.Analysis.TraceReturnIntervalReplay
end CountingMatroid.Analysis.TraceReturnIntervalReplay
namespace CountingMatroid.Analysis.ObservePhaseIntervalReplay
end CountingMatroid.Analysis.ObservePhaseIntervalReplay
namespace CountingMatroid.Analysis.SuccessfulPhaseReplay
end CountingMatroid.Analysis.SuccessfulPhaseReplay
namespace CountingMatroid.Analysis.SuccessfulPrefixTrajectoryDomination
end CountingMatroid.Analysis.SuccessfulPrefixTrajectoryDomination
namespace CountingMatroid.Analysis.SuccessfulPrefixAbortBound
end CountingMatroid.Analysis.SuccessfulPrefixAbortBound
namespace CountingMatroid.Analysis.ObservationRoundDrawCover
end CountingMatroid.Analysis.ObservationRoundDrawCover
namespace CountingMatroid.Analysis.FiniteObservationMarkov
end CountingMatroid.Analysis.FiniteObservationMarkov
namespace CountingMatroid.Analysis.StoppingDrawPrefixCover
end CountingMatroid.Analysis.StoppingDrawPrefixCover
namespace CountingMatroid.Analysis.PhaseBitCursorBound
end CountingMatroid.Analysis.PhaseBitCursorBound
namespace CountingMatroid.Analysis.PhaseHistoryMultiplierLength
end CountingMatroid.Analysis.PhaseHistoryMultiplierLength
namespace CountingMatroid.Analysis.ChainStepBitBound
end CountingMatroid.Analysis.ChainStepBitBound
namespace CountingMatroid.Analysis.ObservationRoundDrawSites
end CountingMatroid.Analysis.ObservationRoundDrawSites
namespace CountingMatroid.Analysis.ClassifiedStateSelection
end CountingMatroid.Analysis.ClassifiedStateSelection
namespace CountingMatroid.Analysis.ChainStepNoninvalid
end CountingMatroid.Analysis.ChainStepNoninvalid
namespace CountingMatroid.Analysis.RestartPhaseTransversal
end CountingMatroid.Analysis.RestartPhaseTransversal
namespace CountingMatroid.Analysis.ScheduleResourceEnvelope
end CountingMatroid.Analysis.ScheduleResourceEnvelope
namespace CountingMatroid.Analysis.ScheduleCostEnvelope
end CountingMatroid.Analysis.ScheduleCostEnvelope
namespace CountingMatroid.Analysis.ScheduleValueEnvelope
end CountingMatroid.Analysis.ScheduleValueEnvelope
namespace CountingMatroid.Analysis.ConditionalRestartAbortMass
end CountingMatroid.Analysis.ConditionalRestartAbortMass
namespace CountingMatroid.Analysis.RestartCostDrawCover
end CountingMatroid.Analysis.RestartCostDrawCover
namespace CountingMatroid.Analysis.RestartAttemptDrawCover
end CountingMatroid.Analysis.RestartAttemptDrawCover
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
namespace Arlib.MarkovChains
end Arlib.MarkovChains
namespace Arlib.MarkovChains.FinChain
end Arlib.MarkovChains.FinChain
namespace Arlib.MarkovChains.FinKernel
end Arlib.MarkovChains.FinKernel
namespace Arlib.Probability
end Arlib.Probability
namespace Arlib.Probability.FinDist
end Arlib.Probability.FinDist
namespace Arlib.Probability.FinKernel
end Arlib.Probability.FinKernel
namespace CountingMatroid.Analysis.ScheduledTransversalTraceMixing
end CountingMatroid.Analysis.ScheduledTransversalTraceMixing
namespace CountingMatroid.Analysis.PositiveTimeTraceMixing
end CountingMatroid.Analysis.PositiveTimeTraceMixing
namespace CountingMatroid.Analysis.IdealChainNonnegDefinite
end CountingMatroid.Analysis.IdealChainNonnegDefinite
namespace CountingMatroid.Analysis.ObservablePoincare
end CountingMatroid.Analysis.ObservablePoincare
namespace CountingMatroid.Analysis.DefectMeanExchangeFlow
end CountingMatroid.Analysis.DefectMeanExchangeFlow
namespace CountingMatroid.Analysis.DefectTransportRaw
end CountingMatroid.Analysis.DefectTransportRaw
namespace CountingMatroid.Analysis.DefectLeafClassifier
end CountingMatroid.Analysis.DefectLeafClassifier
namespace CountingMatroid.Analysis.DefectSlotRoot
end CountingMatroid.Analysis.DefectSlotRoot
namespace CountingMatroid.Analysis.DefectSlotBudget
end CountingMatroid.Analysis.DefectSlotBudget
namespace CountingMatroid.Analysis.DefectSlotFutureBound
end CountingMatroid.Analysis.DefectSlotFutureBound
namespace CountingMatroid.Analysis.DefectTransportTwoPairs
end CountingMatroid.Analysis.DefectTransportTwoPairs
namespace CountingMatroid.Analysis.DefectPartitionTriangle
end CountingMatroid.Analysis.DefectPartitionTriangle
namespace CountingMatroid.Analysis.DefectPartitionQuadraticExtraction
end CountingMatroid.Analysis.DefectPartitionQuadraticExtraction
namespace CountingMatroid.Analysis.ConditionalOperationalCoefficients
end CountingMatroid.Analysis.ConditionalOperationalCoefficients
namespace CountingMatroid.Analysis.ConditionalOccupancyCoefficients
end CountingMatroid.Analysis.ConditionalOccupancyCoefficients
namespace CountingMatroid.Analysis.TransversalVarianceBound
end CountingMatroid.Analysis.TransversalVarianceBound
namespace CountingMatroid.Analysis.ConditionalDefectCoefficientBounds
end CountingMatroid.Analysis.ConditionalDefectCoefficientBounds
namespace CountingMatroid.Analysis.ObservableEnergyDual
end CountingMatroid.Analysis.ObservableEnergyDual
namespace CountingMatroid.Analysis.StationaryCovarianceSum
end CountingMatroid.Analysis.StationaryCovarianceSum
namespace CountingMatroid.Analysis.FinitePhaseEstimationBound
end CountingMatroid.Analysis.FinitePhaseEstimationBound
namespace CountingMatroid.Analysis.BoundedUniformSubkernel
end CountingMatroid.Analysis.BoundedUniformSubkernel
namespace CountingMatroid.Analysis.BoundedUniformSuccessWords
end CountingMatroid.Analysis.BoundedUniformSuccessWords
namespace CountingMatroid.Analysis.FiniteStoppedKernelBind
end CountingMatroid.Analysis.FiniteStoppedKernelBind
namespace CountingMatroid.Analysis.FinitePhaseExecutionAbort
end CountingMatroid.Analysis.FinitePhaseExecutionAbort
namespace CountingMatroid.Analysis.FiniteTapeFirstPhaseBound
end CountingMatroid.Analysis.FiniteTapeFirstPhaseBound
namespace CountingMatroid.Analysis.SuccessfulPrefixRestartEndpointMass
end CountingMatroid.Analysis.SuccessfulPrefixRestartEndpointMass
namespace CountingMatroid.Analysis.StoppedRecordedTraceSubkernel
end CountingMatroid.Analysis.StoppedRecordedTraceSubkernel
namespace CountingMatroid.Analysis.FinitePhaseObservationMSE
end CountingMatroid.Analysis.FinitePhaseObservationMSE
section


/-!
Polynomial output encoding length is proved for every schedule and execution,
using additive observation heights and a phase-product invariant. Nonnegativity
and the zero-phase costs are also proved here. The complete resource envelope
uses separate oracle-call and nonoracle-work obligations; those dependencies
must be closed before the envelope has a complete proof.
-/

set_option autoImplicit false

namespace CountingMatroid.Analysis.BoundedRunResourceEnvelope

open CountingMatroid.Model
open CountingMatroid.Model.Operations
open CountingMatroid.Model.Subroutines

/-- INTERNAL: The charged natural-power fold computes exponentiation. -/
private theorem natPower_fold_value (base : ℕ) (l : List ℕ) (acc : ℕ) :
    (Arlib.Computation.Charged.foldl (fun acc _ => natMul acc base) l acc).val =
      acc * base ^ l.length := by
  induction l generalizing acc with
  | nil => simp
  | cons _ xs ih =>
      rw [Arlib.Computation.Charged.val_foldl_cons, ih]
      simp [natMul, pow_succ]
      ring

/-- INTERNAL: The charged natural power loop computes exponentiation. -/
theorem natPower_value (base exponent : ℕ) :
    (CountingMatroid.Program.natPower base exponent).val = base ^ exponent := by
  unfold CountingMatroid.Program.natPower Arlib.Computation.Charged.repeatFor
  simpa using natPower_fold_value base (List.range exponent) 1


























open CountingMatroid.Analysis.RationalHeight





end CountingMatroid.Analysis.BoundedRunResourceEnvelope

/-! ### Run record
Newest first. History, not instruction — what this file claims is above.

* r16 · handoff blocked · the child-ready shell command was rejected because it used rm -f to remove the old response; no handoff was submitted and BoundedRunOtherSteps remains owned here.
* r16 · partial recovery · proved the all-phase output-length conjunct via rational height and phase-product induction; isolated nonoracle work in BoundedRunOtherSteps for live handoff.
* r15 · decomposed · separated the state-independent oracle charge into BoundedRunOracleCalls; output size and nonoracle charge still need a reachable-state invariant.
* r14 · partial recovery · proved observation type-count and phase-power charge bounds; the positive-phase rational-size and abort-path invariant remains open.
* r13 · partial recovery · proved phase-power binary length and a quadratic charge bound for rational multiplication; the reachable phase-state and abort-path cost invariant is still missing.
* r12 · open · verified that rational multiplication has unbounded charge on arbitrary input (`otherSteps (ratMul (2 ^ K : ℚ) 1) ≥ K`); a reachable-state invariant must also bound observation counts by the loop length.
* r11 · open · direct simplification exposed the entire positive-phase fold; the generic charged loop bound requires a price for arbitrary cursors, while rational-operation costs are unbounded without a reachable-state length invariant.
* r10 · open · audited arbitrary schedule fields and expanded the positive-phase goal; Arlib's fold cost bound needs a state-length invariant for the stored multiplier tables and phase accumulators, which is still absent.
* r9 · partial recovery · proved nonnegativity of every successful observation accumulator, completed phase ratio, and bounded-run output; the three positive-phase quantitative bounds still need a joint phase-state invariant.
* r8 · partial recovery · proved the zero-phase oracle and quadratic work bounds and integrated the entire zero-phase case into the envelope; the positive-phase joint invariant remains open.
* r7 · partial recovery · proved the charged natural-power value and isolated the zero-phase output; the positive-phase state-and-cost invariant remains open.
* r6 · open · isolated the capped-run phase invariant from schedule construction and amplification.
-/

end

section


set_option autoImplicit false

/-!
The phase history below is the value of each prefix of the actual bounded-run
fold, including its absorbing aborted state. Successful local ratio steps
give the product witness used by the lower-tail proof. This is a
deterministic operational representation, not a phase probability estimate.
-/

namespace CountingMatroid.Analysis.BoundedRunPhaseHistory

open CountingMatroid.Model CountingMatroid.Model.Operations
open CountingMatroid.Program CountingMatroid.Analysis.BoundedRunPhase





/-- INTERNAL: Split a charged fold at a prefix while retaining its actual value. -/
private theorem val_foldl_append {α β : Type}
    (f : β → α → Arlib.Computation.Charged Op Cell β)
    (xs ys : List α) (b : β) :
    (Arlib.Computation.Charged.foldl f (xs ++ ys) b).val =
      (Arlib.Computation.Charged.foldl f ys
        (Arlib.Computation.Charged.foldl f xs b).val).val := by
  induction xs generalizing b with
  | nil => rfl
  | cons x xs ih =>
      simpa only [List.cons_append, Arlib.Computation.Charged.val_foldl_cons]
        using ih (f b x).val

/-- INTERNAL: Consecutive history entries are related by the actual phase
body, with the previously reached tables, weights, product and bit cursor.
TEXLINE: main.tex:1160-1205 -/
theorem phaseHistory_succ {n : ℕ} (r : ℕ) (o₁ o₂ : IndependenceOracle n)
    (tape : ℕ → Bool) (s : AnnealingSchedule) (j : ℕ) :
    phaseHistory r o₁ o₂ tape s (j + 1) =
      (boundedRunPhase r o₁ o₂ tape s j
        (phaseHistory r o₁ o₂ tape s j)).val := by
  unfold phaseHistory Arlib.Computation.Charged.repeatFor
  rw [List.range_succ, val_foldl_append]
  rfl











end CountingMatroid.Analysis.BoundedRunPhaseHistory

/-! ### Run record
Newest first. History, not instruction — what this file claims is above.

* r18 · proved · represented actual phase-fold prefixes; proved their successor relation and final-output equality, reconstructed an accurate-ratio witness from successful local steps, and covered witness failure by the first failed phase. No probability estimate or unproved declaration introduced.
-/

end

section


set_option autoImplicit false

namespace CountingMatroid.Analysis.InitialMultipliersGood

open CountingMatroid.Model CountingMatroid.Analysis
open CountingMatroid.Program CountingMatroid.Model.Operations

































/-- PAPER: main.tex:1148-1151
The initial multiplier four is ideal whenever an ordered defect type exists.
The statement includes the vacuous defect families at `n = 0` and `n = 1`.
Its counting proof must characterize the executable classifier's defect fiber,
rather than assume an independent mathematical state classifier. -/
theorem initial_ideal_multiplier {n : ℕ} (r : ℕ)
    (o₁ o₂ : IndependenceOracle n) (index : DefectIndex n) :
    TransversalPartition.partitionSum r o₁ o₂ 1 /
      FirstPhaseFailure.defectPartition r o₁ o₂ 1 index = 4 := by
  have hn : 2 ≤ n := by
    by_contra h
    apply index.distinct
    apply Fin.ext
    omega
  rw [defect_partition_one]
  have hC : TransversalPartition.partitionSum r o₁ o₂ 1 = (2 : ℚ) ^ n := by
    simp [TransversalPartition.partitionSum]
  rw [hC, show n = (n - 2) + 2 by omega, pow_add]
  norm_num

end CountingMatroid.Analysis.InitialMultipliersGood

end

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



/-- INTERNAL: The operational numerator mean is the expectation of the
annealing observable under the ideal stationary law.
TEXLINE: main.tex:1241-1247 -/
theorem operational_numerator_mean {n : ℕ} (r : ℕ) (o₁ o₂ : IndependenceOracle n)
    (q ρ : ℚ) (w : Multipliers n) (hq : 0 < q) (hw : ∀ index, 0 < w index) :
    Ex (operationalLaw r o₁ o₂ q w hq hw) (numeratorObservable r o₁ o₂ ρ) =
      (numeratorMean r o₁ o₂ q ρ w : ℝ) := by
  classical
  unfold Ex numeratorMean
  push_cast
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro state _
  by_cases hk : (classifyState state).val = .transversal
  · simp [operationalLaw, numeratorObservable, hk, div_mul_eq_mul_div]
  · simp [operationalLaw, numeratorObservable, hk]

end CountingMatroid.Analysis.IdealExchangeChain

end
set_option autoImplicit false

namespace CountingMatroid.Analysis.FiniteTapePhaseControl
end CountingMatroid.Analysis.FiniteTapePhaseControl
open CountingMatroid CountingMatroid.Analysis CountingMatroid.Analysis.FiniteTapePhaseControl

open CountingMatroid.Model

/-- INTERNAL: A nonzero capped finite-tape run fails to admit accurate
empirical ratios with probability at most one eighth. The intended witness
is the sequence of `finishPhase` ratios in `Program.boundedRun`.
The deterministic certificate extraction and first-failure union bound are
proved here. `EmpiricalPhaseCertificate` separates the raw restart and
correlated-observation estimates from deterministic finishing and learned-table
preservation. Its scalar arithmetic and exact once-per-index finishing
are proved in `RelativeObservationBounds` and `FinishPhaseEmpiricalUpdate`.
`AnnealingPartitionDrift` proves the concrete schedule's state-weight and
class-partition bounds and ideal-multiplier drift. `DefectPartitionPositive`
proves defect-class nonemptiness against the executable classifier.
`StationaryMeanIdentities` proves the fixed state-weight mean identities using
`TransversalClassPartition`'s proved classifier reindexing.
`PhaseMeanCertificate` therefore removes type-mean identities,
positivity, and multiplier drift from the random event. `InitialMultipliersGood`
proves the executable defect-fiber count and ideal initialization.
`TypeMassLowerBounds` proves lower bounds for all type and numerator means.
`IdealExchangeChain` constructs the normalized law and symmetric exchange
proposal and proves its Metropolis kernel stationary, extending the target by
zero on invalid states. `ObservableProjection` proves the type indicators and
annealing numerator satisfy the required projection range conditions.
`ExchangeProposalGeometry` proves that, on n-element states, the ideal
uniform-label proposal is the paper's half-lazy occupied/unoccupied proposal,
and proves that rejection preserves half-laziness. `ObservablePoincare`
proves the symmetric-conductance energy identity and states the independent
same-paper observable variance estimate.
`FiniteTapeRawPhaseFailureBound` combines the existing conditional abort and
masked-observation-MSE bounds over prefix-free successful consumed histories.
This closes the local finite-tape failure estimate without importing the
lower-tail module. The imported analytic estimates retain their own proof
obligations; this file introduces no additional stochastic proof debt. `InitialRestartLaw`
retains the proved phase-zero fresh-prefix/suffix identity.
`FirstPhaseFailure` supplies the operational certificates and counting cover.
TEXLINE: main.tex:1207-1296,1392-1427 -/
theorem solution (n r : ℕ)
    (M₁ M₂ : Matroid (Fin n)) (o₁ o₂ : IndependenceOracle n)
    (p : InputParams) (hn : 0 < n) (hfull : FullGround M₁ M₂)
    (hr : CommonRank r M₁ M₂) (h₁ : ExactOracle M₁ o₁)
    (h₂ : ExactOracle M₂ o₂)
    (hpositive : 0 < commonBaseCount M₁ M₂) :
    let s := CountingMatroid.Interface.Pseudocode.setup n p
    let m := CountingMatroid.Model.Run.blockLength n r p
    (Set.ncard {bits : List Bool | bits.length = m ∧
      CountingMatroid.Interface.Pseudocode.singleRun r o₁ o₂
        (fun i => (bits[i]?).getD false) s ≠ 0 ∧
      ¬ AccurateRatioProduct n r o₁ o₂ p
        (fun i => (bits[i]?).getD false)} : ENNReal) *
      (1 / 2 : ENNReal) ^ m ≤ (1 / 8 : ENNReal) := by
  classical
  let s := CountingMatroid.Interface.Pseudocode.setup n p
  let m := CountingMatroid.Model.Run.blockLength n r p
  have certified_product (tape : ℕ → Bool)
      (hc : ∀ j < s.L, FirstPhaseFailure.CertifiedPhase r o₁ o₂ tape s j) :
      AccurateRatioProduct n r o₁ o₂ p tape := by
    let weights := (CountingMatroid.Model.Operations.initialWeights n).val
    let initial : CountingMatroid.Program.AnnealingCursor n :=
      ⟨(CountingMatroid.Model.Operations.allocateLearnedWeights n s.L weights).val,
        weights, 1, 0⟩
    let phase := BoundedRunPhase.boundedRunPhase r o₁ o₂ tape s
    let history := fun j => (Arlib.Computation.Charged.repeatFor phase j
      (some initial)).val
    have fold_value
        (f : Option (CountingMatroid.Program.AnnealingCursor n) → ℕ →
          Arlib.Computation.Charged CountingMatroid.Model.Operations.Op
            CountingMatroid.Model.Operations.Cell
            (Option (CountingMatroid.Program.AnnealingCursor n)))
        (l : List ℕ) (b : Option (CountingMatroid.Program.AnnealingCursor n)) :
        (Arlib.Computation.Charged.foldl f l b).val =
          l.foldl (fun acc j => (f acc j).val) b := by
      induction l generalizing b with
      | nil => rfl
      | cons a l ih =>
          simpa only [Arlib.Computation.Charged.val_foldl_cons, List.foldl_cons]
            using ih (f b a).val
    have hsucc (j : ℕ) : history (j + 1) = (phase j (history j)).val := by
      simp only [history, Arlib.Computation.Charged.repeatFor, fold_value,
        List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
    let R := fun j => if hj : j < s.L then Classical.choose (hc j hj) else 1
    have hR (j : ℕ) (hj : j < s.L) :
        (1 - s.η) / (1 + s.η) ≤
          R j / (TransversalPartition.partitionSum r o₁ o₂ (s.ρ ^ (j + 1)) /
            TransversalPartition.partitionSum r o₁ o₂ (s.ρ ^ j)) ∧
        R j / (TransversalPartition.partitionSum r o₁ o₂ (s.ρ ^ (j + 1)) /
            TransversalPartition.partitionSum r o₁ o₂ (s.ρ ^ j)) ≤
          (1 + s.η) / (1 - s.η) ∧
        ∃ current next : CountingMatroid.Program.AnnealingCursor n,
          history j = some current ∧
          (phase j (some current)).val = some next ∧
          next.product = current.product * R j ∧
          FirstPhaseFailure.GoodStoredMultipliers r o₁ o₂ s j current ∧
          (j + 1 < s.L →
            FirstPhaseFailure.GoodStoredMultipliers r o₁ o₂ s (j + 1) next) := by
      simpa only [R, dif_pos hj] using Classical.choose_spec (hc j hj)
    have hproduct : ∀ k ≤ s.L,
        ∃ result : CountingMatroid.Program.AnnealingCursor n,
          history k = some result ∧
            result.product = ∏ j ∈ Finset.range k, R j := by
      intro k
      induction k with
      | zero =>
          intro _
          exact ⟨initial, rfl, by simp [initial]⟩
      | succ k ih =>
          intro hk
          obtain ⟨previous, hprevious, hp⟩ := ih (by omega)
          obtain ⟨current, next, hcurrent, hnext, hmul, _⟩ :=
            (hR k (by omega)).2.2
          have heq : current = previous := Option.some.inj (hcurrent.symm.trans hprevious)
          subst current
          refine ⟨next, ?_, ?_⟩
          · rw [hsucc, hprevious]
            exact hnext
          · rw [hmul, hp, Finset.prod_range_succ]
    obtain ⟨result, hresult, hprod⟩ := hproduct s.L le_rfl
    have hout : CountingMatroid.Interface.Pseudocode.singleRun r o₁ o₂ tape s =
        (2 : ℚ) ^ n * result.product := by
      simp only [CountingMatroid.Interface.Pseudocode.singleRun,
        CountingMatroid.Program.boundedRun, Arlib.Computation.Charged.val_bind]
      change (match history s.L with
        | none => pure (0, 0)
        | some result =>
          (do
            let power ← CountingMatroid.Program.natPower 2 n
            let scale ← CountingMatroid.Model.Operations.ratOfNat power
            let estimate ← CountingMatroid.Model.Operations.ratMul scale result.product
            pure (estimate, result.bitCursor))).val.1 = _
      rw [hresult]
      simp only [Arlib.Computation.Charged.val_bind,
        BoundedRunResourceEnvelope.natPower_value,
        CountingMatroid.Model.Operations.ratOfNat,
        CountingMatroid.Model.Operations.ratMul,
        Arlib.Computation.Charged.val_opMany, Arlib.Computation.Charged.val_pure]
      norm_cast
    refine ⟨R, ?_, ?_⟩
    · exact hout.trans (congrArg ((2 : ℚ) ^ n * ·) hprod)
    · intro j hj
      exact ⟨(hR j hj).1, (hR j hj).2.1⟩
  let bad := fun j => {bits : List Bool | bits.length = m ∧
    FirstPhaseFailure.FirstFailure r o₁ o₂
      (fun i => (bits[i]?).getD false) s j}
  let inaccurate : Set (List Bool) := {bits | bits.length = m ∧
    CountingMatroid.Interface.Pseudocode.singleRun r o₁ o₂
      (fun i => (bits[i]?).getD false) s ≠ 0 ∧
    ¬ AccurateRatioProduct n r o₁ o₂ p (fun i => (bits[i]?).getD false)}
  let uncertified : Set (List Bool) := {bits | bits.length = m ∧
    ¬ ∀ j < s.L, FirstPhaseFailure.CertifiedPhase r o₁ o₂
      (fun i => (bits[i]?).getD false) s j}
  have hsubset : inaccurate ⊆ uncertified := by
    intro bits hb
    refine ⟨hb.1, ?_⟩
    intro hall
    exact hb.2.2 (certified_product _ hall)
  have hfinite : uncertified.Finite :=
    (List.finite_length_eq Bool m).subset (fun _ hb => hb.1)
  have hcard : inaccurate.ncard ≤ ∑ j ∈ Finset.range s.L, (bad j).ncard :=
    (Set.ncard_le_ncard hsubset hfinite).trans
      (FirstPhaseFailure.uncertified_card_le_sum n r o₁ o₂ s m)
  have hcast : (inaccurate.ncard : ENNReal) ≤
      ∑ j ∈ Finset.range s.L, ((bad j).ncard : ENNReal) := by
    exact_mod_cast hcard
  have hη : 0 ≤ s.η := by
    change 0 ≤ p.ε / ((32 * (s.L + 1) : ℕ) : ℚ)
    exact div_nonneg p.ε_pos.le (Nat.cast_nonneg _)
  have hηsmall : s.η ≤ (1 / 3 : ℚ) := by
    have hformula : s.η = p.ε / (32 * ((s.L : ℚ) + 1)) := by
      change p.ε / ((32 * (s.L + 1) : ℕ) : ℚ) = _
      push_cast
      rfl
    rw [hformula]
    apply (div_le_iff₀ (by positivity : (0 : ℚ) < 32 * ((s.L : ℚ) + 1))).mpr
    have hL : (0 : ℚ) ≤ s.L := Nat.cast_nonneg _
    linarith [p.ε_lt_one]
  let rawBad := fun j => {bits : List Bool | bits.length = m ∧
    (∀ a < j, FirstPhaseFailure.CertifiedPhase r o₁ o₂
      (fun i => (bits[i]?).getD false) s a) ∧
    ¬ PhaseMeanCertificate.RawPhaseMeans r o₁ o₂
      (fun i => (bits[i]?).getD false) s j}
  have initial_good : FirstPhaseFailure.GoodStoredMultipliers r o₁ o₂ s 0
      (BoundedRunPhaseHistory.initialCursor n s) := by
    simp [FirstPhaseFailure.GoodStoredMultipliers,
      BoundedRunPhaseHistory.initialCursor,
      CountingMatroid.Model.Operations.initialWeights,
      CountingMatroid.Model.Operations.allocateLearnedWeights,
      InitialMultipliersGood.initial_ideal_multiplier]
  have history_good (tape : ℕ → Bool) (j : ℕ) (hj : j < s.L)
      (hprevious : ∀ a < j, FirstPhaseFailure.CertifiedPhase r o₁ o₂ tape s a) :
      ∃ current : CountingMatroid.Program.AnnealingCursor n,
        BoundedRunPhaseHistory.phaseHistory r o₁ o₂ tape s j = some current ∧
        FirstPhaseFailure.GoodStoredMultipliers r o₁ o₂ s j current := by
    cases j with
    | zero => exact ⟨BoundedRunPhaseHistory.initialCursor n s, rfl, initial_good⟩
    | succ j =>
      obtain ⟨ratio, _, _, current, next, hcurrent, hnext, _, _, hgood⟩ :=
        hprevious j (Nat.lt_succ_self j)
      refine ⟨next, ?_, hgood hj⟩
      rw [BoundedRunPhaseHistory.phaseHistory_succ,
        show BoundedRunPhaseHistory.phaseHistory r o₁ o₂ tape s j = some current
          from hcurrent]
      exact hnext
  have hq (j : ℕ) : 0 < s.ρ ^ j :=
    pow_pos (AnnealingPartitionDrift.schedule_power_lower n p hn).1 j
  let controlledBad := fun j => {bits : List Bool | bits.length = m ∧
    (∀ a < j, FirstPhaseFailure.CertifiedPhase r o₁ o₂
      (fun i => (bits[i]?).getD false) s a) ∧
    ∃ current : CountingMatroid.Program.AnnealingCursor n,
      BoundedRunPhaseHistory.phaseHistory r o₁ o₂
        (fun i => (bits[i]?).getD false) s j = some current ∧
      FirstPhaseFailure.GoodStoredMultipliers r o₁ o₂ s j current ∧
      ∃ hw : ∀ index, 0 < current.currentWeights index,
      Arlib.Probability.Stationary
        (IdealExchangeChain.operationalLaw r o₁ o₂ (s.ρ ^ j)
          current.currentWeights (hq j) hw)
        (IdealExchangeChain.idealChain r o₁ o₂ (s.ρ ^ j)
          current.currentWeights hn (hq j) hw) ∧
      (∀ state : PairedSet n, state.card = n →
        (1 / 2 : ℝ) ≤ IdealExchangeChain.idealChain r o₁ o₂ (s.ρ ^ j)
          current.currentWeights hn (hq j) hw state state) ∧
      (∀ state : PairedSet n, state.card = n → ∀ F : PairedSet n → ℝ,
        (∑ next : PairedSet n,
          IdealExchangeChain.exchangeProposal n hn state next * F next) =
          (1 / 2 : ℝ) * F state + (1 / (2 * (n : ℝ) ^ 2)) *
            ∑ a ∈ state, ∑ b ∈ stateᶜ, F (insert b (state.erase a))) ∧
      (∀ kind state,
        (IdealExchangeChain.operationalLaw r o₁ o₂ (s.ρ ^ j)
          current.currentWeights (hq j) hw) state *
          ObservableProjection.observableProjection
            (IdealExchangeChain.operationalLaw r o₁ o₂ (s.ρ ^ j)
              current.currentWeights (hq j) hw)
            (IdealExchangeChain.typeIndicator kind) state =
        (IdealExchangeChain.operationalLaw r o₁ o₂ (s.ρ ^ j)
          current.currentWeights (hq j) hw) state *
          IdealExchangeChain.typeIndicator kind state) ∧
      (ObservableProjection.observableProjection
        (IdealExchangeChain.operationalLaw r o₁ o₂ (s.ρ ^ j)
          current.currentWeights (hq j) hw)
        (IdealExchangeChain.numeratorObservable r o₁ o₂ s.ρ) =
        IdealExchangeChain.numeratorObservable r o₁ o₂ s.ρ) ∧
      (1 / (5 * (n : ℝ) ^ 2) ≤ Arlib.Probability.FinDist.Ex
        (IdealExchangeChain.operationalLaw r o₁ o₂ (s.ρ ^ j)
          current.currentWeights (hq j) hw)
        (IdealExchangeChain.typeIndicator .transversal)) ∧
      (1 / (20 * (n : ℝ) ^ 2) ≤ Arlib.Probability.FinDist.Ex
        (IdealExchangeChain.operationalLaw r o₁ o₂ (s.ρ ^ j)
          current.currentWeights (hq j) hw)
        (IdealExchangeChain.numeratorObservable r o₁ o₂ s.ρ)) ∧
      (∀ index : DefectIndex n, 1 / (20 * (n : ℝ) ^ 2) ≤ Arlib.Probability.FinDist.Ex
        (IdealExchangeChain.operationalLaw r o₁ o₂ (s.ρ ^ j)
          current.currentWeights (hq j) hw)
        (IdealExchangeChain.typeIndicator (.defect index.emptyPair index.fullPair))) ∧
      (∀ H : PairedSet n → ℝ,
        Arlib.Probability.FinDist.Var
          (IdealExchangeChain.operationalLaw r o₁ o₂ (s.ρ ^ j)
            current.currentWeights (hq j) hw)
          (ObservableProjection.observableProjection
            (IdealExchangeChain.operationalLaw r o₁ o₂ (s.ρ ^ j)
              current.currentWeights (hq j) hw) H) ≤
          2000 * (n : ℝ) ^ 6 * Arlib.MarkovChains.dirichlet
            (IdealExchangeChain.operationalLaw r o₁ o₂ (s.ρ ^ j)
              current.currentWeights (hq j) hw)
            (IdealExchangeChain.idealChain r o₁ o₂ (s.ρ ^ j)
              current.currentWeights hn (hq j) hw) H H) ∧
      ¬ PhaseMeanCertificate.RawPhaseMeans r o₁ o₂
        (fun i => (bits[i]?).getD false) s j}
  have hrawlocal (j : ℕ) (hj : j ∈ Finset.range s.L) :
      ((rawBad j).ncard : ENNReal) * (1 / 2 : ENNReal) ^ m ≤
        1 / (8 * ((s.L : ENNReal) + 1)) := by
    have hsubsetControlled : rawBad j ⊆ controlledBad j := by
      intro bits hb
      obtain ⟨current, hcurrent, hgood⟩ :=
        history_good _ j (Finset.mem_range.mp hj) hb.2.1
      obtain ⟨_, hzero, hdefects⟩ := TypeMassLowerBounds.good_type_mass_bounds
        r o₁ o₂ (s.ρ ^ j) current.currentWeights hn
        (pow_pos (AnnealingPartitionDrift.schedule_power_lower n p hn).1 j)
        hgood.2
      have hC : 0 < TransversalPartition.partitionSum r o₁ o₂ (s.ρ ^ j) :=
        (AnnealingPartitionDrift.partition_step_bounds n r o₁ o₂ p hn j).1
      have hw (index : DefectIndex n) : 0 < current.currentWeights index :=
        (div_pos (div_pos hC
          (DefectPartitionPositive.defect_partition_pos r o₁ o₂ (s.ρ ^ j)
            (hq j) index)) (by norm_num : (0 : ℚ) < 4)).trans_le
          (hgood.2 index).1
      refine ⟨hb.1, hb.2.1, current, hcurrent, hgood, hw,
        IdealExchangeChain.ideal_chain_stationary r o₁ o₂ (s.ρ ^ j)
          current.currentWeights hn (hq j) hw,
        (fun state hcard => ExchangeProposalGeometry.ideal_chain_lazy r o₁ o₂
          (s.ρ ^ j) current.currentWeights hn (hq j) hw state hcard),
        (fun state hcard F => ExchangeProposalGeometry.exchange_proposal_average
          n hn state hcard F),
        (fun kind state => ObservableProjection.type_indicator_projected
          r o₁ o₂ (s.ρ ^ j) current.currentWeights (hq j) hw kind state),
        ObservableProjection.numerator_observable_projected r o₁ o₂ s.ρ _,
        ?_, ?_, ?_, ?_, hb.2.2⟩
      · rw [IdealExchangeChain.operational_type_mean]
        have hr := (Rat.cast_le (K := ℝ)).mpr hzero
        push_cast at hr
        exact hr
      · rw [IdealExchangeChain.operational_numerator_mean]
        have hu := TypeMassLowerBounds.good_numerator_mean_lower_bound
          n r o₁ o₂ p j current.currentWeights hn hgood.2
        have hr := (Rat.cast_le (K := ℝ)).mpr hu
        push_cast at hr
        exact hr
      · intro index
        rw [IdealExchangeChain.operational_type_mean]
        have hr := (Rat.cast_le (K := ℝ)).mpr (hdefects index)
        push_cast at hr
        exact hr
      · intro H
        have hqone : s.ρ ^ j ≤ 1 := by
          calc
            s.ρ ^ j ≤ (1 : ℚ) ^ j := pow_le_pow_left₀
              (AnnealingPartitionDrift.schedule_power_lower n p hn).1.le
              (AnnealingPartitionDrift.schedule_power_lower n p hn).2.1 j
            _ = 1 := by simp
        exact ObservablePoincare.observable_poincare n r M₁ M₂ o₁ o₂
          (s.ρ ^ j) current.currentWeights hn hfull hr h₁ h₂
          (hq j) hqone hw hgood.2 H
    have hcontrolled : ((controlledBad j).ncard : ENNReal) *
        (1 / 2 : ENNReal) ^ m ≤ 1 / (8 * ((s.L : ENNReal) + 1)) := by
      have hsubsetRaw : controlledBad j ⊆ rawBad j := by
        intro bits hb
        rcases hb with ⟨hlen, hprevious, current, hcurrent, hgood, hw,
          hstationary, hlazy, hproposal, htypeProjection, hnumeratorProjection,
          hzeroMean, hnumeratorMean, hdefectMeans, hpoincare, hraw⟩
        exact ⟨hlen, hprevious, hraw⟩
      have hfiniteRaw : (rawBad j).Finite :=
        (List.finite_length_eq Bool m).subset (fun _ hb => hb.1)
      have hc : ((controlledBad j).ncard : ENNReal) ≤
          ((rawBad j).ncard : ENNReal) := by
        exact_mod_cast Set.ncard_le_ncard hsubsetRaw hfiniteRaw
      exact (mul_le_mul_of_nonneg_right hc bot_le).trans
        (FiniteTapeRawPhaseFailureBound.finite_tape_raw_phase_failure_bound
          n r M₁ M₂ o₁ o₂ p hn hfull hr h₁ h₂ hpositive j
          (Finset.mem_range.mp hj))
    have hfiniteControlled : (controlledBad j).Finite :=
      (List.finite_length_eq Bool m).subset (fun _ hb => hb.1)
    have hc : ((rawBad j).ncard : ENNReal) ≤ ((controlledBad j).ncard : ENNReal) := by
      exact_mod_cast Set.ncard_le_ncard hsubsetControlled hfiniteControlled
    exact (mul_le_mul_of_nonneg_right hc bot_le).trans hcontrolled
  have hlocal (j : ℕ) (hj : j ∈ Finset.range s.L) :
      ((bad j).ncard : ENNReal) * (1 / 2 : ENNReal) ^ m ≤
        1 / (8 * ((s.L : ENNReal) + 1)) := by
    have hsubsetRaw : bad j ⊆ rawBad j := by
      intro bits hb
      refine ⟨hb.1, hb.2.1, ?_⟩
      intro hraw
      exact hb.2.2 (EmpiricalPhaseCertificate.raw_phase_certified
        r o₁ o₂ _ s j hη hηsmall
        (PhaseMeanCertificate.raw_phase_means_estimates n r o₁ o₂ p hn _ j hraw))
    have hfiniteRaw : (rawBad j).Finite :=
      (List.finite_length_eq Bool m).subset (fun _ hb => hb.1)
    have hc : ((bad j).ncard : ENNReal) ≤ ((rawBad j).ncard : ENNReal) := by
      exact_mod_cast Set.ncard_le_ncard hsubsetRaw hfiniteRaw
    exact (mul_le_mul_of_nonneg_right hc bot_le).trans (hrawlocal j hj)
  change (inaccurate.ncard : ENNReal) * (1 / 2 : ENNReal) ^ m ≤ _
  calc
    (inaccurate.ncard : ENNReal) * (1 / 2 : ENNReal) ^ m ≤
        (∑ j ∈ Finset.range s.L, ((bad j).ncard : ENNReal)) *
          (1 / 2 : ENNReal) ^ m := mul_le_mul_of_nonneg_right hcast bot_le
    _ = ∑ j ∈ Finset.range s.L,
        ((bad j).ncard : ENNReal) * (1 / 2 : ENNReal) ^ m := Finset.sum_mul ..
    _ ≤ ∑ _j ∈ Finset.range s.L, 1 / (8 * ((s.L : ENNReal) + 1)) :=
      Finset.sum_le_sum hlocal
    _ = (s.L : ENNReal) * (1 / (8 * ((s.L : ENNReal) + 1))) := by simp
    _ = (1 / 8 : ENNReal) * ((s.L : ENNReal) / ((s.L : ENNReal) + 1)) := by
      simp only [div_eq_mul_inv, one_mul,
        ENNReal.mul_inv (Or.inl (by norm_num : (8 : ENNReal) ≠ 0))
          (Or.inl (by norm_num : (8 : ENNReal) ≠ ⊤))]
      ac_rfl
    _ ≤ (1 / 8 : ENNReal) * 1 :=
      mul_le_mul_of_nonneg_left (ENNReal.div_le_of_le_mul (by simp)) bot_le
    _ = (1 / 8 : ENNReal) := mul_one _
