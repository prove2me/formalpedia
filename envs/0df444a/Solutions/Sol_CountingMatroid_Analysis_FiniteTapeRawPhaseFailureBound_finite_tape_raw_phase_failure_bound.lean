-- Prove2me | solution 1 for CountingMatroid.Analysis.FiniteTapeRawPhaseFailureBound.finite_tape_raw_phase_failure_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-24T17:00:10.595904+00:00
-- url     : https://prove2.me/submissions/828d7902-84c9-480c-8c21-84ba008ea0db

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
import Theorems.Thm_CountingMatroid_Analysis_FinitePhaseEstimationBound_completed_failure_mass_le
import Theorems.Thm_CountingMatroid_Analysis_FiniteTapePrefixBound_finite_prefix_failure_bound
import Theorems.Thm_CountingMatroid_Analysis_FiniteTapePrefixBound_stopping_prefixes_free
import Theorems.Thm_CountingMatroid_Analysis_SinglePhaseIntervalReplay_single_phase_interval_replay
import Theorems.Thm_CountingMatroid_Analysis_SuccessfulPhaseReplay_successful_history_replay_of_phase_replay
import Theorems.Thm_CountingMatroid_Analysis_SuccessfulPrefixAbortBound_conditional_successful_prefix_abort_mass
import Theorems.Thm_CountingMatroid_Analysis_SuccessfulPrefixObservationMSE_conditional_successful_prefix_observation_mse

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
namespace CountingMatroid.Interface
end CountingMatroid.Interface
namespace CountingMatroid.Meta
end CountingMatroid.Meta
namespace Arlib
end Arlib
namespace CountingMatroid.Analysis.TransversalRankBridge
end CountingMatroid.Analysis.TransversalRankBridge
namespace CountingMatroid.Analysis.GreedyRankCorrect
end CountingMatroid.Analysis.GreedyRankCorrect
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

/-!
Transfer the conditional abort and masked-observation estimates to a whole
finite tape using the prefix-free consumed cursors of successful histories.
No new stochastic assumption is introduced. The analytic bounds are imported
from their existing proof modules.
-/

namespace CountingMatroid.Analysis.FiniteTapeRawPhaseFailureBound

open CountingMatroid.Model

/-- INTERNAL: Matching the consumed prefix of a finite tape gives agreement
at every bit below the consumed cursor, provided that cursor is within the
tape. This uses defaulted list indexing, exactly as in singleRun.
TEXLINE: main.tex:1207-1212,1392-1421 -/
theorem consumed_prefix_tape_agreement (bitsA bitsB : List Bool) (k : ℕ)
    (hk : k ≤ bitsA.length) (hp : bitsA.take k <+: bitsB) :
    ∀ i < k, (bitsA[i]?).getD false = (bitsB[i]?).getD false := by
  intro i hi
  have hlength : i < (bitsA.take k).length := by
    simp only [List.length_take]
    omega
  have heq := List.prefix_iff_getElem?.mp hp i hlength
  have htake := List.getElem?_eq_getElem hlength
  rw [List.getElem?_take_of_lt hi] at htake
  rw [heq, htake]



end CountingMatroid.Analysis.FiniteTapeRawPhaseFailureBound

/-! ### Run record
Newest first. History, not instruction — what this file claims is above.

* r25 · assembled · proved the whole-tape raw-phase failure bound by successful-history interval replay, prefix-free counting, conditional execution-abort mass, and masked observation MSE. The conditional estimates are existing dependencies, with their analytic obligations retained in the original modules.
-/

end
set_option autoImplicit false

/-!
Transfer the conditional abort and masked-observation estimates to a whole
finite tape using the prefix-free consumed cursors of successful histories.
No new stochastic assumption is introduced. The analytic bounds are imported
from their existing proof modules.
-/

namespace CountingMatroid.Analysis.FiniteTapeRawPhaseFailureBound
end CountingMatroid.Analysis.FiniteTapeRawPhaseFailureBound
open CountingMatroid CountingMatroid.Analysis CountingMatroid.Analysis.FiniteTapeRawPhaseFailureBound

open CountingMatroid.Model

/-- INTERNAL: Bound failure of the actual raw empirical phase conditions
following certified earlier phases. Successful consumed prefixes partition
these tapes; their conditional abort and completed-error budgets total
1/[8(L+1)], including capped random draws.
TEXLINE: main.tex:1207-1285,1392-1427 -/
theorem solution (n r : ℕ)
    (M₁ M₂ : Matroid (Fin n)) (o₁ o₂ : IndependenceOracle n)
    (p : InputParams) (hn : 0 < n) (hfull : FullGround M₁ M₂)
    (hr : CommonRank r M₁ M₂) (h₁ : ExactOracle M₁ o₁)
    (h₂ : ExactOracle M₂ o₂)
    (hpositive : 0 < commonBaseCount M₁ M₂)
    (j : ℕ) (hj : j < (CountingMatroid.Interface.Pseudocode.setup n p).L) :
    let s := CountingMatroid.Interface.Pseudocode.setup n p
    let m := CountingMatroid.Model.Run.blockLength n r p
    (Set.ncard {bits : List Bool | bits.length = m ∧
      (∀ a < j, FirstPhaseFailure.CertifiedPhase r o₁ o₂
        (fun i => (bits[i]?).getD false) s a) ∧
      ¬ PhaseMeanCertificate.RawPhaseMeans r o₁ o₂
        (fun i => (bits[i]?).getD false) s j} : ENNReal) *
      (1 / 2 : ENNReal) ^ m ≤ 1 / (8 * ((s.L : ENNReal) + 1)) := by
  classical
  let s := CountingMatroid.Interface.Pseudocode.setup n p
  let m := CountingMatroid.Model.Run.blockLength n r p
  have hsingle := SinglePhaseIntervalReplay.single_phase_interval_replay r o₁ o₂ s
  let E := fun bits : List Bool =>
    (∀ a < j, FirstPhaseFailure.CertifiedPhase r o₁ o₂
      (fun i => (bits[i]?).getD false) s a) ∧
    ¬ PhaseMeanCertificate.RawPhaseMeans r o₁ o₂
      (fun i => (bits[i]?).getD false) s j
  let cursor := fun bits : List Bool =>
    match BoundedRunPhaseHistory.phaseHistory r o₁ o₂
        (fun i => (bits[i]?).getD false) s j with
    | none => 0
    | some current => current.bitCursor
  let good : Set (List Bool) := {bits | bits.length = m ∧
    ∀ a < j, FirstPhaseFailure.CertifiedPhase r o₁ o₂
      (fun i => (bits[i]?).getD false) s a}
  have hfinite : good.Finite :=
    (List.finite_length_eq Bool m).subset (fun _ hb => hb.1)
  let P := hfinite.toFinset.image (fun bits => bits.take (cursor bits))
  have hlen : ∀ pref ∈ P, pref.length ≤ m := by
    intro pref hp
    obtain ⟨bits, hb, rfl⟩ := Finset.mem_image.mp hp
    have hb' : bits ∈ good := hfinite.mem_toFinset.mp hb
    simp only [List.length_take, hb'.1]
    exact Nat.min_le_right _ _
  have hcover : ∀ bits, bits.length = m → E bits →
      ∃ pref ∈ P, pref <+: bits := by
    intro bits hb he
    refine ⟨bits.take (cursor bits), ?_, List.take_prefix _ _⟩
    apply Finset.mem_image.mpr
    exact ⟨bits, hfinite.mem_toFinset.mpr ⟨hb, he.1⟩, rfl⟩
  have hfree_zero : j = 0 →
      ∀ a ∈ P, ∀ b ∈ P, a <+: b → a = b := by
    intro hjzero a ha b hb _
    obtain ⟨bitsA, _, rfl⟩ := Finset.mem_image.mp ha
    obtain ⟨bitsB, _, rfl⟩ := Finset.mem_image.mp hb
    simp only [cursor, hjzero, BoundedRunPhaseHistory.phaseHistory,
      Arlib.Computation.Charged.repeatFor, List.range_zero,
      Arlib.Computation.Charged.val_foldl_nil,
      BoundedRunPhaseHistory.initialCursor, List.take_zero]
  have hreplay : ∀ bitsA ∈ good, ∀ bitsB ∈ good, cursor bitsA ≤ m →
      bitsA.take (cursor bitsA) <+: bitsB → cursor bitsB = cursor bitsA := by
    intro bitsA ha bitsB _ hwithin hprefix
    have hagree := consumed_prefix_tape_agreement bitsA bitsB (cursor bitsA)
      (by simpa only [ha.1] using hwithin) hprefix
    cases hh : BoundedRunPhaseHistory.phaseHistory r o₁ o₂
        (fun i => (bitsA[i]?).getD false) s j with
    | none =>
        -- Earlier certificates prevent an aborted prefix at positive j.
        cases j with
        | zero =>
            change some (BoundedRunPhaseHistory.initialCursor n s) = none at hh
            contradiction
        | succ a =>
            obtain ⟨_, _, _, previous, next, hprevious, hstep, _⟩ := ha.2 a (by omega)
            have hnext : BoundedRunPhaseHistory.phaseHistory r o₁ o₂
                (fun i => (bitsA[i]?).getD false) s (a + 1) = some next := by
              rw [BoundedRunPhaseHistory.phaseHistory_succ]
              change BoundedRunPhaseHistory.phaseHistory r o₁ o₂
                (fun i => (bitsA[i]?).getD false) s a = some previous at hprevious
              rw [hprevious]
              exact hstep
            rw [hh] at hnext
            contradiction
    | some current =>
        have hb := SuccessfulPhaseReplay.successful_history_replay_of_phase_replay
          r o₁ o₂ s hsingle
          (fun i => (bitsA[i]?).getD false) j current hh
          (fun i => (bitsB[i]?).getD false) (by simpa only [cursor, hh] using hagree)
        simp only [cursor, hh, hb]
  have hfree : ∀ a ∈ P, ∀ b ∈ P, a <+: b → a = b := by
    by_cases hjzero : j = 0
    · exact hfree_zero hjzero
    · apply FiniteTapePrefixBound.stopping_prefixes_free m
        hfinite.toFinset cursor
      · intro bits hb
        exact (hfinite.mem_toFinset.mp hb).1
      · intro bitsA ha bitsB hb
        exact hreplay bitsA (hfinite.mem_toFinset.mp ha)
          bitsB (hfinite.mem_toFinset.mp hb)
  have hconditional : ∀ pref ∈ P,
      (Set.ncard {suffix : List Bool |
        suffix.length = m - pref.length ∧ E (pref ++ suffix)} : ENNReal) *
        (1 / 2 : ENNReal) ^ (m - pref.length) ≤
          1 / (8 * ((s.L : ENNReal) + 1)) := by
    intro pref hp
    let rawBad : Set (List Bool) := {suffix | suffix.length = m - pref.length ∧
      E (pref ++ suffix)}
    have hprefix : PhaseObservationExperiment.SuccessfulPhasePrefix
        n r o₁ o₂ p j pref := by
      obtain ⟨bits, hb, hpref⟩ := Finset.mem_image.mp hp
      have hgood := hfinite.mem_toFinset.mp hb
      exact ⟨bits, hgood.1, hgood.2, hpref.symm⟩
    let aborted : Set (List Bool) := {suffix | suffix.length = m - pref.length ∧
      (∀ a < j, FirstPhaseFailure.CertifiedPhase r o₁ o₂
        (fun i => ((pref ++ suffix)[i]?).getD false) s a) ∧
      ¬ PhaseObservationExperiment.ObservationCompleted r o₁ o₂
        (fun i => ((pref ++ suffix)[i]?).getD false) s j}
    let inaccurate : Set (List Bool) := {suffix | suffix.length = m - pref.length ∧
      PhaseObservationExperiment.ObservationCompleted r o₁ o₂
        (fun i => ((pref ++ suffix)[i]?).getD false) s j ∧
      ¬ PhaseMeanCertificate.RawPhaseMeans r o₁ o₂
        (fun i => ((pref ++ suffix)[i]?).getD false) s j}
    have hcoverRaw : rawBad ⊆ aborted ∪ inaccurate := by
      intro suffix hs
      by_cases hdone : PhaseObservationExperiment.ObservationCompleted r o₁ o₂
          (fun i => ((pref ++ suffix)[i]?).getD false) s j
      · exact Or.inr ⟨hs.1, hdone, hs.2.2⟩
      · exact Or.inl ⟨hs.1, hs.2.1, hdone⟩
    have hfiniteUnion : (aborted ∪ inaccurate).Finite :=
      (List.finite_length_eq Bool (m - pref.length)).subset (by
        intro suffix hs
        exact hs.elim (fun h => h.1) (fun h => h.1))
    have hrawCard : rawBad.ncard ≤ aborted.ncard + inaccurate.ncard :=
      (Set.ncard_le_ncard hcoverRaw hfiniteUnion).trans
        (Set.ncard_union_le aborted inaccurate)
    have habort : (aborted.ncard : ENNReal) *
        (1 / 2 : ENNReal) ^ (m - pref.length) ≤
          3 / (32 * ((s.L : ENNReal) + 1)) := by
      exact SuccessfulPrefixAbortBound.conditional_successful_prefix_abort_mass
        n r M₁ M₂ o₁ o₂ p hn hfull hr h₁ h₂ hpositive
        j hj pref hprefix
    have hmoment : ∀ index : PhaseObservationExperiment.Observable n,
        (∑ suffix : List.Vector Bool (m - pref.length),
          PhaseObservationExperiment.observationSquaredError r o₁ o₂
            (fun i => ((pref ++ suffix.val)[i]?).getD false) s j index) /
          (2 : ℚ) ^ (m - pref.length) ≤
            40000 * (n : ℚ) ^ 8 / s.observations := by
      intro index
      exact SuccessfulPrefixObservationMSE.conditional_successful_prefix_observation_mse
        n r M₁ M₂ o₁ o₂ p hn hfull hr h₁ h₂ hpositive
        j hj pref hprefix index
    have hestimate := FinitePhaseEstimationBound.completed_failure_mass_le
      n r o₁ o₂ p hn j pref hmoment
    calc
      (rawBad.ncard : ENNReal) * (1 / 2 : ENNReal) ^ (m - pref.length) ≤
          (aborted.ncard : ENNReal) * (1 / 2 : ENNReal) ^ (m - pref.length) +
          (inaccurate.ncard : ENNReal) * (1 / 2 : ENNReal) ^ (m - pref.length) := by
        rw [← add_mul, ← Nat.cast_add]
        gcongr
      _ ≤ 3 / (32 * ((s.L : ENNReal) + 1)) +
          1 / (32 * ((s.L : ENNReal) + 1)) := add_le_add habort hestimate
      _ = 1 / (8 * ((s.L : ENNReal) + 1)) := by
        rw [← ENNReal.add_div]
        norm_num only
        rw [show (32 : ENNReal) * ((s.L : ENNReal) + 1) =
          4 * (8 * ((s.L : ENNReal) + 1)) by ring]
        simp only [div_eq_mul_inv, ENNReal.mul_inv
          (Or.inl (by norm_num : (4 : ENNReal) ≠ 0))
          (Or.inl (by norm_num : (4 : ENNReal) ≠ ⊤))]
        rw [← mul_assoc, ENNReal.mul_inv_cancel (by norm_num) (by norm_num), one_mul]
  exact FiniteTapePrefixBound.finite_prefix_failure_bound
    m P E (1 / (8 * ((s.L : ENNReal) + 1))) hlen hfree hcover hconditional
