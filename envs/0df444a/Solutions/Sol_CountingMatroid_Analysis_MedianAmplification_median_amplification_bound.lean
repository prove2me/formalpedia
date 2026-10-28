-- Prove2me | solution 1 for CountingMatroid.Analysis.MedianAmplification.median_amplification_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-24T16:35:32.008746+00:00
-- url     : https://prove2.me/submissions/65d4178e-7923-41f6-b3b6-447e89013c1f

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
import Definitions.Def_CountingMatroid_Analysis_IndependentRunsCore
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
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
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
import Mathlib.Data.Rat.Cast.Order
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
import Theorems.Thm_CountingMatroid_Analysis_MedianAmplification_estimateLaw_eq_independentRuns
import Theorems.Thm_CountingMatroid_Analysis_MedianAmplification_independentRuns_support_length
import Theorems.Thm_CountingMatroid_Analysis_MedianAmplification_independent_runs_majority_tail
import Theorems.Thm_CountingMatroid_Analysis_MedianAmplification_median_bad_implies_majority_bad

namespace CountingMatroid.Interface
end CountingMatroid.Interface
namespace CountingMatroid.Meta
end CountingMatroid.Meta
namespace Arlib
end Arlib
namespace CountingMatroid.Analysis.MedianAmplification
end CountingMatroid.Analysis.MedianAmplification
namespace CountingMatroid.Analysis.SingleRunAccuracy
end CountingMatroid.Analysis.SingleRunAccuracy
namespace CountingMatroid.Analysis.InaccurateNonzeroTapeBound
end CountingMatroid.Analysis.InaccurateNonzeroTapeBound
namespace CountingMatroid.Analysis.FiniteTapeProductAccuracy
end CountingMatroid.Analysis.FiniteTapeProductAccuracy
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
namespace CountingMatroid.Analysis.RatioProductAccuracy
end CountingMatroid.Analysis.RatioProductAccuracy
namespace CountingMatroid.Analysis.AbortTapeBound
end CountingMatroid.Analysis.AbortTapeBound
namespace CountingMatroid.Analysis.FiniteTapeLowerTail
end CountingMatroid.Analysis.FiniteTapeLowerTail
namespace CountingMatroid.Analysis.CertifiedPhaseRatioSteps
end CountingMatroid.Analysis.CertifiedPhaseRatioSteps
section


set_option autoImplicit false

namespace CountingMatroid.Analysis.MedianAmplification

open CountingMatroid.Model.Operations
open Arlib.Computation



/-- INTERNAL: The charged halving step has the expected numerical value. -/
private theorem halfStep_val (δ : ℚ) (i : ℕ) (acc : ℕ × ℚ) :
    (halfStep δ i acc).val =
      if δ < acc.2 then some (acc.1 + 1, acc.2 / 2) else none := by
  by_cases h : δ < acc.2 <;> simp [halfStep, ratLess, h, successor, ratDiv]

/-- INTERNAL: Value equation for a charged loop with early exit. -/
private theorem val_cons {β : Type}
    (f : ℕ → β → Charged CountingMatroid.Model.Operations.Op
      CountingMatroid.Model.Operations.Cell (Option β))
    (i : ℕ) (l : List ℕ) (b : β) :
    (Charged.foldlWhile (fun b i => f i b) (i :: l) b).val =
      match (f i b).val with
      | none => b
      | some b' => (Charged.foldlWhile (fun b i => f i b) l b').val := by
  cases h : (f i b).val with
  | none =>
    simp only [Charged.val] at h
    simp [Charged.foldlWhile, Charged.val, h]
  | some b' =>
    simp only [Charged.val] at h
    simp [Charged.foldlWhile, Charged.val, h]

/-- INTERNAL: A halving loop that runs long enough or exits early satisfies the threshold. -/
private theorem loop_bound (δ : ℚ) :
    ∀ (l : List ℕ) (b : ℕ) (power : ℚ),
      power = (1 / 2 : ℚ) ^ b →
      (1 / 2 : ℚ) ^ (b + l.length) ≤ δ →
      (1 / 2 : ℚ) ^
        ((Charged.foldlWhile (fun acc i => halfStep δ i acc) l (b, power)).val.1) ≤ δ := by
  intro l
  induction l with
  | nil =>
    intro b power hp hbound
    change (1 / 2 : ℚ) ^ b ≤ δ
    simpa using hbound
  | cons i l ih =>
    intro b power hp hbound
    rw [val_cons, halfStep_val]
    by_cases h : δ < power
    · simp only [if_pos h]
      apply ih
      · rw [hp, pow_succ]; ring
      · calc
          (1 / 2 : ℚ) ^ (b + 1 + l.length) =
            (1 / 2 : ℚ) ^ (b + (i :: l).length) := by congr 1; simp; omega
          _ ≤ δ := hbound
    · simp only [if_neg h]
      simpa [hp] using (le_of_not_gt h)

/-- INTERNAL: The binary length cap is sufficient for every positive rational threshold. -/
private theorem cap_bound (δ : ℚ) (hδ : 0 < δ) :
    (1 / 2 : ℚ) ^ (δ.den.log2 + 8) ≤ δ := by
  have hnat : δ.den ≤ 2 ^ (δ.den.log2 + 8) := by
    have ht := Nat.lt_pow_succ_log_self Nat.one_lt_two δ.den
    rw [← Nat.log2_eq_log_two] at ht
    calc
      δ.den ≤ 2 ^ (δ.den.log2 + 1) := Nat.le_of_lt ht
      _ ≤ 2 ^ (δ.den.log2 + 8) := by gcongr <;> omega
  have hden : (0 : ℚ) < δ.den := by exact_mod_cast δ.den_pos
  have hpow : (0 : ℚ) < (2 : ℚ) ^ (δ.den.log2 + 8) := by positivity
  have hnum : (1 : ℚ) ≤ (δ.num : ℚ) := by
    have := Rat.num_pos.mpr hδ
    exact_mod_cast this
  conv_rhs => rw [← δ.num_div_den]
  rw [one_div, inv_pow]
  rw [inv_eq_one_div]
  apply (div_le_div_iff₀ hpow hden).mpr
  nlinarith [show (δ.den : ℚ) ≤ (2 : ℚ) ^ (δ.den.log2 + 8) by exact_mod_cast hnat]

/-- INTERNAL: The charged least-halvings search meets its rational threshold. -/
private theorem least_bound (δ : ℚ) (hδ : 0 < δ) :
    (1 / 2 : ℚ) ^ (CountingMatroid.Program.leastHalvings δ).val ≤ δ := by
  unfold CountingMatroid.Program.leastHalvings
  simp only [Charged.val_bind, CountingMatroid.Model.Operations.binaryLoopBound,
    Charged.val_op, Charged.val_pure, Charged.repeatWhile]
  apply loop_bound δ (List.range (δ.den.log2 + 8)) 0 1
  · simp
  · simpa using cap_bound δ hδ

/-- INTERNAL: Transfer a positive rational threshold bound to `ENNReal`. -/
private theorem enn_bound (δ : ℚ) (b : ℕ)
    (hb : (1 / 2 : ℚ) ^ b ≤ δ) :
    (1 / 2 : ENNReal) ^ b ≤ ENNReal.ofReal (δ : ℝ) := by
  have hreal : (1 / 2 : ℝ) ^ b ≤ (δ : ℝ) := by
    have hc : (((1 / 2 : ℚ) ^ b : ℚ) : ℝ) ≤ (δ : ℝ) := by exact_mod_cast hb
    simpa only [Rat.cast_pow, Rat.cast_div, Rat.cast_one, Rat.cast_ofNat] using hc
  have h := ENNReal.ofReal_le_ofReal hreal
  rw [ENNReal.ofReal_pow (by positivity)] at h
  have heq : (1 / 2 : ENNReal) = ENNReal.ofReal (1 / 2 : ℝ) := by
    rw [ENNReal.ofReal_div_of_pos (by norm_num : (0 : ℝ) < 2)]
    norm_num
  simpa only [heq] using h

/-- INTERNAL: The public schedule exposes the charged halving count. -/
private theorem setup_bδ (n : ℕ) (p : CountingMatroid.Model.InputParams) :
    (CountingMatroid.Interface.Pseudocode.setup n p).bδ =
      (CountingMatroid.Program.leastHalvings p.δ).val := by
  dsimp [CountingMatroid.Interface.Pseudocode.setup, CountingMatroid.Program.schedule]

/-- INTERNAL: The charged schedule implements the paper's repetition count and
halving threshold, in the numerical form needed by amplification.
TEXLINE: main.tex:1442-1446 -/
theorem schedule_confidence_bound (n : ℕ) (p : CountingMatroid.Model.InputParams) :
    let s := CountingMatroid.Interface.Pseudocode.setup n p
    s.repetitions = 10 * s.bδ + 1 ∧
      (1 / 2 : ENNReal) ^ s.bδ ≤ ENNReal.ofReal (p.δ : ℝ) := by
  constructor
  · dsimp [CountingMatroid.Interface.Pseudocode.setup, CountingMatroid.Program.schedule]
    simp [CountingMatroid.Model.Operations.successor,
      CountingMatroid.Model.Operations.natMul, Arlib.Computation.Charged.val_op]
  · rw [setup_bδ]
    exact enn_bound p.δ _ (least_bound p.δ p.δ_pos)

end CountingMatroid.Analysis.MedianAmplification

/-! ### Run record
Newest first. History, not instruction — what this file claims is above.

* r1 · proved · established the charged halving loop invariant and denominator cap bound.
-/

end
set_option autoImplicit false

namespace CountingMatroid.Analysis.MedianAmplification
end CountingMatroid.Analysis.MedianAmplification
open CountingMatroid CountingMatroid.Analysis CountingMatroid.Analysis.MedianAmplification

open CountingMatroid.Model
open CountingMatroid.Model.Subroutines

/-- PAPER: main.tex:1442-1462
Independent bounded runs with one-run failure at most one quarter give the
requested confidence after the paper's scheduled median repetitions. -/
theorem solution (solver : FeasibilityImplementation)
    (n r : ℕ) (o₁ o₂ : IndependenceOracle n) (p : InputParams)
    (lower upper : ℚ)
    (hpretest : CountingMatroid.Interface.Pseudocode.pretest solver n r o₁ o₂ = none)
    (hrun :
      let s := CountingMatroid.Interface.Pseudocode.setup n p
      let runLaw :=
        (CountingMatroid.Model.Run.fairTape
          (CountingMatroid.Model.Run.blockLength n r p)).map
          (fun bits => CountingMatroid.Interface.Pseudocode.singleRun r o₁ o₂
            (fun i => (bits[i]?).getD false) s)
      runLaw.toOuterMeasure {y : ℚ | y < lower ∨ upper < y} ≤
        (1 / 4 : ENNReal)) :
    (CountingMatroid.Interface.Pseudocode.estimateLaw solver n r o₁ o₂ p).toOuterMeasure
      {y : ℚ | y < lower ∨ upper < y} ≤ ENNReal.ofReal (p.δ : ℝ) := by
  let s := CountingMatroid.Interface.Pseudocode.setup n p
  let q := (CountingMatroid.Model.Run.fairTape
      (CountingMatroid.Model.Run.blockLength n r p)).map
      (fun bits => CountingMatroid.Interface.Pseudocode.singleRun r o₁ o₂
        (fun i => (bits[i]?).getD false) s)
  let bad : ℚ → Bool := fun x => decide (x < lower ∨ upper < x)
  have hq : q.toOuterMeasure {x | bad x = true} ≤ (1 / 4 : ENNReal) := by
    simpa only [bad, decide_eq_true_eq] using hrun
  obtain ⟨hrep, hδ⟩ := schedule_confidence_bound n p
  have hodd : Odd (10 * s.bδ + 1) := ⟨5 * s.bδ, by omega⟩
  rw [estimateLaw_eq_independentRuns solver n r o₁ o₂ p hpretest,
    PMF.toOuterMeasure_map_apply]
  change (independentRuns q s.repetitions).toOuterMeasure
    (CountingMatroid.Interface.Pseudocode.median ⁻¹'
      {y : ℚ | y < lower ∨ upper < y}) ≤ ENNReal.ofReal (p.δ : ℝ)
  rw [hrep]
  have hsubset :
      (CountingMatroid.Interface.Pseudocode.median ⁻¹'
        {y : ℚ | y < lower ∨ upper < y}) ∩
      (independentRuns q (10 * s.bδ + 1)).support ⊆
      {xs : List ℚ | (10 * s.bδ + 1) / 2 + 1 ≤ xs.countP bad} := by
    intro xs hx
    rcases hx with ⟨hbadxs, hsupp⟩
    have hlen := independentRuns_support_length q (10 * s.bδ + 1) xs hsupp
    have hoddxs : Odd xs.length := by rw [hlen]; exact hodd
    simpa [bad, hlen] using
      (median_bad_implies_majority_bad xs lower upper hoddxs hbadxs)
  calc
    (independentRuns q (10 * s.bδ + 1)).toOuterMeasure
        (CountingMatroid.Interface.Pseudocode.median ⁻¹'
          {y : ℚ | y < lower ∨ upper < y}) ≤
      (independentRuns q (10 * s.bδ + 1)).toOuterMeasure
        {xs : List ℚ | (10 * s.bδ + 1) / 2 + 1 ≤ xs.countP bad} :=
          (independentRuns q (10 * s.bδ + 1)).toOuterMeasure_mono hsubset
    _ ≤ (1 / 2 : ENNReal) ^ s.bδ := independent_runs_majority_tail q bad s.bδ hq
    _ ≤ ENNReal.ofReal (p.δ : ℝ) := hδ
