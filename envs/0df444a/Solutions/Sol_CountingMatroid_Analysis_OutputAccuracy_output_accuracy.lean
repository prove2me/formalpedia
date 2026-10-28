-- Prove2me | solution 1 for CountingMatroid.Analysis.OutputAccuracy.output_accuracy
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-24T17:13:53.507271+00:00
-- url     : https://prove2.me/submissions/17a2824b-969b-4f55-b439-290b2a887434

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
import Theorems.Thm_CountingMatroid_Analysis_MedianAmplification_median_amplification_bound
import Theorems.Thm_CountingMatroid_Analysis_OutputAccuracy_commonBaseCount_zeroGround
import Theorems.Thm_CountingMatroid_Analysis_OutputSupport_outputLaw_support_iff
import Theorems.Thm_CountingMatroid_Analysis_SingleRunAccuracy_single_run_accuracy_bound
import Theorems.Thm_CountingMatroid_algorithmLaw_answer_eq

namespace CountingMatroid.Analysis.OutputAccuracy
end CountingMatroid.Analysis.OutputAccuracy
namespace CountingMatroid.Analysis.MedianAmplification
end CountingMatroid.Analysis.MedianAmplification
namespace CountingMatroid.Interface
end CountingMatroid.Interface
namespace CountingMatroid.Meta
end CountingMatroid.Meta
namespace Arlib
end Arlib
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
namespace CountingMatroid
end CountingMatroid
namespace CountingMatroid.Analysis.OutputSupport
end CountingMatroid.Analysis.OutputSupport
section


/-!
# The program and the model are the same algorithm

`CountingMatroid.Model.Program` is what the paper's claims are about: a charged
computation whose state is sealed and whose cost is an operator applied to it.
`CountingMatroid.Interface.Pseudocode` is the same algorithm as mathematics for the
answer/output object the correctness theorem measures. Time and space stay over
`CountingMatroid.Model.Program`; this file is only the transport for correctness.

It is a ladder. Each theorem below is proved from the ones above it, and
`outputLaw_answer_eq` is the top: it is the one lemma the analysis rewrites
through, and the only one anything outside this file should need.

The bridge is closed by a charged insertion lemma and the resulting median,
estimator, and PMF law equalities.
-/

set_option autoImplicit false

namespace CountingMatroid













/-- The paper's correctness event reads the first coordinate of `outputLaw`. Project that coordinate, then rewrite by the answer-law equality; the work counters remain outside this bridge. -/
theorem outputLaw_answer_eq (solver : CountingMatroid.Model.Subroutines.FeasibilityImplementation) (n r : ℕ) (o₁ o₂ : CountingMatroid.Model.IndependenceOracle n) (p : CountingMatroid.Model.InputParams) : (CountingMatroid.Model.Run.outputLaw solver n r o₁ o₂ p).map Prod.fst = CountingMatroid.Interface.Pseudocode.estimateLaw solver n r o₁ o₂ p := by
  simp [CountingMatroid.Model.Run.outputLaw]
  rw [PMF.monad_map_eq_map, PMF.map_comp]
  simpa only [Function.comp_def] using algorithmLaw_answer_eq solver n r o₁ o₂ p

end CountingMatroid

/-! ### Run record
Newest first. History, not instruction — what this file claims is above.

* r1 · proved · closed the answer-law bridge and its six preceding and following correspondences.
-/

end

section


set_option autoImplicit false

namespace CountingMatroid.Analysis.OutputSupport

open CountingMatroid.Model
open CountingMatroid.Model.Subroutines

/-- INTERNAL: A possible charged run is the estimate on one supported finite
block sample. -/
theorem algorithmLaw_support_iff (solver : FeasibilityImplementation) (n r : ℕ)
    (o₁ o₂ : IndependenceOracle n) (p : InputParams)
    (run : Arlib.Computation.Charged Operations.Op Operations.Cell ℚ) :
    run ∈ (Model.Run.algorithmLaw solver n r o₁ o₂ p).support ↔
      ∃ blocks ∈ (Model.Run.fairBlocks
          (CountingMatroid.Program.schedule n p).val.repetitions
          (Model.Run.blockLength n r p)).support,
        CountingMatroid.Program.estimate solver n r o₁ o₂ p
          (Model.Run.blockTape blocks) = run := by
  change run ∈ (PMF.map
    (fun blocks => CountingMatroid.Program.estimate solver n r o₁ o₂ p
      (Model.Run.blockTape blocks))
    (Model.Run.fairBlocks
      (CountingMatroid.Program.schedule n p).val.repetitions
      (Model.Run.blockLength n r p))).support ↔ _
  exact PMF.mem_support_map_iff _ _ run



end CountingMatroid.Analysis.OutputSupport

end

section


set_option autoImplicit false

namespace CountingMatroid.Analysis.OutputAccuracy

open CountingMatroid.Model
open CountingMatroid.Model.Subroutines

/-- INTERNAL: On a nonempty ground set, a negative pretest makes the charged
estimator return zero before drawing a tape.
TEXLINE: main.tex:283-289 -/
theorem estimate_zero_of_false (solver : FeasibilityImplementation)
    (n r : ℕ) (o₁ o₂ : IndependenceOracle n) (p : InputParams)
    (tape : ℕ → ℕ → Bool) (hne : n ≠ 0)
    (hf : (solver.run n r o₁ o₂).val = false) :
    (CountingMatroid.Program.estimate solver n r o₁ o₂ p tape).val = 0 := by
  simp [CountingMatroid.Program.estimate, CountingMatroid.Program.preprocess,
    CountingMatroid.Model.Operations.inputSizeIsZero, hne, hf]



/-- INTERNAL: A negative pretest places only zero answers in the charged
output law on a nonempty ground.
TEXLINE: main.tex:283-289, 1464-1469 -/
theorem output_zero_of_false (solver : FeasibilityImplementation)
    (n r : ℕ) (o₁ o₂ : IndependenceOracle n) (p : InputParams)
    (hne : n ≠ 0) (hf : (solver.run n r o₁ o₂).val = false) :
    ∀ x ∈ (Model.Run.outputLaw solver n r o₁ o₂ p).support, x.1 = 0 := by
  intro x hx
  obtain ⟨run, hrun, heq⟩ :=
    (OutputSupport.outputLaw_support_iff solver n r o₁ o₂ p x).mp hx
  obtain ⟨blocks, _, hblocks⟩ :=
    (OutputSupport.algorithmLaw_support_iff solver n r o₁ o₂ p run).mp hrun
  have hz : run.val = 0 := by
    rw [← hblocks]
    exact estimate_zero_of_false solver n r o₁ o₂ p
      (Model.Run.blockTape blocks) hne hf
  simpa [← heq] using hz



end CountingMatroid.Analysis.OutputAccuracy

/-! ### Run record
Newest first. History, not instruction — what this file claims is above.

* r2 · parallel handoff · reduced the positive-input bound to `single_run_accuracy_bound` and `median_amplification_bound`; proved empty and infeasible cases and transferred the charged output law.
* r1 · open · proved exact zero output through the pretest and support lemmas; the positive-count probability estimate remains open.
-/

end
set_option autoImplicit false

namespace CountingMatroid.Analysis.OutputAccuracy
end CountingMatroid.Analysis.OutputAccuracy
open CountingMatroid CountingMatroid.Analysis CountingMatroid.Analysis.OutputAccuracy

open CountingMatroid.Model
open CountingMatroid.Model.Subroutines

/-- PAPER: main.tex:1253-1329, 1442-1470
The annealing estimate and median amplification meet the relative-error law;
the pretest handles the zero case exactly. -/
theorem solution (solver : FeasibilityImplementation)
    (hcorrect : FeasibilityCorrect solver) :
    ∀ (n r : ℕ) (M₁ M₂ : Matroid (Fin n))
      (o₁ o₂ : IndependenceOracle n) (p : InputParams),
      FullGround M₁ M₂ → CommonRank r M₁ M₂ →
      ExactOracle M₁ o₁ → ExactOracle M₂ o₂ →
      let law := Model.Run.outputLaw solver n r o₁ o₂ p
      let Z : ℚ := commonBaseCount M₁ M₂
      law.toOuterMeasure
        {x | x.1 < (1 - p.ε) * Z ∨ (1 + p.ε) * Z < x.1} ≤
          ENNReal.ofReal (p.δ : ℝ) ∧
      (Z = 0 → ∀ x ∈ law.support, x.1 = 0) := by
  intro n r M₁ M₂ o₁ o₂ p hfull hr h₁ h₂
  have htest := hcorrect n r M₁ M₂ o₁ o₂ hfull hr h₁ h₂
  refine ⟨?_, ?_⟩
  · have hpure :
        (CountingMatroid.Interface.Pseudocode.estimateLaw solver n r o₁ o₂ p).toOuterMeasure
          {y : ℚ | y < (1 - p.ε) * (commonBaseCount M₁ M₂ : ℚ) ∨
            (1 + p.ε) * (commonBaseCount M₁ M₂ : ℚ) < y} ≤
          ENNReal.ofReal (p.δ : ℝ) := by
      by_cases hne : n = 0
      · subst n
        have hcount := commonBaseCount_zeroGround M₁ M₂
        have hconst :
            CountingMatroid.Interface.Pseudocode.estimateLaw solver 0 r o₁ o₂ p =
              PMF.pure (1 : ℚ) := by
          simp [CountingMatroid.Interface.Pseudocode.estimateLaw,
            CountingMatroid.Interface.Pseudocode.estimate,
            CountingMatroid.Interface.Pseudocode.pretest,
            CountingMatroid.Program.preprocess,
            CountingMatroid.Model.Operations.inputSizeIsZero]
          change PMF.map (Function.const (List (List Bool)) (1 : ℚ)) _ = _
          exact PMF.map_const _ _
        rw [hconst, hcount]
        simp only [PMF.toOuterMeasure_pure_apply, Set.mem_setOf_eq]
        split_ifs with hbad
        · rcases hbad with hbad | hbad <;>
            simp only [Nat.cast_one, mul_one] at hbad <;> nlinarith [p.ε_pos]
        · exact bot_le
      · by_cases hz : commonBaseCount M₁ M₂ = 0
        · have hf : (solver.run n r o₁ o₂).val = false := by
            simpa [hz] using htest
          have hconst :
              CountingMatroid.Interface.Pseudocode.estimateLaw solver n r o₁ o₂ p =
                PMF.pure (0 : ℚ) := by
            simp [CountingMatroid.Interface.Pseudocode.estimateLaw,
              CountingMatroid.Interface.Pseudocode.estimate,
              CountingMatroid.Interface.Pseudocode.pretest,
              CountingMatroid.Program.preprocess,
              CountingMatroid.Model.Operations.inputSizeIsZero, hne, hf]
            change PMF.map (Function.const (List (List Bool)) (0 : ℚ)) _ = _
            exact PMF.map_const _ _
          rw [hconst, hz]
          simp [PMF.toOuterMeasure_pure_apply]
        have hpositive : 0 < commonBaseCount M₁ M₂ := Nat.pos_of_ne_zero hz
        have hf : (solver.run n r o₁ o₂).val = true := by
          simpa [hpositive] using htest
        have hpretest :
            CountingMatroid.Interface.Pseudocode.pretest solver n r o₁ o₂ = none := by
          simp [CountingMatroid.Interface.Pseudocode.pretest,
            CountingMatroid.Program.preprocess,
            CountingMatroid.Model.Operations.inputSizeIsZero, hne, hf]
        exact MedianAmplification.median_amplification_bound solver n r o₁ o₂ p
          ((1 - p.ε) * (commonBaseCount M₁ M₂ : ℚ))
          ((1 + p.ε) * (commonBaseCount M₁ M₂ : ℚ)) hpretest
          (SingleRunAccuracy.single_run_accuracy_bound n r M₁ M₂ o₁ o₂ p
            hfull hr h₁ h₂ hpositive)
    rw [← CountingMatroid.outputLaw_answer_eq solver n r o₁ o₂ p] at hpure
    simpa only [PMF.toOuterMeasure_map_apply, Set.preimage_setOf_eq] using hpure
  · intro hZ
    have hZnat : commonBaseCount M₁ M₂ = 0 := by exact_mod_cast hZ
    have hne : n ≠ 0 := by
      intro hn
      subst n
      have hcount := commonBaseCount_zeroGround M₁ M₂
      omega
    have hf : (solver.run n r o₁ o₂).val = false := by
      simpa [hZnat] using htest
    exact output_zero_of_false solver n r o₁ o₂ p hne hf
