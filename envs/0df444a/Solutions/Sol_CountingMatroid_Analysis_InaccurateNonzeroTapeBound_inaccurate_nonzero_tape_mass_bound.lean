-- Prove2me | solution 1 for CountingMatroid.Analysis.InaccurateNonzeroTapeBound.inaccurate_nonzero_tape_mass_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-24T17:08:34.434428+00:00
-- url     : https://prove2.me/submissions/74d7d6a6-d625-4b4f-926d-fa5d522e8370

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
import Theorems.Thm_CountingMatroid_Analysis_FiniteTapeProductAccuracy_finite_tape_product_accuracy
import Theorems.Thm_CountingMatroid_Analysis_TransversalPartition_transversal_partition_contamination

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
namespace CountingMatroid.Analysis.RatioProductAccuracy
end CountingMatroid.Analysis.RatioProductAccuracy
section


set_option autoImplicit false

namespace CountingMatroid.Analysis.InaccurateNonzeroTapeBound

open CountingMatroid.Model

/-- INTERNAL: The product estimate and the final-parameter contamination
bound together imply the requested relative-error interval.
TEXLINE: main.tex:1305-1323 -/
private theorem inaccurate_product_contamination (ε z c y : ℚ)
    (hεpos : 0 < ε) (hεone : ε < 1) (hz : 0 ≤ z)
    (hcLower : z ≤ c) (hcUpper : c ≤ (1 + ε / 10) * z)
    (hyLower : (1 - ε / 4) * c ≤ y)
    (hyUpper : y ≤ (1 + ε / 4) * c) :
    (1 - ε) * z ≤ y ∧ y ≤ (1 + ε) * z := by
  constructor
  · have hfactor : 0 ≤ 1 - ε / 4 := by linarith
    have hmul := mul_le_mul_of_nonneg_left hcLower hfactor
    nlinarith
  · have hfactor : 0 ≤ 1 + ε / 4 := by linarith
    have hmul := mul_le_mul_of_nonneg_left hcUpper hfactor
    have hsmall : 0 ≤ ε * (1 - ε) * z := mul_nonneg (mul_nonneg (le_of_lt hεpos)
      (sub_nonneg.mpr (le_of_lt hεone))) hz
    nlinarith



end CountingMatroid.Analysis.InaccurateNonzeroTapeBound

/-! ### Run record
Newest first. History, not instruction — what this file claims is above.

* r8 · decomposed · the parent now elaborates from a concrete transversal partition sum; its contamination and finite-tape product estimates are separate open children. The live handoff request command was refused before execution.
* r7 · blocked · exact? and aesop leave the partition-sum/product-error witness; project search found no analytic partition sum, conditional phase law, or capped-draw coupling.
* r6 · decomposed · proved the deterministic product/contamination comparison and reduced the tape bound to a partition-sum witness with a narrower product-error event; its conditional phase estimate and finite-bit coupling remain open.
* r5 · open · direct simplification reduces the claim to a nonzero bad-tape count bound; phase estimates and product induction for `Program.boundedRun` are missing.
-/

end
set_option autoImplicit false

namespace CountingMatroid.Analysis.InaccurateNonzeroTapeBound
end CountingMatroid.Analysis.InaccurateNonzeroTapeBound
open CountingMatroid CountingMatroid.Analysis CountingMatroid.Analysis.InaccurateNonzeroTapeBound

open CountingMatroid.Model

/-- INTERNAL: At most one eighth of finite tapes complete with a nonzero
estimate outside the relative-error interval. This is the phase-estimation,
multiplier-induction, and product-accuracy part of the run analysis.
TEXLINE: main.tex:1253-1370 -/
theorem solution (n r : ℕ) (M₁ M₂ : Matroid (Fin n))
    (o₁ o₂ : IndependenceOracle n) (p : InputParams)
    (hfull : FullGround M₁ M₂) (hr : CommonRank r M₁ M₂)
    (h₁ : ExactOracle M₁ o₁) (h₂ : ExactOracle M₂ o₂)
    (hpositive : 0 < commonBaseCount M₁ M₂) :
    let s := CountingMatroid.Interface.Pseudocode.setup n p
    let m := CountingMatroid.Model.Run.blockLength n r p
    (Set.ncard {bits : List Bool | bits.length = m ∧
      let y := CountingMatroid.Interface.Pseudocode.singleRun r o₁ o₂
        (fun i => (bits[i]?).getD false) s
      y ≠ 0 ∧
        (y < (1 - p.ε) * (commonBaseCount M₁ M₂ : ℚ) ∨
         (1 + p.ε) * (commonBaseCount M₁ M₂ : ℚ) < y)} : ENNReal) *
      (1 / 2 : ENNReal) ^ m ≤ (1 / 8 : ENNReal) := by
  dsimp only
  let s := CountingMatroid.Interface.Pseudocode.setup n p
  let m := CountingMatroid.Model.Run.blockLength n r p
  let z : ℚ := commonBaseCount M₁ M₂
  let answer : List Bool → ℚ := fun bits =>
    CountingMatroid.Interface.Pseudocode.singleRun r o₁ o₂
      (fun i => (bits[i]?).getD false) s
  have hz : 0 ≤ z := by simp [z]
  let c : ℚ := TransversalPartition.partitionSum r o₁ o₂ (s.ρ ^ s.L)
  have hcontamination : z ≤ c ∧ c ≤ (1 + p.ε / 10) * z := by
    simpa only [z, c, s] using
      (TransversalPartition.transversal_partition_contamination
        n r M₁ M₂ o₁ o₂ p hfull hr h₁ h₂ hpositive)
  obtain ⟨hcLower, hcUpper⟩ := hcontamination
  have hmass :
      (Set.ncard {bits : List Bool | bits.length = m ∧
        answer bits ≠ 0 ∧
          (answer bits < (1 - p.ε / 4) * c ∨
           (1 + p.ε / 4) * c < answer bits)} : ENNReal) *
        (1 / 2 : ENNReal) ^ m ≤ (1 / 8 : ENNReal) := by
    simpa only [answer, c, s, m] using
      (FiniteTapeProductAccuracy.finite_tape_product_accuracy
        n r M₁ M₂ o₁ o₂ p hfull hr h₁ h₂ hpositive)
  let bad : Set (List Bool) := {bits | bits.length = m ∧
    answer bits ≠ 0 ∧
      (answer bits < (1 - p.ε) * z ∨
       (1 + p.ε) * z < answer bits)}
  let productBad : Set (List Bool) := {bits | bits.length = m ∧
    answer bits ≠ 0 ∧
      (answer bits < (1 - p.ε / 4) * c ∨
       (1 + p.ε / 4) * c < answer bits)}
  have hsubset : bad ⊆ productBad := by
    intro bits hb
    refine ⟨hb.1, hb.2.1, ?_⟩
    by_contra hnot
    have hwithin : (1 - p.ε / 4) * c ≤ answer bits ∧
        answer bits ≤ (1 + p.ε / 4) * c := by
      push Not at hnot
      exact hnot
    have haccurate := inaccurate_product_contamination p.ε z c (answer bits)
      p.ε_pos p.ε_lt_one hz hcLower hcUpper hwithin.1 hwithin.2
    rcases hb.2.2 with hl | hu
    · exact (not_lt_of_ge haccurate.1) hl
    · exact (not_lt_of_ge haccurate.2) hu
  have hfinite : productBad.Finite :=
    (List.finite_length_eq Bool m).subset (by intro bits hb; exact hb.1)
  have hcard : bad.ncard ≤ productBad.ncard :=
    Set.ncard_le_ncard hsubset hfinite
  calc
    (Set.ncard {bits : List Bool | bits.length = m ∧
      answer bits ≠ 0 ∧
        (answer bits < (1 - p.ε) * z ∨
         (1 + p.ε) * z < answer bits)} : ENNReal) *
        (1 / 2 : ENNReal) ^ m
      ≤ (productBad.ncard : ENNReal) * (1 / 2 : ENNReal) ^ m := by
          gcongr
    _ ≤ (1 / 8 : ENNReal) := by simpa [productBad] using hmass
