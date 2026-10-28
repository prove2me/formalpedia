-- Prove2me | solution 1 for CountingMatroid.Analysis.SuccessfulPrefixTrajectoryDomination.successful_prefix_trajectory_domination
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-24T16:49:37.111986+00:00
-- url     : https://prove2.me/submissions/9d4d1a4c-cd2c-4d1d-8513-3484c86237bf

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
import Theorems.Thm_CountingMatroid_Analysis_FinitePhaseEstimationBound_schedule_estimation_budget
import Theorems.Thm_CountingMatroid_Analysis_SuccessfulPrefixAbortBound_successful_prefix_has_good_cursor
import Theorems.Thm_CountingMatroid_Analysis_SuccessfulPrefixRecordedPathMass_realized_path_error
import Theorems.Thm_CountingMatroid_Analysis_SuccessfulPrefixRecordedPathMass_stationary_recorded_mass_moment
import Theorems.Thm_CountingMatroid_Analysis_SuccessfulPrefixRecordedPathMass_successful_prefix_recorded_path_mass_domination
import Theorems.Thm_CountingMatroid_Analysis_SuccessfulPrefixTrajectoryDomination_phase_history_after_consumed_prefix

namespace CountingMatroid.Analysis.SuccessfulPrefixTrajectoryDomination
end CountingMatroid.Analysis.SuccessfulPrefixTrajectoryDomination
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
namespace CountingMatroid.Analysis.FiniteTapePrefixBound
end CountingMatroid.Analysis.FiniteTapePrefixBound
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

section


set_option autoImplicit false

namespace CountingMatroid.Analysis.PhaseObservationExperiment

open CountingMatroid.Model CountingMatroid.Program
open CountingMatroid.Analysis.StationaryMeanIdentities
open CountingMatroid.Analysis.RelativeObservationBounds













/-- INTERNAL: Evaluate the observation experiment by its actual restart and
observation witnesses, without replacing their tape or starting state.
TEXLINE: main.tex:1163-1187 -/
theorem observation_data_iff {n : ℕ} (r : ℕ) (o₁ o₂ : IndependenceOracle n)
    (tape : ℕ → Bool) (s : AnnealingSchedule) (j : ℕ)
    (current : AnnealingCursor n) (observed : ObservationCursor n) :
    phaseObservationData r o₁ o₂ tape s j = some (current, observed) ↔
      BoundedRunPhaseHistory.phaseHistory r o₁ o₂ tape s j = some current ∧
      ∃ start, (restartPhase r o₁ o₂ tape s current.tables j current.bitCursor).val =
        some start ∧ (observePhase r o₁ o₂ tape s (s.ρ ^ j)
          current.currentWeights start).val = some observed := by
  simp only [phaseObservationData, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
    Option.some.injEq, Prod.mk.injEq]
  constructor
  · rintro ⟨current', hh, start, hs, observed', ho, hc, hob⟩
    subst current'
    subst observed'
    exact ⟨hh, start, hs, ho⟩
  · rintro ⟨hh, start, hs, ho⟩
    exact ⟨current, hh, start, hs, observed, ho, rfl, rfl⟩







end CountingMatroid.Analysis.PhaseObservationExperiment

end

section


set_option autoImplicit false

/-!
The stationary correlated-average estimate needed by the finite-suffix MSE
bound. Trajectories use the concrete ideal exchange kernel and all original
operational observables, including diagonal indices and zero-weight states.
The finite product includes one final unused transition; summing it out gives
exactly N observations beginning at the stationary starting state.
A finite geometric action sum proves the covariance bound without requiring
a resolvent, full support, or irreducibility on the extended state space.
-/

namespace CountingMatroid.Analysis.StationaryObservableMSE

open CountingMatroid.Model CountingMatroid.Program
open CountingMatroid.Analysis.IdealExchangeChain
open CountingMatroid.Analysis.PhaseObservationExperiment
open Arlib.Probability Arlib.Probability.FinDist Arlib.MarkovChains









/-- INTERNAL: Good current multipliers are strictly positive at a positive
schedule parameter, including the empty defect-index case.
TEXLINE: main.tex:733-735 -/
theorem good_current_weights_pos (n r : ℕ) (o₁ o₂ : IndependenceOracle n)
    (p : InputParams) (hn : 0 < n) (j : ℕ) (current : AnnealingCursor n)
    (hgood : FirstPhaseFailure.GoodStoredMultipliers r o₁ o₂
      (CountingMatroid.Interface.Pseudocode.setup n p) j current) :
    ∀ index, 0 < current.currentWeights index := by
  intro index
  have hρ := (AnnealingPartitionDrift.schedule_power_lower n p hn).1
  have hC := (AnnealingPartitionDrift.partition_step_bounds n r o₁ o₂ p hn j).1
  have hD := DefectPartitionPositive.defect_partition_pos r o₁ o₂
    ((CountingMatroid.Interface.Pseudocode.setup n p).ρ ^ j) (pow_pos hρ j) index
  exact (div_pos (div_pos hC hD) (by norm_num : (0 : ℚ) < 4)).trans_le
    (hgood.2 index).1



/-- INTERNAL: The stationary real observable mean agrees with the rational
mean used in the completed finite-tape squared error.
TEXLINE: main.tex:1241-1247 -/
theorem operational_observable_mean (n r : ℕ) (o₁ o₂ : IndependenceOracle n)
    (p : InputParams) (hn : 0 < n) (j : ℕ) (current : AnnealingCursor n)
    (hw : ∀ index, 0 < current.currentWeights index) (index : Observable n) :
    let s := CountingMatroid.Interface.Pseudocode.setup n p
    let hq := pow_pos (AnnealingPartitionDrift.schedule_power_lower n p hn).1 j
    Ex (operationalLaw r o₁ o₂ (s.ρ ^ j) current.currentWeights hq hw)
      (operationalObservable r o₁ o₂ s.ρ index) =
      (observableMean r o₁ o₂ s j current index : ℝ) := by
  dsimp only
  cases index with
  | inl b =>
      cases b with
      | false => exact operational_type_mean r o₁ o₂ _ _ _ hw .transversal
      | true => exact operational_numerator_mean r o₁ o₂ _ _ _ _ hw
  | inr pair =>
      rcases pair with ⟨i, k⟩
      exact operational_type_mean r o₁ o₂ _ _ _ hw
        (if i = k then .transversal else .defect i k)



end CountingMatroid.Analysis.StationaryObservableMSE

/-! ### Run record
Newest first. History, not instruction — what this file claims is above.

* r25 · proved · replaced the inverse/infinite-series step by a finite geometric covariance bound; proved weighted projection orthogonality, ideal-chain PSD, and the exact product-path second-moment recurrence in four support modules.
* r24 · open · extracted the projected energy estimate and bounded each observable's variance by one; exact? exhausted the heartbeat limit, and no correlated product-path covariance estimate was found in Arlib or Mathlib. The first live child handoff was mechanically rejected without further diagnostic.
-/

end

section


set_option autoImplicit false

/-!
The operational coupling needed for a successful consumed prefix: completed
finite-tape observation errors are dominated by 10 n² times the stationary
ideal trajectory moment at a single fixed good phase cursor. This does not
assert the stationary time-average estimate; that is a separate obligation.
Deterministic history replay and the fixed-mean error identity are proved,
including prefixes truncated at the end of their finite block. The expectation bound is reduced by exact finite pushforward identities to
pointwise recorded-path mass domination in SuccessfulPrefixRecordedPathMass;
that stochastic comparison remains open there.
-/

namespace CountingMatroid.Analysis.SuccessfulPrefixTrajectoryDomination

open CountingMatroid.Model CountingMatroid.Program
open CountingMatroid.Analysis.PhaseObservationExperiment
open CountingMatroid.Analysis.StationaryObservableMSE

/-- INTERNAL: Regroup a finite weighted execution sum by its recorded path.
This transfers expectations without identifying distinct sample spaces.
TEXLINE: main.tex:1207-1255,1415-1421 -/
theorem weighted_fiber_sum {α β : Type} [Fintype β] [DecidableEq β]
    (S : Finset α) (f : α → β) (w : α → ℝ) (g : β → ℝ) :
    (∑ x ∈ S, w x * g (f x)) =
      ∑ y : β, (∑ x ∈ S, if f x = y then w x else 0) * g y := by
  classical
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro x hx
  simp only [ite_mul, zero_mul]
  simp



/-- INTERNAL: Once history replay fixes the phase cursor, every completed
observation is centered at that cursor's stationary mean. This also retains
zero error on either operational abort, without conditioning away the abort.
TEXLINE: main.tex:1207-1212,1241-1255 -/
theorem observation_squared_error_at_cursor {n : ℕ} (r : ℕ)
    (o₁ o₂ : IndependenceOracle n) (tape : ℕ → Bool)
    (s : AnnealingSchedule) (j : ℕ) (current : AnnealingCursor n)
    (hhistory : BoundedRunPhaseHistory.phaseHistory r o₁ o₂ tape s j = some current)
    (hgood : FirstPhaseFailure.GoodStoredMultipliers r o₁ o₂ s j current)
    (hN : 0 < s.observations) (index : Observable n) :
    observationSquaredError r o₁ o₂ tape s j index =
      match phaseObservationData r o₁ o₂ tape s j with
      | none => 0
      | some (_, observed) =>
          (empiricalMean s observed index - observableMean r o₁ o₂ s j current index) ^ 2 := by
  classical
  cases hdata : phaseObservationData r o₁ o₂ tape s j with
  | none => simp only [observationSquaredError, hdata]
  | some pair =>
      rcases pair with ⟨reached, observed⟩
      have hreached := ((observation_data_iff r o₁ o₂ tape s j reached observed).mp hdata).1
      rw [hhistory] at hreached
      have heq : reached = current := (Option.some.inj hreached).symm
      subst reached
      simp only [observationSquaredError, hdata, if_pos (And.intro hgood hN)]



end CountingMatroid.Analysis.SuccessfulPrefixTrajectoryDomination

/-! ### Run record
Newest first. History, not instruction — what this file claims is above.

* 2026-10-08 · retained · live handoff recorded-path-mass-20261008-a2 was mechanically rejected with no compiler diagnostic. All deterministic support proofs and the parent reduction check in a source-only probe using the existing cursor-extraction contract; standalone elaboration awaits the new module artifacts, and the requested Lake build received no grant. The pointwise stochastic child remains open and owned here.

* 2026-10-08 · decomposed · constructed the actual recorded observation trajectory, proved its accumulator identity and exact finite pushforward, and reduced the parent to pointwise recorded-path mass domination. The remaining stochastic obligation is in SuccessfulPrefixRecordedPathMass, pending live handoff.

* 2026-10-08 · reduced · proved finite consumed-prefix history replay without a coverage premise and the fixed-cursor error identity; the parent uses both, centers errors at the ideal mean, and separates the all-abort case. Expanding the stationary moment exposes different index spaces (bit suffixes and ideal paths); their stochastic comparison remains the single original open obligation.

* r24 · open · extracted the reached good cursor and proved full completed-tape length; aesop left the exact moment-domination inequality, without any trajectory-law comparison in the hypotheses. The first live child handoff was mechanically rejected without further diagnostic.
-/

end
set_option autoImplicit false

/-!
The operational coupling needed for a successful consumed prefix: completed
finite-tape observation errors are dominated by 10 n² times the stationary
ideal trajectory moment at a single fixed good phase cursor. This does not
assert the stationary time-average estimate; that is a separate obligation.
Deterministic history replay and the fixed-mean error identity are proved,
including prefixes truncated at the end of their finite block. The expectation bound is reduced by exact finite pushforward identities to
pointwise recorded-path mass domination in SuccessfulPrefixRecordedPathMass;
that stochastic comparison remains open there.
-/

namespace CountingMatroid.Analysis.SuccessfulPrefixTrajectoryDomination
end CountingMatroid.Analysis.SuccessfulPrefixTrajectoryDomination
open CountingMatroid CountingMatroid.Analysis CountingMatroid.Analysis.SuccessfulPrefixTrajectoryDomination

open CountingMatroid.Model CountingMatroid.Program
open CountingMatroid.Analysis.PhaseObservationExperiment
open CountingMatroid.Analysis.StationaryObservableMSE

/-- INTERNAL: Couple completed executions after a successful consumed prefix
to a fixed stationary ideal trajectory, retaining every operational abort.
The 10 n² factor is the paper's uncapped restart endpoint domination; neither
independent observations nor an alternative bit source is assumed.
TEXLINE: main.tex:1207-1255,1392-1421 -/
theorem solution (n r : ℕ)
    (M₁ M₂ : Matroid (Fin n)) (o₁ o₂ : IndependenceOracle n)
    (p : InputParams) (hn : 0 < n) (hfull : FullGround M₁ M₂)
    (hr : CommonRank r M₁ M₂) (h₁ : ExactOracle M₁ o₁)
    (h₂ : ExactOracle M₂ o₂) (hpositive : 0 < commonBaseCount M₁ M₂)
    (j : ℕ) (hj : j < (CountingMatroid.Interface.Pseudocode.setup n p).L)
    (pref : List Bool) (hprefix : SuccessfulPhasePrefix n r o₁ o₂ p j pref)
    (index : Observable n) :
    let s := CountingMatroid.Interface.Pseudocode.setup n p
    let t := CountingMatroid.Model.Run.blockLength n r p - pref.length
    letI := Classical.propDecidable
    ∃ (current : AnnealingCursor n) (hw : ∀ a, 0 < current.currentWeights a),
      FirstPhaseFailure.GoodStoredMultipliers r o₁ o₂ s j current ∧
      (∑ suffix ∈ Finset.univ.filter (fun suffix : List.Vector Bool t =>
        ObservationCompleted r o₁ o₂
          (fun i => ((pref ++ suffix.val)[i]?).getD false) s j),
        (1 / (2 : ℝ) ^ t) *
          (observationSquaredError r o₁ o₂
            (fun i => ((pref ++ suffix.val)[i]?).getD false) s j index : ℝ)) ≤
        (10 * (n : ℝ) ^ 2) *
          stationaryObservationMoment n r o₁ o₂ p hn j current hw index := by
  classical
  obtain ⟨bits, current, hlen, hprevious, hhistory, hstored, hpref, hprefLength⟩ :=
    SuccessfulPrefixAbortBound.successful_prefix_has_good_cursor
      n r o₁ o₂ p j hj pref hprefix
  let m := CountingMatroid.Model.Run.blockLength n r p
  have hplen : pref.length ≤ m := by
    rw [hprefLength]
    exact Nat.min_le_right _ _
  have hfullLength (suffix : List.Vector Bool (m - pref.length)) :
      (pref ++ suffix.val).length = m := by
    rw [List.length_append, suffix.property]
    omega
  let s := CountingMatroid.Interface.Pseudocode.setup n p
  have hfixed (suffix : List.Vector Bool (m - pref.length)) :
      BoundedRunPhaseHistory.phaseHistory r o₁ o₂
        (fun i => ((pref ++ suffix.val)[i]?).getD false) s j = some current :=
    phase_history_after_consumed_prefix r o₁ o₂ s j m bits pref current
      hlen hhistory hpref suffix
  have hN : 0 < s.observations :=
    (FinitePhaseEstimationBound.schedule_estimation_budget n p hn).2.1
  have herr (suffix : List.Vector Bool (m - pref.length)) :=
    observation_squared_error_at_cursor r o₁ o₂
      (fun i => ((pref ++ suffix.val)[i]?).getD false) s j current
      (hfixed suffix) hstored hN index
  let hw := good_current_weights_pos n r o₁ o₂ p hn j current hstored
  let hq := pow_pos (AnnealingPartitionDrift.schedule_power_lower n p hn).1 j
  let π := IdealExchangeChain.operationalLaw r o₁ o₂ (s.ρ ^ j)
    current.currentWeights hq hw
  let G := operationalObservable r o₁ o₂ s.ρ index
  let P := IdealExchangeChain.idealChain r o₁ o₂ (s.ρ ^ j)
    current.currentWeights hn hq hw
  have hmoment : 0 ≤ stationaryObservationMoment n r o₁ o₂ p hn j current hw index := by
    unfold stationaryObservationMoment trajectorySquaredMoment
    apply Finset.sum_nonneg
    intro path _
    exact mul_nonneg (mul_nonneg (π.coe_nonneg (path 0))
      (Finset.prod_nonneg (fun (i : Fin s.observations) _ =>
        P.coe_nonneg (path i.castSucc) (path i.succ)))) (sq_nonneg _)
  have hmean : Arlib.Probability.FinDist.Ex π G =
      (observableMean r o₁ o₂ s j current index : ℝ) :=
    operational_observable_mean n r o₁ o₂ p hn j current hw index
  have herrReal (suffix : List.Vector Bool (m - pref.length)) :
      (observationSquaredError r o₁ o₂
        (fun i => ((pref ++ suffix.val)[i]?).getD false) s j index : ℝ) =
      match phaseObservationData r o₁ o₂
        (fun i => ((pref ++ suffix.val)[i]?).getD false) s j with
      | none => 0
      | some (_, observed) =>
          ((empiricalMean s observed index : ℝ) - Arlib.Probability.FinDist.Ex π G) ^ 2 := by
    rw [herr suffix]
    cases hdata : phaseObservationData r o₁ o₂
      (fun i => ((pref ++ suffix.val)[i]?).getD false) s j with
    | none => simp only [Rat.cast_zero]
    | some pair =>
        rcases pair with ⟨reached, observed⟩
        simp only [hmean, Rat.cast_pow, Rat.cast_sub]
  refine ⟨current, hw, hstored, ?_⟩
  let completed := Finset.univ.filter (fun suffix : List.Vector Bool (m - pref.length) =>
    ObservationCompleted r o₁ o₂
      (fun i => ((pref ++ suffix.val)[i]?).getD false) s j)
  change (∑ suffix ∈ completed, (1 / (2 : ℝ) ^ (m - pref.length)) *
    (observationSquaredError r o₁ o₂
      (fun i => ((pref ++ suffix.val)[i]?).getD false) s j index : ℝ)) ≤
      (10 * (n : ℝ) ^ 2) *
        stationaryObservationMoment n r o₁ o₂ p hn j current hw index
  by_cases habort : completed = ∅
  · rw [habort, Finset.sum_empty]
    exact mul_nonneg (by positivity) hmoment
  · let pathOf := fun suffix : List.Vector Bool (m - pref.length) =>
      SuccessfulPrefixRecordedPathMass.realizedObservationPath r o₁ o₂
        (fun i => ((pref ++ suffix.val)[i]?).getD false) s j current
    let errorOf := fun states : List.Vector (PairedSet n) s.observations =>
      ((states.val.map G).sum / (s.observations : ℝ) -
        Arlib.Probability.FinDist.Ex π G) ^ 2
    have herrPath (suffix : List.Vector Bool (m - pref.length)) :
        (observationSquaredError r o₁ o₂
          (fun i => ((pref ++ suffix.val)[i]?).getD false) s j index : ℝ) =
        match pathOf suffix with
        | none => 0
        | some states => errorOf states := by
      have he := SuccessfulPrefixRecordedPathMass.realized_path_error r o₁ o₂
        (fun i => ((pref ++ suffix.val)[i]?).getD false) s j current
        (hfixed suffix) hstored hN index
      rw [← hmean] at he
      exact he
    have hsumAll :
        (∑ suffix ∈ completed, (1 / (2 : ℝ) ^ (m - pref.length)) *
          (observationSquaredError r o₁ o₂
            (fun i => ((pref ++ suffix.val)[i]?).getD false) s j index : ℝ)) =
        ∑ suffix : List.Vector Bool (m - pref.length),
          (1 / (2 : ℝ) ^ (m - pref.length)) *
            (observationSquaredError r o₁ o₂
              (fun i => ((pref ++ suffix.val)[i]?).getD false) s j index : ℝ) := by
      apply Finset.sum_subset (Finset.filter_subset _ _)
      intro suffix _ hnot
      have hzero : (observationSquaredError r o₁ o₂
          (fun i => ((pref ++ suffix.val)[i]?).getD false) s j index : ℝ) = 0 := by
        cases hd : phaseObservationData r o₁ o₂
            (fun i => ((pref ++ suffix.val)[i]?).getD false) s j with
        | none => simpa only [hd] using herrReal suffix
        | some pair =>
          rcases pair with ⟨reached, observed⟩
          have hh := ((observation_data_iff r o₁ o₂ _ s j reached observed).mp hd).1
          rw [hfixed suffix] at hh
          have heq : reached = current := (Option.some.inj hh).symm
          subst reached
          exact False.elim (hnot (Finset.mem_filter.mpr
            ⟨Finset.mem_univ _, current, observed, hd, hstored, hN⟩))
      rw [hzero, mul_zero]
    rw [hsumAll]
    conv_lhs =>
      arg 2
      intro suffix
      rw [herrPath suffix]
    rw [weighted_fiber_sum Finset.univ pathOf
      (fun _ => 1 / (2 : ℝ) ^ (m - pref.length))
      (fun path => match path with | none => 0 | some states => errorOf states)]
    simp only [Fintype.sum_option, mul_zero, zero_add]
    change (∑ states : List.Vector (PairedSet n) s.observations,
      SuccessfulPrefixRecordedPathMass.recordedSuffixMass
        r o₁ o₂ s j current pref (m - pref.length) states * errorOf states) ≤
        (10 * (n : ℝ) ^ 2) * trajectorySquaredMoment π P G s.observations
    rw [← SuccessfulPrefixRecordedPathMass.stationary_recorded_mass_moment π P G s.observations,
      Finset.mul_sum]
    apply Finset.sum_le_sum
    intro states _
    have hmass := SuccessfulPrefixRecordedPathMass.successful_prefix_recorded_path_mass_domination
      n r M₁ M₂ o₁ o₂ p hn hfull hr h₁ h₂ hpositive j hj pref hprefix
      current hw hstored hfixed states
    exact (mul_le_mul_of_nonneg_right hmass (sq_nonneg _)).trans_eq (mul_assoc _ _ _)
