-- Prove2me | solution 1 for CountingMatroid.Analysis.DefectMeanExchangeFlow.defect_mean_exchange_flow
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-24T16:25:08.962717+00:00
-- url     : https://prove2.me/submissions/d50baff3-8a7d-4979-b9dc-cd2a95470f68

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
import Definitions.Def_CountingMatroid_Analysis_ConditionalDefectCoefficients
import Definitions.Def_CountingMatroid_Analysis_ConditionalDefectExtractionCoefficients
import Definitions.Def_CountingMatroid_Analysis_ConditionalDefectQuadratics
import Definitions.Def_CountingMatroid_Analysis_ConditionalSelectedStateSum
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
import Definitions.Def_CountingMatroid_Analysis_PhaseResourcePrimitives
import Definitions.Def_CountingMatroid_Analysis_QuadraticNonpositiveHyperplane
import Definitions.Def_CountingMatroid_Analysis_RankWeightQuadraticSignature
import Definitions.Def_CountingMatroid_Analysis_RankWeightSupportExchange
import Definitions.Def_CountingMatroid_Analysis_RationalHeight
import Definitions.Def_CountingMatroid_Analysis_RelativeObservationBounds
import Definitions.Def_CountingMatroid_Analysis_ScheduleConfidence
import Definitions.Def_CountingMatroid_Analysis_ScheduleOpeningCost
import Definitions.Def_CountingMatroid_Analysis_ScheduleThermalSetupCost
import Definitions.Def_CountingMatroid_Analysis_SlotBlockSignature
import Definitions.Def_CountingMatroid_Analysis_SlotDemandPairing
import Definitions.Def_CountingMatroid_Analysis_SlotDemandRecursion
import Definitions.Def_CountingMatroid_Analysis_SlotTransportFlow
import Definitions.Def_CountingMatroid_Analysis_SquarefreeCoordinateHessian
import Definitions.Def_CountingMatroid_Analysis_StationaryMeanIdentities
import Definitions.Def_CountingMatroid_Analysis_ThreePairSignatureSchur
import Definitions.Def_CountingMatroid_Analysis_TransversalClassPartition
import Definitions.Def_CountingMatroid_Analysis_TransversalEventMean
import Definitions.Def_CountingMatroid_Analysis_TransversalPartition
import Definitions.Def_CountingMatroid_Analysis_TransversalProjection
import Definitions.Def_CountingMatroid_Analysis_TwoPairSignatureBound
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
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Finsupp.Indicator
import Mathlib.Data.Finsupp.Multiset
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.List.Basic
import Mathlib.Data.List.Induction
import Mathlib.Data.List.Nodup
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
import Theorems.Thm_CountingMatroid_Analysis_DefectPartitionPositive_defect_partition_pos
import Theorems.Thm_CountingMatroid_Analysis_DefectPartitionTriangle_defect_partition_triangle
import Theorems.Thm_CountingMatroid_Analysis_DefectTransportRaw_defect_transport_raw
import Theorems.Thm_CountingMatroid_Analysis_TypeMassLowerBounds_good_type_mass_bounds

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
namespace CountingMatroid.Analysis.DefectMeanExchangeFlow
end CountingMatroid.Analysis.DefectMeanExchangeFlow
namespace CountingMatroid.Analysis.DefectTransportRaw
end CountingMatroid.Analysis.DefectTransportRaw
namespace CountingMatroid.Analysis.DefectLeafClassifier
end CountingMatroid.Analysis.DefectLeafClassifier
namespace CountingMatroid.Analysis.DefectSlotRoot
end CountingMatroid.Analysis.DefectSlotRoot
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
set_option autoImplicit false

/-!
The signed exchange-current bound for the paper's defect-mean transport.
The numerical specialization of goodness and the large-event assumption is
proved here. The remaining mathematical obligations are the three-pair
coefficient inequality in `DefectPartitionTriangle` and the recursive
flow construction in `DefectTransportRaw`; both are imported and used.
-/

namespace CountingMatroid.Analysis.DefectMeanExchangeFlow
end CountingMatroid.Analysis.DefectMeanExchangeFlow
open CountingMatroid CountingMatroid.Analysis CountingMatroid.Analysis.DefectMeanExchangeFlow

open CountingMatroid.Model CountingMatroid.Program
open CountingMatroid.Analysis.IdealExchangeChain
open CountingMatroid.Analysis.ObservableVarianceDecomposition
open CountingMatroid.Analysis.TransversalEventMean
open CountingMatroid.Analysis.ExchangeFlowEnergy

/-- INTERNAL: A normalized exchange-supported current from an ordered defect
fiber to any prescribed two-pair transversal event carrying at least one
quarter of the transversal mass. The cost is the paper's `C_d/c₀` rescaled
by `2n²` times the operational normalizer.
TEXLINE: main.tex:493-709,868-908 -/
theorem solution (n r : ℕ) (M₁ M₂ : Matroid (Fin n))
    (o₁ o₂ : IndependenceOracle n) (q : ℚ) (w : Multipliers n)
    (hn : 0 < n) (hfull : FullGround M₁ M₂) (hr : CommonRank r M₁ M₂)
    (h₁ : ExactOracle M₁ o₁) (h₂ : ExactOracle M₂ o₂)
    (hq : 0 < q) (hqone : q ≤ 1) (hw : ∀ index, 0 < w index)
    (hgood : ∀ index,
      (TransversalPartition.partitionSum r o₁ o₂ q /
        FirstPhaseFailure.defectPartition r o₁ o₂ q index) / 4 ≤ w index ∧
      w index ≤ 4 * (TransversalPartition.partitionSum r o₁ o₂ q /
        FirstPhaseFailure.defectPartition r o₁ o₂ q index))
    (i k : Fin n) (hik : i ≠ k) (a b : Bool)
    (hlarge : classMass (operationalLaw r o₁ o₂ q w hq hw) .transversal / 4 ≤
      eventMass (operationalLaw r o₁ o₂ q w hq hw) (pairEvent i k a b)) :
    let π := operationalLaw r o₁ o₂ q w hq hw
    let κ := fun state next : PairedSet n =>
      exchangeProposal n hn state next * min (π state) (π next)
    ∃ flow : FlowCertificate κ (conditionalMeanDemand π (.defect i k) (pairEvent i k a b)),
      flowEnergy κ flow.current ≤
        (8 + 32 * (n : ℝ)) * (2 * (n : ℝ) ^ 2 / classMass π .transversal) := by
  classical
  intro π κ
  let A := pairEvent i k a b
  -- Previous concrete route, retained in DefectTransportRaw: the dense
  -- source-sink product has the right divergence but fails exchange support.
  -- At n=3 the defect {(1,false),(1,true),(2,false)} and transversal
  -- {(0,false),(1,false),(2,true)} cannot be related by a single exchange.
  -- The prior check is scratch/observable-poincare/NonexchangeProbe.lean.
  have hnreal : (0 : ℝ) < n := by exact_mod_cast hn
  have htype := TypeMassLowerBounds.good_type_mass_bounds r o₁ o₂ q w hn hq hgood
  have hp₀lower : 1 / (5 * (n : ℝ) ^ 2) ≤ classMass π .transversal := by
    dsimp only [π]
    rw [operational_class_mass]
    have hc := (Rat.cast_le (K := ℝ)).mpr htype.2.1
    simpa only [Rat.cast_div, Rat.cast_one, Rat.cast_mul, Rat.cast_ofNat,
      Rat.cast_pow, Rat.cast_natCast] using hc
  have hp₀ : 0 < classMass π .transversal :=
    (div_pos (by norm_num) (by positivity)).trans_le hp₀lower
  have hdLower : 1 / (20 * (n : ℝ) ^ 2) ≤ classMass π (.defect i k) := by
    dsimp only [π]
    rw [operational_class_mass]
    have hc := (Rat.cast_le (K := ℝ)).mpr (htype.2.2 ⟨i, k, hik⟩)
    simpa only [Rat.cast_div, Rat.cast_one, Rat.cast_mul, Rat.cast_ofNat,
      Rat.cast_pow, Rat.cast_natCast] using hc
  have hd : 0 < classMass π (.defect i k) :=
    (div_pos (by norm_num) (by positivity)).trans_le hdLower
  have hA : 0 < eventMass π A := (div_pos hp₀ (by norm_num)).trans_le hlarge
  let D := fun index : DefectIndex n =>
    (FirstPhaseFailure.defectPartition r o₁ o₂ q index : ℝ)
  let C : ℝ := TransversalPartition.partitionSum r o₁ o₂ q
  let Z : ℝ := StationaryMeanIdentities.normalizer r o₁ o₂ q w
  have hD (index : DefectIndex n) : 0 < D index := by
    dsimp only [D]
    exact_mod_cast DefectPartitionPositive.defect_partition_pos r o₁ o₂ q hq index
  obtain ⟨hZq, hzero, _, hdefect⟩ :=
    StationaryMeanIdentities.stationary_mean_identities r o₁ o₂ q 1 w hq hw
  have hZ : 0 < Z := by
    dsimp only [Z]
    exact_mod_cast hZq
  have hzeroReal : classMass π .transversal = C / Z := by
    dsimp only [π]
    rw [operational_class_mass, hzero]
    simp only [Rat.cast_div]
    rfl
  have hdefectReal : classMass π (.defect i k) = (w ⟨i, k, hik⟩ : ℝ) * D ⟨i, k, hik⟩ / Z := by
    dsimp only [π]
    rw [operational_class_mass, hdefect ⟨i, k, hik⟩]
    simp only [Rat.cast_div, Rat.cast_mul]
    rfl
  have hgoodReal (index : DefectIndex n) : C ≤ 4 * (w index : ℝ) * D index := by
    have h : (C / D index) / 4 ≤ (w index : ℝ) := by
      dsimp only [C, D]
      exact_mod_cast (hgood index).1
    have h' := (div_le_iff₀ (by norm_num : (0 : ℝ) < 4)).mp h
    have h'' := (div_le_iff₀ (hD index)).mp h'
    nlinarith
  have hmass : classMass π .transversal / 4 ≤ classMass π (.defect i k) := by
    rw [hzeroReal, hdefectReal]
    calc
      (C / Z) / 4 = (C / 4) / Z := by ring
      _ ≤ (w ⟨i, k, hik⟩ : ℝ) * D ⟨i, k, hik⟩ / Z :=
        div_le_div_of_nonneg_right (by nlinarith [hgoodReal ⟨i, k, hik⟩]) hZ.le
  have hbase : 1 / classMass π (.defect i k) ≤ 4 / classMass π .transversal := by
    apply (div_le_div_iff₀ hd hp₀).mpr
    nlinarith [hmass]
  have hevent : 1 / eventMass π A ≤ 4 / classMass π .transversal := by
    apply (div_le_div_iff₀ hA hp₀).mpr
    nlinarith [hlarge]
  have hterm (t : Fin n) (h : t ≠ i ∧ t ≠ k) :
      D ⟨i, t, Ne.symm h.1⟩ / (w ⟨t, k, h.2⟩ : ℝ) ≤ 4 * D ⟨i, k, hik⟩ := by
    have hwreal : 0 < (w ⟨t, k, h.2⟩ : ℝ) := by exact_mod_cast hw ⟨t, k, h.2⟩
    have htri : D ⟨i, t, Ne.symm h.1⟩ * D ⟨t, k, h.2⟩ ≤ C * D ⟨i, k, hik⟩ := by
      dsimp only [D, C]
      exact_mod_cast DefectPartitionTriangle.defect_partition_triangle
        n r M₁ M₂ o₁ o₂ q hfull hr h₁ h₂ hq hqone i t k (Ne.symm h.1) h.2 hik
    apply (div_le_iff₀ hwreal).mpr
    apply le_of_mul_le_mul_right _ (hD ⟨t, k, h.2⟩)
    calc
      D ⟨i, t, Ne.symm h.1⟩ * D ⟨t, k, h.2⟩ ≤ C * D ⟨i, k, hik⟩ := htri
      _ ≤ (4 * (w ⟨t, k, h.2⟩ : ℝ) * D ⟨t, k, h.2⟩) * D ⟨i, k, hik⟩ :=
        mul_le_mul_of_nonneg_right (hgoodReal ⟨t, k, h.2⟩) (hD ⟨i, k, hik⟩).le
      _ = (4 * D ⟨i, k, hik⟩ * (w ⟨t, k, h.2⟩ : ℝ)) * D ⟨t, k, h.2⟩ := by ring
  have hsum : (∑ t : Fin n, if h : t ≠ i ∧ t ≠ k then
      D ⟨i, t, Ne.symm h.1⟩ / (w ⟨t, k, h.2⟩ : ℝ) else 0) ≤
        (n : ℝ) * (4 * D ⟨i, k, hik⟩) := by
    calc
      _ ≤ ∑ _t : Fin n, 4 * D ⟨i, k, hik⟩ := by
        apply Finset.sum_le_sum
        intro t _
        split_ifs with h
        · exact hterm t h
        · exact mul_nonneg (by norm_num) (hD ⟨i, k, hik⟩).le
      _ = _ := by simp
  have hextra : (2 / (D ⟨i, k, hik⟩ * eventMass π A)) *
      (∑ t : Fin n, if h : t ≠ i ∧ t ≠ k then
        D ⟨i, t, Ne.symm h.1⟩ / (w ⟨t, k, h.2⟩ : ℝ) else 0) ≤
          32 * (n : ℝ) / classMass π .transversal := by
    calc
      _ ≤ (2 / (D ⟨i, k, hik⟩ * eventMass π A)) *
          ((n : ℝ) * (4 * D ⟨i, k, hik⟩)) :=
        mul_le_mul_of_nonneg_left hsum
          (div_nonneg (by norm_num) (mul_pos (hD ⟨i, k, hik⟩) hA).le)
      _ = 8 * (n : ℝ) / eventMass π A := by
        field_simp [(hD ⟨i, k, hik⟩).ne', hA.ne']
        ring
      _ ≤ 32 * (n : ℝ) / classMass π .transversal := by
        apply (div_le_div_iff₀ hA hp₀).mpr
        have h := mul_le_mul_of_nonneg_left hlarge
          (by positivity : (0 : ℝ) ≤ 32 * (n : ℝ))
        nlinarith
  obtain ⟨flow, hflow⟩ := DefectTransportRaw.defect_transport_raw
    n r M₁ M₂ o₁ o₂ q w hn hfull hr h₁ h₂ hq hqone hw i k hik a b hA
  refine ⟨flow, hflow.trans ?_⟩
  change (2 * (n : ℝ) ^ 2) *
    (1 / classMass π (.defect i k) + 1 / eventMass π A +
      (2 / (D ⟨i, k, hik⟩ * eventMass π A)) *
        ∑ t : Fin n, if h : t ≠ i ∧ t ≠ k then
          D ⟨i, t, Ne.symm h.1⟩ / (w ⟨t, k, h.2⟩ : ℝ) else 0) ≤ _
  calc
    _ ≤ (2 * (n : ℝ) ^ 2) *
        (4 / classMass π .transversal + 4 / classMass π .transversal +
          32 * (n : ℝ) / classMass π .transversal) :=
      mul_le_mul_of_nonneg_left (add_le_add (add_le_add hbase hevent) hextra) (by positivity)
    _ = _ := by ring
