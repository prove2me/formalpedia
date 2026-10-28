-- Prove2me | solution 1 for CountingMatroid.Analysis.TransversalVarianceBound.transversal_variance_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-24T16:24:12.690649+00:00
-- url     : https://prove2.me/submissions/281633d1-6d09-44d8-8cbf-8c4077c19de9

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
import Theorems.Thm_CountingMatroid_Analysis_ConditionalDefectCoefficientBounds_conditional_defect_coefficient_bounds
import Theorems.Thm_CountingMatroid_Analysis_ConditionalDefectCoefficients_defect_total_pos
import Theorems.Thm_CountingMatroid_Analysis_ConditionalDefectCoefficients_transversal_total_pos
import Theorems.Thm_CountingMatroid_Analysis_ConditionalTransversalSplitTransport_conditional_transversal_split_transport
import Theorems.Thm_CountingMatroid_Analysis_ConditionalVarianceTree_adaptive_conditional_moment_bound
import Theorems.Thm_CountingMatroid_Analysis_ConditionalVarianceTree_root_conditional_moment
import Theorems.Thm_CountingMatroid_Analysis_DefectPartitionPositive_defect_partition_pos
import Theorems.Thm_CountingMatroid_Analysis_OnePairObservablePoincare_one_pair_observable_poincare
import Theorems.Thm_CountingMatroid_Analysis_TransversalVarianceBound_score_sink
import Theorems.Thm_CountingMatroid_Analysis_TransversalVarianceBound_transversal_variance_eq_of_supported
import Theorems.Thm_CountingMatroid_Analysis_TypeMassLowerBounds_good_type_mass_bounds

namespace CountingMatroid.Analysis.TransversalVarianceBound
end CountingMatroid.Analysis.TransversalVarianceBound
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
namespace CountingMatroid.Analysis.GreedyRankCorrect
end CountingMatroid.Analysis.GreedyRankCorrect
namespace Arlib
end Arlib
namespace CountingMatroid.Interface
end CountingMatroid.Interface
namespace CountingMatroid.Meta
end CountingMatroid.Meta
namespace CountingMatroid.Analysis.TransversalRankBridge
end CountingMatroid.Analysis.TransversalRankBridge
namespace CountingMatroid.Analysis.PairedRankValue
end CountingMatroid.Analysis.PairedRankValue
namespace CountingMatroid.Analysis.SignatureOrthogonalNonpositive
end CountingMatroid.Analysis.SignatureOrthogonalNonpositive
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
namespace CountingMatroid.Analysis.ConditionalDefectCoefficientBounds
end CountingMatroid.Analysis.ConditionalDefectCoefficientBounds
namespace CountingMatroid.Analysis.ConditionalOperationalCoefficients
end CountingMatroid.Analysis.ConditionalOperationalCoefficients
namespace CountingMatroid.Analysis.ConditionalOccupancyCoefficients
end CountingMatroid.Analysis.ConditionalOccupancyCoefficients
namespace CountingMatroid.Analysis.DefectPartitionTriangle
end CountingMatroid.Analysis.DefectPartitionTriangle
namespace CountingMatroid.Analysis.DefectPartitionQuadraticExtraction
end CountingMatroid.Analysis.DefectPartitionQuadraticExtraction
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

/-!
Signed exchange flows and their energy inequality. Conductances may vanish:
a flow must be zero on those pairs. These facts supply the summation-by-parts
and Cauchy--Schwarz step in the paper's transport construction; they do not
construct the recursively balanced flow or bound its energy.
-/

namespace CountingMatroid.Analysis.ExchangeFlowEnergy

open CountingMatroid.Model CountingMatroid.Program
open CountingMatroid.Analysis.ObservableVarianceDecomposition
open CountingMatroid.Analysis.TransversalEventMean
open Arlib.Probability
open scoped BigOperators













/-- INTERNAL: The energy of a potential is nonnegative for nonnegative
conductances. -/
theorem potential_energy_nonneg {α : Type*} [Fintype α]
    (κ : α → α → ℝ) (hκ : ∀ x y, 0 ≤ κ x y) (H : α → ℝ) :
    0 ≤ potentialEnergy κ H := by
  apply mul_nonneg (by norm_num)
  apply Finset.sum_nonneg
  intro x _
  apply Finset.sum_nonneg
  intro y _
  exact mul_nonneg (hκ x y) (sq_nonneg _)







end CountingMatroid.Analysis.ExchangeFlowEnergy

end

section


set_option autoImplicit false

/-!
Conditional transversal and defect totals for the operational rank weights.
The empty assignment recovers the existing partition sums. Positivity and
binary splitting below concern these finite sums; the quadratic signature
inequalities are separate mathematical obligations.
-/

namespace CountingMatroid.Analysis.ConditionalDefectCoefficients

open CountingMatroid.Model CountingMatroid.Program
open CountingMatroid.Analysis.TransversalPartition













/-- INTERNAL: The root transversal total is the partition sum already used
by the program analysis.
TEXLINE: main.tex:390-392 -/
theorem transversal_total_empty {n : ℕ} (r : ℕ)
    (o₁ o₂ : IndependenceOracle n) (q : ℚ) :
    transversalTotal r o₁ o₂ q (fun _ => none) = partitionSum r o₁ o₂ q := by
  classical
  simp [transversalTotal, SubsetRespects, partitionSum]

/-- INTERNAL: The root defect total is the existing operational defect sum.
TEXLINE: main.tex:390-392 -/
theorem defect_total_empty {n : ℕ} (r : ℕ)
    (o₁ o₂ : IndependenceOracle n) (q : ℚ) (index : DefectIndex n) :
    defectTotal r o₁ o₂ q (fun _ => none) index =
      FirstPhaseFailure.defectPartition r o₁ o₂ q index := by
  classical
  simp [defectTotal, Respects, FirstPhaseFailure.defectPartition]

















end CountingMatroid.Analysis.ConditionalDefectCoefficients

end

section


set_option autoImplicit false

/-!
Finite binary variance-tree bookkeeping for partial transversal assignments.
The moment and energy identities are independent of coefficient extraction
and the slot-flow construction. They use the concrete conditional sums.
-/

namespace CountingMatroid.Analysis.ConditionalVarianceTree

open CountingMatroid.Model
open CountingMatroid.Analysis.ConditionalDefectCoefficients
open CountingMatroid.Analysis.ConditionalTransversalSplitTransport
open CountingMatroid.Analysis.TransversalPartition
open CountingMatroid.Analysis.ExchangeFlowEnergy





































/-- INTERNAL: The empty assignment restricts no endpoints, so its energy
is the full potential energy.
TEXLINE: main.tex:834-839 -/
theorem node_energy_empty {n : ℕ} (κ : PairedSet n → PairedSet n → ℝ)
    (H : PairedSet n → ℝ) : nodeEnergy κ H (fun _ => none) = potentialEnergy κ H := by
  classical
  simp only [nodeEnergy, Respects, reduceCtorEq, forall_const, false_implies,
    implies_true, and_self, if_true, potentialEnergy]

end CountingMatroid.Analysis.ConditionalVarianceTree

end

section


set_option autoImplicit false

/-!
The paper's transversal variance estimate, isolated from the final observable
variance bookkeeping. The one-pair case is proved using the existing
constant-two Poincare estimate. The coefficient-score sink selection and
node-bound arithmetic are proved here using separate conditional-coefficient
and split-transport obligations. The adaptive variance tree, root moment
identification, and disjoint-edge charge are proved in ConditionalVarianceTree
and combined here. The parent contains no open proof; the two imported
mathematical prerequisites remain open.
-/

namespace CountingMatroid.Analysis.TransversalVarianceBound

open CountingMatroid.Model CountingMatroid.Program
open CountingMatroid.Analysis.IdealExchangeChain
open CountingMatroid.Analysis.ObservableVarianceDecomposition
open CountingMatroid.Analysis.ExchangeFlowEnergy
open CountingMatroid.Analysis.ObservableProjection
open CountingMatroid.Analysis.ConditionalDefectCoefficients
open CountingMatroid.Analysis.ConditionalTransversalSplitTransport
open CountingMatroid.Analysis.ConditionalVarianceTree
open Arlib.Probability Arlib.Probability.FinDist







/-- INTERNAL: Normalize the two-pair coefficient inequality by its positive
conditional transversal total.
TEXLINE: main.tex:790-796 -/
theorem ratio_pair (a b z : ℚ) (hz : 0 < z) (h : 4 * a * b ≤ z ^ 2) :
    (a / z) * (b / z) ≤ 1 / 4 := by
  rw [div_mul_div_comm]
  apply (div_le_iff₀ (mul_pos hz hz)).mpr
  nlinarith

/-- INTERNAL: Normalize the three-pair coefficient inequality by its
positive conditional transversal total.
TEXLINE: main.tex:790-796 -/
theorem ratio_triangle (a b c z : ℚ) (hz : 0 < z) (h : a * b ≤ z * c) :
    (a / z) * (b / z) ≤ c / z := by
  calc
    _ = a * b / z ^ 2 := by ring
    _ ≤ z * c / z ^ 2 := div_le_div_of_nonneg_right h (sq_nonneg z)
    _ = c / z := by field_simp



end CountingMatroid.Analysis.TransversalVarianceBound

/-! ### Run record
Newest first. History, not instruction — what this file claims is above.

* 2026-10-09 · parent-closed · proved adaptive variance telescoping, fully assigned leaves, restricted-energy splitting and the operational root bridge; combined them with the node estimate to remove the parent hole. Two substantial imported coefficient/transport obligations remain open for live handoff.
* 2026-10-09 · decomposed · defined operational conditional totals and proved positivity and splitting; proved score-sink selection and all node-bound arithmetic, using separate conditional coefficient and split-transport children. The parent hole is now adaptive-tree variance telescoping and disjoint-depth energy charging.
* recovery · partial · proved the supported-law variance bridge and the n=1 branch; exposed the n≥2 centered moment after positive-mass cancellation. Conditional coefficient bounds (397-449) and slot transport (455-709) are missing local lemmas; no new open helper was introduced.
-/

end
set_option autoImplicit false

/-!
The paper's transversal variance estimate, isolated from the final observable
variance bookkeeping. The one-pair case is proved using the existing
constant-two Poincare estimate. The coefficient-score sink selection and
node-bound arithmetic are proved here using separate conditional-coefficient
and split-transport obligations. The adaptive variance tree, root moment
identification, and disjoint-edge charge are proved in ConditionalVarianceTree
and combined here. The parent contains no open proof; the two imported
mathematical prerequisites remain open.
-/

namespace CountingMatroid.Analysis.TransversalVarianceBound
end CountingMatroid.Analysis.TransversalVarianceBound
open CountingMatroid CountingMatroid.Analysis CountingMatroid.Analysis.TransversalVarianceBound

open CountingMatroid.Model CountingMatroid.Program
open CountingMatroid.Analysis.IdealExchangeChain
open CountingMatroid.Analysis.ObservableVarianceDecomposition
open CountingMatroid.Analysis.ExchangeFlowEnergy
open CountingMatroid.Analysis.ObservableProjection
open CountingMatroid.Analysis.ConditionalDefectCoefficients
open CountingMatroid.Analysis.ConditionalTransversalSplitTransport
open CountingMatroid.Analysis.ConditionalVarianceTree
open Arlib.Probability Arlib.Probability.FinDist

/-- PAPER: main.tex:777-839
The transversal conditional variance is bounded by the paper's constant
`n(1+8n)` times `D(H)/c₀`, expressed with normalized ideal conductances. -/
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
    (H : PairedSet n → ℝ) :
    let π := operationalLaw r o₁ o₂ q w hq hw
    let κ := fun state next : PairedSet n =>
      exchangeProposal n hn state next * min (π state) (π next)
    transversalVariance π H ≤ (n : ℝ) * (1 + 8 * (n : ℝ)) *
      (2 * (n : ℝ) ^ 2 * potentialEnergy κ H / classMass π .transversal) := by
  classical
  intro π κ
  by_cases hn1 : n = 1
  · subst n
    have hsupport : ∀ state, (classifyState state).val ≠ .transversal →
        π state = 0 := by
      intro state ht
      cases hk : (classifyState state).val with
      | transversal => exact False.elim (ht hk)
      | invalid =>
          simp [π, operationalLaw, StationaryMeanIdentities.stateWeight,
            hk, weightOfKind]
      | defect i k =>
          have hik : i = k := Subsingleton.elim _ _
          simp [π, operationalLaw, StationaryMeanIdentities.stateWeight,
            hk, weightOfKind, hik]
    obtain ⟨hmass, hvariance⟩ := transversal_variance_eq_of_supported π H hsupport
    have hzero : π ∅ = 0 := hsupport ∅ (by decide)
    have hfullstate : π {(0, false), (0, true)} = 0 :=
      hsupport _ (by decide)
    have hbase : Var π (observableProjection π H) ≤ 2 * potentialEnergy κ H :=
      OnePairObservablePoincare.one_pair_observable_poincare π hzero hfullstate H
    have henergy : 0 ≤ potentialEnergy κ H := by
      apply potential_energy_nonneg
      intro state next
      exact mul_nonneg ((exchangeProposal 1 hn).coe_nonneg state next)
        (le_min (π.coe_nonneg state) (π.coe_nonneg next))
    rw [hvariance, hmass]
    norm_num
    nlinarith [hbase]
  have htwo : 2 ≤ n := by omega
  have hp : 1 / (5 * (n : ℝ) ^ 2) ≤ classMass π .transversal := by
    dsimp only [π]
    rw [operational_class_mass]
    have hmass := (TypeMassLowerBounds.good_type_mass_bounds
      r o₁ o₂ q w hn hq hgood).2.1
    have hcast := (Rat.cast_le (K := ℝ)).mpr hmass
    simpa only [Rat.cast_div, Rat.cast_one, Rat.cast_mul, Rat.cast_ofNat,
      Rat.cast_pow, Rat.cast_natCast] using hcast
  have hnreal : (0 : ℝ) < n := by exact_mod_cast hn
  have hp₀ : 0 < classMass π .transversal :=
    (div_pos (by norm_num) (by positivity)).trans_le hp
  rw [← mul_div_assoc]
  apply (le_div_iff₀ hp₀).mpr
  rw [transversalVariance, div_mul_cancel₀ _ hp₀.ne']
  let Z : ℝ := StationaryMeanIdentities.normalizer r o₁ o₂ q w
  let NodeBound : Prop := ∀ σ : Assignment n, (∃ i, σ i = none) →
    ∃ k, σ k = none ∧
      ((transversalTotal r o₁ o₂ q (Function.update σ k (some false)) : ℝ) *
        (transversalTotal r o₁ o₂ q (Function.update σ k (some true)) : ℝ) /
        (transversalTotal r o₁ o₂ q σ : ℝ)) *
      (conditionalMean r o₁ o₂ q (Function.update σ k (some false)) H -
        conditionalMean r o₁ o₂ q (Function.update σ k (some true)) H) ^ 2 ≤
          (1 + 8 * (n : ℝ)) * (Z * (2 * (n : ℝ) ^ 2) * nodeEnergy κ H σ)
  have hnode : NodeBound := by
    intro σ hremaining
    let s := Finset.univ.filter (fun i => σ i = none)
    have hmem (i : Fin n) : i ∈ s ↔ σ i = none := by simp [s]
    have hs : s.Nonempty := by
      obtain ⟨i, hi⟩ := hremaining
      exact ⟨i, (hmem i).mpr hi⟩
    let z := transversalTotal r o₁ o₂ q σ
    let C := TransversalPartition.partitionSum r o₁ o₂ q
    let c := defectTotal r o₁ o₂ q σ
    let D := FirstPhaseFailure.defectPartition r o₁ o₂ q
    have hz : 0 < z := transversal_total_pos r o₁ o₂ q hq σ
    have hC : 0 < C := by
      dsimp only [C]
      rw [← transversal_total_empty r o₁ o₂ q]
      exact transversal_total_pos r o₁ o₂ q hq _
    have hc (index : DefectIndex n) (he : σ index.emptyPair = none)
        (hf : σ index.fullPair = none) : 0 < c index :=
      defect_total_pos r o₁ o₂ q hq σ index he hf
    have hD (index : DefectIndex n) : 0 < D index :=
      DefectPartitionPositive.defect_partition_pos r o₁ o₂ q hq index
    obtain ⟨hcp, hct⟩ :=
      ConditionalDefectCoefficientBounds.conditional_defect_coefficient_bounds
        n r M₁ M₂ o₁ o₂ q hfull hr h₁ h₂ hq hqone σ
    obtain ⟨hDp, hDt⟩ :=
      ConditionalDefectCoefficientBounds.conditional_defect_coefficient_bounds
        n r M₁ M₂ o₁ o₂ q hfull hr h₁ h₂ hq hqone (fun _ => none)
    simp only [defect_total_empty, transversal_total_empty] at hDp hDt
    let a := fun i j : Fin n => if hij : i ≠ j then
      (c ⟨i, j, hij⟩ / z) * (D ⟨j, i, hij.symm⟩ / C) else 0
    have hscorePair : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → a i j * a j i ≤ 1 / 16 := by
      intro i hi j hj hij
      have hiσ := (hmem i).mp hi
      have hjσ := (hmem j).mp hj
      have hpcond := ratio_pair _ _ _ hz (hcp i j hij hiσ hjσ)
      have hpglobal := ratio_pair _ _ _ hC (hDp j i hij.symm True.intro True.intro)
      dsimp only [a]
      rw [dif_pos hij, dif_pos hij.symm]
      calc
        _ = ((c ⟨i, j, hij⟩ / z) * (c ⟨j, i, hij.symm⟩ / z)) *
          ((D ⟨j, i, hij.symm⟩ / C) * (D ⟨i, j, hij⟩ / C)) := by ring
        _ ≤ (1 / 4 : ℚ) * (1 / 4) :=
          mul_le_mul hpcond hpglobal
            (mul_nonneg (div_pos (hD _) hC).le (div_pos (hD _) hC).le)
            (by norm_num)
        _ = 1 / 16 := by norm_num
    have hscoreTriangle : ∀ i ∈ s, ∀ j ∈ s, ∀ k ∈ s,
        i ≠ j → j ≠ k → i ≠ k → a i j * a j k ≤ a i k := by
      intro i hi j hj k hk hij hjk hik
      have hiσ := (hmem i).mp hi
      have hjσ := (hmem j).mp hj
      have hkσ := (hmem k).mp hk
      have htcond := ratio_triangle _ _ _ _ hz (hct i j k hij hjk hik hiσ hjσ hkσ)
      have htglobal := ratio_triangle _ _ _ _ hC (hDt k j i hjk.symm hij.symm hik.symm True.intro True.intro True.intro)
      dsimp only [a]
      rw [dif_pos hij, dif_pos hjk, dif_pos hik]
      calc
        _ = ((c ⟨i, j, hij⟩ / z) * (c ⟨j, k, hjk⟩ / z)) *
          ((D ⟨k, j, hjk.symm⟩ / C) * (D ⟨j, i, hij.symm⟩ / C)) := by ring
        _ ≤ (c ⟨i, k, hik⟩ / z) * (D ⟨k, i, hik.symm⟩ / C) :=
          mul_le_mul htcond htglobal
            (mul_nonneg (div_pos (hD _) hC).le (div_pos (hD _) hC).le)
            (div_pos (hc _ hiσ hkσ) hz).le
        _ = _ := rfl
    obtain ⟨k, hk, hsink⟩ := score_sink a s hs hscorePair hscoreTriangle
    have hkσ := (hmem k).mp hk
    refine ⟨k, hkσ, ?_⟩
    have hterm (t : Fin n) (h : σ t = none ∧ t ≠ k) :
        (c ⟨k, t, h.2.symm⟩ : ℝ) / (w ⟨t, k, h.2⟩ : ℝ) ≤ 4 * (z : ℝ) := by
      have hscore := hsink t ((hmem t).mpr h.1) h.2.symm
      dsimp only [a] at hscore
      rw [dif_pos h.2.symm] at hscore
      have hprod : c ⟨k, t, h.2.symm⟩ * D ⟨t, k, h.2⟩ ≤ z * C := by
        have h := (div_le_iff₀ (mul_pos hz hC)).mp
          (by simpa only [div_mul_div_comm, one_mul] using hscore)
        simpa using h
      have hgood' : C ≤ 4 * w ⟨t, k, h.2⟩ * D ⟨t, k, h.2⟩ := by
        have hscaled := (div_le_iff₀ (by norm_num : (0 : ℚ) < 4)).mp (hgood ⟨t, k, h.2⟩).1
        have h' := (div_le_iff₀ (hD ⟨t, k, h.2⟩)).mp hscaled
        nlinarith
      have hbound : c ⟨k, t, h.2.symm⟩ / w ⟨t, k, h.2⟩ ≤ 4 * z := by
        apply (div_le_iff₀ (hw _)).mpr
        apply le_of_mul_le_mul_right _ (hD ⟨t, k, h.2⟩)
        calc
          _ ≤ z * C := hprod
          _ ≤ z * (4 * w ⟨t, k, h.2⟩ * D ⟨t, k, h.2⟩) :=
            mul_le_mul_of_nonneg_left hgood' hz.le
          _ = _ := by ring
      exact_mod_cast hbound
    have hsum : (∑ t : Fin n, if h : σ t = none ∧ t ≠ k then
        (c ⟨k, t, h.2.symm⟩ : ℝ) / (w ⟨t, k, h.2⟩ : ℝ) else 0) ≤
          (n : ℝ) * (4 * (z : ℝ)) := by
      calc
        _ ≤ ∑ _t : Fin n, 4 * (z : ℝ) := by
          apply Finset.sum_le_sum
          intro t _
          split_ifs with h
          · exact hterm t h
          · exact mul_nonneg (by norm_num) (by exact_mod_cast hz.le)
        _ = _ := by simp
    have hκ : ∀ state next, 0 ≤ κ state next := fun state next =>
      mul_nonneg ((exchangeProposal n hn).coe_nonneg state next)
        (le_min (π.coe_nonneg state) (π.coe_nonneg next))
    have hEσ : 0 ≤ nodeEnergy κ H σ := by
      apply mul_nonneg (by norm_num)
      apply Finset.sum_nonneg
      intro state _
      apply Finset.sum_nonneg
      intro next _
      split_ifs
      · exact mul_nonneg (hκ _ _) (sq_nonneg _)
      · exact le_rfl
    have hZ : 0 < Z := by
      dsimp only [Z]
      exact_mod_cast (StationaryMeanIdentities.stationary_mean_identities
        r o₁ o₂ q 1 w hq hw).1
    have hzreal : (0 : ℝ) < z := by exact_mod_cast hz
    have hcoef : 1 + 2 / (z : ℝ) *
        (∑ t : Fin n, if h : σ t = none ∧ t ≠ k then
          (c ⟨k, t, h.2.symm⟩ : ℝ) / (w ⟨t, k, h.2⟩ : ℝ) else 0) ≤
            1 + 8 * (n : ℝ) := by
      have h := mul_le_mul_of_nonneg_left hsum
        (show (0 : ℝ) ≤ 2 / (z : ℝ) from div_nonneg (by norm_num) hzreal.le)
      have hcancel : 2 / (z : ℝ) * ((n : ℝ) * (4 * (z : ℝ))) = 8 * (n : ℝ) := by
        field_simp
        norm_num
      rw [hcancel] at h
      linarith
    have htransport := conditional_transversal_split_transport n r M₁ M₂ o₁ o₂
      q w hn hfull hr h₁ h₂ hq hqone hw σ k hkσ H
    exact htransport.trans (mul_le_mul_of_nonneg_right hcoef
      (mul_nonneg (mul_nonneg hZ.le (by positivity)) hEσ))
  have hκ : ∀ state next, 0 ≤ κ state next := fun state next =>
    mul_nonneg ((exchangeProposal n hn).coe_nonneg state next)
      (le_min (π.coe_nonneg state) (π.coe_nonneg next))
  have hZ : 0 < Z := by
    dsimp only [Z]
    exact_mod_cast (StationaryMeanIdentities.stationary_mean_identities
      r o₁ o₂ q 1 w hq hw).1
  let K := (1 + 8 * (n : ℝ)) * (Z * (2 * (n : ℝ) ^ 2))
  have hK : 0 ≤ K := by dsimp only [K]; positivity
  have ht := adaptive_conditional_moment_bound r o₁ o₂ q hq κ hκ H K hK
    (by
      intro σ hremaining
      obtain ⟨k, hk, hb⟩ := hnode σ hremaining
      refine ⟨k, hk, ?_⟩
      simpa only [K, mul_assoc] using hb) (fun _ => none)
  have hcount : (unassigned (n := n) (fun _ => none)).card = n := by simp [unassigned]
  rw [root_conditional_moment r o₁ o₂ q w hq hw H, node_energy_empty, hcount] at ht
  apply le_of_mul_le_mul_left _ hZ
  calc
    _ ≤ (n : ℝ) * K * potentialEnergy κ H := ht
    _ = _ := by dsimp only [K]; ring
