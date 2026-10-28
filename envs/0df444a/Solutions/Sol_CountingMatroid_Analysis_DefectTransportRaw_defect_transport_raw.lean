-- Prove2me | solution 1 for CountingMatroid.Analysis.DefectTransportRaw.defect_transport_raw
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-24T16:22:34.65308+00:00
-- url     : https://prove2.me/submissions/04c664e8-ac13-488f-b0e3-dd1297cd21c0

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
import Theorems.Thm_CountingMatroid_Analysis_DefectLeafClassifier_defect_leaf_operational_weight
import Theorems.Thm_CountingMatroid_Analysis_DefectSlotBudget_defect_slot_budget
import Theorems.Thm_CountingMatroid_Analysis_DefectSlotConservation_future_form_conserved
import Theorems.Thm_CountingMatroid_Analysis_DefectSlotConservation_slot_potential_split
import Theorems.Thm_CountingMatroid_Analysis_DefectSlotConservation_slot_total_split
import Theorems.Thm_CountingMatroid_Analysis_DefectSlotRoot_root_demand_eq
import Theorems.Thm_CountingMatroid_Analysis_DefectSlotSplitSignature_slot_split_signature
import Theorems.Thm_CountingMatroid_Analysis_DefectSlotSplitSignature_slot_total_pos
import Theorems.Thm_CountingMatroid_Analysis_DefectSlotSplitSignature_split_bound_of_orthogonal_nonpositivity
import Theorems.Thm_CountingMatroid_Analysis_DefectTransportTwoPairs_defect_transport_two_pairs
import Theorems.Thm_CountingMatroid_Analysis_InitialMultipliersGood_classify_defect_iff
import Theorems.Thm_CountingMatroid_Analysis_LeafExchangeProposal_scaled_leaf_conductance_lower
import Theorems.Thm_CountingMatroid_Analysis_OmittedRankWeightPolynomial_defect_coefficient_total_pos
import Theorems.Thm_CountingMatroid_Analysis_OmittedRankWeightPolynomial_defect_completion_card
import Theorems.Thm_CountingMatroid_Analysis_OmittedRankWeightPolynomial_omitted_rank_coefficient
import Theorems.Thm_CountingMatroid_Analysis_SlotDemandRecursion_leaf_nodes_balanced
import Theorems.Thm_CountingMatroid_Analysis_SlotDemandRecursion_leaf_nodes_keep
import Theorems.Thm_CountingMatroid_Analysis_SlotDemandRecursion_leaf_potential_bound
import Theorems.Thm_CountingMatroid_Analysis_SlotLeafGeometry_leaf_holes_disjoint
import Theorems.Thm_CountingMatroid_Analysis_SlotLeafGeometry_leaf_holes_shape
import Theorems.Thm_CountingMatroid_Analysis_SlotTransportFlow_slot_transport_flow

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
namespace CountingMatroid.Analysis.DefectSlotBudget
end CountingMatroid.Analysis.DefectSlotBudget
namespace CountingMatroid.Analysis.DefectSlotFutureBound
end CountingMatroid.Analysis.DefectSlotFutureBound
namespace CountingMatroid.Analysis.DefectTransportTwoPairs
end CountingMatroid.Analysis.DefectTransportTwoPairs
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















/-- INTERNAL: The root defect total is the existing operational defect sum.
TEXLINE: main.tex:390-392 -/
theorem defect_total_empty {n : ℕ} (r : ℕ)
    (o₁ o₂ : IndependenceOracle n) (q : ℚ) (index : DefectIndex n) :
    defectTotal r o₁ o₂ q (fun _ => none) index =
      FirstPhaseFailure.defectPartition r o₁ o₂ q index := by
  classical
  simp [defectTotal, Respects, FirstPhaseFailure.defectPartition]









/-- INTERNAL: The ordinary pairs of a defect completion have exactly their
prescribed/default bit; the full pair has both bits and the empty pair neither.
TEXLINE: main.tex:383-392 -/
theorem mem_defect_completion {n : ℕ} (σ : Assignment n) (index : DefectIndex n)
    (i : Fin n) (b : Bool) :
    (i, b) ∈ defectCompletion σ index ↔
      (i ≠ index.emptyPair ∧ i ≠ index.fullPair ∧ (σ i).getD false = b) ∨
        i = index.fullPair := by
  classical
  cases b <;> simp [defectCompletion] <;> tauto







end CountingMatroid.Analysis.ConditionalDefectCoefficients

end

section


set_option autoImplicit false

/-!
The omitted-element rank-weight polynomial, expressed using the operational
paired-rank scan. Its coefficients below are identified with the operational
conditional defect totals. These identities do not assert a Hessian signature
or identify this scan with the rank of a matroid.
-/

namespace CountingMatroid.Analysis.OmittedRankWeightPolynomial

open CountingMatroid.Model CountingMatroid.Program
open CountingMatroid.Analysis.ConditionalDefectCoefficients
open scoped BigOperators
open Classical













/-- INTERNAL: Recover an accepted defect as a completion of its ordinary
pair choices, using the executable classifier's proved occupancy description.
TEXLINE: main.tex:383-392,571-625 -/
theorem defect_is_completion {n : ℕ} (state : PairedSet n) (index : DefectIndex n)
    (hkind : (classifyState state).val = .defect index.emptyPair index.fullPair) :
    defectCompletion (fun i => some (decide ((i, true) ∈ state))) index = state := by
  classical
  obtain ⟨he, hf⟩ := (InitialMultipliersGood.classify_defect_iff state index).mp hkind
  ext ⟨i, b⟩
  rw [mem_defect_completion]
  have hei := he i
  have hfi := hf i
  cases b <;> by_cases hx : (i, false) ∈ state <;>
    by_cases hy : (i, true) ∈ state <;> simp_all [index.distinct]

/-- INTERNAL: Every accepted defect has the cardinality guard required by
the omitted-element polynomial.
TEXLINE: main.tex:383-392,571-625 -/
theorem defect_card {n : ℕ} (state : PairedSet n) (index : DefectIndex n)
    (hkind : (classifyState state).val = .defect index.emptyPair index.fullPair) :
    state.card = n := by
  rw [← defect_is_completion state index hkind]
  exact defect_completion_card _ _

/-- INTERNAL: The conditional defect coefficient is exactly the sum of
coefficients of the omitted-element polynomial on the matching states.
TEXLINE: main.tex:383-392,571-625 -/
theorem defect_coefficient_sum {n : ℕ} (r : ℕ)
    (o₁ o₂ : IndependenceOracle n) (q : ℚ) (σ : Assignment n)
    (index : DefectIndex n) :
    (∑ state : PairedSet n,
      if Respects σ state ∧
          (classifyState state).val = .defect index.emptyPair index.fullPair then
        MvPolynomial.coeff (omittedExponent state) (omittedRankPolynomial r o₁ o₂ q)
      else 0) = defectTotal r o₁ o₂ q σ index := by
  classical
  unfold defectTotal
  apply Finset.sum_congr rfl
  intro state _
  by_cases h : Respects σ state ∧
      (classifyState state).val = .defect index.emptyPair index.fullPair
  · rw [if_pos h, if_pos h, omitted_rank_coefficient, if_pos (defect_card _ _ h.2)]
  · rw [if_neg h, if_neg h]





end CountingMatroid.Analysis.OmittedRankWeightPolynomial

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
The omitted-element quadratic input to the recursive slot transport. The
slot totals and old-hole matrix below follow main.tex:516-601. The numerical
split estimate and the real signature-to-orthogonal-nonpositivity implication
are proved. The explicit block matrix is assembled on the old holes and two
new coordinates. The dual-matroid omitted-label extraction is constructed;
its descendant, homogeneous degree, and exact normalization to the operational
omitted-rank polynomial are proved. The surviving omitted-label patterns
are identified exactly with the operational completion totals in all four
Hessian blocks, including the zero diagonals. The imported rank-weight
signature theorem and the proved block-form calculation give nonpositivity
on the balanced hyperplane and hence the recursive split bound.
-/

namespace CountingMatroid.Analysis.DefectSlotSplitSignature

open CountingMatroid.Model CountingMatroid.Program
open scoped BigOperators
open Classical



















/-- PAPER: main.tex:615-625
The extracted Hessian supplies the split bound at every recursion node. -/
theorem slot_split_control (n r : ℕ) (M₁ M₂ : Matroid (Fin n))
    (o₁ o₂ : IndependenceOracle n) (q : ℚ)
    (hfull : FullGround M₁ M₂) (hr : CommonRank r M₁ M₂)
    (h₁ : ExactOracle M₁ o₁) (h₂ : ExactOracle M₂ o₂)
    (hq : 0 < q) (hqone : q ≤ 1) : SlotSplitControl n r o₁ o₂ q := by
  intro B R U hBR hU hsize t ht h sₐ sᵦ u hbalance
  apply split_bound_of_orthogonal_nonpositivity R sₐ sᵦ h
    (futureMatrix r o₁ o₂ q B R U t) u
    (slot_total_pos r o₁ o₂ q hq B _ _ _) hbalance
  exact slot_split_signature n r M₁ M₂ o₁ o₂ q hfull hr h₁ h₂ hq hqone
    B R U hBR hU hsize t ht h

end CountingMatroid.Analysis.DefectSlotSplitSignature

/-! ### Run record
Newest first. History, not instruction — what this file claims is above.

* 2026-10-09 · proved · closed slot_split_signature using the proved two-active-omission completion characterization; identified all four operational Hessian blocks and impossible diagonal patterns, retaining the existing signature and split-control proofs.
* 2026-10-09 · partial, dependency blocked · proved exact dual-Tutte normalization, paired rank n, complement dual-rank identity, extraction multiplicities, and the finite-state omitted-slot coefficient formula in two new support modules; the parent uses both and still needs omission-pattern/completion equivalence. Both targeted builds and the parent elaboration passed before a concurrent RankWeightQuadraticSignature edit removed its object and failed a later permitted rebuild at List.length_eq_zero.mp.
* 2026-10-09 · partial · proved the real signature-to-orthogonal-nonpositivity step and exact block-vector expansion in two support modules; the original open theorem now has only the explicit operational block-matrix sigPos bound open. Its all-slot omitted-polynomial descendant and coefficient extraction remain unavailable; no new open declaration or Prior assumption was introduced.
-/

end

section


set_option autoImplicit false

/-!
Binary completion identities used by the balanced-hole recursion. Processing
one ordinary pair partitions each old-hole completion into its two children.
The corresponding future-slot matrix identities give conservation of the
future quadratic forms; these identities use finite sets, not a signature
assumption.
-/

namespace CountingMatroid.Analysis.DefectSlotConservation

open CountingMatroid.Model CountingMatroid.Program
open CountingMatroid.Analysis.DefectSlotSplitSignature
open scoped BigOperators











/-- PAPER: main.tex:540-543
The newly introduced holes count the same completions: the processed pair
is empty in either child. -/
theorem new_hole_total_eq {n : ℕ} (r : ℕ) (o₁ o₂ : IndependenceOracle n)
    (q : ℚ) (B R : PairedSet n) (U : Finset (Fin n)) (t : Fin n)
    (hfree : ∀ c : Bool, (t, c) ∉ R) :
    slotTotal r o₁ o₂ q B (insert (t, false) R) (U.erase t) (t, false) =
      slotTotal r o₁ o₂ q B (insert (t, true) R) (U.erase t) (t, true) := by
  classical
  simp only [slotTotal, SlotCompletion, Finset.erase_insert (hfree _)]















/-- INTERNAL: All conservation identities hold for the actual operational
weights, without matroid promises or the quadratic signature premise.
TEXLINE: main.tex:535-567,628-641 -/
theorem slot_conservation_control (n r : ℕ) (o₁ o₂ : IndependenceOracle n) (q : ℚ) :
    SlotConservationControl n r o₁ o₂ q :=
  ⟨slot_total_split r o₁ o₂ q, new_hole_total_eq r o₁ o₂ q,
    future_form_conserved r o₁ o₂ q, slot_potential_split r o₁ o₂ q⟩

end CountingMatroid.Analysis.DefectSlotConservation

end

section


set_option autoImplicit false

/-!
Demand nodes and the binary recursion from the transport proof. Splitting a
node keeps old-hole values and assigns the new hole the value that balances
its child. The recursion records all leaves in processing order.
-/

namespace CountingMatroid.Analysis.SlotDemandRecursion

open CountingMatroid.Model CountingMatroid.Program
open CountingMatroid.Analysis.DefectSlotSplitSignature
open scoped BigOperators



















/-- INTERNAL: The recursion always has at least one leaf, including when
there are no ordinary pairs to process.
TEXLINE: main.tex:708-709 -/
theorem leaf_nodes_nonempty {n : ℕ} (r : ℕ) (o₁ o₂ : IndependenceOracle n)
    (q : ℚ) (B : PairedSet n) (slots : List (Fin n)) (node : DemandNode n) :
    ∃ leaf, leaf ∈ leafNodes r o₁ o₂ q B slots node := by
  induction slots generalizing node with
  | nil => exact ⟨node, by simp [leafNodes]⟩
  | cons t slots ih =>
    obtain ⟨leaf, hleaf⟩ := ih (splitNode r o₁ o₂ q B (t :: slots).toFinset node t false)
    exact ⟨leaf, List.mem_append_left _ hleaf⟩















/-- PAPER: main.tex:528-531
The two unit root demands balance under the positive completion totals. -/
theorem two_hole_root_balanced {n : ℕ} (r : ℕ) (o₁ o₂ : IndependenceOracle n)
    (q : ℚ) (hq : 0 < q) (B : PairedSet n) (U : Finset (Fin n))
    (p d : PairedGround n) (hpd : p ≠ d) :
    CountingMatroid.Analysis.SlotDemandRecursion.Balanced r o₁ o₂ q B U (twoHoleRoot r o₁ o₂ q B U p d) := by
  classical
  let s := slotTotal r o₁ o₂ q B ({p, d} : PairedSet n) U
  have hp : 0 < s p := slot_total_pos r o₁ o₂ q hq B _ _ _
  have hd : 0 < s d := slot_total_pos r o₁ o₂ q hq B _ _ _
  change (∑ i ∈ ({p, d} : PairedSet n), s i *
    (if i = p then 1 / s p else if i = d then -1 / s d else 0)) = 0
  rw [Finset.sum_insert (by simpa using hpd), Finset.sum_singleton]
  simp only [ite_true, if_neg (Ne.symm hpd)]
  rw [mul_div_cancel₀ _ hp.ne', mul_div_cancel₀ _ hd.ne']
  norm_num



/-- INTERNAL: The recursive demand construction satisfies the whole
leaf-demand interface when the imported all-node signature split bound holds.
TEXLINE: main.tex:516-665 -/
theorem demand_recursion_control (n r : ℕ) (o₁ o₂ : IndependenceOracle n)
    (q : ℚ) (hq : 0 < q) (hsplit : SlotSplitControl n r o₁ o₂ q) :
    DemandRecursionControl n r o₁ o₂ q := by
  refine ⟨two_hole_root_balanced r o₁ o₂ q hq, ?_⟩
  intro B slots hnodup node hBR hfree hsize hbalance W hW
  refine ⟨leafNodes r o₁ o₂ q B slots node,
    leaf_nodes_nonempty r o₁ o₂ q B slots node, ?_, ?_, ?_⟩
  · exact leaf_nodes_balanced r o₁ o₂ q hq B slots hnodup node
      (fun s hs c => (hfree s hs c).2) hbalance
  · exact leaf_nodes_keep r o₁ o₂ q B slots hnodup node
      (fun s hs c => (hfree s hs c).2)
  · exact leaf_potential_bound r o₁ o₂ q hq B slots hnodup node hBR hfree hsize
      hbalance W hW hsplit

end CountingMatroid.Analysis.SlotDemandRecursion

end

section


set_option autoImplicit false

/-!
The defect/event transport bound before applying goodness or the three-pair
coefficient inequality. The n = 2 branch uses its actual one-edge current.
For n ≥ 3, the balanced demand tree is realized by the leaf stars in
SlotTransportFlow. Shared-state demands cancel by first-moment conservation,
and distinct leaves use disjoint edges, so their flow energies add.
DefectSlotRoot identifies the exact source and event demands; DefectLeafClassifier
and LeafExchangeProposal identify the operational vertex and edge capacities;
DefectSlotFutureBound and DefectSlotBudget give the final partition-sum bound.
The all-node quadratic signature input is supplied by
DefectSlotSplitSignature.slot_split_control, whose proof obligations live there.
-/
namespace CountingMatroid.Analysis.DefectTransportRaw

open CountingMatroid.Model CountingMatroid.Program
open CountingMatroid.Analysis.IdealExchangeChain
open CountingMatroid.Analysis.ObservableVarianceDecomposition
open CountingMatroid.Analysis.TransversalEventMean
open CountingMatroid.Analysis.ExchangeFlowEnergy

/-- INTERNAL: The two new holes balance their children, have opposite
values, and contribute exactly the quadratic split cost.
TEXLINE: main.tex:531-567 -/
private theorem balanced_hole_split {α : Type*} [DecidableEq α]
    (R : Finset α) (sₐ sᵦ h : α → ℝ) (u : ℝ) (hu : 0 < u)
    (hbalance : ∑ i ∈ R, (sₐ i + sᵦ i) * h i = 0) :
    let X := ∑ i ∈ R, sₐ i * h i
    let Y := ∑ i ∈ R, sᵦ i * h i
    let hₐ := -X / u
    let hᵦ := -Y / u
    X + u * hₐ = 0 ∧ Y + u * hᵦ = 0 ∧ hₐ + hᵦ = 0 ∧
      u * hₐ ^ 2 + u * hᵦ ^ 2 = 2 * X ^ 2 / u := by
  intro X Y hₐ hᵦ
  have hXY : X + Y = 0 := by
    dsimp only [X, Y]
    simpa only [add_mul, Finset.sum_add_distrib] using hbalance
  have hY : Y = -X := by linarith
  have hsum : hₐ + hᵦ = 0 := by
    dsimp only [hₐ, hᵦ]
    rw [← add_div, ← neg_add, hXY]
    simp
  refine ⟨?_, ?_, hsum, ?_⟩
  · dsimp only [hₐ]
    rw [mul_div_cancel₀ _ hu.ne']
    ring
  · dsimp only [hᵦ]
    rw [mul_div_cancel₀ _ hu.ne']
    ring
  · dsimp only [hₐ, hᵦ]
    rw [hY]
    field_simp
    ring



end CountingMatroid.Analysis.DefectTransportRaw


/-! ### Run record
Newest first. History, not instruction — what this file claims is above.

* 2026-10-09 · proved · closed the general branch through certified leaf stars, injective embedding, disjoint-edge flow summation, conserved root demand, operational leaf classification and proposal capacities, and the normalized root budget. All new helper obligations are proved; the imported all-node signature prerequisite remains with its separate owner.
* 2026-10-09 · partial · defined the operational omitted-element polynomial and proved its squarefree coefficient recovery, multiaffinity, and defect-total bridge; proved the numerical orthogonal-complement split bound, slot-completion coefficient bridge, and balanced new-hole equations with their exact cost. The parent now consumes the all-node SlotSplitControl invariant; its signature proof and recursive conservation/leaf-flow assembly remain open.
* 2026-10-09 · partial · proved and used the n = 2 no-ordinary-slot transport via the actual singleton defect/event states and a supported unit-edge current; the surviving branch has n ≥ 3. Located the recursive construction at main.tex:493-709 and its specialization at 868-898. The first split still needs the omitted-rank-weight Hessian signature, absent from the project and pinned libraries; positivity and balanced demands alone do not supply it.
-/

end
set_option autoImplicit false

/-!
The defect/event transport bound before applying goodness or the three-pair
coefficient inequality. The n = 2 branch uses its actual one-edge current.
For n ≥ 3, the balanced demand tree is realized by the leaf stars in
SlotTransportFlow. Shared-state demands cancel by first-moment conservation,
and distinct leaves use disjoint edges, so their flow energies add.
DefectSlotRoot identifies the exact source and event demands; DefectLeafClassifier
and LeafExchangeProposal identify the operational vertex and edge capacities;
DefectSlotFutureBound and DefectSlotBudget give the final partition-sum bound.
The all-node quadratic signature input is supplied by
DefectSlotSplitSignature.slot_split_control, whose proof obligations live there.
-/
namespace CountingMatroid.Analysis.DefectTransportRaw
end CountingMatroid.Analysis.DefectTransportRaw
open CountingMatroid CountingMatroid.Analysis CountingMatroid.Analysis.DefectTransportRaw

open CountingMatroid.Model CountingMatroid.Program
open CountingMatroid.Analysis.IdealExchangeChain
open CountingMatroid.Analysis.ObservableVarianceDecomposition
open CountingMatroid.Analysis.TransversalEventMean
open CountingMatroid.Analysis.ExchangeFlowEnergy

/-- INTERNAL: Specialize the paper's slot transport to the defect/event
slots and bound the off-subgraph totals by full defect partition sums.
No goodness or defect-coefficient inequality is used in this bound.
TEXLINE: main.tex:493-709,868-898 -/
theorem solution (n r : ℕ) (M₁ M₂ : Matroid (Fin n))
    (o₁ o₂ : IndependenceOracle n) (q : ℚ) (w : Multipliers n)
    (hn : 0 < n) (hfull : FullGround M₁ M₂) (hr : CommonRank r M₁ M₂)
    (h₁ : ExactOracle M₁ o₁) (h₂ : ExactOracle M₂ o₂)
    (hq : 0 < q) (hqone : q ≤ 1) (hw : ∀ index, 0 < w index)
    (i k : Fin n) (hik : i ≠ k) (a b : Bool)
    (hA : 0 < eventMass (operationalLaw r o₁ o₂ q w hq hw) (pairEvent i k a b)) :
    let π := operationalLaw r o₁ o₂ q w hq hw
    let κ := fun state next : PairedSet n =>
      exchangeProposal n hn state next * min (π state) (π next)
    let D := FirstPhaseFailure.defectPartition r o₁ o₂ q
    ∃ flow : FlowCertificate κ (conditionalMeanDemand π (.defect i k) (pairEvent i k a b)),
      flowEnergy κ flow.current ≤ (2 * (n : ℝ) ^ 2) *
        (1 / classMass π (.defect i k) + 1 / eventMass π (pairEvent i k a b) +
          (2 / ((D ⟨i, k, hik⟩ : ℝ) * eventMass π (pairEvent i k a b))) *
            ∑ t : Fin n, if h : t ≠ i ∧ t ≠ k then
              (D ⟨i, t, Ne.symm h.1⟩ : ℝ) / (w ⟨t, k, h.2⟩ : ℝ) else 0) := by
  classical
  intro π κ D
  by_cases hn2 : n = 2
  · subst n
    obtain ⟨flow, hflow⟩ := DefectTransportTwoPairs.defect_transport_two_pairs
      r o₁ o₂ q w hn hq hw i k hik a b hA
    refine ⟨flow, hflow.trans ?_⟩
    have hslots : ∀ t : Fin 2, ¬ (t ≠ i ∧ t ≠ k) := by
      intro t h
      have hi : i.val ≠ k.val := fun he => hik (Fin.ext he)
      have hti : t.val ≠ i.val := fun he => h.1 (Fin.ext he)
      have htk : t.val ≠ k.val := fun he => h.2 (Fin.ext he)
      omega
    have hsum : (∑ t : Fin 2, if h : t ≠ i ∧ t ≠ k then
        (D ⟨i, t, Ne.symm h.1⟩ : ℝ) / (w ⟨t, k, h.2⟩ : ℝ) else 0) = 0 := by
      apply Finset.sum_eq_zero
      intro t _
      rw [dif_neg (hslots t)]
    rw [hsum]
    norm_num [π]
  ·
    have hn3 : 3 ≤ n := by
      have hi : i.val ≠ k.val := fun he => hik (Fin.ext he)
      omega
    let A := pairEvent i k a b
    obtain ⟨hZ, _, _, hdef⟩ :=
      StationaryMeanIdentities.stationary_mean_identities r o₁ o₂ q 1 w hq hw
    have hDcoeff : D ⟨i, k, hik⟩ =
        ∑ state : PairedSet n,
          if ConditionalDefectCoefficients.Respects (fun _ => none) state ∧
              (classifyState state).val = .defect i k then
            MvPolynomial.coeff (OmittedRankWeightPolynomial.omittedExponent state)
              (OmittedRankWeightPolynomial.omittedRankPolynomial r o₁ o₂ q)
          else 0 := by
      rw [OmittedRankWeightPolynomial.defect_coefficient_sum
        r o₁ o₂ q (fun _ => none) ⟨i, k, hik⟩,
        ConditionalDefectCoefficients.defect_total_empty]
    have hDpos : 0 < D ⟨i, k, hik⟩ := by
      rw [hDcoeff]
      exact OmittedRankWeightPolynomial.defect_coefficient_total_pos
        r o₁ o₂ q hq (fun _ => none) ⟨i, k, hik⟩ rfl rfl
    have hd : 0 < classMass π (.defect i k) := by
      dsimp only [π]
      rw [operational_class_mass, hdef ⟨i, k, hik⟩]
      exact_mod_cast div_pos (mul_pos (hw _) hDpos) hZ
    let source := fun state : PairedSet n =>
      if (classifyState state).val = .defect i k then
        π state / classMass π (.defect i k) else 0
    let sink := fun state : PairedSet n =>
      if state ∈ A then π state / eventMass π A else 0
    have hsource : (∑ state, source state) = 1 := by
      have heq : (∑ state, source state) =
          classMass π (.defect i k) / classMass π (.defect i k) := by
        change _ = (∑ state, if (classifyState state).val = .defect i k then π state else 0) / _
        rw [Finset.sum_div]
        apply Finset.sum_congr rfl
        intro state _
        dsimp only [source]
        split_ifs <;> simp
      exact heq.trans (div_self hd.ne')
    have hsink : (∑ state, sink state) = 1 := by
      calc
        _ = ∑ state ∈ A, π state / eventMass π A := by
          dsimp only [sink]
          rw [← Finset.sum_filter]
          simp
        _ = eventMass π A / eventMass π A := by rw [← Finset.sum_div]; rfl
        _ = 1 := div_self hA.ne'
    let J := fun state next : PairedSet n =>
      source state * sink next - source next * sink state
    have hanti : ∀ state next, J state next = -J next state := by
      intro state next
      dsimp only [J]
      ring
    have hdiv : ∀ state,
        divergence J state = conditionalMeanDemand π (.defect i k) A state := by
      intro state
      simp only [divergence, J, Finset.sum_sub_distrib,
        ← Finset.mul_sum, ← Finset.sum_mul, hsource, hsink, mul_one, one_mul]
      rfl
    suffices hassembly :
        DefectSlotSplitSignature.SlotSplitControl n r o₁ o₂ q →
        DefectSlotConservation.SlotConservationControl n r o₁ o₂ q →
        SlotDemandRecursion.DemandRecursionControl n r o₁ o₂ q →
          ∃ flow : FlowCertificate κ
              (conditionalMeanDemand π (.defect i k) (pairEvent i k a b)),
            flowEnergy κ flow.current ≤ (2 * (n : ℝ) ^ 2) *
              (1 / classMass π (.defect i k) + 1 / eventMass π (pairEvent i k a b) +
                (2 / ((D ⟨i, k, hik⟩ : ℝ) * eventMass π (pairEvent i k a b))) *
                  ∑ t : Fin n, if h : t ≠ i ∧ t ≠ k then
                    (D ⟨i, t, Ne.symm h.1⟩ : ℝ) / (w ⟨t, k, h.2⟩ : ℝ) else 0) by
      have hsplit := DefectSlotSplitSignature.slot_split_control n r M₁ M₂ o₁ o₂ q
        hfull hr h₁ h₂ hq hqone
      exact hassembly hsplit
        (DefectSlotConservation.slot_conservation_control n r o₁ o₂ q)
        (SlotDemandRecursion.demand_recursion_control n r o₁ o₂ q hq hsplit)
    intro hsplitControl hconservation hrecursion
    -- INTERNAL: Realize the paper's new-hole values at every admissible
    -- node and bound their cost using the supplied all-node split control.
    have controlledSplit (B R : PairedSet n) (U : Finset (Fin n))
        (hBR : Disjoint B R)
        (hU : ∀ t ∈ U, ∀ c : Bool, (t, c) ∉ B ∧ (t, c) ∉ R)
        (hsize : B.card + R.card + U.card = n + 1)
        (t : Fin n) (ht : t ∈ U) (h : PairedGround n → ℝ) :
        let sₐ := fun hole => DefectSlotSplitSignature.slotTotal r o₁ o₂ q B
          (insert (t, false) R) (U.erase t) hole
        let sᵦ := fun hole => DefectSlotSplitSignature.slotTotal r o₁ o₂ q B
          (insert (t, true) R) (U.erase t) hole
        let u := DefectSlotSplitSignature.slotTotal r o₁ o₂ q B
          (insert (t, false) R) (U.erase t) (t, false)
        (∑ hole ∈ R, DefectSlotSplitSignature.slotTotal r o₁ o₂ q B R U hole * h hole) = 0 →
        ∃ hₐ hᵦ : ℝ,
          (∑ hole ∈ R, sₐ hole * h hole) + u * hₐ = 0 ∧
          (∑ hole ∈ R, sᵦ hole * h hole) + u * hᵦ = 0 ∧
          hₐ + hᵦ = 0 ∧
          u * hₐ ^ 2 + u * hᵦ ^ 2 ≤
            -(∑ hole ∈ R, ∑ other ∈ R,
              DefectSlotSplitSignature.futureMatrix r o₁ o₂ q B R U t hole other *
                h hole * h other) := by
      intro sₐ sᵦ u hbalance
      have hchildBalance : (∑ hole ∈ R, (sₐ hole + sᵦ hole) * h hole) = 0 := by
        calc
          _ = ∑ hole ∈ R, DefectSlotSplitSignature.slotTotal r o₁ o₂ q B R U hole *
              h hole := by
            apply Finset.sum_congr rfl
            intro hole hhole
            rw [hconservation.old_hole B R U t ht (hU t ht) hole hhole]
          _ = 0 := hbalance
      have hu : 0 < u := DefectSlotSplitSignature.slot_total_pos r o₁ o₂ q hq B _ _ _
      obtain ⟨hbalₐ, hbalᵦ, hopp, hcost⟩ := balanced_hole_split R sₐ sᵦ h u hu hchildBalance
      refine ⟨-(∑ hole ∈ R, sₐ hole * h hole) / u,
        -(∑ hole ∈ R, sᵦ hole * h hole) / u, hbalₐ, hbalᵦ, hopp, ?_⟩
      rw [hcost]
      exact hsplitControl B R U hBR hU hsize t ht h hchildBalance
    -- Instantiate the proved demand recursion at the paper's defect/event
    -- slots: B={a_k}, p=a_i, d=b_k, with every other original pair ordinary.
    let p : PairedGround n := (i, !a)
    let d : PairedGround n := (k, b)
    let B : PairedSet n := {(k, !b)}
    let U : Finset (Fin n) := (Finset.univ.erase i).erase k
    let root := SlotDemandRecursion.twoHoleRoot r o₁ o₂ q B U p d
    have hpd : p ≠ d := fun he => hik (congrArg Prod.fst he)
    have hrootBalance : CountingMatroid.Analysis.SlotDemandRecursion.Balanced r o₁ o₂ q B U root :=
      hrecursion.root_balanced B U p d hpd
    have hrootHoles : root.holes = {p, d} := rfl
    have hBR : Disjoint B root.holes := by
      rw [hrootHoles, Finset.disjoint_left]
      intro e he hf
      have heq : e = (k, !b) := Finset.mem_singleton.mp he
      subst e
      rcases Finset.mem_insert.mp hf with hp | hd
      · exact hik ((congrArg Prod.fst hp).symm)
      · have hmate : (!b) = b := congrArg Prod.snd (Finset.mem_singleton.mp hd)
        exact Bool.not_ne_self b hmate
    have hfree : ∀ t ∈ U, ∀ c : Bool, (t, c) ∉ B ∧ (t, c) ∉ root.holes := by
      intro t ht c
      obtain ⟨htk, hti, _⟩ := Finset.mem_erase.mp ht |>.imp_right Finset.mem_erase.mp
      constructor
      · intro hm
        exact htk (congrArg Prod.fst (Finset.mem_singleton.mp hm))
      · rw [hrootHoles]
        intro hm
        rcases Finset.mem_insert.mp hm with hp | hd
        · exact hti (congrArg Prod.fst hp)
        · exact htk (congrArg Prod.fst (Finset.mem_singleton.mp hd))
    have hcardU : U.card = n - 2 := by
      dsimp only [U]
      rw [Finset.card_erase_of_mem (by simp [Ne.symm hik]),
        Finset.card_erase_of_mem (Finset.mem_univ i), Finset.card_univ, Fintype.card_fin]
      omega
    have hsize : B.card + root.holes.card + U.card = n + 1 := by
      rw [hrootHoles, Finset.card_insert_of_notMem (by simpa using hpd),
        Finset.card_singleton, hcardU]
      have hBcard : B.card = 1 := Finset.card_singleton _
      simp only [Finset.card_singleton]
      omega
    let W : PairedGround n → ℝ := fun hole =>
      if hole.1 = i then (w ⟨i, k, hik⟩ : ℝ)
      else if h : hole.1 = k then 1 else (w ⟨hole.1, k, h⟩ : ℝ)
    have hW : ∀ t ∈ U.toList,
        W (t, false) = W (t, true) ∧ 0 < W (t, false) := by
      intro t _
      refine ⟨rfl, ?_⟩
      dsimp only [W]
      split_ifs
      · exact_mod_cast hw ⟨i, k, hik⟩
      · exact zero_lt_one
      · exact_mod_cast hw _
    obtain ⟨leaves, hnonempty, hleafBalance, hrootKeep, hleafPotential⟩ :=
      hrecursion.tree B U.toList U.nodup_toList root hBR
        (fun t ht c => hfree t (Finset.mem_toList.mp ht) c)
        (by simpa only [Finset.toList_toFinset] using hsize)
        (by simpa only [Finset.toList_toFinset] using hrootBalance) W hW
    let C : ℝ := (2 * (n : ℝ) ^ 2) * (StationaryMeanIdentities.normalizer r o₁ o₂ q w : ℝ)
    have hC : 0 < C := by
      have hnreal : (0 : ℝ) < n := by exact_mod_cast hn
      have hZreal : (0 : ℝ) < (StationaryMeanIdentities.normalizer r o₁ o₂ q w : ℝ) := by exact_mod_cast hZ
      exact mul_pos (mul_pos (by norm_num) (pow_pos hnreal _)) hZreal
    have hWall : ∀ hole, 0 < W hole := by
      intro hole
      dsimp only [W]
      split_ifs
      · exact_mod_cast hw ⟨i, k, hik⟩
      · exact zero_lt_one
      · exact_mod_cast hw _
    have hκsym : ∀ state next, κ state next = κ next state := by
      intro state next
      dsimp only [κ]
      rw [exchange_proposal_symmetric, min_comm]
    suffices hoperational :
        SlotTransportFlow.completionDemand r o₁ o₂ q B U root =
          conditionalMeanDemand π (.defect i k) (pairEvent i k a b) ∧
        (∀ leaf ∈ SlotDemandRecursion.leafNodes r o₁ o₂ q B U.toList root,
          ∀ x y : leaf.holes, x ≠ y →
            min (W x * DefectSlotSplitSignature.slotTotal r o₁ o₂ q B leaf.holes ∅ x)
              (W y * DefectSlotSplitSignature.slotTotal r o₁ o₂ q B leaf.holes ∅ y) ≤
                C * κ (LeafCliqueFlow.leafVertex B leaf.holes x)
                  (LeafCliqueFlow.leafVertex B leaf.holes y)) ∧
        C * (SlotDemandRecursion.nodePotential r o₁ o₂ q B U W root -
          ∑ t ∈ U, SlotDemandRecursion.nodeFuture r o₁ o₂ q B U root t / W (t, false)) ≤
          (2 * (n : ℝ) ^ 2) *
            (1 / classMass π (.defect i k) + 1 / eventMass π (pairEvent i k a b) +
              (2 / ((D ⟨i, k, hik⟩ : ℝ) * eventMass π (pairEvent i k a b))) *
                ∑ t : Fin n, if h : t ≠ i ∧ t ≠ k then
                  (D ⟨i, t, Ne.symm h.1⟩ : ℝ) / (w ⟨t, k, h.2⟩ : ℝ) else 0) by
      obtain ⟨hdemand, hcapacity, hbudget⟩ := hoperational
      obtain ⟨flow, hflow⟩ := SlotTransportFlow.slot_transport_flow r o₁ o₂ q hq B
        U.toList U.nodup_toList root ⟨p, by rw [hrootHoles]; simp⟩ hBR
        (fun t ht c => hfree t (Finset.mem_toList.mp ht) c)
        (by simpa only [Finset.toList_toFinset] using hsize)
        (by simpa only [Finset.toList_toFinset] using hrootBalance) W hW hsplitControl
        κ C hC hκsym (fun leaf _ hole _ => hWall hole) hcapacity
      let adjusted : FlowCertificate κ
          (conditionalMeanDemand π (.defect i k) (pairEvent i k a b)) :=
        { current := flow.current
          antisymmetric := flow.antisymmetric
          supported := flow.supported
          divergence_eq := fun state => (flow.divergence_eq state).trans (by
            simpa only [Finset.toList_toFinset] using congrFun hdemand state) }
      refine ⟨adjusted, hflow.trans ?_⟩
      simpa only [Finset.toList_toFinset] using hbudget
    refine ⟨DefectSlotRoot.root_demand_eq r o₁ o₂ q w hq hw i k hik a b hA, ?_⟩
    suffices hremaining :
        (∀ leaf ∈ SlotDemandRecursion.leafNodes r o₁ o₂ q B U.toList root,
          ∀ hole : leaf.holes,
            W hole * DefectSlotSplitSignature.slotTotal r o₁ o₂ q B leaf.holes ∅ hole =
              (StationaryMeanIdentities.normalizer r o₁ o₂ q w : ℝ) *
                π (LeafCliqueFlow.leafVertex B leaf.holes hole)) ∧
        C * (SlotDemandRecursion.nodePotential r o₁ o₂ q B U W root -
          ∑ t ∈ U, SlotDemandRecursion.nodeFuture r o₁ o₂ q B U root t / W (t, false)) ≤
          (2 * (n : ℝ) ^ 2) *
            (1 / classMass π (.defect i k) + 1 / eventMass π (pairEvent i k a b) +
              (2 / ((D ⟨i, k, hik⟩ : ℝ) * eventMass π (pairEvent i k a b))) *
                ∑ t : Fin n, if h : t ≠ i ∧ t ≠ k then
                  (D ⟨i, t, Ne.symm h.1⟩ : ℝ) / (w ⟨t, k, h.2⟩ : ℝ) else 0) by
      refine ⟨?_, hremaining.2⟩
      intro leaf hl x y hxy
      have hleafBR := SlotLeafGeometry.leaf_holes_disjoint r o₁ o₂ q B U.toList root hBR
        (fun t ht c => (hfree t (Finset.mem_toList.mp ht) c).1) leaf hl
      exact LeafExchangeProposal.scaled_leaf_conductance_lower n hn B leaf.holes hleafBR
        π π.p_nonneg (StationaryMeanIdentities.normalizer r o₁ o₂ q w : ℝ)
        (by exact_mod_cast hZ) _ (hremaining.1 leaf hl) x y hxy
    refine ⟨?_, DefectSlotBudget.defect_slot_budget r o₁ o₂ q w hq hw i k hik a b hA⟩
    intro leaf hl hole
    obtain ⟨choices, hshape⟩ := SlotLeafGeometry.leaf_holes_shape r o₁ o₂ q B U.toList
      U.nodup_toList root leaf hl
    simp only [Finset.toList_toFinset] at hshape
    exact DefectLeafClassifier.defect_leaf_operational_weight r o₁ o₂ q w hq hw
      i k hik a b leaf.holes choices hshape hole
