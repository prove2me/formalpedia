-- Prove2me | solution 1 for CountingMatroid.Analysis.ConditionalTransversalSplitTransport.conditional_transversal_split_transport
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-24T16:21:40.479381+00:00
-- url     : https://prove2.me/submissions/36575ce0-c85a-4d54-bb89-62fb927c4c5d

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
import Theorems.Thm_CountingMatroid_Analysis_BalancedCliqueEnergy_balanced_clique_pairing_sq_le
import Theorems.Thm_CountingMatroid_Analysis_ConditionalDefectCoefficients_subset_respects_update
import Theorems.Thm_CountingMatroid_Analysis_ConditionalDefectCoefficients_transversal_total_pos
import Theorems.Thm_CountingMatroid_Analysis_ConditionalLeafClassifier_conditional_leaf_classifier
import Theorems.Thm_CountingMatroid_Analysis_ConditionalTransversalSlots_conditional_leaf_respects
import Theorems.Thm_CountingMatroid_Analysis_ConditionalTransversalSlots_doubled_completion_iff
import Theorems.Thm_CountingMatroid_Analysis_ConditionalTransversalSlots_leaf_holes_shape
import Theorems.Thm_CountingMatroid_Analysis_ConditionalTransversalSlots_root_admissible
import Theorems.Thm_CountingMatroid_Analysis_ConditionalTransversalSlots_root_completion_sum
import Theorems.Thm_CountingMatroid_Analysis_ConditionalTransversalSplitTransport_completion_demand_pairing
import Theorems.Thm_CountingMatroid_Analysis_ConditionalTransversalSplitTransport_root_conditional_pairing
import Theorems.Thm_CountingMatroid_Analysis_DefectSlotSplitSignature_slot_split_signature
import Theorems.Thm_CountingMatroid_Analysis_DefectSlotSplitSignature_slot_total_pos
import Theorems.Thm_CountingMatroid_Analysis_DefectSlotSplitSignature_split_bound_of_orthogonal_nonpositivity
import Theorems.Thm_CountingMatroid_Analysis_ExchangeFlowEnergy_flow_energy_bound
import Theorems.Thm_CountingMatroid_Analysis_LeafExchangeProposal_scaled_leaf_conductance_lower
import Theorems.Thm_CountingMatroid_Analysis_OnePairObservablePoincare_one_pair_state_sum
import Theorems.Thm_CountingMatroid_Analysis_SlotLeafGeometry_leaf_holes_disjoint
import Theorems.Thm_CountingMatroid_Analysis_SlotTransportFlow_slot_transport_flow
import Theorems.Thm_CountingMatroid_Analysis_SlotTransportFlow_two_hole_future
import Theorems.Thm_CountingMatroid_Analysis_SlotTransportFlow_two_hole_potential

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
namespace CountingMatroid.Analysis.ConditionalLeafClassifier
end CountingMatroid.Analysis.ConditionalLeafClassifier
namespace CountingMatroid.Analysis.LeafExchangeProposal
end CountingMatroid.Analysis.LeafExchangeProposal
namespace CountingMatroid.Analysis.BalancedCliqueEnergy
end CountingMatroid.Analysis.BalancedCliqueEnergy
namespace CountingMatroid.Analysis.OnePairObservablePoincare
end CountingMatroid.Analysis.OnePairObservablePoincare
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





















/-- PAPER: main.tex:815-817
The two children at an unassigned pair partition the conditional
transversal total. -/
theorem transversal_total_split {n : ℕ} (r : ℕ)
    (o₁ o₂ : IndependenceOracle n) (q : ℚ) (σ : Assignment n)
    (k : Fin n) (hk : σ k = none) :
    transversalTotal r o₁ o₂ q (Function.update σ k (some false)) +
      transversalTotal r o₁ o₂ q (Function.update σ k (some true)) =
        transversalTotal r o₁ o₂ q σ := by
  classical
  unfold transversalTotal
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro A _
  rw [subset_respects_update σ k hk false A, subset_respects_update σ k hk true A]
  by_cases hA : SubsetRespects σ A <;> by_cases hmem : k ∈ A <;> simp [hA, hmem]











end CountingMatroid.Analysis.ConditionalDefectCoefficients

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
Demand nodes and the binary recursion from the transport proof. Splitting a
node keeps old-hole values and assigns the new hole the value that balances
its child. The recursion records all leaves in processing order.
-/

namespace CountingMatroid.Analysis.SlotDemandRecursion

open CountingMatroid.Model CountingMatroid.Program
open CountingMatroid.Analysis.DefectSlotSplitSignature
open scoped BigOperators



































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





end CountingMatroid.Analysis.SlotDemandRecursion

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

/-- INTERNAL: A certified divergence and a current-energy bound suffice
for the corresponding potential-mean estimate.
TEXLINE: main.tex:499-510 -/
theorem FlowCertificate.pairing_sq_le {α : Type*} [Fintype α]
    {κ : α → α → ℝ} {demand : α → ℝ} (flow : FlowCertificate κ demand)
    (hκ : ∀ x y, 0 ≤ κ x y) (K : ℝ) (hcost : flowEnergy κ flow.current ≤ K)
    (H : α → ℝ) : (∑ x, demand x * H x) ^ 2 ≤ K * potentialEnergy κ H := by
  simp_rw [← flow.divergence_eq]
  exact (flow_energy_bound κ flow.current hκ flow.antisymmetric flow.supported H).trans
    (mul_le_mul_of_nonneg_right hcost (potential_energy_nonneg κ hκ H))





end CountingMatroid.Analysis.ExchangeFlowEnergy

end

section


set_option autoImplicit false

/-!
The fixed labels and ordinary slots for a conditional transversal split.
The completion predicates below connect the paper's slot recursion to the
existing assignment-indexed transversal sums.
-/

namespace CountingMatroid.Analysis.ConditionalTransversalSlots

open Classical
open CountingMatroid.Model CountingMatroid.Program
open CountingMatroid.Analysis.ConditionalDefectCoefficients
open CountingMatroid.Analysis.TransversalPartition
open CountingMatroid.Analysis.DefectSlotSplitSignature
open CountingMatroid.Analysis.SlotDemandRecursion



















/-- INTERNAL: The root hole total is the corresponding conditional
transversal total, in the real scalar field used by transport.
TEXLINE: main.tex:810-817 -/
theorem root_transversal_total {n : ℕ} (r : ℕ) (o₁ o₂ : IndependenceOracle n)
    (q : ℚ) (σ : Assignment n) (k : Fin n) (hk : σ k = none) (b : Bool) :
    slotTotal r o₁ o₂ q (fixedLabels σ) {(k, false), (k, true)}
      (ordinarySlots σ k) (k, !b) =
      (transversalTotal r o₁ o₂ q (Function.update σ k (some b)) : ℝ) := by
  classical
  rw [slotTotal, root_completion_sum σ k hk b]
  unfold transversalTotal
  push_cast
  apply Finset.sum_congr rfl
  intro A _
  split_ifs <;> simp [transversalDeficiency]





/-- INTERNAL: The root future-matrix entry is the ordered-defect
correction coefficient in the conditional node inequality.
TEXLINE: main.tex:580-582,818-821 -/
theorem root_future_defect_total {n : ℕ} (r : ℕ) (o₁ o₂ : IndependenceOracle n)
    (q : ℚ) (σ : Assignment n) (k : Fin n) (hk : σ k = none)
    (t : Fin n) (ht : t ∈ ordinarySlots σ k) :
    futureMatrix r o₁ o₂ q (fixedLabels σ) {(k, false), (k, true)}
      (ordinarySlots σ k) t (k, false) (k, true) =
      (defectTotal r o₁ o₂ q σ ⟨k, t, ((mem_ordinary_slots σ k t).mp ht).2.symm⟩ : ℝ) := by
  classical
  have he : (({(k, false), (k, true)} : PairedSet n).erase (k, false)).erase
      (k, true) = ∅ := by simp
  simp only [futureMatrix, Prod.mk.injEq, Bool.false_eq_true, and_false,
    if_false, he, Finset.union_empty, defectTotal, Rat.cast_sum, apply_ite, Rat.cast_zero]
  apply Finset.sum_congr rfl
  intro state _
  simp only [doubled_completion_iff σ k hk t ht state]



end CountingMatroid.Analysis.ConditionalTransversalSlots

/-! ### Run record
Newest first. History, not instruction — what this file claims is above.

* 2026-10-09 · proved · exact root completion/total and doubled-slot defect-coefficient bridges, root admissibility, terminal hole-set shape, and assignment-respecting terminal vertices. All declarations are proved without new assumptions.
-/

end
set_option autoImplicit false

/-!
The slot-transport specialization for a conditioning-tree split. Its
finite conditional means and restricted energy are defined here. Clearing
the two positive child totals reduces the node estimate to the paper's
singleton-slot transport inequality. The one-pair branch is proved using
the balanced leaf-clique estimate. The general branch now specializes the
proved balanced-demand recursion and disjoint leaf-flow assembly, with exact
root coefficients and assignment-respecting energy. Its remaining obligation
is the operational classifier on the terminal leaf vertices, isolated in
ConditionalLeafClassifier; its general forward transversal-classifier bridge
is currently downstream.
-/

namespace CountingMatroid.Analysis.ConditionalTransversalSplitTransport
end CountingMatroid.Analysis.ConditionalTransversalSplitTransport
open CountingMatroid CountingMatroid.Analysis CountingMatroid.Analysis.ConditionalTransversalSplitTransport

open CountingMatroid.Model CountingMatroid.Program
open CountingMatroid.Analysis.ConditionalDefectCoefficients
open CountingMatroid.Analysis.TransversalPartition
open CountingMatroid.Analysis.IdealExchangeChain
open CountingMatroid.Analysis.ExchangeFlowEnergy

/-- PAPER: main.tex:455-709,815-829
Specialize slot transport to the two elements of the branching pair. Every
ordinary hole t then has multiplier w_(t,k), and v_t is c^sigma_(k,t).
This estimate precedes goodness and coefficient-score sink selection. -/
theorem solution (n r : ℕ)
    (M₁ M₂ : Matroid (Fin n)) (o₁ o₂ : IndependenceOracle n)
    (q : ℚ) (w : Multipliers n) (hn : 0 < n)
    (hfull : FullGround M₁ M₂) (hr : CommonRank r M₁ M₂)
    (h₁ : ExactOracle M₁ o₁) (h₂ : ExactOracle M₂ o₂)
    (hq : 0 < q) (hqone : q ≤ 1) (hw : ∀ index, 0 < w index)
    (σ : Assignment n) (k : Fin n) (hk : σ k = none) (H : PairedSet n → ℝ) :
    let π := operationalLaw r o₁ o₂ q w hq hw
    let κ := fun state next : PairedSet n =>
      exchangeProposal n hn state next * min (π state) (π next)
    let z : ℝ := transversalTotal r o₁ o₂ q σ
    let s₀ : ℝ := transversalTotal r o₁ o₂ q (Function.update σ k (some false))
    let s₁ : ℝ := transversalTotal r o₁ o₂ q (Function.update σ k (some true))
    let V : ℝ := ∑ t : Fin n, if h : σ t = none ∧ t ≠ k then
      (defectTotal r o₁ o₂ q σ ⟨k, t, h.2.symm⟩ : ℝ) /
        (w ⟨t, k, h.2⟩ : ℝ) else 0
    (s₀ * s₁ / z) *
      (conditionalMean r o₁ o₂ q (Function.update σ k (some false)) H -
        conditionalMean r o₁ o₂ q (Function.update σ k (some true)) H) ^ 2 ≤
      (1 + 2 / z * V) *
        ((StationaryMeanIdentities.normalizer r o₁ o₂ q w : ℝ) *
          (2 * (n : ℝ) ^ 2) * nodeEnergy κ H σ) := by
  classical
  intro π κ z s₀ s₁ V
  have hz : 0 < z := by
    dsimp only [z]
    exact_mod_cast transversal_total_pos r o₁ o₂ q hq σ
  have hs₀ : 0 < s₀ := by
    dsimp only [s₀]
    exact_mod_cast transversal_total_pos r o₁ o₂ q hq (Function.update σ k (some false))
  have hs₁ : 0 < s₁ := by
    dsimp only [s₁]
    exact_mod_cast transversal_total_pos r o₁ o₂ q hq (Function.update σ k (some true))
  have hsplit : s₀ + s₁ = z := by
    dsimp only [s₀, s₁, z]
    exact_mod_cast transversal_total_split r o₁ o₂ q σ k hk
  let B := (StationaryMeanIdentities.normalizer r o₁ o₂ q w : ℝ) *
    (2 * (n : ℝ) ^ 2) * nodeEnergy κ H σ
  suffices hraw :
      (conditionalMean r o₁ o₂ q (Function.update σ k (some false)) H -
        conditionalMean r o₁ o₂ q (Function.update σ k (some true)) H) ^ 2 ≤
          (1 / s₀ + 1 / s₁ + 2 / (s₀ * s₁) * V) * B by
    calc
      _ ≤ (s₀ * s₁ / z) * ((1 / s₀ + 1 / s₁ + 2 / (s₀ * s₁) * V) * B) :=
        mul_le_mul_of_nonneg_left hraw (div_nonneg (mul_pos hs₀ hs₁).le hz.le)
      _ = _ := by
        change _ = (1 + 2 / z * V) * B
        field_simp [hs₀.ne', hs₁.ne', hz.ne']
        rw [← hsplit]
        ring
  by_cases hn1 : n = 1
  · subst n
    have hk0 : k = 0 := Subsingleton.elim _ _
    subst k
    have hσ : σ = fun _ => none := by
      funext i
      have hi : i = 0 := Subsingleton.elim _ _
      simpa only [hi] using hk
    subst σ
    let x : PairedSet 1 := {(0, false)}
    let y : PairedSet 1 := {(0, true)}
    have hU : (Finset.univ : Finset (Finset (Fin 1))) = {∅, {0}} := by decide
    have htx : transversalState ({0} : Finset (Fin 1)) = x := by decide
    have hty : transversalState (∅ : Finset (Fin 1)) = y := by decide
    have hs₀weight : s₀ = (q ^ transversalDeficiency r o₁ o₂ {0} : ℚ) := by
      simp [s₀, transversalTotal, hU, SubsetRespects, Function.update]
    have hs₁weight : s₁ = (q ^ transversalDeficiency r o₁ o₂ ∅ : ℚ) := by
      simp [s₁, transversalTotal, hU, SubsetRespects, Function.update]
    have hm₀ : conditionalMean r o₁ o₂ q
        (Function.update (fun _ => none) 0 (some false)) H = H x := by
      have hp : (q : ℝ) ^ transversalDeficiency r o₁ o₂ {0} ≠ 0 := by
        exact_mod_cast (pow_pos hq (transversalDeficiency r o₁ o₂ {0})).ne'
      simp [conditionalMean, transversalTotal, hU, SubsetRespects,
        Function.update, hp, htx]
    have hm₁ : conditionalMean r o₁ o₂ q
        (Function.update (fun _ => none) 0 (some true)) H = H y := by
      have hp : (q : ℝ) ^ transversalDeficiency r o₁ o₂ ∅ ≠ 0 := by
        exact_mod_cast (pow_pos hq (transversalDeficiency r o₁ o₂ ∅)).ne'
      simp [conditionalMean, transversalTotal, hU, SubsetRespects,
        Function.update, hp, hty]
    let Z : ℝ := StationaryMeanIdentities.normalizer r o₁ o₂ q w
    have hZ : 0 < Z := by
      dsimp only [Z]
      exact_mod_cast (StationaryMeanIdentities.stationary_mean_identities
        r o₁ o₂ q 1 w hq hw).1
    have hclassx : (classifyState x).val = .transversal := by decide
    have hclassy : (classifyState y).val = .transversal := by decide
    have hπx : π x = s₀ / Z := by
      rw [hs₀weight]
      simp [π, Z, operationalLaw, StationaryMeanIdentities.stateWeight,
        hclassx, weightOfKind, CountingMatroid.Model.Operations.natSub,
        CountingMatroid.Analysis.BoundedRunResourceEnvelope.ratPower_value_import_support, transversalDeficiency, htx]
    have hπy : π y = s₁ / Z := by
      rw [hs₁weight]
      simp [π, Z, operationalLaw, StationaryMeanIdentities.stateWeight,
        hclassy, weightOfKind, CountingMatroid.Model.Operations.natSub,
        CountingMatroid.Analysis.BoundedRunResourceEnvelope.ratPower_value_import_support, transversalDeficiency, hty]
    have hπempty : π ∅ = 0 := by
      have hc : (classifyState (∅ : PairedSet 1)).val = .invalid := by decide
      simp [π, operationalLaw, StationaryMeanIdentities.stateWeight, hc, weightOfKind]
    have hπfull : π {(0, false), (0, true)} = 0 := by
      have hc : (classifyState ({(0, false), (0, true)} : PairedSet 1)).val =
          .invalid := by decide
      simp [π, operationalLaw, StationaryMeanIdentities.stateWeight, hc, weightOfKind]
    have hQxy : exchangeProposal 1 hn x y = (1 / 2 : ℝ) := by
      simp [exchangeProposal, exchangeState, x, y, Fintype.sum_prod_type,
        PairedGround]
      norm_num
    have hQyx : exchangeProposal 1 hn y x = (1 / 2 : ℝ) := by
      rw [exchange_proposal_symmetric]
      exact hQxy
    have hmin0 (state : PairedSet 1) : min 0 (π state) = 0 :=
      min_eq_left (π.coe_nonneg state)
    have hmin0' (state : PairedSet 1) : min (π state) 0 = 0 :=
      min_eq_right (π.coe_nonneg state)
    have henergy : nodeEnergy κ H (fun _ => none) =
        (1 / 2 : ℝ) * min (π x) (π y) * (H x - H y) ^ 2 := by
      simp only [nodeEnergy, Respects, reduceCtorEq, IsEmpty.forall_iff,
        implies_true, and_self, if_true, κ,
        OnePairObservablePoincare.one_pair_state_sum, hπempty, hπfull,
        hmin0, hmin0', mul_zero, zero_mul, sub_self, zero_pow (by decide : 2 ≠ 0),
        zero_add, add_zero]
      change (1 / 2 : ℝ) *
        (exchangeProposal 1 hn x y * min (π x) (π y) * (H x - H y) ^ 2 +
          exchangeProposal 1 hn y x * min (π y) (π x) * (H y - H x) ^ 2) = _
      rw [hQxy, hQyx, min_comm (π y) (π x)]
      ring
    have hV : V = 0 := by simp [V, Fin.sum_univ_one]
    let c := fun b : Bool => if b then s₁ else s₀
    let g := fun b : Bool => if b then (-1 : ℝ) else 1
    let F := fun b : Bool => if b then H y else H x
    have hc : ∀ b, 0 < c b := by intro b; cases b <;> assumption
    have hbalance : (∑ b, g b) = 0 := by simp [g]
    have hhub : ∃ hub : Bool, ∀ b, c b ≤ c hub := by
      rcases le_total s₀ s₁ with h | h
      · exact ⟨true, by intro b; cases b <;> simp [c, h]⟩
      · exact ⟨false, by intro b; cases b <;> simp [c, h]⟩
    obtain ⟨hub, hmax⟩ := hhub
    have hclique := BalancedCliqueEnergy.balanced_clique_pairing_sq_le
      c g F hc hbalance hub hmax
    have hpairing : (∑ b, g b * F b) = H x - H y := by
      simp [g, F]
      ring
    have hcost : (∑ b, (g b) ^ 2 / c b) = 1 / s₀ + 1 / s₁ := by
      simp [g, c, add_comm]
    have hcliqueEnergy : potentialEnergy (fun a b => min (c a) (c b)) F =
        min s₀ s₁ * (H x - H y) ^ 2 := by
      simp [potentialEnergy, c, F, min_comm]
      ring
    rw [hpairing, hcost, hcliqueEnergy] at hclique
    have hscaled : Z * min (s₀ / Z) (s₁ / Z) = min s₀ s₁ := by
      rw [mul_min_of_nonneg _ _ hZ.le, mul_div_cancel₀ _ hZ.ne',
        mul_div_cancel₀ _ hZ.ne']
    rw [hm₀, hm₁, hV]
    simp only [mul_zero, add_zero]
    dsimp only [B]
    rw [henergy, hπx, hπy]
    norm_num only [Nat.cast_one]
    change (H x - H y) ^ 2 ≤
      (1 / s₀ + 1 / s₁) * (Z * 2 *
        ((1 / 2 : ℝ) * min (s₀ / Z) (s₁ / Z) * (H x - H y) ^ 2))
    have heq : Z * 2 *
        ((1 / 2 : ℝ) * min (s₀ / Z) (s₁ / Z) * (H x - H y) ^ 2) =
          min s₀ s₁ * (H x - H y) ^ 2 := by
      calc
        _ = (Z * min (s₀ / Z) (s₁ / Z)) * (H x - H y) ^ 2 := by ring
        _ = _ := by rw [hscaled]
    rw [heq]
    exact hclique
  have hn2 : 2 ≤ n := by omega
  let base := ConditionalTransversalSlots.fixedLabels σ
  let U := ConditionalTransversalSlots.ordinarySlots σ k
  let root := SlotDemandRecursion.twoHoleRoot r o₁ o₂ q base U (k, false) (k, true)
  let W : PairedGround n → ℝ := fun hole =>
    if h : hole.1 = k then 1 else (w ⟨hole.1, k, h⟩ : ℝ)
  let Z : ℝ := StationaryMeanIdentities.normalizer r o₁ o₂ q w
  let C := Z * (2 * (n : ℝ) ^ 2)
  let restricted := fun state next : PairedSet n =>
    if Respects σ state ∧ Respects σ next then κ state next else 0
  have hZ : 0 < Z := by
    dsimp only [Z]
    exact_mod_cast (StationaryMeanIdentities.stationary_mean_identities
      r o₁ o₂ q 1 w hq hw).1
  have hC : 0 < C := by dsimp [C]; positivity
  have hrestricted : ∀ state next, 0 ≤ restricted state next := by
    intro state next
    dsimp only [restricted]
    split_ifs
    · exact mul_nonneg ((exchangeProposal n hn).coe_nonneg state next)
        (le_min (π.coe_nonneg state) (π.coe_nonneg next))
    · exact le_rfl
  have hsym : ∀ state next, restricted state next = restricted next state := by
    intro state next
    dsimp only [restricted, κ]
    simp only [and_comm, exchange_proposal_symmetric, min_comm]
  have hW : ∀ hole, 0 < W hole := by
    intro hole
    dsimp only [W]
    split_ifs
    · norm_num
    · exact_mod_cast hw _
  have hroot : root.holes = {(k, false), (k, true)} := rfl
  have hpd : (k, false) ≠ (k, true) := by simp
  obtain ⟨hBR, hfree, hsize⟩ := ConditionalTransversalSlots.root_admissible σ k hk
  change Disjoint base root.holes at hBR
  change (∀ t ∈ U, ∀ b : Bool, (t, b) ∉ base ∧ (t, b) ∉ root.holes) at hfree
  change base.card + root.holes.card + U.card = n + 1 at hsize
  have hbalance : CountingMatroid.Analysis.SlotDemandRecursion.Balanced r o₁ o₂ q base U root :=
    SlotDemandRecursion.two_hole_root_balanced r o₁ o₂ q hq base U _ _ hpd
  have hWslots : ∀ t ∈ U.toList, W (t, false) = W (t, true) ∧ 0 < W (t, false) := by
    intro t _
    exact ⟨rfl, hW _⟩
  have hsp : DefectSlotSplitSignature.slotTotal r o₁ o₂ q base root.holes U (k, false) = s₁ := by
    simpa only [Bool.not_true, base, U, root, SlotDemandRecursion.twoHoleRoot, s₁] using
      ConditionalTransversalSlots.root_transversal_total r o₁ o₂ q σ k hk true
  have hsd : DefectSlotSplitSignature.slotTotal r o₁ o₂ q base root.holes U (k, true) = s₀ := by
    simpa only [Bool.not_false, base, U, root, SlotDemandRecursion.twoHoleRoot, s₀] using
      ConditionalTransversalSlots.root_transversal_total r o₁ o₂ q σ k hk false
  have hpotential : SlotDemandRecursion.nodePotential r o₁ o₂ q base U W root =
      1 / s₀ + 1 / s₁ := by
    rw [SlotTransportFlow.two_hole_potential r o₁ o₂ q hq base U _ _ hpd W]
    simp only [W, dif_pos rfl, mul_one]
    change 1 / DefectSlotSplitSignature.slotTotal r o₁ o₂ q base root.holes U (k, false) +
      1 / DefectSlotSplitSignature.slotTotal r o₁ o₂ q base root.holes U (k, true) = _
    rw [hsp, hsd, add_comm]
  have hfuture : (∑ t ∈ U,
      SlotDemandRecursion.nodeFuture r o₁ o₂ q base U root t / W (t, false)) =
      -(2 / (s₀ * s₁) * V) := by
    have hV : V = ∑ t ∈ U, if h : σ t = none ∧ t ≠ k then
        (defectTotal r o₁ o₂ q σ ⟨k, t, h.2.symm⟩ : ℝ) /
          (w ⟨t, k, h.2⟩ : ℝ) else 0 := by
      dsimp only [V, U, ConditionalTransversalSlots.ordinarySlots]
      rw [Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro t _
      split_ifs <;> rfl
    rw [hV, Finset.mul_sum, ← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro t ht
    have hguard := (ConditionalTransversalSlots.mem_ordinary_slots σ k t).mp ht
    rw [dif_pos hguard, SlotTransportFlow.two_hole_future r o₁ o₂ q base U _ _ hpd t]
    change -(2 * DefectSlotSplitSignature.futureMatrix r o₁ o₂ q base root.holes U t
      (k, false) (k, true) /
      (DefectSlotSplitSignature.slotTotal r o₁ o₂ q base root.holes U (k, false) *
        DefectSlotSplitSignature.slotTotal r o₁ o₂ q base root.holes U (k, true))) /
      W (t, false) = _
    rw [hsp, hsd]
    have hdef := ConditionalTransversalSlots.root_future_defect_total r o₁ o₂ q σ k hk t ht
    change DefectSlotSplitSignature.futureMatrix r o₁ o₂ q base root.holes U t
      (k, false) (k, true) = _ at hdef
    rw [hdef]
    simp only [W, dif_neg hguard.2]
    ring
  suffices hcap : ∀ leaf ∈ SlotDemandRecursion.leafNodes r o₁ o₂ q base U.toList root,
      ∀ x y : leaf.holes, x ≠ y →
        min (W x * DefectSlotSplitSignature.slotTotal r o₁ o₂ q base leaf.holes ∅ x)
          (W y * DefectSlotSplitSignature.slotTotal r o₁ o₂ q base leaf.holes ∅ y) ≤
            C * restricted (LeafCliqueFlow.leafVertex base leaf.holes x)
              (LeafCliqueFlow.leafVertex base leaf.holes y) by
    have hflow := SlotTransportFlow.slot_transport_flow r o₁ o₂ q hq base
      U.toList U.nodup_toList root (by rw [hroot]; simp) hBR
      (by simpa only [Finset.mem_toList] using hfree)
      (by simpa only [Finset.toList_toFinset] using hsize)
      (by simpa only [Finset.toList_toFinset] using hbalance) W hWslots
      (DefectSlotSplitSignature.slot_split_control n r M₁ M₂ o₁ o₂ q hfull hr h₁ h₂ hq hqone)
      restricted C hC hsym (fun leaf _ i _ => hW i) hcap
    simp only [Finset.toList_toFinset] at hflow
    obtain ⟨flow, hcost⟩ := hflow
    rw [hpotential, hfuture] at hcost
    have hpairing := flow.pairing_sq_le hrestricted
      (C * (1 / s₀ + 1 / s₁ + 2 / (s₀ * s₁) * V))
      (by simpa only [sub_neg_eq_add] using hcost) H
    simp only [Finset.toList_toFinset] at hpairing
    rw [completion_demand_pairing r o₁ o₂ q base U root H,
      root_conditional_pairing r o₁ o₂ q σ k hk H, sub_sq_comm] at hpairing
    have henergy : potentialEnergy restricted H = nodeEnergy κ H σ := by
      unfold potentialEnergy nodeEnergy restricted
      simp only [ite_mul, zero_mul]
    rw [henergy] at hpairing
    dsimp only [B, C, Z]
    exact hpairing.trans_eq (by ring)
  intro leaf hleaf x y hxy
  obtain ⟨choices, hshape⟩ := ConditionalTransversalSlots.leaf_holes_shape
    r o₁ o₂ q base U.toList U.nodup_toList root leaf hleaf
  simp only [Finset.toList_toFinset, hroot] at hshape
  have hleafBR : Disjoint base leaf.holes :=
    SlotLeafGeometry.leaf_holes_disjoint r o₁ o₂ q base U.toList root hBR
      (fun t ht c => (hfree t (Finset.mem_toList.mp ht) c).1) leaf hleaf
  have hrespect (hole : leaf.holes) :
      Respects σ (LeafCliqueFlow.leafVertex base leaf.holes hole) :=
    ConditionalTransversalSlots.conditional_leaf_respects σ k hk choices leaf.holes hshape hole
  have hvertex : ∀ hole : leaf.holes,
      W hole * DefectSlotSplitSignature.slotTotal r o₁ o₂ q base leaf.holes ∅ hole =
        Z * π (LeafCliqueFlow.leafVertex base leaf.holes hole) := by
    intro hole
    suffices hkind : (classifyState (LeafCliqueFlow.leafVertex base leaf.holes hole)).val =
        if hole.val.1 = k then .transversal else .defect hole.val.1 k by
      have hterminal : DefectSlotSplitSignature.slotTotal r o₁ o₂ q base leaf.holes ∅ hole =
          ((q ^ (n - (CountingMatroid.Model.Subroutines.pairedRank r o₁ o₂
            (LeafCliqueFlow.leafVertex base leaf.holes hole)).val) : ℚ) : ℝ) := by
        simp [DefectSlotSplitSignature.slotTotal, DefectSlotSplitSignature.SlotCompletion,
          LeafCliqueFlow.leafVertex]
      have hweight : (StationaryMeanIdentities.stateWeight r o₁ o₂ q w
          (LeafCliqueFlow.leafVertex base leaf.holes hole) : ℝ) =
          W hole * DefectSlotSplitSignature.slotTotal r o₁ o₂ q base leaf.holes ∅ hole := by
        rw [hterminal]
        by_cases hi : hole.val.1 = k
        · simp [StationaryMeanIdentities.stateWeight, hkind, hi, W, weightOfKind,
            CountingMatroid.Model.Operations.natSub, CountingMatroid.Analysis.BoundedRunResourceEnvelope.ratPower_value_import_support]
        · simp [StationaryMeanIdentities.stateWeight, hkind, hi, W, weightOfKind,
            CountingMatroid.Model.Operations.natSub, CountingMatroid.Analysis.BoundedRunResourceEnvelope.ratPower_value_import_support,
            CountingMatroid.Model.Operations.multiplierRead, CountingMatroid.Model.Operations.ratMul]
      rw [← hweight]
      change _ = Z * ((StationaryMeanIdentities.stateWeight r o₁ o₂ q w
        (LeafCliqueFlow.leafVertex base leaf.holes hole) : ℝ) / Z)
      rw [mul_div_cancel₀ _ hZ.ne']
    exact ConditionalLeafClassifier.conditional_leaf_classifier σ k hk choices leaf.holes hshape hole
  have hscaled := LeafExchangeProposal.scaled_leaf_conductance_lower n hn
    base leaf.holes hleafBR π (fun state => π.coe_nonneg state) Z hZ
    (fun hole => W hole * DefectSlotSplitSignature.slotTotal r o₁ o₂ q base leaf.holes ∅ hole)
    hvertex x y hxy
  dsimp only [restricted]
  rw [if_pos ⟨hrespect x, hrespect y⟩]
  dsimp only [C, κ]
  exact hscaled.trans_eq (by ring)
