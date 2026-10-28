-- Prove2me | solution 1 for CountingMatroid.Analysis.SlotTransportFlow.slot_transport_flow
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-24T15:54:55.118708+00:00
-- url     : https://prove2.me/submissions/245eed4b-f418-4dc4-a11d-8e21f8077574

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
import Theorems.Thm_CountingMatroid_Analysis_DisjointFlowSum_disjoint_flow_sum
import Theorems.Thm_CountingMatroid_Analysis_LeafCliqueFlow_leaf_clique_flow
import Theorems.Thm_CountingMatroid_Analysis_SlotDemandPairing_leaf_pairing_conserved
import Theorems.Thm_CountingMatroid_Analysis_SlotDemandRecursion_leaf_nodes_balanced
import Theorems.Thm_CountingMatroid_Analysis_SlotDemandRecursion_leaf_nodes_keep
import Theorems.Thm_CountingMatroid_Analysis_SlotDemandRecursion_leaf_potential_bound
import Theorems.Thm_CountingMatroid_Analysis_SlotLeafGeometry_leaf_holes_disjoint
import Theorems.Thm_CountingMatroid_Analysis_SlotLeafGeometry_leaf_holes_pairwise
import Theorems.Thm_CountingMatroid_Analysis_SlotTransportFlow_terminal_demand_eq

namespace CountingMatroid.Analysis.SlotLeafGeometry
end CountingMatroid.Analysis.SlotLeafGeometry
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
section


set_option autoImplicit false

/-!
Finite-set geometry of the balanced demand tree. Different binary branches
have different displayed hole sets; admissible nodes remain admissible at
all leaves. These facts account for disjoint exchange edges at the leaves.
-/

namespace CountingMatroid.Analysis.SlotLeafGeometry

open CountingMatroid.Model CountingMatroid.Program
open CountingMatroid.Analysis.SlotDemandRecursion









/-- INTERNAL: A common disjoint fixed base can be cancelled from two
leaf unions when recovering their displayed hole sets.
TEXLINE: main.tex:681-683 -/
theorem disjoint_base_union_injective {n : ℕ} (B R S : PairedSet n)
    (hBR : Disjoint B R) (hBS : Disjoint B S) (hunion : B ∪ R = B ∪ S) : R = S := by
  rw [← Finset.union_sdiff_cancel_left hBR, hunion,
    Finset.union_sdiff_cancel_left hBS]



end CountingMatroid.Analysis.SlotLeafGeometry

end
set_option autoImplicit false

/-!
Assemble the balanced binary demand tree into an exchange-supported flow.
The exact first-moment identity cancels ordinary-hole demands, while the
finite-set leaf geometry makes the energies additive. The conductance
hypothesis is local to the terminal cliques and is kept separate from the
operational defect/event specialization.
-/

namespace CountingMatroid.Analysis.SlotTransportFlow
end CountingMatroid.Analysis.SlotTransportFlow
open CountingMatroid CountingMatroid.Analysis CountingMatroid.Analysis.SlotTransportFlow

open CountingMatroid.Model CountingMatroid.Program
open CountingMatroid.Analysis.ExchangeFlowEnergy
open CountingMatroid.Analysis.DefectSlotSplitSignature
open CountingMatroid.Analysis.SlotDemandRecursion
open CountingMatroid.Analysis.SlotDemandPairing
open CountingMatroid.Analysis.LeafCliqueFlow

/-- PAPER: main.tex:670-709
The leaf stars assemble into a flow with the original balanced demand and
energy bounded by the iterated potential estimate. The local conductance
lower bound is the only input still needed from the operational chain. -/
theorem solution {n : ℕ} (r : ℕ) (o₁ o₂ : IndependenceOracle n)
    (q : ℚ) (hq : 0 < q) (B : PairedSet n)
    (slots : List (Fin n)) (hnodup : slots.Nodup) (node : DemandNode n)
    (hne : node.holes.Nonempty) (hBR : Disjoint B node.holes)
    (hfree : ∀ t ∈ slots, ∀ c : Bool, (t, c) ∉ B ∧ (t, c) ∉ node.holes)
    (hsize : B.card + node.holes.card + slots.toFinset.card = n + 1)
    (hbalance : CountingMatroid.Analysis.SlotDemandRecursion.Balanced r o₁ o₂ q B slots.toFinset node)
    (W : PairedGround n → ℝ)
    (hWslots : ∀ t ∈ slots, W (t, false) = W (t, true) ∧ 0 < W (t, false))
    (hsplit : SlotSplitControl n r o₁ o₂ q)
    (κ : PairedSet n → PairedSet n → ℝ) (C : ℝ) (hC : 0 < C)
    (hsym : ∀ s t, κ s t = κ t s)
    (hWleaf : ∀ leaf ∈ leafNodes r o₁ o₂ q B slots node,
      ∀ i ∈ leaf.holes, 0 < W i)
    (hcap : ∀ leaf ∈ leafNodes r o₁ o₂ q B slots node,
      ∀ x y : leaf.holes, x ≠ y →
        min (W x * slotTotal r o₁ o₂ q B leaf.holes ∅ x)
          (W y * slotTotal r o₁ o₂ q B leaf.holes ∅ y) ≤
            C * κ (leafVertex B leaf.holes x) (leafVertex B leaf.holes y)) :
    ∃ flow : FlowCertificate κ (completionDemand r o₁ o₂ q B slots.toFinset node),
      flowEnergy κ flow.current ≤ C *
        (nodePotential r o₁ o₂ q B slots.toFinset W node -
          ∑ t ∈ slots.toFinset,
            nodeFuture r o₁ o₂ q B slots.toFinset node t / W (t, false)) := by
  classical
  let leaves := leafNodes r o₁ o₂ q B slots node
  have hleafBR : ∀ leaf ∈ leaves, Disjoint B leaf.holes :=
    SlotLeafGeometry.leaf_holes_disjoint r o₁ o₂ q B slots node hBR
      (fun t ht c => (hfree t ht c).1)
  have hflows : ∀ leaf ∈ leaves,
      ∃ flow : FlowCertificate κ (completionDemand r o₁ o₂ q B ∅ leaf),
        flowEnergy κ flow.current ≤ C * nodePotential r o₁ o₂ q B ∅ W leaf ∧
        (∀ s t, flow.current s t ≠ 0 → s ∪ t = B ∪ leaf.holes) := by
    intro leaf hl
    have hleafBalance := leaf_nodes_balanced r o₁ o₂ q hq B slots hnodup node
      (fun t ht c => (hfree t ht c).2) hbalance leaf hl
    obtain ⟨i, hi⟩ := hne
    have hkeep := leaf_nodes_keep r o₁ o₂ q B slots hnodup node
      (fun t ht c => (hfree t ht c).2) leaf hl i hi
    obtain ⟨flow, hcost, hunion⟩ := leaf_clique_flow r o₁ o₂ q hq B leaf
      (hleafBR leaf hl) ⟨i, hkeep.1⟩ hleafBalance W (hWleaf leaf hl) κ C hC
      hsym (hcap leaf hl)
    let adjusted : FlowCertificate κ (completionDemand r o₁ o₂ q B ∅ leaf) :=
      { current := flow.current
        antisymmetric := flow.antisymmetric
        supported := flow.supported
        divergence_eq := fun state => (flow.divergence_eq state).trans
          (terminal_demand_eq r o₁ o₂ q B leaf state) }
    exact ⟨adjusted, hcost, hunion⟩
  let J := fun leaf => if hl : leaf ∈ leaves then
    (Classical.choose (hflows leaf hl)).current else (fun _ _ => 0)
  have hanti : ∀ leaf ∈ leaves, ∀ s t, J leaf s t = -J leaf t s := by
    intro leaf hl s t
    dsimp only [J]
    rw [dif_pos hl]
    exact (Classical.choose (hflows leaf hl)).antisymmetric s t
  have hsupport : ∀ leaf ∈ leaves, ∀ s t, κ s t = 0 → J leaf s t = 0 := by
    intro leaf hl s t hz
    dsimp only [J]
    rw [dif_pos hl]
    exact (Classical.choose (hflows leaf hl)).supported s t hz
  have hdiv : ∀ leaf ∈ leaves, ∀ state,
      divergence (J leaf) state = completionDemand r o₁ o₂ q B ∅ leaf state := by
    intro leaf hl state
    dsimp only [J]
    rw [dif_pos hl]
    exact (Classical.choose (hflows leaf hl)).divergence_eq state
  have hunion : ∀ leaf ∈ leaves, ∀ s t, J leaf s t ≠ 0 → s ∪ t = B ∪ leaf.holes := by
    intro leaf hl s t hz
    dsimp only [J] at hz
    rw [dif_pos hl] at hz
    exact (Classical.choose_spec (hflows leaf hl)).2 s t hz
  have hdisjoint : leaves.Pairwise (fun left right => ∀ s t, J left s t * J right s t = 0) := by
    apply List.Pairwise.imp_of_mem (p :=
      SlotLeafGeometry.leaf_holes_pairwise r o₁ o₂ q B slots hnodup node hfree)
    intro left right hl hr hne s t
    by_cases ha : J left s t = 0
    · rw [ha, zero_mul]
    by_cases hb : J right s t = 0
    · rw [hb, mul_zero]
    have heq : B ∪ left.holes = B ∪ right.holes :=
      (hunion left hl s t ha).symm.trans (hunion right hr s t hb)
    exact False.elim (hne (SlotLeafGeometry.disjoint_base_union_injective
      B left.holes right.holes (hleafBR left hl) (hleafBR right hr) heq))
  obtain ⟨flow, _, henergy⟩ := DisjointFlowSum.disjoint_flow_sum κ J
    (fun leaf => completionDemand r o₁ o₂ q B ∅ leaf) leaves hanti hsupport hdiv hdisjoint
  have hdemands : ∀ state,
      (leaves.map (fun leaf => completionDemand r o₁ o₂ q B ∅ leaf state)).sum =
        completionDemand r o₁ o₂ q B slots.toFinset node state := by
    intro state
    exact leaf_pairing_conserved r o₁ o₂ q hq B slots hnodup node hfree hbalance _
  let assembled : FlowCertificate κ (completionDemand r o₁ o₂ q B slots.toFinset node) :=
    { current := flow.current
      antisymmetric := flow.antisymmetric
      supported := flow.supported
      divergence_eq := fun state => (flow.divergence_eq state).trans (hdemands state) }
  refine ⟨assembled, henergy.trans_le ?_⟩
  have hleafCost : ∀ leaf ∈ leaves,
      flowEnergy κ (J leaf) ≤ C * nodePotential r o₁ o₂ q B ∅ W leaf := by
    intro leaf hl
    dsimp only [J]
    rw [dif_pos hl]
    exact (Classical.choose_spec (hflows leaf hl)).1
  calc
    _ ≤ (leaves.map (fun leaf => C * nodePotential r o₁ o₂ q B ∅ W leaf)).sum :=
      List.sum_le_sum hleafCost
    _ = C * (leaves.map (nodePotential r o₁ o₂ q B ∅ W)).sum := List.sum_map_mul_left _ _ _
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (leaf_potential_bound r o₁ o₂ q hq B slots hnodup node hBR hfree hsize
        hbalance W hWslots hsplit) hC.le
