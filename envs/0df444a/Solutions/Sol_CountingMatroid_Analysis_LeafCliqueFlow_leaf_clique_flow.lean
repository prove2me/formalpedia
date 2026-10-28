-- Prove2me | solution 1 for CountingMatroid.Analysis.LeafCliqueFlow.leaf_clique_flow
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-24T15:29:26.114521+00:00
-- url     : https://prove2.me/submissions/7aa1258e-e2ee-4177-a243-3216651f34fd

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
import Theorems.Thm_CountingMatroid_Analysis_BalancedCliqueFlow_star_flow
import Theorems.Thm_CountingMatroid_Analysis_DefectSlotSplitSignature_slot_total_pos
import Theorems.Thm_CountingMatroid_Analysis_EmbeddedFlow_embed_flow

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
Embed a finite signed flow into a larger state space. Injectivity preserves
its divergence, support, and energy, including zero conductances.
-/

namespace CountingMatroid.Analysis.EmbeddedFlow

open CountingMatroid.Analysis.ExchangeFlowEnergy



/-- INTERNAL: Injectivity recovers the original current on embedded vertices.
TEXLINE: main.tex:670-683 -/
theorem embedded_current_apply {α β : Type*} [Fintype α] [DecidableEq β]
    (v : α → β) (hv : Function.Injective v) (J : α → α → ℝ) (x y : α) :
    embeddedCurrent v J (v x) (v y) = J x y := by
  classical
  simp [embeddedCurrent, hv.eq_iff, ite_and]

/-- INTERNAL: An extended current vanishes if either endpoint is outside
its embedded vertex set.
TEXLINE: main.tex:670-683 -/
theorem embedded_current_off_image {α β : Type*} [Fintype α] [DecidableEq β]
    (v : α → β) (J : α → α → ℝ) (s t : β)
    (hoff : (∀ x, v x ≠ s) ∨ (∀ y, v y ≠ t)) : embeddedCurrent v J s t = 0 := by
  rcases hoff with hs | ht
  · simp [embeddedCurrent, hs]
  · simp [embeddedCurrent, ht]











end CountingMatroid.Analysis.EmbeddedFlow

end

section


set_option autoImplicit false

/-!
Realize a terminal balanced demand node on its actual finite-set vertices.
The only conductance input is the lower bound on exchanges between those
vertices. This lemma does not assume disjointness of different leaves.
-/

namespace CountingMatroid.Analysis.LeafCliqueFlow

open CountingMatroid.Model CountingMatroid.Program
open CountingMatroid.Analysis.ExchangeFlowEnergy
open CountingMatroid.Analysis.DefectSlotSplitSignature
open CountingMatroid.Analysis.SlotDemandRecursion
open CountingMatroid.Analysis.SlotDemandPairing



/-- INTERNAL: Distinct holes give distinct leaf vertices because each
omitted label is absent from the fixed base.
TEXLINE: main.tex:670-674 -/
theorem leaf_vertex_injective {n : ℕ} (B R : PairedSet n)
    (hBR : Disjoint B R) : Function.Injective (leafVertex B R) := by
  classical
  intro x y hxy
  apply Subtype.ext
  by_contra hne
  have hxB : x.val ∉ B := fun hx => Finset.disjoint_left.mp hBR hx x.property
  have hxin : x.val ∈ leafVertex B R y :=
    Finset.mem_union_right _ (Finset.mem_erase.mpr ⟨hne, x.property⟩)
  have hxout : x.val ∉ leafVertex B R x := by
    simp [leafVertex, hxB]
  exact hxout (hxy.symm ▸ hxin)

/-- INTERNAL: The union of two distinct clique vertices recovers the
entire selected leaf set, so an exchange edge determines that set.
TEXLINE: main.tex:681-683 -/
theorem leaf_vertex_union {n : ℕ} (B R : PairedSet n) (x y : R) (hxy : x ≠ y) :
    leafVertex B R x ∪ leafVertex B R y = B ∪ R := by
  classical
  have hne : x.val ≠ y.val := fun he => hxy (Subtype.ext he)
  ext z
  simp only [leafVertex, Finset.mem_union, Finset.mem_erase]
  by_cases hz : z = x.val
  · subst z
    simp [hne, x.property]
  · tauto



end CountingMatroid.Analysis.LeafCliqueFlow

end
set_option autoImplicit false

/-!
Realize a terminal balanced demand node on its actual finite-set vertices.
The only conductance input is the lower bound on exchanges between those
vertices. This lemma does not assume disjointness of different leaves.
-/

namespace CountingMatroid.Analysis.LeafCliqueFlow
end CountingMatroid.Analysis.LeafCliqueFlow
open CountingMatroid CountingMatroid.Analysis CountingMatroid.Analysis.LeafCliqueFlow

open CountingMatroid.Model CountingMatroid.Program
open CountingMatroid.Analysis.ExchangeFlowEnergy
open CountingMatroid.Analysis.DefectSlotSplitSignature
open CountingMatroid.Analysis.SlotDemandRecursion
open CountingMatroid.Analysis.SlotDemandPairing

/-- PAPER: main.tex:670-683
A terminal balanced node has a supported flow on its actual state vertices.
A lower bound by the minimum vertex capacity gives the leaf potential
bound, with an arbitrary positive common scaling factor. -/
theorem solution {n : ℕ} (r : ℕ) (o₁ o₂ : IndependenceOracle n)
    (q : ℚ) (hq : 0 < q) (B : PairedSet n) (node : DemandNode n)
    (hBR : Disjoint B node.holes) (hne : node.holes.Nonempty)
    (hbalance : CountingMatroid.Analysis.SlotDemandRecursion.Balanced r o₁ o₂ q B ∅ node)
    (W : PairedGround n → ℝ) (hW : ∀ i ∈ node.holes, 0 < W i)
    (κ : PairedSet n → PairedSet n → ℝ) (C : ℝ) (hC : 0 < C)
    (hsym : ∀ s t, κ s t = κ t s)
    (hcap : ∀ x y : node.holes, x ≠ y →
      min (W x * slotTotal r o₁ o₂ q B node.holes ∅ x)
        (W y * slotTotal r o₁ o₂ q B node.holes ∅ y) ≤
          C * κ (leafVertex B node.holes x) (leafVertex B node.holes y)) :
    ∃ flow : FlowCertificate κ (fun state => ∑ hole : node.holes,
        if leafVertex B node.holes hole = state then
          slotTotal r o₁ o₂ q B node.holes ∅ hole * node.values hole else 0),
      flowEnergy κ flow.current ≤ C * nodePotential r o₁ o₂ q B ∅ W node ∧
      (∀ s t, flow.current s t ≠ 0 → s ∪ t = B ∪ node.holes) := by
  classical
  letI : Nonempty node.holes := ⟨⟨hne.choose, hne.choose_spec⟩⟩
  let v := leafVertex B node.holes
  let f := fun i : node.holes => slotTotal r o₁ o₂ q B node.holes ∅ i
  let c := fun i : node.holes => W i * f i
  let g := fun i : node.holes => f i * node.values i
  have hf : ∀ i, 0 < f i := fun i => slot_total_pos r o₁ o₂ q hq B _ _ i
  have hc : ∀ i, 0 < c i := fun i => mul_pos (hW i i.property) (hf i)
  have hbal : ∑ i, g i = 0 := by
    dsimp only [g, f]
    rw [Finset.sum_coe_sort node.holes (fun i =>
      slotTotal r o₁ o₂ q B node.holes ∅ i * node.values i)]
    exact hbalance
  obtain ⟨hub, _, hmax⟩ := Finset.exists_max_image (Finset.univ : Finset node.holes) c
    Finset.univ_nonempty
  obtain ⟨localFlow, _, hlocalCost⟩ := BalancedCliqueFlow.star_flow
    (fun x y => κ (v x) (v y)) (fun i => c i / C) g hub hbal
    (fun i => hsym _ _) (fun i => div_pos (hc i) hC) (by
      intro i hi
      apply (div_le_iff₀ hC).mpr
      have hh := hcap i hub hi
      rw [min_eq_left (hmax i (Finset.mem_univ i))] at hh
      simpa only [mul_comm] using hh)
  have hv : Function.Injective v := leaf_vertex_injective B node.holes hBR
  obtain ⟨flow, hcurrent, henergy⟩ := EmbeddedFlow.embed_flow v hv κ g localFlow
  refine ⟨flow, henergy.trans_le (hlocalCost.trans ?_), ?_⟩
  · have hcost : (∑ i, (g i) ^ 2 / (c i / C)) =
        C * nodePotential r o₁ o₂ q B ∅ W node := by
      dsimp only [nodePotential, g, c, f]
      rw [Finset.sum_coe_sort node.holes (fun i =>
        (slotTotal r o₁ o₂ q B node.holes ∅ i * node.values i) ^ 2 /
          (W i * slotTotal r o₁ o₂ q B node.holes ∅ i / C)), Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i hi
      have hfi := slot_total_pos r o₁ o₂ q hq B node.holes ∅ i
      field_simp [hfi.ne', (hW i hi).ne', hC.ne']
      <;> ring
    exact le_of_eq hcost
  · intro s t hnonzero
    rw [hcurrent] at hnonzero
    have hs : ∃ x, v x = s := by
      by_contra hx
      have hz := EmbeddedFlow.embedded_current_off_image v localFlow.current s t
        (Or.inl (by simpa using hx))
      exact hnonzero hz
    have ht : ∃ y, v y = t := by
      by_contra hy
      have hz := EmbeddedFlow.embedded_current_off_image v localFlow.current s t
        (Or.inr (by simpa using hy))
      exact hnonzero hz
    obtain ⟨x, rfl⟩ := hs
    obtain ⟨y, rfl⟩ := ht
    have hxy : x ≠ y := by
      rintro rfl
      have ha := localFlow.antisymmetric x x
      have hz : localFlow.current x x = 0 := by linarith
      exact hnonzero ((EmbeddedFlow.embedded_current_apply v hv localFlow.current x x).trans hz)
    exact leaf_vertex_union B node.holes x y hxy
