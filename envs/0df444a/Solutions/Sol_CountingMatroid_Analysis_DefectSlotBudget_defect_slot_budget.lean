-- Prove2me | solution 1 for CountingMatroid.Analysis.DefectSlotBudget.defect_slot_budget
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-24T16:09:37.651992+00:00
-- url     : https://prove2.me/submissions/aa602444-9cd9-4c4d-aa0c-06175e2eca12

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
import Theorems.Thm_CountingMatroid_Analysis_DefectSlotFutureBound_root_future_le_defect_partition
import Theorems.Thm_CountingMatroid_Analysis_DefectSlotRoot_defect_root_shape
import Theorems.Thm_CountingMatroid_Analysis_DefectSlotRoot_event_slot_total
import Theorems.Thm_CountingMatroid_Analysis_DefectSlotSplitSignature_slot_total_pos
import Theorems.Thm_CountingMatroid_Analysis_SlotTransportFlow_two_hole_future
import Theorems.Thm_CountingMatroid_Analysis_SlotTransportFlow_two_hole_potential

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
Identify the root completion classes in the defect/event transport with
the executable classifier and prescribed transversal event. All totals
use the actual operational rank weights.
-/

namespace CountingMatroid.Analysis.DefectSlotRoot

open CountingMatroid.Model CountingMatroid.Program
open Classical
open CountingMatroid.Analysis.DefectSlotSplitSignature
open CountingMatroid.Analysis.SlotDemandRecursion
open CountingMatroid.Analysis.SlotDemandPairing
open CountingMatroid.Analysis.SlotTransportFlow
open CountingMatroid.Analysis.TransversalEventMean
open CountingMatroid.Analysis.ConditionalDefectCoefficients
open CountingMatroid.Analysis.ExchangeFlowEnergy
open CountingMatroid.Analysis.IdealExchangeChain
open CountingMatroid.Analysis.ObservableVarianceDecomposition



/-- INTERNAL: The fixed full-pair label and the other root hole together
are the two labels of that pair.
TEXLINE: main.tex:875-885 -/
theorem defect_root_base {n : ℕ} (i k : Fin n) (hik : i ≠ k) (a b : Bool) :
    ({(k, !b)} : PairedSet n) ∪ ({(i, !a), (k, b)} : PairedSet n).erase (i, !a) =
      {(k, false), (k, true)} := by
  classical
  have hp : (i, !a) ≠ (k, b) := fun he => hik (congrArg Prod.fst he)
  rw [Finset.erase_insert (by simpa using hp)]
  cases b <;> simp [Finset.pair_comm]

/-- PAPER: main.tex:875-892
The source root hole has exactly all states of the ordered defect fiber. -/
theorem source_completion_iff {n : ℕ} (i k : Fin n) (hik : i ≠ k)
    (a b : Bool) (state : PairedSet n) :
    SlotCompletion {(k, !b)} {(i, !a), (k, b)}
      ((Finset.univ.erase i).erase k) (i, !a) state ↔
        (classifyState state).val = .defect i k := by
  unfold SlotCompletion
  rw [defect_root_base i k hik a b]
  exact defect_root_shape ⟨i, k, hik⟩ state







/-- PAPER: main.tex:892-895
The source root total is the complete ordered defect partition sum. -/
theorem source_slot_total {n : ℕ} (r : ℕ) (o₁ o₂ : IndependenceOracle n)
    (q : ℚ) (i k : Fin n) (hik : i ≠ k) (a b : Bool) :
    slotTotal r o₁ o₂ q {(k, !b)} {(i, !a), (k, b)}
      ((Finset.univ.erase i).erase k) (i, !a) =
        (FirstPhaseFailure.defectPartition r o₁ o₂ q ⟨i, k, hik⟩ : ℝ) := by
  classical
  simp only [slotTotal, source_completion_iff i k hik a b,
    FirstPhaseFailure.defectPartition, Rat.cast_sum, apply_ite, Rat.cast_zero]







end CountingMatroid.Analysis.DefectSlotRoot

end
set_option autoImplicit false

/-!
Normalize the iterated two-hole potential estimate into the defect/event
mass bound. Root future entries are bounded by full defect partitions.
-/

namespace CountingMatroid.Analysis.DefectSlotBudget
end CountingMatroid.Analysis.DefectSlotBudget
open CountingMatroid CountingMatroid.Analysis CountingMatroid.Analysis.DefectSlotBudget

open CountingMatroid.Model CountingMatroid.Program
open CountingMatroid.Analysis.IdealExchangeChain
open CountingMatroid.Analysis.ObservableVarianceDecomposition
open CountingMatroid.Analysis.TransversalEventMean
open CountingMatroid.Analysis.DefectSlotSplitSignature
open CountingMatroid.Analysis.SlotDemandRecursion

/-- INTERNAL: The exact mass and partition normalization of the paper's
root potential bound, before any goodness assumption is imposed.
TEXLINE: main.tex:652-665,875-898 -/
theorem solution {n : ℕ} (r : ℕ) (o₁ o₂ : IndependenceOracle n)
    (q : ℚ) (w : Multipliers n) (hq : 0 < q) (hw : ∀ index, 0 < w index)
    (i k : Fin n) (hik : i ≠ k) (a b : Bool)
    (hA : 0 < eventMass (operationalLaw r o₁ o₂ q w hq hw) (pairEvent i k a b)) :
    let π := operationalLaw r o₁ o₂ q w hq hw
    let B : PairedSet n := {(k, !b)}
    let U : Finset (Fin n) := (Finset.univ.erase i).erase k
    let p : PairedGround n := (i, !a)
    let d : PairedGround n := (k, b)
    let W : PairedGround n → ℝ := fun hole =>
      if hole.1 = i then (w ⟨i, k, hik⟩ : ℝ)
      else if h : hole.1 = k then 1 else (w ⟨hole.1, k, h⟩ : ℝ)
    let root := twoHoleRoot r o₁ o₂ q B U p d
    let D := FirstPhaseFailure.defectPartition r o₁ o₂ q
    let C : ℝ := (2 * (n : ℝ) ^ 2) * (StationaryMeanIdentities.normalizer r o₁ o₂ q w : ℝ)
    C * (nodePotential r o₁ o₂ q B U W root -
      ∑ t ∈ U, nodeFuture r o₁ o₂ q B U root t / W (t, false)) ≤
        (2 * (n : ℝ) ^ 2) *
          (1 / classMass π (.defect i k) + 1 / eventMass π (pairEvent i k a b) +
            (2 / ((D ⟨i, k, hik⟩ : ℝ) * eventMass π (pairEvent i k a b))) *
              ∑ t : Fin n, if h : t ≠ i ∧ t ≠ k then
                (D ⟨i, t, Ne.symm h.1⟩ : ℝ) / (w ⟨t, k, h.2⟩ : ℝ) else 0) := by
  classical
  intro π B U p d W root D C
  let Z : ℝ := (StationaryMeanIdentities.normalizer r o₁ o₂ q w : ℝ)
  let Dik : ℝ := (D ⟨i, k, hik⟩ : ℝ)
  let E := eventMass π (pairEvent i k a b)
  let S := ∑ t : Fin n, if h : t ≠ i ∧ t ≠ k then
    (D ⟨i, t, Ne.symm h.1⟩ : ℝ) / (w ⟨t, k, h.2⟩ : ℝ) else 0
  let coefficient := 2 / (Dik * Z * E)
  obtain ⟨hZq, _, _, hdef⟩ :=
    StationaryMeanIdentities.stationary_mean_identities r o₁ o₂ q 1 w hq hw
  have hZ : 0 < Z := by dsimp only [Z]; exact_mod_cast hZq
  have hDik : 0 < Dik := by
    dsimp only [Dik, D]
    rw [← DefectSlotRoot.source_slot_total r o₁ o₂ q i k hik a b]
    exact slot_total_pos r o₁ o₂ q hq _ _ _ _
  have hE : 0 < E := hA
  have hwi : (0 : ℝ) < (w ⟨i, k, hik⟩ : ℝ) := by exact_mod_cast hw ⟨i, k, hik⟩
  have hpd : p ≠ d := fun he => hik (congrArg Prod.fst he)
  have hsp : slotTotal r o₁ o₂ q B {p, d} U p = Dik :=
    DefectSlotRoot.source_slot_total r o₁ o₂ q i k hik a b
  have hsd : slotTotal r o₁ o₂ q B {p, d} U d = Z * E :=
    DefectSlotRoot.event_slot_total r o₁ o₂ q w hq hw i k hik a b
  have hWp : W p = (w ⟨i, k, hik⟩ : ℝ) := by simp [W, p]
  have hWd : W d = 1 := by simp [W, d, Ne.symm hik]
  have hmass : classMass π (.defect i k) = (w ⟨i, k, hik⟩ : ℝ) * Dik / Z := by
    dsimp only [π]
    rw [operational_class_mass, hdef ⟨i, k, hik⟩]
    simp only [Rat.cast_div, Rat.cast_mul]
    rfl
  have hrootCost : C * nodePotential r o₁ o₂ q B U W root =
      (2 * (n : ℝ) ^ 2) * (1 / classMass π (.defect i k) + 1 / E) := by
    rw [SlotTransportFlow.two_hole_potential r o₁ o₂ q hq B U p d hpd W,
      hsp, hsd, hWp, hWd, hmass]
    change ((2 * (n : ℝ) ^ 2) * Z) * (1 / (Dik * (w ⟨i, k, hik⟩ : ℝ)) +
      1 / ((Z * E) * 1)) = _
    field_simp [hZ.ne', hDik.ne', hE.ne', hwi.ne']
    <;> ring
  have hcoefficient : 0 ≤ coefficient := (div_pos (by norm_num)
    (mul_pos (mul_pos hDik hZ) hE)).le
  have hS : (∑ t ∈ U, if h : t ≠ i ∧ t ≠ k then
      (D ⟨i, t, Ne.symm h.1⟩ : ℝ) / (w ⟨t, k, h.2⟩ : ℝ) else 0) = S := by
    apply Finset.sum_subset (Finset.subset_univ _)
    intro t _ ht
    have hneg : ¬ (t ≠ i ∧ t ≠ k) := by
      intro hh
      exact ht (by simp [U, hh.1, hh.2])
    rw [dif_neg hneg]
  have hfutureBound : -(∑ t ∈ U, nodeFuture r o₁ o₂ q B U root t / W (t, false)) ≤
      coefficient * S := by
    calc
      _ = ∑ t ∈ U, -(nodeFuture r o₁ o₂ q B U root t / W (t, false)) :=
        by rw [Finset.sum_neg_distrib]
      _ ≤ ∑ t ∈ U, coefficient * (if h : t ≠ i ∧ t ≠ k then
          (D ⟨i, t, Ne.symm h.1⟩ : ℝ) / (w ⟨t, k, h.2⟩ : ℝ) else 0) := by
        apply Finset.sum_le_sum
        intro t ht
        have htk : t ≠ k := (Finset.mem_erase.mp ht).1
        have hti : t ≠ i := (Finset.mem_erase.mp (Finset.mem_erase.mp ht).2).1
        have hwt : W (t, false) = (w ⟨t, k, htk⟩ : ℝ) := by
          simp only [W, if_neg hti, dif_neg htk]
        have hwpos : (0 : ℝ) < (w ⟨t, k, htk⟩ : ℝ) := by exact_mod_cast hw _
        rw [SlotTransportFlow.two_hole_future r o₁ o₂ q B U p d hpd t,
          hsp, hsd, hwt, dif_pos ⟨hti, htk⟩]
        calc
          _ = coefficient * (futureMatrix r o₁ o₂ q B {p, d} U t p d /
              (w ⟨t, k, htk⟩ : ℝ)) := by dsimp only [coefficient]; ring
          _ ≤ _ := mul_le_mul_of_nonneg_left
            (div_le_div_of_nonneg_right
              (DefectSlotFutureBound.root_future_le_defect_partition r o₁ o₂ q hq
                i t k hti.symm htk hik a b) hwpos.le) hcoefficient
      _ = coefficient * S := by rw [← Finset.mul_sum, hS]
  have hC : 0 ≤ C := by dsimp only [C]; positivity
  have hscale : C * coefficient = (2 * (n : ℝ) ^ 2) * (2 / (Dik * E)) := by
    change ((2 * (n : ℝ) ^ 2) * Z) * (2 / (Dik * Z * E)) = _
    field_simp [hZ.ne']
  calc
    _ = C * nodePotential r o₁ o₂ q B U W root +
        C * (-(∑ t ∈ U, nodeFuture r o₁ o₂ q B U root t / W (t, false))) := by ring
    _ = (2 * (n : ℝ) ^ 2) * (1 / classMass π (.defect i k) + 1 / E) +
        C * (-(∑ t ∈ U, nodeFuture r o₁ o₂ q B U root t / W (t, false))) := by rw [hrootCost]
    _ ≤ (2 * (n : ℝ) ^ 2) * (1 / classMass π (.defect i k) + 1 / E) +
        C * (coefficient * S) := add_le_add le_rfl (mul_le_mul_of_nonneg_left hfutureBound hC)
    _ = _ := by rw [← mul_assoc, hscale]; ring
