-- Prove2me | solution 1 for CountingMatroid.Analysis.DefectSlotRoot.root_demand_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-24T16:09:21.254162+00:00
-- url     : https://prove2.me/submissions/8ae818e8-d2e5-432c-a366-88ae4276238a

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
import Theorems.Thm_CountingMatroid_Analysis_DefectSlotRoot_defect_root_shape
import Theorems.Thm_CountingMatroid_Analysis_DefectSlotRoot_event_completion_iff
import Theorems.Thm_CountingMatroid_Analysis_DefectSlotRoot_event_slot_total
import Theorems.Thm_CountingMatroid_Analysis_DefectSlotSplitSignature_slot_total_pos

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

/-- INTERNAL: Evaluate a completion moment on the weighted indicator of
one state, for the pointwise root-demand identity.
TEXLINE: main.tex:493-498,684-692 -/
private theorem completion_moment_indicator {n : ℕ} (B R : PairedSet n)
    (U : Finset (Fin n)) (hole : PairedGround n) (f : PairedSet n → ℝ)
    (state : PairedSet n) :
    completionMoment B R U hole (fun S => if S = state then f S else 0) =
      if SlotCompletion B R U hole state then f state else 0 := by
  classical
  unfold completionMoment
  rw [Finset.sum_eq_single state]
  · simp
  · intro S _ hS
    simp [hS]
  · simp





end CountingMatroid.Analysis.DefectSlotRoot

end
set_option autoImplicit false

/-!
Identify the root completion classes in the defect/event transport with
the executable classifier and prescribed transversal event. All totals
use the actual operational rank weights.
-/

namespace CountingMatroid.Analysis.DefectSlotRoot
end CountingMatroid.Analysis.DefectSlotRoot
open CountingMatroid CountingMatroid.Analysis CountingMatroid.Analysis.DefectSlotRoot

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

/-- PAPER: main.tex:493-498,875-895
The two-hole root demand is exactly the normalized defect source minus
the normalized prescribed-event sink used by the parent flow certificate. -/
theorem solution {n : ℕ} (r : ℕ) (o₁ o₂ : IndependenceOracle n)
    (q : ℚ) (w : Multipliers n) (hq : 0 < q) (hw : ∀ index, 0 < w index)
    (i k : Fin n) (hik : i ≠ k) (a b : Bool)
    (hA : 0 < eventMass (operationalLaw r o₁ o₂ q w hq hw) (pairEvent i k a b)) :
    completionDemand r o₁ o₂ q {(k, !b)} ((Finset.univ.erase i).erase k)
      (twoHoleRoot r o₁ o₂ q {(k, !b)} ((Finset.univ.erase i).erase k) (i, !a) (k, b)) =
        conditionalMeanDemand (operationalLaw r o₁ o₂ q w hq hw) (.defect i k) (pairEvent i k a b) := by
  classical
  let Z : ℝ := (StationaryMeanIdentities.normalizer r o₁ o₂ q w : ℝ)
  let D : ℝ := (FirstPhaseFailure.defectPartition r o₁ o₂ q ⟨i, k, hik⟩ : ℝ)
  let π := operationalLaw r o₁ o₂ q w hq hw
  let A := pairEvent i k a b
  let f := fun state : PairedSet n =>
    ((q ^ (n - (CountingMatroid.Model.Subroutines.pairedRank r o₁ o₂ state).val) : ℚ) : ℝ)
  obtain ⟨hZq, _, _, hdef⟩ :=
    StationaryMeanIdentities.stationary_mean_identities r o₁ o₂ q 1 w hq hw
  have hZ : 0 < Z := by dsimp only [Z]; exact_mod_cast hZq
  have hD : 0 < D := by
    dsimp only [D]
    rw [← source_slot_total r o₁ o₂ q i k hik a b]
    exact slot_total_pos r o₁ o₂ q hq _ _ _ _
  have hwi : (0 : ℝ) < (w ⟨i, k, hik⟩ : ℝ) := by exact_mod_cast hw ⟨i, k, hik⟩
  have hmass : classMass π (.defect i k) = (w ⟨i, k, hik⟩ : ℝ) * D / Z := by
    dsimp only [π]
    rw [operational_class_mass, hdef ⟨i, k, hik⟩]
    simp only [Rat.cast_div, Rat.cast_mul]
    rfl
  have hpd : (i, !a) ≠ (k, b) := fun he => hik (congrArg Prod.fst he)
  funext state
  have hsource :
      (1 / D) * (if (classifyState state).val = .defect i k then f state else 0) =
        (if (classifyState state).val = .defect i k then π state / classMass π (.defect i k) else 0) := by
    by_cases hs : (classifyState state).val = .defect i k
    · rw [if_pos hs, if_pos hs, hmass]
      have hweight : StationaryMeanIdentities.stateWeight r o₁ o₂ q w state =
          w ⟨i, k, hik⟩ * q ^ (n - (CountingMatroid.Model.Subroutines.pairedRank r o₁ o₂ state).val) := by
        simp [StationaryMeanIdentities.stateWeight, hs, weightOfKind, hik,
          Model.Operations.natSub, CountingMatroid.Analysis.BoundedRunResourceEnvelope.ratPower_value_import_support,
          Model.Operations.multiplierRead, Model.Operations.ratMul]
      change (1 / D) * f state =
        ((StationaryMeanIdentities.stateWeight r o₁ o₂ q w state : ℝ) / Z) /
          ((w ⟨i, k, hik⟩ : ℝ) * D / Z)
      rw [hweight, Rat.cast_mul]
      change (1 / D) * f state = (((w ⟨i, k, hik⟩ : ℝ) * f state) / Z) /
        ((w ⟨i, k, hik⟩ : ℝ) * D / Z)
      field_simp [hD.ne', hZ.ne', hwi.ne']
    · simp only [if_neg hs, mul_zero]
  have hsink :
      (-1 / (Z * eventMass π A)) * (if state ∈ A then f state else 0) =
        -(if state ∈ A then π state / eventMass π A else 0) := by
    by_cases hs : state ∈ A
    · rw [if_pos hs, if_pos hs]
      have hclass : (classifyState state).val = .transversal := (Finset.mem_filter.mp hs).2.1
      have hweight : StationaryMeanIdentities.stateWeight r o₁ o₂ q w state =
          q ^ (n - (CountingMatroid.Model.Subroutines.pairedRank r o₁ o₂ state).val) := by
        simp [StationaryMeanIdentities.stateWeight, hclass, weightOfKind,
          Model.Operations.natSub, CountingMatroid.Analysis.BoundedRunResourceEnvelope.ratPower_value_import_support]
      change (-1 / (Z * eventMass π A)) * f state =
        -((StationaryMeanIdentities.stateWeight r o₁ o₂ q w state : ℝ) / Z / eventMass π A)
      rw [hweight]
      change (-1 / (Z * eventMass π A)) * f state = -(f state / Z / eventMass π A)
      ring
    · simp only [if_neg hs, mul_zero, neg_zero]
  unfold completionDemand nodePairing
  change (∑ hole ∈ ({(i, !a), (k, b)} : PairedSet n),
    (if hole = (i, !a) then 1 / slotTotal r o₁ o₂ q {(k, !b)} {(i, !a), (k, b)}
      ((Finset.univ.erase i).erase k) (i, !a)
     else if hole = (k, b) then -1 / slotTotal r o₁ o₂ q {(k, !b)} {(i, !a), (k, b)}
      ((Finset.univ.erase i).erase k) (k, b) else 0) *
    completionMoment {(k, !b)} {(i, !a), (k, b)} ((Finset.univ.erase i).erase k)
      hole (fun S => if S = state then f S else 0)) = _
  rw [Finset.sum_insert (by simpa using hpd), Finset.sum_singleton]
  simp only [ite_true, if_neg (Ne.symm hpd)]
  rw [completion_moment_indicator, completion_moment_indicator,
    source_completion_iff i k hik a b, event_completion_iff i k hik a b,
    source_slot_total r o₁ o₂ q i k hik a b,
    event_slot_total r o₁ o₂ q w hq hw i k hik a b]
  have heq := congrArg₂ (fun x y : ℝ => x + y) hsource hsink
  by_cases hs : (classifyState state).val = .defect i k <;>
    by_cases hm : state ∈ A
  all_goals simpa only [D, Z, π, A, conditionalMeanDemand, sub_eq_add_neg,
    hs, hm, if_true, if_false] using heq
