-- Prove2me | solution 1 for CountingMatroid.Analysis.SlotDemandPairing.split_pairing_conserved
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-24T15:29:14.971532+00:00
-- url     : https://prove2.me/submissions/c3c198eb-88a7-446d-96b5-06844afa1f64

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
import Definitions.Def_CountingMatroid_Analysis_BoundedRunPhase
import Definitions.Def_CountingMatroid_Analysis_BoundedRunPhaseHistory
import Definitions.Def_CountingMatroid_Analysis_ConditionalDefectCoefficients
import Definitions.Def_CountingMatroid_Analysis_ConditionalDefectExtractionCoefficients
import Definitions.Def_CountingMatroid_Analysis_ConditionalDefectQuadratics
import Definitions.Def_CountingMatroid_Analysis_CubicTensorContraction
import Definitions.Def_CountingMatroid_Analysis_DefectPartitionQuadraticConstruction
import Definitions.Def_CountingMatroid_Analysis_DefectSlotConservation
import Definitions.Def_CountingMatroid_Analysis_DefectSlotSplitSignature
import Definitions.Def_CountingMatroid_Analysis_FirstPhaseFailure
import Definitions.Def_CountingMatroid_Analysis_InitialMultipliersGood
import Definitions.Def_CountingMatroid_Analysis_LorentzianDirectionalSignature
import Definitions.Def_CountingMatroid_Analysis_OmittedRankWeightPolynomial
import Definitions.Def_CountingMatroid_Analysis_OmittedSlotCoefficientFormula
import Definitions.Def_CountingMatroid_Analysis_OmittedSlotQuadratic
import Definitions.Def_CountingMatroid_Analysis_OmittedTutteNormalization
import Definitions.Def_CountingMatroid_Analysis_QuadraticNonpositiveHyperplane
import Definitions.Def_CountingMatroid_Analysis_RankWeightQuadraticSignature
import Definitions.Def_CountingMatroid_Analysis_RankWeightSupportExchange
import Definitions.Def_CountingMatroid_Analysis_ScheduleConfidence
import Definitions.Def_CountingMatroid_Analysis_SlotBlockSignature
import Definitions.Def_CountingMatroid_Analysis_SlotDemandPairing
import Definitions.Def_CountingMatroid_Analysis_SlotDemandRecursion
import Definitions.Def_CountingMatroid_Analysis_SquarefreeCoordinateHessian
import Definitions.Def_CountingMatroid_Analysis_ThreePairSignatureSchur
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
import Theorems.Thm_CountingMatroid_Analysis_SlotDemandPairing_completion_moment_split
import Theorems.Thm_CountingMatroid_Analysis_SlotDemandRecursion_split_nodes_opposite

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







/-- INTERNAL: Old holes retain their values in both children.
TEXLINE: main.tex:543-553 -/
theorem split_node_keeps {n : ℕ} (r : ℕ) (o₁ o₂ : IndependenceOracle n)
    (q : ℚ) (B : PairedSet n) (U : Finset (Fin n))
    (node : DemandNode n) (t : Fin n) (c : Bool) (hfree : (t, c) ∉ node.holes)
    (i : PairedGround n) (hi : i ∈ node.holes) :
    (splitNode r o₁ o₂ q B U node t c).values i = node.values i := by
  classical
  have hne : i ≠ (t, c) := by rintro rfl; exact hfree hi
  exact Function.update_of_ne hne _ _

































end CountingMatroid.Analysis.SlotDemandRecursion

end

section


set_option autoImplicit false

/-!
First-moment conservation for the paper's balanced demand recursion.
The same completion partition works for an arbitrary state function, so
opposite new-hole demands cancel before any exchange flow is constructed.
-/

namespace CountingMatroid.Analysis.SlotDemandPairing

open CountingMatroid.Model CountingMatroid.Program
open CountingMatroid.Analysis.DefectSlotSplitSignature
open CountingMatroid.Analysis.SlotDemandRecursion
open scoped BigOperators









/-- PAPER: main.tex:540-543,689-692
The new-hole completion moments coincide for both choices, since the
processed pair is empty in their shared state. -/
theorem new_hole_moment_eq {n : ℕ} (B R : PairedSet n)
    (U : Finset (Fin n)) (t : Fin n)
    (hfree : ∀ c : Bool, (t, c) ∉ R) (f : PairedSet n → ℝ) :
    completionMoment B (insert (t, false) R) (U.erase t) (t, false) f =
      completionMoment B (insert (t, true) R) (U.erase t) (t, true) f := by
  classical
  simp only [completionMoment, SlotCompletion, Finset.erase_insert (hfree _)]









end CountingMatroid.Analysis.SlotDemandPairing

end
set_option autoImplicit false

/-!
First-moment conservation for the paper's balanced demand recursion.
The same completion partition works for an arbitrary state function, so
opposite new-hole demands cancel before any exchange flow is constructed.
-/

namespace CountingMatroid.Analysis.SlotDemandPairing
end CountingMatroid.Analysis.SlotDemandPairing
open CountingMatroid CountingMatroid.Analysis CountingMatroid.Analysis.SlotDemandPairing

open CountingMatroid.Model CountingMatroid.Program
open CountingMatroid.Analysis.DefectSlotSplitSignature
open CountingMatroid.Analysis.SlotDemandRecursion
open scoped BigOperators

/-- PAPER: main.tex:684-692
A balanced split preserves the pairing: old-hole moments partition, while
the two opposite new-hole values multiply the same shared-state moment. -/
theorem solution {n : ℕ} (r : ℕ) (o₁ o₂ : IndependenceOracle n)
    (q : ℚ) (B : PairedSet n) (U : Finset (Fin n)) (node : DemandNode n)
    (t : Fin n) (ht : t ∈ U)
    (hfree : ∀ c : Bool, (t, c) ∉ B ∧ (t, c) ∉ node.holes)
    (hbalance : CountingMatroid.Analysis.SlotDemandRecursion.Balanced r o₁ o₂ q B U node) (f : PairedSet n → ℝ) :
    nodePairing B (U.erase t) (splitNode r o₁ o₂ q B U node t false) f +
      nodePairing B (U.erase t) (splitNode r o₁ o₂ q B U node t true) f =
        nodePairing B U node f := by
  classical
  let N := fun c => splitNode r o₁ o₂ q B U node t c
  change (∑ i ∈ insert (t, false) node.holes,
    (N false).values i * completionMoment B (N false).holes (U.erase t) i f) +
    (∑ i ∈ insert (t, true) node.holes,
    (N true).values i * completionMoment B (N true).holes (U.erase t) i f) = _
  rw [Finset.sum_insert (hfree false).2, Finset.sum_insert (hfree true).2]
  have hold : (∑ i ∈ node.holes,
      (N false).values i * completionMoment B (N false).holes (U.erase t) i f) +
      (∑ i ∈ node.holes,
      (N true).values i * completionMoment B (N true).holes (U.erase t) i f) =
      nodePairing B U node f := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i hi
    rw [split_node_keeps r o₁ o₂ q B U node t false (hfree false).2 i hi,
      split_node_keeps r o₁ o₂ q B U node t true (hfree true).2 i hi, ← mul_add]
    exact congrArg (node.values i * ·)
      (completion_moment_split B node.holes U t ht i hi hfree f)
  have hnew := new_hole_moment_eq B node.holes U t (fun c => (hfree c).2) f
  have hopp := split_nodes_opposite r o₁ o₂ q B U node t ht hfree hbalance
  change (N false).values (t, false) + (N true).values (t, true) = 0 at hopp
  change completionMoment B (N false).holes (U.erase t) (t, false) f =
    completionMoment B (N true).holes (U.erase t) (t, true) f at hnew
  rw [← hnew]
  have hcancel : (N false).values (t, false) *
      completionMoment B (N false).holes (U.erase t) (t, false) f +
      (N true).values (t, true) *
      completionMoment B (N false).holes (U.erase t) (t, false) f = 0 := by
    rw [← add_mul, hopp, zero_mul]
  linarith
