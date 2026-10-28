-- Prove2me | solution 1 for CountingMatroid.Analysis.SlotDemandRecursion.leaf_potential_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-24T15:53:00.47745+00:00
-- url     : https://prove2.me/submissions/834e68dd-3943-46f1-97a0-c9822770deda

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
import Theorems.Thm_CountingMatroid_Analysis_DefectSlotConservation_future_form_conserved
import Theorems.Thm_CountingMatroid_Analysis_SlotDemandRecursion_split_node_balanced
import Theorems.Thm_CountingMatroid_Analysis_SlotDemandRecursion_split_nodes_opposite
import Theorems.Thm_CountingMatroid_Analysis_SlotDemandRecursion_split_potential_bound

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





/-- INTERNAL: A fresh split leaves every later pair fresh, using the
absence of repetitions in the processing order.
TEXLINE: main.tex:516-553 -/
private theorem split_tail_free {n : ℕ} (r : ℕ) (o₁ o₂ : IndependenceOracle n)
    (q : ℚ) (B : PairedSet n) (node : DemandNode n) (t : Fin n)
    (slots : List (Fin n)) (ht : t ∉ slots)
    (hfree : ∀ s ∈ t :: slots, ∀ c : Bool, (s, c) ∉ node.holes) (c : Bool) :
    ∀ s ∈ slots, ∀ d : Bool,
      (s, d) ∉ (splitNode r o₁ o₂ q B (t :: slots).toFinset node t c).holes := by
  classical
  intro s hs d
  have hst : s ≠ t := by rintro rfl; exact ht hs
  change (s, d) ∉ insert (t, c) node.holes
  simp only [Finset.mem_insert, Prod.mk.injEq, not_or]
  exact ⟨fun h => hst h.1, hfree s (List.mem_cons_of_mem t hs) d⟩













/-- PAPER: main.tex:628-641
The concrete split operation conserves every future-slot quadratic. -/
theorem split_future_conserved {n : ℕ} (r : ℕ) (o₁ o₂ : IndependenceOracle n)
    (q : ℚ) (B : PairedSet n) (U : Finset (Fin n))
    (node : DemandNode n) (t s : Fin n) (ht : t ∈ U) (hts : t ≠ s)
    (hfree : ∀ c : Bool, (t, c) ∉ B ∧ (t, c) ∉ node.holes)
    (hbalance : CountingMatroid.Analysis.SlotDemandRecursion.Balanced r o₁ o₂ q B U node) :
    nodeFuture r o₁ o₂ q B (U.erase t) (splitNode r o₁ o₂ q B U node t false) s +
      nodeFuture r o₁ o₂ q B (U.erase t) (splitNode r o₁ o₂ q B U node t true) s =
        nodeFuture r o₁ o₂ q B U node s := by
  exact DefectSlotConservation.future_form_conserved r o₁ o₂ q B node.holes U t s
    ht hts hfree node.values
    (splitNode r o₁ o₂ q B U node t false).values
    (splitNode r o₁ o₂ q B U node t true).values
    (split_node_keeps r o₁ o₂ q B U node t false (hfree false).2)
    (split_node_keeps r o₁ o₂ q B U node t true (hfree true).2)
    (split_nodes_opposite r o₁ o₂ q B U node t ht hfree hbalance)













end CountingMatroid.Analysis.SlotDemandRecursion

end
set_option autoImplicit false

/-!
Demand nodes and the binary recursion from the transport proof. Splitting a
node keeps old-hole values and assigns the new hole the value that balances
its child. The recursion records all leaves in processing order.
-/

namespace CountingMatroid.Analysis.SlotDemandRecursion
end CountingMatroid.Analysis.SlotDemandRecursion
open CountingMatroid CountingMatroid.Analysis CountingMatroid.Analysis.SlotDemandRecursion

open CountingMatroid.Model CountingMatroid.Program
open CountingMatroid.Analysis.DefectSlotSplitSignature
open scoped BigOperators

/-- PAPER: main.tex:642-665
Iterating the balanced splits bounds the total leaf potential by the root
potential minus the sum of its future-slot quadratics. This is the recursive
potential estimate before the root's two-hole data are substituted. -/
theorem solution {n : ℕ} (r : ℕ) (o₁ o₂ : IndependenceOracle n)
    (q : ℚ) (hq : 0 < q) (B : PairedSet n)
    (slots : List (Fin n)) (hnodup : slots.Nodup) (node : DemandNode n)
    (hBR : Disjoint B node.holes)
    (hfree : ∀ s ∈ slots, ∀ c : Bool, (s, c) ∉ B ∧ (s, c) ∉ node.holes)
    (hsize : B.card + node.holes.card + slots.toFinset.card = n + 1)
    (hbalance : CountingMatroid.Analysis.SlotDemandRecursion.Balanced r o₁ o₂ q B slots.toFinset node)
    (W : PairedGround n → ℝ)
    (hW : ∀ s ∈ slots, W (s, false) = W (s, true) ∧ 0 < W (s, false))
    (hsplit : SlotSplitControl n r o₁ o₂ q) :
    ((leafNodes r o₁ o₂ q B slots node).map (nodePotential r o₁ o₂ q B ∅ W)).sum ≤
      nodePotential r o₁ o₂ q B slots.toFinset W node -
        ∑ s ∈ slots.toFinset, nodeFuture r o₁ o₂ q B slots.toFinset node s / W (s, false) := by
  classical
  induction slots generalizing node with
  | nil =>
    simp only [leafNodes, List.map_singleton, List.sum_singleton,
      List.toFinset_nil, Finset.sum_empty, sub_zero, le_refl]
  | cons t slots ih =>
    obtain ⟨ht, hnd⟩ := List.nodup_cons.mp hnodup
    let U := (t :: slots).toFinset
    let V := slots.toFinset
    have hUe : U = insert t V := List.toFinset_cons
    let N := fun c => splitNode r o₁ o₂ q B U node t c
    have htV : t ∉ V := by simpa only [V, List.mem_toFinset] using ht
    have htU : t ∈ U := by simp only [U, List.toFinset_cons, Finset.mem_insert, true_or]
    have herase : U.erase t = V := by
      rw [hUe, Finset.erase_insert htV]
    have hft (c : Bool) : (t, c) ∉ B ∧ (t, c) ∉ node.holes :=
      hfree t List.mem_cons_self c
    have hchildBR (c : Bool) : Disjoint B (N c).holes := by
      change Disjoint B (insert (t, c) node.holes)
      rw [Finset.disjoint_insert_right]
      exact ⟨hft c |>.1, hBR⟩
    have hchildFree (c : Bool) : ∀ s ∈ slots, ∀ d : Bool,
        (s, d) ∉ B ∧ (s, d) ∉ (N c).holes := by
      intro s hs d
      exact ⟨(hfree s (List.mem_cons_of_mem t hs) d).1,
        split_tail_free r o₁ o₂ q B node t slots ht
          (fun s hs d => (hfree s hs d).2) c s hs d⟩
    have hchildSize (c : Bool) : B.card + (N c).holes.card + V.card = n + 1 := by
      have hUcard : U.card = V.card + 1 := by
        rw [hUe, Finset.card_insert_of_notMem htV]
      have hRcard : (N c).holes.card = node.holes.card + 1 :=
        Finset.card_insert_of_notMem (hft c).2
      change B.card + node.holes.card + U.card = n + 1 at hsize
      omega
    have hchildBal (c : Bool) : CountingMatroid.Analysis.SlotDemandRecursion.Balanced r o₁ o₂ q B V (N c) := by
      rw [← herase]
      exact split_node_balanced r o₁ o₂ q hq B U node t c (hft c).2
    have hWTail : ∀ s ∈ slots, W (s, false) = W (s, true) ∧ 0 < W (s, false) :=
      fun s hs => hW s (List.mem_cons_of_mem t hs)
    have hrec (c : Bool) := ih hnd (N c) (hchildBR c) (hchildFree c)
      (hchildSize c) (hchildBal c) hWTail
    have hbound := split_potential_bound r o₁ o₂ q hq B U node t htU hBR
      (fun s hs d => hfree s (List.mem_toFinset.mp hs) d) hsize hbalance W
      (hW t List.mem_cons_self).1 (hW t List.mem_cons_self).2 hsplit
    rw [herase] at hbound
    have hfutureSum :
        (∑ s ∈ V, nodeFuture r o₁ o₂ q B V (N false) s / W (s, false)) +
        (∑ s ∈ V, nodeFuture r o₁ o₂ q B V (N true) s / W (s, false)) =
          ∑ s ∈ V, nodeFuture r o₁ o₂ q B U node s / W (s, false) := by
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro s hs
      rw [← add_div]
      have hts : t ≠ s := by rintro rfl; exact htV hs
      have hc := split_future_conserved r o₁ o₂ q B U node t s htU hts hft hbalance
      rw [herase] at hc
      rw [hc]
    have hrootSum :
        (∑ s ∈ U, nodeFuture r o₁ o₂ q B U node s / W (s, false)) =
        nodeFuture r o₁ o₂ q B U node t / W (t, false) +
          ∑ s ∈ V, nodeFuture r o₁ o₂ q B U node s / W (s, false) := by
      rw [hUe, Finset.sum_insert htV]
    rw [leafNodes, List.map_append, List.sum_append]
    change _ ≤ nodePotential r o₁ o₂ q B U W node -
      ∑ s ∈ U, nodeFuture r o₁ o₂ q B U node s / W (s, false)
    rw [hrootSum]
    have ha := hrec false
    have hb := hrec true
    change ((leafNodes r o₁ o₂ q B slots (N false)).map
      (nodePotential r o₁ o₂ q B ∅ W)).sum ≤
      nodePotential r o₁ o₂ q B V W (N false) -
        ∑ s ∈ V, nodeFuture r o₁ o₂ q B V (N false) s / W (s, false) at ha
    change ((leafNodes r o₁ o₂ q B slots (N true)).map
      (nodePotential r o₁ o₂ q B ∅ W)).sum ≤
      nodePotential r o₁ o₂ q B V W (N true) -
        ∑ s ∈ V, nodeFuture r o₁ o₂ q B V (N true) s / W (s, false) at hb
    change nodePotential r o₁ o₂ q B V W (N false) +
      nodePotential r o₁ o₂ q B V W (N true) ≤
      nodePotential r o₁ o₂ q B U W node - nodeFuture r o₁ o₂ q B U node t / W (t, false)
      at hbound
    change ((leafNodes r o₁ o₂ q B slots (N false)).map
      (nodePotential r o₁ o₂ q B ∅ W)).sum +
      ((leafNodes r o₁ o₂ q B slots (N true)).map
      (nodePotential r o₁ o₂ q B ∅ W)).sum ≤ _
    linarith [ha, hb, hbound, hfutureSum]
