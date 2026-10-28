-- Prove2me | solution 1 for CountingMatroid.Analysis.DefectSlotConservation.slot_total_split
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-24T14:36:42.98874+00:00
-- url     : https://prove2.me/submissions/da09287d-9b1e-49d7-b4a3-797c21f7e615

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

/-- INTERNAL: Separate the chosen label of the pair being processed from
its remaining completion labels.
TEXLINE: main.tex:531-540 -/
private theorem choice_image_split {n : ℕ} (U : Finset (Fin n))
    (t : Fin n) (ht : t ∈ U) (choices : Fin n → Bool) :
    U.image (fun s => (s, choices s)) =
      insert (t, choices t) ((U.erase t).image (fun s => (s, choices s))) := by
  classical
  conv_lhs => rw [← Finset.insert_erase ht, Finset.image_insert]

/-- INTERNAL: A free binary pair can be selected in exactly its two
possible ways; choices at all other pairs stay unchanged.
TEXLINE: main.tex:531-540 -/
private theorem choice_completion_split {n : ℕ} (Q : PairedSet n)
    (U : Finset (Fin n)) (t : Fin n) (ht : t ∈ U) (state : PairedSet n) :
    (∃ choices : Fin n → Bool,
      state = Q ∪ U.image (fun s => (s, choices s))) ↔
    (∃ choices : Fin n → Bool,
      state = insert (t, false) Q ∪ (U.erase t).image (fun s => (s, choices s))) ∨
    (∃ choices : Fin n → Bool,
      state = insert (t, true) Q ∪ (U.erase t).image (fun s => (s, choices s))) := by
  classical
  constructor
  · rintro ⟨choices, rfl⟩
    rw [choice_image_split U t ht choices]
    cases choices t
    · left
      exact ⟨choices, by simp⟩
    · right
      exact ⟨choices, by simp⟩
  · have lift (c : Bool) (choices : Fin n → Bool)
        (hs : state = insert (t, c) Q ∪
          (U.erase t).image (fun s => (s, choices s))) :
        ∃ choices : Fin n → Bool,
          state = Q ∪ U.image (fun s => (s, choices s)) := by
      refine ⟨Function.update choices t c, ?_⟩
      have himage : (U.erase t).image (fun s => (s, Function.update choices t c s)) =
          (U.erase t).image (fun s => (s, choices s)) := by
        apply Finset.image_congr
        intro s hs
        dsimp only
        rw [Function.update_of_ne (Finset.ne_of_mem_erase hs)]
      rw [choice_image_split U t ht, Function.update_self, himage]
      simpa using hs
    rintro (⟨choices, hs⟩ | ⟨choices, hs⟩)
    · exact lift false choices hs
    · exact lift true choices hs

/-- INTERNAL: After a pair has been processed, precisely its chosen label
occurs, provided neither of its labels is fixed in the base.
TEXLINE: main.tex:531-540 -/
private theorem child_membership {n : ℕ} (Q : PairedSet n)
    (U : Finset (Fin n)) (t : Fin n) (hQ : ∀ c : Bool, (t, c) ∉ Q)
    (c d : Bool) (state : PairedSet n)
    (hs : ∃ choices : Fin n → Bool,
      state = insert (t, c) Q ∪ (U.erase t).image (fun s => (s, choices s))) :
    (t, d) ∈ state ↔ d = c := by
  classical
  obtain ⟨choices, rfl⟩ := hs
  have hn : (t, d) ∉ (U.erase t).image (fun s => (s, choices s)) := by
    rintro hm
    obtain ⟨s, hs, heq⟩ := Finset.mem_image.mp hm
    have hst : s = t := congrArg Prod.fst heq
    exact (Finset.ne_of_mem_erase hs) hst
  simp [hQ d, hn]























end CountingMatroid.Analysis.DefectSlotConservation

end
set_option autoImplicit false

/-!
Binary completion identities used by the balanced-hole recursion. Processing
one ordinary pair partitions each old-hole completion into its two children.
The corresponding future-slot matrix identities give conservation of the
future quadratic forms; these identities use finite sets, not a signature
assumption.
-/

namespace CountingMatroid.Analysis.DefectSlotConservation
end CountingMatroid.Analysis.DefectSlotConservation
open CountingMatroid CountingMatroid.Analysis CountingMatroid.Analysis.DefectSlotConservation

open CountingMatroid.Model CountingMatroid.Program
open CountingMatroid.Analysis.DefectSlotSplitSignature
open scoped BigOperators

/-- PAPER: main.tex:535-540
The two child totals of any old hole add to its parent total. -/
theorem solution {n : ℕ} (r : ℕ) (o₁ o₂ : IndependenceOracle n)
    (q : ℚ) (B R : PairedSet n) (U : Finset (Fin n))
    (t : Fin n) (ht : t ∈ U)
    (hfree : ∀ c : Bool, (t, c) ∉ B ∧ (t, c) ∉ R)
    (hole : PairedGround n) (hhole : hole ∈ R) :
    slotTotal r o₁ o₂ q B (insert (t, false) R) (U.erase t) hole +
      slotTotal r o₁ o₂ q B (insert (t, true) R) (U.erase t) hole =
        slotTotal r o₁ o₂ q B R U hole := by
  classical
  have hne (c : Bool) : hole ≠ (t, c) := by
    rintro rfl
    exact (hfree c).2 hhole
  have hshape (c : Bool) (state : PairedSet n) :
      SlotCompletion B (insert (t, c) R) (U.erase t) hole state ↔
        ∃ choices : Fin n → Bool,
          state = insert (t, c) (B ∪ R.erase hole) ∪
            (U.erase t).image (fun s => (s, choices s)) := by
    unfold SlotCompletion
    rw [Finset.erase_insert_of_ne (hne c).symm]
    simp only [Finset.union_insert]
  have hQ (c : Bool) : (t, c) ∉ B ∪ R.erase hole := by
    simp only [Finset.mem_union, Finset.mem_erase, not_or]
    exact ⟨(hfree c).1, fun h => (hfree c).2 h.2⟩
  unfold slotTotal
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro state _
  have hsplit : SlotCompletion B R U hole state ↔
      SlotCompletion B (insert (t, false) R) (U.erase t) hole state ∨
        SlotCompletion B (insert (t, true) R) (U.erase t) hole state := by
    rw [hshape false, hshape true]
    exact choice_completion_split (B ∪ R.erase hole) U t ht state
  have hdisjoint : SlotCompletion B (insert (t, false) R) (U.erase t) hole state →
      ¬ SlotCompletion B (insert (t, true) R) (U.erase t) hole state := by
    intro ha hb
    have hmem := (child_membership _ U t hQ false false state
      ((hshape false state).mp ha)).mpr rfl
    have hfalse := (child_membership _ U t hQ true false state
      ((hshape true state).mp hb)).mp hmem
    cases hfalse
  rw [hsplit]
  by_cases ha : SlotCompletion B (insert (t, false) R) (U.erase t) hole state
  · rw [if_pos ha, if_neg (hdisjoint ha), if_pos (Or.inl ha), add_zero]
  · by_cases hb : SlotCompletion B (insert (t, true) R) (U.erase t) hole state
    · rw [if_neg ha, if_pos hb, if_pos (Or.inr hb), zero_add]
    · rw [if_neg ha, if_neg hb, if_neg (not_or.mpr ⟨ha, hb⟩), zero_add]
