-- Prove2me | solution 1 for CountingMatroid.Analysis.SlotOmissionPatternCharacterization.omission_pattern_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-24T16:09:47.530986+00:00
-- url     : https://prove2.me/submissions/02e5047e-63f5-41df-8823-1efee153fa0a

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
import Theorems.Thm_CountingMatroid_Analysis_SlotOmissionPatternCharacterization_active_completion_card
import Theorems.Thm_CountingMatroid_Analysis_SlotOmissionPatternCharacterization_active_completion_membership
import Theorems.Thm_CountingMatroid_Analysis_SlotOmissionPatternCharacterization_pattern_iff_membership

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
section


set_option autoImplicit false

/-! The surviving omitted-label patterns in the slot quadratic are exactly
completions with two distinct active labels omitted. This is the combinatorial
coefficient identification in the transport Hessian. -/

namespace CountingMatroid.Analysis.SlotOmissionPatternCharacterization
open CountingMatroid.Model
open CountingMatroid.Analysis.OmittedSlotCoefficientFormula
open CountingMatroid.Analysis.OmittedSlotQuadratic
open CountingMatroid.Analysis.OmittedTutteNormalization
open scoped BigOperators
open Classical



















/-- INTERNAL: Membership in the chosen-label image is pointwise. -/
lemma mem_choice_image {n : ℕ} (S : Finset (Fin n)) (choices : Fin n → Bool)
    (e : PairedGround n) :
    e ∈ S.image (fun s => (s, choices s)) ↔ e.1 ∈ S ∧ choices e.1 = e.2 := by
  constructor
  · rintro he
    obtain ⟨s, hs, rfl⟩ := Finset.mem_image.mp he
    exact ⟨hs, rfl⟩
  · rintro ⟨hs, hb⟩
    exact Finset.mem_image.mpr ⟨e.1, hs, Prod.ext rfl hb⟩



/-- INTERNAL: The explicit completion selects exactly its chosen ordinary label. -/
lemma ordinary_completion_membership {n : ℕ} (B R : PairedSet n) (U : Finset (Fin n))
    (hU : ∀ s ∈ U, ∀ b : Bool, (s, b) ∉ B ∧ (s, b) ∉ R)
    (t s : Fin n) (hs : s ∈ U.erase t) (i j : R ⊕ Bool)
    (choices : Fin n → Bool) (b : Bool) :
    (s, b) ∈ B ∪ ((R ∪ {(t, false), (t, true)}).erase
      (activeLabel R t i)).erase (activeLabel R t j) ∪
      (U.erase t).image (fun s => (s, choices s)) ↔ choices s = b := by
  have hnB := (hU s (Finset.mem_erase.mp hs).2 b).1
  have hnR := (hU s (Finset.mem_erase.mp hs).2 b).2
  have hst := (Finset.mem_erase.mp hs).1
  simp [Finset.mem_erase, mem_choice_image, hnB, hnR, Prod.ext_iff, hst, hs, (Finset.mem_erase.mp hs).2]



end CountingMatroid.Analysis.SlotOmissionPatternCharacterization

/-! ### Run record
Newest first. History, not instruction — what this file claims is above.

* 2026-10-09 · proved · characterized every surviving quadratic omission pattern as an explicit completion with two distinct active omissions; proved active squarefreeness, ordinary-slot selection, and the completion cardinality from the original node hypotheses.
-/

end
set_option autoImplicit false

/-! The surviving omitted-label patterns in the slot quadratic are exactly
completions with two distinct active labels omitted. This is the combinatorial
coefficient identification in the transport Hessian. -/

namespace CountingMatroid.Analysis.SlotOmissionPatternCharacterization
end CountingMatroid.Analysis.SlotOmissionPatternCharacterization
open CountingMatroid CountingMatroid.Analysis CountingMatroid.Analysis.SlotOmissionPatternCharacterization
open CountingMatroid.Model
open CountingMatroid.Analysis.OmittedSlotCoefficientFormula
open CountingMatroid.Analysis.OmittedSlotQuadratic
open CountingMatroid.Analysis.OmittedTutteNormalization
open scoped BigOperators
open Classical

/-- PAPER: main.tex:592-601
A quadratic omitted-label pattern exists exactly for two distinct active
omissions, with all other active labels selected and one choice per ordinary slot. -/
lemma solution {n : ℕ} (B R : PairedSet n) (U : Finset (Fin n))
    (hBR : Disjoint B R)
    (hU : ∀ s ∈ U, ∀ b : Bool, (s, b) ∉ B ∧ (s, b) ∉ R)
    (hsize : B.card + R.card + U.card = n + 1)
    (t : Fin n) (ht : t ∈ U) (i j : R ⊕ Bool) (state : PairedSet n) :
    SlotOmissionPattern B R U t (Finsupp.single i 1 + Finsupp.single j 1) state ↔
      i ≠ j ∧ ∃ choices : Fin n → Bool,
        state = B ∪ ((R ∪ {(t, false), (t, true)}).erase (activeLabel R t i)).erase
          (activeLabel R t j) ∪ (U.erase t).image (fun s => (s, choices s)) := by
  rw [pattern_iff_membership B R U hBR hU t ht]
  constructor
  · rintro ⟨hc, hB, hS, ha, ho⟩
    have hij : i ≠ j := by
      intro hij
      subst j
      have hi := ha i
      simp only [Finsupp.add_apply, Finsupp.single_eq_same] at hi
      split_ifs at hi <;> norm_num at hi
    have hactive (k : R ⊕ Bool) : activeLabel R t k ∈ state ↔ k ≠ i ∧ k ≠ j := by
      by_cases hki : k = i
      · subst k
        have hk := ha i
        by_cases hm : activeLabel R t i ∈ state <;>
          simp [Finsupp.add_apply, Finsupp.single_apply, hm, hij] at hk ⊢
      · by_cases hkj : k = j
        · subst k
          have hk := ha j
          by_cases hm : activeLabel R t j ∈ state <;>
            simp [Finsupp.add_apply, Finsupp.single_apply, hm, hij, hij.symm] at hk ⊢
        · have hk := ha k
          by_cases hm : activeLabel R t k ∈ state <;>
            simp [Finsupp.add_apply, Finsupp.single_apply, hki, hkj, hm, eq_comm] at hk ⊢
    let choices : Fin n → Bool := fun s => if (s, true) ∈ state then true else false
    have hchoice (s : Fin n) (hs : s ∈ U.erase t) (b : Bool) :
        (s, b) ∈ state ↔ choices s = b := by
      cases b
      · rw [ho s hs]
        simp [choices]
      · simp [choices]
    refine ⟨hij, choices, ?_⟩
    ext e
    by_cases heB : e ∈ B
    · have heS := hB heB
      simp [heB, heS]
    · by_cases heR : e ∈ R
      · let k : R ⊕ Bool := Sum.inl ⟨e, heR⟩
        have hk : activeLabel R t k = e := rfl
        calc
          (e ∈ state) ↔ k ≠ i ∧ k ≠ j := by simpa only [hk] using hactive k
          _ ↔ _ := by simpa only [hk] using
            (active_completion_membership B R U hBR hU t ht i j k choices).symm
      · by_cases het : e.1 = t
        · let k : R ⊕ Bool := Sum.inr e.2
          have hk : activeLabel R t k = e := Prod.ext het.symm rfl
          calc
            (e ∈ state) ↔ k ≠ i ∧ k ≠ j := by simpa only [hk] using hactive k
            _ ↔ _ := by simpa only [hk] using
              (active_completion_membership B R U hBR hU t ht i j k choices).symm
        · by_cases heU : e.1 ∈ U.erase t
          · calc
              (e ∈ state) ↔ choices e.1 = e.2 := by
                simpa only [Prod.mk.eta] using hchoice e.1 heU e.2
              _ ↔ _ := by simpa only [Prod.mk.eta] using
                (ordinary_completion_membership B R U hU t e.1 heU i j choices e.2).symm
          · have hnU : e.1 ∉ U := by
              intro h
              exact heU (Finset.mem_erase.mpr ⟨het, h⟩)
            have hnS : e ∉ state := by
              intro h
              have hh := hS h
              simp [heB, heR, hnU] at hh
            simp [hnS, heB, heR, Prod.ext_iff, het, mem_choice_image, heU, hnU]
  · rintro ⟨hij, choices, rfl⟩
    refine ⟨active_completion_card B R U hBR hU hsize t ht i j hij choices, ?_, ?_, ?_, ?_⟩
    · intro e he
      exact Finset.mem_union_left _ (Finset.mem_union_left _ he)
    · intro e he
      rcases Finset.mem_union.mp he with he | he
      · rcases Finset.mem_union.mp he with heB | heA
        · exact Finset.mem_union_left _ (Finset.mem_union_left _ heB)
        · have heA' := Finset.mem_of_mem_erase (Finset.mem_of_mem_erase heA)
          rcases Finset.mem_union.mp heA' with heR | heT
          · exact Finset.mem_union_left _ (Finset.mem_union_right _ heR)
          · have het : e.1 = t := by
              rcases Finset.mem_insert.mp heT with he | he
              · exact congrArg Prod.fst he
              · exact congrArg Prod.fst (Finset.mem_singleton.mp he)
            exact Finset.mem_union_right _ (Finset.mem_product.mpr
              ⟨het ▸ ht, Finset.mem_univ _⟩)
      · obtain ⟨s, hs, rfl⟩ := Finset.mem_image.mp he
        exact Finset.mem_union_right _ (Finset.mem_product.mpr
          ⟨(Finset.mem_erase.mp hs).2, Finset.mem_univ _⟩)
    · intro k
      simp only [active_completion_membership B R U hBR hU t ht i j k choices]
      by_cases hki : k = i <;> by_cases hkj : k = j <;>
        simp [Finsupp.add_apply, Finsupp.single_apply, hki, hkj, hij, eq_comm]
    · intro s hs
      rw [ordinary_completion_membership B R U hU t s hs i j choices false,
        ordinary_completion_membership B R U hU t s hs i j choices true]
      cases choices s <;> simp
