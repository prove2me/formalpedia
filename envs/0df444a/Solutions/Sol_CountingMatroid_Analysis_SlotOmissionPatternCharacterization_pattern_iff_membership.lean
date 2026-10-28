-- Prove2me | solution 1 for CountingMatroid.Analysis.SlotOmissionPatternCharacterization.pattern_iff_membership
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-24T15:54:44.449336+00:00
-- url     : https://prove2.me/submissions/46a65dc4-1a71-4dc5-b353-7649521fca36

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
import Theorems.Thm_CountingMatroid_Analysis_SlotOmissionPatternCharacterization_active_label_injective
import Theorems.Thm_CountingMatroid_Analysis_SlotOmissionPatternCharacterization_merged_exponent_ordinary
import Theorems.Thm_CountingMatroid_Analysis_SlotOmissionPatternCharacterization_merged_preimage_active

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

/-! Exact normalization and rank correspondence for the omitted-label Tutte
slice and its slot extraction. These identities do not assume coefficient
identification for the final transport Hessian. -/
namespace CountingMatroid.Analysis.OmittedTutteNormalization
open CountingMatroid.Model
open CountingMatroid.Analysis.RankWeightQuadraticSignature
open CountingMatroid.Analysis.ConditionalDefectExtractionCoefficients
open CountingMatroid.Analysis.DefectPartitionQuadraticExtraction
open scoped BigOperators



/-- INTERNAL: Evaluate a squarefree selected-label exponent. -/
lemma label_exponent_apply {α : Type} [DecidableEq α] (A : Finset α) (e : α) :
    labelExponent A e = if e ∈ A then 1 else 0 := by
  classical
  simp [labelExponent, Finsupp.single_apply, eq_comm]

















end CountingMatroid.Analysis.OmittedTutteNormalization

end

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





/-- INTERNAL: The merged exponent at an active label remains squarefree. -/
lemma merged_exponent_active {n : ℕ} (B R D : PairedSet n) (U : Finset (Fin n))
    (hU : ∀ s ∈ U, ∀ b : Bool, (s, b) ∉ B ∧ (s, b) ∉ R)
    (t : Fin n) (hD : ∀ e ∈ D, e ∈ R ∨ e.1 ∈ U) (k : R ⊕ Bool) :
    ((labelExponent D).mapDomain (mergedLabel R t)) (activeLabel R t k) =
      if activeLabel R t k ∈ D then 1 else 0 := by
  rw [labelExponent, Finsupp.mapDomain_finsetSum]
  simp only [Finsupp.mapDomain_single, Finsupp.finset_sum_apply, Finsupp.single_apply]
  trans ∑ e ∈ D, if e = activeLabel R t k then (1 : ℕ) else 0
  · apply Finset.sum_congr rfl
    intro e he
    simp only [merged_preimage_active B R U hU t e (hD e he) k]
  · simp [eq_comm]

/-- INTERNAL: The ordinary extracted exponent is one at each false-label
representative and zero elsewhere. -/
lemma ordinary_exponent_apply {n : ℕ} (U : Finset (Fin n)) (t : Fin n)
    (e : PairedGround n) : ordinarySlotExponent U t e =
      if e.1 ∈ U.erase t ∧ e.2 = false then 1 else 0 := by
  have heq : ordinarySlotExponent U t =
      ∑ s ∈ U.erase t, (Finsupp.single (s, false) 1 : PairedGround n →₀ ℕ) := by
    simp [ordinarySlotExponent]
  rw [heq]
  rcases e with ⟨s, b⟩
  cases b <;> simp [Finsupp.single_apply, Prod.ext_iff]





/-- INTERNAL: Active labels are never among the fixed omissions. -/
lemma active_label_not_fixed {n : ℕ} (B R : PairedSet n) (U : Finset (Fin n))
    (t : Fin n) (ht : t ∈ U) (k : R ⊕ Bool) :
    activeLabel R t k ∉ fixedOmissions B R U := by
  cases k with
  | inl k => simp [activeLabel, fixedOmissions, k.property]
  | inr b => simp [activeLabel, fixedOmissions, ht]













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

/-- INTERNAL: The exponent test is equivalent to selecting fixed labels,
selecting the complement of the active exponents, and one label per ordinary slot.
TEXLINE: main.tex:584-601 -/
lemma solution {n : ℕ} (B R : PairedSet n) (U : Finset (Fin n))
    (hBR : Disjoint B R)
    (hU : ∀ s ∈ U, ∀ b : Bool, (s, b) ∉ B ∧ (s, b) ∉ R)
    (t : Fin n) (ht : t ∈ U) (d : R ⊕ Bool →₀ ℕ) (state : PairedSet n) :
    SlotOmissionPattern B R U t d state ↔
      state.card = n ∧ B ⊆ state ∧ state ⊆ B ∪ R ∪ U.product Finset.univ ∧
      (∀ k, (if activeLabel R t k ∈ state then 0 else 1) = d k) ∧
      (∀ s ∈ U.erase t, (s, false) ∈ state ↔ (s, true) ∉ state) := by
  have hf := active_label_injective B R U hU t ht
  have hordinary (s : Fin n) (hs : s ∈ U.erase t) (b : Bool) :
      (s, b) ∉ fixedOmissions B R U := by
    simp [fixedOmissions, (Finset.mem_erase.mp hs).2]
  have hrange (s : Fin n) (hs : s ∈ U.erase t) :
      (s, false) ∉ Set.range (activeLabel R t) := by
    rintro ⟨k, hk⟩
    cases k with
    | inl k => exact (hU s (Finset.mem_erase.mp hs).2 false).2 (hk ▸ k.property)
    | inr b => exact (Finset.mem_erase.mp hs).1 (congrArg Prod.fst hk).symm
  have hactord (k : R ⊕ Bool) : ordinarySlotExponent U t (activeLabel R t k) = 0 := by
    rw [ordinary_exponent_apply]
    cases k with
    | inl k =>
      apply if_neg
      rintro ⟨hk, hb⟩
      have he : (k : PairedGround n) = ((k : PairedGround n).1, false) := by
        exact Prod.ext rfl hb
      exact (hU k.val.1 (Finset.mem_erase.mp hk).2 false).2 (he ▸ k.property)
    | inr b => simp [activeLabel]
  constructor
  · rintro ⟨hc, hC, hD, heq⟩
    have hB : B ⊆ state := by
      intro e he
      by_contra hn
      have heC : e ∉ fixedOmissions B R U := by simp [fixedOmissions, he]
      have hd := hD e (by simp [hn, heC])
      rcases hd with hd | hd
      · exact Finset.disjoint_left.mp hBR he hd
      · exact (hU e.1 hd e.2).1 (by simpa using he)
    have hS : state ⊆ B ∪ R ∪ U.product Finset.univ := by
      intro e he
      by_contra hn
      have heC : e ∈ fixedOmissions B R U := by
        simpa only [fixedOmissions, Finset.mem_sdiff, Finset.mem_univ, true_and] using hn
      have hout := hC heC
      simpa [he] using hout
    refine ⟨hc, hB, hS, ?_, ?_⟩
    · intro k
      have hk := DFunLike.congr_fun heq (activeLabel R t k)
      rw [merged_exponent_active B R _ U hU t hD k,
        Finsupp.add_apply, Finsupp.mapDomain_apply hf, hactord, add_zero] at hk
      have hn := active_label_not_fixed B R U t ht k
      simpa [hn] using hk
    · intro s hs
      have hsEq := DFunLike.congr_fun heq (s, false)
      rw [merged_exponent_ordinary B R _ U hU t s hs, Finsupp.add_apply,
        Finsupp.mapDomain_of_notMem_range _ _ (hrange s hs),
        show ordinarySlotExponent U t (s, false) = 1 by simp [ordinary_exponent_apply, hs],
        zero_add] at hsEq
      have hn₀ := hordinary s hs false
      have hn₁ := hordinary s hs true
      simp only [Finset.mem_sdiff, Finset.mem_univ, true_and, hn₀, hn₁, not_false_eq_true,
        and_true] at hsEq
      by_cases ha : (s, false) ∈ state <;> by_cases hb : (s, true) ∈ state <;>
        simp only [ha, hb, not_true_eq_false, not_false_eq_true, ite_true, ite_false] at hsEq ⊢ <;> omega
  · rintro ⟨hc, hB, hS, ha, ho⟩
    have hC : fixedOmissions B R U ⊆ Finset.univ \ state := by
      intro e he
      have hn : e ∉ B ∪ R ∪ U.product Finset.univ := by
        simpa [fixedOmissions] using he
      simp only [Finset.mem_sdiff, Finset.mem_univ, true_and]
      exact fun h => hn (hS h)
    have hD : ∀ e ∈ (Finset.univ \ state) \ fixedOmissions B R U,
        e ∈ R ∨ e.1 ∈ U := by
      intro e he
      have hnS : e ∉ state := (Finset.mem_sdiff.mp (Finset.mem_sdiff.mp he).1).2
      have hnotC := (Finset.mem_sdiff.mp he).2
      have heT : e ∈ B ∪ R ∪ U.product Finset.univ := by
        by_contra hn
        exact hnotC (by
          simpa only [fixedOmissions, Finset.mem_sdiff, Finset.mem_univ, true_and] using hn)
      rcases Finset.mem_union.mp heT with heBR | heU
      · rcases Finset.mem_union.mp heBR with heB | heR
        · exact False.elim (hnS (hB heB))
        · exact Or.inl heR
      · exact Or.inr (Finset.mem_product.mp heU).1
    refine ⟨hc, hC, hD, ?_⟩
    ext e
    by_cases heR : e ∈ R
    · let k : R ⊕ Bool := Sum.inl ⟨e, heR⟩
      have hk : activeLabel R t k = e := rfl
      rw [← hk, merged_exponent_active B R _ U hU t hD k,
        Finsupp.add_apply, Finsupp.mapDomain_apply hf, hactord, add_zero]
      have hn := active_label_not_fixed B R U t ht k
      simpa [hn] using ha k
    · by_cases het : e.1 = t
      · let k : R ⊕ Bool := Sum.inr e.2
        have hk : activeLabel R t k = e := Prod.ext het.symm rfl
        rw [← hk, merged_exponent_active B R _ U hU t hD k,
          Finsupp.add_apply, Finsupp.mapDomain_apply hf, hactord, add_zero]
        have hn := active_label_not_fixed B R U t ht k
        simpa [hn] using ha k
      · by_cases heo : e.1 ∈ U.erase t ∧ e.2 = false
        · obtain ⟨hs, hb⟩ := heo
          have he : e = (e.1, false) := Prod.ext rfl hb
          rw [he, merged_exponent_ordinary B R _ U hU t e.1 hs, Finsupp.add_apply,
            Finsupp.mapDomain_of_notMem_range _ _ (hrange e.1 hs),
            show ordinarySlotExponent U t (e.1, false) = 1 by simp [ordinary_exponent_apply, hs],
            zero_add]
          have hn₀ := hordinary e.1 hs false
          have hn₁ := hordinary e.1 hs true
          simp only [Finset.mem_sdiff, Finset.mem_univ, true_and, hn₀, hn₁,
            not_false_eq_true, and_true]
          have ho' := ho e.1 hs
          by_cases h₀ : (e.1, false) ∈ state <;>
            by_cases h₁ : (e.1, true) ∈ state <;>
            simp [h₀, h₁] at ho' ⊢
        · rw [Finsupp.add_apply, ordinary_exponent_apply, if_neg heo]
          have hnr : e ∉ Set.range (activeLabel R t) := by
            rintro ⟨k, hk⟩
            cases k with
            | inl k => exact heR (hk ▸ k.property)
            | inr b => exact het (congrArg Prod.fst hk).symm
          rw [Finsupp.mapDomain_of_notMem_range _ _ hnr, zero_add]
          apply Finsupp.mapDomain_of_not_mem_image_support
          rintro ⟨f, hf, hfe⟩
          have hfD : f ∈ (Finset.univ \ state) \ fixedOmissions B R U := by
            simpa [Finsupp.mem_support_iff, label_exponent_apply] using hf
          have hfallowed := hD f hfD
          by_cases hfa : f ∈ R ∨ f.1 = t
          · have hfe' : f = e := by simpa [mergedLabel, hfa] using hfe
            rcases hfa with hfR | hft
            · exact heR (hfe' ▸ hfR)
            · exact het (hfe' ▸ hft)
          · have hfe' : (f.1, false) = e := by simpa [mergedLabel, hfa] using hfe
            apply heo
            refine ⟨?_, (congrArg Prod.snd hfe').symm⟩
            rw [← congrArg Prod.fst hfe']
            exact Finset.mem_erase.mpr ⟨(not_or.mp hfa).2,
              hfallowed.resolve_left (not_or.mp hfa).1⟩
