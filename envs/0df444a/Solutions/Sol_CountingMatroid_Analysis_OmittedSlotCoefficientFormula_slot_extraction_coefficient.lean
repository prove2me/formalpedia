-- Prove2me | solution 1 for CountingMatroid.Analysis.OmittedSlotCoefficientFormula.slot_extraction_coefficient
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-24T15:54:49.572731+00:00
-- url     : https://prove2.me/submissions/ee48c409-e58f-439c-917c-3fdf35a0d22c

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
import Theorems.Thm_CountingMatroid_Analysis_ConditionalDefectExtractionCoefficients_derivative_list_coefficient
import Theorems.Thm_CountingMatroid_Analysis_ConditionalDefectExtractionCoefficients_masked_substitution_coefficient
import Theorems.Thm_CountingMatroid_Analysis_ConditionalDefectExtractionCoefficients_restriction_coefficient
import Theorems.Thm_CountingMatroid_Analysis_OmittedSlotCoefficientFormula_extract_label_coefficient

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

/-! Exact coefficient extraction for the omitted-slot quadratic. The final
state sum retains the full omitted-label pattern condition; identifying those
patterns with the transport completion predicates is a separate combinatorial
obligation. No signature inequality is asserted here. -/
namespace CountingMatroid.Analysis.OmittedSlotCoefficientFormula
open CountingMatroid.Model
open CountingMatroid.Analysis.RankWeightQuadraticSignature
open CountingMatroid.Analysis.ConditionalDefectExtractionCoefficients
open CountingMatroid.Analysis.OmittedSlotQuadratic
open CountingMatroid.Analysis.OmittedTutteNormalization
open scoped BigOperators
open Classical



/-- INTERNAL: A sum of single exponents vanishes off its variable list. -/
lemma single_list_sum_zero {α : Type} [DecidableEq α] (l : List α)
    (j : α) (hj : j ∉ l) :
    ((l.map (fun i => (Finsupp.single i 1 : α →₀ ℕ))).sum) j = 0 := by
  induction l with
  | nil => simp
  | cons i l ih =>
    simp only [List.mem_cons, not_or] at hj
    simp [hj.1, ih hj.2]

/-- INTERNAL: Distinct paired-label extractions shift the requested coefficient by one in each extracted variable.
TEXLINE: main.tex:587-589 -/
lemma extract_labels_coefficient {n : ℕ} (l : List (PairedGround n))
    (hl : l.Nodup) (g : MvPolynomial (PairedGround n) ℚ)
    (d : PairedGround n →₀ ℕ) (hd : ∀ j ∈ l, d j = 0) :
    (l.foldl (fun p j => extractLabel j p) g).coeff d =
      g.coeff (d + (l.map (fun j => Finsupp.single j 1)).sum) := by
  induction l generalizing g with
  | nil => simp
  | cons j l ih =>
    have hnodup := List.nodup_cons.mp hl
    rw [List.foldl_cons, ih hnodup.2 _ (fun s hs => hd s (by simp [hs]))]
    rw [extract_label_coefficient j _ _ (by
      rw [Finsupp.add_apply, hd j (by simp), single_list_sum_zero l j hnodup.1])]
    congr 1
    simp only [List.map_cons, List.sum_cons]
    ac_rfl














end CountingMatroid.Analysis.OmittedSlotCoefficientFormula

end
set_option autoImplicit false

/-! Exact coefficient extraction for the omitted-slot quadratic. The final
state sum retains the full omitted-label pattern condition; identifying those
patterns with the transport completion predicates is a separate combinatorial
obligation. No signature inequality is asserted here. -/
namespace CountingMatroid.Analysis.OmittedSlotCoefficientFormula
end CountingMatroid.Analysis.OmittedSlotCoefficientFormula
open CountingMatroid CountingMatroid.Analysis CountingMatroid.Analysis.OmittedSlotCoefficientFormula
open CountingMatroid.Model
open CountingMatroid.Analysis.RankWeightQuadraticSignature
open CountingMatroid.Analysis.ConditionalDefectExtractionCoefficients
open CountingMatroid.Analysis.OmittedSlotQuadratic
open CountingMatroid.Analysis.OmittedTutteNormalization
open scoped BigOperators
open Classical

/-- INTERNAL: Exact coefficient formula for the omitted-slot operations on an arbitrary input polynomial.
TEXLINE: main.tex:584-601 -/
lemma solution {n : ℕ} (g : MvPolynomial (PairedGround n) ℚ)
    (B R : PairedSet n) (U : Finset (Fin n))
    (hU : ∀ t ∈ U, ∀ b : Bool, (t, b) ∉ B ∧ (t, b) ∉ R)
    (t : Fin n) (ht : t ∈ U) (d : R ⊕ Bool →₀ ℕ) :
    (linearSubstitution (activeSubstitution R t)
      ((U.erase t).toList.foldl (fun p s => extractLabel (s, false) p)
        (linearSubstitution (slotSubstitution R U t)
          (differentiateLabels (fixedOmissions B R U) g)))).coeff d =
      ∑ v ∈ (differentiateLabels (fixedOmissions B R U)
        g).support,
        if (∀ e ∈ v.support, e ∈ R ∨ e.1 ∈ U) ∧
          v.mapDomain (mergedLabel R t) =
            d.mapDomain (activeLabel R t) + ordinarySlotExponent U t then
          g.coeff
            (v + labelExponent (fixedOmissions B R U)) else 0 := by
  classical
  have hf : Function.Injective (activeLabel R t) := by
    intro i j hij
    cases i with
    | inl i =>
      cases j with
      | inl j => exact congrArg Sum.inl (Subtype.ext hij)
      | inr b =>
        have he : (i : PairedGround n) = (t, b) := hij
        exact False.elim ((hU t ht b).2 (he ▸ i.property))
    | inr b =>
      cases j with
      | inl j =>
        have he : (j : PairedGround n) = (t, b) := hij.symm
        exact False.elim ((hU t ht b).2 (he ▸ j.property))
      | inr c => exact congrArg Sum.inr (congrArg Prod.snd hij)
  have hweights : activeSubstitution R t =
      fun s j => if s = activeLabel R t j then (1 : ℚ) else 0 := by
    funext s j
    cases j <;> rfl
  have hzero : ∀ s ∈ (U.erase t).toList,
      (d.mapDomain (activeLabel R t)) (s, false) = 0 := by
    intro s hs
    have hst := Finset.mem_erase.mp (Finset.mem_toList.mp hs)
    apply Finsupp.mapDomain_of_notMem_range
    rintro ⟨j, hj⟩
    cases j with
    | inl j =>
      exact (hU s hst.2 false).2 (hj ▸ j.property)
    | inr b =>
      exact hst.1 (congrArg Prod.fst hj).symm
  rw [hweights, restriction_coefficient _ hf]
  have hfold (g : MvPolynomial (PairedGround n) ℚ) :
      (U.erase t).toList.foldl (fun p s => extractLabel (s, false) p) g =
      ((U.erase t).toList.map (fun s => (s, false))).foldl (fun p e => extractLabel e p) g := by
    rw [List.foldl_map]
  rw [hfold, extract_labels_coefficient _ ((Finset.nodup_toList _).map
    (by intro i j h; exact congrArg Prod.fst h)) _ _ (by
      intro e he
      obtain ⟨s, hs, rfl⟩ := List.mem_map.mp he
      exact hzero s hs)]
  simp only [List.map_map]
  change (linearSubstitution (slotSubstitution R U t)
    (differentiateLabels (fixedOmissions B R U)
      g)).coeff
    (d.mapDomain (activeLabel R t) + ordinarySlotExponent U t) = _
  have hmask : slotSubstitution R U t =
      fun e f => if (e ∈ R ∨ e.1 ∈ U) ∧ mergedLabel R t e = f then (1 : ℚ) else 0 := by
    funext e f
    unfold slotSubstitution mergedLabel
    by_cases he : e ∈ R <;> by_cases het : e.1 = t <;>
      by_cases heu : e.1 ∈ U <;> simp_all
  rw [hmask, masked_substitution_coefficient]
  apply Finset.sum_congr rfl
  intro v hv
  by_cases ha : (∀ e ∈ v.support, e ∈ R ∨ e.1 ∈ U) ∧
      v.mapDomain (mergedLabel R t) = d.mapDomain (activeLabel R t) + ordinarySlotExponent U t
  · rw [if_pos ha, if_pos ha]
    unfold differentiateLabels
    rw [derivative_list_coefficient _ (Finset.nodup_toList _) _ _ (by
      intro e he
      have hC := Finset.mem_toList.mp he
      have hn : e ∉ R ∧ e.1 ∉ U := by
        simp only [fixedOmissions, Finset.mem_sdiff, Finset.mem_univ, true_and,
          Finset.mem_union] at hC
        simp_all
      by_contra hne
      exact (ha.1 e (Finsupp.mem_support_iff.mpr hne)).elim hn.1 hn.2)]
    congr 1
    simp [labelExponent]
  · rw [if_neg ha, if_neg ha]
