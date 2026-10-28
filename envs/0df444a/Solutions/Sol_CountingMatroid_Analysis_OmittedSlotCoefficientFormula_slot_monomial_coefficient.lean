-- Prove2me | solution 1 for CountingMatroid.Analysis.OmittedSlotCoefficientFormula.slot_monomial_coefficient
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-24T16:09:47.541557+00:00
-- url     : https://prove2.me/submissions/df618983-a0a8-4f62-a706-477da00f7d2a

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
import Theorems.Thm_CountingMatroid_Analysis_OmittedSlotCoefficientFormula_slot_extraction_coefficient

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

/-- INTERNAL: The omitted-slot extraction of a squarefree monomial has multiplicity one and the displayed surviving-pattern test.
TEXLINE: main.tex:584-601 -/
lemma solution {n : ℕ} (B R : PairedSet n) (U : Finset (Fin n))
    (hU : ∀ t ∈ U, ∀ b : Bool, (t, b) ∉ B ∧ (t, b) ∉ R)
    (t : Fin n) (ht : t ∈ U) (d : R ⊕ Bool →₀ ℕ)
    (A : PairedSet n) (c : ℚ) :
    (linearSubstitution (activeSubstitution R t)
      ((U.erase t).toList.foldl (fun p s => extractLabel (s, false) p)
        (linearSubstitution (slotSubstitution R U t)
          (differentiateLabels (fixedOmissions B R U)
            (MvPolynomial.monomial (labelExponent A) c))))).coeff d =
      if (fixedOmissions B R U) ⊆ A ∧
        (∀ e ∈ A \ fixedOmissions B R U, e ∈ R ∨ e.1 ∈ U) ∧
        (labelExponent (A \ fixedOmissions B R U)).mapDomain (mergedLabel R t) =
          d.mapDomain (activeLabel R t) + ordinarySlotExponent U t then c else 0 := by
  classical
  rw [slot_extraction_coefficient _ B R U hU t ht]
  let C := fixedOmissions B R U
  let v₀ := labelExponent (A \ C)
  have hsupport (S : PairedSet n) (e : PairedGround n) :
      e ∈ (labelExponent S).support ↔ e ∈ S := by
    simp [Finsupp.mem_support_iff, label_exponent_apply]
  have hvzero : ∀ e ∈ C.toList, v₀ e = 0 := by
    intro e he
    simp [v₀, label_exponent_apply, Finset.mem_toList.mp he]
  change (∑ v ∈ (differentiateLabels C (MvPolynomial.monomial (labelExponent A) c)).support,
      if (∀ e ∈ v.support, e ∈ R ∨ e.1 ∈ U) ∧
          v.mapDomain (mergedLabel R t) = d.mapDomain (activeLabel R t) + ordinarySlotExponent U t then
        (MvPolynomial.monomial (labelExponent A) c).coeff (v + labelExponent C) else 0) =
    if C ⊆ A ∧ (∀ e ∈ A \ C, e ∈ R ∨ e.1 ∈ U) ∧
        v₀.mapDomain (mergedLabel R t) = d.mapDomain (activeLabel R t) + ordinarySlotExponent U t then c else 0
  by_cases hCA : C ⊆ A
  · have hexp : v₀ + labelExponent C = labelExponent A := by
      ext e
      simp only [Finsupp.add_apply, v₀, label_exponent_apply, Finset.mem_sdiff]
      by_cases heC : e ∈ C
      · have heA := hCA heC
        simp [heC, heA]
      · by_cases heA : e ∈ A <;> simp [heC, heA]
    have heq (v : PairedGround n →₀ ℕ) :
        v + labelExponent C = labelExponent A ↔ v = v₀ := by
      rw [← hexp]
      exact add_right_cancel_iff
    have heq' (v : PairedGround n →₀ ℕ) : labelExponent A = v + labelExponent C ↔ v = v₀ :=
      eq_comm.trans (heq v)
    simp_rw [MvPolynomial.coeff_monomial, heq']
    rw [Finset.sum_eq_single v₀]
    · simp only [ite_and, if_pos hCA, v₀, hsupport, ite_true]
    · intro v hv hne
      simp [hne]
    · intro hnot
      have hd := MvPolynomial.notMem_support_iff.mp hnot
      unfold differentiateLabels at hd
      rw [derivative_list_coefficient C.toList (Finset.nodup_toList _) _ v₀ hvzero] at hd
      have hsum : (C.toList.map (fun e => Finsupp.single e 1)).sum = labelExponent C := by
        simp [labelExponent]
      rw [hsum, hexp, MvPolynomial.coeff_monomial, if_pos rfl] at hd
      simp [hd]
  · have hfalse (v : PairedGround n →₀ ℕ) : v + labelExponent C ≠ labelExponent A := by
      intro hv
      apply hCA
      intro e heC
      have he := DFunLike.congr_fun hv e
      rw [Finsupp.add_apply, label_exponent_apply C, if_pos heC,
        label_exponent_apply A] at he
      by_contra hn
      rw [if_neg hn] at he
      omega
    simp only [MvPolynomial.coeff_monomial]
    simp_rw [if_neg (hfalse _).symm]
    simp only [ite_self, Finset.sum_const_zero]
    rw [if_neg (by rintro ⟨h, _⟩; exact hCA h)]
