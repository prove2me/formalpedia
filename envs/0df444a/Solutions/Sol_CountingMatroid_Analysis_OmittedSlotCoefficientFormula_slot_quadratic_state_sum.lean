-- Prove2me | solution 1 for CountingMatroid.Analysis.OmittedSlotCoefficientFormula.slot_quadratic_state_sum
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-24T16:11:45.126152+00:00
-- url     : https://prove2.me/submissions/ead246d6-9fb8-42a1-a32d-f5d10092e57b

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
import Theorems.Thm_CountingMatroid_Analysis_OmittedSlotCoefficientFormula_slot_monomial_coefficient

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

/-!
The omitted-element rank-weight polynomial, expressed using the operational
paired-rank scan. Its coefficients below are identified with the operational
conditional defect totals. These identities do not assert a Hessian signature
or identify this scan with the rank of a matroid.
-/

namespace CountingMatroid.Analysis.OmittedRankWeightPolynomial

open CountingMatroid.Model CountingMatroid.Program
open CountingMatroid.Analysis.ConditionalDefectCoefficients
open scoped BigOperators
open Classical



/-- INTERNAL: Each omitted label occurs once, and every selected label has
exponent zero.
TEXLINE: main.tex:571-625 -/
theorem omitted_exponent_apply {n : ℕ} (state : PairedSet n) (e : PairedGround n) :
    omittedExponent state e = if e ∈ state then 0 else 1 := by
  classical
  simp [omittedExponent]



















end CountingMatroid.Analysis.OmittedRankWeightPolynomial

end

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

/-- INTERNAL: Expand the operational slot quadratic as a finite sum of rank weights over exactly the surviving omitted-label patterns.
TEXLINE: main.tex:584-601 -/
lemma solution {n : ℕ} (r : ℕ) (o₁ o₂ : IndependenceOracle n)
    (q : ℚ) (B R : PairedSet n) (U : Finset (Fin n))
    (hU : ∀ t ∈ U, ∀ b : Bool, (t, b) ∉ B ∧ (t, b) ∉ R)
    (t : Fin n) (ht : t ∈ U) (d : R ⊕ Bool →₀ ℕ) :
    (operationalSlotQuadratic r o₁ o₂ q B R U t).coeff d =
      ∑ state : PairedSet n, if SlotOmissionPattern B R U t d state then
        q ^ (n - (CountingMatroid.Model.Subroutines.pairedRank r o₁ o₂ state).val) else 0 := by
  classical
  have hdiff (l : List (PairedGround n)) {β : Type} (S : Finset β)
      (f : β → MvPolynomial (PairedGround n) ℚ) :
      l.foldl (fun p e => MvPolynomial.pderiv e p) (∑ z ∈ S, f z) =
        ∑ z ∈ S, l.foldl (fun p e => MvPolynomial.pderiv e p) (f z) := by
    induction l generalizing f with
    | nil => rfl
    | cons e l ih =>
      simp only [List.foldl_cons, map_sum]
      exact ih _
  have hextract (l : List (Fin n)) {β : Type} (S : Finset β)
      (f : β → MvPolynomial (PairedGround n) ℚ) :
      l.foldl (fun p s => extractLabel (s, false) p) (∑ z ∈ S, f z) =
        ∑ z ∈ S, l.foldl (fun p s => extractLabel (s, false) p) (f z) := by
    induction l generalizing f with
    | nil => rfl
    | cons e l ih =>
      simp only [List.foldl_cons]
      have hstep : extractLabel (e, false) (∑ z ∈ S, f z) =
          ∑ z ∈ S, extractLabel (e, false) (f z) := by
        simp [extractLabel, linearSubstitution, map_sum]
      rw [hstep, ih]
  have hzero (l : List (PairedGround n)) :
      l.foldl (fun p e => MvPolynomial.pderiv e p) 0 = (0 : MvPolynomial (PairedGround n) ℚ) := by
    induction l with
    | nil => rfl
    | cons e l ih => simpa using ih
  have hzero' (l : List (Fin n)) :
      l.foldl (fun p s => extractLabel (s, false) p) 0 = (0 : MvPolynomial (PairedGround n) ℚ) := by
    induction l with
    | nil => rfl
    | cons e l ih => simpa [extractLabel, linearSubstitution] using ih
  have hlabel (state : PairedSet n) :
      OmittedRankWeightPolynomial.omittedExponent state = labelExponent (Finset.univ \ state) := by
    ext e
    rw [label_exponent_apply, OmittedRankWeightPolynomial.omitted_exponent_apply]
    simp
  unfold operationalSlotQuadratic OmittedRankWeightPolynomial.omittedRankPolynomial
  simp only [differentiateLabels, hdiff, linearSubstitution, map_sum]
  change (linearSubstitution (activeSubstitution R t)
    ((U.erase t).toList.foldl (fun p s => extractLabel (s, false) p)
      (∑ state : PairedSet n, linearSubstitution (slotSubstitution R U t)
        ((fixedOmissions B R U).toList.foldl (fun p e => MvPolynomial.pderiv e p)
          (if state.card = n then MvPolynomial.monomial (OmittedRankWeightPolynomial.omittedExponent state)
            (q ^ (n - (CountingMatroid.Model.Subroutines.pairedRank r o₁ o₂ state).val)) else 0))))).coeff d = _
  rw [hextract]
  simp only [linearSubstitution, map_sum, MvPolynomial.coeff_sum]
  apply Finset.sum_congr rfl
  intro state _
  by_cases hc : state.card = n
  · rw [if_pos hc, hlabel]
    change (linearSubstitution (activeSubstitution R t)
      ((U.erase t).toList.foldl (fun p s => extractLabel (s, false) p)
        (linearSubstitution (slotSubstitution R U t)
          (differentiateLabels (fixedOmissions B R U)
            (MvPolynomial.monomial (labelExponent (Finset.univ \ state))
              (q ^ (n - (CountingMatroid.Model.Subroutines.pairedRank r o₁ o₂ state).val))))))).coeff d = _
    rw [slot_monomial_coefficient B R U hU t ht]
    simp only [SlotOmissionPattern, hc, true_and]
  · rw [if_neg hc, hzero]
    simp only [map_zero, hzero', MvPolynomial.coeff_zero]
    rw [if_neg (by rintro ⟨h, _⟩; exact hc h)]
