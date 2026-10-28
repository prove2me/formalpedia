-- Prove2me | solution 1 for CountingMatroid.Analysis.OmittedTutteNormalization.normalized_omitted_polynomial
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-24T16:11:45.008537+00:00
-- url     : https://prove2.me/submissions/2f1312f3-e481-4153-b693-945eb38c80ea

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
import Theorems.Thm_CountingMatroid_Analysis_OmittedTutteNormalization_dual_paired_rank
import Theorems.Thm_CountingMatroid_Analysis_OmittedTutteNormalization_normalized_tutte_coefficient

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





/-- PAPER: main.tex:360-364
The normalized homogenizer derivative gives the half-ground rank-weight polynomial. -/
lemma normalized_tutte_polynomial {α : Type} [Fintype α] [DecidableEq α]
    (N : Matroid α) (q : ℚ) (m : ℕ) (hcard : Fintype.card α = 2 * m) :
    MvPolynomial.C (q ^ m / (m.factorial : ℚ)) *
      linearSubstitution (fun s t => if s = some t then 1 else 0)
        ((MvPolynomial.pderiv none)^[m] (tuttePolynomial N q)) =
      ∑ A : Finset α, if A.card = m then
        MvPolynomial.monomial (labelExponent A)
          (q ^ m * (q ^ (N.eRk (A : Set α)).toNat)⁻¹) else 0 := by
  classical
  ext d
  rw [normalized_tutte_coefficient N q m hcard, MvPolynomial.coeff_sum]
  apply Finset.sum_congr rfl
  intro A _
  by_cases hc : A.card = m <;> simp [hc, MvPolynomial.coeff_monomial]











end CountingMatroid.Analysis.OmittedTutteNormalization

end
set_option autoImplicit false

/-! Exact normalization and rank correspondence for the omitted-label Tutte
slice and its slot extraction. These identities do not assume coefficient
identification for the final transport Hessian. -/
namespace CountingMatroid.Analysis.OmittedTutteNormalization
end CountingMatroid.Analysis.OmittedTutteNormalization
open CountingMatroid CountingMatroid.Analysis CountingMatroid.Analysis.OmittedTutteNormalization
open CountingMatroid.Model
open CountingMatroid.Analysis.RankWeightQuadraticSignature
open CountingMatroid.Analysis.ConditionalDefectExtractionCoefficients
open CountingMatroid.Analysis.DefectPartitionQuadraticExtraction
open scoped BigOperators

/-- PAPER: main.tex:354-367
The normalized dual Tutte slice is exactly the operational omitted-label polynomial. -/
lemma solution {n : ℕ} (r : ℕ) (M₁ M₂ : Matroid (Fin n))
    (o₁ o₂ : IndependenceOracle n) (q : ℚ) (hfull : FullGround M₁ M₂)
    (hr : CommonRank r M₁ M₂) (h₁ : ExactOracle M₁ o₁)
    (h₂ : ExactOracle M₂ o₂) (hq : 0 < q) :
    MvPolynomial.C (q ^ n / (n.factorial : ℚ)) *
      linearSubstitution OmittedSlotQuadratic.omitHomogenizer
        ((MvPolynomial.pderiv none)^[n] (tuttePolynomial (pairedMatroid M₁ M₂)✶ q)) =
      OmittedRankWeightPolynomial.omittedRankPolynomial r o₁ o₂ q := by
  classical
  have hsub : OmittedSlotQuadratic.omitHomogenizer (n := n) =
      fun s t => if s = some t then 1 else 0 := by
    funext s t
    cases s <;> simp [OmittedSlotQuadratic.omitHomogenizer]
  rw [hsub, normalized_tutte_polynomial _ q n (by simp [PairedGround, Nat.mul_comm])]
  unfold OmittedRankWeightPolynomial.omittedRankPolynomial
  apply Fintype.sum_bijective (fun A : PairedSet n => Finset.univ \ A)
    (show Function.Bijective (fun A : PairedSet n => Finset.univ \ A) from
      (show Function.Involutive (fun A : PairedSet n => Finset.univ \ A) from by
        intro A; ext e; simp).bijective)
  intro A
  have hc : (Finset.univ \ A : PairedSet n).card = n ↔ A.card = n := by
    rw [Finset.card_sdiff_of_subset (Finset.subset_univ _), Finset.card_univ]
    have hle := Finset.card_le_univ A
    simp only [PairedGround, Fintype.card_prod, Fintype.card_bool, Fintype.card_fin] at *
    omega
  by_cases ha : A.card = n
  · rw [if_pos ha, if_pos (hc.mpr ha)]
    have he : labelExponent A =
        OmittedRankWeightPolynomial.omittedExponent (Finset.univ \ A : PairedSet n) := by
      ext e
      rw [label_exponent_apply, OmittedRankWeightPolynomial.omitted_exponent_apply]
      simp
    rw [he]
    congr 1
    have hcompl : (Finset.univ \ (Finset.univ \ A) : PairedSet n) = A := by ext e; simp
    have hrk := dual_paired_rank r M₁ M₂ o₁ o₂ hfull hr h₁ h₂
      (Finset.univ \ A) (hc.mpr ha)
    rw [hcompl] at hrk
    rw [hrk]
    have hle : (CountingMatroid.Model.Subroutines.pairedRank r o₁ o₂ (Finset.univ \ A)).val ≤ n := by
      rw [← hrk]
      apply ENat.toNat_le_of_le_natCast
      simpa only [Set.encard_coe_eq_coe_finsetCard, ha] using
        ((pairedMatroid M₁ M₂)✶).eRk_le_encard (A : Set (PairedGround n))
    have hpow : q ^ n = q ^ (n - (CountingMatroid.Model.Subroutines.pairedRank r o₁ o₂ (Finset.univ \ A)).val) *
        q ^ (CountingMatroid.Model.Subroutines.pairedRank r o₁ o₂ (Finset.univ \ A)).val := by
      rw [← pow_add, Nat.sub_add_cancel hle]
    rw [hpow]
    have hne : q ^ (CountingMatroid.Model.Subroutines.pairedRank r o₁ o₂ (Finset.univ \ A)).val ≠ 0 :=
      pow_ne_zero _ hq.ne'
    field_simp
  · rw [if_neg ha, if_neg (by simpa only [hc] using ha)]
