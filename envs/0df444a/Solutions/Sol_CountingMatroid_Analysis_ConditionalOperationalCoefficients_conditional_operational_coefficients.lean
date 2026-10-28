-- Prove2me | solution 1 for CountingMatroid.Analysis.ConditionalOperationalCoefficients.conditional_operational_coefficients
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-24T16:15:48.49198+00:00
-- url     : https://prove2.me/submissions/ed4b31b1-f6fd-4ed2-b5c7-2ef2692287b0

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
import Definitions.Def_CountingMatroid_Analysis_ConditionalSelectedStateSum
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
import Definitions.Def_CountingMatroid_Analysis_TwoPairSignatureBound
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
import Theorems.Thm_CountingMatroid_Analysis_ConditionalOccupancyCoefficients_operational_cubic_coefficient
import Theorems.Thm_CountingMatroid_Analysis_ConditionalOccupancyCoefficients_operational_defect_coefficient
import Theorems.Thm_CountingMatroid_Analysis_ConditionalOccupancyCoefficients_operational_transversal_coefficient

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
namespace CountingMatroid.Analysis.ConditionalOperationalCoefficients
end CountingMatroid.Analysis.ConditionalOperationalCoefficients
namespace CountingMatroid.Analysis.SignatureOrthogonalNonpositive
end CountingMatroid.Analysis.SignatureOrthogonalNonpositive
namespace CountingMatroid.Analysis.ConditionalOccupancyCoefficients
end CountingMatroid.Analysis.ConditionalOccupancyCoefficients
section

set_option autoImplicit false

/-! Exact selected-state sums for arbitrary assignments. Tutte normalization,
assigned-label derivatives and pair identification yield the operational
rank weights. The occupancy-to-classification conversion is separate. -/
namespace CountingMatroid.Analysis.ConditionalSelectedStateSum

open CountingMatroid.Model
open CountingMatroid.Analysis.ConditionalDefectCoefficients
open CountingMatroid.Analysis.ConditionalDefectQuadratics
open CountingMatroid.Analysis.ConditionalDefectExtractionCoefficients
open CountingMatroid.Analysis.RankWeightQuadraticSignature
open CountingMatroid.Analysis.OmittedTutteNormalization
open CountingMatroid.Analysis.DefectPartitionQuadraticExtraction
open scoped BigOperators
open Classical





















/-- INTERNAL: Ordinary-pair extraction contributes one precisely at unassigned nonretained pairs.
TEXLINE: main.tex:354-367,403-417 -/
theorem ordinary_exponent_apply {n : ℕ} (σ : Assignment n) (T : Finset (Fin n)) (i : Fin n) :
    ordinaryExponent σ T i = if σ i = none ∧ i ∉ T then 1 else 0 := by
  classical
  simp [ordinaryExponent, ← List.sum_toFinset _ (Finset.nodup_toList _),
    Finsupp.single_apply, assignedPairs, eq_comm]



end CountingMatroid.Analysis.ConditionalSelectedStateSum

/-! ### Run record
Newest first. History, not instruction — what this file claims is above.

* 2026-10-09 · proved · exact normalization through assigned-label conditioning, monomial survival, operational assignment equivalence and finite paired-state coefficient sums; also proved the pair-occupancy and ordinary-exponent evaluations used by the coefficient classifier.
-/

end
set_option autoImplicit false

/-! The exact operational coefficients of the conditioned pair and triple
Hessians. ConditionalSelectedStateSum supplies normalization and the exact
state sums; ConditionalOccupancyCoefficients converts their occupancy tests
to operational defect and transversal totals and excludes cubic occupancy.
Finite matrix-entry enumeration preserves the derivative multiplicities.
This declaration supplies no signature premise. -/

namespace CountingMatroid.Analysis.ConditionalOperationalCoefficients
end CountingMatroid.Analysis.ConditionalOperationalCoefficients
open CountingMatroid CountingMatroid.Analysis CountingMatroid.Analysis.ConditionalOperationalCoefficients

open CountingMatroid.Model
open CountingMatroid.Analysis.ConditionalDefectCoefficients
open CountingMatroid.Analysis.ConditionalDefectQuadratics
open CountingMatroid.Analysis.ConditionalDefectExtractionCoefficients
open CountingMatroid.Analysis.ConditionalSelectedStateSum
open CountingMatroid.Analysis.ConditionalOccupancyCoefficients
open CountingMatroid.Analysis.TwoPairSignatureBound
open CountingMatroid.Analysis.ThreePairSignatureSchur

/-- PAPER: main.tex:403-417
After conditioning, exact exponent extraction gives the operational
transversal and ordered-defect entries of both Hessians. -/
theorem solution (n r : ℕ)
    (M₁ M₂ : Matroid (Fin n)) (o₁ o₂ : IndependenceOracle n) (q : ℚ)
    (hfull : FullGround M₁ M₂) (hr : CommonRank r M₁ M₂)
    (h₁ : ExactOracle M₁ o₁) (h₂ : ExactOracle M₂ o₂)
    (hq : 0 < q) (σ : Assignment n) :
      (∀ (i j : Fin n) (hij : i ≠ j), σ i = none → σ j = none →
        ∀ s t : Fin 2,
          (((conditionedPairPolynomial M₁ M₂ q σ).coeff ((Finsupp.single s 1 + Finsupp.single t 1).mapDomain
              (![i, j] : Fin 2 → Fin n) + ordinaryExponent σ {i, j}) *
            (if s = t then 2 else 1) : ℚ) : ℝ) =
          twoPairMatrix (defectTotal r o₁ o₂ q σ ⟨j, i, hij.symm⟩) (defectTotal r o₁ o₂ q σ ⟨i, j, hij⟩) (transversalTotal r o₁ o₂ q σ) s t) ∧
      (∀ (i j k : Fin n) (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k),
        σ i = none → σ j = none → σ k = none → ∀ s t : Fin 3,
          (((conditionedPairPolynomial M₁ M₂ q σ).coeff ((Finsupp.single s 1 + Finsupp.single t 1).mapDomain
              (![i, j, k] : Fin 3 → Fin n) + Finsupp.single k 1 +
              ordinaryExponent σ {i, j, k}) *
            ((Finsupp.single s 1 + Finsupp.single t 1 : Fin 3 →₀ ℕ) 2 + 1) *
            (if s = t then 2 else 1) : ℚ) : ℝ) =
          threePairMatrix (defectTotal r o₁ o₂ q σ ⟨j, i, hij.symm⟩) (defectTotal r o₁ o₂ q σ ⟨i, j, hij⟩)
            (defectTotal r o₁ o₂ q σ ⟨j, k, hjk⟩) (defectTotal r o₁ o₂ q σ ⟨i, k, hik⟩) (transversalTotal r o₁ o₂ q σ) s t) := by
  classical
  have hD (i j : Fin n) (hij : i ≠ j) (hi : σ i = none) (hj : σ j = none) :=
    operational_defect_coefficient r M₁ M₂ o₁ o₂ q hfull hr h₁ h₂ hq σ
      ⟨i, j, hij⟩ hi hj
  have hT := operational_transversal_coefficient r M₁ M₂ o₁ o₂ q hfull hr h₁ h₂ hq σ
  constructor
  · intro i j hij hi hj s t
    have hA : (conditionedPairPolynomial M₁ M₂ q σ).coeff
        (Finsupp.single i 2 + ordinaryExponent σ {i, j}) =
        defectTotal r o₁ o₂ q σ ⟨j, i, hij.symm⟩ := by
      simpa only [Finset.pair_comm j i] using hD j i hij.symm hj hi
    have hC := hD i j hij hi hj
    have hZ : (conditionedPairPolynomial M₁ M₂ q σ).coeff
        (Finsupp.single i 1 + Finsupp.single j 1 + ordinaryExponent σ {i, j}) =
        transversalTotal r o₁ o₂ q σ := by
      have he : Finsupp.single i 1 + Finsupp.single j 1 + ordinaryExponent σ {i, j} =
          ordinaryExponent σ ∅ := by
        ext x
        by_cases hxi : x = i <;> by_cases hxj : x = j <;>
          simp [ordinary_exponent_apply, hxi, hxj,
            hi, hj, hij, hij.symm]
      rw [he]
      exact hT
    fin_cases s <;> fin_cases t
    all_goals simp only [Finsupp.mapDomain_add, Finsupp.mapDomain_single]
    · norm_num [twoPairMatrix, ← Finsupp.single_add, hA, mul_comm]
    · norm_num [twoPairMatrix, hZ]
    · norm_num [twoPairMatrix]
      rw [add_comm (Finsupp.single j 1) (Finsupp.single i 1)]
      exact hZ
    · norm_num [twoPairMatrix, ← Finsupp.single_add, hC, mul_comm]
  · intro i j k hij hjk hik hi hj hk s t
    have hD3 (a b c : Fin n) (hab : a ≠ b) (hbc : b ≠ c) (hac : a ≠ c)
        (ha : σ a = none) (hb : σ b = none) (hc : σ c = none) :
        (conditionedPairPolynomial M₁ M₂ q σ).coeff
          (Finsupp.single a 1 + Finsupp.single a 1 + Finsupp.single c 1 +
            ordinaryExponent σ {a, b, c}) = defectTotal r o₁ o₂ q σ ⟨b, a, hab.symm⟩ := by
      have he : Finsupp.single a 1 + Finsupp.single a 1 + Finsupp.single c 1 +
          ordinaryExponent σ {a, b, c} =
          Finsupp.single a 2 + ordinaryExponent σ {b, a} := by
        ext x
        by_cases hxa : x = a <;> by_cases hxb : x = b <;> by_cases hxc : x = c <;>
          simp [ordinary_exponent_apply, hxa, hxb, hxc,
            ha, hb, hc, hab, hab.symm, hbc, hbc.symm, hac, hac.symm]
      rw [he]
      exact hD b a hab.symm hb ha
    have hA := hD3 i j k hij hjk hik hi hj hk
    have hC : (conditionedPairPolynomial M₁ M₂ q σ).coeff
        (Finsupp.single j 1 + Finsupp.single j 1 + Finsupp.single k 1 +
          ordinaryExponent σ {i, j, k}) = defectTotal r o₁ o₂ q σ ⟨i, j, hij⟩ := by
      simpa only [Finset.insert_comm] using hD3 j i k hij.symm hik hjk hj hi hk
    have hDK : (conditionedPairPolynomial M₁ M₂ q σ).coeff
        (Finsupp.single i 1 + Finsupp.single k 1 + Finsupp.single k 1 +
          ordinaryExponent σ {i, j, k}) = defectTotal r o₁ o₂ q σ ⟨j, k, hjk⟩ := by
      have hset : ({k, j, i} : Finset (Fin n)) = {i, j, k} := by
        ext x
        simp only [Finset.mem_insert, Finset.mem_singleton]
        tauto
      have h := hD3 k j i hjk.symm hij.symm hik.symm hk hj hi
      rw [hset] at h
      simpa only [add_comm, add_left_comm, add_assoc] using h
    have hEK : (conditionedPairPolynomial M₁ M₂ q σ).coeff
        (Finsupp.single j 1 + Finsupp.single k 1 + Finsupp.single k 1 +
          ordinaryExponent σ {i, j, k}) = defectTotal r o₁ o₂ q σ ⟨i, k, hik⟩ := by
      have hset : ({k, i, j} : Finset (Fin n)) = {i, j, k} := by
        ext x
        simp only [Finset.mem_insert, Finset.mem_singleton]
        tauto
      have h := hD3 k i j hik.symm hij hjk.symm hk hi hj
      rw [hset] at h
      simpa only [add_comm, add_left_comm, add_assoc] using h
    have hZ : (conditionedPairPolynomial M₁ M₂ q σ).coeff
        (Finsupp.single i 1 + Finsupp.single j 1 + Finsupp.single k 1 +
          ordinaryExponent σ {i, j, k}) = transversalTotal r o₁ o₂ q σ := by
      have he : Finsupp.single i 1 + Finsupp.single j 1 + Finsupp.single k 1 +
          ordinaryExponent σ {i, j, k} = ordinaryExponent σ ∅ := by
        ext x
        by_cases hxi : x = i <;> by_cases hxj : x = j <;> by_cases hxk : x = k <;>
          simp [ordinary_exponent_apply, hxi, hxj, hxk,
            hi, hj, hk, hij, hij.symm, hjk, hjk.symm, hik, hik.symm]
      rw [he]
      exact hT
    have hZero : (conditionedPairPolynomial M₁ M₂ q σ).coeff
        (Finsupp.single k 1 + Finsupp.single k 1 + Finsupp.single k 1 +
          ordinaryExponent σ {i, j, k}) = 0 := by
      apply operational_cubic_coefficient r M₁ M₂ o₁ o₂ q hfull hr h₁ h₂ hq σ _ k
      norm_num [Finsupp.single_apply, ordinary_exponent_apply]
    fin_cases s <;> fin_cases t
    all_goals simp only [Finsupp.mapDomain_add, Finsupp.mapDomain_single]
    all_goals norm_num [threePairMatrix, Finsupp.single_apply, Fin.ext_iff]
    · rw [hA]; ring
    · rw [hZ]
    · rw [hDK]; ring
    · rw [add_comm (Finsupp.single j 1) (Finsupp.single i 1), hZ]
    · rw [hC]; ring
    · rw [hEK]; ring
    · rw [add_comm (Finsupp.single k 1) (Finsupp.single i 1), hDK]; ring
    · rw [add_comm (Finsupp.single k 1) (Finsupp.single j 1), hEK]; ring
    · exact hZero
