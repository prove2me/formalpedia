-- Prove2me | solution 1 for CountingMatroid.Analysis.ConditionalSelectedStateSum.conditioned_state_coefficient
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-24T16:11:14.288447+00:00
-- url     : https://prove2.me/submissions/a8f33667-24a1-4781-a07b-a7ea59b8fe73

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
import Theorems.Thm_CountingMatroid_Analysis_ConditionalSelectedStateSum_condition_selected_monomial_coefficient
import Theorems.Thm_CountingMatroid_Analysis_ConditionalSelectedStateSum_conditioned_selected_sum
import Theorems.Thm_CountingMatroid_Analysis_ConditionalSelectedStateSum_selected_labels_respects
import Theorems.Thm_CountingMatroid_Analysis_PairedRankValue_paired_rank_eq_eRk

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
set_option autoImplicit false

/-! Exact selected-state sums for arbitrary assignments. Tutte normalization,
assigned-label derivatives and pair identification yield the operational
rank weights. The occupancy-to-classification conversion is separate. -/
namespace CountingMatroid.Analysis.ConditionalSelectedStateSum
end CountingMatroid.Analysis.ConditionalSelectedStateSum
open CountingMatroid CountingMatroid.Analysis CountingMatroid.Analysis.ConditionalSelectedStateSum

open CountingMatroid.Model
open CountingMatroid.Analysis.ConditionalDefectCoefficients
open CountingMatroid.Analysis.ConditionalDefectQuadratics
open CountingMatroid.Analysis.ConditionalDefectExtractionCoefficients
open CountingMatroid.Analysis.RankWeightQuadraticSignature
open CountingMatroid.Analysis.OmittedTutteNormalization
open CountingMatroid.Analysis.DefectPartitionQuadraticExtraction
open scoped BigOperators
open Classical

/-- INTERNAL: Identify every conditioned coefficient with a finite operational rank-weight state sum.
TEXLINE: main.tex:354-367,403-417 -/
theorem solution {n : ℕ} (r : ℕ) (M₁ M₂ : Matroid (Fin n)) (o₁ o₂ : IndependenceOracle n)
    (q : ℚ) (hfull : FullGround M₁ M₂) (hr : CommonRank r M₁ M₂)
    (h₁ : ExactOracle M₁ o₁) (h₂ : ExactOracle M₂ o₂) (hq : 0 < q)
    (σ : Assignment n) (d : Fin n →₀ ℕ) :
    (conditionedPairPolynomial M₁ M₂ q σ).coeff d =
      ∑ A : PairedSet n, if A.card = n ∧ Respects σ A ∧
          (labelExponent (A \ (selectedLabelList σ).toFinset)).mapDomain Prod.fst = d then
        q ^ (n - (CountingMatroid.Model.Subroutines.pairedRank r o₁ o₂ A).val) else 0 := by
  classical
  rw [conditioned_selected_sum]
  have hadd (l : List (Fin n)) (f : PairedSet n → MvPolynomial (PairedGround n) ℚ) :
      l.foldl (fun p i => MvPolynomial.pderiv (i, (σ i).getD false) p) (∑ A, f A) =
        ∑ A, l.foldl (fun p i => MvPolynomial.pderiv (i, (σ i).getD false) p) (f A) := by
    induction l generalizing f with
    | nil => rfl
    | cons i l ih => simp only [List.foldl_cons, map_sum, ih]
  unfold conditionSelected
  rw [hadd]
  simp only [linearSubstitution, map_sum, MvPolynomial.coeff_sum]
  apply Finset.sum_congr rfl
  intro A _
  by_cases hc : A.card = n
  · rw [if_pos hc]
    change (conditionSelected σ (MvPolynomial.monomial (labelExponent A) _)).coeff d = _
    rw [condition_selected_monomial_coefficient]
    have hpat : ((selectedLabelList σ).toFinset ⊆ A ∧
        (∀ e ∈ A \ (selectedLabelList σ).toFinset, σ e.1 = none) ∧
          (labelExponent (A \ (selectedLabelList σ).toFinset)).mapDomain Prod.fst = d) ↔
        Respects σ A ∧ (labelExponent (A \ (selectedLabelList σ).toFinset)).mapDomain Prod.fst = d := by
      rw [← and_assoc, selected_labels_respects]
    simp only [hpat]
    simp only [hc, true_and]
    split_ifs
    · rw [CountingMatroid.Analysis.PairedRankValue.paired_rank_eq_eRk r M₁ M₂ o₁ o₂ hfull hr h₁ h₂]
      have hle : ((pairedMatroid M₁ M₂).eRk (A : Set (PairedGround n))).toNat ≤ n := by
        apply ENat.toNat_le_of_le_natCast
        simpa only [Set.encard_coe_eq_coe_finsetCard, hc] using
          (pairedMatroid M₁ M₂).eRk_le_encard (A : Set (PairedGround n))
      rw [show q ^ n = q ^ (n - ((pairedMatroid M₁ M₂).eRk (A : Set (PairedGround n))).toNat) *
        q ^ ((pairedMatroid M₁ M₂).eRk (A : Set (PairedGround n))).toNat by
          rw [← pow_add, Nat.sub_add_cancel hle]]
      field_simp [pow_ne_zero _ hq.ne']
    · rfl
  · rw [if_neg hc, if_neg (by rintro ⟨h, _⟩; exact hc h)]
    have hz (l : List (Fin n)) :
        l.foldl (fun p i => MvPolynomial.pderiv (i, (σ i).getD false) p)
          (0 : MvPolynomial (PairedGround n) ℚ) = 0 := by
      induction l with
      | nil => rfl
      | cons i l ih => simp only [List.foldl_cons, map_zero, ih]
    simp [hz]
