-- Prove2me | solution 1 for CountingMatroid.Analysis.ConditionalSelectedStateSum.conditioned_selected_sum
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-24T15:55:31.416743+00:00
-- url     : https://prove2.me/submissions/df334671-65e8-4273-8960-c955e9d0ec42

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
import Theorems.Thm_CountingMatroid_Analysis_ConditionalDefectExtractionCoefficients_restriction_coefficient
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

/-! Exact normalization and rank correspondence for the omitted-label Tutte
slice and its slot extraction. These identities do not assume coefficient
identification for the final transport Hessian. -/
namespace CountingMatroid.Analysis.OmittedTutteNormalization
open CountingMatroid.Model
open CountingMatroid.Analysis.RankWeightQuadraticSignature
open CountingMatroid.Analysis.ConditionalDefectExtractionCoefficients
open CountingMatroid.Analysis.DefectPartitionQuadraticExtraction
open scoped BigOperators









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

/-- INTERNAL: Move the proved Tutte normalization through assigned-label derivatives and pair substitution.
TEXLINE: main.tex:354-367,403-417 -/
theorem solution {n : ℕ} (M₁ M₂ : Matroid (Fin n)) (q : ℚ) (σ : Assignment n) :
    conditionedPairPolynomial M₁ M₂ q σ =
      conditionSelected σ (∑ A : PairedSet n, if A.card = n then
        MvPolynomial.monomial (labelExponent A)
          (q ^ n * (q ^ ((pairedMatroid M₁ M₂).eRk (A : Set (PairedGround n))).toNat)⁻¹)
        else 0) := by
  classical
  have hproj (g : MvPolynomial (Option (PairedGround n)) ℚ) (e : PairedGround n) :
      project (MvPolynomial.pderiv (some e) g) = MvPolynomial.pderiv e (project g) := by
    ext d
    simp only [project, restriction_coefficient _ (Option.some_injective _), MvPolynomial.coeff_pderiv]
    rw [Finsupp.mapDomain_apply (Option.some_injective (PairedGround n))]
    congr 2
    rw [Finsupp.mapDomain_add, Finsupp.mapDomain_single]
  have hfold (l : List (Fin n)) (g : MvPolynomial (Option (PairedGround n)) ℚ) :
      project (l.foldl (fun p i => MvPolynomial.pderiv (some (i, (σ i).getD false)) p) g) =
        l.foldl (fun p i => MvPolynomial.pderiv (i, (σ i).getD false) p) (project g) := by
    induction l generalizing g with
    | nil => rfl
    | cons i l ih => simp only [List.foldl_cons, ih, hproj]
  have hC (l : List (Fin n)) (g : MvPolynomial (PairedGround n) ℚ) (c : ℚ) :
      l.foldl (fun p i => MvPolynomial.pderiv (i, (σ i).getD false) p) (MvPolynomial.C c * g) =
        MvPolynomial.C c * l.foldl (fun p i => MvPolynomial.pderiv (i, (σ i).getD false) p) g := by
    induction l generalizing g with
    | nil => rfl
    | cons i l ih => simp only [List.foldl_cons, MvPolynomial.pderiv_C_mul, ih]
  have hsub (g : MvPolynomial (Option (PairedGround n)) ℚ) :
      linearSubstitution (conditionedPairSubstitution σ) g =
        linearSubstitution (fun e t => if σ e.1 = none ∧ e.1 = t then 1 else 0) (project g) := by
    unfold project linearSubstitution
    rw [MvPolynomial.comp_aeval_apply]
    congr 1
    congr 1
    funext s
    cases s <;> simp [conditionedPairSubstitution]
  rw [← normalized_tutte_polynomial (pairedMatroid M₁ M₂) q n (by simp [PairedGround, Nat.mul_comm])]
  unfold conditionedPairPolynomial conditionSelected
  rw [hsub, hfold, hC]
  simp [linearSubstitution, project]
