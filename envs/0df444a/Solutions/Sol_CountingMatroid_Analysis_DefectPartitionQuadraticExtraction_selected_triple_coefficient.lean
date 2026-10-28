-- Prove2me | solution 1 for CountingMatroid.Analysis.DefectPartitionQuadraticExtraction.selected_triple_coefficient
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-24T15:32:35.439116+00:00
-- url     : https://prove2.me/submissions/9e7345b9-bd01-4c3e-803b-2538a2f9dd1e

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
import Theorems.Thm_CountingMatroid_Analysis_ConditionalDefectExtractionCoefficients_restriction_coefficient

namespace CountingMatroid.Interface
end CountingMatroid.Interface
namespace CountingMatroid.Meta
end CountingMatroid.Meta
namespace Arlib
end Arlib
namespace CountingMatroid.Analysis.TransversalRankBridge
end CountingMatroid.Analysis.TransversalRankBridge
namespace CountingMatroid.Analysis.GreedyRankCorrect
end CountingMatroid.Analysis.GreedyRankCorrect
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
namespace CountingMatroid.Analysis.DefectPartitionQuadraticExtraction
end CountingMatroid.Analysis.DefectPartitionQuadraticExtraction
namespace CountingMatroid.Analysis.ConditionalOperationalCoefficients
end CountingMatroid.Analysis.ConditionalOperationalCoefficients
namespace CountingMatroid.Analysis.SignatureOrthogonalNonpositive
end CountingMatroid.Analysis.SignatureOrthogonalNonpositive
namespace CountingMatroid.Analysis.ConditionalOccupancyCoefficients
end CountingMatroid.Analysis.ConditionalOccupancyCoefficients
namespace CountingMatroid.Analysis.PairedRankValue
end CountingMatroid.Analysis.PairedRankValue
section

set_option autoImplicit false

/-! Exact coefficient calculus for the existing conditioned descendants.
The calculations below account for ordinary-pair extraction and retained
coordinate relabelling; operational rank-weight identities are separate. -/

namespace CountingMatroid.Analysis.ConditionalDefectExtractionCoefficients

open CountingMatroid.Model
open CountingMatroid.Analysis.ConditionalDefectCoefficients
open CountingMatroid.Analysis.ConditionalDefectQuadratics
open CountingMatroid.Analysis.RankWeightQuadraticSignature
open CountingMatroid.Analysis.DefectPartitionQuadraticExtraction
open scoped BigOperators

/-- INTERNAL: Deleting one variable preserves coefficients with zero exponent
in that variable. TEXLINE: main.tex:369-373 -/
private theorem deletion_coefficient {α : Type} [Fintype α] [DecidableEq α] (j : α)
    (g : MvPolynomial α ℚ) (d : α →₀ ℕ) (hd : d j = 0) :
    (linearSubstitution (fun s t => if s = j then 0 else if s = t then 1 else 0) g).coeff d =
      g.coeff d := by
  classical
  let f : {s : α // s ≠ j} → α := Subtype.val
  have hf : Function.Injective f := Subtype.val_injective
  have hsub : linearSubstitution
      (fun s t => if s = j then 0 else if s = t then 1 else 0) g =
      MvPolynomial.rename f (MvPolynomial.killCompl hf g) := by
    have hh : (MvPolynomial.aeval (fun s => ∑ t,
        MvPolynomial.C (if s = j then 0 else if s = t then 1 else 0 : ℚ) *
          MvPolynomial.X t)) = (MvPolynomial.rename f).comp (MvPolynomial.killCompl hf) := by
      apply MvPolynomial.algHom_ext
      intro s
      by_cases hs : s = j
      · subst s
        simp [MvPolynomial.killCompl, f]
      · have hr : s ∈ Set.range f := ⟨⟨s, hs⟩, rfl⟩
        simp [MvPolynomial.killCompl, hs, f]
        exact ((Equiv.ofInjective f hf).apply_symm_apply ⟨s, hr⟩).symm |> congrArg Subtype.val
    exact DFunLike.congr_fun hh g
  rw [hsub]
  let e := d.comapDomain f hf.injOn
  have hsupp : (↑d.support : Set α) ⊆ Set.range f := by
    intro s hs
    refine ⟨⟨s, ?_⟩, rfl⟩
    intro hsj
    subst s
    simp [hd] at hs
  have he : e.mapDomain f = d := d.mapDomain_comapDomain f hf hsupp
  rw [← he, MvPolynomial.coeff_rename_mapDomain f hf, MvPolynomial.coeff_killCompl]


/-- INTERNAL: Differentiating and deleting extracts exponent exactly one,
with no multiplicity. TEXLINE: main.tex:369-373 -/
theorem extract_one_coefficient {n : ℕ} (j : Fin n)
    (g : MvPolynomial (Fin n) ℚ) (d : Fin n →₀ ℕ) (hd : d j = 0) :
    (extractOne j g).coeff d = g.coeff (d + Finsupp.single j 1) := by
  unfold extractOne
  rw [deletion_coefficient j _ d hd, MvPolynomial.coeff_pderiv]
  simp [hd]

/-- INTERNAL: An extraction exponent vanishes outside its variable list. -/
private theorem single_list_sum_zero {α : Type} [DecidableEq α] (l : List α)
    (j : α) (hj : j ∉ l) :
    ((l.map (fun i => (Finsupp.single i 1 : α →₀ ℕ))).sum) j = 0 := by
  induction l with
  | nil => simp
  | cons i l ih =>
    simp only [List.mem_cons, not_or] at hj
    simp [hj.1, ih hj.2]

/-- INTERNAL: Distinct ordinary-pair extractions shift the requested
coefficient by one in every extracted variable. TEXLINE: main.tex:408-417 -/
theorem extract_list_coefficient {n : ℕ} (l : List (Fin n))
    (hl : l.Nodup) (g : MvPolynomial (Fin n) ℚ)
    (d : Fin n →₀ ℕ) (hd : ∀ j ∈ l, d j = 0) :
    (l.foldl (fun p j => extractOne j p) g).coeff d =
      g.coeff (d + (l.map (fun j => Finsupp.single j 1)).sum) := by
  induction l generalizing g with
  | nil => simp
  | cons j l ih =>
    have hnodup := List.nodup_cons.mp hl
    rw [List.foldl_cons, ih hnodup.2 _ (fun s hs => hd s (by simp [hs]))]
    rw [extract_one_coefficient j _ _ (by
      rw [Finsupp.add_apply, hd j (by simp), single_list_sum_zero l j hnodup.1])]
    congr 1
    simp only [List.map_cons, List.sum_cons]
    ac_rfl



































end CountingMatroid.Analysis.ConditionalDefectExtractionCoefficients

end
set_option autoImplicit false

/-!
The selected triple quadratic has the paper's exact operational Hessian.
Construction provides homogeneity and the vanishing last diagonal entry.
The remaining entries follow from the empty-assignment instance of the
proved conditioned operational coefficient identities, with the ordinary
pair extractions and final derivative multiplicity computed explicitly.
-/

namespace CountingMatroid.Analysis.DefectPartitionQuadraticExtraction
end CountingMatroid.Analysis.DefectPartitionQuadraticExtraction
open CountingMatroid CountingMatroid.Analysis CountingMatroid.Analysis.DefectPartitionQuadraticExtraction

open CountingMatroid.Model
open CountingMatroid.Analysis.RankWeightQuadraticSignature
open CountingMatroid.Analysis.ThreePairSignatureSchur
open CountingMatroid.Analysis.TwoLabelDerivativeNilpotence
open CountingMatroid.Analysis.ConditionalDefectCoefficients
open CountingMatroid.Analysis.ConditionalDefectQuadratics
open CountingMatroid.Analysis.ConditionalDefectExtractionCoefficients

/-- INTERNAL: Compute the selected triple coefficient before the operational
occupancy conversion, including the final derivative multiplicity.
TEXLINE: main.tex:412-417 -/
theorem solution {n : ℕ} (M₁ M₂ : Matroid (Fin n)) (q : ℚ)
    (i j k : Fin n) (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k)
    (d : Fin 3 →₀ ℕ) :
    (selectedTripleQuadratic M₁ M₂ q i j k).coeff d =
      (q ^ n / (n.factorial : ℚ)) *
        (linearSubstitution pairSubstitution
          ((MvPolynomial.pderiv none)^[n] (tuttePolynomial (pairedMatroid M₁ M₂) q))).coeff
          (d.mapDomain (![i, j, k] : Fin 3 → Fin n) + Finsupp.single k 1 +
            ((((List.finRange n).filter (fun s => s ≠ i ∧ s ≠ j ∧ s ≠ k)).map
              (fun s => Finsupp.single s 1)).sum)) * (d 2 + 1) := by
  classical
  have hf : Function.Injective (![i, j, k] : Fin 3 → Fin n) := by
    intro s t h
    fin_cases s <;> fin_cases t <;> simp_all
  have hweights : tripleSubstitution i j k =
      fun s t => if s = (![i, j, k] : Fin 3 → Fin n) t then 1 else 0 := by
    funext s t
    fin_cases t <;> by_cases hi : s = i <;> by_cases hj : s = j <;>
      by_cases hk : s = k <;> simp_all [tripleSubstitution]
  unfold selectedTripleQuadratic
  rw [MvPolynomial.coeff_C_mul, hweights, restriction_coefficient _ hf,
    MvPolynomial.coeff_pderiv]
  have hkval : (d.mapDomain (![i, j, k] : Fin 3 → Fin n)) k = d 2 := by
    simpa using Finsupp.mapDomain_apply hf d 2
  rw [hkval, extract_list_coefficient _ ((List.nodup_finRange n).filter _)]
  · ring
  · intro s hs
    simp only [List.mem_filter, List.mem_finRange, true_and, decide_eq_true_eq] at hs
    have hzero : (d.mapDomain (![i, j, k] : Fin 3 → Fin n)) s = 0 := by
      apply Finsupp.mapDomain_of_notMem_range
      rintro ⟨t, ht⟩
      fin_cases t <;> simp_all
    simp [Finsupp.add_apply, hzero, hs.2.2]
