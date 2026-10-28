-- Prove2me | solution 1 for CountingMatroid.Analysis.DefectPartitionQuadraticExtraction.selected_triple_last_diagonal_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-24T15:32:46.05599+00:00
-- url     : https://prove2.me/submissions/90c7bd1c-6eb9-4ecb-b8e8-5fa3ecaecd76

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
import Definitions.Def_CountingMatroid_Analysis_CubicTensorContraction
import Definitions.Def_CountingMatroid_Analysis_DefectPartitionQuadraticConstruction
import Definitions.Def_CountingMatroid_Analysis_FirstPhaseFailure
import Definitions.Def_CountingMatroid_Analysis_InitialMultipliersGood
import Definitions.Def_CountingMatroid_Analysis_LorentzianDirectionalSignature
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
import Mathlib.Algebra.MvPolynomial.PDeriv
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
import Theorems.Thm_CountingMatroid_Analysis_LinearPolynomialChainRule_linear_aeval_pderiv
import Theorems.Thm_CountingMatroid_Analysis_TwoLabelDerivativeNilpotence_derivative_degree_le
import Theorems.Thm_CountingMatroid_Analysis_TwoLabelDerivativeNilpotence_tutte_label_squarefree
import Theorems.Thm_CountingMatroid_Analysis_TwoLabelDerivativeNilpotence_two_label_derivative_cube

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
section


set_option autoImplicit false

/-! Squarefree label variables in the Tutte polynomial imply that three
derivatives in the sum of two label directions vanish. This uses no
operational rank or partition identification. -/

namespace CountingMatroid.Analysis.TwoLabelDerivativeNilpotence

open CountingMatroid.Analysis.RankWeightQuadraticSignature
open scoped BigOperators

/-- INTERNAL: Partial derivatives commute, including repeated variables.
TEXLINE: main.tex:354-373 -/
theorem derivative_commute {α : Type} (x y : α) (p : MvPolynomial α ℚ) :
    MvPolynomial.pderiv x (MvPolynomial.pderiv y p) =
      MvPolynomial.pderiv y (MvPolynomial.pderiv x p) := by
  classical
  ext d
  simp only [MvPolynomial.coeff_pderiv, Finsupp.add_apply, Finsupp.single_apply]
  by_cases h : x = y
  · subst y; rfl
  · simp [h, Ne.symm h, add_comm, add_left_comm]
    ring









/-- INTERNAL: Homogenizing derivatives preserve the two-label cubic
nilpotence of the Tutte polynomial.
TEXLINE: main.tex:354-373,412-417 -/
theorem tutte_two_label_derivative_cube {α : Type} [Fintype α]
    (N : Matroid α) (q : ℚ) (x y : α) (m : ℕ) :
    let p := (MvPolynomial.pderiv none)^[m] (tuttePolynomial N q)
    let D := fun g : MvPolynomial (Option α) ℚ =>
      MvPolynomial.pderiv (some x) g + MvPolynomial.pderiv (some y) g
    D (D (D p)) = 0 := by
  have hdegree (z : α) (l : ℕ) :
      ((MvPolynomial.pderiv none)^[l] (tuttePolynomial N q)).degreeOf (some z) ≤ 1 := by
    induction l with
    | zero => exact tutte_label_squarefree N q z
    | succ l ih =>
      rw [Function.iterate_succ_apply']
      exact (derivative_degree_le none (some z) _).trans ih
  exact two_label_derivative_cube (some x) (some y) _ (hdegree x m) (hdegree y m)

/-- INTERNAL: A substitution column supported at one source variable
transports its partial derivative exactly.
TEXLINE: main.tex:369-373,412-417 -/
theorem linear_substitution_derivative_single {α β : Type} [Fintype α] [Fintype β] [DecidableEq α]
    (a : α → β → ℚ) (s : α) (t : β)
    (hcolumn : ∀ u, a u t = if u = s then 1 else 0) (p : MvPolynomial α ℚ) :
    MvPolynomial.pderiv t (linearSubstitution a p) =
      linearSubstitution a (MvPolynomial.pderiv s p) := by
  classical
  unfold linearSubstitution
  rw [CountingMatroid.Analysis.LinearPolynomialChainRule.linear_aeval_pderiv]
  simp_rw [hcolumn]
  simp

end CountingMatroid.Analysis.TwoLabelDerivativeNilpotence

end

section


set_option autoImplicit false

/-!
The concrete selected-element quadratic used in the three-pair inequality.
It is constructed from the homogenized Tutte polynomial by the paper's
actual derivative and substitution sequence. Its membership in the allowed
closure operations is proved separately from its operational coefficients.
Its last diagonal Hessian entry is proved to vanish directly from squarefree
label exponents, without any operational coefficient identity.
The remaining coefficient identities need the paired-rank correspondence
and extraction calculation; it does not assume a signature theorem. The
existing paired-rank correspondence and extraction-calculus lemmas live in
modules that import this module. Reusing them here requires separating the
construction declarations above the operational extraction theorem from
that theorem, so those dependencies no longer import their consumer.
-/

namespace CountingMatroid.Analysis.DefectPartitionQuadraticExtraction

open CountingMatroid.Model
open CountingMatroid.Analysis.RankWeightQuadraticSignature
open CountingMatroid.Analysis.ThreePairSignatureSchur
open CountingMatroid.Analysis.TwoLabelDerivativeNilpotence





















/-- INTERNAL: Differentiating a merged pair sums the two label derivatives.
TEXLINE: main.tex:403-407 -/
theorem pair_substitution_derivative {n : ℕ} (j : Fin n)
    (p : MvPolynomial (Option (PairedGround n)) ℚ) :
    MvPolynomial.pderiv j (linearSubstitution pairSubstitution p) =
      linearSubstitution pairSubstitution
        (MvPolynomial.pderiv (some (j, false)) p +
          MvPolynomial.pderiv (some (j, true)) p) := by
  classical
  unfold linearSubstitution
  rw [CountingMatroid.Analysis.LinearPolynomialChainRule.linear_aeval_pderiv]
  congr 1
  simp [pairSubstitution, Fintype.sum_prod_type, Finset.sum_add_distrib, add_comm]

/-- INTERNAL: Extraction at an ordinary pair commutes with differentiation
at a distinct retained pair.
TEXLINE: main.tex:408-417 -/
theorem extract_one_derivative_commute {n : ℕ} (j k : Fin n) (hjk : j ≠ k)
    (p : MvPolynomial (Fin n) ℚ) :
    MvPolynomial.pderiv k (extractOne j p) = extractOne j (MvPolynomial.pderiv k p) := by
  classical
  unfold extractOne
  rw [linear_substitution_derivative_single _ k k]
  · rw [derivative_commute k j]
  · intro s
    by_cases hs : s = j
    · subst s; simp [hjk]
    · simp [hs]



end CountingMatroid.Analysis.DefectPartitionQuadraticExtraction

end
set_option autoImplicit false

/-!
The concrete selected-element quadratic used in the three-pair inequality.
It is constructed from the homogenized Tutte polynomial by the paper's
actual derivative and substitution sequence. Its membership in the allowed
closure operations is proved separately from its operational coefficients.
Its last diagonal Hessian entry is proved to vanish directly from squarefree
label exponents, without any operational coefficient identity.
The remaining coefficient identities need the paired-rank correspondence
and extraction calculation; it does not assume a signature theorem. The
existing paired-rank correspondence and extraction-calculus lemmas live in
modules that import this module. Reusing them here requires separating the
construction declarations above the operational extraction theorem from
that theorem, so those dependencies no longer import their consumer.
-/

namespace CountingMatroid.Analysis.DefectPartitionQuadraticExtraction
end CountingMatroid.Analysis.DefectPartitionQuadraticExtraction
open CountingMatroid CountingMatroid.Analysis CountingMatroid.Analysis.DefectPartitionQuadraticExtraction

open CountingMatroid.Model
open CountingMatroid.Analysis.RankWeightQuadraticSignature
open CountingMatroid.Analysis.ThreePairSignatureSchur
open CountingMatroid.Analysis.TwoLabelDerivativeNilpotence

/-- INTERNAL: The last diagonal Hessian entry vanishes: the merged pair k
has at most two selected labels, and this entry takes three k derivatives.
TEXLINE: main.tex:412-417 -/
theorem solution {n : ℕ} (M₁ M₂ : Matroid (Fin n))
    (q : ℚ) (i j k : Fin n) :
    hessian (selectedTripleQuadratic M₁ M₂ q i j k) 2 2 = 0 := by
  classical
  let f := linearSubstitution pairSubstitution
    ((MvPolynomial.pderiv none)^[n] (tuttePolynomial (pairedMatroid M₁ M₂) q))
  let ordinary := (List.finRange n).filter (fun s => s ≠ i ∧ s ≠ j ∧ s ≠ k)
  let cubic := ordinary.foldl (fun g s => extractOne s g) f
  have hf : MvPolynomial.pderiv k (MvPolynomial.pderiv k (MvPolynomial.pderiv k f)) = 0 := by
    dsimp only [f]
    rw [pair_substitution_derivative, pair_substitution_derivative, pair_substitution_derivative]
    have hnil := tutte_two_label_derivative_cube (pairedMatroid M₁ M₂) q
      (k, false) (k, true) n
    dsimp only at hnil
    rw [hnil]
    simp [linearSubstitution]
  have hfold (l : List (Fin n)) (hl : ∀ s ∈ l, s ≠ k)
      (g : MvPolynomial (Fin n) ℚ)
      (hg : MvPolynomial.pderiv k (MvPolynomial.pderiv k (MvPolynomial.pderiv k g)) = 0) :
      MvPolynomial.pderiv k (MvPolynomial.pderiv k (MvPolynomial.pderiv k
        (l.foldl (fun p s => extractOne s p) g))) = 0 := by
    induction l generalizing g with
    | nil => exact hg
    | cons s l ih =>
      apply ih (fun t ht => hl t (by simp [ht]))
      rw [extract_one_derivative_commute s k (hl s (by simp)),
        extract_one_derivative_commute s k (hl s (by simp)),
        extract_one_derivative_commute s k (hl s (by simp)), hg]
      simp [extractOne, linearSubstitution]
  have hc : MvPolynomial.pderiv k (MvPolynomial.pderiv k (MvPolynomial.pderiv k cubic)) = 0 :=
    hfold ordinary (by
      intro s hs
      simp only [ordinary, List.mem_filter, List.mem_finRange, true_and, decide_eq_true_eq] at hs
      exact hs.2.2) f hf
  have hcolumn : ∀ s, tripleSubstitution i j k s 2 = if s = k then 1 else 0 := by
    intro s
    simp [tripleSubstitution, show (2 : Fin 3) ≠ 0 by decide, show (2 : Fin 3) ≠ 1 by decide]
  have hrestrict := linear_substitution_derivative_single
    (tripleSubstitution i j k) k (2 : Fin 3) hcolumn
  change ((MvPolynomial.constantCoeff
    (MvPolynomial.pderiv 2 (MvPolynomial.pderiv 2
      (MvPolynomial.C (q ^ n / (n.factorial : ℚ)) *
        linearSubstitution (tripleSubstitution i j k) (MvPolynomial.pderiv k cubic)))) : ℚ) : ℝ) = 0
  simp only [MvPolynomial.pderiv_C_mul]
  rw [hrestrict, hrestrict, hc]
  simp [linearSubstitution]
