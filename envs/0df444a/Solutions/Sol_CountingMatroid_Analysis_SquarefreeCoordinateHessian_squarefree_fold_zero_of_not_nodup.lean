-- Prove2me | solution 1 for CountingMatroid.Analysis.SquarefreeCoordinateHessian.squarefree_fold_zero_of_not_nodup
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-24T15:27:17.111521+00:00
-- url     : https://prove2.me/submissions/55f9ccc1-5390-4789-99ba-3335a7b4c573

import Definitions.Def_CountingMatroid_Analysis_CubicTensorContraction
import Definitions.Def_CountingMatroid_Analysis_LorentzianDirectionalSignature
import Definitions.Def_CountingMatroid_Analysis_QuadraticNonpositiveHyperplane
import Definitions.Def_CountingMatroid_Analysis_RankWeightSupportExchange
import Definitions.Def_CountingMatroid_Analysis_SquarefreeCoordinateHessian
import Mathlib.Algebra.MvPolynomial.PDeriv
import Mathlib.Analysis.InnerProductSpace.Spectrum
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Combinatorics.Matroid.Rank.ENat
import Mathlib.Data.Finsupp.Multiset
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Multiset.Count
import Mathlib.Data.Real.Basic
import Mathlib.LinearAlgebra.Matrix.BilinearForm
import Mathlib.LinearAlgebra.QuadraticForm.Signature
import Mathlib.RingTheory.MvPolynomial.EulerIdentity
import Mathlib.RingTheory.MvPolynomial.Homogeneous
import Mathlib.Tactic
import Mathlib.Tactic.Positivity
import Mathlib.Topology.Algebra.Order.Field
import Mathlib.Topology.Instances.Rat
import Mathlib.Topology.Instances.Real.Lemmas
import Theorems.Thm_CountingMatroid_Analysis_SquarefreeCoordinateHessian_coordinate_monomial_zero_of_count

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
namespace CountingMatroid.Analysis.SquarefreeFullDerivative
end CountingMatroid.Analysis.SquarefreeFullDerivative
section


set_option autoImplicit false

/-! The subset exponent description of the rank-weight polynomial support.
The exchange condition depends only on the subsets, not on matroid ranks. -/

namespace CountingMatroid.Analysis.RankWeightSupportExchange

open scoped BigOperators
open LorentzianDirectionalSignature





/-- INTERNAL: Each label coordinate is the subset's membership indicator. -/
theorem subsetExponent_some {α : Type} [Fintype α] [DecidableEq α]
    (A : Finset α) (a : α) : subsetExponent A (some a) = if a ∈ A then 1 else 0 := by
  classical
  simp [subsetExponent, Finsupp.single_apply, eq_comm]



/-- INTERNAL: Each summand of the polynomial is a single encoded monomial. -/
theorem rank_weight_term_monomial {α : Type} [Fintype α] [DecidableEq α]
    (A : Finset α) (c : ℚ) :
    MvPolynomial.C c * MvPolynomial.X none ^ (Fintype.card α - A.card) *
      (∏ a ∈ A, MvPolynomial.X (some a)) =
      MvPolynomial.monomial (subsetExponent A) c := by
  rw [MvPolynomial.C_mul_X_pow_eq_monomial]
  have hprod : (∏ a ∈ A, MvPolynomial.X (some a) : MvPolynomial (Option α) ℚ) =
      MvPolynomial.monomial (∑ a ∈ A, Finsupp.single (some a) 1) 1 := by
    rw [MvPolynomial.monomial_sum_one]
    rfl
  rw [hprod, MvPolynomial.monomial_mul, mul_one]
  rfl





end CountingMatroid.Analysis.RankWeightSupportExchange

/-! ### Run record
Newest first. History, not instruction — what this file claims is above.

* 2026-10-09 · proved · identified the support with all subset exponents and proved unit exchange by insert, erase, and swap; the argument needs only positive coefficients and no matroid exchange or rank-signature theorem.
-/

end
set_option autoImplicit false

/-! Coordinate differentiation of a homogeneous polynomial whose label
variables are squarefree reduces its constant Hessian to a residual matrix.
The matrix records the selected labels and the number of homogenizer
derivatives. This calculation concerns arbitrary subset coefficients and
does not assume a matroid signature bound. -/

namespace CountingMatroid.Analysis.SquarefreeCoordinateHessian
end CountingMatroid.Analysis.SquarefreeCoordinateHessian
open CountingMatroid CountingMatroid.Analysis CountingMatroid.Analysis.SquarefreeCoordinateHessian

open scoped BigOperators
open LorentzianDirectionalSignature

/-- INTERNAL: A repeated label derivative annihilates the entire squarefree
homogenization, independently of the homogenizer derivatives. -/
theorem solution {α : Type} [Fintype α] [DecidableEq α]
    (w : Finset α → ℚ) (xs : List (Option α)) (hnd : ¬ (xs.filterMap id).Nodup) :
    xs.foldr (fun s f => MvPolynomial.pderiv s f)
      (∑ A : Finset α, MvPolynomial.C (w A) *
        MvPolynomial.X none ^ (Fintype.card α - A.card) *
          ∏ a ∈ A, MvPolynomial.X (some a)) = 0 := by
  classical
  have hcount (ys : List (Option α)) (a : α) :
      (ys.filterMap id).count a = ys.count (some a) := by
    induction ys with
    | nil => rfl
    | cons s ys ih => cases s <;> simpa [List.count_cons] using ih
  rw [List.nodup_iff_count_le_one] at hnd
  push_neg at hnd
  obtain ⟨a, ha⟩ := hnd
  rw [hcount] at ha
  have hsum (ys : List (Option α)) (f : Finset α → MvPolynomial (Option α) ℚ) :
      ys.foldr (fun s p => MvPolynomial.pderiv s p) (∑ A, f A) =
        ∑ A, ys.foldr (fun s p => MvPolynomial.pderiv s p) (f A) := by
    induction ys with
    | nil => rfl
    | cons s ys ih => simp only [List.foldr_cons, ih, map_sum]
  rw [hsum]
  apply Finset.sum_eq_zero
  intro A _
  rw [RankWeightSupportExchange.rank_weight_term_monomial]
  apply coordinate_monomial_zero_of_count xs (some a)
  rw [RankWeightSupportExchange.subsetExponent_some]
  split_ifs <;> omega
