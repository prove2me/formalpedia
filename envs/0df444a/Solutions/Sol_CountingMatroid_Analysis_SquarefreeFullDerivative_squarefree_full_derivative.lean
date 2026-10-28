-- Prove2me | solution 1 for CountingMatroid.Analysis.SquarefreeFullDerivative.squarefree_full_derivative
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-24T15:27:12.180324+00:00
-- url     : https://prove2.me/submissions/da62fd29-ad66-45ba-8e9b-51c027ad3163

import Definitions.Def_CountingMatroid_Analysis_CubicTensorContraction
import Definitions.Def_CountingMatroid_Analysis_LorentzianDirectionalSignature
import Definitions.Def_CountingMatroid_Analysis_QuadraticNonpositiveHyperplane
import Definitions.Def_CountingMatroid_Analysis_RankWeightSupportExchange
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
import Theorems.Thm_CountingMatroid_Analysis_SquarefreeFullDerivative_squarefree_fold_coeff

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

/-- INTERNAL: Different subsets give different monomials. -/
theorem subsetExponent_injective {α : Type} [Fintype α] [DecidableEq α] :
    Function.Injective (subsetExponent (α := α)) := by
  intro A B h
  ext a
  have ha := congrArg (fun m => m (some a)) h
  simp only [subsetExponent_some] at ha
  by_cases hA : a ∈ A <;> by_cases hB : a ∈ B <;> simp_all

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

section


set_option autoImplicit false

/-! Coefficient extraction for full coordinate derivatives of squarefree-label
homogenizations. The coefficient multiplier counts repeated homogenizer
coordinates while the label coordinates are distinct. -/

namespace CountingMatroid.Analysis.SquarefreeFullDerivative

open scoped BigOperators
open RankWeightSupportExchange



/-- INTERNAL: The encoded subset monomial has exactly its assigned weight,
since different subsets have different encoded exponents. -/
theorem squarefree_homogenization_coeff {α : Type} [Fintype α] [DecidableEq α]
    (w : Finset α → ℚ) (S : Finset α) :
    (∑ A : Finset α, MvPolynomial.C (w A) *
      MvPolynomial.X none ^ (Fintype.card α - A.card) *
        ∏ a ∈ A, MvPolynomial.X (some a)).coeff (subsetExponent S) = w S := by
  classical
  simp_rw [rank_weight_term_monomial]
  rw [MvPolynomial.coeff_sum]
  simp only [MvPolynomial.coeff_monomial, subsetExponent_injective.eq_iff]
  simp



end CountingMatroid.Analysis.SquarefreeFullDerivative

/-! ### Run record
Newest first. History, not instruction — what this file claims is above.

* 2026-10-09 · proved · extracted coefficients through distinct label derivatives with an ascending-factorial homogenizer multiplier, then identified full derivatives with the selected subset weight times the homogenizer factorial.
-/

end
set_option autoImplicit false

/-! Coefficient extraction for full coordinate derivatives of squarefree-label
homogenizations. The coefficient multiplier counts repeated homogenizer
coordinates while the label coordinates are distinct. -/

namespace CountingMatroid.Analysis.SquarefreeFullDerivative
end CountingMatroid.Analysis.SquarefreeFullDerivative
open CountingMatroid CountingMatroid.Analysis CountingMatroid.Analysis.SquarefreeFullDerivative

open scoped BigOperators
open RankWeightSupportExchange

/-- INTERNAL: A full coordinate derivative with distinct labels extracts the
weight of their set, multiplied by the factorial of the homogenizer count.
TEXLINE: main.tex:334-348 -/
theorem solution {α : Type} [Fintype α] [DecidableEq α]
    (w : Finset α → ℚ) (xs : List (Option α))
    (hnd : (xs.filterMap id).Nodup) (hlen : xs.length = Fintype.card α) :
    MvPolynomial.constantCoeff
      (xs.foldr (fun s f => MvPolynomial.pderiv s f)
        (∑ A : Finset α, MvPolynomial.C (w A) *
          MvPolynomial.X none ^ (Fintype.card α - A.card) *
            ∏ a ∈ A, MvPolynomial.X (some a))) =
      w (xs.filterMap id).toFinset * (Nat.factorial (xs.count none) : ℚ) := by
  classical
  rw [MvPolynomial.constantCoeff_eq]
  rw [squarefree_fold_coeff xs _ 0 hnd (by simp)]
  have hcount (ys : List (Option α)) : ys.count none + (ys.filterMap id).length = ys.length := by
    induction ys with
    | nil => simp
    | cons s xs ih => cases s <;> simp at * <;> omega
  have he : Finsupp.single none (xs.count none) +
      ∑ a ∈ (xs.filterMap id).toFinset, Finsupp.single (some a) 1 =
      subsetExponent (xs.filterMap id).toFinset := by
    unfold subsetExponent
    rw [List.toFinset_card_of_nodup hnd]
    rw [show Fintype.card α - (xs.filterMap id).length = xs.count none by have hc := hcount xs; omega]
  simp only [zero_add, Finsupp.zero_apply, Nat.one_ascFactorial, he,
    squarefree_homogenization_coeff]
