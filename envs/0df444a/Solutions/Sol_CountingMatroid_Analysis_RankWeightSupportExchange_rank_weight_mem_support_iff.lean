-- Prove2me | solution 1 for CountingMatroid.Analysis.RankWeightSupportExchange.rank_weight_mem_support_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-24T14:46:03.885341+00:00
-- url     : https://prove2.me/submissions/3d33ceaa-505a-4673-b3b2-79435a0ebb7d

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
set_option autoImplicit false

/-! The subset exponent description of the rank-weight polynomial support.
The exchange condition depends only on the subsets, not on matroid ranks. -/

namespace CountingMatroid.Analysis.RankWeightSupportExchange
end CountingMatroid.Analysis.RankWeightSupportExchange
open CountingMatroid CountingMatroid.Analysis CountingMatroid.Analysis.RankWeightSupportExchange

open scoped BigOperators
open LorentzianDirectionalSignature

/-- INTERNAL: Nonzero rank weights leave exactly all subset exponents in the
polynomial support. TEXLINE: main.tex:334-339 -/
theorem solution {α : Type} [Fintype α] [DecidableEq α]
    (N : Matroid α) (q : ℚ) (hq : 0 < q) (m : Option α →₀ ℕ) :
    m ∈ (∑ A : Finset α,
      MvPolynomial.C ((q ^ (N.eRk (A : Set α)).toNat)⁻¹) *
        MvPolynomial.X none ^ (Fintype.card α - A.card) *
          ∏ a ∈ A, MvPolynomial.X (some a)).support ↔
      ∃ A : Finset α, m = subsetExponent A := by
  classical
  simp_rw [rank_weight_term_monomial]
  constructor
  · intro hm
    obtain ⟨A, _, hA⟩ := Finset.mem_biUnion.mp (MvPolynomial.support_sum hm)
    have hne : (q ^ (N.eRk (A : Set α)).toNat)⁻¹ ≠ 0 :=
      ne_of_gt (inv_pos.mpr (pow_pos hq _))
    rw [MvPolynomial.support_monomial, if_neg hne, Finset.mem_singleton] at hA
    exact ⟨A, hA⟩
  · rintro ⟨A, rfl⟩
    rw [MvPolynomial.mem_support_iff, MvPolynomial.coeff_sum]
    simp only [MvPolynomial.coeff_monomial]
    have hinj := subsetExponent_injective (α := α)
    simp only [hinj.eq_iff]
    simpa using ne_of_gt (inv_pos.mpr (pow_pos hq (N.eRk (A : Set α)).toNat))
