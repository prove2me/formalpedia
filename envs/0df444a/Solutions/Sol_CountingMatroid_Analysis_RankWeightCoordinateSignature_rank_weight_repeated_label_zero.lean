-- Prove2me | solution 1 for CountingMatroid.Analysis.RankWeightCoordinateSignature.rank_weight_repeated_label_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-24T14:45:58.63308+00:00
-- url     : https://prove2.me/submissions/67c405fc-d8a9-4bf8-83f5-bca578357013

import Definitions.Def_CountingMatroid_Analysis_CubicTensorContraction
import Definitions.Def_CountingMatroid_Analysis_LorentzianDirectionalSignature
import Definitions.Def_CountingMatroid_Analysis_QuadraticNonpositiveHyperplane
import Definitions.Def_CountingMatroid_Analysis_RankWeightSupportExchange
import Definitions.Def_CountingMatroid_Analysis_SquarefreeCoordinateHessian
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.MvPolynomial.PDeriv
import Mathlib.Algebra.Order.Chebyshev
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

section


set_option autoImplicit false

/-! The matroid-specific coordinate Hessian bound, independently of the
subset support exchange argument. Ground sizes at most two and derivatives
beginning with two identical labels are verified. The general bound is reduced
to a squarefree-polynomial Hessian identity and a matroid residual-matrix
hyperplane bound; both imported obligations remain open. The paper instead
invokes Brändén–Huh (2020), Theorem 4.10, Theorem 2.10 and Corollary 2.11
at main.tex:334-348 without proving them.

No independent rank-weight Lorentzian or Hessian-signature theorem was found
in the pinned Mathlib or Arlib sources. The downstream
`RankWeightCoordinateLorentzian.rank_weight_coordinate_lorentzian` cannot
supply the missing input: it constructs its coordinate-signature field using
this theorem. The generic coordinate and directional certificate APIs require
that field as a hypothesis; they do not establish the matroid-specific bound.
The new residual-matrix reduction does not use either certificate API.
-/

namespace CountingMatroid.Analysis.RankWeightCoordinateSignature

open scoped BigOperators
open LorentzianDirectionalSignature
open RankWeightSupportExchange

/-- INTERNAL: Coordinate derivatives of a monomial remain a monomial with
coordinatewise smaller exponents, including the zero coefficient case. -/
theorem coordinate_derivative_monomial {σ : Type}
    (xs : List σ) (m : σ →₀ ℕ) (c : ℚ) :
    ∃ e : σ →₀ ℕ, ∃ b : ℚ, e ≤ m ∧
      xs.foldr (fun s f => MvPolynomial.pderiv s f)
        (MvPolynomial.monomial m c) = MvPolynomial.monomial e b := by
  induction xs with
  | nil => exact ⟨m, c, le_rfl, rfl⟩
  | cons s xs ih =>
    obtain ⟨e, b, he, hpoly⟩ := ih
    refine ⟨e - Finsupp.single s 1, b * e s, ?_, ?_⟩
    · exact le_trans tsub_le_self he
    · simp only [List.foldr_cons, hpoly, MvPolynomial.pderiv_monomial]

/-- INTERNAL: Iterated coordinate derivatives distribute over finite sums. -/
theorem coordinate_derivative_sum {σ β : Type} (xs : List σ)
    (S : Finset β) (f : β → MvPolynomial σ ℚ) :
    xs.foldr (fun s p => MvPolynomial.pderiv s p) (∑ b ∈ S, f b) =
      ∑ b ∈ S, xs.foldr (fun s p => MvPolynomial.pderiv s p) (f b) := by
  induction xs with
  | nil => rfl
  | cons s xs ih => simp only [List.foldr_cons, ih, map_sum]





end CountingMatroid.Analysis.RankWeightCoordinateSignature

/-! ### Run record
Newest first. History, not instruction — what this file claims is above.

* 2026-10-09 · deferred handoff · the scheduler retained these children because CubicTensorContraction has an active writer in their build closure. Continued in the polynomial child: derivative commutation and excessive-count monomial annihilation are proved, closing every repeated-label normal-form branch. The two remaining boundaries are distinct-label factorial coefficient extraction and the residual matroid matrix sign bound.
* 2026-10-09 · decomposed · replaced the general local hole by the explicit squarefree-coordinate Hessian normal form and residual rank-weight matrix hyperplane bound. This replaces the cited Lorentzian-certificate route by polynomial coefficient extraction and a parallel-class square decomposition. Both substantial child obligations remain open; all earlier binary, vacuous, and repeated-label proofs and imports are preserved.
* 2026-10-09 · library dependency blocked · rechecked the target and its named dependencies; the file elaborates with its existing open signature warning. Searched 9,774 Mathlib and 385 Arlib Lean sources for Lorentzian, M-convex, Tutte/rank-generating, log-concavity, and matroid/polynomial/Hessian statements; found no applicable borrowed result. A stdin coordinate-certificate application exposes the missing certificate, and the downstream certificate explicitly calls this theorem. Proposed only the unchanged borrowed coordinate-signature statement as Prior input; preserved every proof and added no helper debt.
* 2026-10-09 · partial · proved that iterated coordinate derivatives of a monomial decrease all exponents; consequently two repeated leading label derivatives annihilate the rank-weight polynomial after any tail. This closes an additional signature branch, without using positivity, full ground, or a Lorentzian assumption. The live handoff was deferred because LorentzianDirectionalSignature still had an active writer.
* 2026-10-09 · open · separated the general coordinate signature from the independently proved subset support description; preserved the binary and vacuous cases. The nonempty-list route requires a degree-three derivative invariant or a contracted-rank-polynomial normal form, not the available two-element certificate.
-/

end
set_option autoImplicit false

/-! The matroid-specific coordinate Hessian bound, independently of the
subset support exchange argument. Ground sizes at most two and derivatives
beginning with two identical labels are verified. The general bound is reduced
to a squarefree-polynomial Hessian identity and a matroid residual-matrix
hyperplane bound; both imported obligations remain open. The paper instead
invokes Brändén–Huh (2020), Theorem 4.10, Theorem 2.10 and Corollary 2.11
at main.tex:334-348 without proving them.

No independent rank-weight Lorentzian or Hessian-signature theorem was found
in the pinned Mathlib or Arlib sources. The downstream
`RankWeightCoordinateLorentzian.rank_weight_coordinate_lorentzian` cannot
supply the missing input: it constructs its coordinate-signature field using
this theorem. The generic coordinate and directional certificate APIs require
that field as a hypothesis; they do not establish the matroid-specific bound.
The new residual-matrix reduction does not use either certificate API.
-/

namespace CountingMatroid.Analysis.RankWeightCoordinateSignature
end CountingMatroid.Analysis.RankWeightCoordinateSignature
open CountingMatroid CountingMatroid.Analysis CountingMatroid.Analysis.RankWeightCoordinateSignature

open scoped BigOperators
open LorentzianDirectionalSignature
open RankWeightSupportExchange

/-- INTERNAL: Squarefree label exponents annihilate any derivative beginning
with two identical label coordinates, regardless of its remaining tail.
TEXLINE: main.tex:334-339 -/
theorem solution {α : Type} [Fintype α] [DecidableEq α]
    (N : Matroid α) (q : ℚ) (a : α) (ys : List (Option α)) :
    (some a :: some a :: ys).foldr (fun s f => MvPolynomial.pderiv s f)
      (∑ A : Finset α,
        MvPolynomial.C ((q ^ (N.eRk (A : Set α)).toNat)⁻¹) *
          MvPolynomial.X none ^ (Fintype.card α - A.card) *
            ∏ b ∈ A, MvPolynomial.X (some b)) = 0 := by
  classical
  rw [coordinate_derivative_sum]
  apply Finset.sum_eq_zero
  intro A _
  rw [rank_weight_term_monomial]
  obtain ⟨e, c, he, hpoly⟩ := coordinate_derivative_monomial ys
    (subsetExponent A) ((q ^ (N.eRk (A : Set α)).toNat)⁻¹)
  have heone : e (some a) ≤ 1 := by
    have hbound := he (some a)
    rw [subsetExponent_some] at hbound
    split_ifs at hbound <;> omega
  simp only [List.foldr_cons, hpoly, MvPolynomial.pderiv_monomial,
    Finsupp.tsub_apply, Finsupp.single_eq_same]
  have hz : e (some a) - 1 = 0 := by omega
  simp [hz]
