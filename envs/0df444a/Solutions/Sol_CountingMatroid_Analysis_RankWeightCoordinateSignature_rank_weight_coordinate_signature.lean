-- Prove2me | solution 1 for CountingMatroid.Analysis.RankWeightCoordinateSignature.rank_weight_coordinate_signature
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-24T15:54:12.656992+00:00
-- url     : https://prove2.me/submissions/832e481d-7258-4ecb-9275-036e4601eb6a

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
import Theorems.Thm_CountingMatroid_Analysis_BinaryRankWeightSignature_binary_tutte_nonpositive_hyperplane
import Theorems.Thm_CountingMatroid_Analysis_RankWeightCoordinateSignature_rank_weight_repeated_label_zero
import Theorems.Thm_CountingMatroid_Analysis_RankWeightResidualSignature_rank_weight_residual_signature
import Theorems.Thm_CountingMatroid_Analysis_SquarefreeCoordinateHessian_squarefree_coordinate_hessian

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

/-!
A quadratic form is nonpositive on a hyperplane if some real linear
functional has a nonpositive kernel. This property survives linear pullback
and nonnegative scaling. It implies the signature bound, and also gives
nonpositivity on the orthogonal complement of any positive vector.
No property of matroid polynomials is assumed or asserted here.
-/

namespace CountingMatroid.Analysis.QuadraticNonpositiveHyperplane





/-- INTERNAL: Nonnegative scaling preserves the same nonpositive hyperplane.
TEXLINE: main.tex:326-348 -/
theorem HasNonpositiveHyperplane.smul {V : Type} [AddCommGroup V] [Module ℝ V]
    {Q : QuadraticForm ℝ V} (hQ : HasNonpositiveHyperplane Q)
    (c : ℝ) (hc : 0 ≤ c) : HasNonpositiveHyperplane (c • Q) := by
  obtain ⟨l, hl⟩ := hQ
  exact ⟨l, fun v hv => mul_nonpos_of_nonneg_of_nonpos hc (hl v hv)⟩

/-- INTERNAL: Rank-nullity converts the hyperplane witness to the exact
positive-signature bound used for quadratic descendants.
TEXLINE: main.tex:326-348 -/
theorem HasNonpositiveHyperplane.sigPos_le_one {V : Type}
    [AddCommGroup V] [Module ℝ V] [FiniteDimensional ℝ V]
    {Q : QuadraticForm ℝ V} (hQ : HasNonpositiveHyperplane Q) : sigPos Q ≤ 1 := by
  obtain ⟨l, hl⟩ := hQ
  have hdim := QuadraticForm.sigPos_add_finrank_le_of_nonpos
    (V := LinearMap.ker l) (fun v hv => hl v (LinearMap.mem_ker.mp hv))
  have hnull := l.finrank_range_add_finrank_ker
  have hrange : Module.finrank ℝ (LinearMap.range l) ≤ 1 := by
    simpa using (LinearMap.range l).finrank_le
  omega



end CountingMatroid.Analysis.QuadraticNonpositiveHyperplane

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

/-- PAPER: main.tex:334-348
Every quadratic coordinate derivative of the homogenized rank-weight
polynomial has at most one positive Hessian eigenvalue.
BORROWED: Brändén–Huh, Lorentzian polynomials (2020), Theorem 4.10,
with partial derivative closure (Theorem 2.10 and Corollary 2.11) and the
defining quadratic signature property. -/
theorem solution {α : Type} [Fintype α] [DecidableEq α]
    (N : Matroid α) (hfull : N.E = Set.univ)
    (q : ℚ) (hq : 0 < q) (hqone : q ≤ 1)
    (xs : List (Option α)) (hlength : xs.length + 2 = Fintype.card α) :
    sigPos (constantHessianForm
      (xs.foldr (fun s f => MvPolynomial.pderiv s f)
        (∑ A : Finset α,
          MvPolynomial.C ((q ^ (N.eRk (A : Set α)).toNat)⁻¹) *
            MvPolynomial.X none ^ (Fintype.card α - A.card) *
              ∏ a ∈ A, MvPolynomial.X (some a)))) ≤ 1 := by
  classical
  by_cases hrepeat : ∃ a ys, xs = some a :: some a :: ys
  · obtain ⟨a, ys, rfl⟩ := hrepeat
    rw [rank_weight_repeated_label_zero N q a ys]
    apply QuadraticNonpositiveHyperplane.HasNonpositiveHyperplane.sigPos_le_one
    refine ⟨0, ?_⟩
    intro v _
    simp only [constantHessianForm, map_zero, Rat.cast_zero,
      Matrix.toQuadraticForm', LinearMap.BilinMap.toQuadraticMap_apply]
    change Matrix.toLinearMap₂' ℝ (0 : Matrix (Option α) (Option α) ℝ) v v ≤ 0
    rw [map_zero]
    simp
  by_cases hsmall : Fintype.card α < 2
  · omega
  · by_cases htwo : Fintype.card α = 2
    · have hnil : xs = [] := by
        apply List.eq_nil_iff_length_eq_zero.mpr
        omega
      subst xs
      exact (BinaryRankWeightSignature.binary_tutte_nonpositive_hyperplane
        N q hq hqone htwo).sigPos_le_one
    · cases xs with
      | nil => simp only [List.length_nil] at hlength; omega
      | cons s xs =>
        simp only [List.foldr_cons]
        obtain ⟨S, k, c, hc, hsize, hform⟩ :=
          SquarefreeCoordinateHessian.squarefree_coordinate_hessian
            (fun A : Finset α => (q ^ (N.eRk (A : Set α)).toNat)⁻¹)
            (s :: xs) hlength
        have hsignature :=
          (RankWeightResidualSignature.rank_weight_residual_signature
            N hfull q hq hqone S k hsize).smul c hc
        rw [← hform] at hsignature
        exact hsignature.sigPos_le_one
