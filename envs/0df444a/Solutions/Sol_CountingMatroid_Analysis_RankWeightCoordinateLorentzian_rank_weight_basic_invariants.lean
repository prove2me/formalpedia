-- Prove2me | solution 1 for CountingMatroid.Analysis.RankWeightCoordinateLorentzian.rank_weight_basic_invariants
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-24T14:46:03.941031+00:00
-- url     : https://prove2.me/submissions/2db7d46b-d90d-4373-b74c-948fd1f9fa3c

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
set_option autoImplicit false

/-!
The matroid-specific coordinate certificate needed by the general Lorentzian
directional-closure theorem. Homogeneity and coefficient nonnegativity are
proved directly. Support exchange is proved in RankWeightSupportExchange
using the exact subset description of the support. The remaining coordinate
quadratic signatures are isolated in RankWeightCoordinateSignature, with the
cases of ground size at most two and two repeated leading label derivatives
verified. The parent uses both children.
The general coordinate signature remains open pending the cited Brändén–Huh
result or an independent proof; no directional conclusion is assumed here.
-/

namespace CountingMatroid.Analysis.RankWeightCoordinateLorentzian
end CountingMatroid.Analysis.RankWeightCoordinateLorentzian
open CountingMatroid CountingMatroid.Analysis CountingMatroid.Analysis.RankWeightCoordinateLorentzian

open scoped BigOperators
open LorentzianDirectionalSignature

/-- INTERNAL: The directly verified degree and coefficient-cone components
of the matroid coordinate certificate. They do not assert a signature bound.
TEXLINE: main.tex:332-339 -/
theorem solution {α : Type} [Fintype α] [DecidableEq α]
    (N : Matroid α) (q : ℚ) (hq : 0 < q) :
    let p : MvPolynomial (Option α) ℚ := ∑ A : Finset α,
      MvPolynomial.C ((q ^ (N.eRk (A : Set α)).toNat)⁻¹) *
        MvPolynomial.X none ^ (Fintype.card α - A.card) *
          ∏ a ∈ A, MvPolynomial.X (some a)
    p.IsHomogeneous (Fintype.card α) ∧ ∀ m, 0 ≤ p.coeff m := by
  classical
  dsimp only
  constructor
  · apply MvPolynomial.IsHomogeneous.sum
    intro A _
    have hprod : (∏ a ∈ A, MvPolynomial.X (some a) :
        MvPolynomial (Option α) ℚ).IsHomogeneous A.card := by
      simpa using MvPolynomial.IsHomogeneous.prod A
        (fun a => (MvPolynomial.X (some a) : MvPolynomial (Option α) ℚ))
        (fun _ => 1) (fun a _ => MvPolynomial.isHomogeneous_X ℚ (some a))
    have hterm := ((MvPolynomial.isHomogeneous_X_pow
      (R := ℚ) (none : Option α) (Fintype.card α - A.card)).C_mul
        ((q ^ (N.eRk (A : Set α)).toNat)⁻¹)).mul hprod
    simpa only [Nat.sub_add_cancel A.card_le_univ] using hterm
  · have hmul (f g : MvPolynomial (Option α) ℚ)
        (hf : ∀ m, 0 ≤ f.coeff m) (hg : ∀ m, 0 ≤ g.coeff m) :
        ∀ m, 0 ≤ (f * g).coeff m := by
      intro m
      rw [MvPolynomial.coeff_mul]
      exact Finset.sum_nonneg (fun t _ => mul_nonneg (hf t.1) (hg t.2))
    have hprod (A : Finset α) :
        ∀ m, 0 ≤ (∏ a ∈ A, MvPolynomial.X (some a) :
          MvPolynomial (Option α) ℚ).coeff m := by
      induction A using Finset.induction_on with
      | empty =>
        intro m
        simp only [Finset.prod_empty, MvPolynomial.coeff_one]
        split_ifs <;> norm_num
      | @insert a A ha ih =>
        rw [Finset.prod_insert ha]
        exact hmul _ _ (fun m => by
          rw [MvPolynomial.coeff_X]
          split_ifs <;> norm_num) ih
    intro m
    rw [MvPolynomial.coeff_sum]
    apply Finset.sum_nonneg
    intro A _
    rw [mul_assoc, MvPolynomial.coeff_C_mul]
    apply mul_nonneg (inv_nonneg.mpr (pow_pos hq _).le)
    exact hmul _ _ (fun m => by
      rw [MvPolynomial.coeff_X_pow]
      split_ifs <;> norm_num) (hprod A) m
