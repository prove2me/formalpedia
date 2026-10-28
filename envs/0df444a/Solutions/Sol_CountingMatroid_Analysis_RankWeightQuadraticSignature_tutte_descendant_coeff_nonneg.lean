-- Prove2me | solution 1 for CountingMatroid.Analysis.RankWeightQuadraticSignature.tutte_descendant_coeff_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-24T14:47:07.687264+00:00
-- url     : https://prove2.me/submissions/09b4f929-626c-4c91-801d-f4cc5860d017

import Definitions.Def_CountingMatroid_Analysis_CubicTensorContraction
import Definitions.Def_CountingMatroid_Analysis_LorentzianDirectionalSignature
import Definitions.Def_CountingMatroid_Analysis_QuadraticNonpositiveHyperplane
import Definitions.Def_CountingMatroid_Analysis_RankWeightQuadraticSignature
import Definitions.Def_CountingMatroid_Analysis_RankWeightSupportExchange
import Definitions.Def_CountingMatroid_Analysis_SquarefreeCoordinateHessian
import Definitions.Def_CountingMatroid_Model_Prelude
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
import Mathlib.Data.Rat.Defs
import Mathlib.Data.Real.Basic
import Mathlib.LinearAlgebra.Matrix.BilinearForm
import Mathlib.LinearAlgebra.QuadraticForm.Basic
import Mathlib.LinearAlgebra.QuadraticForm.Signature
import Mathlib.RingTheory.MvPolynomial.EulerIdentity
import Mathlib.RingTheory.MvPolynomial.Homogeneous
import Mathlib.Tactic
import Mathlib.Tactic.Positivity
import Mathlib.Topology.Algebra.Order.Field
import Mathlib.Topology.Instances.Rat
import Mathlib.Topology.Instances.Real.Lemmas

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
set_option autoImplicit false

/-!
The precise external signature input, separate from the operational rank
correspondence and coefficient extraction proved in the counting paper.
`Descendant` records only partial derivatives, nonnegative linear
substitutions, and nonnegative scalar multiplication. The signature uses
Mathlib's maximum dimension of a positive definite subspace over the reals.
The empty- and singleton-ground signature cases are proved, using the
homogeneous-degree invariant of every descendant. The two-element ground
case is proved by rank submodularity and a two-square calculation, with
the resulting hyperplane transported through every allowed substitution.
The signature case with at most one output variable follows from the ambient
dimension bound. The remaining
Bränden–Huh input is the unresolved borrowed mixed-derivative prerequisite
in `MixedDirectionalRankWeightSignature`. The exact normal
form of a descendant is proved: nonnegative directional derivatives in the
original variables, followed by one nonnegative linear substitution and a
nonnegative scalar. A nonzero quadratic uses exactly ground-set size minus
two derivatives. The unresolved signature bound is applied to this normal
form. A proved nonpositive-hyperplane invariant transports the Hessian
through the final substitution and scaling and recovers the exact orthogonal
kernel used by the signature bound. Only its establishment for the original
mixed directional derivative on ground sets of size at least three remains
open in that support module; no Lorentzian assumption has been introduced.
-/

namespace CountingMatroid.Analysis.RankWeightQuadraticSignature
end CountingMatroid.Analysis.RankWeightQuadraticSignature
open CountingMatroid CountingMatroid.Analysis CountingMatroid.Analysis.RankWeightQuadraticSignature

open scoped BigOperators

/-- INTERNAL: The coefficient cone is an invariant of the entire descendant
derivation, including substitutions that introduce or merge variables.
TEXLINE: main.tex:334-348 -/
theorem solution {α τ : Type} [Fintype α]
    (N : Matroid α) (q : ℚ) (hq : 0 < q) (g : MvPolynomial τ ℚ)
    (hg : Descendant (tuttePolynomial N q) τ g) :
    ∀ d, 0 ≤ g.coeff d := by
  classical
  have hmul {υ : Type} (p₁ p₂ : MvPolynomial υ ℚ)
      (h₁ : ∀ d, 0 ≤ p₁.coeff d) (h₂ : ∀ d, 0 ≤ p₂.coeff d) :
      ∀ d, 0 ≤ (p₁ * p₂).coeff d := by
    intro d
    rw [MvPolynomial.coeff_mul]
    exact Finset.sum_nonneg (fun m _ => mul_nonneg (h₁ m.1) (h₂ m.2))
  have hpow {υ : Type} (p : MvPolynomial υ ℚ)
      (hp : ∀ d, 0 ≤ p.coeff d) (k : ℕ) :
      ∀ d, 0 ≤ (p ^ k).coeff d := by
    induction k with
    | zero => intro d; simp only [pow_zero, MvPolynomial.coeff_one]; split_ifs <;> norm_num
    | succ k ih => rw [pow_succ]; exact hmul _ _ ih hp
  have hprod {ι υ : Type} (S : Finset ι) (p : ι → MvPolynomial υ ℚ)
      (hp : ∀ i ∈ S, ∀ d, 0 ≤ (p i).coeff d) :
      ∀ d, 0 ≤ (∏ i ∈ S, p i).coeff d := by
    induction S using Finset.induction_on with
    | empty => intro d; simp only [Finset.prod_empty, MvPolynomial.coeff_one]; split_ifs <;> norm_num
    | @insert i S hi ih =>
      rw [Finset.prod_insert hi]
      exact hmul _ _ (hp i (by simp)) (ih (fun j hj => hp j (by simp [hj])))
  have hbase : ∀ d, 0 ≤ (tuttePolynomial N q).coeff d := by
    intro d
    unfold tuttePolynomial
    rw [MvPolynomial.coeff_sum]
    apply Finset.sum_nonneg
    intro A _
    rw [mul_assoc, MvPolynomial.coeff_C_mul]
    apply mul_nonneg (inv_nonneg.mpr (pow_pos hq _).le)
    apply hmul
    · intro m; rw [MvPolynomial.coeff_X_pow]; split_ifs <;> norm_num
    · exact hprod A (fun a => MvPolynomial.X (some a))
        (fun a _ m => by rw [MvPolynomial.coeff_X]; split_ifs <;> norm_num)
  induction hg with
  | initial => exact hbase
  | derivative t _ ih =>
    intro d
    rw [MvPolynomial.coeff_pderiv]
    exact mul_nonneg (ih _) (by positivity)
  | @substitute τ υ _ p a ha hp ih =>
    let L := fun s => ∑ t, MvPolynomial.C (a s t) * MvPolynomial.X t
    have hL : ∀ s d, 0 ≤ (L s).coeff d := by
      intro s d
      dsimp only [L]
      rw [MvPolynomial.coeff_sum]
      apply Finset.sum_nonneg
      intro t _
      rw [MvPolynomial.coeff_C_mul]
      exact mul_nonneg (ha s t) (by rw [MvPolynomial.coeff_X]; split_ifs <;> norm_num)
    intro d
    unfold linearSubstitution
    rw [p.as_sum, map_sum, MvPolynomial.coeff_sum]
    apply Finset.sum_nonneg
    intro m _
    rw [MvPolynomial.aeval_monomial]
    change 0 ≤ (MvPolynomial.C (p.coeff m) *
      m.prod (fun s k => L s ^ k)).coeff d
    rw [MvPolynomial.coeff_C_mul]
    apply mul_nonneg (ih m)
    exact hprod m.support _ (fun s _ => hpow (L s) (hL s) (m s)) d
  | scale c hc _ ih =>
    intro d
    rw [MvPolynomial.coeff_C_mul]
    exact mul_nonneg hc (ih d)
