-- Prove2me | solution 1 for FunctionalInequalities.Analysis.cfc_eq_mul_diagonal_mul_408915f
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-23T15:06:12.518085+00:00
-- url     : https://prove2.me/submissions/aa8d74d1-ee0e-4b22-8a95-2162ac2d15b7

import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Analysis.Matrix.HermitianFunctionalCalculus
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.NoncommRing

open Matrix
section
namespace FunctionalInequalities
end FunctionalInequalities
open FunctionalInequalities
section
namespace FunctionalInequalities.Analysis
end FunctionalInequalities.Analysis
open FunctionalInequalities FunctionalInequalities.Analysis
variable {n : Type*} [Fintype n] [DecidableEq n]
variable {n : Type*} [Fintype n] [DecidableEq n]
namespace FunctionalInequalities.Analysis
end FunctionalInequalities.Analysis
open FunctionalInequalities.Analysis in
/-- The functional calculus of a real symmetric matrix in its orthonormal eigenbasis. -/
theorem solution {A : Matrix n n ℝ} (hA : A.IsHermitian) (f : ℝ → ℝ) :
    cfc f A = (hA.eigenvectorUnitary : Matrix n n ℝ) * diagonal (fun i => f (hA.eigenvalues i)) *
      (hA.eigenvectorUnitary : Matrix n n ℝ)ᵀ := by
  have hdiag :
      diagonal (RCLike.ofReal ∘ f ∘ hA.eigenvalues) =
        diagonal (fun i => f (hA.eigenvalues i)) := by
    apply congrArg (fun g : n → ℝ => diagonal g)
    funext i
    simp [Function.comp_def, RCLike.ofReal_real_eq_id]

  have hstar :
      star (hA.eigenvectorUnitary : Matrix n n ℝ) =
        (hA.eigenvectorUnitary : Matrix n n ℝ)ᵀ := by
    rw [Matrix.star_eq_conjTranspose,
      Matrix.conjTranspose_eq_transpose_of_trivial]

  rw [hA.cfc_eq f, Matrix.IsHermitian.cfc]
  change
    (hA.eigenvectorUnitary : Matrix n n ℝ) *
        diagonal (RCLike.ofReal ∘ f ∘ hA.eigenvalues) *
        star (hA.eigenvectorUnitary : Matrix n n ℝ) =
      (hA.eigenvectorUnitary : Matrix n n ℝ) *
        diagonal (fun i => f (hA.eigenvalues i)) *
        (hA.eigenvectorUnitary : Matrix n n ℝ)ᵀ
  rw [hdiag, hstar]
