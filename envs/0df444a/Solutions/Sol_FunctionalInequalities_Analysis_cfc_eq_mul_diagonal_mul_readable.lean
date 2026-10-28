-- Prove2me | solution 1 for FunctionalInequalities.Analysis.cfc_eq_mul_diagonal_mul_readable
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-26T13:29:52.497893+00:00
-- url     : https://prove2.me/submissions/f3089528-6a2b-49b1-8ad2-375332785b05

import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_Matrix_Trace_Power

open Matrix
variable {n : Type*} [Fintype n] [DecidableEq n]
variable {n : Type*} [Fintype n] [DecidableEq n]
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
