-- Prove2me | solution 1 for BookProof.DensitySpectral.density_diag_eq_kernel_apply
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-09T05:41:44.561985+00:00
-- url     : https://prove2.me/submissions/da06a571-24f5-47c3-8495-dc0180c81270

-- Generated from ChapterDensityMarginalConditional.lean — solution of BookProof.DensitySpectral.density_diag_eq_kernel_apply
import Mathlib
import Definitions.Def_ChapterDensityMarginalConditional
open BookProof.DensitySpectral




open Matrix
open scoped BigOperators ComplexOrder

variable {n : Type*} [Fintype n] [DecidableEq n]

variable {n : Type*} [Fintype n] [DecidableEq n]

set_option maxHeartbeats 1000000 in
theorem solution (U : Matrix n n ℂ) (d : n → ℝ) (i : n) :
    (U * Matrix.diagonal (RCLike.ofReal ∘ d) * Uᴴ : Matrix n n ℂ) i i
      = ((∑ k, bornKernel U i k * d k : ℝ) : ℂ) := by

  rw [Matrix.mul_apply]
  push_cast
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Matrix.mul_diagonal, Matrix.conjTranspose_apply]
  simp only [Function.comp_apply, bornKernel,
    Complex.normSq_eq_conj_mul_self]
  simp []
  ring
