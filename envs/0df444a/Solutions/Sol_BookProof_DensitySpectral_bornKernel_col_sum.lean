-- Prove2me | solution 1 for BookProof.DensitySpectral.bornKernel_col_sum
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-08T23:49:28.171855+00:00
-- url     : https://prove2.me/submissions/6d5a7e95-33a1-4532-8798-e8f7932f6a0c

-- Generated from ChapterDensityMarginalConditional.lean — solution of BookProof.DensitySpectral.bornKernel_col_sum
import Mathlib
import Definitions.Def_ChapterDensityMarginalConditional
open BookProof.DensitySpectral




open Matrix
open scoped BigOperators ComplexOrder

variable {n : Type*} [Fintype n] [DecidableEq n]

variable {n : Type*} [Fintype n] [DecidableEq n]

set_option maxHeartbeats 1000000 in
theorem solution (U : Matrix.unitaryGroup n ℂ) (j : n) :
    ∑ i, bornKernel (U : Matrix n n ℂ) i j = 1 := by

  have h : (U : Matrix n n ℂ)ᴴ * (U : Matrix n n ℂ) = 1 := by
    have := Unitary.star_mul_self_of_mem U.2
    simpa [Matrix.star_eq_conjTranspose] using this
  have h2 := congrFun (congrFun h j) j
  rw [Matrix.mul_apply] at h2
  simp only [Matrix.conjTranspose_apply, Matrix.one_apply_eq] at h2
  have key : ∀ i, star ((U : Matrix n n ℂ) i j) * (U : Matrix n n ℂ) i j
      = ((Complex.normSq ((U : Matrix n n ℂ) i j) : ℝ) : ℂ) := fun i => by
    rw [mul_comm]
    simpa [Complex.star_def] using Complex.mul_conj ((U : Matrix n n ℂ) i j)
  simp only [key] at h2
  rw [← Complex.ofReal_sum] at h2
  exact_mod_cast h2
