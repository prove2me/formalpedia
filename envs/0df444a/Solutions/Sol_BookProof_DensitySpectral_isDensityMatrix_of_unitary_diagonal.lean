-- Prove2me | solution 1 for BookProof.DensitySpectral.isDensityMatrix_of_unitary_diagonal
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-09T05:42:13.545454+00:00
-- url     : https://prove2.me/submissions/88b473a9-6da7-4bec-b05f-f2b9ed0e539a

-- Generated from ChapterDensitySpectral.lean — solution of BookProof.DensitySpectral.isDensityMatrix_of_unitary_diagonal
import Mathlib
import Definitions.Def_ChapterDensitySpectral
open BookProof.DensitySpectral




open Matrix
open scoped BigOperators ComplexOrder

variable {n : Type*} [Fintype n] [DecidableEq n]

variable {n : Type*} [Fintype n] [DecidableEq n]

set_option maxHeartbeats 1000000 in
theorem solution
    (U : Matrix.unitaryGroup n ℂ) (d : n → ℝ)
    (hd : ∀ i, 0 ≤ d i) (hsum : ∑ i, d i = 1) :
    IsDensityMatrix ((U : Matrix n n ℂ) * diagonal (RCLike.ofReal ∘ d)
      * (U : Matrix n n ℂ)ᴴ) := by

  set D : Matrix n n ℂ := diagonal (RCLike.ofReal ∘ d) with hD
  have hDherm : D.IsHermitian := by
    rw [hD, Matrix.IsHermitian, Matrix.diagonal_conjTranspose]
    congr 1; funext i; simp [Function.comp]
  have hUstarU : (U : Matrix n n ℂ)ᴴ * (U : Matrix n n ℂ) = 1 := by
    have := Matrix.UnitaryGroup.star_mul_self U
    simpa [Matrix.star_eq_conjTranspose] using this
  refine ⟨?_, ?_, ?_⟩
  · unfold Matrix.IsHermitian
    rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
      hDherm, Matrix.mul_assoc]
  · have hDpsd : D.PosSemidef := by
      rw [hD, Matrix.posSemidef_diagonal_iff]
      intro i; simp only [Function.comp]; rw [RCLike.ofReal_nonneg]; exact hd i
    exact hDpsd.mul_mul_conjTranspose_same (U : Matrix n n ℂ)
  · rw [Matrix.trace_mul_comm, ← Matrix.mul_assoc, hUstarU, Matrix.one_mul, hD,
      Matrix.trace_diagonal]
    simp only [Function.comp]
    rw [← RCLike.ofReal_sum, hsum, RCLike.ofReal_one]
