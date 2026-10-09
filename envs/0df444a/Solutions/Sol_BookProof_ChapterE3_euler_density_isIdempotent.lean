-- Prove2me | solution 1 for BookProof.ChapterE3.euler_density_isIdempotent
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-09T06:31:35.709982+00:00
-- url     : https://prove2.me/submissions/91ae773b-e956-4829-9feb-3d7072826ca2

-- Generated from ChapterE3.lean — solution of BookProof.ChapterE3.euler_density_isIdempotent
import Mathlib
import Definitions.Def_ChapterE3
open BookProof.ChapterE3



open scoped Matrix BigOperators


variable {n : ℕ}

variable {n : ℕ}

set_option maxHeartbeats 1000000 in
theorem solution (l w : Fin n → ℝ) (θ : ℝ)
    (hll : ∑ i, l i * l i = 1) (hww : ∑ i, w i * w i = 1)
    (hlw : ∑ i, l i * w i = 0) :
    (Matrix.vecMulVec (fun i => Real.cos θ * l i + Real.sin θ * w i)
        (fun i => Real.cos θ * l i + Real.sin θ * w i))
      * (Matrix.vecMulVec (fun i => Real.cos θ * l i + Real.sin θ * w i)
        (fun i => Real.cos θ * l i + Real.sin θ * w i))
      = Matrix.vecMulVec (fun i => Real.cos θ * l i + Real.sin θ * w i)
        (fun i => Real.cos θ * l i + Real.sin θ * w i) := by

  have h_sum : ∑ i, (Real.cos θ * l i + Real.sin θ * w i)
      * (Real.cos θ * l i + Real.sin θ * w i) = 1 := by
    ring_nf
    simp_all [Finset.sum_add_distrib, mul_assoc, mul_comm, mul_left_comm,
      Real.sin_sq, Real.cos_sq]
    ring
    simp_all [Finset.sum_add_distrib, ← Finset.mul_sum _ _ _, ← Finset.sum_mul, sq]
    ring
  convert congr_arg (fun x : ℝ => x • Matrix.vecMulVec
    (fun i => Real.cos θ * l i + Real.sin θ * w i)
    (fun i => Real.cos θ * l i + Real.sin θ * w i)) h_sum using 1
  · ext i j
    simp [Matrix.vecMulVec, Matrix.mul_apply, Finset.mul_sum _ _ _,
      mul_comm, mul_left_comm]
  · norm_num
