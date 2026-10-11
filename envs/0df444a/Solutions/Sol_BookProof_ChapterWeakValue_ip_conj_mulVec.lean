-- Prove2me | solution 1 for BookProof.ChapterWeakValue.ip_conj_mulVec
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-10T17:21:11.868467+00:00
-- url     : https://prove2.me/submissions/e09eca46-21a9-4d7c-bdef-55419a74a437

-- Generated from ChapterWeakValue.lean — solution of BookProof.ChapterWeakValue.ip_conj_mulVec
import Mathlib
import Definitions.Def_ChapterWeakValue
open BookProof.ChapterWeakValue



open scoped BigOperators Matrix


variable {n : ℕ}

variable {n : ℕ}

set_option maxHeartbeats 1000000 in
theorem solution (A : Matrix (Fin n) (Fin n) ℂ) (f v : Fin n → ℂ) :
    starRingEnd ℂ (ip f (A *ᵥ v)) = ip v (Aᴴ *ᵥ f) := by

  simp only [ip, Matrix.mulVec, dotProduct, map_sum, map_mul, Complex.conj_conj,
    Matrix.conjTranspose_apply, RCLike.star_def, Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring
