-- Prove2me | solution 1 for BookProof.ChapterF4.observable_matrix_entry
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-09T07:02:14.396876+00:00
-- url     : https://prove2.me/submissions/9a4cdf06-2e54-426a-9701-a278e1889a1c

-- Generated from ChapterF4.lean — solution of BookProof.ChapterF4.observable_matrix_entry
import Mathlib
import Definitions.Def_ChapterF4
open BookProof.ChapterF4



open scoped BigOperators Matrix

variable {d k : ℕ}
variable {A : Type*} [NormedRing A] [NormedAlgebra ℂ A] [StarRing A] [ContinuousStar A]
  [CompleteSpace A] [StarModule ℂ A]
variable {α κ Ω : Type*} [Fintype α] [DecidableEq α] [Fintype κ] [DecidableEq κ]
  {mΩ : MeasurableSpace Ω}

set_option maxHeartbeats 1000000 in
theorem solution {d n : ℕ} (W : Matrix (Fin d) (Fin n) ℂ)
    (a : Fin d) (r s : Fin n) :
    Matrix.trace ((Matrix.single r s (1 : ℂ))ᴴ * Wᴴ * Matrix.single a a (1 : ℂ) * W)
      = (starRingEnd ℂ) (W a r) * W a s := by

  simp only [Matrix.trace, Matrix.single, Matrix.diag_apply, Matrix.mul_apply,
      Matrix.conjTranspose_apply, Matrix.of_apply, RCLike.star_def,
          MonoidWithZeroHom.map_ite_one_zero, ite_mul, one_mul, zero_mul, mul_ite, mul_one,
              mul_zero];
  simp? +contextual [ Finset.sum_ite, Finset.filter_eq, Finset.filter_and, mul_comm ];
  rw [ Finset.sum_eq_single s ] <;> simp? +contextual ;
  · rw [ Finset.sum_eq_single a ] <;> aesop;
  · aesop
