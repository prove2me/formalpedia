-- Prove2me | solution 1 for BookProof.ChapterSirkGroupTransfer.norm_pow_sub_pow_le
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-09-08T05:56:21.506566+00:00
-- url     : https://prove2.me/submissions/eea59076-1f3b-4f33-8acd-eb802d620198

-- Generated from ChapterSirkGroupTransfer.lean — solution of BookProof.ChapterSirkGroupTransfer.norm_pow_sub_pow_le
import Mathlib
import Definitions.Def_ChapterSirkGroupTransfer
import Theorems.Thm_BookProof_ChapterSirkGroupTransfer_norm_pow_le_of_le
open BookProof.ChapterSirkGroupTransfer








noncomputable section


open NormedSpace

variable {A : Type*} [NormedRing A] [NormOneClass A] [NormedAlgebra ℂ A] [CompleteSpace A]

set_option maxHeartbeats 1000000 in
omit [NormedAlgebra ℂ A] [CompleteSpace A] in
theorem solution {a b : A} {M : ℝ} (ha : ‖a‖ ≤ M) (hb : ‖b‖ ≤ M) (n : ℕ) :
    ‖a ^ (n + 1) - b ^ (n + 1)‖ ≤ (n + 1) * M ^ n * ‖a - b‖ := by

  have hM : 0 ≤ M := le_trans (norm_nonneg _) ha
  induction n with
  | zero => simp
  | succ n ih =>
    have hsplit : a ^ (n + 2) - b ^ (n + 2)
        = a * (a ^ (n + 1) - b ^ (n + 1)) + (a - b) * b ^ (n + 1) := by
      rw [pow_succ' a (n + 1), pow_succ' b (n + 1)]
      noncomm_ring
    have h1 : ‖a * (a ^ (n + 1) - b ^ (n + 1))‖ ≤ M * ((n + 1) * M ^ n * ‖a - b‖) :=
      le_trans (norm_mul_le _ _) (by gcongr)
    have h2 : ‖(a - b) * b ^ (n + 1)‖ ≤ ‖a - b‖ * M ^ (n + 1) :=
      le_trans (norm_mul_le _ _)
        (mul_le_mul_of_nonneg_left (norm_pow_le_of_le hb (n + 1)) (norm_nonneg _))
    have hstep : ((n : ℝ) + 1 + 1) * M ^ (n + 1) * ‖a - b‖
        = M * (((n : ℝ) + 1) * M ^ n * ‖a - b‖) + ‖a - b‖ * M ^ (n + 1) := by
      rw [pow_succ]; ring
    rw [hsplit]
    refine le_trans (norm_add_le _ _) ?_
    push_cast
    rw [hstep]
    exact add_le_add h1 h2
