-- Prove2me | solution 2 for BookProof.ChapterSirkGroupTransfer.norm_pow_le_of_le
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-09-08T05:53:31.509375+00:00
-- url     : https://prove2.me/submissions/a565cffa-2fd1-48c7-b54c-669b97648801

-- Generated from ChapterSirkGroupTransfer.lean — solution of BookProof.ChapterSirkGroupTransfer.norm_pow_le_of_le
import Mathlib
import Definitions.Def_ChapterSirkGroupTransfer
open BookProof.ChapterSirkGroupTransfer








noncomputable section


open NormedSpace

variable {A : Type*} [NormedRing A] [NormOneClass A] [NormedAlgebra ℂ A] [CompleteSpace A]

set_option maxHeartbeats 1000000 in
omit [NormedAlgebra ℂ A] [CompleteSpace A] in
theorem solution {a : A} {M : ℝ} (ha : ‖a‖ ≤ M) (n : ℕ) : ‖a ^ n‖ ≤ M ^ n := by

  have hM : 0 ≤ M := le_trans (norm_nonneg _) ha
  induction n with
  | zero => simp
  | succ n ih =>
    calc ‖a ^ (n + 1)‖ = ‖a * a ^ n‖ := by rw [pow_succ']
      _ ≤ ‖a‖ * ‖a ^ n‖ := norm_mul_le _ _
      _ ≤ M * M ^ n := by gcongr
      _ = M ^ (n + 1) := by ring
