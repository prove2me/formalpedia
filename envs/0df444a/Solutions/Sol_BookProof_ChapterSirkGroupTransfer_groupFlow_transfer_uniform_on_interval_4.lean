-- Prove2me | solution 4 for BookProof.ChapterSirkGroupTransfer.groupFlow_transfer_uniform_on_interval
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-09-08T02:35:01.348577+00:00
-- url     : https://prove2.me/submissions/8c9c801e-8234-4108-9a12-04f50a51857d

-- Generated from ChapterSirkGroupTransfer.lean — solution of BookProof.ChapterSirkGroupTransfer.groupFlow_transfer_uniform_on_interval
import Mathlib
import Definitions.Def_ChapterSirkGroupTransfer
import Theorems.Thm_BookProof_ChapterSirkGroupTransfer_norm_groupFlow_sub_le
open BookProof.ChapterSirkGroupTransfer








noncomputable section


open NormedSpace

variable {A : Type*} [NormedRing A] [NormOneClass A] [NormedAlgebra ℂ A] [CompleteSpace A]

set_option maxHeartbeats 1000000 in
theorem solution {a b : A} {M T : ℝ} (ha : ‖a‖ ≤ M)
    (hb : ‖b‖ ≤ M) (hT : 0 ≤ T) {t : ℝ} (ht : |t| ≤ T) :
    ‖groupFlow a t - groupFlow b t‖ ≤ T * ‖a - b‖ * Real.exp (T * M) := by

  have hM : 0 ≤ M := le_trans (norm_nonneg _) ha
  refine le_trans (norm_groupFlow_sub_le ha hb t) ?_
  gcongr
