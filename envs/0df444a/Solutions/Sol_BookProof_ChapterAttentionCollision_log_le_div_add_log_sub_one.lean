-- Prove2me | solution 1 for BookProof.ChapterAttentionCollision.log_le_div_add_log_sub_one
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-08T16:42:05.08043+00:00
-- url     : https://prove2.me/submissions/0b092f15-128b-46ee-a986-4b7e97dd8445

-- Generated from ChapterAttentionCollision.lean — solution of BookProof.ChapterAttentionCollision.log_le_div_add_log_sub_one
import Mathlib
import Definitions.Def_ChapterAttentionCollision
open BookProof.ChapterAttentionCollision



open scoped BigOperators

noncomputable section


open BookProof.ChapterSoftmaxSharpness BookProof.ChapterSoftmaxOrder

variable {m : ℕ}

variable {m : ℕ}

set_option maxHeartbeats 1000000 in
theorem solution {x c : ℝ} (hx : 0 < x) (hc : 0 < c) :
    Real.log x ≤ x / c + Real.log c - 1 := by

  have h : Real.log (x / c) ≤ x / c - 1 := Real.log_le_sub_one_of_pos (by positivity)
  rw [Real.log_div hx.ne' hc.ne'] at h
  linarith
