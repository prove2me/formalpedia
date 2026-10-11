-- Prove2me | solution 1 for BookProof.ChapterResidualStream.norm_residual_sub_self
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-11T11:26:00.602767+00:00
-- url     : https://prove2.me/submissions/c1b412f1-4567-4ddd-bd1f-a95e7a3bca5b

-- Generated from ChapterResidualStream.lean — theorem BookProof.ChapterResidualStream.norm_residual_sub_self
import Definitions.Def_ChapterSoftmaxSharpness
import Definitions.Def_ChapterAttentionOutput
import Mathlib
import Definitions.Def_ChapterResidualStream
open BookProof.ChapterResidualStream


open scoped BigOperators

noncomputable section


open BookProof.ChapterSoftmaxSharpness BookProof.ChapterAttentionOutput

variable {m : ℕ} {E : Type*} [NormedAddCommGroup E]
open BookProof.ChapterResidualStream

theorem solution(f : E → E) (x : E) : ‖residual f x - x‖ = ‖f x‖ := by
  unfold BookProof.ChapterResidualStream.residual
  rw [add_sub_cancel_left]
