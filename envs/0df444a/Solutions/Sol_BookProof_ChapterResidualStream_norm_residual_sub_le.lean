-- Prove2me | solution 1 for BookProof.ChapterResidualStream.norm_residual_sub_le
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T06:33:51.35186+00:00
-- url     : https://prove2.me/submissions/e2e977bc-794d-44bc-a6e6-46f531e4e1a6

import Definitions.Def_ChapterSoftmaxSharpness
import Definitions.Def_ChapterAttentionOutput
import Mathlib
import Definitions.Def_ChapterResidualStream
-- Generated from ChapterResidualStream.lean — theorem BookProof.ChapterResidualStream.norm_residual_sub_le
open BookProof.ChapterResidualStream


open scoped BigOperators

noncomputable section


open BookProof.ChapterSoftmaxSharpness BookProof.ChapterAttentionOutput

variable {m : ℕ} {E : Type*} [NormedAddCommGroup E]


theorem solution {f : E → E} {L : ℝ}
    (hf : ∀ x y, ‖f x - f y‖ ≤ L * ‖x - y‖) (x y : E) :
    ‖residual f x - residual f y‖ ≤ (1 + L) * ‖x - y‖ := by
  have e : residual f x - residual f y = (x - y) + (f x - f y) := by
    simp only [BookProof.ChapterResidualStream.residual]; abel
  rw [e]
  calc ‖(x - y) + (f x - f y)‖ ≤ ‖x - y‖ + ‖f x - f y‖ := norm_add_le _ _
    _ ≤ ‖x - y‖ + L * ‖x - y‖ := by linarith [hf x y]
    _ = (1 + L) * ‖x - y‖ := by ring

