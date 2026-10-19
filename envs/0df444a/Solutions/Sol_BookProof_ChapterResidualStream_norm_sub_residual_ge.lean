-- Prove2me | solution 1 for BookProof.ChapterResidualStream.norm_sub_residual_ge
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T06:34:19.453642+00:00
-- url     : https://prove2.me/submissions/63759854-f356-4f00-9ae6-c56a49eeb09a

import Definitions.Def_ChapterSoftmaxSharpness
import Definitions.Def_ChapterAttentionOutput
import Mathlib
import Definitions.Def_ChapterResidualStream
-- Generated from ChapterResidualStream.lean — theorem BookProof.ChapterResidualStream.norm_sub_residual_ge
open BookProof.ChapterResidualStream


open scoped BigOperators

noncomputable section


open BookProof.ChapterSoftmaxSharpness BookProof.ChapterAttentionOutput

variable {m : ℕ} {E : Type*} [NormedAddCommGroup E]


theorem solution {f : E → E} {L : ℝ}
    (hf : ∀ x y, ‖f x - f y‖ ≤ L * ‖x - y‖) (x y : E) :
    (1 - L) * ‖x - y‖ ≤ ‖residual f x - residual f y‖ := by
  have e : x - y = (residual f x - residual f y) - (f x - f y) := by
    simp only [BookProof.ChapterResidualStream.residual]; abel
  have h1 : ‖x - y‖ ≤ ‖residual f x - residual f y‖ + ‖f x - f y‖ := by
    calc ‖x - y‖ = ‖(residual f x - residual f y) - (f x - f y)‖ := by rw [← e]
      _ ≤ _ := norm_sub_le _ _
  nlinarith [hf x y]

