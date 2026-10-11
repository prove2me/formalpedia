-- Prove2me | solution 1 for BookProof.ChapterResidualStream.residual_injective
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-11T08:52:11.24486+00:00
-- url     : https://prove2.me/submissions/fdbb3209-28ef-437d-8ea3-712fc8a32e58
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

-- Generated from ChapterResidualStream.lean — solution of BookProof.ChapterResidualStream.residual_injective
import Mathlib
import Definitions.Def_ChapterResidualStream
import Theorems.Thm_BookProof_ChapterResidualStream_norm_sub_residual_ge
import Definitions.Def_ChapterSoftmaxSharpness
import Definitions.Def_ChapterAttentionOutput
open BookProof.ChapterResidualStream



open scoped BigOperators

noncomputable section


open BookProof.ChapterSoftmaxSharpness BookProof.ChapterAttentionOutput

variable {m : ℕ} {E : Type*} [NormedAddCommGroup E]

variable {m : ℕ} {E : Type*} [NormedAddCommGroup E]

set_option maxHeartbeats 1000000 in
theorem solution {f : E → E} {L : ℝ} (hL : L < 1)
    (hf : ∀ x y, ‖f x - f y‖ ≤ L * ‖x - y‖) :
    Function.Injective (residual f) := by

  intro x y hxy
  have h := norm_sub_residual_ge hf x y
  rw [hxy, sub_self, norm_zero] at h
  have hx : ‖x - y‖ ≤ 0 := by
    by_contra hpos
    push_neg at hpos
    nlinarith
  have : x - y = 0 := by
    exact norm_eq_zero.mp (le_antisymm hx (norm_nonneg _))
  exact sub_eq_zero.mp this
