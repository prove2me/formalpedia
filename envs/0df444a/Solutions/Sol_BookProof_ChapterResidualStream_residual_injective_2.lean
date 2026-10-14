-- Prove2me | solution 2 for BookProof.ChapterResidualStream.residual_injective
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-13T11:27:27.289266+00:00
-- url     : https://prove2.me/submissions/05817465-6ce6-4611-9e5f-e49e669220ba

-- Generated from ChapterResidualStream.lean — theorem BookProof.ChapterResidualStream.residual_injective
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

theorem solution{f : E → E} {L : ℝ} (hL : L < 1)
    (hf : ∀ x y, ‖f x - f y‖ ≤ L * ‖x - y‖) :
    Function.Injective (residual f) := by
  intro x y hxy
  unfold BookProof.ChapterResidualStream.residual at hxy
  have h1 : x - y = f y - f x := by
    rw [sub_eq_sub_iff_add_eq_add, hxy, add_comm]
  have h2 := hf y x
  rw [← h1, norm_sub_rev y x] at h2
  have h3 : ‖x - y‖ = 0 := by nlinarith [norm_nonneg (x - y)]
  exact sub_eq_zero.mp (norm_eq_zero.mp h3)
