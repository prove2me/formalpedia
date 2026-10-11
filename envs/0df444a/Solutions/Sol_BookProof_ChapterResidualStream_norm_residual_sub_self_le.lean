-- Prove2me | solution 1 for BookProof.ChapterResidualStream.norm_residual_sub_self_le
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-11T08:51:56.503994+00:00
-- url     : https://prove2.me/submissions/3794f88a-90f7-44bd-bba9-93a7ec24be54
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

-- Generated from ChapterResidualStream.lean — solution of BookProof.ChapterResidualStream.norm_residual_sub_self_le
import Mathlib
import Definitions.Def_ChapterResidualStream
import Theorems.Thm_BookProof_ChapterResidualStream_norm_residual_sub_self
import Theorems.Thm_BookProof_ChapterAttentionOutput_norm_headOutput_le
import Definitions.Def_ChapterSoftmaxSharpness
import Definitions.Def_ChapterAttentionOutput
open BookProof.ChapterResidualStream



open scoped BigOperators

noncomputable section


open BookProof.ChapterSoftmaxSharpness BookProof.ChapterAttentionOutput

variable {m : ℕ} {E : Type*} [NormedAddCommGroup E]

variable {m : ℕ} {E : Type*} [NormedAddCommGroup E]

set_option maxHeartbeats 1000000 in
theorem solution [NormedSpace ℝ E] (beta : ℝ) (s : Fin m → ℝ)
    {v : Fin m → E} {C : ℝ} (hv : ∀ j, ‖v j‖ ≤ C) (i : Fin m) (x : E) :
    ‖residual (fun _ => headOutput beta s v) x - x‖ ≤ C := by

  rw [norm_residual_sub_self]
  exact norm_headOutput_le beta s hv i
