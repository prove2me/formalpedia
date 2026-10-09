-- Prove2me | solution 1 for BookProof.ChapterAttentionCollision.effectiveSupport_uniform
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-08T16:42:03.310246+00:00
-- url     : https://prove2.me/submissions/c5e51e75-2725-4187-bcdd-d4a652867ce0

-- Generated from ChapterAttentionCollision.lean — solution of BookProof.ChapterAttentionCollision.effectiveSupport_uniform
import Mathlib
import Definitions.Def_ChapterAttentionCollision
import Theorems.Thm_BookProof_ChapterAttentionCollision_collisionProb_uniform
open BookProof.ChapterAttentionCollision



open scoped BigOperators

noncomputable section


open BookProof.ChapterSoftmaxSharpness BookProof.ChapterSoftmaxOrder

variable {m : ℕ}

variable {m : ℕ}

set_option maxHeartbeats 1000000 in
theorem solution (hm : 0 < m) :
    effectiveSupport (fun _ : Fin m => (1 : ℝ) / m) = (m : ℝ) := by

  have hm' : (m : ℝ) ≠ 0 := by positivity
  rw [effectiveSupport, collisionProb_uniform hm]
  field_simp
