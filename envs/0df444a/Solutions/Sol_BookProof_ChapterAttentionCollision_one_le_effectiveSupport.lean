-- Prove2me | solution 1 for BookProof.ChapterAttentionCollision.one_le_effectiveSupport
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-08T16:41:25.269155+00:00
-- url     : https://prove2.me/submissions/3dfa8712-4d35-486f-9300-2eab0e5da745

-- Generated from ChapterAttentionCollision.lean — solution of BookProof.ChapterAttentionCollision.one_le_effectiveSupport
import Mathlib
import Definitions.Def_ChapterAttentionCollision
import Theorems.Thm_BookProof_ChapterAttentionCollision_collisionProb_le_one
import Theorems.Thm_BookProof_ChapterAttentionCollision_collisionProb_pos
open BookProof.ChapterAttentionCollision



open scoped BigOperators

noncomputable section


open BookProof.ChapterSoftmaxSharpness BookProof.ChapterSoftmaxOrder

variable {m : ℕ}

variable {m : ℕ}

set_option maxHeartbeats 1000000 in
theorem solution {p : Fin m → ℝ} (hp0 : ∀ j, 0 ≤ p j) (hp1 : ∀ j, p j ≤ 1)
    (hsum : ∑ j, p j = 1) : 1 ≤ effectiveSupport p := by

  have hpos := collisionProb_pos hsum
  rw [effectiveSupport, le_div_iff₀ hpos, one_mul]
  exact collisionProb_le_one hp0 hp1 hsum
