-- Prove2me | solution 1 for BookProof.ChapterAttentionCollision.collisionProb_uniform
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-08T16:41:49.942986+00:00
-- url     : https://prove2.me/submissions/431b047e-050d-4d21-8693-7c2347a791dc

-- Generated from ChapterAttentionCollision.lean — solution of BookProof.ChapterAttentionCollision.collisionProb_uniform
import Mathlib
import Definitions.Def_ChapterAttentionCollision
open BookProof.ChapterAttentionCollision



open scoped BigOperators

noncomputable section


open BookProof.ChapterSoftmaxSharpness BookProof.ChapterSoftmaxOrder

variable {m : ℕ}

variable {m : ℕ}

set_option maxHeartbeats 1000000 in
theorem solution (hm : 0 < m) :
    collisionProb (fun _ : Fin m => (1 : ℝ) / m) = (m : ℝ)⁻¹ := by

  have hm' : (m : ℝ) ≠ 0 := by positivity
  simp only [collisionProb, div_pow, one_pow, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul]
  field_simp
