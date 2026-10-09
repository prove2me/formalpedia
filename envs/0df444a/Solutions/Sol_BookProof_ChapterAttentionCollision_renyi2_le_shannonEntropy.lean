-- Prove2me | solution 1 for BookProof.ChapterAttentionCollision.renyi2_le_shannonEntropy
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-08T16:42:17.20807+00:00
-- url     : https://prove2.me/submissions/6645428e-a826-4f41-abba-17338a9b40d7

-- Generated from ChapterAttentionCollision.lean — solution of BookProof.ChapterAttentionCollision.renyi2_le_shannonEntropy
import Mathlib
import Definitions.Def_ChapterAttentionCollision
import Theorems.Thm_BookProof_ChapterAttentionCollision_collisionProb_pos
import Theorems.Thm_BookProof_ChapterAttentionCollision_log_le_div_add_log_sub_one
import Definitions.Def_ChapterAttentionEntropy
open BookProof.ChapterAttentionEntropy
open BookProof.ChapterAttentionCollision



open scoped BigOperators

noncomputable section


open BookProof.ChapterSoftmaxSharpness BookProof.ChapterSoftmaxOrder

variable {m : ℕ}

variable {m : ℕ}

set_option maxHeartbeats 1000000 in
theorem solution {p : Fin m → ℝ} (hp0 : ∀ j, 0 ≤ p j)
    (hsum : ∑ j, p j = 1) : renyi2 p ≤ shannonEntropy p := by

  have hc : 0 < collisionProb p := collisionProb_pos hsum
  have key : ∀ j : Fin m, p j * Real.log (p j)
      ≤ p j * (p j / collisionProb p + Real.log (collisionProb p) - 1) := by
    intro j
    rcases (hp0 j).lt_or_eq with hpos | hzero
    · exact mul_le_mul_of_nonneg_left (log_le_div_add_log_sub_one hpos hc) hpos.le
    · simp [← hzero]
  have hsum_le : ∑ j, p j * Real.log (p j)
      ≤ ∑ j, p j * (p j / collisionProb p + Real.log (collisionProb p) - 1) :=
    Finset.sum_le_sum fun j _ => key j
  have hrhs : ∑ j, p j * (p j / collisionProb p + Real.log (collisionProb p) - 1)
      = Real.log (collisionProb p) := by
    have hexp : ∀ j : Fin m, p j * (p j / collisionProb p + Real.log (collisionProb p) - 1)
        = (p j) ^ 2 / collisionProb p + p j * (Real.log (collisionProb p) - 1) := by
      intro j; field_simp; ring
    rw [Finset.sum_congr rfl fun j _ => hexp j, Finset.sum_add_distrib, ← Finset.sum_div,
      ← Finset.sum_mul, hsum]
    rw [show ∑ j, (p j) ^ 2 = collisionProb p from rfl, div_self hc.ne']
    ring
  rw [hrhs] at hsum_le
  rw [renyi2, shannonEntropy]
  linarith
