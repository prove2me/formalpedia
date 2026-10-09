-- Prove2me | solution 1 for BookProof.ChapterAttentionCollision.effectiveSupport_le_card
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-08T16:41:37.669986+00:00
-- url     : https://prove2.me/submissions/2c304315-caac-4305-afeb-76d805c7f4af

-- Generated from ChapterAttentionCollision.lean — solution of BookProof.ChapterAttentionCollision.effectiveSupport_le_card
import Mathlib
import Definitions.Def_ChapterAttentionCollision
import Theorems.Thm_BookProof_ChapterAttentionCollision_inv_card_le_collisionProb
import Theorems.Thm_BookProof_ChapterAttentionCollision_collisionProb_pos
open BookProof.ChapterAttentionCollision



open scoped BigOperators

noncomputable section


open BookProof.ChapterSoftmaxSharpness BookProof.ChapterSoftmaxOrder

variable {m : ℕ}

variable {m : ℕ}

set_option maxHeartbeats 1000000 in
theorem solution {p : Fin m → ℝ} (hsum : ∑ j, p j = 1) :
    effectiveSupport p ≤ (m : ℝ) := by

  have hpos := collisionProb_pos hsum
  have h := inv_card_le_collisionProb hsum
  have hm : 0 < (m : ℝ) := by
    rcases Nat.eq_zero_or_pos m with hm0 | hm0
    · subst hm0
      simp at hsum
    · exact_mod_cast hm0
  rw [effectiveSupport, div_le_iff₀ hpos]
  calc (1 : ℝ) = (m : ℝ) * (m : ℝ)⁻¹ := by field_simp
    _ ≤ (m : ℝ) * collisionProb p := by
        exact mul_le_mul_of_nonneg_left h hm.le
