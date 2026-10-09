-- Prove2me | solution 1 for BookProof.ChapterAttentionMixing.l1dist_pushIter_le
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-08T17:08:36.519537+00:00
-- url     : https://prove2.me/submissions/492556fa-1dc7-42f7-bdc4-0c5594bc8d72

-- Generated from ChapterAttentionMixing.lean — solution of BookProof.ChapterAttentionMixing.l1dist_pushIter_le
import Mathlib
import Definitions.Def_ChapterAttentionMixing
import Theorems.Thm_BookProof_ChapterAttentionMixing_pushIter_succ
import Theorems.Thm_BookProof_ChapterAttentionMixing_pushIter_isProb
import Theorems.Thm_BookProof_ChapterAttentionMixing_mul_min_le_one
import Theorems.Thm_BookProof_ChapterAttentionMarkov_l1dist_push_le_of_min
import Definitions.Def_ChapterAttentionMarkov
import Theorems.Thm_BookProof_ChapterAttentionMixing_pushIter_zero
open BookProof.ChapterAttentionMarkov
open BookProof.ChapterAttentionMixing



open scoped BigOperators

open Filter Topology

noncomputable section


open BookProof.ChapterSoftmaxSharpness BookProof.ChapterSoftmaxOrder

variable {m : ℕ}

variable {m : ℕ}

set_option maxHeartbeats 1000000 in
theorem solution {P : Fin m → Fin m → ℝ} {p q : Fin m → ℝ} {eps : ℝ}
    (hP : IsStochastic P) (hmin : ∀ i j, eps ≤ P i j) (hp : IsProb p) (hq : IsProb q)
    (n : ℕ) :
    l1dist (pushIter P n p) (pushIter P n q) ≤ (1 - m * eps) ^ n * l1dist p q := by

  induction n with
  | zero => simp [pushIter_zero]
  | succ n ih =>
      rcases Nat.eq_zero_or_pos m with hm0 | hm0
      · subst hm0
        simp [l1dist]
      have hi : Fin m := ⟨0, hm0⟩
      have hc0 : 0 ≤ 1 - (m : ℝ) * eps := by
        have := mul_min_le_one hP hmin hi
        linarith
      have hstep := l1dist_push_le_of_min hP hmin (pushIter_isProb hP hp n)
        (pushIter_isProb hP hq n)
      rw [pushIter_succ, pushIter_succ]
      calc l1dist (push P (pushIter P n p)) (push P (pushIter P n q))
          ≤ (1 - m * eps) * l1dist (pushIter P n p) (pushIter P n q) := hstep
        _ ≤ (1 - m * eps) * ((1 - m * eps) ^ n * l1dist p q) :=
            mul_le_mul_of_nonneg_left ih hc0
        _ = (1 - m * eps) ^ (n + 1) * l1dist p q := by ring
