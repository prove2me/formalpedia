-- Prove2me | solution 1 for BookProof.ChapterAttentionMixing.mul_min_le_one
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-08T17:28:24.796546+00:00
-- url     : https://prove2.me/submissions/37118f1c-ac97-4ba7-9d80-2b4abf7f973d

-- Generated from ChapterAttentionMixing.lean — solution of BookProof.ChapterAttentionMixing.mul_min_le_one
import Mathlib
import Definitions.Def_ChapterAttentionMixing
import Definitions.Def_ChapterAttentionMarkov
open BookProof.ChapterAttentionMarkov
open BookProof.ChapterAttentionMixing



open scoped BigOperators

open Filter Topology

noncomputable section


open BookProof.ChapterSoftmaxSharpness BookProof.ChapterSoftmaxOrder

variable {m : ℕ}

variable {m : ℕ}

set_option maxHeartbeats 1000000 in
theorem solution {P : Fin m → Fin m → ℝ} {eps : ℝ} (hP : IsStochastic P)
    (hmin : ∀ i j, eps ≤ P i j) (i : Fin m) : (m : ℝ) * eps ≤ 1 := by

  have h : ∑ _j : Fin m, eps ≤ ∑ j, P i j := Finset.sum_le_sum fun j _ => hmin i j
  rw [hP.2 i] at h
  simpa [Finset.card_univ, mul_comm] using h
