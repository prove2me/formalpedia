-- Prove2me | solution 1 for BookProof.ChapterAttentionMarkov.compose_isStochastic
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-08T17:04:44.360665+00:00
-- url     : https://prove2.me/submissions/64cd1239-61d4-43ad-9a61-1b6e2f52d5d3

-- Generated from ChapterAttentionMarkov.lean — solution of BookProof.ChapterAttentionMarkov.compose_isStochastic
import Mathlib
import Definitions.Def_ChapterAttentionMarkov
open BookProof.ChapterAttentionMarkov



open scoped BigOperators

noncomputable section


open BookProof.ChapterSoftmaxSharpness BookProof.ChapterSoftmaxOrder

variable {m : ℕ}

variable {m : ℕ}

set_option maxHeartbeats 1000000 in
theorem solution {P Q : Fin m → Fin m → ℝ} (hP : IsStochastic P)
    (hQ : IsStochastic Q) : IsStochastic (compose P Q) := by

  refine ⟨fun i j => Finset.sum_nonneg fun k _ => mul_nonneg (hP.1 i k) (hQ.1 k j), fun i => ?_⟩
  calc ∑ j, compose P Q i j = ∑ k, ∑ j, P i k * Q k j := by
        simp only [compose]
        exact Finset.sum_comm
    _ = ∑ k, P i k := by
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [← Finset.mul_sum, hQ.2 k, mul_one]
    _ = 1 := hP.2 i
