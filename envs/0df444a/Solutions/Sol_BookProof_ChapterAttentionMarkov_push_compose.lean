-- Prove2me | solution 1 for BookProof.ChapterAttentionMarkov.push_compose
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-08T17:04:45.461979+00:00
-- url     : https://prove2.me/submissions/89891744-0c9b-4d08-9eda-4d2e48637359

-- Generated from ChapterAttentionMarkov.lean — solution of BookProof.ChapterAttentionMarkov.push_compose
import Mathlib
import Definitions.Def_ChapterAttentionMarkov
open BookProof.ChapterAttentionMarkov



open scoped BigOperators

noncomputable section


open BookProof.ChapterSoftmaxSharpness BookProof.ChapterSoftmaxOrder

variable {m : ℕ}

variable {m : ℕ}

set_option maxHeartbeats 1000000 in
theorem solution (P Q : Fin m → Fin m → ℝ) (p : Fin m → ℝ) (j : Fin m) :
    push (compose P Q) p j = push Q (push P p) j := by

  simp only [push, compose, Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun i _ => by ring
