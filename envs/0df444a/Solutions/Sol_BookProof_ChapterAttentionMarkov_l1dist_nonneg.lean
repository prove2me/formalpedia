-- Prove2me | solution 1 for BookProof.ChapterAttentionMarkov.l1dist_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-08T17:04:57.570348+00:00
-- url     : https://prove2.me/submissions/86d69e8e-65e6-4cec-989f-c5a90e7bcb76

-- Generated from ChapterAttentionMarkov.lean — solution of BookProof.ChapterAttentionMarkov.l1dist_nonneg
import Mathlib
import Definitions.Def_ChapterAttentionMarkov
open BookProof.ChapterAttentionMarkov



open scoped BigOperators

noncomputable section


open BookProof.ChapterSoftmaxSharpness BookProof.ChapterSoftmaxOrder

variable {m : ℕ}

variable {m : ℕ}

set_option maxHeartbeats 1000000 in
theorem solution (p q : Fin m → ℝ) : 0 ≤ l1dist p q := Finset.sum_nonneg fun _ _ => abs_nonneg _
