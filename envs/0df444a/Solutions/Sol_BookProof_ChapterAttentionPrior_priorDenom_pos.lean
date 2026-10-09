-- Prove2me | solution 1 for BookProof.ChapterAttentionPrior.priorDenom_pos
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-08T17:33:30.030641+00:00
-- url     : https://prove2.me/submissions/67f0b7eb-b974-409a-8b56-183b78af1ba8

-- Generated from ChapterAttentionPrior.lean — solution of BookProof.ChapterAttentionPrior.priorDenom_pos
import Mathlib
import Definitions.Def_ChapterAttentionPrior
open BookProof.ChapterAttentionPrior



open scoped BigOperators

noncomputable section


open BookProof.ChapterSoftmaxSharpness BookProof.ChapterSoftmaxOrder

variable {m : ℕ}

variable {m : ℕ}

set_option maxHeartbeats 1000000 in
theorem solution {w : Fin m → ℝ} (hw : ∀ j, 0 < w j) (beta : ℝ) (s : Fin m → ℝ)
    (i : Fin m) : 0 < ∑ l, w l * Real.exp (beta * s l) :=
  Finset.sum_pos' (fun l _ => (mul_pos (hw l) (Real.exp_pos _)).le)
      ⟨i, Finset.mem_univ i, mul_pos (hw i) (Real.exp_pos _)⟩
