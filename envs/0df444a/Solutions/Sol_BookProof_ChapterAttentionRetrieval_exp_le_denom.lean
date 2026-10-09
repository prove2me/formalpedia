-- Prove2me | solution 1 for BookProof.ChapterAttentionRetrieval.exp_le_denom
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-08T18:37:55.714499+00:00
-- url     : https://prove2.me/submissions/284aa160-a320-4217-8f70-b5fb273c3540

-- Generated from ChapterAttentionRetrieval.lean — solution of BookProof.ChapterAttentionRetrieval.exp_le_denom
import Mathlib
import Definitions.Def_ChapterAttentionRetrieval
open BookProof.ChapterAttentionRetrieval



open scoped BigOperators

noncomputable section


open BookProof.ChapterSoftmaxSharpness BookProof.ChapterSoftmaxOrder

variable {m n : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

variable {m n : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

set_option maxHeartbeats 1000000 in
theorem solution (beta : ℝ) (s : Fin m → ℝ) (j : Fin m) :
    Real.exp (beta * s j) ≤ ∑ l, Real.exp (beta * s l) :=
  Finset.single_le_sum (f := fun l => Real.exp (beta * s l))
      (fun _ _ => (Real.exp_pos _).le) (Finset.mem_univ j)
