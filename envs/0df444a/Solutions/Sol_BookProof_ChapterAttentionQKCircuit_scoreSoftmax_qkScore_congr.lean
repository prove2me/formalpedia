-- Prove2me | solution 1 for BookProof.ChapterAttentionQKCircuit.scoreSoftmax_qkScore_congr
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-08T17:36:05.907067+00:00
-- url     : https://prove2.me/submissions/69394993-78af-4a14-bf81-fcb78ebab416

-- Generated from ChapterAttentionQKCircuit.lean — solution of BookProof.ChapterAttentionQKCircuit.scoreSoftmax_qkScore_congr
import Mathlib
import Definitions.Def_ChapterAttentionQKCircuit
import Theorems.Thm_BookProof_ChapterAttentionQKCircuit_qkScore_congr_of_qkMatrix_eq
open BookProof.ChapterAttentionQKCircuit



open scoped BigOperators

noncomputable section


open Matrix BookProof.ChapterSoftmaxSharpness BookProof.ChapterSoftmaxOrder

variable {d n m : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

variable {d n m : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

set_option maxHeartbeats 1000000 in
theorem solution (beta : ℝ) {WQ₁ WK₁ WQ₂ WK₂ : Matrix (Fin d) (Fin n) ℝ}
    (h : qkMatrix WQ₁ WK₁ = qkMatrix WQ₂ WK₂) (x : Fin n → ℝ) (k : Fin m → Fin n → ℝ)
    (j : Fin m) :
    scoreSoftmax beta (fun l => qkScore WQ₁ WK₁ x (k l)) j
      = scoreSoftmax beta (fun l => qkScore WQ₂ WK₂ x (k l)) j := by

  have : (fun l => qkScore WQ₁ WK₁ x (k l)) = fun l => qkScore WQ₂ WK₂ x (k l) :=
    funext fun l => qkScore_congr_of_qkMatrix_eq h x (k l)
  rw [this]
