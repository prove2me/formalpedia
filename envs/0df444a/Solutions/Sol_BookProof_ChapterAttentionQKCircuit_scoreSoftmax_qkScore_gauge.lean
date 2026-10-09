-- Prove2me | solution 1 for BookProof.ChapterAttentionQKCircuit.scoreSoftmax_qkScore_gauge
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-08T17:36:08.443699+00:00
-- url     : https://prove2.me/submissions/55aa9afd-3bf3-4578-a63d-177a598c8232

-- Generated from ChapterAttentionQKCircuit.lean — solution of BookProof.ChapterAttentionQKCircuit.scoreSoftmax_qkScore_gauge
import Mathlib
import Definitions.Def_ChapterAttentionQKCircuit
import Theorems.Thm_BookProof_ChapterAttentionQKCircuit_qkMatrix_gauge
import Theorems.Thm_BookProof_ChapterAttentionQKCircuit_scoreSoftmax_qkScore_congr
open BookProof.ChapterAttentionQKCircuit



open scoped BigOperators

noncomputable section


open Matrix BookProof.ChapterSoftmaxSharpness BookProof.ChapterSoftmaxOrder

variable {d n m : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

variable {d n m : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

set_option maxHeartbeats 1000000 in
theorem solution (beta : ℝ) {A B : Matrix (Fin d) (Fin d) ℝ}
    (hAB : Aᵀ * B = 1) (WQ WK : Matrix (Fin d) (Fin n) ℝ) (x : Fin n → ℝ)
    (k : Fin m → Fin n → ℝ) (j : Fin m) :
    scoreSoftmax beta (fun l => qkScore (A * WQ) (B * WK) x (k l)) j
      = scoreSoftmax beta (fun l => qkScore WQ WK x (k l)) j := scoreSoftmax_qkScore_congr beta (qkMatrix_gauge hAB WQ WK) x k j
