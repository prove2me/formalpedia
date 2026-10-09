-- Prove2me | solution 1 for BookProof.ChapterAttentionQKCircuit.qkScore_gauge
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-08T17:35:53.375607+00:00
-- url     : https://prove2.me/submissions/a1cce875-c3e3-496b-8c9c-e30c0c331257

-- Generated from ChapterAttentionQKCircuit.lean — solution of BookProof.ChapterAttentionQKCircuit.qkScore_gauge
import Mathlib
import Definitions.Def_ChapterAttentionQKCircuit
import Theorems.Thm_BookProof_ChapterAttentionQKCircuit_qkScore_congr_of_qkMatrix_eq
import Theorems.Thm_BookProof_ChapterAttentionQKCircuit_qkMatrix_gauge
open BookProof.ChapterAttentionQKCircuit



open scoped BigOperators

noncomputable section


open Matrix BookProof.ChapterSoftmaxSharpness BookProof.ChapterSoftmaxOrder

variable {d n m : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

variable {d n m : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

set_option maxHeartbeats 1000000 in
theorem solution {A B : Matrix (Fin d) (Fin d) ℝ} (hAB : Aᵀ * B = 1)
    (WQ WK : Matrix (Fin d) (Fin n) ℝ) (x y : Fin n → ℝ) :
    qkScore (A * WQ) (B * WK) x y = qkScore WQ WK x y := qkScore_congr_of_qkMatrix_eq (qkMatrix_gauge hAB WQ WK) x y
