-- Prove2me | solution 1 for BookProof.ChapterAttentionQKCircuit.qkScore_congr_of_qkMatrix_eq
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-08T17:35:18.369908+00:00
-- url     : https://prove2.me/submissions/25288043-a682-45e1-a8a3-ac0eee833f25

-- Generated from ChapterAttentionQKCircuit.lean — solution of BookProof.ChapterAttentionQKCircuit.qkScore_congr_of_qkMatrix_eq
import Mathlib
import Definitions.Def_ChapterAttentionQKCircuit
import Theorems.Thm_BookProof_ChapterAttentionQKCircuit_qkScore_eq_bilinear
open BookProof.ChapterAttentionQKCircuit



open scoped BigOperators

noncomputable section


open Matrix BookProof.ChapterSoftmaxSharpness BookProof.ChapterSoftmaxOrder

variable {d n m : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

variable {d n m : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

set_option maxHeartbeats 1000000 in
theorem solution {WQ₁ WK₁ WQ₂ WK₂ : Matrix (Fin d) (Fin n) ℝ}
    (h : qkMatrix WQ₁ WK₁ = qkMatrix WQ₂ WK₂) (x y : Fin n → ℝ) :
    qkScore WQ₁ WK₁ x y = qkScore WQ₂ WK₂ x y := by

  rw [qkScore_eq_bilinear, qkScore_eq_bilinear, h]
