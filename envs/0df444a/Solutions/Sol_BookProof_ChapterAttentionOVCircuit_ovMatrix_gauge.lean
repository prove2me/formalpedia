-- Prove2me | solution 1 for BookProof.ChapterAttentionOVCircuit.ovMatrix_gauge
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-08T17:30:40.889667+00:00
-- url     : https://prove2.me/submissions/d9417867-cf72-4739-a928-c6247b838db7

-- Generated from ChapterAttentionOVCircuit.lean — solution of BookProof.ChapterAttentionOVCircuit.ovMatrix_gauge
import Mathlib
import Definitions.Def_ChapterAttentionOVCircuit
open BookProof.ChapterAttentionOVCircuit



open scoped BigOperators

noncomputable section


open Matrix BookProof.ChapterSoftmaxSharpness BookProof.ChapterSoftmaxOrder

variable {d n p m : ℕ}

variable {d n p m : ℕ}

set_option maxHeartbeats 1000000 in
theorem solution {A B : Matrix (Fin d) (Fin d) ℝ} (hAB : A * B = 1)
    (WO : Matrix (Fin n) (Fin d) ℝ) (WV : Matrix (Fin d) (Fin n) ℝ) :
    ovMatrix (WO * A) (B * WV) = ovMatrix WO WV := by

  rw [ovMatrix, ovMatrix, Matrix.mul_assoc, ← Matrix.mul_assoc A B WV, hAB, Matrix.one_mul]
