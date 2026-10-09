-- Prove2me | solution 1 for BookProof.ChapterA3.lorentzLie_smul
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-08T15:07:54.77874+00:00
-- url     : https://prove2.me/submissions/34bb3d64-15e7-47b4-87c0-79816133f873

-- Generated from ChapterA3e.lean — solution of BookProof.ChapterA3.lorentzLie_smul
import Mathlib
import Definitions.Def_ChapterA3e
open BookProof.ChapterA3



open Matrix

set_option maxHeartbeats 1000000 in
theorem solution {A : Matrix (Fin 4) (Fin 4) ℝ} (c : ℝ)
    (h : A ∈ LorentzLie) : c • A ∈ LorentzLie := by

  simp only [LorentzLie, Set.mem_setOf_eq] at *
  rw [Matrix.smul_mul, Matrix.transpose_smul, Matrix.mul_smul, ← smul_add, h,
    smul_zero]
