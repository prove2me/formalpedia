-- Prove2me | solution 1 for BookProof.ChapterA3.lorentzLie_add
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-08T15:07:31.59206+00:00
-- url     : https://prove2.me/submissions/c156563b-471d-47be-897f-4d7ab401719a

-- Generated from ChapterA3e.lean — solution of BookProof.ChapterA3.lorentzLie_add
import Mathlib
import Definitions.Def_ChapterA3e
open BookProof.ChapterA3



open Matrix

set_option maxHeartbeats 1000000 in
theorem solution {A₁ A₂ : Matrix (Fin 4) (Fin 4) ℝ}
    (h1 : A₁ ∈ LorentzLie) (h2 : A₂ ∈ LorentzLie) : A₁ + A₂ ∈ LorentzLie := by

  simp only [LorentzLie, Set.mem_setOf_eq] at *
  have hd : (A₁ + A₂) * minkowskiMat + minkowskiMat * (A₁ + A₂)ᵀ
      = (A₁ * minkowskiMat + minkowskiMat * A₁ᵀ)
        + (A₂ * minkowskiMat + minkowskiMat * A₂ᵀ) := by
    simp only [Matrix.add_mul, Matrix.mul_add, Matrix.transpose_add]; abel
  rw [hd, h1, h2, add_zero]
