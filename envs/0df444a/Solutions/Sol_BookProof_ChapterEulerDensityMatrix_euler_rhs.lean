-- Prove2me | solution 1 for BookProof.ChapterEulerDensityMatrix.euler_rhs
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-09T06:46:33.169136+00:00
-- url     : https://prove2.me/submissions/6484f4da-f0a6-4e86-89dc-2b726bead15e

-- Generated from ChapterEulerDensityMatrix.lean — solution of BookProof.ChapterEulerDensityMatrix.euler_rhs
import Mathlib
import Definitions.Def_ChapterEulerDensityMatrix
open BookProof.ChapterEulerDensityMatrix



open scoped Matrix

set_option maxHeartbeats 1000000 in
theorem solution (t : ℝ) :
    (1 / 2 : ℝ) • (1 : Matrix (Fin 2) (Fin 2) ℝ)
        + Zdiag * ((Real.cos (2 * t)) • (1 : Matrix (Fin 2) (Fin 2) ℝ)
            + (Real.sin (2 * t)) • Jdens)
      = !![1 / 2 + Real.cos (2 * t) / 2, Real.sin (2 * t) / 2;
           Real.sin (2 * t) / 2, 1 / 2 - Real.cos (2 * t) / 2] := by

  have hM : (Real.cos (2 * t)) • (1 : Matrix (Fin 2) (Fin 2) ℝ)
        + (Real.sin (2 * t)) • Jdens
      = !![Real.cos (2 * t), Real.sin (2 * t); -Real.sin (2 * t), Real.cos (2 * t)] := by
    rw [Matrix.one_fin_two]; ext i j; fin_cases i <;> fin_cases j <;> simp [Jdens]
  have h1 : (1 / 2 : ℝ) • (1 : Matrix (Fin 2) (Fin 2) ℝ) = !![1 / 2, 0; 0, 1 / 2] := by
    rw [Matrix.one_fin_two]; ext i j; fin_cases i <;> fin_cases j <;> simp
  rw [hM, h1, show Zdiag = !![1 / 2, 0; 0, -1 / 2] from rfl, Matrix.mul_fin_two]
  ext i j; fin_cases i <;> fin_cases j <;> simp <;> ring
