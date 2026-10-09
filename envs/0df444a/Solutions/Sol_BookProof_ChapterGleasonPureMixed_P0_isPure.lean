-- Prove2me | solution 1 for BookProof.ChapterGleasonPureMixed.P0_isPure
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-09T07:47:23.147398+00:00
-- url     : https://prove2.me/submissions/191f12c6-a81f-4216-bc30-c293228a3ca9

-- Generated from ChapterGleasonPureMixed.lean — solution of BookProof.ChapterGleasonPureMixed.P0_isPure
import Mathlib
import Definitions.Def_ChapterGleasonPureMixed
open BookProof.ChapterGleasonPureMixed



open scoped BigOperators
open Matrix

set_option maxHeartbeats 1000000 in
theorem solution : IsPureState P0 := by

  refine ⟨?_, ?_, ?_⟩
  · ext i j; fin_cases i <;> fin_cases j <;> simp [P0]
  · ext i j; fin_cases i <;> fin_cases j <;>
      simp [P0, Matrix.mul_apply, Fin.sum_univ_two]
  · simp [P0, Matrix.trace, Fin.sum_univ_two]
