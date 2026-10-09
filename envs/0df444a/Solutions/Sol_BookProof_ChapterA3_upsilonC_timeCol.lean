-- Prove2me | solution 1 for BookProof.ChapterA3.upsilonC_timeCol
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-08T15:51:10.855951+00:00
-- url     : https://prove2.me/submissions/c3486412-b93c-4ac1-b3c3-a6b75b1fe82f

-- Generated from ChapterA4c.lean — solution of BookProof.ChapterA3.upsilonC_timeCol
import Mathlib
import Definitions.Def_ChapterA4c
import Definitions.Def_ChapterA3h
open BookProof.ChapterA3



open Matrix
open scoped ComplexConjugate

set_option maxHeartbeats 1000000 in
theorem solution (T : Matrix (Fin 2) (Fin 2) ℂ) (μ : Fin 4) :
    UpsilonC T μ 0 = pauliCoeff (Tᴴ * T) μ := by

  unfold UpsilonC
  have h0 : pauliσ 0 = (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
    ext i j; fin_cases i <;> fin_cases j <;> simp [pauliσ]
  simp [h0]
