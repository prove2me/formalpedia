-- Prove2me | solution 1 for BookProof.NavierStokes.ghost_CAR
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-09-07T16:46:18.172063+00:00
-- url     : https://prove2.me/submissions/5fe1473c-fbc2-46ca-8ea6-ba04a17d7281

-- Generated from ChapterNavierStokes.lean — solution of BookProof.NavierStokes.ghost_CAR
import Mathlib
import Definitions.Def_ChapterNavierStokes
import Theorems.Thm_BookProof_NavierStokes_ghostCreate_eq
open BookProof.NavierStokes













open Matrix

set_option maxHeartbeats 1000000 in
theorem solution : ghostAnnih * ghostCreate + ghostCreate * ghostAnnih = 1 := by

  rw [ghostCreate_eq]
  ext i j; fin_cases i <;> fin_cases j <;> simp [ghostAnnih]
