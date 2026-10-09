-- Prove2me | solution 1 for BookProof.ChapterA5.coeffBoostZ_sq
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-08T15:53:32.130132+00:00
-- url     : https://prove2.me/submissions/f3fc3fed-763d-4b18-8803-cf1f6f0425e2

-- Generated from ChapterA5.lean — solution of BookProof.ChapterA5.coeffBoostZ_sq
import Mathlib
import Definitions.Def_ChapterA5
open BookProof.ChapterA5



open Matrix


open BookProof.ChapterA3

set_option maxHeartbeats 1000000 in
theorem solution (j : Fin 3) : coeffBoostZ j * coeffBoostZ j = 1 := by

  fin_cases j <;> decide
