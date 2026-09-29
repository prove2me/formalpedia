-- Prove2me | solution 1 for BookProof.GaugeFixing.matrixModel_c_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-09-07T16:34:58.50886+00:00
-- url     : https://prove2.me/submissions/b743be76-98d6-416b-a295-70e66a6ff38c

-- Generated from ChapterGaugeFixing.lean — solution of BookProof.GaugeFixing.matrixModel_c_ne_zero
import Mathlib
import Definitions.Def_ChapterGaugeFixing
import Theorems.Thm_BookProof_GaugeFixing_Qm_ne_zero
open BookProof.GaugeFixing























variable {F : BiDegree → Type} (S : GaugeFixingSystem F)

set_option maxHeartbeats 1000000 in
theorem solution : (matrixModel.c : Mat2) ≠ 0 := by

  simpa [matrixModel] using Qm_ne_zero
