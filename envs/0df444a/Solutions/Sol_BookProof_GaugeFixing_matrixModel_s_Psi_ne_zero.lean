-- Prove2me | solution 1 for BookProof.GaugeFixing.matrixModel_s_Psi_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-09-07T17:21:57.052853+00:00
-- url     : https://prove2.me/submissions/5243248f-5ac1-4bc0-bb83-3416e10a3c54

-- Generated from ChapterGaugeFixing.lean — solution of BookProof.GaugeFixing.matrixModel_s_Psi_ne_zero
import Mathlib
import Definitions.Def_ChapterGaugeFixing
import Theorems.Thm_BookProof_GaugeFixing_matrixModel_s_Psi
open BookProof.GaugeFixing























variable {F : BiDegree → Type} (S : GaugeFixingSystem F)

set_option maxHeartbeats 1000000 in
theorem solution : (sTop matrixModel (Psi matrixModel) : Mat2) ≠ 0 := by

  rw [matrixModel_s_Psi]; exact one_ne_zero
