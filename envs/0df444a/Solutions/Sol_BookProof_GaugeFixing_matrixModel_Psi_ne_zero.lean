-- Prove2me | solution 1 for BookProof.GaugeFixing.matrixModel_Psi_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-09-07T17:00:30.425333+00:00
-- url     : https://prove2.me/submissions/a1e6865c-9ccb-4fd6-beab-11554a79c92c

-- Generated from ChapterGaugeFixing.lean — solution of BookProof.GaugeFixing.matrixModel_Psi_ne_zero
import Mathlib
import Definitions.Def_ChapterGaugeFixing
import Theorems.Thm_BookProof_GaugeFixing_Pm_ne_zero
import Theorems.Thm_BookProof_GaugeFixing_matrixModel_Psi
open BookProof.GaugeFixing























variable {F : BiDegree → Type} (S : GaugeFixingSystem F)

set_option maxHeartbeats 1000000 in
theorem solution : (Psi matrixModel : Mat2) ≠ 0 := by

  rw [matrixModel_Psi]; exact Pm_ne_zero
