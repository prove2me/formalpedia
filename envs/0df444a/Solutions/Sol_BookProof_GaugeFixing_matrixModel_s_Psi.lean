-- Prove2me | solution 1 for BookProof.GaugeFixing.matrixModel_s_Psi
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-09-07T17:02:26.151195+00:00
-- url     : https://prove2.me/submissions/0c22a3d5-fa70-493e-ba95-decc559d92f5

-- Generated from ChapterGaugeFixing.lean — solution of BookProof.GaugeFixing.matrixModel_s_Psi
import Mathlib
import Definitions.Def_ChapterGaugeFixing
import Theorems.Thm_BookProof_GaugeFixing_matrixModel_Psi
open BookProof.GaugeFixing























variable {F : BiDegree → Type} (S : GaugeFixingSystem F)

set_option maxHeartbeats 1000000 in
theorem solution : (sTop matrixModel (Psi matrixModel) : Mat2) = 1 := by

  change sMat (-1) (Psi matrixModel) = 1
  rw [show (Psi matrixModel : Mat2) = Pm from matrixModel_Psi]
  exact sMat_Pm
