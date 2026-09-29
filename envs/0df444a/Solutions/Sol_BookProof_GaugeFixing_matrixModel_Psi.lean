-- Prove2me | solution 1 for BookProof.GaugeFixing.matrixModel_Psi
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-09-07T16:33:37.265709+00:00
-- url     : https://prove2.me/submissions/18a08a59-e98f-4e7c-9daf-a4792ff4ef78

-- Generated from ChapterGaugeFixing.lean — solution of BookProof.GaugeFixing.matrixModel_Psi
import Mathlib
import Definitions.Def_ChapterGaugeFixing
import Theorems.Thm_BookProof_GaugeFixing_Pm_mul_Vm
open BookProof.GaugeFixing























variable {F : BiDegree → Type} (S : GaugeFixingSystem F)

set_option maxHeartbeats 1000000 in
theorem solution : (Psi matrixModel : Mat2) = Pm := by

  simp [Psi, gaugeField, matrixModel, Pm_mul_Vm]
