-- Prove2me | solution 2 for BookProof.GaugeFixing.Pm_mul_Vm
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-09-07T15:21:01.796717+00:00
-- url     : https://prove2.me/submissions/e6aa3e9b-f627-42e9-a88e-ae1b0d7d7e8d

-- Generated from ChapterGaugeFixing.lean — solution of BookProof.GaugeFixing.Pm_mul_Vm
import Mathlib
import Definitions.Def_ChapterGaugeFixing
open BookProof.GaugeFixing























variable {F : BiDegree → Type} (S : GaugeFixingSystem F)

set_option maxHeartbeats 1000000 in
theorem solution : Pm * Vm = Pm := by

  ext i j; fin_cases i <;> fin_cases j <;> simp [Pm, Vm, Matrix.mul_apply, Fin.sum_univ_two]
