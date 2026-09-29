-- Prove2me | solution 1 for BookProof.GaugeFixing.Pm_mul_Vm
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-07T14:48:28.200303+00:00
-- url     : https://prove2.me/submissions/58dd56be-a547-4395-a149-539e74feb09a

-- Generated from ChapterGaugeFixing.lean — theorem BookProof.GaugeFixing.Pm_mul_Vm
import Mathlib
import Definitions.Def_ChapterGaugeFixing
open BookProof.GaugeFixing






















variable {F : BiDegree → Type} (S : GaugeFixingSystem F)

theorem solution : Pm * Vm = Pm := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [Pm, Vm, Matrix.mul_apply, Fin.sum_univ_two]
