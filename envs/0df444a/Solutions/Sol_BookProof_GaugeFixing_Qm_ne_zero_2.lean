-- Prove2me | solution 2 for BookProof.GaugeFixing.Qm_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-09-07T15:24:03.229213+00:00
-- url     : https://prove2.me/submissions/f8151c4c-01ad-4961-a436-2b4233be4148

-- Generated from ChapterGaugeFixing.lean — solution of BookProof.GaugeFixing.Qm_ne_zero
import Mathlib
import Definitions.Def_ChapterGaugeFixing
open BookProof.GaugeFixing























variable {F : BiDegree → Type} (S : GaugeFixingSystem F)

set_option maxHeartbeats 1000000 in
theorem solution : Qm ≠ 0 := by

  intro h
  have h01 : Qm 0 1 = (0 : Mat2) 0 1 := by rw [h]
  simp [Qm] at h01
