-- Prove2me | solution 2 for BookProof.GaugeFixing.Pm_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-09-07T15:22:32.747888+00:00
-- url     : https://prove2.me/submissions/68d0f7b8-ddaa-4c0b-afce-a5b009e82211

-- Generated from ChapterGaugeFixing.lean — solution of BookProof.GaugeFixing.Pm_ne_zero
import Mathlib
import Definitions.Def_ChapterGaugeFixing
open BookProof.GaugeFixing























variable {F : BiDegree → Type} (S : GaugeFixingSystem F)

set_option maxHeartbeats 1000000 in
theorem solution : Pm ≠ 0 := by

  intro h
  have h10 : Pm 1 0 = (0 : Mat2) 1 0 := by rw [h]
  simp [Pm] at h10
