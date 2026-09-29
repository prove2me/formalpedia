-- Prove2me | solution 1 for BookProof.GaugeFixing.Qm_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-07T14:45:39.215512+00:00
-- url     : https://prove2.me/submissions/7dfc172e-1477-437d-80ee-fe6527666520

-- Generated from ChapterGaugeFixing.lean — theorem BookProof.GaugeFixing.Qm_ne_zero
import Mathlib
import Definitions.Def_ChapterGaugeFixing
open BookProof.GaugeFixing






















variable {F : BiDegree → Type} (S : GaugeFixingSystem F)

theorem solution : Qm ≠ 0 := by
  intro h
  have h01 : Qm 0 1 = (0 : Mat2) 0 1 := by rw [h]
  simp [Qm] at h01
