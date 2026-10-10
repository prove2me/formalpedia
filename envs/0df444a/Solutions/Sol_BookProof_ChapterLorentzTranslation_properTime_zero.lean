-- Prove2me | solution 1 for BookProof.ChapterLorentzTranslation.properTime_zero
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-09T21:22:13.428983+00:00
-- url     : https://prove2.me/submissions/684857f7-6f51-4ec3-9350-ea914f53d2ec

-- Generated from ChapterLorentzTranslation.lean — solution of BookProof.ChapterLorentzTranslation.properTime_zero
import Mathlib
import Definitions.Def_ChapterLorentzTranslation
open BookProof.ChapterLorentzTranslation




open scoped BigOperators

set_option maxHeartbeats 1000000 in
theorem solution (w : Fin 3 → ℝ) : properTime w 0 (0 : Fin 3 → ℝ) = 0 := by

  unfold properTime; simp
