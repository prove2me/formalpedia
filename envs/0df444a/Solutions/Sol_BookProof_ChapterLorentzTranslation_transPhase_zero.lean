-- Prove2me | solution 1 for BookProof.ChapterLorentzTranslation.transPhase_zero
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-09T21:22:41.464858+00:00
-- url     : https://prove2.me/submissions/0ac251d7-4a81-48af-b2a5-9a1a9d5d18ed

-- Generated from ChapterLorentzTranslation.lean — solution of BookProof.ChapterLorentzTranslation.transPhase_zero
import Mathlib
import Definitions.Def_ChapterLorentzTranslation
import Theorems.Thm_BookProof_ChapterLorentzTranslation_properTime_zero
open BookProof.ChapterLorentzTranslation




open scoped BigOperators

set_option maxHeartbeats 1000000 in
theorem solution (M : ℝ) (w : Fin 3 → ℝ) :
    transPhase M w 0 (0 : Fin 3 → ℝ) = 1 := by

  unfold transPhase; rw [properTime_zero]; simp
