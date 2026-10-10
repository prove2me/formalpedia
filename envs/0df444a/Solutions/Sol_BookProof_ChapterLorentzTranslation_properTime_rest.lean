-- Prove2me | solution 1 for BookProof.ChapterLorentzTranslation.properTime_rest
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-09T21:22:27.458401+00:00
-- url     : https://prove2.me/submissions/6d2fea63-bb39-44ce-a913-e7ae5225e782

-- Generated from ChapterLorentzTranslation.lean — solution of BookProof.ChapterLorentzTranslation.properTime_rest
import Mathlib
import Definitions.Def_ChapterLorentzTranslation
import Theorems.Thm_BookProof_ChapterLorentzTranslation_gamma_zero
open BookProof.ChapterLorentzTranslation




open scoped BigOperators

set_option maxHeartbeats 1000000 in
theorem solution (x0 : ℝ) (xs : Fin 3 → ℝ) :
    properTime (fun _ => 0) x0 xs = x0 := by

  unfold properTime; simp [gamma_zero]
