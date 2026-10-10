-- Prove2me | solution 1 for BookProof.ChapterLorentzTranslation.properTime_add
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-09T21:21:38.542485+00:00
-- url     : https://prove2.me/submissions/117416b0-7bd4-4157-9834-21c16fce4054

-- Generated from ChapterLorentzTranslation.lean — solution of BookProof.ChapterLorentzTranslation.properTime_add
import Mathlib
import Definitions.Def_ChapterLorentzTranslation
open BookProof.ChapterLorentzTranslation




open scoped BigOperators

set_option maxHeartbeats 1000000 in
theorem solution (w : Fin 3 → ℝ) (x0 y0 : ℝ) (xs ys : Fin 3 → ℝ) :
    properTime w (x0 + y0) (xs + ys) = properTime w x0 xs + properTime w y0 ys := by

  unfold properTime
  simp only [Pi.add_apply, mul_add, Finset.sum_add_distrib]
  ring
