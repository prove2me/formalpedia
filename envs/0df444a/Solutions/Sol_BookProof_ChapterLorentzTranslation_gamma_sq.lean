-- Prove2me | solution 1 for BookProof.ChapterLorentzTranslation.gamma_sq
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-09T21:21:04.908218+00:00
-- url     : https://prove2.me/submissions/a4e15bdd-9f6d-41da-98cc-37cbc8f014be

-- Generated from ChapterLorentzTranslation.lean — solution of BookProof.ChapterLorentzTranslation.gamma_sq
import Mathlib
import Definitions.Def_ChapterLorentzTranslation
open BookProof.ChapterLorentzTranslation




open scoped BigOperators

set_option maxHeartbeats 1000000 in
theorem solution (w : Fin 3 → ℝ) : gamma w ^ 2 = 1 + ∑ i, (w i) ^ 2 := by

  unfold gamma; rw [Real.sq_sqrt (by positivity)]
