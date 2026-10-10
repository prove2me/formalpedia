-- Prove2me | solution 1 for BookProof.ChapterLorentzTranslation.mass_shell
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-09T21:21:09.413094+00:00
-- url     : https://prove2.me/submissions/c40c59c4-aa29-4c62-be2a-75961868c98f

-- Generated from ChapterLorentzTranslation.lean — solution of BookProof.ChapterLorentzTranslation.mass_shell
import Mathlib
import Definitions.Def_ChapterLorentzTranslation
import Theorems.Thm_BookProof_ChapterLorentzTranslation_gamma_sq
open BookProof.ChapterLorentzTranslation




open scoped BigOperators

set_option maxHeartbeats 1000000 in
theorem solution (w : Fin 3 → ℝ) : gamma w ^ 2 - ∑ i, (w i) ^ 2 = 1 := by

  rw [gamma_sq]; ring
