-- Prove2me | solution 1 for BookProof.ChapterLorentzTranslation.transPhase_rest
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-09T21:24:15.487069+00:00
-- url     : https://prove2.me/submissions/5e9616de-5f0b-4998-9bb1-ead07e878aba

-- Generated from ChapterLorentzTranslation.lean — solution of BookProof.ChapterLorentzTranslation.transPhase_rest
import Mathlib
import Definitions.Def_ChapterLorentzTranslation
import Theorems.Thm_BookProof_ChapterLorentzTranslation_properTime_rest
open BookProof.ChapterLorentzTranslation




open scoped BigOperators

set_option maxHeartbeats 1000000 in
theorem solution (M : ℝ) (x0 : ℝ) (xs : Fin 3 → ℝ) :
    transPhase M (fun _ => 0) x0 xs = Complex.exp (Complex.I * (M : ℂ) * (x0 : ℂ)) := by

  unfold transPhase; rw [properTime_rest]
