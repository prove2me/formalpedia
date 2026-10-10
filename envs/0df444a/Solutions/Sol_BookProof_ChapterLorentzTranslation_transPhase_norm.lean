-- Prove2me | solution 1 for BookProof.ChapterLorentzTranslation.transPhase_norm
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-09T21:24:00.503981+00:00
-- url     : https://prove2.me/submissions/d2c8a0c9-b255-4285-82da-b5cdb761faf9

-- Generated from ChapterLorentzTranslation.lean — solution of BookProof.ChapterLorentzTranslation.transPhase_norm
import Mathlib
import Definitions.Def_ChapterLorentzTranslation
open BookProof.ChapterLorentzTranslation




open scoped BigOperators

set_option maxHeartbeats 1000000 in
theorem solution (M : ℝ) (w : Fin 3 → ℝ) (x0 : ℝ) (xs : Fin 3 → ℝ) :
    ‖transPhase M w x0 xs‖ = 1 := by

  unfold transPhase
  rw [Complex.norm_exp]
  have : (Complex.I * (M : ℂ) * (properTime w x0 xs : ℂ)).re = 0 := by
    simp [Complex.mul_re, Complex.mul_im]
  rw [this, Real.exp_zero]
