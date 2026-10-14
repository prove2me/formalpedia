-- Prove2me | solution 1 for BookProof.ChapterTrajectory.midProb_H
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-12T12:54:48.604175+00:00
-- url     : https://prove2.me/submissions/131cfa39-0380-4261-bad9-46796cce4a66

-- Generated from ChapterTrajectory.lean — theorem BookProof.ChapterTrajectory.midProb_H
import Mathlib
import Definitions.Def_ChapterTrajectory
import Definitions.Def_ChapterDoubleSlit
open BookProof.ChapterDoubleSlit
open BookProof.ChapterTrajectory


open scoped BigOperators Matrix


variable {n : ℕ}
open BookProof.ChapterTrajectory

theorem solution(a : Fin 2) : midProb H psi0 a = 1 / 2 := by
  have h2 : ‖((1 / Real.sqrt 2 : ℝ) : ℂ)‖ ^ 2 = 1 / 2 := by
    rw [Complex.norm_real, Real.norm_eq_abs, sq_abs, div_pow, Real.sq_sqrt (by norm_num)]
    norm_num
  fin_cases a <;> simpa [midProb, H, psi0, Matrix.mulVec, dotProduct, Fin.sum_univ_two] using h2
