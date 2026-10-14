-- Prove2me | solution 1 for BookProof.ChapterTrajectory.transProb_H
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-12T13:29:46.578357+00:00
-- url     : https://prove2.me/submissions/522550e4-5eba-406e-9d07-1281375a1a87

-- Generated from ChapterTrajectory.lean — theorem BookProof.ChapterTrajectory.transProb_H
import Mathlib
import Definitions.Def_ChapterTrajectory
import Definitions.Def_ChapterDoubleSlit
open BookProof.ChapterDoubleSlit
open BookProof.ChapterTrajectory


open scoped BigOperators Matrix


variable {n : ℕ}
open BookProof.ChapterTrajectory

theorem solution(f a : Fin 2) : transProb H f a = 1 / 2 := by
  have h2 : ‖((1 / Real.sqrt 2 : ℝ) : ℂ)‖ ^ 2 = 1 / 2 := by
    rw [Complex.norm_real, Real.norm_eq_abs, sq_abs, div_pow, Real.sq_sqrt (by norm_num)]
    norm_num
  fin_cases f <;> fin_cases a <;> simpa [transProb, H] using h2
