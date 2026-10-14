-- Prove2me | solution 1 for BookProof.ChapterTrajectory.dslit_condProb
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-13T13:33:12.015661+00:00
-- url     : https://prove2.me/submissions/89016ceb-20d2-4624-99af-cc1400342954

-- Generated from ChapterTrajectory.lean — theorem BookProof.ChapterTrajectory.dslit_condProb
import Mathlib
import Definitions.Def_ChapterTrajectory
import Definitions.Def_ChapterDoubleSlit
open BookProof.ChapterDoubleSlit
open BookProof.ChapterTrajectory


open scoped BigOperators Matrix


variable {n : ℕ}
open BookProof.ChapterTrajectory

theorem solution(f a : Fin 2) : condProb H H psi0 f a = 1 / 2 := by
  have hs : ‖(1 / (Real.sqrt 2 : ℂ))‖ ^ 2 = 1 / 2 := by
    rw [norm_div, norm_one, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg 2), div_pow, Real.sq_sqrt (by norm_num)]
    norm_num
  fin_cases f <;> fin_cases a <;> simp [condProb, jointProb, finalProb, midProb, transProb, H, psi0, Matrix.mulVec, dotProduct, Fin.sum_univ_two, norm_mul, mul_pow, hs] <;> norm_num
