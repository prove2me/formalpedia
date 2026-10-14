-- Prove2me | solution 1 for BookProof.ChapterTrajectory.dslit_finalProb
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-12T15:39:13.728891+00:00
-- url     : https://prove2.me/submissions/e70c6c28-bf99-44bd-bf4e-baf69a2a9668

-- Generated from ChapterTrajectory.lean — theorem BookProof.ChapterTrajectory.dslit_finalProb
import Mathlib
import Definitions.Def_ChapterTrajectory
import Definitions.Def_ChapterDoubleSlit
open BookProof.ChapterDoubleSlit
open BookProof.ChapterTrajectory


open scoped BigOperators Matrix


variable {n : ℕ}
open BookProof.ChapterTrajectory

theorem solution(f : Fin 2) : finalProb H H psi0 f = 1 / 2 := by
  have h2 : ‖((1 / Real.sqrt 2 : ℝ) : ℂ)‖ ^ 2 = 1 / 2 := by
    rw [Complex.norm_real, Real.norm_eq_abs, sq_abs, div_pow, Real.sq_sqrt (by norm_num)]
    norm_num
  have hm : ∀ a : Fin 2, midProb H psi0 a = 1 / 2 := by
    intro a
    fin_cases a <;> simpa [midProb, H, psi0, Matrix.mulVec, dotProduct, Fin.sum_univ_two] using h2
  have ht : ∀ f a : Fin 2, transProb H f a = 1 / 2 := by
    intro f a
    fin_cases f <;> fin_cases a <;> simpa [transProb, H] using h2
  unfold finalProb jointProb
  simp only [Fin.sum_univ_two, hm, ht]
  norm_num
