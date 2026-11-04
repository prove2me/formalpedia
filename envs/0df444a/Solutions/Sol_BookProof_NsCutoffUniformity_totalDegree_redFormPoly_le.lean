-- Prove2me | solution 1 for BookProof.NsCutoffUniformity.totalDegree_redFormPoly_le
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-11-03T22:25:18.196076+00:00
-- url     : https://prove2.me/submissions/49c5a420-7ede-455c-803f-a9ad50ec4ed9

-- Generated from ChapterNsCutoffUniformity.lean — solution of BookProof.NsCutoffUniformity.totalDegree_redFormPoly_le
import Mathlib
import Definitions.Def_ChapterNsCutoffUniformity
import Definitions.Def_ChapterNavierStokesFullEulerianFock
open BookProof.NsCutoffUniformity




open MvPolynomial BookProof.NsFullEuler

noncomputable section

variable {n : ℕ}

variable {n : ℕ}
variable {ι : Type*}
variable (nu : ℝ) (k : Fin 3 → ℝ)
private theorem totalDegree_C_mul_X_le (c : ℂ) (a : Fin (n * 6)) :
    (C c * X a : MvPolynomial (Fin (n * 6)) ℂ).totalDegree ≤ 2 := by
  refine (totalDegree_mul _ _).trans ?_
  rw [totalDegree_C, totalDegree_X]
  norm_num
private theorem totalDegree_C_mul_X_mul_X_le (c : ℂ) (a b : Fin (n * 6)) :
    (C c * (X a * X b) : MvPolynomial (Fin (n * 6)) ℂ).totalDegree ≤ 2 := by
  refine (totalDegree_mul _ _).trans ?_
  have hab : (X a * X b : MvPolynomial (Fin (n * 6)) ℂ).totalDegree ≤ 2 := by
    refine (totalDegree_mul _ _).trans ?_
    rw [totalDegree_X, totalDegree_X]
  rw [totalDegree_C]
  simpa using hab

set_option maxHeartbeats 1000000 in
theorem solution (p : Fin n) (r : Fin 7) :
    (redFormPoly nu k n p r).totalDegree ≤ 2 := by

  rw [redFormPoly]
  split
  · refine (totalDegree_add _ _).trans ?_
    refine max_le ?_ (totalDegree_C_mul_X_le _ _)
    rw [totalDegree_X]
    norm_num
  · split
    · refine (totalDegree_finset_sum _ _).trans (Finset.sup_le fun j _ => ?_)
      exact totalDegree_C_mul_X_mul_X_le _ _ _
    · refine (totalDegree_finset_sum _ _).trans (Finset.sup_le fun j _ => ?_)
      exact totalDegree_C_mul_X_le _ _
