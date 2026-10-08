-- Prove2me | solution 1 for BookProof.ChapterA3.isPin_of_sq_neg_one
-- status  : ACCEPTED   (prove)
-- author  : @miao
-- created : 2026-10-06T18:05:15.389607+00:00
-- url     : https://prove2.me/submissions/8c9ab35c-cdff-4731-8b11-e60473051902

import Mathlib
import Definitions.Def_ChapterA3d
open BookProof.ChapterA3 Matrix

theorem solution {S : Matrix (Fin 4) (Fin 4) ℝ} (h : S * S = -1)
    (hL : ∃ Λ, HasLambda S Λ) : IsPin S := by
  have hd : S.det * S.det = 1 := by
    have hd := congrArg Matrix.det h
    norm_num [Matrix.det_mul, Matrix.det_neg] at hd
    exact hd
  have hn : S.det ≠ 0 := by intro hz; simp [hz] at hd
  refine ⟨isUnit_iff_ne_zero.mpr hn, ?_, hL⟩
  rcases mul_self_eq_one_iff.mp hd with hp | hp <;> simp [hp]

#print axioms solution
