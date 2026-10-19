-- Prove2me | solution 1 for BookProof.ChapterF4.observable_matrix_identity
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T10:42:55.228412+00:00
-- url     : https://prove2.me/submissions/98cbf929-f9d5-43e6-b589-cb899c310c1c

import Mathlib
import Definitions.Def_ChapterF4
-- Generated from ChapterF4.lean — theorem BookProof.ChapterF4.observable_matrix_identity
open BookProof.ChapterF4


open scoped BigOperators Matrix

variable {d k : ℕ}
theorem solution {dd kk : ℕ} (W : Matrix (Fin dd) (Fin kk) ℂ)
    (a : Fin dd) (r s : Fin kk) :
    Matrix.trace ((Matrix.single r s (1 : ℂ) : Matrix (Fin kk) (Fin kk) ℂ)ᴴ * Wᴴ
        * (Matrix.single a a (1 : ℂ) : Matrix (Fin dd) (Fin dd) ℂ) * W)
      = (starRingEnd ℂ) (W a r) * W a s := by
  rw [Matrix.conjTranspose_single, Matrix.mul_assoc, Matrix.mul_assoc, Matrix.trace_single_mul]
  simp only [star_one, one_smul, Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.single_apply]
  simp [Finset.sum_ite_eq, Finset.sum_ite_eq', ite_and]
