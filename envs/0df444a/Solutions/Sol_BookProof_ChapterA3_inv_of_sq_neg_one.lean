-- Prove2me | solution 1 for BookProof.ChapterA3.inv_of_sq_neg_one
-- status  : ACCEPTED   (prove)
-- author  : @miao
-- created : 2026-10-06T18:05:12.764328+00:00
-- url     : https://prove2.me/submissions/9c040706-b0ad-4af5-95e0-dde77d39dc0c

import Mathlib
import Definitions.Def_ChapterA3d
open BookProof.ChapterA3 Matrix

theorem solution {S : Matrix (Fin 4) (Fin 4) ℝ} (h : S * S = -1) :
    S⁻¹ = -S := by
  apply Matrix.inv_eq_left_inv
  simp [neg_mul, h]

#print axioms solution
