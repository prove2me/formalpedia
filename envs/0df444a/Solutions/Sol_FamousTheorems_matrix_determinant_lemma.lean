-- Prove2me | solution 1 for FamousTheorems.matrix_determinant_lemma
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-09-24T08:03:47.258985+00:00
-- url     : https://prove2.me/submissions/cbd5ead4-be68-4c0e-b8b0-6b0240ad8142

import Mathlib

theorem solution {m ι α : Type*} [Fintype m] [DecidableEq m] [CommRing α] [Unique ι] {A : Matrix m m α}
    (hA : IsUnit A.det) (u v : m → α) :
    (A + Matrix.replicateCol ι u * Matrix.replicateRow ι v).det =
      A.det * (1 + Matrix.replicateRow ι v * A⁻¹ * Matrix.replicateCol ι u).det := by
  exact Matrix.det_add_replicateCol_mul_replicateRow (ι := ι) hA u v
