-- Prove2me | solution 1 for BookProof.ChapterA3.isPin_neg
-- status  : ACCEPTED   (prove)
-- author  : @miao
-- created : 2026-10-06T18:05:24.140476+00:00
-- url     : https://prove2.me/submissions/1a01a95c-0f7b-40ab-a9d2-f9333394e72b

import Mathlib
import Definitions.Def_ChapterA3c
open BookProof.ChapterA3 Matrix

theorem solution {S : Matrix (Fin 4) (Fin 4) ℝ} (h : IsPin S) : IsPin (-S) := by
  rcases h with ⟨hu, hd, Λ, hΛ⟩
  have hi : (-S)⁻¹ = -S⁻¹ := by
    apply Matrix.inv_eq_left_inv
    simpa using Matrix.nonsing_inv_mul S hu
  refine ⟨?_, ?_, Λ, ?_⟩
  · simpa [Matrix.det_neg] using hu
  · simpa [Matrix.det_neg] using hd
  · intro μ
    simpa [hi, neg_mul, mul_neg] using hΛ μ

#print axioms solution
