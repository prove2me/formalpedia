-- Prove2me | solution 1 for BookProof.ChapterH8.adjoint_pow
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-02T03:06:33.133766+00:00
-- url     : https://prove2.me/submissions/3edbd21c-b52d-4608-85c6-4236417cbbd7

import Mathlib
import Definitions.Def_ChapterH8

set_option autoImplicit false

universe u

noncomputable section

open BookProof.ChapterH8 BookProof.ChapterH4 BookProof.ChapterH5 BookProof.ChapterH6

open ContinuousLinearMap in
theorem solution {F : Type u} [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
    (A : F →L[ℂ] F) (k : ℕ) : adjoint (A ^ k) = (adjoint A) ^ k := by
  rw [← ContinuousLinearMap.star_eq_adjoint, ← ContinuousLinearMap.star_eq_adjoint, star_pow]

end
