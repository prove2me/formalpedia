-- Prove2me | solution 1 for BookProof.ChapterH6.krylov_rayleigh_transfer
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-03T00:59:32.940987+00:00
-- url     : https://prove2.me/submissions/5515108c-0375-4145-8a25-4b8c09d5b243

import Mathlib
import Definitions.Def_ChapterH6
import Definitions.Def_ChapterH4

set_option autoImplicit false

open BookProof.ChapterH4 BookProof.ChapterH6 in
theorem solution {E F : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
    (V : F →L[ℂ] E) (X : E →L[ℂ] E) (y : F) :
    inner ℂ y (compress V X y) = inner ℂ (V y) (X (V y)) := by
  unfold compress
  rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.adjoint_inner_right]
  rfl
