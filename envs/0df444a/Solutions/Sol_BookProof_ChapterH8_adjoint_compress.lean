-- Prove2me | solution 1 for BookProof.ChapterH8.adjoint_compress
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-02T02:57:33.287505+00:00
-- url     : https://prove2.me/submissions/f8c2ae74-4691-46a6-9ba6-ca4ac322b456

import Mathlib
import Definitions.Def_ChapterH8

set_option autoImplicit false

open BookProof.ChapterH8

noncomputable section

open BookProof.ChapterH4 BookProof.ChapterH5 BookProof.ChapterH6

open BookProof.ChapterH8 BookProof.ChapterH4 BookProof.ChapterH5 BookProof.ChapterH6 ContinuousLinearMap in
theorem solution {E F : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
    (V : F →L[ℂ] E) (X : E →L[ℂ] E) :
    adjoint (compress V X) = compress V (adjoint X) := by
  simp only [BookProof.ChapterH4.compress, ContinuousLinearMap.adjoint_comp,
    ContinuousLinearMap.adjoint_adjoint, ContinuousLinearMap.comp_assoc]

end
