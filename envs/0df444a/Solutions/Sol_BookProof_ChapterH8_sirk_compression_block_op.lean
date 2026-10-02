-- Prove2me | solution 1 for BookProof.ChapterH8.sirk_compression_block_op
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-02T03:36:26.030893+00:00
-- url     : https://prove2.me/submissions/ec9f967e-73f5-4476-85ef-4c492cd54cb3

import Mathlib
import Definitions.Def_ChapterH8

set_option autoImplicit false

open BookProof.ChapterH8

noncomputable section

open BookProof.ChapterH4 BookProof.ChapterH5 BookProof.ChapterH6

open BookProof.ChapterH4 BookProof.ChapterH5 BookProof.ChapterH6 ContinuousLinearMap in
theorem solution {E F G : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
    [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]
    (Vn : F →L[ℂ] E) (Vm : G →L[ℂ] E) (J : F →L[ℂ] G)
    (X : E →L[ℂ] E) (hJ : Vn = Vm.comp J) :
    compress Vn X = (adjoint J).comp ((compress Vm X).comp J) := by
  subst hJ
  simp only [compress, ContinuousLinearMap.adjoint_comp, ContinuousLinearMap.comp_assoc]

end
