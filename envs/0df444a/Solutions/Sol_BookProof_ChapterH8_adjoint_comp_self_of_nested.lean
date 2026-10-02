-- Prove2me | solution 1 for BookProof.ChapterH8.adjoint_comp_self_of_nested
-- status  : ACCEPTED   (prove)
-- author  : @sometik179
-- created : 2026-10-01T16:45:35.507226+00:00
-- url     : https://prove2.me/submissions/b2207652-6940-4e9c-86bd-94bdb20f69ee

import Mathlib.Analysis.InnerProductSpace.Adjoint

variable {E F G : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
  [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]

open ContinuousLinearMap

-- https://prove2.me/theorems/b6df429c-5fa5-483a-ac23-12dd913d08be
theorem solution (Vn : F →L[ℂ] E) (Vm : G →L[ℂ] E) (J : F →L[ℂ] G)
    (hJ : Vn = Vm.comp J)
    (hVm : (adjoint Vm).comp Vm = ContinuousLinearMap.id ℂ G)
    (hJJ : (adjoint J).comp J = ContinuousLinearMap.id ℂ F) :
    (adjoint Vn).comp Vn = ContinuousLinearMap.id ℂ F := by
  rw [hJ, adjoint_comp, comp_assoc, ← comp_assoc (adjoint Vm), hVm,
    id_comp, hJJ]
