-- Prove2me | solution 1 for BookProof.ChapterH8.adjoint_comp_nested
-- status  : ACCEPTED   (prove)
-- author  : @sometik179
-- created : 2026-10-01T16:45:20.279568+00:00
-- url     : https://prove2.me/submissions/1ebbed1d-228f-4c64-b5f0-6783ae5ff762

import Mathlib.Analysis.InnerProductSpace.Adjoint

variable {E F G : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
  [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]

open ContinuousLinearMap

-- https://prove2.me/theorems/2b918845-247e-4507-884b-0f5165b268c5
theorem solution (Vn : F →L[ℂ] E) (Vm : G →L[ℂ] E) (J : F →L[ℂ] G)
    (hJ : Vn = Vm.comp J)
    (hVm : (adjoint Vm).comp Vm = ContinuousLinearMap.id ℂ G) :
    (adjoint Vn).comp Vm = adjoint J := by
  rw [hJ, adjoint_comp, comp_assoc, hVm, comp_id]
