-- Prove2me | solution 1 for BookProof.ChapterH7.compress_isSelfAdjoint
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-11T16:59:45.393372+00:00
-- url     : https://prove2.me/submissions/7b4d650d-2c9d-4dce-843e-9489d0141f8f

-- Generated from ChapterH7.lean — solution of BookProof.ChapterH7.compress_isSelfAdjoint
import Mathlib
import Definitions.Def_ChapterH7
import Definitions.Def_ChapterH6
import Definitions.Def_ChapterH4
open BookProof.ChapterH7



noncomputable section

open BookProof.ChapterH4 BookProof.ChapterH6

variable {E F : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

set_option maxHeartbeats 1000000 in
theorem solution (V : F →L[ℂ] E) (X : E →L[ℂ] E) (hX : IsSelfAdjoint X) :
    IsSelfAdjoint (compress V X) := by

  have hadj : ContinuousLinearMap.adjoint X = X :=
    (ContinuousLinearMap.star_eq_adjoint X).symm.trans hX
  have hstar : star (compress V X) = compress V X := by
    rw [ContinuousLinearMap.star_eq_adjoint, compress, ContinuousLinearMap.adjoint_comp,
      ContinuousLinearMap.adjoint_comp, ContinuousLinearMap.adjoint_adjoint, hadj,
      ContinuousLinearMap.comp_assoc]
  exact hstar
