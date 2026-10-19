-- Prove2me | solution 1 for BookProof.ChapterA.conjCLM_unitScale
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-17T00:48:06.750902+00:00
-- url     : https://prove2.me/submissions/b0249a46-0d1a-4429-b62e-baf3fa8d5dc6

-- Generated from ChapterA2d.lean — solution of BookProof.ChapterA.conjCLM_unitScale
import Mathlib
import Definitions.Def_ChapterA2d
import Definitions.Def_ChapterA
open BookProof.ChapterA



open scoped ComplexConjugate InnerProductSpace


variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V]
variable {W : Type*} [NormedAddCommGroup W] [InnerProductSpace ℂ W] [CompleteSpace W]

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V]
variable {W : Type*} [NormedAddCommGroup W] [InnerProductSpace ℂ W] [CompleteSpace W]

set_option maxHeartbeats 1000000 in
theorem solution (α : V ≃ₗᵢ[ℂ] W) (l : ℂ) (hl : ‖l‖ = 1) (m : V →L[ℂ] V) :
    conjCLM (α.trans (unitScaleEquiv l hl)) m = conjCLM α m := by

  ext x;
  -- By definition of `unitScaleEquiv`, we know that `unitScaleEquiv l hl x = l • x`.
  have h_unitScaleEquiv : (α.trans (unitScaleEquiv l hl)).symm x = (1 / l) • (α.symm x) := by
    simp only [unitScaleEquiv, LinearIsometryEquiv.symm_trans, LinearIsometryEquiv.trans_apply,
        one_div];
    exact α.symm.map_smul _ _;
  convert congr_arg ( fun y => α ( l • m y ) ) h_unitScaleEquiv using 1;
  · simp [ conjCLM, unitScaleEquiv ];
  · simp [ smul_smul, show l ≠ 0 by rintro rfl; simp at hl ]
