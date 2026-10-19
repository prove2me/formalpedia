-- Prove2me | solution 1 for BookProof.ChapterSchurRepresentation.adjoint_uCLM
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-17T01:27:59.664731+00:00
-- url     : https://prove2.me/submissions/5934a5e4-fd31-4718-a568-0b304555f477

-- Generated from ChapterSchurRepresentation.lean — solution of BookProof.ChapterSchurRepresentation.adjoint_uCLM
import Mathlib
import Definitions.Def_ChapterSchurRepresentation
import Definitions.Def_ChapterA
import Definitions.Def_ChapterSchurIrreducible
open BookProof.ChapterSchurRepresentation



open scoped ComplexConjugate InnerProductSpace


open BookProof.ChapterA BookProof.ChapterA.System BookProof.ChapterSchurIrreducible

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V]

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V]

set_option maxHeartbeats 1000000 in
theorem solution (f : V ≃ₗᵢ[ℂ] V) :
    ContinuousLinearMap.adjoint (uCLM f) = uCLM f.symm := by

  refine ((ContinuousLinearMap.eq_adjoint_iff _ _).mpr ?_).symm
  intro x y
  change ⟪f.symm x, y⟫_ℂ = ⟪x, f y⟫_ℂ
  rw [← f.inner_map_map (f.symm x) y, f.apply_symm_apply]
