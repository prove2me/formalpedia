-- Prove2me | solution 1 for BookProof.FriedrichsSquare.frDom_le_clDom
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-17T01:11:08.737629+00:00
-- url     : https://prove2.me/submissions/cf2fadc1-aa43-4754-9a74-1c07455af046

-- Generated from ChapterFriedrichsSquareFactorization.lean — solution of BookProof.FriedrichsSquare.frDom_le_clDom
import Mathlib
import Definitions.Def_ChapterFriedrichsSquareFactorization
import Theorems.Thm_BookProof_FriedrichsSquare_fst_mem_clDom_of_mem_factorRel
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterClosureUniqueness
import Definitions.Def_ChapterEsaClosureCore
open BookProof.FriedrichsSquare




open BookProof.FarisLavine BookProof.EsaClosure BookProof.ClosureUniqueness
open BookProof.EsaClosure

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]
variable {D : Submodule ℂ F}

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]
variable {D : Submodule ℂ F}
variable [CompleteSpace F]

set_option maxHeartbeats 1000000 in
theorem solution (A : D →ₗ[ℂ] F) : frDom A ≤ clDom A := by

  intro x hx
  obtain ⟨z, hz⟩ := mem_frDom_iff.1 hx
  exact fst_mem_clDom_of_mem_factorRel (p := (x, z)) hz
