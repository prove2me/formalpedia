-- Prove2me | solution 1 for BookProof.FriedrichsSquare.fst_mem_clDom_of_mem_factorRel
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-17T01:09:18.809409+00:00
-- url     : https://prove2.me/submissions/eab95e9d-5bce-4f8c-94ab-d5237f761acb

-- Generated from ChapterFriedrichsSquareFactorization.lean — solution of BookProof.FriedrichsSquare.fst_mem_clDom_of_mem_factorRel
import Mathlib
import Definitions.Def_ChapterFriedrichsSquareFactorization
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterClosureUniqueness
import Definitions.Def_ChapterEsaClosureCore
open BookProof.FriedrichsSquare




open BookProof.FarisLavine BookProof.EsaClosure BookProof.ClosureUniqueness
open BookProof.ClosureUniqueness
open BookProof.EsaClosure

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]
variable {D : Submodule ℂ F}

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]
variable {D : Submodule ℂ F}

set_option maxHeartbeats 1000000 in
theorem solution {A : D →ₗ[ℂ] F} {p : F × F} (hp : p ∈ factorRel A) :
    p.1 ∈ clDom A := by

  obtain ⟨y, hy, -⟩ := hp
  exact mem_clDom_iff.2 ⟨y, hy⟩
