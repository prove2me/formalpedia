-- Prove2me | solution 1 for BookProof.FriedrichsSquare.mem_flipGraph_iff
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-17T01:09:48.516162+00:00
-- url     : https://prove2.me/submissions/6dd9518c-0ff6-4ccd-b8e5-3ede564032b7

-- Generated from ChapterFriedrichsSquareFactorization.lean — solution of BookProof.FriedrichsSquare.mem_flipGraph_iff
import Mathlib
import Definitions.Def_ChapterFriedrichsSquareFactorization
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
theorem solution {A : D →ₗ[ℂ] F} {p : WithLp 2 (F × F)} :
    p ∈ flipGraph A ↔ ((WithLp.ofLp p).2, -(WithLp.ofLp p).1) ∈ clGraph A := Iff.rfl
