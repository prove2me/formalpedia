-- Prove2me | solution 1 for BookProof.FriedrichsSquare.factorRel_quadForm_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-17T01:10:51.665119+00:00
-- url     : https://prove2.me/submissions/49587ecf-769e-4af4-a914-0cfb50ebc2e6

-- Generated from ChapterFriedrichsSquareFactorization.lean — solution of BookProof.FriedrichsSquare.factorRel_quadForm_nonneg
import Mathlib
import Definitions.Def_ChapterFriedrichsSquareFactorization
import Theorems.Thm_BookProof_ClosureUniqueness_factorGraph_quadForm_nonneg
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterEsaClosureCore
import Definitions.Def_ChapterClosureUniqueness
open BookProof.FriedrichsSquare




open BookProof.FarisLavine BookProof.EsaClosure BookProof.ClosureUniqueness

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]
variable {D : Submodule ℂ F}

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]
variable {D : Submodule ℂ F}
variable [CompleteSpace F]

set_option maxHeartbeats 1000000 in
theorem solution {A : D →ₗ[ℂ] F} {p : F × F} (hp : p ∈ factorRel A) :
    0 ≤ (inner ℂ p.1 p.2 : ℂ).re ∧ (inner ℂ p.1 p.2 : ℂ).im = 0 := factorGraph_quadForm_nonneg hp
