-- Prove2me | solution 1 for BookProof.FriedrichsSquare.frExt_quadForm_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-17T01:11:11.230871+00:00
-- url     : https://prove2.me/submissions/b5e76af5-9659-4719-931c-ed911225db40

-- Generated from ChapterFriedrichsSquareFactorization.lean — solution of BookProof.FriedrichsSquare.frExt_quadForm_nonneg
import Mathlib
import Definitions.Def_ChapterFriedrichsSquareFactorization
import Theorems.Thm_BookProof_ClosureUniqueness_factorGraph_quadForm_nonneg
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterEsaClosureCore
import Definitions.Def_ChapterClosureUniqueness
import Definitions.Def_ChapterFarisLavineCore
open BookProof.FriedrichsSquare




open BookProof.FarisLavine BookProof.EsaClosure BookProof.ClosureUniqueness

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]
variable {D : Submodule ℂ F}

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]
variable {D : Submodule ℂ F}
variable [CompleteSpace F]

set_option maxHeartbeats 1000000 in
theorem solution (A : D →ₗ[ℂ] F) (hdense : Dense (D : Set F))
    (hsym : SymmetricOn D A) (x : frDom A) :
    0 ≤ (inner ℂ (x : F) (frExt A hdense hsym x) : ℂ).re ∧
      (inner ℂ (x : F) (frExt A hdense hsym x) : ℂ).im = 0 := factorGraph_quadForm_nonneg (p := ((x : F), frFun A x)) (frFun_spec A x)
