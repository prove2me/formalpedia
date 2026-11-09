-- Prove2me | solution 1 for BookProof.FriedrichsSquare.isFriedrichsSqExtension_factorRel
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-11-08T07:28:36.951882+00:00
-- url     : https://prove2.me/submissions/d44879d1-c3fc-48d2-8c88-f7f095340046

-- Generated from ChapterFriedrichsSquareFactorization.lean — solution of BookProof.FriedrichsSquare.isFriedrichsSqExtension_factorRel
import Mathlib
import Definitions.Def_ChapterFriedrichsSquareFactorization
import Theorems.Thm_BookProof_FriedrichsSquare_fst_mem_clDom_of_mem_factorRel
import Theorems.Thm_BookProof_FriedrichsSquare_adjPairs_factorRel
import Theorems.Thm_BookProof_ClosureUniqueness_mem_factorGraph_sqOp
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterEsaClosureCore
import Definitions.Def_ChapterClosureUniqueness
import Definitions.Def_ChapterFarisLavineCore
open BookProof.FriedrichsSquare




open BookProof.FarisLavine BookProof.EsaClosure BookProof.ClosureUniqueness

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]
variable {D : Submodule ℂ F}
variable [CompleteSpace F]

set_option maxHeartbeats 1000000 in
theorem solution [CompleteSpace F] (A : D →ₗ[ℂ] F)
    (hsym : SymmetricOn D A) (hstab : ∀ v : D, (A v : F) ∈ D) :
    IsFriedrichsSqExtension A hstab (factorRel A) where
  extends_sq v := mem_factorGraph_sqOp A hsym hstab v
  form_domain _ hp := fst_mem_clDom_of_mem_factorRel hp
  selfAdjoint := adjPairs_factorRel A
