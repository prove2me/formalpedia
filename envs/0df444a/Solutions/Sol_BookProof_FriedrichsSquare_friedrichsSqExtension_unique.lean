-- Prove2me | solution 1 for BookProof.FriedrichsSquare.friedrichsSqExtension_unique
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-17T01:11:06.439997+00:00
-- url     : https://prove2.me/submissions/47f62974-7fd5-4c99-8900-6d42c7017df7

-- Generated from ChapterFriedrichsSquareFactorization.lean — solution of BookProof.FriedrichsSquare.friedrichsSqExtension_unique
import Mathlib
import Definitions.Def_ChapterFriedrichsSquareFactorization
import Theorems.Thm_BookProof_FriedrichsSquare_isFriedrichsSqExtension_iff_eq_factorRel
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
theorem solution [CompleteSpace F] {A : D →ₗ[ℂ] F}
    (hsym : SymmetricOn D A) {hstab : ∀ v : D, (A v : F) ∈ D} {R₁ R₂ : Submodule ℂ (F × F)}
    (h₁ : IsFriedrichsSqExtension A hstab R₁) (h₂ : IsFriedrichsSqExtension A hstab R₂) :
    R₁ = R₂ :=
  ((isFriedrichsSqExtension_iff_eq_factorRel hsym).1 h₁).trans
      ((isFriedrichsSqExtension_iff_eq_factorRel hsym).1 h₂).symm
