-- Prove2me | solution 1 for BookProof.ClosureUniqueness.eq_clExt_of_isClosureOf
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-11T16:55:41.311325+00:00
-- url     : https://prove2.me/submissions/0d134d16-266a-4521-a1c9-090f52298f98

-- Generated from ChapterClosureUniqueness.lean — solution of BookProof.ClosureUniqueness.eq_clExt_of_isClosureOf
import Mathlib
import Definitions.Def_ChapterClosureUniqueness
import Theorems.Thm_BookProof_ClosureUniqueness_clExt_isClosureOf
import Theorems.Thm_BookProof_ClosureUniqueness_closure_unique
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterEsaClosureCore
import Definitions.Def_ChapterFarisLavineCore
open BookProof.ClosureUniqueness




open BookProof.FarisLavine BookProof.EsaClosure

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]
variable {D D₁ D₂ Dom Dom₁ Dom₂ : Submodule ℂ F}

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]
variable {D D₁ D₂ Dom Dom₁ Dom₂ : Submodule ℂ F}

set_option maxHeartbeats 1000000 in
theorem solution {T : D →ₗ[ℂ] F} {A : Dom →ₗ[ℂ] F} (hA : IsClosureOf T A)
    (hdense : Dense (D : Set F)) (hsym : SymmetricOn D T) :
    Dom = clDom T ∧ ∀ (x : F) (h₁ : x ∈ Dom) (h₂ : x ∈ clDom T),
      A ⟨x, h₁⟩ = clExt T hdense hsym ⟨x, h₂⟩ := closure_unique hA (clExt_isClosureOf T hdense hsym)
