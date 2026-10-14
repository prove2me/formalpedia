-- Prove2me | solution 1 for BookProof.ClosureUniqueness.closure_unique
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-11T16:55:40.324996+00:00
-- url     : https://prove2.me/submissions/fb0bfc24-c966-422c-b890-87067517cc7b

-- Generated from ChapterClosureUniqueness.lean — solution of BookProof.ClosureUniqueness.closure_unique
import Mathlib
import Definitions.Def_ChapterClosureUniqueness
import Theorems.Thm_BookProof_ClosureUniqueness_opGraph_eq_clGraph_of_isClosureOf
import Theorems.Thm_BookProof_ClosureUniqueness_eq_of_opGraph_eq
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterEsaClosureCore
open BookProof.ClosureUniqueness




open BookProof.FarisLavine BookProof.EsaClosure

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]
variable {D D₁ D₂ Dom Dom₁ Dom₂ : Submodule ℂ F}

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]
variable {D D₁ D₂ Dom Dom₁ Dom₂ : Submodule ℂ F}

set_option maxHeartbeats 1000000 in
theorem solution {T : D →ₗ[ℂ] F} {A : Dom₁ →ₗ[ℂ] F} {B : Dom₂ →ₗ[ℂ] F}
    (hA : IsClosureOf T A) (hB : IsClosureOf T B) :
    Dom₁ = Dom₂ ∧ ∀ (x : F) (h₁ : x ∈ Dom₁) (h₂ : x ∈ Dom₂), A ⟨x, h₁⟩ = B ⟨x, h₂⟩ :=
  eq_of_opGraph_eq
      ((opGraph_eq_clGraph_of_isClosureOf hA).trans (opGraph_eq_clGraph_of_isClosureOf hB).symm)
