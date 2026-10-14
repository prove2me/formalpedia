-- Prove2me | solution 1 for BookProof.ClosureUniqueness.farisLavine_clGraph_eq_of_cores
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-11T16:57:01.357506+00:00
-- url     : https://prove2.me/submissions/9a4b1119-bdee-4cf8-939f-cd5b33700970

-- Generated from ChapterClosureUniqueness.lean — solution of BookProof.ClosureUniqueness.farisLavine_clGraph_eq_of_cores
import Mathlib
import Definitions.Def_ChapterClosureUniqueness
import Theorems.Thm_BookProof_ClosureUniqueness_clGraph_eq_of_isCoreOf_pair
import Theorems.Thm_BookProof_ClosureUniqueness_clDom_eq_of_clGraph_eq
import Theorems.Thm_BookProof_ClosureUniqueness_adjGraph_eq_of_clGraph_eq
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterEsaClosureCore
open BookProof.ClosureUniqueness




open BookProof.FarisLavine BookProof.EsaClosure

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]
variable {D D₁ D₂ Dom Dom₁ Dom₂ : Submodule ℂ F}

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]
variable {D D₁ D₂ Dom Dom₁ Dom₂ : Submodule ℂ F}
variable [CompleteSpace F]

set_option maxHeartbeats 1000000 in
theorem solution {T : D →ₗ[ℂ] F} {T₁ : D₁ →ₗ[ℂ] F} {T₂ : D₂ →ₗ[ℂ] F}
    (h₁ : IsCoreOf T₁ T) (h₂ : IsCoreOf T₂ T) :
    clGraph T₁ = clGraph T₂ ∧ clDom T₁ = clDom T₂ ∧ adjGraph T₁ = adjGraph T₂ := by

  have h := clGraph_eq_of_isCoreOf_pair h₁ h₂
  exact ⟨h, clDom_eq_of_clGraph_eq h, adjGraph_eq_of_clGraph_eq h⟩
