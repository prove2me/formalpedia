-- Prove2me | solution 1 for BookProof.ClosureUniqueness.factorGraph_eq_of_isCoreOf_pair
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-11T16:55:47.992993+00:00
-- url     : https://prove2.me/submissions/7fb13946-d19e-447f-b3c0-cd71860c500f

-- Generated from ChapterClosureUniqueness.lean — solution of BookProof.ClosureUniqueness.factorGraph_eq_of_isCoreOf_pair
import Mathlib
import Definitions.Def_ChapterClosureUniqueness
import Theorems.Thm_BookProof_ClosureUniqueness_clGraph_eq_of_isCoreOf_pair
import Theorems.Thm_BookProof_ClosureUniqueness_factorGraph_eq_of_clGraph_eq
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterEsaClosureCore
open BookProof.ClosureUniqueness




open BookProof.FarisLavine BookProof.EsaClosure

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]
variable {D D₁ D₂ Dom Dom₁ Dom₂ : Submodule ℂ F}

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]
variable {D D₁ D₂ Dom Dom₁ Dom₂ : Submodule ℂ F}

set_option maxHeartbeats 1000000 in
theorem solution {T : D →ₗ[ℂ] F} {T₁ : D₁ →ₗ[ℂ] F} {T₂ : D₂ →ₗ[ℂ] F}
    (h₁ : IsCoreOf T₁ T) (h₂ : IsCoreOf T₂ T) : factorGraph T₁ = factorGraph T₂ := factorGraph_eq_of_clGraph_eq (clGraph_eq_of_isCoreOf_pair h₁ h₂)
