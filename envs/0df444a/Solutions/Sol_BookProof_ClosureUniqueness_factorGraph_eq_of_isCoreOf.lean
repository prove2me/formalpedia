-- Prove2me | solution 1 for BookProof.ClosureUniqueness.factorGraph_eq_of_isCoreOf
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-09T14:19:03.43807+00:00
-- url     : https://prove2.me/submissions/179c788b-0247-43ba-8b04-89404b560089
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

-- Generated from ChapterClosureUniqueness.lean — solution of BookProof.ClosureUniqueness.factorGraph_eq_of_isCoreOf
import Mathlib
import Definitions.Def_ChapterClosureUniqueness
import Theorems.Thm_BookProof_ClosureUniqueness_clGraph_eq_of_isCoreOf
import Theorems.Thm_BookProof_ClosureUniqueness_factorGraph_eq_of_clGraph_eq
open BookProof.ClosureUniqueness




open BookProof.FarisLavine BookProof.EsaClosure

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]
variable {D D₁ D₂ Dom Dom₁ Dom₂ : Submodule ℂ F}

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]
variable {D D₁ D₂ Dom Dom₁ Dom₂ : Submodule ℂ F}

set_option maxHeartbeats 1000000 in
theorem solution {T₁ : D₁ →ₗ[ℂ] F} {T₂ : D₂ →ₗ[ℂ] F} (h : IsCoreOf T₁ T₂) :
    factorGraph T₁ = factorGraph T₂ := factorGraph_eq_of_clGraph_eq (clGraph_eq_of_isCoreOf h)
