-- Prove2me | solution 1 for BookProof.ClosureUniqueness.clGraph_eq_of_isCoreOf
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-11T16:55:42.431811+00:00
-- url     : https://prove2.me/submissions/399d9153-7a75-4db7-a7ba-13e4a2321604

-- Generated from ChapterClosureUniqueness.lean — solution of BookProof.ClosureUniqueness.clGraph_eq_of_isCoreOf
import Mathlib
import Definitions.Def_ChapterClosureUniqueness
import Theorems.Thm_BookProof_ClosureUniqueness_opGraph_le_of_extends
import Definitions.Def_ChapterEsaClosureCore
import Definitions.Def_ChapterFarisLavine
open BookProof.ClosureUniqueness




open BookProof.FarisLavine BookProof.EsaClosure

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]
variable {D D₁ D₂ Dom Dom₁ Dom₂ : Submodule ℂ F}

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]
variable {D D₁ D₂ Dom Dom₁ Dom₂ : Submodule ℂ F}

set_option maxHeartbeats 1000000 in
theorem solution {T₁ : D₁ →ₗ[ℂ] F} {T₂ : D₂ →ₗ[ℂ] F} (h : IsCoreOf T₁ T₂) :
    clGraph T₁ = clGraph T₂ := by

  refine le_antisymm ?_ ?_
  · exact Submodule.topologicalClosure_mono (opGraph_le_of_extends h.1)
  · intro p hp
    refine clGraph_subset_of_isClosed (clGraph_isClosed T₁) (fun v => ?_) hp
    exact h.2 (mem_opGraph T₂ v)
