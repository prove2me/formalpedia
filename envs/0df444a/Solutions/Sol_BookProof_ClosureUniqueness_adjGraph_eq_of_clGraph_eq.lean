-- Prove2me | solution 1 for BookProof.ClosureUniqueness.adjGraph_eq_of_clGraph_eq
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-11T16:55:45.716733+00:00
-- url     : https://prove2.me/submissions/e0685797-a7f1-4803-b241-ba7ceceeb2a6

-- Generated from ChapterClosureUniqueness.lean — solution of BookProof.ClosureUniqueness.adjGraph_eq_of_clGraph_eq
import Mathlib
import Definitions.Def_ChapterClosureUniqueness
import Theorems.Thm_BookProof_ClosureUniqueness_adjGraph_eq_adjPairs_clGraph
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterEsaClosureCore
open BookProof.ClosureUniqueness




open BookProof.FarisLavine BookProof.EsaClosure

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]
variable {D D₁ D₂ Dom Dom₁ Dom₂ : Submodule ℂ F}

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]
variable {D D₁ D₂ Dom Dom₁ Dom₂ : Submodule ℂ F}

set_option maxHeartbeats 1000000 in
theorem solution {T₁ : D₁ →ₗ[ℂ] F} {T₂ : D₂ →ₗ[ℂ] F}
    (h : clGraph T₁ = clGraph T₂) : adjGraph T₁ = adjGraph T₂ := by

  rw [adjGraph_eq_adjPairs_clGraph, adjGraph_eq_adjPairs_clGraph, h]
