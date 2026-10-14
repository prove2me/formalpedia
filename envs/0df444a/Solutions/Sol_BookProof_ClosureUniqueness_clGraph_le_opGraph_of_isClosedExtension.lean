-- Prove2me | solution 1 for BookProof.ClosureUniqueness.clGraph_le_opGraph_of_isClosedExtension
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-11T16:55:37.975479+00:00
-- url     : https://prove2.me/submissions/49ecfe26-4a1d-4d50-89d0-ab47047d1cf7

-- Generated from ChapterClosureUniqueness.lean — solution of BookProof.ClosureUniqueness.clGraph_le_opGraph_of_isClosedExtension
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
theorem solution {T : D →ₗ[ℂ] F} {A : Dom →ₗ[ℂ] F}
    (h : IsClosedExtension T A) : clGraph T ≤ opGraph A := by

  intro p hp
  exact clGraph_subset_of_isClosed h.2 (fun v => opGraph_le_of_extends h.1 (mem_opGraph T v)) hp
