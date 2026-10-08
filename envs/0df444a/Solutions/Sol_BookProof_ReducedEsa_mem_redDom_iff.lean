-- Prove2me | solution 1 for BookProof.ReducedEsa.mem_redDom_iff
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-07T10:51:30.44602+00:00
-- url     : https://prove2.me/submissions/8ab6edad-6233-4851-b4d1-5e0b12dd4da2

import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterGraphCoreTransfer
import Mathlib
import Definitions.Def_ChapterReducingSubspaceEsa

open BookProof.ReducedEsa BookProof.FarisLavine BookProof.GraphCore

theorem solution {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]
    {P : F →ₗ[ℂ] F} {D : Submodule ℂ F} {x : sector P} :
    x ∈ redDom P D ↔ (x : F) ∈ D := by
  simp [redDom, Submodule.mem_comap]
