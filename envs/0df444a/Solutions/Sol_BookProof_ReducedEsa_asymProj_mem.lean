-- Prove2me | solution 1 for BookProof.ReducedEsa.asymProj_mem
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-07T10:51:33.667099+00:00
-- url     : https://prove2.me/submissions/ac405d0a-d949-4f8e-b070-9f2799e3f873

import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterGraphCoreTransfer
import Mathlib
import Definitions.Def_ChapterReducingSubspaceEsa

open BookProof.ReducedEsa BookProof.FarisLavine BookProof.GraphCore

theorem solution {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]
    {D : Submodule ℂ F} {U : F →ₗ[ℂ] F}
    (hUD : ∀ x ∈ D, U x ∈ D) : ∀ x ∈ D, asymProj U x ∈ D := by
  intro x hx
  rw [asymProj_apply]
  exact D.smul_mem (2⁻¹ : ℂ) (D.sub_mem hx (hUD x hx))
