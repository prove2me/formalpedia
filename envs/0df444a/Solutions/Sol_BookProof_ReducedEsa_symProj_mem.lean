-- Prove2me | solution 1 for BookProof.ReducedEsa.symProj_mem
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-07T10:51:32.614973+00:00
-- url     : https://prove2.me/submissions/cd976e06-0eb0-4540-a773-3e1347c68e71

import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterGraphCoreTransfer
import Mathlib
import Definitions.Def_ChapterReducingSubspaceEsa

open BookProof.ReducedEsa BookProof.FarisLavine BookProof.GraphCore

theorem solution {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]
    {D : Submodule ℂ F} {U : F →ₗ[ℂ] F}
    (hUD : ∀ x ∈ D, U x ∈ D) : ∀ x ∈ D, symProj U x ∈ D := by
  intro x hx
  rw [symProj_apply]
  exact D.smul_mem (2⁻¹ : ℂ) (D.add_mem hx (hUD x hx))
