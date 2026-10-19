-- Prove2me | solution 1 for BookProof.ChapterSchurRepresentation.repSystem_isNormal
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-17T01:28:14.253375+00:00
-- url     : https://prove2.me/submissions/64d54f1d-cb54-49ae-a05a-37f88c207b35

-- Generated from ChapterSchurRepresentation.lean — solution of BookProof.ChapterSchurRepresentation.repSystem_isNormal
import Mathlib
import Definitions.Def_ChapterSchurRepresentation
import Theorems.Thm_BookProof_ChapterSchurRepresentation_adjoint_uCLM
import Definitions.Def_ChapterSchurIrreducible
import Definitions.Def_ChapterA
open BookProof.ChapterSchurRepresentation



open scoped ComplexConjugate InnerProductSpace


open BookProof.ChapterA BookProof.ChapterA.System BookProof.ChapterSchurIrreducible
open BookProof.ChapterA
open BookProof.ChapterA.System

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V]

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V]

set_option maxHeartbeats 1000000 in
theorem solution {G : Type*} [Group G] (U : G →* (V ≃ₗᵢ[ℂ] V)) :
    (repSystem U).IsNormal := by

  rintro m ⟨g, rfl⟩
  refine ⟨g⁻¹, ?_⟩
  rw [adjoint_uCLM]
  congr 1
  rw [map_inv]
  rfl
