-- Prove2me | solution 1 for BookProof.ReducedEsa.commutes_symProj
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-19T05:41:33.085379+00:00
-- url     : https://prove2.me/submissions/8f098c92-d5dc-408c-a4fd-022dbc047a4d

-- Generated from ChapterReducingSubspaceEsa.lean — solution of BookProof.ReducedEsa.commutes_symProj
import Mathlib
import Definitions.Def_ChapterReducingSubspaceEsa
import Theorems.Thm_BookProof_ReducedEsa_symProj_mem
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterGraphCoreTransfer
import Definitions.Def_ChapterA
open BookProof.ReducedEsa




open BookProof.FarisLavine BookProof.GraphCore
open BookProof.ChapterA
open BookProof.ChapterA.System

noncomputable section

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]
variable {P : F →ₗ[ℂ] F}
variable {D : Submodule ℂ F}
variable (T : D →ₗ[ℂ] F)
variable {T}
variable (U : F →ₗ[ℂ] F)
variable {U}

set_option maxHeartbeats 1000000 in

theorem solution {hUD : ∀ x ∈ D, U x ∈ D}
    (hTU : ∀ x : D, T ⟨U (x : F), hUD _ x.2⟩ = U (T x)) :
    Commutes T (symProj_mem (D := D) hUD) where
  comm x := by
    have hsplit : (⟨symProj U (x : F), symProj_mem (D := D) hUD _ x.2⟩ : D)
        = (2⁻¹ : ℂ) • ((x : D) + ⟨U (x : F), hUD _ x.2⟩) := by
      apply Subtype.ext
      simp [symProj]
    rw [hsplit, map_smul, map_add, hTU x]
    simp [symProj]
