-- Prove2me | solution 1 for BookProof.ReducedEsa.essentiallySelfAdjointOn_symSector
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-19T14:41:14.806521+00:00
-- url     : https://prove2.me/submissions/ceb38806-3813-43b1-805e-f2801fb3c07f

-- Generated from ChapterReducingSubspaceEsa.lean — solution of BookProof.ReducedEsa.essentiallySelfAdjointOn_symSector
import Mathlib
import Definitions.Def_ChapterReducingSubspaceEsa
import Theorems.Thm_BookProof_ReducedEsa_essentiallySelfAdjointOn_red
import Theorems.Thm_BookProof_ReducedEsa_isReducingProjection_symProj
import Theorems.Thm_BookProof_ReducedEsa_symProj_mem
import Theorems.Thm_BookProof_ReducedEsa_commutes_symProj
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterGraphCoreTransfer
import Definitions.Def_ChapterFarisLavineCore
open BookProof.ReducedEsa




open BookProof.FarisLavine BookProof.GraphCore

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
theorem solution (hU2 : ∀ x, U (U x) = x)
    (hUi : ∀ x y : F, (inner ℂ (U x) (U y) : ℂ) = inner ℂ x y)
    {hUD : ∀ x ∈ D, U x ∈ D} (hTU : ∀ x : D, T ⟨U (x : F), hUD _ x.2⟩ = U (T x))
    (hesa : EssentiallySelfAdjointOn D T) :
    EssentiallySelfAdjointOn (redDom (symProj U) D)
      (redOp T (isReducingProjection_symProj hU2 hUi) (commutes_symProj hTU)) := essentiallySelfAdjointOn_red _ _ hesa
