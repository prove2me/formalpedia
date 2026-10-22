-- Prove2me | solution 1 for BookProof.NavierStokesFlow.SignFlip.essentiallySelfAdjointOn_of_intertwine_inc
-- status  : ACCEPTED   (prove)
-- author  : @Ethan Cheung
-- created : 2026-10-22T03:58:03.743992+00:00
-- url     : https://prove2.me/submissions/cd185c4b-9710-4d39-a012-82ff83e09dfb

import Mathlib
import Definitions.Def_ChapterNavierStokesSignFlip
import Definitions.Def_ChapterFarisLavineCore
import Definitions.Def_ChapterNavierStokesAffineFiberEsa
open BookProof.NavierStokesFlow
open BookProof.NavierStokesFlow.SignFlip


open scoped ENNReal



open LpNat BookProof.FarisLavine IkebeKato HermiteFarisLavine ShiftHamiltonian AffineFiber

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] {D : Submodule ℂ F}

theorem solution (U : F ≃ₗᵢ[ℂ] F) (T T' : D →ₗ[ℂ] F)
    (hU : ∀ v : D, U (v : F) ∈ D)
    (hcomm : ∀ v : D, U (T v) = T' ⟨U (v : F), hU v⟩)
    (hT : EssentiallySelfAdjointOn D T) : EssentiallySelfAdjointOn D T' := by
  apply BookProof.NavierStokesFlow.SignFlip.essentiallySelfAdjointOn_of_intertwine <;> assumption

