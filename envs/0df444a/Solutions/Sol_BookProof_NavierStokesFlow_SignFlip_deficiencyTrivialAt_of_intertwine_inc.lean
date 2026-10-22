-- Prove2me | solution 1 for BookProof.NavierStokesFlow.SignFlip.deficiencyTrivialAt_of_intertwine_inc
-- status  : ACCEPTED   (prove)
-- author  : @Ethan Cheung
-- created : 2026-10-22T03:58:05.464836+00:00
-- url     : https://prove2.me/submissions/e4b05e74-286c-4a62-9ffd-5f2f318d772f

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
    (hcomm : ∀ v : D, U (T v) = T' ⟨U (v : F), hU v⟩) (z : ℂ)
    (hT : DeficiencyTrivialAt D T z) : DeficiencyTrivialAt D T' z := by
  apply BookProof.NavierStokesFlow.SignFlip.deficiencyTrivialAt_of_intertwine <;> assumption

