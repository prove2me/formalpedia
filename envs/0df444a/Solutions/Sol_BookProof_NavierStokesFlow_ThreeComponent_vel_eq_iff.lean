-- Prove2me | solution 1 for BookProof.NavierStokesFlow.ThreeComponent.vel_eq_iff
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-09-13T07:57:03.455541+00:00
-- url     : https://prove2.me/submissions/0c4f3b30-e267-4d38-8545-f98dcd1b1a24

-- Generated from ChapterNavierStokesThreeComponent.lean — solution of BookProof.NavierStokesFlow.ThreeComponent.vel_eq_iff
import Mathlib
import Definitions.Def_ChapterNavierStokesThreeComponent
import Definitions.Def_ChapterNavierStokesDeficiency
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterNavierStokesIkebeKato
import Definitions.Def_ChapterNavierStokesShiftHamiltonian
import Definitions.Def_ChapterNavierStokesSignedShift
open BookProof.NavierStokesFlow
open BookProof.NavierStokesFlow.ThreeComponent
















open scoped ENNReal



open BookProof.NavierStokesFlow.LpNat BookProof.FarisLavine BookProof.NavierStokesFlow.IkebeKato BookProof.NavierStokesFlow.ShiftHamiltonian BookProof.NavierStokesFlow.SignedShift





































variable (A : Matrix (Fin 3) (Fin 3) ℝ) (c : Fin 3 → ℝ)

set_option maxHeartbeats 1000000 in
theorem solution (x y : Vel) : x = y ↔ x 0 = y 0 ∧ x 1 = y 1 ∧ x 2 = y 2 := by

  constructor
  · rintro rfl
    exact ⟨rfl, rfl, rfl⟩
  · rintro ⟨h0, h1, h2⟩
    funext j
    fin_cases j <;> assumption
