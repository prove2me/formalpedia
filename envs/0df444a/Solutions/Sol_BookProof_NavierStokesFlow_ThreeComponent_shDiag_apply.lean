-- Prove2me | solution 1 for BookProof.NavierStokesFlow.ThreeComponent.shDiag_apply
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-09-13T07:55:56.326517+00:00
-- url     : https://prove2.me/submissions/c0398b6a-1a2d-4655-a309-711a849f861a

-- Generated from ChapterNavierStokesThreeComponent.lean — solution of BookProof.NavierStokesFlow.ThreeComponent.shDiag_apply
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
theorem solution (i : Fin 3) (β : Vel) (j : Fin 3) :
    shDiag i β j = β j + (if j = i then 2 else 0) := by

  by_cases h : j = i
  · subst h; simp [shDiag, raise]
  · simp [shDiag, raise_of_ne h, h]
