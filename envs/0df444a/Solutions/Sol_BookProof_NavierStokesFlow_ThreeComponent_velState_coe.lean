-- Prove2me | solution 1 for BookProof.NavierStokesFlow.ThreeComponent.velState_coe
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-09-13T07:56:46.622342+00:00
-- url     : https://prove2.me/submissions/35e3edd0-ad0c-4e57-af57-bbd8a24cc64d

-- Generated from ChapterNavierStokesThreeComponent.lean — solution of BookProof.NavierStokesFlow.ThreeComponent.velState_coe
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
theorem solution (β α : Vel) :
    ((velState A c β : L2I Vel) : Vel → ℂ) α = if α = β then 1 else 0 := by

  simp [velState, lp.single_apply, Pi.single_apply, eq_comm]
