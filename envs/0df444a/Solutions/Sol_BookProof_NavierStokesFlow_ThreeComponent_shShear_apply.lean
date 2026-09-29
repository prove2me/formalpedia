-- Prove2me | solution 1 for BookProof.NavierStokesFlow.ThreeComponent.shShear_apply
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-09-13T11:30:52.793565+00:00
-- url     : https://prove2.me/submissions/e239c16c-2aaf-47e2-9da8-6cd6049559d2

-- Generated from ChapterNavierStokesThreeComponent.lean — solution of BookProof.NavierStokesFlow.ThreeComponent.shShear_apply
import Mathlib
import Definitions.Def_ChapterNavierStokesThreeComponent
import Theorems.Thm_BookProof_NavierStokesFlow_ThreeComponent_raise_apply
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
    shShear i β j = β j + (if j = i then 1 else 0) := raise_apply i β j
