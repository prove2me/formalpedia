-- Prove2me | solution 1 for BookProof.NavierStokesFlow.ThreeComponent.shearHop_shift
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-09-13T07:56:12.954086+00:00
-- url     : https://prove2.me/submissions/29e7f284-34d0-43eb-be91-371e7f21f250

-- Generated from ChapterNavierStokesThreeComponent.lean — solution of BookProof.NavierStokesFlow.ThreeComponent.shearHop_shift
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
theorem solution (i : Fin 3) : (shearHop A c i).shift = shShear i := rfl
