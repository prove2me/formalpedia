-- Prove2me | solution 1 for BookProof.NavierStokesFlow.ThreeComponent.velH_domain_dense
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-09-13T07:56:13.985212+00:00
-- url     : https://prove2.me/submissions/cf37ffb7-28ad-43e6-9925-6ff9b3992e25

-- Generated from ChapterNavierStokesThreeComponent.lean — solution of BookProof.NavierStokesFlow.ThreeComponent.velH_domain_dense
import Mathlib
import Definitions.Def_ChapterNavierStokesThreeComponent
import Definitions.Def_ChapterNavierStokesEsa
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
theorem solution :
    Dense ((lpFiniteModes Vel : Submodule ℂ (L2I Vel)) : Set (L2I Vel)) := lpFiniteModes_dense
