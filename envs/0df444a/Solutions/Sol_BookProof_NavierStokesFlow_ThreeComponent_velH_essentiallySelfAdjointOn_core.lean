-- Prove2me | solution 1 for BookProof.NavierStokesFlow.ThreeComponent.velH_essentiallySelfAdjointOn_core
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-09-13T07:56:14.555796+00:00
-- url     : https://prove2.me/submissions/02bf153a-e3f5-4dd8-a8e3-ff810d5437cf

-- Generated from ChapterNavierStokesThreeComponent.lean — solution of BookProof.NavierStokesFlow.ThreeComponent.velH_essentiallySelfAdjointOn_core
import Mathlib
import Definitions.Def_ChapterNavierStokesThreeComponent
import Theorems.Thm_BookProof_NavierStokesFlow_SignedShift_listH_essentiallySelfAdjointOn_core
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
    EssentiallySelfAdjointOn (lpFiniteModes Vel)
      ((velH A c).comp (Submodule.inclusion (finiteModes_le_maxDom (velSym (velMu A c))))) := SignedShift.listH_essentiallySelfAdjointOn_core _ (velSym_ge_one (velMu_nonneg A c))
