-- Prove2me | solution 1 for BookProof.NavierStokesFlow.ThreeComponent.hopList_eq
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-09-13T07:54:47.632773+00:00
-- url     : https://prove2.me/submissions/b1a50c49-42ba-4430-8196-3407e532bc05

-- Generated from ChapterNavierStokesThreeComponent.lean — solution of BookProof.NavierStokesFlow.ThreeComponent.hopList_eq
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
theorem solution : hopList A c =
    [diagHop A c 0, shearHop A c 0,
      pairHop A c 0 0, rotHop A c 0 0, pairHop A c 0 1, rotHop A c 0 1,
      pairHop A c 0 2, rotHop A c 0 2,
     diagHop A c 1, shearHop A c 1,
      pairHop A c 1 0, rotHop A c 1 0, pairHop A c 1 1, rotHop A c 1 1,
      pairHop A c 1 2, rotHop A c 1 2,
     diagHop A c 2, shearHop A c 2,
      pairHop A c 2 0, rotHop A c 2 0, pairHop A c 2 1, rotHop A c 2 1,
      pairHop A c 2 2, rotHop A c 2 2] := rfl
