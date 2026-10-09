-- Prove2me | solution 1 for BookProof.FockDegreesOfFreedom.NavierStokes.jetCard_firstOrder
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-09T07:13:07.660299+00:00
-- url     : https://prove2.me/submissions/f34ec8f6-f637-4ba7-a293-cec2b5d82622

-- Generated from ChapterFockDegreesOfFreedom.lean — solution of BookProof.FockDegreesOfFreedom.NavierStokes.jetCard_firstOrder
import Mathlib
import Definitions.Def_ChapterFockDegreesOfFreedom
open BookProof.FockDegreesOfFreedom
open BookProof.FockDegreesOfFreedom.NavierStokes




open Fintype

set_option maxHeartbeats 1000000 in
theorem solution :
    Fintype.card (Fin 3 ⊕ Fin 3 ⊕ (Fin 3 × Fin 3)) = 15 := by
 simp
