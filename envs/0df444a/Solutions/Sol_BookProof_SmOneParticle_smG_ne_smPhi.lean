-- Prove2me | solution 1 for BookProof.SmOneParticle.smG_ne_smPhi
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-11T10:21:16.444286+00:00
-- url     : https://prove2.me/submissions/5868c1e9-68b5-41a8-b17b-a1f3e3f087e5

-- Generated from ChapterSmOneParticle.lean — solution of BookProof.SmOneParticle.smG_ne_smPhi
import Mathlib
import Definitions.Def_ChapterSmOneParticle
open BookProof.SmOneParticle

set_option maxHeartbeats 1000000 in
theorem solution (a : Fin 8) (i : Fin 3) (b : Fin 4) : smG a i ≠ smPhi b := by

  intro h
  have := smIdx.injective h
  simp at this
