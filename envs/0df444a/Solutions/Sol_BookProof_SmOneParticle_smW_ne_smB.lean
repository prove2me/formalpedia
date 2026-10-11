-- Prove2me | solution 1 for BookProof.SmOneParticle.smW_ne_smB
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-11T10:21:18.220742+00:00
-- url     : https://prove2.me/submissions/bea2cb4a-41f7-4494-9b07-7e5f7a28a0f2

-- Generated from ChapterSmOneParticle.lean — solution of BookProof.SmOneParticle.smW_ne_smB
import Mathlib
import Definitions.Def_ChapterSmOneParticle
open BookProof.SmOneParticle

set_option maxHeartbeats 1000000 in
theorem solution (k i : Fin 3) (j : Fin 3) : smW k i ≠ smB j := by

  intro h
  have := smIdx.injective h
  simp at this
