-- Prove2me | solution 1 for BookProof.SmOneParticle.smG_ne_smDG
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-11T10:21:17.311241+00:00
-- url     : https://prove2.me/submissions/9884c463-d113-4b03-b39b-0f9be6197fa8

-- Generated from ChapterSmOneParticle.lean — solution of BookProof.SmOneParticle.smG_ne_smDG
import Mathlib
import Definitions.Def_ChapterSmOneParticle
open BookProof.SmOneParticle

set_option maxHeartbeats 1000000 in
theorem solution (a : Fin 8) (i : Fin 3) (b : Fin 8) (k l : Fin 3) :
    smG a i ≠ smDG b k l := by

  intro h
  have := smIdx.injective h
  simp at this
