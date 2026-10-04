-- Prove2me | solution 1 for BookProof.NavierStokesFlow.FockManyMode.modeShift_shift_ne_prime
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-03T02:14:03.738892+00:00
-- url     : https://prove2.me/submissions/4447bd9b-8d37-4d68-94df-91d985ed6e7c

import Mathlib
import Definitions.Def_ChapterNavierStokesFockManyMode
import Definitions.Def_ChapterNavierStokesAffineFiberEsa

set_option autoImplicit false

open BookProof.NavierStokesFlow BookProof.NavierStokesFlow.FockManyMode in
theorem solution {d : ℕ} (i i₀ : Fin d) :
    modeShift i (modeShift i₀ (0 : Occ d)) ≠ modeShift i₀ 0 := by
  intro h
  have h1 := congrFun h i
  rw [modeShift_self] at h1
  omega
