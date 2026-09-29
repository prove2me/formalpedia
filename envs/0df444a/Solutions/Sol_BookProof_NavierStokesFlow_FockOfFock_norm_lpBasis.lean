-- Prove2me | solution 1 for BookProof.NavierStokesFlow.FockOfFock.norm_lpBasis
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T09:20:21.29362+00:00
-- url     : https://prove2.me/submissions/04227b3a-bdb4-4d7a-8a8f-373cb7ff52b0

-- Adapted from Leonardo Pedro, timepiece commit61595bc, Apache-2.0.
-- https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterNavierStokesFockSpace.lean
import Definitions.Def_ChapterNavierStokesFockSpace
import Mathlib
set_option autoImplicit false
open BookProof.NavierStokesFlow BookProof.NavierStokesFlow.FockOfFock
open BookProof.NavierStokesFlow.FullEsa BookProof.NavierStokesFlow.LpNat

variable {ι : Type*}

theorem solution [DecidableEq ι] (i : ι) : ‖lpBasis (ι := ι) i‖ = 1 := by
  have : ‖((lpBasis i : lpFiniteModes ι) : lp (fun _ : ι => ℂ) 2)‖ = ‖(1 : ℂ)‖ :=
    lp.norm_single (by norm_num) i 1
  simpa using this


#print axioms solution
