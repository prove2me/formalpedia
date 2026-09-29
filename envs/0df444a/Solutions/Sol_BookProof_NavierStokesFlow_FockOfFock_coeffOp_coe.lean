-- Prove2me | solution 1 for BookProof.NavierStokesFlow.FockOfFock.coeffOp_coe
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T09:20:23.729979+00:00
-- url     : https://prove2.me/submissions/ea540003-f6f9-4d60-8b59-486c3c4d273b

-- Adapted from Leonardo Pedro, timepiece commit61595bc, Apache-2.0.
-- https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterNavierStokesFockSpace.lean
import Definitions.Def_ChapterNavierStokesFockSpace
import Mathlib
set_option autoImplicit false
open BookProof.NavierStokesFlow BookProof.NavierStokesFlow.FockOfFock
open BookProof.NavierStokesFlow.FullEsa BookProof.NavierStokesFlow.LpNat

variable {ι : Type*}

theorem solution (T : (ι → ℂ) → ι → ℂ) (hsupp) (hadd) (hsmul) (f : lpFiniteModes ι) :
    (((coeffOp T hsupp hadd hsmul f : lpFiniteModes ι) : lp (fun _ : ι => ℂ) 2) : ι → ℂ)
      = T ((f : lp (fun _ : ι => ℂ) 2) : ι → ℂ) := rfl


#print axioms solution
