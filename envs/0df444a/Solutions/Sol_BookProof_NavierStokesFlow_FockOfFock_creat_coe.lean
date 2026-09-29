-- Prove2me | solution 1 for BookProof.NavierStokesFlow.FockOfFock.creat_coe
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T09:44:07.634017+00:00
-- url     : https://prove2.me/submissions/684b2d30-e661-44d3-a77b-8d351f619dec

-- Adapted from Leonardo Pedro, timepiece commit61595bc, Apache-2.0.
-- https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterNavierStokesFockSpace.lean
import Definitions.Def_ChapterNavierStokesFockSpace
import Mathlib
set_option autoImplicit false
open BookProof.NavierStokesFlow BookProof.NavierStokesFlow.FockOfFock
open BookProof.NavierStokesFlow.FullEsa BookProof.NavierStokesFlow.LpNat

variable {M : Type*}

theorem solution [DecidableEq M] (m : M) (f : FockDom M) (n : Conf M) :
    (((creat m f : FockDom M) : FockL2 M) : Conf M → ℂ) n
      = (Real.sqrt (n m) : ℂ) * ((f : FockL2 M) : Conf M → ℂ) (n - Finsupp.single m 1) := rfl


#print axioms solution
