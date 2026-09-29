-- Prove2me | solution 1 for BookProof.NavierStokesFlow.FockOfFock.lpBasis_coe
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T09:20:20.468281+00:00
-- url     : https://prove2.me/submissions/878ef19c-b2bb-4fad-9321-7062eb187647

-- Adapted from Leonardo Pedro, timepiece commit61595bc, Apache-2.0.
-- https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterNavierStokesFockSpace.lean
import Definitions.Def_ChapterNavierStokesFockSpace
import Mathlib
set_option autoImplicit false
open BookProof.NavierStokesFlow BookProof.NavierStokesFlow.FockOfFock
open BookProof.NavierStokesFlow.FullEsa BookProof.NavierStokesFlow.LpNat

variable {ι : Type*}

theorem solution [DecidableEq ι] (i j : ι) :
    (((lpBasis i : lpFiniteModes ι) : lp (fun _ : ι => ℂ) 2) : ι → ℂ) j
      = if j = i then 1 else 0 := by
  by_cases h : j = i
  · subst h; simp [lpBasis, lp.single_apply]
  · simp [lpBasis, lp.single_apply, h]


#print axioms solution
