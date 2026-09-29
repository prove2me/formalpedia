-- Prove2me | solution 1 for BookProof.NavierStokesFlow.FockOfFock.lpBasis_total
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T09:20:22.157549+00:00
-- url     : https://prove2.me/submissions/4e29e109-fa3f-47d7-9024-3ac86943afcf

-- Adapted from Leonardo Pedro, timepiece commit61595bc, Apache-2.0.
-- https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterNavierStokesFockSpace.lean
import Definitions.Def_ChapterNavierStokesFockSpace
import Mathlib
set_option autoImplicit false
open BookProof.NavierStokesFlow BookProof.NavierStokesFlow.FockOfFock
open BookProof.NavierStokesFlow.FullEsa BookProof.NavierStokesFlow.LpNat

variable {ι : Type*}

theorem solution [DecidableEq ι] (w : lp (fun _ : ι => ℂ) 2)
    (hw : ∀ i, (inner ℂ ((lpBasis i : lpFiniteModes ι) : lp (fun _ : ι => ℂ) 2) w : ℂ) = 0) :
    w = 0 := by
  ext i
  have h := hw i
  rw [show ((lpBasis i : lpFiniteModes ι) : lp (fun _ : ι => ℂ) 2) = lp.single 2 i 1 from rfl,
    lp.inner_single_left] at h
  simpa using h


#print axioms solution
