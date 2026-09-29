-- Prove2me | solution 1 for BookProof.NavierStokesFlow.FockOfFock.ofCoeff_coe
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T09:17:53.675186+00:00
-- url     : https://prove2.me/submissions/98b99650-ea6f-40b0-af8f-27ce90220007

-- Adapted from Leonardo Pedro, timepiece commit61595bc, Apache-2.0.
-- https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterNavierStokesFockSpace.lean
import Definitions.Def_ChapterNavierStokesFockSpace
import Mathlib
set_option autoImplicit false
open BookProof.NavierStokesFlow BookProof.NavierStokesFlow.FockOfFock
open BookProof.NavierStokesFlow.FullEsa BookProof.NavierStokesFlow.LpNat

variable {ι : Type*}

theorem solution (φ : ι → ℂ) (h : (Function.support φ).Finite) :
    (((ofCoeff φ h : lpFiniteModes ι) : lp (fun _ : ι => ℂ) 2) : ι → ℂ) = φ := rfl


#print axioms solution
