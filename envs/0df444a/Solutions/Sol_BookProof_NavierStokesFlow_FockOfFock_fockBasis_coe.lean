-- Prove2me | solution 1 for BookProof.NavierStokesFlow.FockOfFock.fockBasis_coe
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T09:20:28.6496+00:00
-- url     : https://prove2.me/submissions/c4ddf433-2d3e-4dc7-855b-4c5b7aadacd5

-- Adapted from Leonardo Pedro, timepiece commit61595bc, Apache-2.0.
-- https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterNavierStokesFockSpace.lean
import Definitions.Def_ChapterNavierStokesFockSpace
import Mathlib
set_option autoImplicit false
open BookProof.NavierStokesFlow BookProof.NavierStokesFlow.FockOfFock
open BookProof.NavierStokesFlow.FullEsa BookProof.NavierStokesFlow.LpNat

section
variable {ι : Type*}
private theorem lpBasis_coe [DecidableEq ι] (i j : ι) :
    (((lpBasis i : lpFiniteModes ι) : lp (fun _ : ι => ℂ) 2) : ι → ℂ) j
      = if j = i then 1 else 0 := by
  by_cases h : j = i
  · subst h; simp [lpBasis, lp.single_apply]
  · simp [lpBasis, lp.single_apply, h]

end

variable {M : Type*} [DecidableEq M]

theorem solution (n k : Conf M) :
    (((fockBasis n : FockDom M) : FockL2 M) : Conf M → ℂ) k = if k = n then 1 else 0 :=
  lpBasis_coe n k


#print axioms solution
