-- Prove2me | solution 1 for BookProof.NavierStokesFlow.FockOfFock.innerBasis_total
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T09:20:29.376975+00:00
-- url     : https://prove2.me/submissions/6e9fb6ab-86c5-4d21-a4dc-51f6dd42b1f2

-- Adapted from Leonardo Pedro, timepiece commit61595bc, Apache-2.0.
-- https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterNavierStokesFockSpace.lean
import Definitions.Def_ChapterNavierStokesFockSpace
import Mathlib
set_option autoImplicit false
open BookProof.NavierStokesFlow BookProof.NavierStokesFlow.FockOfFock
open BookProof.NavierStokesFlow.FullEsa BookProof.NavierStokesFlow.LpNat

section
variable {ι : Type*}
private theorem lpBasis_total [DecidableEq ι] (w : lp (fun _ : ι => ℂ) 2)
    (hw : ∀ i, (inner ℂ ((lpBasis i : lpFiniteModes ι) : lp (fun _ : ι => ℂ) 2) w : ℂ) = 0) :
    w = 0 := by
  ext i
  have h := hw i
  rw [show ((lpBasis i : lpFiniteModes ι) : lp (fun _ : ι => ℂ) 2) = lp.single 2 i 1 from rfl,
    lp.inner_single_left] at h
  simpa using h

end

variable {K : Type*} [DecidableEq K]

theorem solution (w : FockL2 K)
    (hw : ∀ c : Conf K, (inner ℂ ((fockBasis c : FockDom K) : FockL2 K) w : ℂ) = 0) : w = 0 :=
  lpBasis_total w hw


#print axioms solution
