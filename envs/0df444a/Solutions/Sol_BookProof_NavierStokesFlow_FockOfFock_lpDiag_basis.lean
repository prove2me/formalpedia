-- Prove2me | solution 1 for BookProof.NavierStokesFlow.FockOfFock.lpDiag_basis
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T09:24:15.745268+00:00
-- url     : https://prove2.me/submissions/806a0a3c-48aa-44c8-88af-bacda46f6b76

-- Adapted from Leonardo Pedro, timepiece commit61595bc, Apache-2.0.
-- https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterNavierStokesFockSpace.lean
import Definitions.Def_ChapterNavierStokesFockSpace
import Mathlib
set_option autoImplicit false
open BookProof.NavierStokesFlow BookProof.NavierStokesFlow.FockOfFock
open BookProof.NavierStokesFlow.FullEsa BookProof.NavierStokesFlow.LpNat

variable {ι : Type*}

private theorem lpBasis_coe [DecidableEq ι] (i j : ι) :
    (((lpBasis i : lpFiniteModes ι) : lp (fun _ : ι => ℂ) 2) : ι → ℂ) j
      = if j = i then 1 else 0 := by
  by_cases h : j = i
  · subst h; simp [lpBasis, lp.single_apply]
  · simp [lpBasis, lp.single_apply, h]

private theorem lpDiag_coe (c : ι → ℝ) (f : lpFiniteModes ι) (i : ι) :
    (((lpDiag c f : lpFiniteModes ι) : lp (fun _ : ι => ℂ) 2) : ι → ℂ) i
      = (c i : ℂ) * ((f : lp (fun _ : ι => ℂ) 2) : ι → ℂ) i := rfl

theorem solution [DecidableEq ι] (c : ι → ℝ) (i : ι) :
    lpDiag c (lpBasis i) = ((c i : ℝ) : ℂ) • lpBasis i := by
  apply Subtype.ext
  apply lp.ext
  funext j
  change (c j : ℂ) * (((lpBasis i : lpFiniteModes ι) : lp (fun _ : ι => ℂ) 2) : ι → ℂ) j =
    (c i : ℂ) * (((lpBasis i : lpFiniteModes ι) : lp (fun _ : ι => ℂ) 2) : ι → ℂ) j
  rw [lpBasis_coe]
  by_cases h : j = i
  · subst j
    rfl
  · simp [h]

#print axioms solution
