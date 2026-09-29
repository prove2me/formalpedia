-- Prove2me | solution 1 for BookProof.NavierStokesFlow.FockOfFock.lpDiag_isSymmetricDom
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T09:20:26.065872+00:00
-- url     : https://prove2.me/submissions/24f447b1-8351-40db-9112-1086fdae3ca7

-- Adapted from Leonardo Pedro, timepiece commit61595bc, Apache-2.0.
-- https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterNavierStokesFockSpace.lean
import Definitions.Def_ChapterNavierStokesFockSpace
import Mathlib
set_option autoImplicit false
open BookProof.NavierStokesFlow BookProof.NavierStokesFlow.FockOfFock
open BookProof.NavierStokesFlow.FullEsa BookProof.NavierStokesFlow.LpNat

variable {ι : Type*}

private theorem lpDiag_coe (c : ι → ℝ) (f : lpFiniteModes ι) (i : ι) :
    (((lpDiag c f : lpFiniteModes ι) : lp (fun _ : ι => ℂ) 2) : ι → ℂ) i
      = (c i : ℂ) * ((f : lp (fun _ : ι => ℂ) 2) : ι → ℂ) i := rfl

theorem solution (c : ι → ℝ) : IsSymmetricDom (lpDiag c) := by
  intro x y
  rw [lp.inner_eq_tsum, lp.inner_eq_tsum]
  refine tsum_congr fun i => ?_
  simp only [RCLike.inner_apply, lpDiag_coe, map_mul, Complex.conj_ofReal]
  ring


#print axioms solution
