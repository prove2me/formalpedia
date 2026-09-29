-- Prove2me | solution 1 for BookProof.NavierStokesFlow.ThreeComponent.velH_ne_zero_of_vorticity
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-09-13T13:20:47.687732+00:00
-- url     : https://prove2.me/submissions/987e01fb-13d7-4480-aaa9-cf4b3322f99c

-- Generated from ChapterNavierStokesThreeComponent.lean — solution of BookProof.NavierStokesFlow.ThreeComponent.velH_ne_zero_of_vorticity
import Mathlib
import Definitions.Def_ChapterNavierStokesThreeComponent
import Theorems.Thm_BookProof_NavierStokesFlow_ThreeComponent_velH_coord_rot
import Definitions.Def_ChapterNavierStokesDeficiency
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterNavierStokesIkebeKato
import Definitions.Def_ChapterNavierStokesShiftHamiltonian
import Definitions.Def_ChapterNavierStokesSignedShift
open BookProof.NavierStokesFlow
open BookProof.NavierStokesFlow.ThreeComponent
















open scoped ENNReal



open BookProof.NavierStokesFlow.LpNat BookProof.FarisLavine BookProof.NavierStokesFlow.IkebeKato BookProof.NavierStokesFlow.ShiftHamiltonian BookProof.NavierStokesFlow.SignedShift





































variable (A : Matrix (Fin 3) (Fin 3) ℝ) (c : Fin 3 → ℝ)

set_option maxHeartbeats 1000000 in
theorem solution (h : A 0 1 - A 1 0 ≠ 0) :
    velH A c (velState A c ![0, 1, 0]) ≠ 0 := by

  intro h0
  have hco := velH_coord_rot A c
  rw [h0] at hco
  simp only [lp.coeFn_zero, Pi.zero_apply] at hco
  have : ((A 0 1 - A 1 0) / 2 : ℝ) = 0 := by
    have h1 : (((A 0 1 - A 1 0) / 2 : ℝ) : ℂ) = 0 := by
      have := hco.symm
      simpa [Complex.ext_iff] using this
    exact_mod_cast h1
  exact h (by linarith)
