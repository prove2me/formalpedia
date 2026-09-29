-- Prove2me | solution 1 for BookProof.NavierStokesFlow.FockManyMode.fockH_apply
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T09:27:15.743882+00:00
-- url     : https://prove2.me/submissions/14327c24-c6e1-40fc-b5c8-bf9109d16f45

-- Adapted from Leonardo Pedro, timepiece commit 61595bc, Apache-2.0.
-- https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterNavierStokesFockManyMode.lean
import Definitions.Def_ChapterNavierStokesFockManyMode
import Mathlib
set_option autoImplicit false
open BookProof.NavierStokesFlow BookProof.NavierStokesFlow.FockManyMode
open BookProof.NavierStokesFlow.LpNat BookProof.FarisLavine
open BookProof.NavierStokesFlow.IkebeKato BookProof.NavierStokesFlow.ShiftHamiltonian
variable {d : ℕ} {κ : Fin d → ℝ}

theorem solution (hκ : ∀ i, 0 ≤ κ i) (x : maxDom (fockSym κ)) :
    (fockH hκ x : L2I (Occ d)) = ∑ i, (ShiftData.shiftH (modeData hκ i) x : L2I (Occ d)) := by
  rw [fockH]
  exact LinearMap.sum_apply _ _ _
#print axioms solution
