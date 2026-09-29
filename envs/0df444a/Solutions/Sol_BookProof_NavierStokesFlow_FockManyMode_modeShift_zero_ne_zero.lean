-- Prove2me | solution 1 for BookProof.NavierStokesFlow.FockManyMode.modeShift_zero_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-10T21:13:36.208115+00:00
-- url     : https://prove2.me/submissions/ab927a89-366c-4dc6-aa1a-7d9302973ae7

import Mathlib
import Definitions.Def_ChapterNavierStokesFockManyMode
open BookProof.NavierStokesFlow
open BookProof.NavierStokesFlow.FockManyMode
open scoped ENNReal
open BookProof.NavierStokesFlow.LpNat BookProof.FarisLavine BookProof.NavierStokesFlow.IkebeKato BookProof.NavierStokesFlow.ShiftHamiltonian
variable {d : ℕ} {κ : Fin d → ℝ}

theorem solution (i : Fin d) : modeShift i (0 : Occ d) ≠ 0 := by
  intro h
  have hi := congrFun h i
  simpa [modeShift] using hi
