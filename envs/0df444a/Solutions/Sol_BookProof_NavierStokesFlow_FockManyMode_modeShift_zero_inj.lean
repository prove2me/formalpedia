-- Prove2me | solution 1 for BookProof.NavierStokesFlow.FockManyMode.modeShift_zero_inj
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-10T21:13:39.539777+00:00
-- url     : https://prove2.me/submissions/a8414bd5-a12c-4e27-98bb-bd4db5970de0

import Mathlib
import Definitions.Def_ChapterNavierStokesFockManyMode
open BookProof.NavierStokesFlow
open BookProof.NavierStokesFlow.FockManyMode
open scoped ENNReal
open BookProof.NavierStokesFlow.LpNat BookProof.FarisLavine BookProof.NavierStokesFlow.IkebeKato BookProof.NavierStokesFlow.ShiftHamiltonian
variable {d : ℕ} {κ : Fin d → ℝ}

theorem solution {i j : Fin d} (h : modeShift i (0 : Occ d) = modeShift j 0) : i = j := by
  by_contra hne
  have hi := congrFun h i
  have h20 : (2 : ℕ) = 0 := by
    simpa [modeShift, hne] using hi
  omega
