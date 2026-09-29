-- Prove2me | solution 1 for BookProof.NavierStokesFlow.FockManyMode.modeData_sym
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-10T22:34:36.573447+00:00
-- url     : https://prove2.me/submissions/ebb3b073-e504-458b-b822-2715c40e909b

import Mathlib
import Definitions.Def_ChapterNavierStokesFockManyMode
open BookProof.NavierStokesFlow
open BookProof.NavierStokesFlow.FockManyMode
open scoped ENNReal
open BookProof.NavierStokesFlow.LpNat BookProof.FarisLavine BookProof.NavierStokesFlow.IkebeKato BookProof.NavierStokesFlow.ShiftHamiltonian
noncomputable section

variable {d : ℕ} {κ : Fin d → ℝ}

theorem solution (hκ : ∀ i, 0 ≤ κ i) (i : Fin d) :
    (modeData hκ i).sym = fockSym κ := by
  rfl
