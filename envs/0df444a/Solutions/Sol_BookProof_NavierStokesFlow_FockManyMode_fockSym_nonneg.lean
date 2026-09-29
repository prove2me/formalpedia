-- Prove2me | solution 1 for BookProof.NavierStokesFlow.FockManyMode.fockSym_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-10T21:13:52.810967+00:00
-- url     : https://prove2.me/submissions/db6f65e1-d5c6-4fa6-b421-d4dd375de637

import Mathlib
import Definitions.Def_ChapterNavierStokesFockManyMode
open BookProof.NavierStokesFlow
open BookProof.NavierStokesFlow.FockManyMode
open scoped ENNReal
open BookProof.NavierStokesFlow.LpNat BookProof.FarisLavine BookProof.NavierStokesFlow.IkebeKato BookProof.NavierStokesFlow.ShiftHamiltonian
variable {d : ℕ} {κ : Fin d → ℝ}

theorem solution (hκ : ∀ i, 0 ≤ κ i) (α : Occ d) : 0 ≤ fockSym κ α := by
  have h := fockSym_ge_one hκ α
  linarith
