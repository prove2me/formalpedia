-- Prove2me | solution 1 for BookProof.NavierStokesFlow.FockManyMode.testState_coe_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-03T02:49:23.14222+00:00
-- url     : https://prove2.me/submissions/e064fc39-368c-4555-b0eb-fcc1d0676591

-- Generated from ChapterNavierStokesFockManyMode.lean — solution of BookProof.NavierStokesFlow.FockManyMode.testState_coe_eq_zero
import Mathlib
import Definitions.Def_ChapterNavierStokesFockManyMode
import Theorems.Thm_BookProof_NavierStokesFlow_FockManyMode_testState_coe
open BookProof.NavierStokesFlow
open BookProof.NavierStokesFlow.FockManyMode



open scoped ENNReal



open LpNat BookProof.FarisLavine IkebeKato ShiftHamiltonian


variable {d : ℕ} {κ : Fin d → ℝ}

variable {d : ℕ} {κ : Fin d → ℝ}

set_option maxHeartbeats 1000000 in
theorem solution (i₀ : Fin d) {β : Occ d}
    (h0 : β ≠ 0) (h1 : β ≠ modeShift i₀ 0) :
    ((testState κ i₀ : L2I (Occ d)) : Occ d → ℂ) β = 0 := by

  rw [testState_coe, if_neg h0, if_neg h1]
