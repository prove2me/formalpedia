-- Prove2me | solution 1 for BookProof.NavierStokesFlow.FockManyMode.testState_coe_zero
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-03T02:49:57.724977+00:00
-- url     : https://prove2.me/submissions/2be7d83c-f319-46d3-9be2-fff7c908c8c5

-- Generated from ChapterNavierStokesFockManyMode.lean — solution of BookProof.NavierStokesFlow.FockManyMode.testState_coe_zero
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
theorem solution (i₀ : Fin d) :
    ((testState κ i₀ : L2I (Occ d)) : Occ d → ℂ) 0 = 1 := by

  rw [testState_coe, if_pos rfl]
