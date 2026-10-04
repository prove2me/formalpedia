-- Prove2me | solution 1 for BookProof.NavierStokesFlow.FockManyMode.testState_coe
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-03T02:33:41.24936+00:00
-- url     : https://prove2.me/submissions/12a5a8dc-9ac3-4fd2-85a2-1fb6b48532ea

-- Generated from ChapterNavierStokesFockManyMode.lean — solution of BookProof.NavierStokesFlow.FockManyMode.testState_coe
import Mathlib
import Definitions.Def_ChapterNavierStokesFockManyMode
import Theorems.Thm_BookProof_NavierStokesFlow_FockManyMode_modeShift_zero_ne_zero
open BookProof.NavierStokesFlow
open BookProof.NavierStokesFlow.FockManyMode



open scoped ENNReal



open LpNat BookProof.FarisLavine IkebeKato ShiftHamiltonian


variable {d : ℕ} {κ : Fin d → ℝ}

variable {d : ℕ} {κ : Fin d → ℝ}

set_option maxHeartbeats 1000000 in
theorem solution (i₀ : Fin d) (β : Occ d) :
    ((testState κ i₀ : L2I (Occ d)) : Occ d → ℂ) β
      = if β = 0 then 1 else if β = modeShift i₀ 0 then 1 else 0 := by

  classical
  have hne : (0 : Occ d) ≠ modeShift i₀ 0 := Ne.symm (modeShift_zero_ne_zero i₀)
  simp only [testState, lp.coeFn_add, Pi.add_apply, lp.single_apply, Pi.single_apply]
  by_cases h0 : β = 0
  · subst h0
    simp [hne]
  · by_cases h1 : β = modeShift i₀ 0
    · subst h1
      simp [h0]
    · simp [h0, h1]
