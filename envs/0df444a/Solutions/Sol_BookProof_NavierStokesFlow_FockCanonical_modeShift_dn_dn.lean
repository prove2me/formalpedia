-- Prove2me | solution 1 for BookProof.NavierStokesFlow.FockCanonical.modeShift_dn_dn
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-03T02:32:13.309414+00:00
-- url     : https://prove2.me/submissions/7373d106-121a-4236-aff5-2306e15f9497

-- Generated from ChapterNavierStokesFockCanonical.lean — solution of BookProof.NavierStokesFlow.FockCanonical.modeShift_dn_dn
import Mathlib
import Definitions.Def_ChapterNavierStokesFockCanonical
import Theorems.Thm_BookProof_NavierStokesFlow_FockCanonical_dn_self
import Theorems.Thm_BookProof_NavierStokesFlow_FockCanonical_up_up
import Theorems.Thm_BookProof_FockSecondQuantization_up_dn
open BookProof.NavierStokesFlow
open BookProof.NavierStokesFlow.FockCanonical



open scoped ENNReal



open LpNat BookProof.FarisLavine IkebeKato ShiftHamiltonian FockManyMode HermiteCanonical

variable {d : ℕ} {κ : Fin d → ℝ}

variable {d : ℕ} {κ : Fin d → ℝ}

set_option maxHeartbeats 1000000 in
theorem solution (i : Fin d) {β : Occ d} (h : 2 ≤ β i) :
    modeShift i (dn i (dn i β)) = β := by

  rw [← up_up]
  have h1 : 1 ≤ dn i β i := by simp only [dn_self]; omega
  rw [up_dn i h1, up_dn i (by omega : 1 ≤ β i)]
