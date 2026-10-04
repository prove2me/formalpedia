-- Prove2me | solution 1 for BookProof.NavierStokesFlow.FockCanonical.dn_dn_self
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-03T02:14:43.422167+00:00
-- url     : https://prove2.me/submissions/973bcb71-5caf-4e6a-a59a-c1c13018e275

-- Generated from ChapterNavierStokesFockCanonical.lean — solution of BookProof.NavierStokesFlow.FockCanonical.dn_dn_self
import Mathlib
import Definitions.Def_ChapterNavierStokesFockCanonical
import Theorems.Thm_BookProof_NavierStokesFlow_FockCanonical_dn_self
open BookProof.NavierStokesFlow
open BookProof.NavierStokesFlow.FockCanonical



open scoped ENNReal



open LpNat BookProof.FarisLavine IkebeKato ShiftHamiltonian FockManyMode HermiteCanonical

variable {d : ℕ} {κ : Fin d → ℝ}

variable {d : ℕ} {κ : Fin d → ℝ}

set_option maxHeartbeats 1000000 in
theorem solution (i : Fin d) (β : Occ d) : (dn i (dn i β)) i = β i - 2 := by

  simp only [dn_self]
  omega
