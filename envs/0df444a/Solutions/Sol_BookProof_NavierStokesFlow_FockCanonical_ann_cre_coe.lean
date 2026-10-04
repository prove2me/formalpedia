-- Prove2me | solution 1 for BookProof.NavierStokesFlow.FockCanonical.ann_cre_coe
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-03T02:14:47.401653+00:00
-- url     : https://prove2.me/submissions/082a4460-b52b-4acc-9707-ce243ec0058b

-- Generated from ChapterNavierStokesFockCanonical.lean — solution of BookProof.NavierStokesFlow.FockCanonical.ann_cre_coe
import Mathlib
import Definitions.Def_ChapterNavierStokesFockCanonical
import Theorems.Thm_BookProof_NavierStokesFlow_FockCanonical_up_self
import Theorems.Thm_BookProof_NavierStokesFlow_FockCanonical_dn_up
import Theorems.Thm_BookProof_NavierStokesFlow_FockCanonical_ann_coe
import Theorems.Thm_BookProof_NavierStokesFlow_FockCanonical_cre_coe
import Theorems.Thm_BookProof_NavierStokesFlow_HermiteCanonical_sqrt_mul_sqrt
open BookProof.NavierStokesFlow
open BookProof.NavierStokesFlow.FockCanonical



open scoped ENNReal



open LpNat BookProof.FarisLavine IkebeKato ShiftHamiltonian FockManyMode HermiteCanonical

variable {d : ℕ} {κ : Fin d → ℝ}

variable {d : ℕ} {κ : Fin d → ℝ}

set_option maxHeartbeats 1000000 in
theorem solution (i : Fin d) (x : lpFiniteModes (Occ d)) (α : Occ d) :
    (((ann i (cre i x) : lpFiniteModes (Occ d)) : L2I (Occ d)) : Occ d → ℂ) α
      = ((α i : ℂ) + 1) * ((x : L2I (Occ d)) : Occ d → ℂ) α := by

  rw [ann_coe, cre_coe, up_self, dn_up]
  push_cast
  rw [← mul_assoc, sqrt_mul_sqrt _ (by positivity)]
  push_cast
  ring
