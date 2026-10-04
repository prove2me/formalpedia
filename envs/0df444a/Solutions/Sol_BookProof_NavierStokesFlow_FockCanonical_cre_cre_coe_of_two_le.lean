-- Prove2me | solution 1 for BookProof.NavierStokesFlow.FockCanonical.cre_cre_coe_of_two_le
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-03T02:14:39.412742+00:00
-- url     : https://prove2.me/submissions/59ac7e94-f54b-4307-b7c4-76272baae27e

-- Generated from ChapterNavierStokesFockCanonical.lean — solution of BookProof.NavierStokesFlow.FockCanonical.cre_cre_coe_of_two_le
import Mathlib
import Definitions.Def_ChapterNavierStokesFockCanonical
import Theorems.Thm_BookProof_NavierStokesFlow_FockCanonical_dn_self
import Theorems.Thm_BookProof_NavierStokesFlow_FockCanonical_cre_coe
open BookProof.NavierStokesFlow
open BookProof.NavierStokesFlow.FockCanonical



open scoped ENNReal



open LpNat BookProof.FarisLavine IkebeKato ShiftHamiltonian FockManyMode HermiteCanonical

variable {d : ℕ} {κ : Fin d → ℝ}

variable {d : ℕ} {κ : Fin d → ℝ}

set_option maxHeartbeats 1000000 in
theorem solution (i : Fin d) (x : lpFiniteModes (Occ d)) {β : Occ d}
    (h : 2 ≤ β i) :
    (((cre i (cre i x) : lpFiniteModes (Occ d)) : L2I (Occ d)) : Occ d → ℂ) β
      = (Real.sqrt (β i : ℝ) : ℂ) * (Real.sqrt ((β i : ℝ) - 1) : ℂ)
        * ((x : L2I (Occ d)) : Occ d → ℂ) (dn i (dn i β)) := by

  rw [cre_coe, cre_coe, dn_self]
  have hcast : ((β i - 1 : ℕ) : ℝ) = (β i : ℝ) - 1 := by
    have : (1 : ℕ) ≤ β i := by omega
    push_cast [Nat.cast_sub this]
    ring
  rw [hcast]
  ring
