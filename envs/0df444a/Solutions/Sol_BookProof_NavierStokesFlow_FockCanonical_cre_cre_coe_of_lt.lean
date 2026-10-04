-- Prove2me | solution 1 for BookProof.NavierStokesFlow.FockCanonical.cre_cre_coe_of_lt
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-03T02:14:35.806522+00:00
-- url     : https://prove2.me/submissions/b1e6d6f1-3e99-4d93-8ee6-ea4df2dc2f76

-- Generated from ChapterNavierStokesFockCanonical.lean — solution of BookProof.NavierStokesFlow.FockCanonical.cre_cre_coe_of_lt
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
    (h : β i < 2) :
    (((cre i (cre i x) : lpFiniteModes (Occ d)) : L2I (Occ d)) : Occ d → ℂ) β = 0 := by

  rw [cre_coe, cre_coe, dn_self]
  rcases Nat.lt_or_ge (β i) 1 with h0 | h1
  · have : β i = 0 := by omega
    rw [this]
    simp
  · have : β i - 1 = 0 := by omega
    rw [this]
    simp
