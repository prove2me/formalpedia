-- Prove2me | solution 1 for BookProof.NavierStokesFlow.FockCanonical.coe_sum_apply
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-03T02:14:23.624878+00:00
-- url     : https://prove2.me/submissions/185abd7c-0bca-471b-8f73-3c2dcf557b2e

-- Generated from ChapterNavierStokesFockCanonical.lean — solution of BookProof.NavierStokesFlow.FockCanonical.coe_sum_apply
import Mathlib
import Definitions.Def_ChapterNavierStokesFockCanonical
open BookProof.NavierStokesFlow
open BookProof.NavierStokesFlow.FockCanonical



open scoped ENNReal



open LpNat BookProof.FarisLavine IkebeKato ShiftHamiltonian FockManyMode HermiteCanonical

variable {d : ℕ} {κ : Fin d → ℝ}

variable {d : ℕ} {κ : Fin d → ℝ}

set_option maxHeartbeats 1000000 in
theorem solution (s : Finset (Fin d)) (v : Fin d → lpFiniteModes (Occ d)) (α : Occ d) :
    (((∑ i ∈ s, v i : lpFiniteModes (Occ d)) : L2I (Occ d)) : Occ d → ℂ) α
      = ∑ i ∈ s, (((v i : lpFiniteModes (Occ d)) : L2I (Occ d)) : Occ d → ℂ) α := by

  classical
  induction s using Finset.induction with
  | empty => simp
  | insert i t hi ih =>
      rw [Finset.sum_insert hi, Finset.sum_insert hi, ← ih]
      simp only [Submodule.coe_add, lp.coeFn_add, Pi.add_apply]
