-- Prove2me | solution 1 for BookProof.NavierStokesFlow.FockCanonical.fock_canonical_essentiallySelfAdjointOn_core
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-09T09:49:50.071615+00:00
-- url     : https://prove2.me/submissions/fee02a9c-24c5-42a1-8356-32f3d985db28
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

-- Generated from ChapterNavierStokesFockCanonical.lean — solution of BookProof.NavierStokesFlow.FockCanonical.fock_canonical_essentiallySelfAdjointOn_core
import Mathlib
import Definitions.Def_ChapterNavierStokesFockCanonical
import Theorems.Thm_BookProof_NavierStokesFlow_FockCanonical_fock_hamiltonian_eq
import Theorems.Thm_BookProof_NavierStokesFlow_FockManyMode_fockH_essentiallySelfAdjointOn_core
open BookProof.NavierStokesFlow
open BookProof.NavierStokesFlow.FockCanonical



open scoped ENNReal



open LpNat IkebeKato ShiftHamiltonian FockManyMode HermiteCanonical
open BookProof.FarisLavine

variable {d : ℕ} {κ : Fin d → ℝ}

set_option maxHeartbeats 1000000 in
theorem solution (hκ : ∀ i, 0 ≤ κ i) :
    EssentiallySelfAdjointOn (lpFiniteModes (Occ d))
      ((lpFiniteModes (Occ d)).subtype.comp
        (∑ i, ((1 : ℂ) / 2) • ((mom κ i).comp (drift κ i) + (drift κ i).comp (mom κ i)))) := by

  rw [fock_hamiltonian_eq hκ]
  exact fockH_essentiallySelfAdjointOn_core hκ
