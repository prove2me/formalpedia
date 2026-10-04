-- Prove2me | solution 1 for BookProof.NavierStokesFlow.FockCanonical.ann_ann_coe
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-03T02:14:51.425507+00:00
-- url     : https://prove2.me/submissions/090eff59-ecb0-4d90-8bac-d0850bee78f1

-- Generated from ChapterNavierStokesFockCanonical.lean — solution of BookProof.NavierStokesFlow.FockCanonical.ann_ann_coe
import Mathlib
import Definitions.Def_ChapterNavierStokesFockCanonical
import Theorems.Thm_BookProof_NavierStokesFlow_FockCanonical_up_self
import Theorems.Thm_BookProof_NavierStokesFlow_FockCanonical_up_up
import Theorems.Thm_BookProof_NavierStokesFlow_FockCanonical_ann_coe
open BookProof.NavierStokesFlow
open BookProof.NavierStokesFlow.FockCanonical



open scoped ENNReal



open LpNat BookProof.FarisLavine IkebeKato ShiftHamiltonian FockManyMode HermiteCanonical

variable {d : ℕ} {κ : Fin d → ℝ}

variable {d : ℕ} {κ : Fin d → ℝ}

set_option maxHeartbeats 1000000 in
theorem solution (i : Fin d) (x : lpFiniteModes (Occ d)) (α : Occ d) :
    (((ann i (ann i x) : lpFiniteModes (Occ d)) : L2I (Occ d)) : Occ d → ℂ) α
      = (Real.sqrt ((α i : ℝ) + 1) : ℂ) * (Real.sqrt ((α i : ℝ) + 2) : ℂ)
        * ((x : L2I (Occ d)) : Occ d → ℂ) (modeShift i α) := by

  rw [ann_coe, ann_coe, up_self, up_up]
  push_cast
  ring_nf
