-- Prove2me | solution 1 for BookProof.NavierStokesFlow.FockManyMode.fockH_essentiallySelfAdjointOn_core
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-08T22:52:13.057042+00:00
-- url     : https://prove2.me/submissions/09d7e7d8-14fd-4a71-b747-484687f5ef70
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

-- Generated from ChapterNavierStokesFockManyMode.lean — solution of BookProof.NavierStokesFlow.FockManyMode.fockH_essentiallySelfAdjointOn_core
import Mathlib
import Definitions.Def_ChapterNavierStokesFockManyMode
import Theorems.Thm_BookProof_NavierStokesFlow_FockManyMode_fockSym_nonneg
import Theorems.Thm_BookProof_NavierStokesFlow_FockManyMode_fockH_symmetricOn
import Theorems.Thm_BookProof_NavierStokesFlow_FockManyMode_fockH_relative_bound
import Theorems.Thm_BookProof_NavierStokesFlow_FockManyMode_fockH_commForm_bound
import Theorems.Thm_BookProof_NavierStokesFlow_IkebeKato_essentiallySelfAdjointOn_finiteModes_of_farisLavine_bounds
import Definitions.Def_ChapterNavierStokesIkebeKato
open BookProof.NavierStokesFlow
open BookProof.NavierStokesFlow.FockManyMode



open scoped ENNReal



open LpNat BookProof.FarisLavine IkebeKato ShiftHamiltonian


variable {d : ℕ} {κ : Fin d → ℝ}

variable {d : ℕ} {κ : Fin d → ℝ}

set_option maxHeartbeats 1000000 in
theorem solution (hκ : ∀ i, 0 ≤ κ i) :
    EssentiallySelfAdjointOn (lpFiniteModes (Occ d))
      ((fockH hκ).comp (Submodule.inclusion (finiteModes_le_maxDom (fockSym κ)))) := by

  refine essentiallySelfAdjointOn_finiteModes_of_farisLavine_bounds (fockSym κ)
    (fockSym_nonneg hκ) (fockH hκ) ((d : ℝ) ^ 2 / 2) (2 * d * ∑ i, κ i ^ 2)
    (∑ i, (2 * κ i + 4 * κ i ^ 2)) (fockH_symmetricOn hκ) ?_
    (fockH_relative_bound hκ) (fockH_commForm_bound hκ)
  exact Finset.sum_nonneg fun i _ => by nlinarith [hκ i]
